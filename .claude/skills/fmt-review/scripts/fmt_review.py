#!/usr/bin/env python3
"""Track the changes to parsers and formatters in Lean core for post-hoc formatter reviews.

The reference is the master commit of the last completed review. Its syntax inventory
(`fmt-review-inventory.json`) is compared with the inventory of the current build to find the
review items. The state (`fmt-review.json`) keeps the items with their verdicts, and
`fmt-review.md` shows them. See `.claude/skills/fmt-review/SKILL.md` for the procedure.
"""

import argparse
import datetime
import difflib
import fnmatch
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent
INVENTORY_LEAN = SCRIPTS / "inventory.lean"
PR_URL = "https://github.com/leanprover/lean4/pull/{}"
# Paths whose changes are formatter changes. A commit that touches one of them is a review item.
FMT_PATHS = [
    "src/Lean/Fmt/",
    "src/lake/Lake/Formatters/",
    "src/lake/Lake/Formatters.lean",
    "src/Lean/Fmt.lean",
    "src/Lean/Linter/Fmt.lean",
    "tests/fmt/",
    "script/missing-fmts.sh",
    "script/check-fmt-idempotence.sh",
    "script/eval-fmt-fresh.sh",
    ".claude/skills/fmt-formatters/",
]
STATUSES = ["pending", "fix", "fixed", "ok", "deferred"]
OPEN_STATUSES = ["pending", "fix"]
TYPE_ORDER = [
    "syntax-changed", "syntax-added", "syntax-removed", "combinator-changed",
    "kind-added", "kind-removed", "category-added", "category-removed", "category-changed",
    "tokens", "fmt-changed", "fmt-added", "fmt-replaced", "fmt-removed", "fmt-incomplete",
    "fmt-failure", "commit",
]
LINT_TYPES = ["fmt-incomplete", "fmt-failure"]
MAX_INLINE = 3
MAX_FMT_LINES = 60


class Ctx:
    """Paths of the repository, the build and the state files."""

    def __init__(self, state_dir=None, stage=None):
        self.root = Path(run(["jj", "root"], cwd=Path.cwd()).strip())
        self.dir = Path(state_dir).resolve() if state_dir else self.root
        self.state_path = self.dir / "fmt-review.json"
        self.ref_inv_path = self.dir / "fmt-review-inventory.json"
        self.md_path = self.dir / "fmt-review.md"
        self.work = self.root / "build" / "fmt-review"
        self.target_inv_path = self.work / "inventory.json"
        self.stage = Path(stage).resolve() if stage else self.root / "build" / "release" / "stage1"
        self._file_cache = {}
        self._annotate_cache = {}
        self._snapshotted = False

    def jj(self, *args):
        # The first call snapshots the working copy; later calls reuse that snapshot.
        flags = ["--no-pager", "--color=never"]
        if self._snapshotted:
            flags.append("--ignore-working-copy")
        out = run(["jj", *flags, *args], cwd=self.root)
        self._snapshotted = True
        return out

    def rel(self, path):
        try:
            return os.path.relpath(self.root / path, self.dir)
        except ValueError:
            return str(self.root / path)


def run(cmd, cwd=None, check=True):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    if check and p.returncode != 0:
        sys.exit(f"error: command failed: {' '.join(map(str, cmd))}\n{p.stderr.strip()}")
    return p.stdout


def today():
    return datetime.date.today().isoformat()


def load_json(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def write_json(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1, sort_keys=False)
        f.write("\n")


# --- jj ----------------------------------------------------------------------------------------

def resolve(ctx, rev):
    out = ctx.jj("log", "-r", rev, "--no-graph", "-T",
                 'commit_id ++ "\\t" ++ author.timestamp().format("%Y-%m-%d") ++ "\\t" '
                 '++ description.first_line() ++ "\\n"').strip().splitlines()
    if len(out) != 1:
        sys.exit(f"error: revision '{rev}' must resolve to exactly one commit, got {len(out)}")
    commit, date, title = out[0].split("\t", 2)
    return {"commit": commit, "date": date, "title": title}


def is_ancestor(ctx, a, b):
    return ctx.jj("log", "-r", f"{a} & ::({b})", "--no-graph", "-T", 'commit_id ++ "\\n"').strip() != ""


def commits_in(ctx, revset):
    """The commits of `revset`, oldest first, with the files that they change."""
    template = ('commit_id ++ "\\x1e" ++ change_id ++ "\\x1e" ++ author.name() ++ "\\x1e" '
                '++ author.timestamp().format("%Y-%m-%d") ++ "\\x1e" ++ description.first_line() '
                '++ "\\x1e" ++ self.diff().files().map(|e| e.path()).join("\\x1f") ++ "\\x1d"')
    out = ctx.jj("log", "-r", revset, "--reversed", "--no-graph", "-T", template)
    commits = []
    for rec in out.split("\x1d"):
        rec = rec.strip("\n")
        if not rec:
            continue
        commit, change, author, date, title, files = rec.split("\x1e")
        m = re.search(r"\(#(\d+)\)\s*$", title)
        commits.append({
            "commit": commit, "change": change, "author": author, "date": date, "title": title,
            "pr": int(m.group(1)) if m else None,
            "files": [f for f in files.split("\x1f") if f],
        })
    return commits


def file_at(ctx, rev, path):
    """The lines of `path` at `rev`, or of the working copy file if `rev` is None."""
    key = (rev, path)
    if key not in ctx._file_cache:
        if rev is None:
            p = ctx.root / path
            text = p.read_text(encoding="utf-8") if p.exists() else None
        else:
            r = subprocess.run(["jj", "--no-pager", "--ignore-working-copy", "file", "show", "-r",
                                rev, path], cwd=ctx.root, capture_output=True, text=True)
            text = r.stdout if r.returncode == 0 else None
        ctx._file_cache[key] = text.splitlines() if text is not None else None
    return ctx._file_cache[key]


def source_lines(ctx, rev, path, lines):
    text = file_at(ctx, rev, path) if path and lines else None
    return text[lines[0] - 1:lines[1]] if text is not None else None


def annotate(ctx, path):
    """The commit that last changed each line of `path` in the working-copy commit."""
    if path not in ctx._annotate_cache:
        r = subprocess.run(["jj", "--no-pager", "--ignore-working-copy", "file", "annotate", "-r",
                            "@", path, "-T", 'commit.commit_id() ++ "\\n"'],
                           cwd=ctx.root, capture_output=True, text=True)
        ctx._annotate_cache[path] = r.stdout.splitlines() if r.returncode == 0 else []
    return ctx._annotate_cache[path]


# --- build and inventory -----------------------------------------------------------------------

def module_file(module):
    if module is None:
        return None
    parts = module.split(".")
    prefix = "src/lake/" if parts[0] == "Lake" else "src/"
    return prefix + "/".join(parts) + ".lean"


def stale_modules(ctx):
    """The core modules whose source file is newer than its `.olean` in the stage."""
    lib = ctx.stage / "lib" / "lean"
    stale = []
    for base, tops in [("src", ["Init", "Std", "Lean"]), ("src/lake", ["Lake"])]:
        for top in tops:
            srcs = list((ctx.root / base / top).rglob("*.lean")) + [ctx.root / base / f"{top}.lean"]
            for src in srcs:
                olean = lib / src.relative_to(ctx.root / base).with_suffix(".olean")
                if olean.exists() and olean.stat().st_mtime < src.stat().st_mtime:
                    stale.append(str(src.relative_to(ctx.root)))
    return sorted(stale)


def check_build(ctx, allow_stale):
    lean = ctx.stage / "bin" / "lean"
    if not lean.exists():
        sys.exit(f"error: {lean} does not exist. Build Lean first (see the fmt-review skill).")
    stale = stale_modules(ctx)
    if stale:
        msg = (f"{len(stale)} source files are newer than their .olean files, for example "
               f"{', '.join(stale[:3])}. Build Lean first: make -C build/release -j24")
        if not allow_stale:
            sys.exit("error: " + msg + " (or pass --allow-stale)")
        print("warning: " + msg, file=sys.stderr)


def make_inventory(ctx, allow_stale=False):
    check_build(ctx, allow_stale)
    ctx.work.mkdir(parents=True, exist_ok=True)
    out = ctx.work / "inventory.raw.json"
    lean = ctx.stage / "bin" / "lean"
    plugin = ctx.stage / "lib" / "lean" / "libLake_shared.so"
    r = subprocess.run([str(lean), f"--plugin={plugin}", "--run", str(INVENTORY_LEAN), str(out)],
                       cwd=ctx.root, capture_output=True, text=True)
    if r.returncode != 0:
        sys.exit(f"error: inventory.lean failed:\n{r.stdout}{r.stderr}")
    return load_json(out)


def write_inventory(path, inv, meta):
    """Writes an inventory with one entry per line, without the `deps` of the declarations."""
    lines = ["{", f'"meta": {json.dumps(meta, ensure_ascii=False, sort_keys=True)},']
    for section in ["decls", "kinds", "fmts", "categories"]:
        entries = sorted(inv[section].items())
        lines.append(f'"{section}": {{')
        for i, (k, v) in enumerate(entries):
            v = {kk: vv for kk, vv in v.items() if kk != "deps"}
            sep = "," if i < len(entries) - 1 else ""
            lines.append(f"{json.dumps(k, ensure_ascii=False)}: "
                         f"{json.dumps(v, ensure_ascii=False, sort_keys=True)}{sep}")
        lines.append("},")
    lines.append(f'"tokens": {json.dumps(inv["tokens"], ensure_ascii=False)}')
    lines.append("}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


# --- items -------------------------------------------------------------------------------------

def fingerprint(item):
    """The parts of an item that a verdict covers. A verdict is reset when they change."""
    keys = ["hash", "refHash", "kinds", "fmtDecl", "fmtPriority", "added", "removed", "commit",
            "behavior", "count", "message"]
    data = {k: item[k] for k in keys if k in item}
    return hashlib.sha1(json.dumps(data, sort_keys=True).encode()).hexdigest()[:16]


def kind_fmt(inv, kind):
    k = inv["kinds"].get(kind)
    return k["fmt"] if k else None


def owner_module(inv, kind):
    k = inv["kinds"].get(kind)
    if k and k["owners"]:
        return inv["decls"].get(k["owners"][0], {}).get("module")
    return None


def affected_kinds(target, decl):
    """The kinds that are defined by a declaration that uses `decl`, transitively."""
    users = {}
    for n, d in target["decls"].items():
        for dep in d.get("deps", []):
            users.setdefault(dep, []).append(n)
    seen, todo, kinds = {decl}, [decl], set()
    while todo:
        for u in users.get(todo.pop(), []):
            if u not in seen:
                seen.add(u)
                todo.append(u)
                kinds.update(target["decls"][u]["kinds"])
    return sorted(kinds)


def compute_items(ref, target):
    items = {}

    def add(type_, name, **fields):
        item = {"id": f"{type_}:{name}" if name else type_, "type": type_, "name": name}
        item.update(fields)
        item["fingerprint"] = fingerprint(item)
        items[item["id"]] = item

    rd, td = ref["decls"], target["decls"]
    for n in sorted(set(rd) | set(td)):
        r, t = rd.get(n), td.get(n)
        kinds_r, kinds_t = (r or {}).get("kinds", []), (t or {}).get("kinds", [])
        defines = bool(kinds_r or kinds_t)
        if r and t:
            if r["hash"] == t["hash"] and kinds_r == kinds_t:
                continue
            type_ = "syntax-changed" if defines else "combinator-changed"
        elif t and defines:
            type_ = "syntax-added"
        elif r and defines:
            type_ = "syntax-removed"
        else:
            continue
        cur = t or r
        fields = {
            "module": cur["module"], "lines": (t or {}).get("lines"),
            "refModule": (r or {}).get("module"), "refLines": (r or {}).get("lines"),
            "hash": (t or {}).get("hash"), "refHash": (r or {}).get("hash"),
            "declType": cur["type"], "kinds": sorted(set(kinds_r) | set(kinds_t)),
        }
        if type_ == "combinator-changed":
            fields["affected"] = affected_kinds(target, n)
        fields["fmts"] = {k: kind_fmt(target, k) for k in kinds_t}
        add(type_, n, **fields)

    rk, tk = ref["kinds"], target["kinds"]
    for k in sorted(set(tk) - set(rk)):
        if not tk[k]["owners"]:
            add("kind-added", k, kinds=[k], fmts={k: tk[k]["fmt"]})
    for k in sorted(set(rk) - set(tk)):
        if not rk[k]["owners"]:
            add("kind-removed", k, kinds=[k])

    for k in sorted(set(rk) & set(tk)):
        fr, ft = rk[k]["fmt"], tk[k]["fmt"]
        if fr == ft:
            continue
        module = owner_module(target, k)
        common = {"kinds": [k], "module": module, "categories": tk[k]["categories"]}
        if fr is None:
            add("fmt-added", k, fmtDecl=ft["decl"], fmtPriority=ft["priority"], **common)
        elif ft is None:
            add("fmt-removed", k, refFmtDecl=fr["decl"], **common)
        else:
            add("fmt-replaced", k, fmtDecl=ft["decl"], fmtPriority=ft["priority"],
                refFmtDecl=fr["decl"], refFmtPriority=fr["priority"], **common)

    rf, tf = ref["fmts"], target["fmts"]
    for f in sorted(set(rf) & set(tf)):
        if rf[f]["hash"] != tf[f]["hash"]:
            served = sorted(k for k, v in tk.items() if v["fmt"] and v["fmt"]["decl"] == f)
            add("fmt-changed", f, module=tf[f]["module"], lines=tf[f]["lines"],
                refModule=rf[f]["module"], refLines=rf[f]["lines"], hash=tf[f]["hash"],
                refHash=rf[f]["hash"], kinds=served)

    rc, tc = ref["categories"], target["categories"]
    for c in sorted(set(rc) | set(tc)):
        r, t = rc.get(c), tc.get(c)
        cur = t or r
        fields = {"module": cur["module"], "lines": (t or {}).get("lines"),
                  "refLines": (r or {}).get("lines"), "decl": cur["decl"],
                  "behavior": cur["behavior"]}
        if r and t:
            if (r["decl"], r["behavior"]) != (t["decl"], t["behavior"]):
                add("category-changed", c, refBehavior=r["behavior"], refDecl=r["decl"], **fields)
        elif t:
            add("category-added", c, **fields)
        else:
            add("category-removed", c, **fields)

    added = sorted(set(target["tokens"]) - set(ref["tokens"]))
    removed = sorted(set(ref["tokens"]) - set(target["tokens"]))
    if added or removed:
        add("tokens", None, added=added, removed=removed)
    return items


def item_paths(item):
    """(path, lines) pairs of the current and the reference source of an item."""
    cur = (module_file(item.get("module")), item.get("lines"))
    ref = (module_file(item.get("refModule") or item.get("module")), item.get("refLines"))
    return cur, ref


def link_commits(ctx, items, range_commits, local_commits):
    """Adds to each item the commits in the range (or local commits) that changed its source."""
    known = {c["commit"]: c for c in range_commits + local_commits}
    by_file = {}
    for c in range_commits + local_commits:
        for f in c["files"]:
            by_file.setdefault(f, []).append(c["commit"])
    for item in items.values():
        if item["type"] == "commit":
            continue
        (path, lines), (ref_path, ref_lines) = item_paths(item)
        found = []
        if path and lines:
            ann = annotate(ctx, path)
            for c in ann[lines[0] - 1:lines[1]]:
                if c in known and c not in found:
                    found.append(c)
        if not found:
            # Removed declarations, and changes from outside of the declaration's own text.
            for p in {path, ref_path} - {None}:
                for c in by_file.get(p, []):
                    if c not in found:
                        found.append(c)
            item["commitsByFile"] = True
        item["commits"] = sorted(found, key=lambda c: list(known).index(c))
        if path and lines and ref_lines:
            cur = source_lines(ctx, None, path, lines)
            old = source_lines(ctx, ctx.reference, ref_path, ref_lines)
            if cur is not None and old is not None:
                item["sourceChanged"] = cur != old


def plain_title(title):
    return re.sub(r"\s*\(#\d+\)\s*$", "", title)


def fmt_commit_items(range_commits, local_commits, absorbed):
    """Items for the commits that change formatter files.

    `absorbed` holds the local changes whose syntax and formatters an earlier review made part of
    the reference. They get no item while they are local, and their landed version is `ok`.
    """
    items = {}
    landed = {plain_title(v["title"]): ch for ch, v in absorbed.items()}
    for c in range_commits + local_commits:
        paths = [f for f in c["files"] if any(f == p or f.startswith(p) for p in FMT_PATHS)]
        if not paths:
            continue
        local = c in local_commits
        if local and c["change"] in absorbed:
            continue
        # A local commit gets a new commit id when it is rebased or edited, but keeps its change id
        # (letters k-z, so it cannot be mistaken for a hexadecimal commit id).
        key = c["change"][:12] if local else c["commit"][:12]
        item = {"id": f"commit:{key}", "type": "commit", "name": key, "title": c["title"],
                "author": c["author"], "date": c["date"], "pr": c["pr"], "fmtFiles": paths,
                "commits": [c["commit"]], "local": local}
        item["fingerprint"] = fingerprint(dict(item, commit=key))
        item["commit"] = c["commit"]
        if not local and plain_title(c["title"]) in landed:
            ch = landed[plain_title(c["title"])]
            item["landedFrom"] = ch
            item["initialStatus"] = "ok"
            item["initialNote"] = (f"landed version of the local change {ch[:12]}, which the review "
                                   f"of {absorbed[ch]['reviewed']} made part of the reference")
        items[item["id"]] = item
    return items


def merge_items(state, live, keep_types=()):
    """Replaces the items of `state` by `live` and keeps the verdicts of the items in both."""
    old = state["items"]
    new, dropped, reopened = {}, [], []
    for id_, item in live.items():
        o = old.get(id_)
        if o:
            for k in ["status", "note", "verdictFingerprint", "verdictDate", "firstSeen"]:
                if k in o:
                    item[k] = o[k]
            if o.get("carried"):
                # A deferred item of an earlier review that changed again is a live item again.
                item["deferredSince"] = o.get("carriedSince")
            if o["status"] != "pending" and o.get("verdictFingerprint") != item["fingerprint"]:
                item["status"] = "pending"
                item["note"] = (o.get("note", "") + " [reopened: changed after the verdict]").strip()
                reopened.append(id_)
        else:
            item["status"] = item.pop("initialStatus", "pending")
            item["note"] = item.pop("initialNote", "")
            item["firstSeen"] = today()
            if item["status"] != "pending":
                item["verdictFingerprint"] = item["fingerprint"]
                item["verdictDate"] = today()
        item.pop("initialStatus", None)
        item.pop("initialNote", None)
        new[id_] = item
    for id_, o in old.items():
        if id_ in new:
            continue
        if o.get("carried") or o["type"] in keep_types:
            new[id_] = o
        else:
            dropped.append(id_)
    state["items"] = new
    return dropped, reopened


def missing_list(target):
    missing = {}
    for k, v in target["kinds"].items():
        if v["fmt"] is not None or v["private"] or k in ("null", "choice"):
            continue
        owner = v["owners"][0] if v["owners"] else None
        d = target["decls"].get(owner, {}) if owner else {}
        missing[k] = {"module": d.get("module"), "lines": d.get("lines"), "owner": owner,
                      "categories": v["categories"], "refs": v.get("fmtRefs", [])}
        if owner is None:
            # `ident`, `group`, `token.*` and the like, which no parser declaration defines.
            missing[k]["generic"] = True
    return missing


# --- state -------------------------------------------------------------------------------------

def load_state(ctx):
    if not ctx.state_path.exists():
        sys.exit(f"error: {ctx.state_path} does not exist. Run `init` first.")
    state = load_json(ctx.state_path)
    ctx.reference = state["reference"]["commit"]
    return state


def save_state(ctx, state):
    write_json(ctx.state_path, state)
    render(ctx, state)


def refresh_state(ctx, state, target_rev, allow_stale):
    """Recomputes the items of `state` for the build of the working copy and `target_rev`."""
    target = resolve(ctx, target_rev)
    ref = state["reference"]["commit"]
    if not is_ancestor(ctx, target["commit"], "@"):
        sys.exit(f"error: the target {target['commit'][:12]} ({target_rev}) is not an ancestor of "
                 "the working copy. Rebase the fmt-review stack onto it first.")
    if not is_ancestor(ctx, ref, target["commit"]):
        sys.exit(f"error: the reference {ref[:12]} is not an ancestor of the target.")
    inv = make_inventory(ctx, allow_stale)
    write_inventory(ctx.target_inv_path, inv, {"commit": target["commit"], "date": today()})
    ref_inv = load_json(ctx.ref_inv_path)
    range_commits = commits_in(ctx, f"{ref}..{target['commit']}")
    local_commits = [c for c in commits_in(ctx, f"{target['commit']}..@")
                     if any(f.startswith("src/") for f in c["files"])]
    live = compute_items(ref_inv, inv)
    link_commits(ctx, live, range_commits, local_commits)
    live.update(fmt_commit_items(range_commits, local_commits, state.get("absorbed", {})))
    dropped, reopened = merge_items(state, live, keep_types=LINT_TYPES)
    state["target"] = dict(target, refreshed=today(), commitCount=len(range_commits),
                           local=[{k: c[k] for k in ("commit", "change", "title")}
                                  for c in local_commits])
    state["commits"] = {c["commit"]: {k: c[k] for k in ("change", "author", "date", "title", "pr")}
                        for c in range_commits + local_commits
                        if any(c["commit"] in i.get("commits", []) for i in state["items"].values())}
    for c in local_commits:
        if c["commit"] in state["commits"]:
            state["commits"][c["commit"]]["local"] = True
    state["missing"] = missing_list(inv)
    state["privateKinds"] = sum(1 for v in inv["kinds"].values() if v["private"])
    state["kindCount"] = len(inv["kinds"])
    return dropped, reopened


# --- commands ----------------------------------------------------------------------------------

def cmd_init(ctx, args):
    if ctx.state_path.exists() and not args.force:
        sys.exit(f"error: {ctx.state_path} exists. Pass --force to replace it.")
    reference = resolve(ctx, args.reference)
    if not is_ancestor(ctx, reference["commit"], "@"):
        sys.exit("error: the reference is not an ancestor of the working copy.")
    local = [c for c in commits_in(ctx, f"{reference['commit']}..@")
             if any(f.startswith("src/") for f in c["files"])]
    if local:
        sys.exit("error: the working copy changes src/ relative to the reference, so the build does "
                 "not show the reference: " + ", ".join(c["commit"][:12] for c in local))
    inv = make_inventory(ctx, args.allow_stale)
    write_inventory(ctx.ref_inv_path, inv, {"commit": reference["commit"], "date": today()})
    ctx.reference = reference["commit"]
    state = {
        "version": 1,
        "reference": dict(reference, reviewed=today()),
        "target": dict(reference, refreshed=today(), commitCount=0, local=[]),
        "items": {}, "commits": {}, "missingNotes": {}, "log": [],
        "missing": missing_list(inv),
        "privateKinds": sum(1 for v in inv["kinds"].values() if v["private"]),
        "kindCount": len(inv["kinds"]),
    }
    save_state(ctx, state)
    print(f"Initialized the review state with the reference {reference['commit'][:12]} "
          f"({reference['title']}). Syntax without a formatter: {missing_counts(state)}.")


def cmd_refresh(ctx, args):
    state = load_state(ctx)
    dropped, reopened = refresh_state(ctx, state, args.target, args.allow_stale)
    save_state(ctx, state)
    summarize(state, dropped, reopened)


def summarize(state, dropped=(), reopened=()):
    items = state["items"].values()
    counts = {s: sum(1 for i in items if i["status"] == s) for s in STATUSES}
    t = state["target"]
    print(f"Reference {state['reference']['commit'][:12]} -> target {t['commit'][:12]} "
          f"({t['commitCount']} commits). Items: "
          + (", ".join(f"{n} {s}" for s, n in counts.items() if n) or "none"))
    if t.get("local"):
        print("The build includes local changes: "
              + ", ".join(f"{c.get('change', c['commit'])[:12]} {c['title']}" for c in t["local"]))
    if reopened:
        print("Reopened (changed after the verdict): " + ", ".join(reopened))
    if dropped:
        print("Dropped (no longer different from the reference): " + ", ".join(dropped))
    print(f"Syntax without a formatter: {missing_counts(state)}")


def missing_counts(state):
    missing, notes = state["missing"], state.get("missingNotes", {})
    exempt = sum(1 for k in missing if notes.get(k, {}).get("exempt"))
    generic = sum(1 for k, v in missing.items()
                  if v.get("generic") and not notes.get(k, {}).get("exempt"))
    unmatched = sum(1 for k, v in missing.items()
                    if not v.get("generic") and not v.get("refs")
                    and not notes.get(k, {}).get("exempt"))
    return (f"{len(missing) - exempt - generic} kinds, {unmatched} of them not matched by a "
            f"formatter (and {generic} generic kinds, {exempt} exempt kinds)")


def find_items(state, patterns, all_matches=False):
    ids = list(state["items"])
    found = []
    for p in patterns:
        if p in state["items"]:
            found.append(p)
            continue
        if any(ch in p for ch in "*?["):
            m = [i for i in ids if fnmatch.fnmatchcase(i, p)]
        else:
            m = [i for i in ids if p in i]
        if not m:
            sys.exit(f"error: no item matches '{p}'")
        if len(m) > 1 and not all_matches and not any(ch in p for ch in "*?["):
            sys.exit(f"error: '{p}' matches several items: {', '.join(m[:10])}. "
                     "Use the full id or a glob.")
        found.extend(i for i in m if i not in found)
    return found


def cmd_list(ctx, args):
    state = load_state(ctx)
    for item in sorted_items(state["items"].values()):
        if args.status and item["status"] not in args.status:
            continue
        if args.open and item["status"] not in OPEN_STATUSES:
            continue
        if args.type and item["type"] not in args.type:
            continue
        loc = location(item)
        commits = ", ".join(commit_label(state, c) for c in item.get("commits", [])[:MAX_INLINE])
        print(f"{item['status']:8} {item['id']}  {loc or ''}  {commits}".rstrip())


def cmd_show(ctx, args):
    state = load_state(ctx)
    target = load_json(ctx.target_inv_path) if ctx.target_inv_path.exists() else None
    for id_ in find_items(state, args.items, all_matches=True):
        show_item(ctx, state, state["items"][id_], args.context,
                  target if args.fmt_source else None)
        print()


def show_item(ctx, state, item, context, target):
    print(f"== {item['id']} [{item['status']}]")
    if item.get("note"):
        print(f"note: {item['note']}")
    since = item.get("carriedSince") if item.get("carried") else item.get("deferredSince")
    if since:
        print(f"deferred in the review up to {since[:12]}")
    if item["type"] == "commit":
        print(f"commit {item['commit'][:12]} {item['author']} {item['date']}: {item['title']}")
        if item.get("pr"):
            print(PR_URL.format(item["pr"]))
        print("formatter files: " + ", ".join(item["fmtFiles"]))
        print(f"diff: jj diff --git -r {item['commit'][:12]}")
        return
    (path, lines), (ref_path, ref_lines) = item_paths(item)
    if path:
        print(f"source: {path}:{lines[0] if lines else '?'}"
              + (f" (reference: {ref_path}:{ref_lines[0]})" if ref_lines else ""))
    for k in ["declType", "categories", "behavior", "refBehavior", "fmtDecl", "fmtPriority",
              "refFmtDecl", "refFmtPriority"]:
        if item.get(k) not in (None, []):
            print(f"{k}: {item[k]}")
    if item.get("kinds"):
        print("kinds:")
        for k in item["kinds"]:
            f = item.get("fmts", {}).get(k, "-")
            print(f"  {k}" + (": NO FORMATTER" if f is None else "" if f == "-" else
                              f": {f['decl']} (provider priority {f['priority']})"))
    if item.get("affected") is not None:
        a = item["affected"]
        print(f"affected kinds ({len(a)}): " + ", ".join(a[:40]) + (" ..." if len(a) > 40 else ""))
    if item["type"] == "tokens":
        print("added tokens: " + " ".join(repr(t) for t in item["added"]))
        print("removed tokens: " + " ".join(repr(t) for t in item["removed"]))
    if item.get("count"):
        print(f"occurrences: {item['count']}")
    for loc in item.get("locations", []):
        print(f"  {loc}")
    if item.get("message"):
        print(item["message"])
    if item.get("commits"):
        how = " (commits that touch the file)" if item.get("commitsByFile") else ""
        print(f"commits{how}:")
        for c in item["commits"]:
            info = state["commits"].get(c, {})
            pr = f" {PR_URL.format(info['pr'])}" if info.get("pr") else ""
            local = " [local]" if info.get("local") else ""
            print(f"  {c[:12]} {info.get('author', '')} {info.get('date', '')}: "
                  f"{info.get('title', '')}{pr}{local}")
    if item.get("sourceChanged") is False:
        print("The source text is unchanged. The elaborated definition changed, for example "
              "because a declaration or instance that it uses changed.")
    cur = source_lines(ctx, None, path, lines)
    old = source_lines(ctx, ctx.reference, ref_path, ref_lines)
    if cur is not None and old is not None:
        diff = list(difflib.unified_diff(old, cur, f"reference/{ref_path}", f"current/{path}",
                                         lineterm="", n=context))
        print("\n".join(diff) if diff else "(source text unchanged)")
    elif cur is not None:
        print(f"--- current source ({path}:{lines[0]}):")
        print("\n".join(cur))
    elif old is not None:
        print(f"--- reference source ({ref_path}:{ref_lines[0]}):")
        print("\n".join(old))
    if target is None or item["type"] == "fmt-changed":
        return
    fmt_decls = {f["decl"] for f in item.get("fmts", {}).values() if f}
    if item.get("fmtDecl"):
        fmt_decls.add(item["fmtDecl"])
    for decl in sorted(fmt_decls):
        info = target["fmts"].get(decl)
        if not info:
            print(f"formatter {decl}: generic or derived from the syntax declaration")
            continue
        fpath = module_file(info["module"])
        src = source_lines(ctx, None, fpath, info["lines"])
        print(f"--- formatter {decl} ({fpath}:{info['lines'][0] if info['lines'] else '?'}):")
        if src:
            print("\n".join(src[:MAX_FMT_LINES]))
            if len(src) > MAX_FMT_LINES:
                print(f"... ({len(src) - MAX_FMT_LINES} more lines)")


def cmd_verdict(ctx, args):
    state = load_state(ctx)
    ids = find_items(state, args.items)
    for id_ in ids:
        item = state["items"][id_]
        item["status"] = args.status
        if args.note is not None:
            item["note"] = args.note
        item["verdictFingerprint"] = item["fingerprint"]
        item["verdictDate"] = today()
        print(f"{args.status:8} {id_}")
    save_state(ctx, state)


def cmd_missing(ctx, args):
    state = load_state(ctx)
    notes = state.get("missingNotes", {})
    for k, v in sorted(state["missing"].items(), key=lambda kv: (kv[1]["module"] or "", kv[0])):
        if args.module and not (v["module"] or "").startswith(args.module):
            continue
        n = notes.get(k, {})
        if n.get("exempt") and not args.all:
            continue
        if v.get("generic") and not args.all:
            continue
        if args.unmatched and v.get("refs"):
            continue
        path = module_file(v["module"])
        loc = f"{path}:{v['lines'][0]}" if path and v["lines"] else "-"
        cats = ",".join(v["categories"]) or "-"
        extra = (" [exempt]" if n.get("exempt") else "") + (" [generic]" if v.get("generic") else "")
        if v.get("refs"):
            extra += " matched in " + ", ".join(v["refs"][:MAX_INLINE])
        if n.get("note"):
            extra += f" -- {n['note']}"
        print(f"{k}  ({cats})  {loc}{extra}")


def cmd_missing_note(ctx, args):
    state = load_state(ctx)
    notes = state.setdefault("missingNotes", {})
    for k in args.kinds:
        if k not in state["missing"] and k not in notes:
            sys.exit(f"error: '{k}' is not in the list of kinds without a formatter")
        if args.clear:
            notes.pop(k, None)
            continue
        n = notes.setdefault(k, {})
        if args.note is not None:
            n["note"] = args.note
        if args.exempt is not None:
            n["exempt"] = args.exempt
    save_state(ctx, state)


def cmd_lint(ctx, args):
    """Runs the `linter.fmt.missing` linter on the core files that changed since the reference."""
    state = load_state(ctx)
    check_build(ctx, args.allow_stale)
    ref, target = state["reference"]["commit"], state["target"]["commit"]
    if args.files:
        files = args.files
    else:
        files = sorted({f for c in commits_in(ctx, f"{ref}..@") for f in c["files"]
                        if f.endswith(".lean") and re.match(r"src/(Init|Std|Lean|lake/Lake)(/|\.lean)", f)
                        and (ctx.root / f).exists()})
    if not files:
        print("No core files changed since the reference.")
        return
    out = ctx.work / "lint"
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    (out / "files.txt").write_text("\n".join(files) + "\n")
    cmd = ["bash", str(ctx.root / "script" / "missing-fmts.sh"), str(ctx.stage), str(out),
           str(args.jobs), str(out / "files.txt")]
    if shutil.which("systemd-run") and not args.no_scope:
        cmd = ["systemd-run", "--user", "--scope", "-q", "-p", f"MemoryMax={args.mem}",
               "-p", "MemorySwapMax=0", *cmd]
    print(f"Linting {len(files)} files with {args.jobs} jobs ...", file=sys.stderr)
    subprocess.run(cmd, cwd=ctx.root, check=False)
    live, usage = parse_lint(out, files)
    lint_state = {"items": {i: it for i, it in state["items"].items() if it["type"] in LINT_TYPES}}
    merge_items(lint_state, live)
    state["items"] = {i: it for i, it in state["items"].items() if it["type"] not in LINT_TYPES}
    state["items"].update(lint_state["items"])
    state["lint"] = {"target": target, "date": today(), "files": len(files),
                     "missingUsage": usage}
    save_state(ctx, state)
    print(f"Lint items: {len(live)}. Missing-formatter warnings for "
          f"{len(usage)} kinds. Logs: {out}")


def parse_lint(out, files):
    warn = re.compile(r"^(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+): warning: (?P<msg>.*)$")
    incomplete = re.compile(r"Auto-formatter (?:(?P<decl>\S+) )?for syntax kind (?P<kind>\S+) is incomplete")
    missing = re.compile(r"no auto-formatter registered for syntax kind (?P<kind>\S+)")
    items, usage = {}, {}
    for f in files:
        log = out / (f + ".log")
        if not log.exists():
            continue
        text = log.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines()
        for i, line in enumerate(lines):
            m = warn.match(line)
            if not m:
                continue
            loc = f"{m['file']}:{m['line']}"
            msg = m["msg"]
            if (mi := incomplete.search(msg)):
                id_ = f"fmt-incomplete:{mi['kind']}"
                it = items.setdefault(id_, {"id": id_, "type": "fmt-incomplete", "name": mi["kind"],
                                            "kinds": [mi["kind"]], "fmtDecl": mi["decl"],
                                            "count": 0, "locations": []})
                it["count"] += 1
                if len(it["locations"]) < 5:
                    it["locations"].append(loc)
            elif (mm := missing.search(msg)):
                usage.setdefault(mm["kind"], []).append(loc)
            elif "The auto-formatter failed" in msg:
                id_ = f"fmt-failure:{loc}"
                detail = "\n".join(lines[i + 1:i + 4]).strip()
                items[id_] = {"id": id_, "type": "fmt-failure", "name": loc, "message": detail,
                              "locations": [loc]}
    for it in items.values():
        if it["type"] == "fmt-incomplete":
            it["locations"].sort()
        it["fingerprint"] = fingerprint(it)
    usage = {k: {"count": len(v), "example": sorted(v)[0]} for k, v in usage.items()}
    return items, usage


def cmd_advance(ctx, args):
    state = load_state(ctx)
    dropped, reopened = refresh_state(ctx, state, state["target"]["commit"], args.allow_stale)
    open_items = [i for i in state["items"].values() if i["status"] in OPEN_STATUSES]
    if open_items and not args.force:
        save_state(ctx, state)
        sys.exit(f"error: {len(open_items)} items are open: "
                 + ", ".join(i["id"] for i in open_items[:10])
                 + ". Give them a verdict, or pass --force to carry them into the next review.")
    if state["target"].get("local") and not args.allow_local:
        save_state(ctx, state)
        sys.exit("error: the build includes local changes that are not in the target: "
                 + ", ".join(c["commit"][:12] for c in state["target"]["local"])
                 + ". Their syntax and formatters become part of the reference. Pass --allow-local "
                 "if they will land in master (for example, fixes with an open PR).")
    items = list(state["items"].values())
    counts = {s: sum(1 for i in items if i["status"] == s) for s in STATUSES}
    entry = {
        "date": today(),
        "from": {k: state["reference"][k] for k in ("commit", "title", "date")},
        "to": {k: state["target"][k] for k in ("commit", "title", "date")},
        "commitCount": state["target"]["commitCount"],
        "counts": {s: n for s, n in counts.items() if n},
        "local": state["target"].get("local", []),
        "notes": [{"id": i["id"], "status": i["status"], "note": i["note"]}
                  for i in sorted_items(items) if i.get("note")],
    }
    if args.summary:
        entry["summary"] = args.summary
    state.setdefault("log", []).append(entry)
    write_inventory(ctx.ref_inv_path, load_json(ctx.target_inv_path),
                    {"commit": state["target"]["commit"], "date": today()})
    absorbed = state.setdefault("absorbed", {})
    for i in items:
        if i.get("landedFrom"):
            absorbed.pop(i["landedFrom"], None)
    for c in state["target"].get("local", []):
        absorbed.setdefault(c["change"], {"title": c["title"], "reviewed": today()})
    keep = {}
    for i in items:
        if i["status"] in ["deferred", *OPEN_STATUSES]:
            i["carried"] = True
            i.setdefault("carriedSince", state["target"]["commit"])
            keep[i["id"]] = i
    state["items"] = keep
    state["commits"] = {c: v for c, v in state["commits"].items()
                        if any(c in i.get("commits", []) for i in keep.values())}
    state["reference"] = {k: state["target"][k] for k in ("commit", "title", "date")}
    state["reference"]["reviewed"] = today()
    state["target"] = dict(state["reference"], refreshed=today(), commitCount=0,
                           local=state["target"].get("local", []))
    state.pop("lint", None)
    save_state(ctx, state)
    print(f"The reference is now {state['reference']['commit'][:12]} "
          f"({state['reference']['title']}). {len(keep)} items are carried into the next review.")


def cmd_render(ctx, args):
    state = load_state(ctx)
    render(ctx, state)


def cmd_status(ctx, args):
    summarize(load_state(ctx))


# --- rendering ---------------------------------------------------------------------------------

BEGIN = "<!-- fmt-review: generated, begin. Edit with fmt_review.py; edits here are lost. -->"
END = "<!-- fmt-review: generated, end. Free-form notes below this line are kept. -->"


def sorted_items(items):
    def key(i):
        t = TYPE_ORDER.index(i["type"]) if i["type"] in TYPE_ORDER else len(TYPE_ORDER)
        return (t, i.get("module") or "", i["id"])
    return sorted(items, key=key)


def location(item):
    path, lines = item_paths(item)[0]
    if item["type"] == "commit":
        return None
    if item.get("locations"):
        return item["locations"][0]
    if path and lines:
        return f"{path}:{lines[0]}"
    ref_path, ref_lines = item_paths(item)[1]
    if ref_path and ref_lines:
        return f"(removed) {ref_path}:{ref_lines[0]}"
    return None


def md_link(ctx, loc):
    if not loc:
        return ""
    removed = loc.startswith("(removed) ")
    loc = loc.removeprefix("(removed) ")
    path, _, line = loc.partition(":")
    name = Path(path).name + (f":{line}" if line else "")
    link = f"[{name}]({ctx.rel(path)}{'#L' + line if line else ''})"
    return ("removed, was " if removed else "") + link


def commit_label(state, c, md=False):
    info = state.get("commits", {}).get(c, {})
    if info.get("pr"):
        return f"[#{info['pr']}]({PR_URL.format(info['pr'])})" if md else f"#{info['pr']}"
    if info.get("local"):
        change = info.get("change", c)[:12]
        return f"local change `{change}`" if md else f"local:{change}"
    return f"`{c[:12]}`" if md else c[:12]


def code(s):
    return f"`{s}`" if "`" not in s else f"``{s}``"


def kinds_cell(item):
    if item["type"] == "commit":
        return esc(item["title"])
    if item["type"] == "tokens":
        parts = []
        if item["added"]:
            parts.append("added " + " ".join(code(t) for t in item["added"][:8]))
        if item["removed"]:
            parts.append("removed " + " ".join(code(t) for t in item["removed"][:8]))
        return "; ".join(parts)
    if item["type"] == "combinator-changed":
        a = item.get("affected", [])
        return f"used by {len(a)} kinds" + (": " + ", ".join(code(k) for k in a[:MAX_INLINE])
                                            + (" …" if len(a) > MAX_INLINE else "") if a else "")
    cells = []
    fmts = item.get("fmts", {})
    for k in item.get("kinds", [])[:MAX_INLINE]:
        f = fmts.get(k, "-")
        if item["type"] in ("fmt-added", "fmt-replaced"):
            cells.append(f"{code(k)} → {code(item['fmtDecl'])}")
        elif item["type"] == "fmt-removed":
            cells.append(f"{code(k)}, was {code(item['refFmtDecl'])}")
        elif f is None:
            cells.append(f"{code(k)} → **no formatter**")
        elif f == "-":
            cells.append(code(k))
        else:
            cells.append(f"{code(k)} → {code(f['decl'])}")
    more = len(item.get("kinds", [])) - MAX_INLINE
    if more > 0:
        cells.append(f"+{more} more")
    if item["type"] == "fmt-incomplete":
        cells.append(f"{item['count']} occurrences")
    if item["type"] == "fmt-failure":
        cells.append(esc(item["message"].splitlines()[0] if item["message"] else ""))
    return "<br>".join(cells)


def esc(s):
    return (s or "").replace("|", "\\|").replace("\n", " ")


def item_table(ctx, state, items):
    rows = ["| Status | Item | Location | Kinds → formatter | Commits | Note |",
            "|---|---|---|---|---|---|"]
    for i in items:
        commits = i.get("commits", [])
        cl = ", ".join(commit_label(state, c, md=True) for c in commits[:MAX_INLINE])
        if len(commits) > MAX_INLINE:
            cl += f" +{len(commits) - MAX_INLINE}"
        if i.get("commitsByFile") and commits:
            cl += " (file)"
        name = code(i["id"])
        if i.get("sourceChanged") is False:
            name += " (source unchanged)"
        rows.append(f"| {i['status']} | {name} | {md_link(ctx, location(i))} | {kinds_cell(i)} "
                    f"| {cl} | {esc(i.get('note', ''))} |")
    return rows


def render(ctx, state):
    ref, tgt = state["reference"], state["target"]
    items = sorted_items(state["items"].values())
    live = [i for i in items if not i.get("carried")]
    carried = [i for i in items if i.get("carried")]
    open_ = [i for i in live if i["status"] in OPEN_STATUSES]
    decided = [i for i in live if i["status"] not in OPEN_STATUSES]
    counts = {s: sum(1 for i in items if i["status"] == s) for s in STATUSES}
    out = [
        "# Formatter review",
        "",
        BEGIN,
        "",
        "This file tracks the changes to parsers and formatters in `master` since the last manual "
        "review of the auto-formatter. The `fmt-review` skill (`.claude/skills/fmt-review/SKILL.md`) "
        "gives the procedure. `fmt-review.json` holds the same data for tools.",
        "",
        "| | |",
        "|---|---|",
        f"| Reference (last review) | `{ref['commit'][:12]}` {esc(ref['title'])} "
        f"({ref['date']}), reviewed {ref.get('reviewed', '?')} |",
        f"| Target (last refresh) | `{tgt['commit'][:12]}` {esc(tgt['title'])} ({tgt['date']}), "
        f"refreshed {tgt.get('refreshed', '?')} |",
        f"| Commits since the reference | {tgt.get('commitCount', 0)} |",
        f"| Local changes in the build | "
        + (", ".join(f"change `{c.get('change', c['commit'])[:12]}` {esc(c['title'])}"
                     for c in tgt.get("local", [])) or "none") + " |",
        f"| Items | " + (", ".join(f"{n} {s}" for s, n in counts.items() if n) or "none") + " |",
        f"| Syntax without a formatter | {missing_counts(state)}, of "
        f"{state.get('kindCount', '?')} kinds |",
    ]
    lint = state.get("lint")
    if lint:
        stale = "" if lint["target"] == tgt["commit"] else " (older target: run `lint` again)"
        out.append(f"| Lint of changed files | {lint['files']} files on {lint['date']}{stale} |")
    else:
        out.append("| Lint of changed files | not run for this target |")
    out += ["", f"## Open items ({len(open_)})", ""]
    out += item_table(ctx, state, open_) if open_ else ["None."]
    out += ["", f"## Decided items of this review ({len(decided)})", ""]
    out += item_table(ctx, state, decided) if decided else ["None."]
    out += ["", f"## Items carried from earlier reviews ({len(carried)})", ""]
    out += item_table(ctx, state, carried) if carried else ["None."]

    notes = state.get("missingNotes", {})
    usage = (lint or {}).get("missingUsage", {})
    missing = state["missing"]
    exempt = sorted(k for k in missing if notes.get(k, {}).get("exempt"))
    generic = sorted(k for k, v in missing.items() if v.get("generic") and k not in exempt)
    shown = {k: v for k, v in missing.items() if k not in exempt and k not in generic}
    unmatched = {k: v for k, v in shown.items() if not v.get("refs")}
    matched = {k: v for k, v in shown.items() if v.get("refs")}
    out += ["", f"## Syntax without a formatter ({len(shown)})", "",
            f"These syntax node kinds have no formatter. Where such a node reaches `fmt`, the "
            f"output keeps its input layout. The list leaves out {state.get('privateKinds', 0)} "
            f"private kinds (`local` syntax, which cannot have a formatter), {len(generic)} "
            f"generic kinds and {len(exempt)} exempt kinds."
            + (" A count shows the uses in the linted files." if usage else ""),
            "", f"### Not matched by a formatter ({len(unmatched)})", "",
            "No formatter code mentions these kinds. They need a formatter of their own.", ""]

    def module_groups(entries, refs):
        by_module = {}
        for k, v in entries.items():
            by_module.setdefault(v["module"], []).append(k)
        for module in sorted(by_module):
            ks = sorted(by_module[module])
            path = module_file(module)
            out.append(f"- [{module}]({ctx.rel(path)}) ({len(ks)}):")
            for k in ks:
                v = missing[k]
                line = f"#L{v['lines'][0]}" if v["lines"] else ""
                label = f"[{code(k)}]({ctx.rel(path)}{line})"
                cats = f" ({', '.join(v['categories'])})" if v["categories"] else ""
                n = usage.get(k, {}).get("count", 0)
                use = f", {n} use{'s' if n != 1 else ''} in linted files" if n else ""
                by = ""
                if refs:
                    r = v["refs"]
                    by = (", in " + ", ".join(code(x) for x in r[:MAX_INLINE])
                          + (f" +{len(r) - MAX_INLINE}" if len(r) > MAX_INLINE else ""))
                note = f" — {esc(notes[k]['note'])}" if notes.get(k, {}).get("note") else ""
                out.append(f"  - {label}{cats}{use}{by}{note}")

    module_groups(unmatched, refs=False)
    out += ["", f"### Matched by the formatter of other syntax ({len(matched)})", "",
            "The code of another formatter mentions these kinds, usually in an antiquotation "
            "pattern of the parent syntax. Such a formatter handles the node without `fmt`. A node "
            "in another place keeps its input layout.", ""]
    module_groups(matched, refs=True)
    if generic:
        out += ["", "Generic kinds, which no parser declaration defines (`ident`, `group`, the "
                "`token.*` kinds of non-reserved symbols and others). They are not parsers of "
                "their own: " + ", ".join(code(k) for k in generic)]
    if exempt:
        out += ["", "Exempt kinds: " + ", ".join(
            f"{code(k)}" + (f" ({esc(notes[k]['note'])})" if notes[k].get("note") else "")
            for k in exempt)]

    out += ["", "## Review history", ""]
    log = state.get("log", [])
    if log:
        out += ["| Date | Reference → target | Commits | Items | Summary |", "|---|---|---|---|---|"]
        for e in reversed(log):
            counts = ", ".join(f"{n} {s}" for s, n in e["counts"].items()) or "none"
            out.append(f"| {e['date']} | `{e['from']['commit'][:12]}` → `{e['to']['commit'][:12]}` "
                       f"| {e['commitCount']} | {counts} | {esc(e.get('summary', ''))} |")
    else:
        out.append("No completed review yet.")
    out += ["", END]

    notes_text = "\n## Notes\n\n"
    if ctx.md_path.exists():
        old = ctx.md_path.read_text(encoding="utf-8")
        if END in old:
            notes_text = old.split(END, 1)[1]
    ctx.md_path.write_text("\n".join(out) + notes_text, encoding="utf-8")


# --- main --------------------------------------------------------------------------------------

def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--dir", help="directory of the state files (default: the repository root)")
    p.add_argument("--stage", help="the Lean stage to use (default: build/release/stage1)")
    sub = p.add_subparsers(dest="cmd", required=True)

    s = sub.add_parser("init", help="start tracking with a reference commit")
    s.add_argument("--reference", default="master")
    s.add_argument("--force", action="store_true")
    s.add_argument("--allow-stale", action="store_true")
    s.set_defaults(fn=cmd_init)

    s = sub.add_parser("refresh", help="recompute the items for the current build")
    s.add_argument("--target", default="master")
    s.add_argument("--allow-stale", action="store_true")
    s.set_defaults(fn=cmd_refresh)

    s = sub.add_parser("status", help="print a summary")
    s.set_defaults(fn=cmd_status)

    s = sub.add_parser("list", help="list the items")
    s.add_argument("--status", nargs="+", choices=STATUSES)
    s.add_argument("--type", nargs="+", choices=TYPE_ORDER)
    s.add_argument("--open", action="store_true", help="only pending and fix items")
    s.set_defaults(fn=cmd_list)

    s = sub.add_parser("show", help="show the details and the source diff of items")
    s.add_argument("items", nargs="+", help="item ids, unique substrings or globs")
    s.add_argument("--context", type=int, default=3)
    s.add_argument("--no-fmt-source", dest="fmt_source", action="store_false",
                   help="do not print the source of the formatters of the kinds")
    s.set_defaults(fn=cmd_show)

    s = sub.add_parser("verdict", help="record a verdict")
    s.add_argument("items", nargs="+", help="item ids, unique substrings or globs")
    s.add_argument("--status", required=True, choices=STATUSES)
    s.add_argument("--note")
    s.set_defaults(fn=cmd_verdict)

    s = sub.add_parser("missing", help="list the kinds without a formatter")
    s.add_argument("--module", help="module prefix")
    s.add_argument("--all", action="store_true", help="include exempt and generic kinds")
    s.add_argument("--unmatched", action="store_true",
                   help="only the kinds that no formatter code mentions")
    s.set_defaults(fn=cmd_missing)

    s = sub.add_parser("missing-note", help="annotate kinds without a formatter")
    s.add_argument("kinds", nargs="+")
    s.add_argument("--note")
    g = s.add_mutually_exclusive_group()
    g.add_argument("--exempt", dest="exempt", action="store_true", default=None,
                   help="the kind does not need a formatter of its own")
    g.add_argument("--no-exempt", dest="exempt", action="store_false")
    s.add_argument("--clear", action="store_true")
    s.set_defaults(fn=cmd_missing_note)

    s = sub.add_parser("lint", help="run linter.fmt.missing on the files changed since the reference")
    s.add_argument("--jobs", type=int, default=16)
    s.add_argument("--mem", default="30G", help="MemoryMax of the systemd scope")
    s.add_argument("--no-scope", action="store_true")
    s.add_argument("--files", nargs="+")
    s.add_argument("--allow-stale", action="store_true")
    s.set_defaults(fn=cmd_lint)

    s = sub.add_parser("advance", help="complete the review: make the target the new reference")
    s.add_argument("--force", action="store_true", help="carry open items into the next review")
    s.add_argument("--allow-local", action="store_true")
    s.add_argument("--summary", help="one line for the review history")
    s.add_argument("--allow-stale", action="store_true")
    s.set_defaults(fn=cmd_advance)

    s = sub.add_parser("render", help="write fmt-review.md again")
    s.set_defaults(fn=cmd_render)

    args = p.parse_args()
    ctx = Ctx(args.dir, args.stage)
    ctx.reference = None
    args.fn(ctx, args)


if __name__ == "__main__":
    main()
