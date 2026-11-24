"""Unit tests of the item logic of fmt_review.py. Run: python3 test_fmt_review.py"""
import sys
sys.path.insert(0, str(__import__("pathlib").Path(__file__).resolve().parent))
import fmt_review as f

local = {"commit": "a" * 40, "change": "k" * 32, "author": "x", "date": "2026-11-24",
         "title": "fix: formatter for foo", "pr": None, "files": ["src/Lean/Fmt/Formatters/X.lean"]}
landed = {"commit": "b" * 40, "change": "l" * 32, "author": "x", "date": "2026-11-30",
          "title": "fix: formatter for foo (#17000)", "pr": 17000,
          "files": ["src/Lean/Fmt/Formatters/X.lean"]}
other = {"commit": "c" * 40, "change": "m" * 32, "author": "y", "date": "2026-11-30",
         "title": "feat: new layout (#17001)", "pr": 17001, "files": ["src/Lean/Fmt/FmtM/Layouts.lean"]}
unrelated = {"commit": "d" * 40, "change": "n" * 32, "author": "y", "date": "2026-11-30",
             "title": "fix: grind (#17002)", "pr": 17002, "files": ["src/Lean/Meta/Grind.lean"]}
absorbed = {"k" * 32: {"title": "fix: formatter for foo", "reviewed": "2026-11-24"}}

# The absorbed local change gets no item while it is local.
items = f.fmt_commit_items([], [local], absorbed)
assert items == {}, items
# Without the absorbed entry, it is a pending item keyed by its change id.
items = f.fmt_commit_items([], [local], {})
assert list(items) == ["commit:" + "k" * 12], items
# Its landed version starts as `ok`; other formatter commits are pending; others give no item.
items = f.fmt_commit_items([landed, other, unrelated], [], absorbed)
assert sorted(items) == ["commit:" + "b" * 12, "commit:" + "c" * 12], items
state = {"items": {}}
f.merge_items(state, items)
assert state["items"]["commit:" + "b" * 12]["status"] == "ok"
assert "landed version" in state["items"]["commit:" + "b" * 12]["note"]
assert state["items"]["commit:" + "c" * 12]["status"] == "pending"
# A refresh with the same items keeps the verdicts.
items2 = f.fmt_commit_items([landed, other, unrelated], [], absorbed)
f.merge_items(state, items2)
assert state["items"]["commit:" + "b" * 12]["status"] == "ok"

# A carried item that changes again becomes a live, pending item.
carried_state = {"items": {"syntax-changed:A.p": {
    "id": "syntax-changed:A.p", "type": "syntax-changed", "status": "deferred", "note": "later",
    "fingerprint": "old", "verdictFingerprint": "old", "carried": True, "carriedSince": "f" * 40}}}
live = {"syntax-changed:A.p": {"id": "syntax-changed:A.p", "type": "syntax-changed",
                               "fingerprint": "new"}}
f.merge_items(carried_state, live)
it = carried_state["items"]["syntax-changed:A.p"]
assert it["status"] == "pending" and not it.get("carried") and it["deferredSince"] == "f" * 40, it
# A carried item that did not change again stays carried.
carried_state = {"items": {"syntax-changed:A.p": dict(it, carried=True, status="deferred")}}
f.merge_items(carried_state, {})
assert carried_state["items"]["syntax-changed:A.p"]["carried"]

# compute_items on a synthetic pair of inventories.
ref = {"decls": {
    "A.p": {"type": "parser", "module": "A", "lines": [1, 2], "hash": "1", "kinds": ["A.p"]},
    "A.c": {"type": "parser", "module": "A", "lines": [3, 3], "hash": "2", "kinds": []},
    "A.gone": {"type": "descr", "module": "A", "lines": [5, 5], "hash": "3", "kinds": ["A.gone"]},
}, "kinds": {
    "A.p": {"owners": ["A.p"], "categories": ["term"], "private": False,
            "fmt": {"decl": "F.p", "priority": 1000}},
    "A.gone": {"owners": ["A.gone"], "categories": ["term"], "private": False, "fmt": None},
    "A.q": {"owners": [], "categories": [], "private": False, "fmt": {"decl": "F.q", "priority": 1000}},
}, "fmts": {"F.p": {"module": "F", "lines": [1, 4], "hash": "9"},
            "F.q": {"module": "F", "lines": [5, 6], "hash": "8"}},
   "categories": {"term": {"decl": "C.term", "module": "C", "lines": [1, 1], "behavior": "both"}},
   "tokens": ["a", "b"]}
target = {"decls": {
    "A.p": {"type": "parser", "module": "A", "lines": [1, 2], "hash": "1", "kinds": ["A.p"], "deps": ["A.c"]},
    "A.c": {"type": "parser", "module": "A", "lines": [3, 3], "hash": "2x", "kinds": [], "deps": []},
    "A.new": {"type": "descr", "module": "A", "lines": [7, 7], "hash": "4", "kinds": ["A.new"], "deps": []},
}, "kinds": {
    "A.p": {"owners": ["A.p"], "categories": ["term"], "private": False,
            "fmt": {"decl": "F.p", "priority": 1000}},
    "A.new": {"owners": ["A.new"], "categories": ["term"], "private": False, "fmt": None},
    "A.q": {"owners": [], "categories": [], "private": False, "fmt": None},
}, "fmts": {"F.p": {"module": "F", "lines": [1, 5], "hash": "9x"}},
   "categories": {"term": {"decl": "C.term", "module": "C", "lines": [2, 2], "behavior": "both"}},
   "tokens": ["a", "c"]}
items = f.compute_items(ref, target)
assert sorted(items) == sorted([
    "combinator-changed:A.c", "syntax-added:A.new", "syntax-removed:A.gone", "fmt-removed:A.q",
    "fmt-changed:F.p", "tokens"]), sorted(items)
assert items["combinator-changed:A.c"]["affected"] == ["A.p"]
assert items["syntax-added:A.new"]["fmts"] == {"A.new": None}
assert items["tokens"]["added"] == ["c"] and items["tokens"]["removed"] == ["b"]
assert items["fmt-changed:F.p"]["kinds"] == ["A.p"]
missing = f.missing_list(target)
assert sorted(missing) == ["A.new", "A.q"] and missing["A.q"].get("generic")

# parse_lint on a synthetic log.
import tempfile, pathlib
d = pathlib.Path(tempfile.mkdtemp())
(d / "src/Lean").mkdir(parents=True)
(d / "src/Lean/X.lean.log").write_text(
    "src/Lean/X.lean:3:2: warning: Auto-formatter Lean.Fmt.fmtFoo for syntax kind Lean.Parser.Term.foo is incomplete.\n"
    "The syntax at the location has the following form:\n\n(Lean.Parser.Term.foo ...)\n"
    "src/Lean/X.lean:9:0: warning: Auto-formatter Lean.Fmt.fmtFoo for syntax kind Lean.Parser.Term.foo is incomplete.\n"
    "src/Lean/X.lean:12:0: warning: no auto-formatter registered for syntax kind Lean.Parser.Term.bar\n"
    "src/Lean/X.lean:20:0: warning: The auto-formatter failed, so this command was not checked for missing formatters:\n\nsome error\n")
items, usage = f.parse_lint(d, ["src/Lean/X.lean"])
assert sorted(items) == ["fmt-failure:src/Lean/X.lean:20", "fmt-incomplete:Lean.Parser.Term.foo"], items
assert items["fmt-incomplete:Lean.Parser.Term.foo"]["count"] == 2
assert items["fmt-incomplete:Lean.Parser.Term.foo"]["fmtDecl"] == "Lean.Fmt.fmtFoo"
assert usage == {"Lean.Parser.Term.bar": {"count": 1, "example": "src/Lean/X.lean:12"}}, usage
assert "some error" in items["fmt-failure:src/Lean/X.lean:20"]["message"]
print("all tests passed")
