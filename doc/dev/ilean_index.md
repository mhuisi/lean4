# A SQLite index for ilean data

This document describes a design that replaces the in-memory `References` of the watchdog with an index in SQLite.
It is based on benchmarks of `References`, SQLite and five other stores (LMDB, libmdbx, RocksDB, LevelDB and DuckDB).
The benchmarks used the ilean data of core and Mathlib, and synthetic data up to 100 times larger.
The section [How the numbers were measured](#how-the-numbers-were-measured) describes the method.

Status: design. Nothing of it is implemented.
[ilean_index_lmdb.md](ilean_index_lmdb.md) describes the same design with LMDB as the store.

## The problem

The watchdog loads every `.ilean` file at startup (`startLoadingReferences`) and keeps all of their data in `References`.
At the size of core and Mathlib (12263 ileans with 4.0M reference locations), this has these costs:

- **Startup:** each start parses all JSON again. This takes 5.4 s at this size and grows linearly with the data.
- **Memory:** the data takes about 550 MB of heap, with string sharing between ileans. At 12 times this size, it took 6.6 GB.
- **Queries:** each query over all modules builds a map of all modules again (`allRefs`, called from `allRefsFor`).
  A lookup of one ident takes about 6 ms at this size and about 0.4 s at 12 times this size.
  The outgoing calls of a decl call `definitionOf?` for each callee, so a large decl takes seconds.
- **Low memory:** in a memory cgroup of 512 MB, `References` did not finish loading.

## Goals

- **Memory:** the RSS of the index stays low and does not grow with the ilean data.
- **Startup:** a start does not load all data again.
- **Open files:** queries see the current data of the files that are open in an editor.
- **Builds:** the index follows the `.ilean` files that Lake writes while the server runs.

## Overview

- **Source of truth:** the `.ilean` files stay the source of truth. Lean and Lake write them as today.
- **Index:** the watchdog keeps a derived index in one SQLite file, and it is the only process that writes this file.
- **Readers:** each reader uses its own connection. In WAL mode, readers never wait for the writer.
- **Open files:** the data of open files goes into a second SQLite file for each watchdog session (see [Data of open files](#data-of-open-files)).
- **Recovery:** the index is derived data. If its schema version differs or the file is damaged, the watchdog deletes the file and indexes all ileans again.

## Schema

```sql
CREATE TABLE str(id INTEGER PRIMARY KEY, s TEXT NOT NULL UNIQUE);
CREATE TABLE module(id INTEGER PRIMARY KEY, name_id INTEGER NOT NULL UNIQUE, hash INTEGER NOT NULL,
  path TEXT NOT NULL, max_span INTEGER NOT NULL, next_seq INTEGER NOT NULL);
CREATE TABLE ident(id INTEGER PRIMARY KEY, mod_id INTEGER NOT NULL, name TEXT NOT NULL, UNIQUE(name, mod_id));
CREATE TABLE ref(ident_id INTEGER NOT NULL, module_id INTEGER NOT NULL, seq INTEGER NOT NULL,
  is_def INTEGER NOT NULL, sl INTEGER NOT NULL, sc INTEGER NOT NULL, el INTEGER NOT NULL, ec INTEGER NOT NULL,
  parent_id INTEGER, PRIMARY KEY(ident_id, module_id, seq)) WITHOUT ROWID;
CREATE INDEX ref_mod ON ref(module_id, sl);
CREATE TABLE decl(module_id INTEGER NOT NULL, name_id INTEGER NOT NULL, rsl INTEGER, rsc INTEGER, rel INTEGER,
  rec INTEGER, ssl INTEGER, ssc INTEGER, sel INTEGER, sec INTEGER, PRIMARY KEY(module_id, name_id)) WITHOUT ROWID;
CREATE TABLE imp(module_id INTEGER NOT NULL, mod_id INTEGER NOT NULL, is_private INTEGER, is_all INTEGER,
  is_meta INTEGER, PRIMARY KEY(module_id, mod_id)) WITHOUT ROWID;
CREATE INDEX imp_by ON imp(mod_id);
```

- **`str`:** holds module names, the module names of idents, decl names and parent decl names.
- **`ident`:** holds the `.const` idents. Ileans contain no local variables, because `Frontend` collects them with `localVars := false`.
- **`ref`:** the table is clustered by `(ident_id, module_id)`, so all references of one ident are one range scan.
  `ref_mod` serves `findAt`, outgoing calls and the deletion of a module.
- **`module.max_span`:** the largest `el - sl` of all locations of the module.
  `findAt` scans `ref_mod` only from `line - max_span` to `line`.
- **Schema version:** `PRAGMA user_version` holds it.

At core and Mathlib size, the file is 290 MB. At 100 times that size, it is 31.5 GB.

## Queries

| Request | Access path | Core + Mathlib | 100× |
|---|---|---|---|
| References of an ident | Prefix scan of the `ref` primary key | 21 µs for 80 results | 21 µs |
| References of `Nat` | The same scan | 12 ms for 47k results | 2.6 s for 4.5M results |
| `definitionOf` | Primary key `(ident_id, module_id)`, `is_def = 1` | 3.3 µs | 3.6 µs |
| `findAt` | `ref_mod` range from `line - max_span` to `line` | 11 µs | 15 µs |
| Incoming calls | References with `LEFT JOIN` of `decl` and `str` | 1.9 ms for 2005 results | 2.0 ms |
| Outgoing calls | `ref_mod` scan of one module, then `definitionOf` for each callee | 3.8 ms for the largest decl | 4.2 ms |
| Workspace symbols | `LIKE` prefilter over `ident`, then the definition row | 49 ms for `sum_comm` | 5.9 s |
| `importedBy` | `imp_by` | 0.1 ms | 0.12 ms |

The times are warm-cache medians from C++. A Lean binding adds the cost of the Lean objects for each result.

- **Workspace symbols:** the fuzzy matcher rejects each word that does not contain the pattern as an ASCII case-insensitive subsequence (`String.charactersIn`).
  SQLite's `LIKE` is also case-insensitive for ASCII only.
  Thus `name LIKE '%s%u%m%\_%c%o%m%m%' ESCAPE '\'` returns a superset of the matches, and the scoring runs in Lean on these candidates.
- **Join order:** the symbol query must fix its join order with `CROSS JOIN`.
  Without statistics from `ANALYZE`, SQLite chose a plan that took 1.7 s instead of 50 ms.
- **Module names:** readers cache module names on demand and drop the cache above a size limit (16384 entries in the benchmark).
  A reader must not load the whole module table, because at 100× it has 1.38M rows.

## Writes

### Watcher events

- **One transaction per module:** for each changed `.ilean`, one transaction deletes the rows of the module and inserts the new rows.
  The deletion uses `ref_mod` for `ref` and the primary keys of `decl` and `imp`.
  Strings and idents are looked up or inserted in SQL, with a cache for the duration of the transaction.
- **Times:** a median module (168 locations) takes 0.5 ms, and the largest module (22227 locations) takes 60 ms.
  A wave of 1078 rebuilt modules takes 3.5 s. These times stayed the same up to 100×.
- **Readers during writes:** during the wave, the p99 of a rare lookup in another thread stayed at about 30 µs.
- **Half-written files:** Lean truncates and rewrites an `.ilean` in place, so the watchdog can read a file that is only half written.
  If the parse fails, the index keeps the old rows and the old hash, and the next watcher event tries again.

### First start

On an empty index, the watchdog indexes all ileans in batches:

- **Batches:** commit every 100 to 1000 modules.
- **Order:** sort the `ref` rows of a batch by primary key before the inserts.
- **Indexes:** create `ref_mod` and `imp_by` after the last batch.
- **Page cache:** if memory is not short, use a page cache of 16 to 64 MB during the first start. After it, return to the default of 2 MB.

Store work at core and Mathlib size, median of three runs:

| First start | Store work | Peak RSS |
|---|---|---|
| One module per transaction | 14.8 s | 14 MB |
| 100 modules per transaction | 12.9 s | 14 MB |
| 1000 modules per transaction | 11.0 s | 14 MB |
| 1000 modules, sorted rows, indexes at the end | 9.6 s | 41 MB |
| The same with a 64 MB page cache | 9.5 s | 176 MB |

- **12 times the data:** the store work fell from 266 s to 151 s with sorted batches, indexes at the end and a 64 MB cache.
  At this size, the larger page cache gave most of the gain.
- **Low memory:** in a memory cgroup of 128 MB, 100 modules per transaction was fastest (17 s instead of 22 s).
  Larger batches and a larger cache were slower there.
- **Cost of large transactions:** they cost no memory, because SQLite writes dirty pages to the WAL when its cache is full.
  They cost disk: with one transaction for all modules, the WAL grew to the size of the database.
- **Remaining time:** most of it goes to the 4M row inserts in SQLite's bytecode interpreter, not to the commits.
  With one row per ident and module and packed locations, the rows drop to 1.3M. This was not measured.
- **Parsing:** Lean's JSON parser needs 5.4 s at this size, and simdjson in C needs 1.0 s.
  With Lean's parser, the first start takes about 15 s.
- **Requests during the first start:** the first start runs in the background, as the load does today, so requests during it see partial data.

### Later starts

- **Validation:** stream the `module` table and compare each stored hash with the `.ilean.hash` file that Lake writes next to each `.ilean`.
  Re-index each changed module, and delete each module whose `.ilean` is gone.
- **New files:** the watchdog already walks the search path for `.ilean` files. A point lookup in `module` for each file finds the new ones.
- **Times:** at core and Mathlib size, the validation takes 38 ms.
  At 100× (1.38M modules), reading the hash files took 25 to 80 s. A manifest of all ilean hashes from Lake removes this cost.
- **Without Lake:** if there is no `.hash` file, use the mtime and the size, or compute the hash.

## Data of open files

A worker knows the current data of its own file only. A request such as "find references" needs the current data of all open files.
Thus the workers share this data through a second SQLite file for each watchdog session:

- **Session file:** it has the same tables as the index, plus `open_module(module, uri, version, is_setup_failure)`.
  The watchdog makes a new session file at startup.
- **Writes:** each worker writes the rows of its own file where it sends `$/lean/ileanInfoUpdate` and `$/lean/ileanInfoFinal` today.
  A new document version replaces the rows of the module, an update of the same version adds rows, and the final notification replaces all rows.
- **Query rule:** take the rows from the index, except for modules that have a session row with a successful setup. Then add the session rows.
  This is the rule of `getModuleRefs?` and `hasRefs` today, in SQL.
- **Cleanup:** a worker that crashes cannot delete its rows. The watchdog deletes them when it detects that the worker exited (`eraseFileWorker`).

The requests go to these processes:

- **The worker of the document:** references, prepare rename, rename and prepare call hierarchy.
  The worker finds the ident in its own info trees, so local variables never leave the worker.
- **The watchdog:** workspace symbols, incoming and outgoing calls, the module hierarchy and `$/lean/waitForILeans`.

What changes:

- **Removed:** the `References` state of the watchdog, the three ilean notifications, `$/lean/queryModule` and `bendLocationLinks`.
  `$/lean/importClosure` stays, because it carries no ilean data.
- **Times:** for the largest Mathlib module (2932 locations), an incremental update into the session file took 0.3 ms and the final write took 6.2 ms.
  Today, the watchdog parses each notification from JSON: 0.2 ms for an update and 2.8 ms for the final notification (313 KB).
- **Rename:** `handleRename` returns `changes?` without document versions, so the client applies its ranges to the current text.
  Thus the worker must answer a rename from the data of the current document version.
- **Not measured:** the cost of the session rows in the queries.

## Settings

- **Journal:** `journal_mode=WAL` and `synchronous=NORMAL`, so a commit does no `fsync`.
  The index is derived data, so a commit that a crash loses costs only a new index of that module.
- **Page cache:** the default of 2 MB for readers, and for the writer outside the first start. No `mmap_size`.
- **Threads:** one connection per thread. Build SQLite with `SQLITE_THREADSAFE=2`.
- **Other writers:** a `busy_timeout` for the writer, in case a second watchdog opens the same index.

## Memory

RSS of the store process, measured in the C++ benchmark:

| | Core + Mathlib | 12× | 100× |
|---|---|---|---|
| Heap after the start | 3 MB | 3 MB | 3 MB |
| Heap after all queries, after `malloc_trim` | 11 MB | 3 MB | 3 MB |
| Mapped file pages | 6 MB | 6 MB | 6 MB |
| Extra heap of the largest query | 13 MB | 108 MB | 1.3 GB |
| `References` today, heap | 550 MB | 6.6 GB | about 53 GB (linear estimate) |

- **Large results:** the extra heap comes from the result of one large query. Examples are the references of `Nat` and the symbol candidates of a short query.
  The server must limit the size of a result or produce it in parts. It must also keep only the top 1000 symbols while it scores them.
- **Freed buffers:** glibc keeps freed result buffers. Without `malloc_trim`, the heap after all queries was 1.1 GB at 100×.
  Lean's allocator was not measured.
- **Low memory:** the benchmark ran SQLite in memory cgroups from 1 GB down to 64 MB, where the page cache counts toward the limit.
  At every limit, SQLite completed the first start, all queries and all updates.
  Its peak RSS was 5 to 40 MB. At 64 MB, a rare lookup took 32 µs and the symbol scan took 83 ms.
- **The watchdog itself:** the Lean process starts at about 100 MB of RSS (19 MB of heap and 85 MB of mapped `libleanshared`). That is more than SQLite needs.

## Why SQLite

| Store | Result |
|---|---|
| `References` today | 550 MB of heap and 5.4 s of parsing at each start at core and Mathlib size. Both grow linearly. It did not load in 512 MB. |
| LMDB | 3 to 10 times faster than SQLite for lookups and writes. Its RSS includes all file pages that it maps: 28 GB at 100×, as much as the cgroup allowed. With its default readahead, it thrashed under memory pressure. It needs `MDB_NORDAHEAD`. |
| libmdbx | Like LMDB. Its writes were slower, and its first start took 500 s instead of 11 s with 128 MB. |
| RocksDB | It keeps the index and filter blocks of all table files on the heap: 688 MB at 100×. Its updates failed with 128 MB. Only one process can write. |
| LevelDB | Small and fast for writes. It failed with 64 MB. Only one process can write. |
| DuckDB | With its default memory limit (80 percent of the memory that it detects), a lookup took 1 to 2 ms at every size. An update of one module took 11 ms at core and Mathlib size and 59 ms at 12 times the data. Scans of large results were as fast as in SQLite or faster. Its heap grew to 1.1 GB at 12 times the data, and its first start took 1.6 hours there. It failed in memory cgroups of 256 MB and below. With a limit of 256 MB, which the benchmark chose, it ran out of memory at 3.3 times the data. |
| SQLite | Constant heap of a few MB at every size, and it worked down to 64 MB. The SQL code is short: about 500 lines in the benchmark, against about 740 lines for the LMDB layout. FTS5 is available for a symbol index. |

## Integration

- **Library:** vendor the SQLite amalgamation (public domain) and build it as a static library that is linked into the Lean libraries.
  This follows the CaDiCaL FFI (#15247). Compile it with `-fvisibility=hidden`, so that user FFI code can link its own SQLite.
- **Binding:** two external object types (connection and statement) with finalizers, and about 12 functions:
  open, close, exec, prepare, bind, step, column, reset, finalize, busy timeout, last insert rowid and error message.
- **Lean API:** a module such as `Lean.Server.IleanIndex` implements the queries and writes of this document.
  The request handlers of the watchdog and the workers call it instead of `References`.

## Open questions

- **Location of the index:** one index per workspace (for example in `.lake/`), or one per user with rows keyed by the ilean hash.
  A per-user index lets projects share the index of a toolchain and of common dependencies.
- **Binding cost:** the cost of the Lean FFI binding for large results.
- **Symbol index:** an FTS5 trigram index for large workspaces, because the full scan takes 6 s at 100×.
- **Parsing:** a binary ilean format or a C parser, to remove the 5.4 s of JSON parsing at core and Mathlib size.
- **Platforms:** Windows and macOS were not measured.

## How the numbers were measured

- **Data:** the ileans of core and Mathlib with its dependencies (12263 files with 4.0M locations).
  For larger data, the benchmark copied the Mathlib part with new module, ident and decl names, and kept one copy of core.
  So references to core idents grow with each copy. The sizes were 1, 3.3, 12 and 100 times core and Mathlib.
- **Stores:** one C++ program ran the same operations against each store, with decoded ilean data and simdjson for parsing.
  `References` ran as a compiled Lean program that calls the real server functions.
  All stores returned identical results, and `References` returned the same result counts.
- **Machine:** Linux with 96 hardware threads, NVMe RAID0 with XFS.
  Each process ran in a memory cgroup of 28 GB without swap, or with the limit that a section names.
- **Runs:** one run per measurement, except where a section names a median.
- **Harness:** the benchmark harness is not part of this repository.
