# An LMDB index for ilean data

This document describes the design of [ilean_index.md](ilean_index.md) with LMDB as the store instead of SQLite.
The overall design stays the same, and so do these sections of that document:
- **The problem and the goals:** the costs of the in-memory `References` today, and what the index must do.
- **The data of open files:** the overlay rule, and which process answers which request.
- **Large results:** a query whose result grows with the data needs a size limit or results in parts.
- **The method:** how the numbers were measured.

This document describes what differs with LMDB: the key layout, the transactions, the memory behavior and the failure modes.
All numbers come from the same benchmarks.

Status: design. Nothing of it is implemented.

## The trade-off against SQLite

| | LMDB | SQLite |
|---|---|---|
| Lookup of one ident, core + Mathlib | 3.6 µs | 21 µs |
| Update of the largest module (22227 locations) | 6.4 ms | 60 ms |
| Optimized first start, store work, core + Mathlib | 2.5 s | 8.8 s |
| Optimized first start, store work, 100 times the data | 337 s | 1008 s |
| Heap after all queries | 1 MB | 3 MB |
| Mapped file pages after all queries, 100 times the data | 27.7 GB (the cgroup limit) | 6 MB |
| Index file, core + Mathlib | 532 MB | 290 MB |
| Code of the store in the benchmark | about 740 lines of C++ | about 500 lines of C++ |
| Library code | 0.1 MB | 1.4 MB |

LMDB is faster for every operation and its heap is smaller.
Its costs are the mapped file pages, the need to manage readahead, and more code of its own.
The section [Failure modes](#failure-modes) lists the consequences of the memory map.

## Overview

- **Source of truth:** the `.ilean` files stay the source of truth. Lean and Lake write them as today.
- **Index:** the watchdog keeps a derived index in one LMDB environment, a directory with `data.mdb` and `lock.mdb`. It is the only process that writes it.
- **Readers:** each query uses one read transaction on a snapshot. Readers never wait for the writer.
- **Open files:** each worker writes the data of its own file into an environment of its own (see [Data of open files](#data-of-open-files)).
- **Recovery:** the index is derived data. If its schema version differs, or LMDB reports a damaged file, the watchdog deletes the environment and indexes all ileans again.

## Environment settings

- **Map size:** 1 TiB on Linux and macOS. The map size reserves address space only, and the file grows as data arrives.
  Windows is different (see [Platforms](#platforms)).
- **`MDB_NOSYNC`:** a commit does no `fsync`. After a system crash, the last commits can be missing, but the file stays consistent.
  The hash check at the next start finds the modules whose rows are missing or old, and indexes them again.
- **`MDB_NORDAHEAD`:** required. Without it, the kernel reads ahead around each page fault, and the index thrashed when memory was short (see [Memory](#memory)).
- **`MDB_NOTLS`:** a read transaction is not bound to the thread that created it.
  Lean tasks can continue on another thread, so the binding needs this flag.
- **No `MDB_WRITEMAP`:** with it, a full disk causes `SIGBUS`, and a bug in the process can damage the file.
  Without it, LMDB writes with `pwrite` and keeps the dirty pages of a write transaction on the heap until the commit.
- **Sub-databases and readers:** `mdb_env_set_maxdbs(12)`. `mdb_env_set_maxreaders` must cover all threads of all processes that open the environment, for example 512.
- **One handle per process:** LMDB does not allow a process to open the same environment twice. The watchdog and each worker must share one handle for each environment.

## Key layout

The environment has 12 named sub-databases. All integer ids are 32 bits, and keys store them big-endian, so that the byte order of a key is the numeric order.

| Sub-database | Key | Value | Used by |
|---|---|---|---|
| `meta` | `"counters"` | next string id, next ident id, next module id | writes |
| `str` | string | string id | interning, lookups by name |
| `strr` | string id | string | names in results |
| `ident` | module string id, ident name | ident id | lookup of an ident |
| `identr` | ident id | module string id, ident name | `findAt`, outgoing calls |
| `modname` | module name | module id | lookup of a module |
| `module` | module id | content hash, max span, name, ilean path | module names, hash check |
| `modrefs` | module id | the ident ids, imports, decls and locations of the module | `findAt`, outgoing calls, replace |
| `post` | ident id, module id | the locations of the ident in the module | references, `definitionOf` |
| `decl` | module id, decl name id | range and selection range | incoming calls |
| `impby` | imported module string id, importer module id | import flags | `importedBy` |
| `defs` | ident id | module id, definition range, ident name | workspace symbols |

- **Long keys:** LMDB rejects keys longer than 511 bytes.
  A string longer than 400 bytes gets a key of three parts: its first 391 bytes, the byte `0xFF` and a 64-bit hash of the whole string.
  UTF-8 never contains the byte `0xFF`.
  Readers and writers compare the full string to detect a collision.
- **`post` values:** a packed array of 24-byte records (is definition, start line, start column, end line, end column, parent decl string id).
- **`modrefs` values:** the max span, the ident ids, imports as 8-byte records, decls as 36-byte records,
  and all locations as 28-byte records (the `post` record plus the ident id), sorted by start position.
- **Why `modrefs` exists:** one value holds everything that `findAt` and a replace need, so neither scans `post`.

## Queries

| Request | Access path | Core + Mathlib | 100× |
|---|---|---|---|
| References of an ident | Prefix scan of `post` over the ident id | 3.6 µs for 80 results | 3.4 µs |
| References of `Nat` | The same scan | 1.4 ms for 47k results | 1.3 s for 4.5M results |
| `definitionOf` | One `post` get, then the definition record | 0.6 µs | 0.8 µs |
| `findAt` | Binary search in the `modrefs` value from `line - max_span` | 4.0 µs | 2.1 µs |
| Incoming calls | References, then one `decl` get for each new (module, parent) pair | 0.50 ms for 2005 results | 0.60 ms |
| Outgoing calls | Scan of the `modrefs` value, then `definitionOf` for each callee | 1.0 ms for the largest decl | 0.39 ms |
| Workspace symbols | Full scan of `defs` with the subsequence filter | 35 ms for `sum_comm` | 7.1 s |
| `importedBy` | Prefix scan of `impby` | 16 µs | 10 µs |

- **Zero copy:** a get returns a pointer into the map. The binding must copy each value into Lean objects before the read transaction ends.
- **Disk reads at 100 times the data:** the index file (54 GB) was larger than the memory cgroup (28 GB), so some reads went to disk.
  This explains the times of the scans: the incoming calls of `Nat` took 23 s and the symbol scan 7.1 s.
- **Module names:** as in the SQLite design, readers cache module names on demand and drop the cache above a size limit.

## Writes

### Watcher events

- **One write transaction per module:** read the old `modrefs` value of the module.
  Delete its `post`, `decl` and `impby` entries, and its `defs` entries that point at this module.
  Then intern the strings and idents, and write the new entries.
- **Times:** a median module takes 0.2 ms, the largest module 6.4–8 ms, and a wave of 1078 modules 0.75–2.2 s.
  The p99 per module in the wave rose from 3.7 ms at core and Mathlib size to 27 ms at 100 times the data.
- **Readers during writes:** the p99 of a rare lookup in another thread stayed at about 6 µs.
- **Half-written files:** if an `.ilean` fails to parse, the index keeps the old entries, as in the SQLite design.

### First start

- **Batches:** one write transaction for every 100 modules.
  The dirty pages of an open transaction stay on the heap, so the batch size sets the heap peak:

  | First start | Core + Mathlib | 12× | 100× |
  |---|---|---|---|
  | One module per transaction | 3.4 s | 47 s | 509 s |
  | 100 modules per transaction | 2.5 s | 49 s | 337 s |
  | Heap peak, 100 modules | 35 MB | 35 MB | 40 MB |
  | Mapped file pages, peak | 0.5 GB | 5.9 GB | 16 GB |

  With 1000 modules per transaction, the first start at core and Mathlib size took 2.5 s as well, but the heap peak was 115 MB.
- **Bulk load:** writing all keys of a sub-database in sorted order with `MDB_APPEND` took 2.3 s at core and Mathlib size.
  But it sorts everything in memory, and its peak was 460 MB, which grows with the data.
- **Parsing:** as in the SQLite design, Lean's JSON parser adds 5.4 s at core and Mathlib size.

### Later starts

- **Validation:** scan `module` and compare each stored hash with the `.ilean.hash` file, as in the SQLite design.
  The scan itself took 1.8 ms at core and Mathlib size.

### File size

- **The file only grows:** LMDB reuses freed pages, but it never returns space to the file system.
  In the benchmark, the updates made the file grow from 532 MB to 612 MB at core and Mathlib size.
  At 3.3 times the data, it grew from 1.7 GB to 2.8 GB.
- **Long read transactions:** a read transaction keeps its snapshot, so pages freed after it began cannot be reused while it is open. Thus each request must use a short read transaction.
- **Compaction:** `mdb_env_copy2` with `MDB_CP_COMPACT` writes a compact copy. The watchdog can do this in the background and switch to the copy at a quiet time, or build the index again.

## Data of open files

- **One environment per worker:** each worker writes the data of its own file into an environment of its own, in the session directory of the watchdog.
  Thus each environment has exactly one writer, and no write lock is shared between processes.
- **Readers:** the watchdog and the other workers open these environments read-only to apply the overlay rule.
  Only a few files are open at a time, so this costs a few small maps.
- **Writes:** a new document version replaces the module's entries. An update of the same version merges its locations into the `post` values and into the `modrefs` value.
  For the largest Mathlib module (2932 locations), an incremental update took 0.10 ms and the final write 0.58 ms.
- **Cleanup:** the watchdog deletes the environment of a worker when the worker exits.

## Threads and transactions in Lean

- **Read transactions:** a query begins a read transaction, copies its results into Lean objects, and resets the transaction.
  `mdb_txn_reset` and `mdb_txn_renew` reuse one transaction object, so this costs little.
- **The write transaction:** it must stay on the thread that began it.
  Thus all writes run on one dedicated thread, and a transaction never stays open across a task switch.
- **Where the layout code lives:** the key encoding, the value encodings and the binary search are best written in C, behind a small Lean API that returns arrays.
  A thin binding with one Lean call for each get or put needs more calls for each query, and it must copy each value.

## Memory

- **Heap:** 1 MB after the start and after all queries (after `malloc_trim`), at every size.
  The extra heap of one large query is the size of its results.
  For the incoming calls of `Nat` at 100 times the data, this was 1.3 GB.
- **Mapped file pages:** every page that a query reads stays mapped, and it counts in the RSS until the kernel takes it back.
  At 100 times the data, they grew to 27.7 GB, the limit of the memory cgroup. These pages are clean, so the kernel can drop them without I/O.
- **Low memory, measured in memory cgroups where the page cache counts toward the limit:**
  - **With the default readahead,** the index thrashed at 256 MB. An update phase read 291–562 GB from disk, and the rebuild wave took 47–94 s instead of 2 s.
  - **With `MDB_NORDAHEAD`,** every phase completed down to 64 MB.
    At 64 MB, a rare lookup took 3.3 µs, `findAt` 8 µs, the rebuild wave 6.9 s and the symbol scan 706 ms.
    At 12 times the data and 512 MB, the wave took 2.8 s and the symbol scan 9.1 s.
  - **Scans when memory is short:** without readahead, a scan faults one page at a time.
    At 64 MB, the symbol scan took 706 ms in LMDB against 83 ms in SQLite, which reads with `pread`.

## Failure modes

- **`SIGBUS`:** a read error on a mapped page causes `SIGBUS`, which kills the watchdog. Examples are a failing disk and a network file system that drops out.
  A truncated index file has the same effect.
  The editor then starts a new server, and the new watchdog must check the environment at startup.
  Nothing outside the watchdog may truncate or rewrite the index file.
- **OOM killer:** Linux ranks processes by RSS, including file-backed pages. Thus a watchdog with many GB mapped is a likely victim in an out-of-memory situation. This is so even though most of these pages are reclaimable.
- **Page faults:** a fault on a page that is not resident waits for the disk in the thread that touched it.
  On kernels before 6.4, it also holds the lock of the address space, and other threads that map or unmap memory wait too.
- **`MDB_MAP_FULL`:** the map size limits the file. With 1 TiB on 64-bit Linux and macOS, it is not reached.
  To grow the map, a process must first end all of its transactions.
- **`MDB_READERS_FULL`:** the reader table has a fixed size. A crashed process leaves stale entries, which `mdb_reader_check` removes. The watchdog must call it at startup and from time to time.
- **Damaged file:** if `mdb_env_open` or a transaction reports `MDB_CORRUPTED` or `MDB_INVALID`, the watchdog deletes the environment and indexes again.

## Platforms

- **Linux:** all numbers in this document come from Linux.
- **macOS:** LMDB uses POSIX semaphores instead of robust mutexes there. How a write lock is recovered after a crash was not checked.
  With one writer per environment, a crashed writer is the process that owns the environment, so the risk is small.
- **Windows:** LMDB 0.9 makes the data file as large as the map size when it opens the environment.
  Thus the map size on Windows must start small and grow, which needs a moment without open transactions in the process.
- **WebAssembly:** LMDB needs shared file mappings, which Emscripten does not provide. A WebAssembly build of the server needs another store.

## Integration

- **Library:** vendor `mdb.c`, `midl.c` and their headers (OpenLDAP Public License 2.8, BSD-style, with a notice to keep) and build them as a static library.
  As for SQLite, the library is linked into the Lean libraries and compiled with `-fvisibility=hidden`.
- **Binding:** about 18 functions: environment create, set map size, set max databases, set max readers, open and close,
  transaction begin, commit, abort, reset and renew, database open, get, put, delete, cursor open, get and close, reader check and error string.
- **Own code:** the key layout, the value encodings, the long-key scheme and the queries of this document, about 740 lines of C++ in the benchmark.
  SQLite needs no equivalent code, because its tables and indexes do this.

## Open questions

- **Everything open in the SQLite design:** the location of the index, the cost of the binding, a symbol index and faster parsing.
  LMDB has no full-text search, so a symbol index must be a sub-database of our own.
- **macOS and Windows:** lock recovery on macOS, and the growth of the map size on Windows.
- **Readahead per query:** `madvise` can turn readahead back on for the symbol scan only. This was not measured.
