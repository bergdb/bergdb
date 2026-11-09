# 020-24-17 A graph store

Created 2026-11-09 by Frans Lundberg.

A new user of 2026.4 writes a property graph on BergDB (u17, for coord-1109, round 6 of the
common brief of 020-24). Nodes and edges are Data Objects, with user indexes for adjacency
and for node lookups. The application runs traversals, deletes nodes with all their edges,
changes edge types in bulk, and reads the graph as it was at earlier lookup times. It runs
concurrent writers and readers, a restart and crashes, and checks every result against an
in-memory graph. The question: what does the index API make easy or hard for a graph?

The class path was only the frozen release candidate's
`night/candidate/bergdb-release.jar` (`03ce6ec`). The documentation was read in a clone of
the candidate's repository at `03ce6ec`: README.md, `java/src/overview-pub.html`, the
Javadoc comments of `bergdb.pub` and `bergdb.pub.util`, and releases/next.md. No
implementation code was read. Nothing in BergDB was changed.


## 1. The application

All is in `/Users/f/fl/bench/2026-11-09/app-u17/app/`, about 1,800 lines:

* `GraphApp.java` (1,290 lines): the application, its oracle and its crash child.
* `Probes.java`: the reproductions of U17-2 and U17-3.
* `ScanAfterChurn.java`, `ScanDeletedHub.java` and `ScanTime.java`: those of U17-1.
* `BuildCost.java`, `MemGrowth.java` and `ErrorClose.java`: two more reproductions, and a
  check of `close()` after an `Error`.

`run-small.txt` and `run1.txt` to `run10.txt` are the outputs of `GraphApp`. `probes.txt`,
`scantime-run10.txt`, `buildcost-3.txt` and `gc7.txt` hold the outputs of the others. To
run: `javac -cp bergdb-release.jar -d classes *.java`, then `java -cp
bergdb-release.jar:classes GraphApp DBDIR`. The options:

* `-Dnodes=` and `-Dedges=`: the size of the graph.
* `-Dconc=`: the seconds of the concurrent phase.
* `-Dsd=` and `-Dcache=`: the startup distance and the cache, in MB.
* `-Dretain=`: the retain duration in seconds; 0 keeps every state.
* `-Dnochurn=true`: no index churn in the concurrent phase.

The application:

* **Data.** A node is `/n/ID`, a `Node`: `id`, `name`, a nested `Props` (`city`, `age`),
  and its `outDeg` and `inDeg`. An edge is `/e/SRC-DST`, an `Edge`: a nested `Ends` (`src`,
  `dst`), `type` (one of four), and a weight `w` (a double). An ordered pair has at most one
  edge, and a change of type is a put at the same key.
* **Indexes.** On `/e/`:
  * `out` (long `ends.src`, string `type`, long `ends.dst`) and `in` (long `ends.dst`,
    string `type`, long `ends.src`): three levels, with nested fields.
  * `etype` (string `type`, double `w`). It is built over 8,000 to 120,000 existing edges,
    then deleted and made again as (string `type`, long `ends.src`).
  * `by-w` (double `w`), built while three writers write.
  * `ix2`, deleted and made again every 0.3 to 1 s during the concurrent phase, with the two
    definitions of `etype` in turn.
  * `late` (string `type`, long `ends.dst`), whose build a crash interrupts.

  On `/n/`: `name` (string) and `city-age` (string `props.city`, long `props.age`).
* **Queries.**
  * Out- and in-neighbours, of all types and of one type (`eq(n)`, `eq(n).eq(type)`).
  * Out-neighbours of one type in a range of ids: `from()` and `to()` on level 3.
  * The whole of `out`, `in` backward, and the edges of a type in a weight range.
  * Nodes by name (`eq()`, `prefix()`), and by city and age range.
  * Breadth-first search, to depth 3 for all types and to depth 6 for one type.
  * Shortest path: a BFS of up to 8 hops. Its length is compared with the oracle's, and
    each hop must be an edge of the oracle.
  * Neighbours of neighbours: the nodes at distance exactly 2.
* **Transactions.** Every change is one `rw()`. Its action reads through its environment
  and writes the edges and both end nodes, whose degrees it changes. A node is deleted with
  all its edges in one `rw()`, in this order:
  1. It reads the node through the environment.
  2. It lists the node's edges with `out` and `in` through another connection, since the
     environment cannot scan (U17-2).
  3. It reads each edge through the environment and deletes it.
  4. It changes the degrees of the edges' other ends.
  5. It deletes the node.

  Two bulk changes of an edge type: all "likes" edges become "knows" in one transaction
  (1,900 to 30,000 edges), and "knows" edges become "follows" in `w()` batches of 500.
* **The oracle.** An in-memory graph. The writes of each committed transaction are applied
  to it, and it is copied at 8 times, each with its `Transaction.getTime()`. Every check
  compares the database at a lookup time with the oracle of that time:
  * the primary listings of `/n/` and `/e/`: every value, with the degrees;
  * the whole of `out` and `in`, in order;
  * the queries of 5 to 60 sampled nodes;
  * 2 to 12 traversals.
* **The phases of one run.**
  1. The indexes, then the load, then `etype`'s build.
  2. The queries at the latest state.
  3. Single changes, a delete of the node with the most edges in each of three rounds, and
     renames.
  4. The bulk type changes, and their past state: `etype` at the time before them gives
     every "likes" edge.
  5. `etype` deleted and made again with another definition.
  6. Every earlier time, checked against its copy. At the times before its deletion,
     `etype` has its first definition.
  7. The concurrent phase, 20 to 30 s:
     * 3 writers, each transaction 1 to 3 random operations: add an edge, remove one,
       change a type, delete a node with its edges, or add a node;
     * 2 readers that freeze their lookup time and run a BFS;
     * the build of `by-w`, and the churn of `ix2`;
     * a reader that scans `ix2` slowly at frozen times.
  8. A restart, with every earlier time checked again.
  9. A crash: a child JVM is killed with SIGKILL 0 to 120 ms after its 300th to 600th
     transaction, counted at the syncs. The database is started and checked against the
     oracle, replayed up to the last transaction found (each transaction holds a marker).
     Then the earlier times are checked again.
  10. The same crash while the child builds the index `late`.
* **The concurrent phase is checked afterwards.** Each writer records the times and the
  writes of its transactions. Each reader records its frozen time (`getLookupTime()` after
  the first read, a get or a scan) and its result. The writes are replayed in the order of
  their times, and each result is compared with the replayed graph at its time:
  * each BFS with the BFS of the replayed graph;
  * each scan of `ix2` with the order of the definition that `ix2` had then.

  Within each snapshot, the readers also check that each reached node exists, and that its
  stored `outDeg` equals its entries in `out`. After the phase, the application checks
  three things more:
  * no edge has a deleted end;
  * `by-w` lists every edge in order;
  * the middle transaction's time reads right as an earlier time.

Each run exits with 1 on a wrong result. The eleven runs:

* 300 nodes and 1,500 edges;
* 1,500 nodes and 8,000 edges, three times with the default settings;
* the same graph with a startup distance of 5 MB, a cache of 8 or 50 MB, and a retain
  duration of 3 s or none, six times;
* 20,000 nodes and 120,000 edges.

In all, they made 14.2 million checks, 1.85 million writer transactions in the concurrent
phases, 810,000 BFS by the readers, and 490 slow scans of `ix2` across its deletions. They
also made 22 crashes, 11 of them in the middle of a build. Every check passed.


## 2. The findings

No wrong result came out:

* Every scan, listing and traversal equalled the oracle at the latest state and at earlier
  times, also after a restart and after the crashes.
* Every crash kept a prefix of the transactions, which reached the last synced one. Each
  interrupted build resumed at the start and was right.
* With a retain duration, an earlier time was refused (`LookupTimeNotAvailableException`)
  only when it was before `getFirstAvailableLookupTime()`, and read right otherwise.

One bug of performance came out (U17-1): a scan walks the deleted index entries that follow
its range, which degrades steadily under index churn. The other findings are what a graph
needs and the API does not give. Most severe first:

| ID | Kind | Severity | What | Reproduction |
|-----|------|----------|------|--------------|
| U17-1 | bug | high   | a scan walks the deleted entries after its range      | ScanAfterChurn |
| U17-2 | API | medium | no scan in an rw(): a delete misses a concurrent edge | Probes phantom |
| U17-3 | API | medium | a hub's delete never commits while edges are added    | Probes hub     |
| U17-4 | doc | low    | what a Connection read inside an action reads         | section 3      |
| U17-5 | API | low    | scans read each value: no levels-only scan, no count  | GraphApp       |
| U17-6 | API | low    | an index of one directory; a listing without an end   | section 3      |
| U17-7 | API | low    | no index of an array's elements: node labels          | section 3      |
| U17-8 | doc | low    | a build halves the writers' rate while it runs        | BuildCost      |
| U17-9 | doc | low    | memory() keeps every state in the heap, unbounded     | MemGrowth      |

U17-1 was sent to coord-1109 at once, at about 19:50, as an early warning.


## 3. The findings in detail

### U17-1. A scan walks the deleted entries after its range (bug, high)

In the concurrent phase, the churn of `ix2` came with commit stalls. Transactions of all
three writers took 0.2 to 3.1 s, and in one second of `run9.txt` only 1 transaction
committed in all. The same run without the churn (`run8.txt`, `-Dnochurn=true`) had no
transaction over 200 ms.

`run10.txt` counted the runs of each slow transaction and the time spent in them. Each slow
transaction had a node delete in it and ran once or twice, and nearly all of its time went
to the action's reads. So the cause was a slow read, not conflicts. `ScanTime`, run on a
copy of `run10`'s database, timed the scan `in` eq(n) for every node; it is in
`scantime-run10.txt`:

* The median was 13 µs.
* The scans of the newest nodes, the highest dst values, took 0.7 to 1.65 s each, also in
  a second pass.
* `out` stayed below 70 ms, and below 12 ms in a second pass.

Such a scan reads no entry. What it passes is what follows its range in key order: the
deleted entries of the 18 earlier generations of `ix2`, which sorts after `in` and before
`out`.

The minimal reproduction is `ScanAfterChurn K NAME [DIR]`:

1. A memory database gets 10,000 objects in `/e/` (`src`, `dst`, `type`) and an index `in`
   (long `dst`).
2. K times: create NAME (string `type`), join, `deleteIndex(NAME)`.
3. Time `useIndex("in").eq(v)` for 20 values of v above every dst.

| Creations and deletions of the other index | Empty scan, median | A dst with edges |
|--------------------------------------------|--------------------|------------------|
| none                                        | 0.05 ms | 0.15 ms |
| 40 of "ix2"                                 | 5.9 ms  | 0.09 ms |
| 80 of "ix2"                                 | 14.8 ms | 0.06 ms |
| 160 of "ix2"                                | 30.9 ms | 0.05 ms |
| 40 of "aa" (sorts before "in")              | 0.01 ms | 0.05 ms |
| 40 of "ix2", file database, after a restart | 8.7 ms  | 0.37 ms |

So the scan's time grows linearly with the deleted entries that follow its range. In
memory, each deleted entry costs about 20 ns. In the file database with a cache of 50 MB,
where the nodes were evicted, it cost several µs, which made the seconds above. A restart
does not help. With the default retain duration, the deleted entries stay forever, as the
earlier states need them. Whether a cut removes them, with a retain duration, was not
measured. Which scans are hit depends on the names of the indexes: an index whose name
sorts just before one that is churned. The scans hit are the empty scans, and the last
scan of a range at the end of the index. Many traversals make them, such as an in-edge
lookup of a new node.

Deleted data does the same, more mildly: `ScanDeletedHub` gives a node 100,000 in-edges
and deletes them. After that, the scan `in(499)` of its neighbour in the order took 1.06
ms instead of 0.02 ms, and the empty `in(500)` took 0.96 ms. A graph whose edges come and
go piles up such entries. No wrong result came out.

This is the read path, with no reclaim, so the cause looks like U14-1's: a walk over
deleted keys that never skips them. That is a guess, not checked in the code. Severity
high: a few dozen creations and deletions of an index make reads of up to seconds, and so
transactions of up to seconds, permanently. That is far from the README's "no get or
commit waits more than about 20 ms for BergDB's own work".

Beside it, as U14-1 found: with a retain duration of 3 s, the churn of `ix2` also held
reclaim back. In `run7.txt`, the first available lookup time was 27.9 s old at the end of
the phase, and the directory was 791 MB (`run6.txt`). Without the churn (`run8.txt`) it
was 5.4 s old, and the directory 332 MB.

### U17-2. No index scan in an rw(): a node delete misses a concurrent edge (API, medium)

The natural transaction of a graph is "delete node n and every edge of n". It reads a set
of keys that an index gives. `RwEnvironment` has only `get()` and `exists()`: no
`useIndex()` and no `usePrimary()`. So the action lists the edges outside its read set,
through a `Connection`. Another transaction may add an edge to n after that listing and
commit before the delete. That edge is not deleted, and it is left with a deleted end. The
read set covers the keys read, not the range scanned: a phantom. Nothing in the Javadoc
says so, or how to avoid it. `Action.run()` says "read through env the state that the
writes depend on", which an action cannot do for a scan.

`Probes phantom` sets up this case:

* a memory database with 300 nodes, and `out` and `in` as in the application;
* 3 writers, each of 30,000 `rw()` transactions that read both end nodes and put an edge;
* a deleter of every second node. It lists the node's edges through a second connection,
  then reads and deletes each through the environment.

The two outputs:

    phantom, touch=false: 14241 edges, 22 dangling (an endpoint deleted); delete runs 170 for 150 deletes
    phantom, touch=true: 14219 edges, 0 dangling (an endpoint deleted); delete runs 178 for 150 deletes

The workaround is `touch=true`, the application's protocol:

* Every transaction that adds or removes an edge also writes both end nodes: in the probe
  a version, in the application the degrees.
* The delete reads the node through the environment first.

A concurrent edge change then conflicts with the delete, which runs again. Its new
listing, made after its read time, holds the edge. With this protocol, the application
found no edge with a deleted end in 1.85 million concurrent writer transactions. The cost:
every edge write is also a write of two nodes, and so each well-connected node becomes a
key that many transactions write (U17-3).

Wishes:

* a scan in an `rw()` whose range joins the read set (a predicate or range lock);
* at least, a sentence in `Action` and `RwEnvironment` that a listing made through a
  connection is not in the read set, with the pattern above.

### U17-3. An rw() that reads a hub never commits while edges are added (API, medium)

With U17-2's workaround, the delete of a node with many edges reads the node, and each edge
added to the node writes it. The delete's action is long, as it lists and reads every edge.
So while edges are added at a modest rate, each run meets a conflict, and `rw()` runs the
action again and again. It does not return until the writers stop.

`Probes hub EDGES WRITERS SECONDS` with `-Dpause=MS` sets up this case:

* a memory database with 5,000 nodes, one of them a hub with 3,000 in-edges;
* writers that add an edge to the hub, write both its nodes, then sleep `pause` ms;
* after 0.2 s, a thread that deletes the hub as in U17-2.

| Writers' pause | Edges added to the hub a second | The hub's delete |
|----------------|---------------------------------|------------------|
| 20 ms | about 80     | committed after 0.96 s, 7 runs        |
| 5 ms  | about 240    | not in 15 s, 28 runs; committed after |
| none  | about 43,000 | not in 20 s, 34 runs; committed after |

So a node of a few thousand edges cannot be deleted while a few hundred edges a second are
added to it, in a database that is otherwise idle. `Connection.rw()` says that "under
overload it may never commit". Its example is a long action while other transactions write
more than about 100,000 keys. One hot key that the action reads is enough, at a rate that
is no overload. There is no lock, priority or limit of runs to use instead.

An application can split the delete. It first marks the node "deleting", which the adders
respect, then removes the edges in batches, then deletes the node. That is a protocol of
its own. Wishes:

* a way to make one transaction win, such as an `rw()` that, after N runs, holds off the
  writers of the keys it has read;
* at least, this case in the Javadoc.

### U17-4. What a Connection read inside an action reads (doc, low)

The application's delete reads `useIndex()` through a second connection inside the action,
the only way to scan there (U17-2). The Javadoc of `Action.run()` and of `Connection.rw()`
says that a call of a Connection inside the action "is a transaction of its own, committed
at once, not undone, and made again at each run". That fits a write, and puzzles for a
read.

It does not say at which time such a read reads. It reads at the connection's lookup time,
so at the latest state, not at the action's read time ("the latest state as of its first
read", `RwEnvironment.get()`). It may see writes that the action's reads do not. The
application relies on that: its listing is at or after the action's read time, so the
conflict check covers the gap. A user has to infer it.

A sentence for `Action.run()`: a read through a connection reads at that connection's
lookup time, is not in the transaction's read set, and is the way to scan within an action,
with U17-2's caveat.

### U17-5. A scan reads every entry's value: no levels-only scan, no count (API, low)

The neighbours of a node are a level of `out` (`ends.dst`). But a scan gives only values
(`objects()`) or keys with values (`kvs()`), and each entry reads the edge at its key, to
skip a stale entry and to convert it. So a BFS reads every edge object that it passes.

The rates, measured in one thread after the load, on a loaded F53:

| Graph, cache | Scans of out(n) a second | Entries a second | BFS (depth 3) a second |
|--------------|--------------------------|------------------|------------------------|
| 1,500 nodes, 8,000 edges, 200 MB    | 88,900 | 474,000 | 2,540 |
| 1,500 nodes, 8,000 edges, 8 MB      | 16,800 | 90,000  | 504   |
| 20,000 nodes, 120,000 edges, 100 MB | 8,800  | 53,000  | 208   |

A shortest path search that explores the whole graph of 20,000 nodes takes about 2.3 s:
20,000 scans. A degree needs a full scan, or a counter kept by the application, and that
counter is what makes U17-3's hot keys. Wishes:

* a scan of the entries' levels and keys only: the neighbour ids without the edge objects;
* a count of a scan's range.

### U17-6. An index of one directory; a listing without an end (API, low)

An index holds the values of one directory, not those of its subdirectories. That shapes
the layout of a graph:

* **A per-node layout** (`/adj/N/M` for the edge from N to M) lists a node's edges with
  `usePrimary()`. But no index covers all the edges, so in-edges, edges by type and a
  global weight order need copies.
* **The flat layout** (`/e/`, the application's) is indexed. But `usePrimary()` has
  `startAt()` and no end bound or prefix, so a listing of `/e/N-*` must be stopped by hand.

Also, the three-level `out` (src, type, dst) cannot answer "is there an edge from n to m of
any type": that needs eq on levels 1 and 3 with level 2 open. Here the edge's key answers
it, as a pair has at most one edge; a multigraph needs another index. All of this is as
documented. It is what a graph user meets first.

### U17-7. No index of an array's elements: node labels (API, low)

A node often has several labels or tags. An array field gives no index entry
(`IndexBuilder`, rule 2), so a node with `labels: String[]` cannot be found by a label. The
workaround is a directory with one object for each label and node, written in the node's
transactions. A wish: a multi-valued level, with an entry for each element.

### U17-8. A build halves the writers' rate while it runs (doc, low)

`IndexBuilder.start()` says that a build is paced "so that the application's writers and
readers go on". They go on, at about half their rate. `BuildCost DIR 120000 3` puts 120,000
edges, starts 3 writers of single puts, and after 5 s starts the build of an index on the
same directory. Its output is in `buildcost-3.txt` and `probes.txt`:

* The writers made about 50,000 puts a second before the build, 28,000 falling to 14,000
  during it, and 14,000 after it.
* A control run with no build fell from 58,000 to 22,000 a second, as the directory grew.
* So during the build, the writers ran at about half of the control's rate.
* The build took 38 s and read 702,192 values, against under 2 s for 120,000 values with
  no writers. It reads the values put after it began, up to its last key, as releases/next.md
  says.

A sentence in `IndexBuilder.start()` on the writers' cost would help a user plan a build.

### U17-9. memory() keeps every state in the heap (doc, low)

The first version of `Probes phantom` ran its writers until the deletes ended. With the
deletes' runs again, that took about 30 s, and it failed with `OutOfMemoryError` in a heap
of 1 GB. A memory database keeps its whole stream in the heap, with every earlier state by
default, so it grows with every write, also when the live data stays small. All that
`DatabaseBuilder.memory()` says is: "An in-memory database stream will be used. This option
may be suitable for testing." `MemGrowth` puts one small object at 100 keys over and over:

| Puts | Heap above the start |
|------|----------------------|
| 200,000   | 70 MB  |
| 600,000   | 202 MB |
| 1,000,000 | 332 MB |

A sentence for `memory()`: the stream, with every write, is kept in the heap, and with the
default retain duration it is never cut. A test that writes much sets a retain duration or
uses a directory.

In that failure, the `OutOfMemoryError` left the try-with-resources block as an
`IllegalArgumentException`, "Self-suppression not permitted", with the error as its cause:
`close()` threw the same error instance. `ErrorClose` shows that `close()` of a database
that an `Error` failed returns normally, as `Database` says. The same instance was most
likely the JVM's shared `OutOfMemoryError`, which it throws when the heap is full.
`Database` covers that case ("while the heap stays full, BergDB cannot promise even to fail
cleanly"), so it is not a finding.


## 4. What went well

* **Nested multi-level indexes fit adjacency exactly.** `out` on (`ends.src`, `type`,
  `ends.dst`) answers three questions, with one builder each: the out-neighbours, the
  out-neighbours of a type, and those of a type in a range of neighbour ids. `in` does the
  same backward. The grammar (`eq()` on the leading levels, then `from()`, `to()` or
  `prefix()`) is checked call by call, so a wrong call failed at once, with a clear
  message.
* **Time travel is easy and right.**
  * `freezeLookupTime()`, a first read, then `getLookupTime()`: a reader gets a consistent
    graph for a whole BFS, and the time to check it with.
  * `setLookupTime(t)` with a `Transaction.getTime()` reads the graph as it was.
  * Every earlier time read right, also after a restart and after crashes.
  * Across the deletions and re-creations of `etype` and `ix2` with other definitions, each
    time used its own definition. At the old times, a `from(double)` was taken; at the new
    ones, it was refused. 490 slow scans at frozen times, during which the index was
    deleted and its cleanup ran, all equalled the replay.
* **Transactions are atomic and serializable, as documented.** With U17-2's workaround,
  the degrees stored in the nodes equalled the entries of `out` in every reader's snapshot.
  Every BFS at a frozen time equalled the BFS of the writes, replayed in the order of their
  times: the transaction times are unique and give the commit order.
* **Index builds.**
  * `etype` was built over 120,000 edges in 3.7 s.
  * `by-w` was built in 0.3 to 2.9 s while three writers wrote (16.7 s over 116,000
    edges), and was right.
  * `late`, interrupted by a crash with 1,050 to 3,950 values read, was `BUILDING` with 0
    values read after the start. Then it became active and was right.
* **Crashes.** Each start after SIGKILL kept every transaction up to the last synced one,
  each whole: the marker of the last transaction and the graph agreed. Often it kept more
  after a delay before the kill, such as up to 750 with 600 synced.
* **The Javadoc** answered every question precisely, but those above: the read state of
  an action, the order of entries with equal levels by key, the definition read at the
  lookup time, and the rules for `-0.0` and float.
