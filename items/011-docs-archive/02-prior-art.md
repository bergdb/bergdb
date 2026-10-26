BergDB prior art and what seems novel
=====================================

011-02. Moved here from `docs/prior-art.md` on 2026-10-26 (006-07); history, not kept up to date.

Draft 2, 2026-10-12. Written by Claude for Frans Lundberg.
Draft 2 adds Berkeley DB JE (verified), the wandering tree problem (UBIFS,
LogFS, LSB-tree), LeanStore, ForestDB and OrioleDB to section 4, and the
four properties P1 to P4 with sharper claims to section 5.
2026-10-13: added runtime timing and checkpoint terminology in section 5.5.

Closure review: Java status is pinned to `ebe5f77`, 2026-10-13 18:02 CEST;
see [levels.md](04-levels.md). The claims below are research candidates, not
established novelty or implementation guarantees. The review qualifies the
timing/history comparisons and separates prior source-reading records from
the primary-source checks made at closure.

Literature related to BergDB, how BergDB compares, and which parts seem to be
new. Answers a first round of question Q12 (novelty) in
[problem.md](01-problem.md) and checks its list "Prior art to check". Terms
follow [2015-algos.pdf](../../docs/sources/2015-algos.pdf). Each
reference in section 7 says whether it was read, verified, or is from
Claude's own knowledge.


1 Summary
=========

BergDB has three layers, and the literature covers them differently.

1. The index: a multiversion B-tree. Append-only key nodes, time splits and
   space splits, a DAG instead of a tree, and a structure to find the root
   for a lookup time. Closely related mechanisms were published in Easton's
   Write-Once B-tree (WOBT) in 1986, and developed further in the
   Time-Split B-tree (TSB-tree, Lomet and Salzberg 1989) and the Multiversion
   B-tree (MVBT, Becker et al. 1996). These mechanisms alone do not support
   a novelty claim. BergDB developed them from
   the same root: Driscoll, Sarnak, Sleator and Tarjan's persistent data
   structures.

2. The nodes: cache-aware, fixed-size 64-bit klongs, filled append-only and
   searched linearly. Each part has prior art (Masstree, unsorted
   append-only leaves for persistent memory, cache-conscious B-trees). The
   combination with versions in the node, where TIME klongs are interleaved
   with KEY klongs and resolved in the same linear scan, may be new.

3. The storage: self-indexed streams. One append-only stream holds both the
   user transactions and the index. Index nodes are kept dirty in memory and
   each is written only before it would leave the startup section, a bounded
   tail of the stream. Startup reads the tail and reruns its transactions.
   The mechanism is related to ARIES redo points, log-structured file
   systems, UBIFS and Berkeley DB Java Edition, but none of them found so
   far combines all of its properties. This is the best candidate for the
   novel contribution. Pure append-only storage alone is not new (Berkeley
   DB JE, CouchDB, Hyder); the candidate is the combination of four
   properties, P1 to P4 in section 5.3.

The literature on layer 1 provides designs and proof techniques: merges,
the MVBT's version conditions, the TSB-tree's split-policy analysis and
query algorithms. BergDB's append-only representation and deletion rules
need their own adaptation and proof before inheriting those bounds.
BergDB can then present layer 1 as related to known work
and put its claim on layer 3, with layer 2 as a possible second claim.


2 The index: multiversion B-trees
=================================


2.1 Persistent data structures (1986)
-------------------------------------

Driscoll, Sarnak, Sleator and Tarjan, "Making Data Structures Persistent"
(STOC 1986, JCSS 1989), Frans's key reference since 2012. Two methods make a
linked structure partially persistent: fat nodes, where each field keeps all
its values with timestamps, and node copying, where a node gets a few extra
slots for changes and is copied when the slots are full. BergDB's key node
is node copying with a large node: changes are appended as klongs until the
node is full, then the live content is copied to a new node and a pointer
to it is added to the parent. The multiversion B-trees below are the same
idea applied to B-trees on disk. The TSB-tree paper cites Sarnak and
Tarjan's persistent search trees (CACM 1986).


2.2 The Write-Once B-tree (1986)
--------------------------------

Malcolm Easton, "Key-Sequence Data Sets on Indelible Storage", IBM Journal
of Research and Development 30(3), 1986. Not read; described here from
section 2 of the TSB-tree paper, which was read.

Built for write-once (WORM) optical disks, where nothing can be overwritten:

* A node holds its entries in insertion order. An update is the insert of a
  new version with the same key. The last entry for a key wins.
* A full node is split "by current time only" (the current versions are
  copied into one new node) or "by key value and current time" (the
  current versions are copied into two new nodes). The old node stays as
  history. New index entries are appended to the parent. Becker et al.
  (1996, section 5) state the rule: first a version split, then a key split
  if the current entries fill more than a given fraction of the new node,
  for example 2/3.
* Index nodes split the same way. Old and new index nodes point to the same
  children, so "the WOBT is a DAG, not a tree".
* When the root splits, a new root is created, and a list of the successive
  root addresses is kept. Becker et al. describe the new root as holding
  references to the old root and to the two halves of the split, so all
  paths have the same length. BergDB's time-split-2 and space-split-3 do
  the same: the new super root T' points to the old T.
* A lookup as of time T ignores all entries with a time after T and then
  searches as for the latest version.

The mapping to BergDB:

| BergDB (2015-algos, Dag.java)                | WOBT                                          |
|----------------------------------------------|-----------------------------------------------|
| Key node, append-only klongs                 | Node in insertion order, repeated keys        |
| TIME klong, then KEY klongs                  | Entries timestamped with commit time          |
| Time split: copy lastVersion() to N'         | Split by current time only                    |
| Space split: last version into A and B       | Split by key value and current time           |
| Space split if last.size > maxNodeSize / 2   | Key split too if current entries fill > about 2/3 |
| Old node N stays, reachable for old times    | Old node stays on the WORM disk               |
| Dag with shared children                     | "a DAG, not a tree"                           |
| TopDs finds the space root for a time        | List of successive root addresses             |
| Pointer valid in t0, t1)                    | Ignore entries with a time after T            |

The reasons differ. The WOBT appends because the medium cannot be
overwritten. BergDB appends to keep old versions readable without locks and
to keep the in-memory node simple; the stream is append-only for its own
reasons (section 4).

The WOBT's weakness is the one BergDB solved differently: every new entry
is burned to the disk at once, using a whole sector (about 1 KB) for one
record. BergDB keeps dirty nodes in memory and writes whole node versions
later (section 5).


2.3 The Time-Split B-tree (1989)
--------------------------------

David Lomet and Betty Salzberg, "Access Methods for Multiversion Data",
SIGMOD 1989, pages 315 to 324. Read in full on 2026-10-12.

Setting: databases that never delete (financial transactions, medical and
legal records), timestamps are transaction commit times ("rollback
database"), step-wise constant data. Current data on magnetic disk,
history on cheap WORM optical disks, one index over both. The TSB-tree is
the WOBT adapted to this split:

* Key splits of current nodes are done in place, as in a B+-tree; history
  is not copied. This reduces redundancy.
* A time split can use any time T after the node's previous time split,
  not only the current time. The time-split rule: entries with time < T go
  to the historical node, entries with time >= T to the current node, and
  for every key the version valid at T goes to both. Choosing T as the
  time of the last update, for example, avoids copying later inserts into
  the historical node.
* History migrates one node at a time, consolidated, appended to the end of
  the historical store. Historical nodes can have any size, so WORM
  sectors are filled.
* Choosing between a key split and a time split is a cost trade-off: a cost
  function weighs magnetic-disk space against optical-disk space. Only
  inserts in a node: key split. Only updates of one key: time split.
* Index nodes need special rules. A key split may use any key in an index
  entry; entries whose key range strictly contains the split key are copied
  to both nodes, and these are always historical. A time split is allowed
  only at a time before which all entries point to historical nodes;
  otherwise the split would cascade down the tree. Only historical nodes
  have more than one parent.
* Secondary indexes are TSB-trees of (timestamp, secondary key, primary
  key).
* Concurrency: records of uncommitted transactions have no timestamp and
  are never migrated; read-only transactions get a start timestamp and run
  without locks. The paper notes that this holds for any versioning system.

The paper cites POSTGRES (Stonebraker, VLDB 1987) as pioneering
no-overwrite storage with history.

What BergDB does not need: the index-node split rules exist because the
TSB-tree splits current nodes in place on an overwritable disk. BergDB
copies the last version at every level, as the WOBT does, which is simpler
and fits append-only storage.

What BergDB could use: the redundancy analysis and the idea that the split
time and the split type are policy choices with a cost model.


2.4 Follow-ups to the TSB-tree
------------------------------

* Lomet and Salzberg, "The Performance of a Multiversion Access Method",
  SIGMOD 1990. Analyzes space use and redundancy under three split
  policies for data nodes, as summarized by Becker et al. (1996, section
  5):
  * WOBT policy: version split at the current time, then a key split if
    the current entries fill more than a fraction (for example 2/3).
  * Time of last update: version split at the time of the last update, so
    less goes to the historical node, then the same key split rule.
  * Isolated key split: a key split of the whole node, history included, if
    at least a fraction (for example 2/3) of its entries are current;
    otherwise a version split at the current time. Least redundancy, but
    old versions end up spread over both halves, so a range query at an old
    time can cost Theta(N / B) nodes in the worst case.

  BergDB's rule is the WOBT policy with the threshold 1/2. It space-splits
  only the last version, so history is never spread, and it avoids the
  weakness of the isolated key split.
* Lomet and Salzberg, "Exploiting A History Database for Backup", VLDB
  1993. Uses the historical nodes of a TSB-tree as incremental backup,
  related to BergDB's claim that hot backup of an append-only stream is
  trivial.
* Immortal DB: transaction-time support built into Microsoft SQL Server, a
  research prototype by Lomet and others (SIGMOD 2005, ICDE 2006). Old
  versions are kept in history pages chained from current pages.
* Lomet, Hong, Nehme and Zhang, "Transaction Time Indexing with Version
  Compression", PVLDB 1(1), 2008. A TSB-tree in Immortal DB, with delta
  compression between adjacent versions of a record and of index terms,
  while keeping SQL Server's B+-tree concurrency control and recovery.


2.5 Multiversion B-trees with guarantees
----------------------------------------

* Lanka and Mays, "Fully Persistent B+-trees", SIGMOD 1991. Fat-node and
  version-block methods for B+-trees where any version can be updated, not
  only the latest.
* Becker, Gschwind, Ohler, Seeger and Widmayer, "An Asymptotically Optimal
  Multiversion B-tree" (MVBT), VLDB Journal 5(4), 1996. Read in full on
  2026-10-12. Structurally the closest to BergDB, and built on Driscoll et
  al.: the paper calls its version split "comparable to a time split at the
  current time in Lomet and Salzberg (1989)" and to Driscoll's node
  copying. Only the current version can be updated (partial persistence).
  * Entries carry a lifespan [insertion version, deletion version). A
    delete overwrites the deletion version in place in the live node.
    BergDB cannot do that and appends a DELETE klong instead; this changes
    space, not structure.
  * Node capacity b = k * d. The weak version condition: for every version
    i, every node except the roots holds either 0 or at least d entries
    alive at i. This makes a search at any version as cheap as in a B-tree
    of that version.
  * A full node gets a version split: its live entries are copied to a new
    node, and the old node is dead from then on. The strong version
    condition: after a version split, the new node holds between
    (1 + eps) * d and (k - eps) * d live entries, so at least eps * d + 1
    updates are needed before it splits or underflows again. Without it, a
    nearly full copy would split again at once, costing about one node per
    insert. Too many entries (strong version overflow): a key split. Too
    few (strong version underflow): a merge with a copy of the live entries
    of a sibling, then a key split if needed.
  * A delete that leaves a node with fewer than d live entries (weak
    version underflow) triggers a version split and a merge. This is how
    the tree shrinks. Merges propagate up, and the root of the current
    version can be replaced by a smaller one.
  * Several roots, found through a small B-tree over version intervals
    (root*), like TopDs. Its search costs O(log_B p) for p roots; when the
    data was built by inserts only, p is O(log_B N).
  * Bounds, worst case: O(N / B) nodes in total, O(log_B m_i) node accesses
    for an update or exact match at version i, and O(log_B m_i + r / B) for
    a range query returning r entries, where m_i is the number of live
    entries at version i (n_t in problem.md). The constants are high in the
    worst case (11.5 redundant copies per key for b = 25), but the
    experiments measured 1.31 to 1.70.

  BergDB's rule last.size > maxNodeSize / 2 is the overflow half of the
  strong version condition: after a time split, N' is at most half full,
  so about B / 2 klongs must be appended before N' splits again. The
  underflow half and the weak version condition are missing, because
  BergDB never merges.
* Varman and Verma, "An Efficient Multiversion Access Structure", IEEE TKDE
  9(3), 1997 (the MVAS). Similar bounds with less redundancy. Not verified.
* Tonta, Seeger and Soisalon-Soininen, "Multiversion Concurrency Control
  for Multiversion B-Trees", arXiv 2606.09133, June 2026. A concurrent MVBT
  (cMVBT): optimistic latches for writes, no latches for range scans, the
  MVBT's guarantees kept, and continuous garbage collection with
  free-space management. Recent and directly relevant to BergDB's
  resident reads and to reclaim. Abstract read only.
* Salzberg and Tsotras, "Comparison of Access Methods for Time-Evolving
  Data", ACM Computing Surveys 31(2), 1999. The survey that classifies and
  compares all of the above. Read this first.

What BergDB can take from this:

* Merges. BergDB splits but never merges (problem.md, Q1). The MVBT's weak
  version condition and merges give its n_t bound. BergDB has no proved
  replacement bound in the largest live-key count. Copying live entries
  during a merge is compatible in principle with append-only storage, but
  lifespan/deletion updates need adaptation; it is not an unchanged drop-in.
* Space and query proof techniques that BergDB can adapt after establishing
  the corresponding occupancy and version invariants.


3 The nodes: cache-aware klongs
===============================

A key node has a default capacity of 30 klongs (maxNodeSize, 32 - 2).
The klong array's content alone is 240 bytes, about four 64-byte cache lines;
pointers, arrays and Java object headers add memory and accesses. A klong
is a 64-bit word of one of three
types (Klong.java):

* TIME: a field described as 58 bits; the current `Klong.MAX_TIME` limits
  public time values to 56 bits. Starts a new version within the node.
* KEY: up to 7 key bytes and a 3-bit length, with a pointer to a child key
  node or a value node. The key bytes are packed from the high end, so two
  key segments compare with one integer comparison.
* DELETE: a 62-bit bitmap marking earlier klongs in the node as deleted.

Klongs are appended, never moved. A lookup is one linear scan that finds
both the key and the version valid at the lookup time. Resident klong
traversal avoids node latches; pointer loading/installation uses locks, so
the complete Java read operation is not claimed formally lock-free.
The original append/publication design is in
([2012-05-linear-search.txt).
Keys longer than 7 bytes continue in the next segment, so the structure is
a trie of small multiversion B-trees.

Prior art:

* Masstree. Mao, Kohler and Morris, "Cache Craftiness for Fast Multicore
  Key-Value Storage", EuroSys 2012. A trie of B+-trees where each layer
  indexes an 8-byte slice of the key, compared as an integer. Very close to
  BergDB's segmented klongs (BergDB: 2012-02-segmented-keys, the same
  year). Single-version, in memory.
* Judy arrays (Baskins, about 2002) and prefix B-trees (Bayer and Unterauer,
  TODS 1977), both in Frans's 2012 tree study.
* Cache-conscious B-trees: CSB+-trees (Rao and Ross, SIGMOD 2000) and
  prefetching B+-trees (Chen, Gibbons and Mowry, SIGMOD 2001). Nodes sized
  to cache lines, fewer pointers.
* Unsorted, append-only leaves with linear search, compacted when full, for
  persistent memory: NV-Tree (Yang et al., FAST 2015), wB+-tree (Chen and
  Jin, PVLDB 2015) and FPTree (Oukid et al., SIGMOD 2016). They trade
  slower lookups for fewer writes and cache-line flushes, the trade BergDB
  made in 2012.
* Bw-tree (Levandoski, Lomet and Sengupta, ICDE 2013): changes are
  prepended to a page as delta records and consolidated when the chain is
  long. An append-only node in another form.

Possibly new: versions inside the cache-sized node, as TIME klongs in the
same append-only array, resolved by the same linear scan. And a different
view of the time split: in the WOBT it is a way to separate current data
from history; in BergDB it also bounds the length of every linear scan,
because history cannot pile up in a node. Not checked against the
literature on in-memory multiversion indexes.


4 The storage: append-only databases and recovery
=================================================

Systems that store data append-only or out of place, and how they bound
recovery. The problem they share, as Frans put it to Tore Risch in 2012:
with stream pointers, a changed node gets a new position, so its parent
changes, and so on up to the root. Writing the whole path for every update
makes the stream several times larger than the data.

* POSTGRES (Stonebraker, "The Design of the POSTGRES Storage System", VLDB
  1987). No-overwrite storage with time travel; a vacuum cleaner moves
  history to an archive, possibly on WORM disk.
* Log-structured file systems (Rosenblum and Ousterhout, SOSP 1991, TOCS
  1992). Everything is appended to a log. A checkpoint region at a fixed,
  overwritten location points to the inode map; recovery reads the
  checkpoint and rolls forward. A segment cleaner reclaims space.
* ARIES (Mohan et al., TODS 1992). Fuzzy checkpoints and a dirty page table.
  Each dirty page has a recLSN, the log position where it first got dirty;
  redo starts at the smallest recLSN. Writing old dirty pages moves the
  redo point forward. This is the same mechanism as BergDB's startup pos
  and TransSeq: got-dirty position = recLSN, startup pos = redo point,
  index transaction = writing old dirty pages. ARIES overwrites pages in
  place and keeps the log separate from the data.
* Copy-on-write trees with path copying: CouchDB, LMDB, and Hyder
  (Bernstein, Reid and Das, CIDR 2011). Every commit writes the path to the
  root, the cost BergDB avoids. ZFS and btrfs (Rodeh, "B-trees, Shadowing,
  and Clones", ACM TOS 2008) batch it: dirty nodes are kept in memory and
  written together at the end of a transaction group, and a separate
  intent log is replayed after a crash. The root pointer (uberblock,
  superblock) is overwritten in place.
* UBIFS (Linux flash file system, 2008). A journal plus an index B+-tree
  written out of place. Index changes are kept in memory and written at
  commit, when the journal is full; mount reads the index and replays the
  bounded journal. Close to the startup section, but commits write all
  dirty index nodes at once, and a master node in a fixed area points to
  the latest index root.
* Berkeley DB Java Edition (Sleepycat, about 2004). One log holds the
  records and the B-tree, and it is purely append-only: JE "only ever
  appends data to the end of a log file". The cleaner copies active records
  forward and deletes obsolete files; checkpoints limit normal recovery
  work. The JE 7.5 API specifies a default 20 MB checkpointer interval.
  These facts were checked at closure in Oracle's
  [backup/recovery guide](https://docs.oracle.com/cd/E17277_02/html/GettingStartedGuide/backuprestore.html)
  and [EnvironmentConfig](https://docs.oracle.com/cd/E17277_02/html/java/com/sleepycat/je/EnvironmentConfig.html#CHECKPOINTER_BYTES_INTERVAL).
  The earlier dirty-node/delta description came from 2006 architecture
  snippets, not a full source audit. Detailed internal-node reconciliation
  remains unchecked. Transaction isolation is not retained arbitrary
  `get(key, time)` history: obsolete log records can be cleaned away. JE is
  close storage/recovery prior art, not evidence for BergDB's whole P1–P4
  combination or its history semantics.
* ForestDB (Couchbase, Ahn et al., IEEE Transactions on Computers 2016).
  Append-only file with an HB+-trie. New documents are indexed in an
  in-memory write buffer (the WAL index), which is flushed to the trie
  after a number of writes; a commit appends a DB header. On reopen, the
  WAL entries after the last flush are rebuilt, which takes long if
  commits are rare. Batched index writes, not per node. Verified only from
  dbdb.io and Couchbase issue MB-12127; the paper not read.
* The wandering tree problem. In out-of-place storage, a changed node gets
  a new position, so its parent must be written, and so on up to the root.
  The term is from flash file systems. UBIFS keeps index changes in memory
  (the TNC) and writes the index at commit, with the root found through a
  master node at a fixed place. LogFS (Engel, Linux 2.6.34 to 4.9) delays
  parent updates: a changed block pointer is written to the journal as an
  "alias" (logical address and new value), and the journal is scanned at
  mount. Aliases are the closest relative of Rule R found so far, but the
  journal is a separate area. The LSB-tree (log-structured B-tree for NAND
  flash, KIPS Transactions 2008) also defers the change of parent nodes;
  only its abstract was found.
* Graefe, "Write-Optimized B-Trees", VLDB 2004. Fence keys instead of
  sibling pointers, so a moved page needs only its parent updated; notes
  that this removes the indirection layer of log-structured file systems.
* LeanStore. Haubenschild, Sauer, Neumann and Leis, "Rethinking Logging,
  Checkpoints, and Recovery for High-Performance Storage Engines", SIGMOD
  2020. Continuous, incremental and fuzzy checkpointing that bounds
  recovery time, with index recovery and out-of-memory workloads. Pages are
  written in place, with a separate log. The closest relative of claim C2
  in the in-place world. At closure the paper's abstract and logging/recovery
  discussion were inspected in the [author PDF](https://db.in.tum.de/~leis/papers/rethinkingLogging.pdf).
  This establishes relevant prior art for continuous checkpointing, not
  equivalence to BergDB's per-node policy or retained historical queries.
* OrioleDB (Korotkov; US patent 10,325,030, filed 2018, priority 2017,
  "Durable multiversion B+-tree"). A parent's downlink points to a page in
  memory or on disk, like BergDB's mixed pointers of 2012. Copy-on-write
  checkpoints, a separate row-level WAL, and an in-memory undo log for MVCC:
  not the single append-only-stream design. Retained arbitrary-time history
  on disk is not established by the patent abstract inspected here; do not
  infer it from MVCC or undo alone. Abstract only.
* LSM-trees (O'Neil et al., Acta Informatica 1996) and LHAM (Muth, O'Neil,
  Pick and Weikum, VLDB Journal 2000), an LSM-style method for history.
  Runs are rewritten by merging, not appended to.
* Bw-tree with LLAMA (Levandoski, Lomet and Sengupta, VLDB 2013). A mapping
  table from logical page ids to positions in a log-structured store breaks
  the path-copying chain: a page can move without changing its parent.
* System prevalence and Prevayler (cited in Frans's v5): a checkpoint
  stream with the whole data set in memory.
* Datomic (Hickey, 2012): immutable, accumulate-only database with
  as-of queries, built on persistent trees in external storage.


5 Self-indexed streams: the candidate novel concept
===================================================


5.1 The concept
---------------

From Frans's [self-indexed_streams_v5_130704.pdf](../../docs/sources/self-indexed_streams_v5_130704.pdf)
(dated January 2012), [2015-algos.pdf](../../docs/sources/2015-algos.pdf)
and [startup.md](../../docs/sources/startup.md):

* The stream is the database. It can be read anywhere, appended at the end,
  and cut at the front. Nothing is overwritten, and there is no separate
  log, checkpoint region or superblock.
* Continuous checkpointing. The state is split into items (nodes), and each
  item is checkpointed on its own, without requiring a whole-index
  transaction-consistent image. This removes a global checkpoint event
  from the design, but does not bound foreground writeout, GC or reclaim
  pauses. v5 builds this up from state-only, transaction-only and checkpoint
  streams; measured bursts and scheduling obligations are in section 5.5.
* Mixed pointers. A node points to its children with stream pointers or
  memory pointers. Dirty index nodes must remain resident. In the model,
  dirtiness means that the latest stored version is incomplete for some
  reachable lookup time; a child being written does not by itself dirty an
  ancestor (sis-model.md, section 5.2).
* Data is written at once, the index lazily. Value nodes and the user
  transaction are appended to the buffer at execution; durability requires
  the configured sync. Index nodes are written only
  before they would leave the startup section: the startup pos moves
  forward, and the dirty nodes that got dirty before it are written
  (TransSeq, index transactions).
* Bounded startup. Startup reads the tail from the startup pos, rebuilds
  the index as of that position, and reruns the user transactions in the
  tail. Startup time depends on the startup distance D, not on the database
  size as a design goal. Java measurements support practical tail-limited
  recovery, but replay's tree work and startup lag have no proved bound.
* One write, three purposes. A written index node version is the
  durability of the index, the checkpoint that bounds startup, and part of
  the history: old versions stay in the stream and serve historical
  lookups.
* General. v5 defines it for any linked data structure in the sense of
  Driscoll et al., not only B-trees.


5.2 Comparison
--------------

| System            | Index stored        | Index written when             | Separate log or root in place | History kept | Startup bounded by      |
|-------------------|---------------------|--------------------------------|-------------------------------|--------------|-------------------------|
| WOBT              | Append-only, WORM   | Every change, at once          | Root list                     | Yes          | No recovery needed      |
| TSB-tree          | In place + history  | In place; history at time split| Yes (normal DBMS)             | Yes          | DBMS log                |
| ARIES DBMS        | In place            | Dirty pages, any time          | Yes                           | No           | Redo point              |
| LFS               | Appended            | Checkpoints                    | Checkpoint region             | No           | Checkpoint interval     |
| ZFS, btrfs        | Copy-on-write       | Whole transaction group        | Intent log, uberblock         | Snapshots    | Group interval + log    |
| UBIFS             | Out of place        | All at commit (journal full)   | Master node, fixed area       | No           | Journal size            |
| CouchDB, LMDB     | Path copy           | Changed paths at commit        | Header / meta page            | MVCC/snapshots, not a retained as-of API | No replay           |
| Berkeley DB JE    | One log             | Checkpoints                    | No                            | No           | Checkpoint interval     |
| ForestDB          | One file            | WAL flush, batched             | No (headers appended)         | Until compaction | WAL size            |
| LeanStore         | In place            | Continuous checkpointing       | Yes                           | Retained as-of history not established here | Checkpoint progress     |
| BergDB            | One stream          | Nodes taken as the recovery frontier advances | No                | Yes, within available history | Target D; lag and replay costs remain open |

Columns are simplified and are not a proof that a system has P1–P4 below.
"Startup bounded by" names its recovery control mechanism, not a common
worst-case complexity guarantee. MVCC, snapshots and uncollected old bytes
must not be equated with a retained arbitrary-time query API.


5.3 Candidate claims
--------------------

The four properties describe the candidate method and its intended contract.
The current Java implementation does not establish all four as guarantees:

* P1 Pure append-only. The only durable storage is one stream. Bytes are
  only appended (reclaim cuts the front). No separate log, no root or
  checkpoint region at a fixed place.
* P2 Deferred per-node writes without mandatory path copying or a consistent
  whole-index cut. A node's write does not force its parent to be written
  immediately. Rule A requeues a still-dirty node with the current
  transaction. A batch can nevertheless include many or all currently due
  nodes; absence of a global checkpoint event is not a no-spike guarantee.
* P3 Retained history with inexpensive resident reads. Queries can use
  every admitted time, within retained history. Resident traversal follows
  direct references; Java loading/publication uses synchronization. Reader
  lifetime across reclaim cuts remains open.
* P4 Recovery controlled by a tail target rather than whole-stream replay.
  A strict bound needs a startup-frontier scheduling policy and replay cost
  analysis. D alone does not bound time independently of tree accesses or
  transaction mix in the current implementation.

Relevant combinations and the distinctions still to check:

| Design | Relevant overlap | Important distinction |
|---|---|---|
| BergDB level 1 | Transaction log and retained in-memory history | Startup replays the whole log; memory grows with history |
| Path-copying stores | Out-of-place persistence and direct root recovery | Writes changed paths; MVCC/snapshots alone do not establish retained timestamp queries |
| Berkeley DB JE, ForestDB | Append-only storage and deferred index persistence | Checkpoint/WAL-flush policies differ; retained as-of history requires a separate check |
| TSB-tree/MVBT with DBMS recovery | Historical indexes plus normal logging/recovery | Storage and recovery integration differ from one append-only stream |
| LeanStore | Continuous checkpointing and recovery control | Separate logging/page persistence; P3's retained-history API is not established by this comparison |

This limited review has not identified an equivalent complete method;
that is not proof of novelty. P1 alone is not new. P1 and P2
are close to Berkeley DB JE, where the difference is per-node deadlines
instead of checkpoints. P1, P2 and P3 together is the strongest claim, and
P4 must be part of the method's contract: transaction-only replay can
provide append-only storage and history without useful recovery control.

The claim is best put as a method, not a data structure: a way to store
any partially persistent linked structure (A1 to A4 in
[sis-model.md](../../docs/sis-model.md)) on one append-only stream, with the
multiversion B-tree as one instance. This extends Driscoll et al. from
memory to durable storage; Frans's 2016 working title was "Making Data
Structures Persistent and Storing Them". The Lean proofs already hold for
valid modeled runs with A1 to A4, the exact still-dirty test and the
model's reference and startup-policy rules. They do not establish that
every concrete multiversion B-tree implementation meets those rules.

The status of the proofs. T1 and T2 prove abstract recovery and restart
invariance under those assumptions. Append-only storage is built into the
model, not inferred as a new implementation result. They do not prove that
startup is short (P4) or that each node is
written at most once per section as a bound on writes (P2). These are T3
and T4, not yet stated or proven.

Why the four together matter, to check: storage that only allows appends
(zoned SSDs, SMR disks, append-only cloud objects, WORM compliance
storage); replication and backup by copying bytes, with byte-identical
replicas by T2; ledger and audit databases with full history and a
hash-chained stream.

The earlier claims, sharpened:

* C1. A single append-only stream, with no in-place updates at all, no
  separate log and no checkpoint region, from which a database with an
  index larger than memory uses controlled tail recovery. Closest: LFS,
  UBIFS, Berkeley DB JE; append-only recovery is not new alone. BergDB's
  strict startup bound and larger-than-memory implementation are still
  open (Level 4). Now P1 and the intended P4.
* C2. Per-node write deadlines instead of checkpoints: an index node is
  written as its dirty transaction leaves the selected startup section,
  so the index write rate adapts to the update pattern and there is no
  checkpoint event. Closest: ARIES (the redo point moved by writing old
  dirty pages), but ARIES overwrites pages and has a separate log.
  LeanStore's continuous checkpointing (2020) is related prior art, not an
  established equivalence. Now P2. Write volume versus batched checkpoints
  needs a matched comparison; no equality or automatic no-spike gain is
  established. Deferred writes can reduce path copying, but actual bytes
  depend on node versions, workload and maintenance.
* C3. The written index node versions are at the same time the checkpoint
  and the multiversion index: the same versions serve both purposes.
  This does not mean retaining history is free; versions add bytes and
  reclaim/eviction work. Closest: the TSB-tree's historical nodes and the
  WOBT, which have no lazy writes.
* C4. The method is defined for general linked data structures (v5), as an
  extension of Driscoll et al. from persistence in memory to durable,
  append-only storage. Frans's 2016 working title: "Making Data Structures
  Persistent and Storing Them".
* C5. The cache-aware versioned node of section 3, if it holds up.

The claims stand only with their invariants proven: INV-RESTART and
INV-CRASH in [problem.md](01-problem.md), and the bound on write overhead (R4,
Q5). The 2017 startup failures are analyzed historically in
[startup-invariants.md](03-startup-invariants.md); the repaired Java passes the
recorded Level 2 checks in [levels.md](04-levels.md). Correctness and novelty
are separate obligations; neither follows merely from the other.


5.4 To check
------------

Searches not yet made, in rough order of risk to the claims:

* Berkeley DB JE recovery: how internal nodes logged after the checkpoint
  are placed into the tree (by node id, like Rule R?), and whether internal
  nodes are ever written on a per-node schedule. Read the source,
  `com.sleepycat.je.recovery.RecoveryManager` (`readINs`, `buildINs`), and
  the 2006 architecture white paper.
* LogFS aliases (`Documentation/filesystems/logfs.txt`), the closest
  relative of Rule R found so far.
* The ForestDB paper (Ahn et al., 2016), for WAL flush and recovery.
* The LSB-tree full text, for how deferred parent changes are recovered.
* UBIFS design document (Hunter, 2008), for lazy index writes.
* Log-structured stores for flash and persistent memory after 2010: LLAMA,
  SplinterDB, and key-value stores with "bounded recovery".
* Main-memory databases with continuous or incremental checkpointing, for
  C2.
* Literature citing Driscoll et al. together with "disk", "log" or
  "durable", for C4.
* In-memory multiversion indexes with versions inside the node, for C5.


5.5 Runtime timing: pauses, latency and maintenance scheduling
-------------------------------------------------------------

For the database user, acknowledged durable transactions must survive the
specified failures. In BergDB, execution into the buffer and completion of
a durability sync are distinct. During
normal operation, the important checkpointing questions concern delays:
does maintenance stop transaction processing, when can delays occur, how
long can they last, and can the application control them? Checkpointing
must be assessed by its effect on transaction and reader latency, as well
as by recovery time and total write volume.

This is an established concern in the literature. Andy Pavlo's CMU
presentation, [Checkpoint Protocols (15-721, Spring 2018), slide 6](https://15721.courses.cs.cmu.edu/spring2018/slides/13-checkpoints.pdf#page=6),
lists two ideal checkpoint properties: "Do not slow down regular txn
processing" and "Do not introduce unacceptable latency spikes".

Useful terms:

| Term | Meaning for this discussion |
|------|-----------------------------|
| Tail latency | The slow end of the response-time distribution, commonly measured at p99, p99.9 and higher percentiles. |
| Latency jitter | Variation in response time, including periodic maintenance spikes. |
| Online / non-blocking checkpointing | Checkpointing proceeds alongside transaction processing without requiring global quiescence; this does not imply zero interference or formally lock-free operations. |
| Incremental maintenance | Maintenance is performed in small steps interleaved with normal operation. |
| I/O pacing / rate limiting | Maintenance consumes resources under a scheduling budget, reducing bursts of I/O. |
| Deamortization | Occasional expensive work is distributed across operations to establish a bound on each operation's work. |

Amortized efficiency alone does not guarantee smooth latency: 999 cheap
operations followed by one expensive operation can have a low amortized
cost. "Spread out naturally" describes incremental maintenance; a proven
per-operation bound would justify "deamortized". See Bernstein, Forster
and Henzinger, [A Deamortization Approach for Dynamic Spanner and Dynamic
Maximal Matching](https://arxiv.org/abs/1810.10932), which explicitly
connects the distinction to real-time requirements.

Fuzzy checkpointing describes checkpoint consistency, not a latency bound:
transactions may continue while checkpoint state is collected, and recovery
reconciles that state. "Incremental checkpointing" can mean writing only
changes since the preceding checkpoint, rather than spreading work evenly
over time. A background checkpoint can avoid a global pause while still
causing delays through resource contention. PostgreSQL explicitly spreads
checkpoint writes over an interval to avoid I/O bursts, using
`checkpoint_completion_target`:
[WAL Configuration](https://www.postgresql.org/docs/18/wal-configuration.html).

For self-indexed streams, the intended timing property is continuous index
persistence in small, bounded steps, without a global checkpoint pause,
while sync provides the configured durability. Per-node deadlines alone do
not prove this: many nodes can become due together. The "no checkpoint
spike" aspect of C2 needs a scheduling argument and measurement. Specify
the maintenance work budget per transaction or scheduling interval, how
the application controls it, and what happens when maintenance falls
behind: write backpressure, more dirty-node memory, or a longer recovery
window. Reclaim has now been tested and tuned: the initial load check wrote
up to 4019 index nodes in one commit, and later grids still show bursts.
Those observations make this scheduling obligation concrete; see
[levels.md](04-levels.md), "Level 3 cost".

Evaluate latency over time alongside maintenance activity, reporting high
percentiles and maximum observed delays. "Predictable latency" is a useful
initial objective; "hard real-time" requires deadline guarantees under
stated execution and storage assumptions, beyond bounds on algorithmic
work alone.


6 Reading order
===============

1. Salzberg and Tsotras 1999, the survey.
2. Becker et al. 1996, the MVBT: a closely related index with proved
   occupancy, space and query bounds that BergDB does not yet inherit.
3. Lomet and Salzberg 1989, the TSB-tree, and Easton 1986.
4. Mohan et al. 1992, ARIES, sections on checkpoints and the dirty page
   table: the closest relative of the startup pos.
5. Berkeley DB JE architecture and recovery, LogFS aliases, and the UBIFS
   design document: the closest relatives of self-indexed streams.
6. Mao et al. 2012, Masstree, for the nodes.

Search terms used in the literature on layer 1: multiversion, transaction
time, temporal access method, partially persistent, time-evolving data.
"Append-only database" and "persistent B-tree" lead elsewhere.


7 References
============

Status: read = full text read; verified = existence, authors and venue
checked on the web; known = from Claude's knowledge, not checked.
These labels preserve the earlier research's reading record. Closure
checks are identified below; sources labeled known or abstract-only do not
support a completed novelty determination.

* Bayer, Unterauer. Prefix B-trees. ACM TODS 2(1), 1977. Known.
* Becker, Gschwind, Ohler, Seeger, Widmayer. An Asymptotically Optimal
  Multiversion B-tree. VLDB Journal 5(4), 1996, pages 264 to 275. Read:
  https://users.cs.utah.edu/~lifeifei/cis5930/mvbt.pdf
* Bernstein, Reid, Das. Hyder: A Transactional Record Manager for Shared
  Flash. CIDR 2011. Known.
* Chen, Gibbons, Mowry. Improving Index Performance through Prefetching.
  SIGMOD 2001. Known.
* Chen, Jin. Persistent B+-Trees in Non-Volatile Main Memory. PVLDB 8(7),
  2015. Known.
* Driscoll, Sarnak, Sleator, Tarjan. Making Data Structures Persistent.
  STOC 1986; JCSS 38(1), 1989. Cited by Frans.
* Easton. Key-Sequence Data Sets on Indelible Storage. IBM J. Res. Develop.
  30(3), 1986, pages 230 to 241. Verified (reference list of Lomet and
  Salzberg 1989).
* Lanka, Mays. Fully Persistent B+-trees. SIGMOD 1991. Verified.
* Levandoski, Lomet, Sengupta. The Bw-Tree: A B-tree for New Hardware
  Platforms. ICDE 2013. LLAMA: A Cache/Storage Subsystem for Modern
  Hardware. PVLDB 6(10), 2013. Known.
* Lomet, Salzberg. Access Methods for Multiversion Data. SIGMOD 1989, pages
  315 to 324. Read: https://www.cs.bu.edu/fac/gkollios/cs591/tsbtree.pdf
  (scanned).
* Lomet, Salzberg. The Performance of a Multiversion Access Method. SIGMOD
  1990. Verified; its split policies as summarized in Becker et al. 1996.
* Lomet, Salzberg. Exploiting A History Database for Backup. VLDB 1993.
  Verified.
* Lomet, Barga, Mokbel, Shegalov, Wang, Zhu. Immortal DB: Transaction Time
  Support for SQL Server. SIGMOD 2005. Known.
* Lomet, Hong, Nehme, Zhang. Transaction Time Indexing with Version
  Compression. PVLDB 1(1), 2008, pages 870 to 881. Verified.
* Mao, Kohler, Morris. Cache Craftiness for Fast Multicore Key-Value
  Storage. EuroSys 2012. Known.
* Mohan, Haderle, Lindsay, Pirahesh, Schwarz. ARIES. ACM TODS 17(1), 1992.
  Known.
* Muth, O'Neil, Pick, Weikum. The LHAM Log-Structured History Data Access
  Method. VLDB Journal 8(3-4), 2000. Known.
* O'Neil, Cheng, Gawlick, O'Neil. The Log-Structured Merge-Tree.
  Acta Informatica 33(4), 1996. Known.
* Oukid, Lasperas, Nica, Willhalm, Lehner. FPTree. SIGMOD 2016. Known.
* Rao, Ross. Making B+-Trees Cache Conscious in Main Memory. SIGMOD 2000.
  Known.
* Rodeh. B-trees, Shadowing, and Clones. ACM TOS 3(4), 2008. Known.
* Rosenblum, Ousterhout. The Design and Implementation of a Log-Structured
  File System. SOSP 1991; ACM TOCS 10(1), 1992. Known.
* Salzberg, Tsotras. Comparison of Access Methods for Time-Evolving Data.
  ACM Computing Surveys 31(2), 1999. Known.
* Stonebraker. The Design of the POSTGRES Storage System. VLDB 1987.
  Verified (reference list of Lomet and Salzberg 1989).
* Tonta, Seeger, Soisalon-Soininen. Multiversion Concurrency Control for
  Multiversion B-Trees. arXiv 2606.09133, 2026. Verified, abstract read.
* Varman, Verma. An Efficient Multiversion Access Structure. IEEE TKDE
  9(3), 1997. Known, not found in a web search.
* Yang, Wei, Zhang, Zhou, Zhang, He. NV-Tree. FAST 2015. Known.
* Ahn, Seo, Lee, Kim, et al. ForestDB: A Fast Key-Value Storage System for
  Variable-Length String Keys. IEEE Transactions on Computers 65(3), 2016.
  Known; the design verified from https://dbdb.io/db/forestdb and
  https://issues.couchbase.com/browse/MB-12127.
* Berkeley DB Java Edition. Oracle (Sleepycat). Append-only log and
  checkpoints verified: Getting Started Guide,
  https://download.oracle.com/berkeley-db/docs/je/1.7.1/GettingStartedGuide/backuprestore.html;
  FAQ, https://oracle.com/technetwork/database/berkeleydb/je-faq-096044.html;
  Berkeley DB Java Edition Architecture, white paper, September 2006,
  https://www.oracle.com/technetwork/database/database-technologies/berkeleydb/learnmore/bdb-je-architecture-whitepaper-366830.pdf
  (search snippets only). Recovery details not verified.
  Closure checks: [Oracle JE backup/recovery guide, 7.5](https://docs.oracle.com/cd/E17277_02/html/GettingStartedGuide/backuprestore.html)
  and [checkpointer interval](https://docs.oracle.com/cd/E17277_02/html/java/com/sleepycat/je/EnvironmentConfig.html#CHECKPOINTER_BYTES_INTERVAL).
  Detailed recovery-source reconciliation remains unreviewed.
* Engel. LogFS. Linux kernel, `Documentation/filesystems/logfs.txt`, 2009.
  Verified: https://lkml.iu.edu/hypermail/linux/kernel/0911.2/02393.html
* Graefe. Write-Optimized B-Trees. VLDB 2004. Verified:
  https://www.vldb.org/conf/2004/RS18P2.PDF
* Haubenschild, Sauer, Neumann, Leis. Rethinking Logging, Checkpoints, and
  Recovery for High-Performance Storage Engines. SIGMOD 2020. Verified,
  abstract originally read: https://cris.fau.de/publications/255101727.
  Closure: abstract and relevant logging/recovery discussion inspected in
  [author PDF](https://db.in.tum.de/~leis/papers/rethinkingLogging.pdf).
* Apache CouchDB. [Technical overview](https://docs.couchdb.org/en/stable/intro/overview.html).
  Closure: storage/snapshot discussion inspected; MVCC snapshots are not
  evidence of BergDB's retained arbitrary-time query contract.
* Korotkov. Durable multiversion B+-tree. US patent 10,325,030 B2, filed
  2018-06-25 (Oriole DB Inc.). Verified, abstract read:
  https://patents.google.com/patent/US10325030
* Log-Structured B-Tree for NAND Flash Memory (LSB-tree). KIPS
  Transactions Part D, 2008. Verified, abstract only:
  https://www.researchgate.net/publication/245570968_Log-Structured_B-Tree_for_NAND_Flash_Memory
* UBIFS. Hunter, A Brief Introduction to the Design of UBIFS, 2008. Known.
  The wandering tree problem verified from https://arxiv.org/pdf/1907.11825
* Pavlo. Checkpoint Protocols. CMU 15-721, Spring 2018, lecture 13.
  Relevant slides inspected: ideal checkpoint properties (slide 6),
  consistent and fuzzy checkpoints (slide 7), and checkpoint implementations.
  https://15721.courses.cs.cmu.edu/spring2018/slides/13-checkpoints.pdf
* Bernstein, Forster, Henzinger. A Deamortization Approach for Dynamic
  Spanner and Dynamic Maximal Matching. arXiv 1810.10932, 2018.
  Abstract read; relevant to amortized versus per-operation guarantees:
  https://arxiv.org/abs/1810.10932
* PostgreSQL. WAL Configuration. Version 18 documentation, checkpoint
  write pacing discussion inspected:
  https://www.postgresql.org/docs/18/wal-configuration.html
