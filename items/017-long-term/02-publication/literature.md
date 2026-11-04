017-02, literature. The sources, with what each says
====================================================

Created 2026-11-04 by Claude (Opus 5.5) for Frans Lundberg, for 017-02.
Status: a first reading, not a closed review.

The literature behind [self-indexed-streams.md](self-indexed-streams.md)
and [transactions.md](transactions.md). It extends 011-02 (draft 2,
sections 4, 5 and 7) and does not repeat what that document says of the
1986 to 2012 multiversion B-trees, ARIES, LFS, ZFS and btrfs.

How it was made. Three web searches by subagents on 2026-11-04: one on
storage and recovery, one on transactions, one on venues (the venues are
in [options.md](options.md)). Each tagged what it read; I kept the tags,
and I did not reread the sources myself. Each entry gives the source, what
it does that touches BergDB, and the distinction. Tags:

* [full] the source itself, the whole text or the relevant sections.
* [abstract] the abstract or a documentation page.
* [secondary] docs, blogs, summaries, search snippets.
* [memory] from the model's knowledge, not checked on 2026-11-04.

Before any of these goes into a paper, every [memory] and [secondary]
entry must be read in the original.


Storage and recovery
====================


The closest relatives of self-indexed streams
---------------------------------------------

* **Berkeley DB Java Edition.** Oracle, "Berkeley DB Java Edition
  Architecture", white paper, September 2006,
  https://www.oracle.com/technetwork/database/berkeleydb/learnmore/bdb-je-architecture-whitepaper-366830.pdf
  [full, sections 3.2 to 3.6]; JE source, `RecoveryManager.java` and
  `Checkpointer.java`, late JE (18.x era) as vendored in Apache Doris,
  https://apache.googlesource.com/doris-thirdparty/+/284830b22b0dc8cefbeef81c3002e97faa2dff01/src/com/sleepycat/je/recovery/RecoveryManager.java
  [full: class and method comments, main code paths].
  * One log of numbered files. Each record change (an LN) is appended at
    once. Internal nodes (INs, BINs) are only marked dirty; the white paper
    says that with a replay from the start of the log, INs would never need
    to be logged: they are logged to bound recovery and to allow eviction.
  * INs are written by a checkpointer (environment-wide, triggered by
    bytes of log or by time), by eviction and by `Database.sync`. The
    checkpoint flushes bottom up, to the highest dirty level, because
    writing an IN dirties its parent.
  * Recovery finds the last checkpoint end and the mapping-tree root at the
    end of the log (no fixed place), then reads every IN logged after the
    checkpoint start and puts it into its parent's slot if its LSN is newer;
    the parent is found by node id and key. Then undo and redo.
  * The cleaner may delete any file of low utilisation, copying its live
    records forward: reclaim is not front only. No retained history.
  * The distinction: a global checkpoint, both for the cascade up the tree
    and to bound the scan of INs at recovery. BergDB has per-transaction
    deadlines for dirty nodes and no checkpoint event, and writing a node
    does not dirty its parent (sis-model.md, section 5.2). Of everything
    found, JE is the system a paper must compare with first.
* **bcachefs.** Overstreet, "bcachefs: Principles of Operation", manual,
  2026, https://evilpiepirate.org/~kent/bcachefs-principles-of-operation.pdf;
  Linux `fs/bcachefs/journal_reclaim.h` (6.12) [full, relevant sections].
  * B-tree updates go to nodes in memory and to a journal, a ring apart
    from the B-tree's buckets. Each dirty node holds a journal pin at its
    oldest unflushed sequence; reclaim writes the nodes that pin the oldest
    sequences, every 100 ms and harder below 25 % free journal space.
  * A node write appends a sorted batch of keys inside the node's own
    region (128 to 256 KB), so the parent's pointer does not change: no
    wandering tree, by a stable address.
  * Mount replays the journal from its last sequence; roots are in a fixed
    superblock on a clean shutdown. No history.
  * The distinction: per-node deadlines over a bounded journal, as BergDB,
    but a separate journal, fixed places and in-place appends inside nodes.
    New to the BergDB literature; 011-02 did not have it.
* **LeanStore's logging and checkpoints.** Haubenschild, Sauer, Neumann,
  Leis, "Rethinking Logging, Checkpoints, and Recovery for High-Performance
  Storage Engines", SIGMOD 2020,
  https://db.in.tum.de/~leis/papers/rethinkingLogging.pdf [full].
  * Section 3.4: a page with changes older than the WAL limit must be
    written before the log is truncated; enforced per shard, round robin.
    Pages are written in place; per-thread logs.
  * The in-place counterpart of BergDB's deadlines and startup distance.
    The group's later papers (vmcache, SIGMOD 2023; "Moving on From Group
    Commit", SIGMOD 2025) change I/O and commit, not checkpoints [abstract].
* **FineLine.** Sauer, Graefe, Härder, "FineLine: Log-structured
  Transactional Storage and Recovery", PVLDB 11(13), 2018,
  https://www.vldb.org/pvldb/vol11/p2249-sauer.pdf [full].
  * An indexed log is the only store; nodes are never flushed. Each commit
    epoch appends a partition sorted by node id; partitions merge like an
    LSM. No checkpoints: a node is recovered on demand by merging its log
    records. The partition index needs its own persistence.
  * No as-of queries, no bound like D. The paper calls LogBase's index
    checkpoints "a second storage representation"; BergDB's written nodes
    are not a second representation, they are the index and the history.
* **FOEDUS.** Kimura, "FOEDUS: OLTP Engine for a Thousand Cores and NVRAM",
  SIGMOD 2015,
  https://15721.courses.cs.cmu.edu/spring2016/papers/p691-kimura.pdf
  [full, relevant sections].
  * Every page pointer is a dual pointer: volatile (DRAM) and snapshot (an
    immutable page). A periodic log gleaner builds snapshots from logical
    logs; its pointer-dropping step stops the world.
  * The snapshots serve both reads and recovery: the nearest to BergDB's
    "one write, three purposes". But separate logs and snapshot files, and
    a global gleaner.
* **LLAMA and the Bw-tree.** Levandoski, Lomet, Sengupta, "LLAMA: A
  Cache/Storage Subsystem for Modern Hardware", PVLDB 6(10), 2013,
  https://www.vldb.org/pvldb/vol6/p877-levandoski.pdf [full]; "The
  Bw-Tree: A B-tree for New Hardware Platforms", ICDE 2013 [relevant
  sections].
  * A mapping table maps page ids to a memory pointer or a store offset
    (mixed pointers, in one table, not in the parents). A flush appends a
    page's state or deltas to the log-structured store; the store is
    cleaned at its oldest end, live pages moved to the tail (front-only
    reclaim, as BergDB's).
  * The mapping table is checkpointed to one of two fixed places; recovery
    loads it and scans the store from the checkpoint's start. The
    transaction component keeps its own log. No history.
* **Graefe's per-page chains.** Graefe, Kuno, "Definition, Detection, and
  Recovery of Single-Page Failures", PVLDB 5(7), 2012,
  https://vldb.org/pvldb/vol5/p646_goetzgraefe_vldb2012.pdf [full];
  Graefe, Guy, Sauer, "Instant Recovery with Write-Ahead Logging", 2014
  and 2016 [secondary].
  * Each log record holds the page's previous PageLSN; a parent's pointer
    carries the child's expected PageLSN. The WAL-world counterpart of
    BergDB's prevPos links and of checking a pointer against a version.
* **Oracle fast-start checkpointing and its relatives.**
  https://docs.oracle.com/cd/B10500_01/server.920/a96533/instreco.htm
  [secondary]. The database writer writes the oldest modified buffers
  first; `FAST_START_MTTR_TARGET` (seconds) becomes limits on dirty buffers
  and redo. SQL Server's indirect checkpoints (`TARGET_RECOVERY_TIME`),
  InnoDB's fuzzy checkpoints and RocksDB's `max_total_wal_size` are the
  same idea [secondary]. The product precedent for a recovery target with
  per-page deadlines, in place.
* **FASTER and CPR.** Chandramouli et al., SIGMOD 2018; Prasaad,
  Chandramouli, Kossmann, SIGMOD 2019,
  https://www.microsoft.com/en-us/research/uploads/prod/2019/01/cpr-sigmod19.pdf
  [full, section 6]. Records with previous addresses in a hybrid log;
  recovery scans the log's tail and fixes hash-index slots along the
  chains. Pointer fix-up from a tail, but for a flat hash index with
  whole-index checkpoints.


Append-only stores with history, and the wandering tree
-------------------------------------------------------

* **ForestDB.** Ahn, Seo, Mayuram, Yaseen, Kim, Maeng, IEEE Trans.
  Computers 65(3), 902 to 915, 2016, doi 10.1109/TC.2015.2435779
  [abstract; no free full text]; the project wiki,
  https://github.com/couchbase/forestdb/wiki/Implementation-Details [full].
  One append-only file. Documents appended at once and indexed in an
  in-memory WAL index; past a threshold, a commit applies the batch to the
  HB+-trie, appending changed nodes and their ancestors to the root, then
  a header. Recovery scans back for the last header and rebuilds the WAL
  index. Snapshots at any older header until compaction. Batched path
  copying.
* **UBIFS.** Hunter, "A Brief Introduction to the Design of UBIFS", 2008,
  http://www.linux-mtd.infradead.org/doc/ubifs_whitepaper.pdf [full]. The
  index changes only in memory until a commit, when the journal is
  "reasonably full"; the commit writes all dirty index nodes and a master
  node at fixed eraseblocks. Mount time grows with the journal size, a mkfs
  parameter. A global commit; no history.
* **LogFS aliases.** Engel, LogFS documentation, LKML, November 2009,
  https://lkml.iu.edu/hypermail/linux/kernel/0911.2/02393.html [full].
  Parent pointer changes are kept as journal "aliases" (logical address,
  new value) and written back by count. A separate journal, two fixed
  superblocks, no history. The document does not say how mount applies the
  aliases.
* **LSB-tree.** Kim, Joo, Lee, KIPS Trans. D 15-D(6), 2008, in Korean,
  https://koreascience.kr/article/JAKO200801655031205.pdf [full]; Kim,
  Lee, Des. Autom. Embed. Syst. 19, 2015 [abstract]. A log page per leaf
  delays parent changes until it fills, then path copying; recovery scans
  the whole device. Far from BergDB.
* **Tux3.** Phillips, 2008 to 2013, https://lwn.net/Articles/309094/
  [full]. Redirect-on-write; a parent's pointer change stays dirty in cache
  and is logged; a periodic global "unify" writes the metadata.
* **OrioleDB.** Korotkov, US patent 10,325,030 B2, 2019,
  https://patents.google.com/patent/US10325030 [full, most of the
  description]. Downlinks to pages in memory or on disk (mixed pointers);
  incremental copy-on-write checkpoints up to the root; a separate row WAL.
* **FoundationDB Redwood.** `VersionedBTree.cpp`, 2021,
  https://github.com/apple/foundationdb/blob/main/fdbserver/kvstore/VersionedBTree.cpp
  [full, relevant comments]. Logical page ids and a remap queue (no path
  copying); data copied back in place later; fixed headers; versions for a
  short window.
* **Log-structured file systems after 2010.** F2FS (Lee et al., FAST 2015)
  stops the wandering tree with a node address table and checkpoints to
  fixed packs [full]; NILFS2 keeps checkpoints as mountable snapshots
  [secondary]; Btrfs (Rodeh, Bacik, Mason, ACM TOS 2013) writes up to the
  superblock at each commit, also in zoned mode [abstract].
* **Append-only stores with path copying and history.** Dolt's chunk
  journal, 2023, https://www.dolthub.com/blog/2023-03-08-dolt-chunk-journal/
  [secondary]; irmin-pack (Tarides, 2020) [full]; BTrDB (Andersen, Culler,
  FAST 2016) [secondary]; hitchhiker trees (Greenberg, 2016) [secondary];
  CouchDB and LMDB (011-02). All keep history and write the path to a root
  per commit.
* **Other log-structured stores.** sled (2019, page-table snapshots)
  [full]; Tucana (ATC 2016) [abstract]; WiscKey (Lu et al., FAST 2016),
  whose value log is cleaned from the tail with live values re-appended
  [full]; WiredTiger's global copy-on-write checkpoints, fixed "turtle"
  file and separate log, https://source.wiredtiger.com/develop/arch-checkpoint.html
  [full]; TokuFT and BetrFS [memory].
* **Zoned storage.** ZenFS (ATC 2021) [memory]; ZB+-tree (2023)
  [abstract]; ZKV and the Z+-tree (ACM TACO 2025),
  https://ranger.uta.edu/~jiang/publication/Journals/2025/ACM-TACO(ZKV).pdf
  [full]: a WAL with meta-log snapshots. None has one stream and lazy node
  writes, so zoned and append-only devices remain an open use case.


Multiversion and temporal indexes since 2015
--------------------------------------------

* **cMVBT.** Tonta, Seeger, Soisalon-Soininen, "Multiversion Concurrency
  Control for Multiversion B-Trees", arXiv 2606.09133, 2026,
  https://arxiv.org/html/2606.09133v1 [full]. Main memory only; external
  storage is named as ongoing work. Nodes with an immutable committed part
  and an uncommitted part; as-of queries through a root list. The state of
  the MVBT line: it has not reached durable storage. A paper on
  self-indexed streams would be the durable step the authors name.
* **ChronicleDB.** Seidemann, Seeger, EDBT 2017, TODS 2019 [abstract];
  Datenbank-Spektrum 2020 [full]. Time-only keys; the right flank of the
  tree in RAM; a separate log for durability.
* **MV-PBT** (Riegger et al., EDBT 2020) [full]; **RocksDB user-defined
  timestamps** [secondary]; **fully persistent B-trees** in the I/O model
  (Brodal et al., TCS 2020, ESA 2025) [abstract], where "persistent" means
  versions, not crash recovery; **HAMMER1** (DragonFly BSD, 2008)
  [secondary]; **PermART** (Waterloo) [secondary].
* **Driscoll et al. on disk.** Two searches found no paper that cites
  Driscoll, Sarnak, Sleator, Tarjan (1986) for durable, append-only storage
  with crash recovery. Absence in a search is weak evidence; it supports
  only "not found".


The log is the database
-----------------------

* **LogBase.** Vo et al., PVLDB 5(10), 2012,
  https://vldb.org/pvldb/vol5/p1004_hoangtamvo_vldb2012.pdf [full]. The log
  on HDFS is the only data store; an in-memory multiversion index gives
  as-of reads; the whole index is flushed to separate files periodically.
* **Amazon Aurora.** Verbitski et al., SIGMOD 2017 [full]. Only redo is
  shipped; storage materialises pages per page; nothing is needed at
  startup. Distributed, pages kept separately.
* **Socrates and Constant Time Recovery.** Antonopoulos et al., SIGMOD 2019
  and PVLDB 2019 [parts]. Persistent row versions serve snapshot isolation
  and instant undo; in place, versions for the active window only.
* **Deuteronomy TC.** Levandoski et al., CIDR 2015,
  https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/DeuteronomyTC-CIDR2015-full.pdf
  [relevant sections]. The redo log's buffers are the version cache: one
  write is durability and version, for recent versions only.
* **Hyder.** Bernstein, Reid, Das, CIDR 2011,
  https://web.eecs.umich.edu/~michjc/eecs584/Papers/cidr11_hyder.pdf [full,
  sections 1 to 4]. The log is the database; a multiversion binary tree
  copied along the path per transaction. Also in the transaction section.
* **Tango.** Balakrishnan et al., SOSP 2013 [full, section 3]. Objects over
  a shared log; checkpoints in the log itself.
* **Others.** Neon (GetPage@LSN over delta and image layers) [secondary];
  FoundationDB (Zhou et al., SIGMOD 2021), recovery independent of data
  size by other means [parts]; Delta Lake (PVLDB 2020) with a fixed
  `_last_checkpoint` file [parts]; SlateDB with a fixed manifest [docs];
  Hekaton's checkpoint files (Diaconu et al., SIGMOD 2013), with the index
  rebuilt at start [full, section 7]; SiloR (Zheng et al., OSDI 2014),
  whole fuzzy checkpoints [full]; CALC (Ren et al., SIGMOD 2016)
  [abstract]; Zigzag, Ping-Pong, PACMAN [memory].


Transactions
============

The sources for [transactions.md](transactions.md), section 4. Where a
line says "rerun", the system reruns the transaction's code on a conflict.


Foundations
-----------

* Kung, Robinson, "On Optimistic Methods for Concurrency Control", ACM
  TODS 6(2), 1981, doi 10.1145/319566.319567 [memory]. Read, validation and
  write phases; backward validation of the read set against the write sets
  of transactions that committed meanwhile; "serial validation" in one
  critical section, as BergDB's commit under its write lock.
* Berenson et al., "A Critique of ANSI SQL Isolation Levels", SIGMOD 1995
  [memory]: snapshot isolation. Adya, PhD thesis, MIT 1999,
  https://pmg.csail.mit.edu/papers/adya-phd.pdf [memory]: the isolation
  levels by dependency graphs (PL-3, PL-2.99). Cahill, Röhm, Fekete,
  SIGMOD 2008 [memory]: serializable snapshot isolation.
* Stonebraker, "The Design of the POSTGRES Storage System", VLDB 1987
  [memory]: no-overwrite storage whose versions serve both concurrency and
  "time travel". Lomet et al., "Immortal DB", SIGMOD 2005 [secondary]: a
  transaction can begin `AS OF` a time.


Software transactional memory
-----------------------------

* Shavit, Touitou, PODC 1995 [memory]: static transactions, data set known
  in advance.
* Herlihy, Luchangco, Moir, Scherer, DSTM, PODC 2003 [memory]: a Java
  library, objects opened for read or write, rerun loop, in memory.
* Harris, Fraser, OOPSLA 2003 [memory]: `atomic` blocks in Java, validated
  at commit, rerun.
* Harris, Marlow, Peyton Jones, Herlihy, "Composable Memory Transactions",
  PPoPP 2005 [memory]: Haskell's `atomically`, `retry`, `orElse`; the type
  system keeps I/O out of a transaction, so a rerun is safe by
  construction.
* Dice, Shalev, Shavit, TL2, DISC 2006 [memory]: a global version clock
  read at start, read-set revalidation at commit; single version.
* Riegel, Felber, Fetzer, LSA (DISC 2006) and SI-STM (TRANSACT 2006)
  [memory]: snapshot STMs with multiple versions.
* Spear et al., RingSTM, SPAA 2008 [memory]: Bloom-filter write signatures
  of recent commits, collisions give false conflicts only. The nearest STM
  to BergDB's hashed, binned key modification set.
* Clojure refs, Hickey 2007 and 2008, https://clojure.org/reference/refs
  [abstract]: multiversion STM with per-ref history; write-write conflicts
  only (snapshot isolation, write skew; `ensure` protects a read). Avout
  (Liebke 2011) made it durable on ZooKeeper [secondary].
* JVSTM. Cachopo, Rito-Silva, "Versioned Boxes as the Basis for Memory
  Transactions", SCOOL 2005, Science of Computer Programming 63(2), 2006,
  https://inesc-id-esw.github.io/jvstm [abstract]; Fernandes, Cachopo,
  TRANSACT 2010,
  https://people.cs.umass.edu/~moss/transact-2010/public-papers/24.pdf
  [full, pages 1 to 3], and the source's `ReadWriteTransaction.java`
  [full]. Java; each box keeps versions; a transaction reads as of its
  start; read-only transactions never conflict; commit under a global lock
  validates the read set; write-only transactions never conflict;
  validation against the write sets of later commits. In memory; the Fénix
  framework persists it to MySQL (Cachopo, Rito-Silva, ICWE 2006; Carvalho
  et al., 2008) [secondary], in production at IST Lisbon. The closest
  mechanism found, without durable history.
* Multiverse, ScalaSTM, Deuce STM (2008 to 2012) [memory]: JVM STMs, in
  memory.
* Durable and persistent-memory TMs: Mnemosyne and NV-Heaps (ASPLOS 2011),
  DudeTM (2017), Pisces (ATC 2019), TimeStone (2020) [memory]. No historic
  queries.


Databases with transactions in host-language code
-------------------------------------------------

* **Hyder** (CIDR 2011, above) [full]. The database runs in the
  application process; a transaction runs on a snapshot of the log's tree
  and appends one intention record, with its read set for serializability;
  every server's deterministic meld checks it against the intentions since
  the snapshot. Old snapshots stay readable. All three parts of BergDB's
  approach, January 2011 (HPTS 2009 before).
* **FoundationDB.** https://apple.github.io/foundationdb/developer-guide.html
  [abstract]; Zhou et al., SIGMOD 2021 [parts]. Client code in a retry loop
  (`db.run(tr -> ...)` in Java); the read version is fixed at the first
  read; read and write conflict ranges go to resolvers; range reads cover
  the range, so no phantoms. Versions for about 5 seconds
  (`transaction_too_old`). Alpha in January 2012, the month of Frans's
  notes. Explicit conflict ranges (`addReadConflictRange` and the like)
  [memory] are what BergDB's virtual keys do.
* **Omid and write-snapshot isolation.** Yabandeh, Gómez Ferro, "A
  Critique of Snapshot Isolation", EuroSys 2012 [secondary]; ReTSO
  (Junqueira, Reed, Yabandeh, 2011) [memory]. Client transactions on HBase
  read at their start time; a status oracle aborts one whose read rows
  were committed after its start; bounded memory, an old start is a
  conflict.
* **Datomic** (Hickey, March 2012),
  https://docs.datomic.com/reference/database-functions.html; Jepsen,
  https://jepsen.io/analyses/datomic-pro-1.0.7075 [secondary]. Database
  values, `as-of`, `since`, `history`, `with`; one transactor; transaction
  functions run in the transactor; `:db/cas`. No automatic read-set
  validation of peer code.
* **XTDB** (formerly Crux, 2019 on) [memory]: bitemporal as-of;
  transactions as operation lists with `match` and functions run at
  indexing.
* **Xodus** (JetBrains), https://github.com/JetBrains/xodus [full:
  `EnvironmentImpl.java`, `TransactionBase.java`]. Append-only log,
  snapshot isolation; `computeInTransaction` reruns the Java code when any
  transaction committed since the snapshot: BergDB's design with the whole
  database as read set.
* **CockroachDB** (2015 on) [secondary]: client retry loops; MVCC reads;
  `AS OF SYSTEM TIME` on the same versions; read refresh validates read
  spans.
* **Percolator** (OSDI 2010) [memory], **App Engine Datastore** (2008) and
  **Megastore** (CIDR 2011) [secondary], **Spanner** (OSDI 2012) [memory],
  **Apache Ignite** optimistic serializable transactions [secondary],
  **MapDB TxMaker** [secondary], **H2 MVStore** [memory], **LMDB**
  [memory], **Berkeley DB JE** locking transactions [memory], **Chronicle
  Map and Queue** [memory]: each has some of the parts.
* **Fauna** (2016 on), Jepsen 2019,
  https://jepsen.io/analyses/faunadb-2.5.4 [secondary]: speculative
  execution at a snapshot, read timestamps checked through a Calvin-style
  log; `At(ts)`; code in FQL on the server.
* **Calvin** (Thomson et al., SIGMOD 2012) with OLLP (Thomson, Abadi, VLDB
  2010) [memory]: deterministic stored procedures; a reconnaissance read
  at a snapshot for dependent transactions, restarted if it changed.


Main-memory engines, object databases, prevalence
-------------------------------------------------

* Hekaton (Larson et al., PVLDB 5(4), 2011; Diaconu et al., SIGMOD 2013)
  [memory]: optimistic MVCC, read-set and scan-set validation at commit,
  compiled T-SQL procedures. Silo (SOSP 2013) [memory]: OCC with epochs and
  node sets against phantoms. Cicada (SIGMOD 2017) [memory]. HyPer MVCC
  (Neumann, Mühlbauer, Kemper, SIGMOD 2015),
  https://db.in.tum.de/~muehlbau/papers/mvcc.pdf [secondary]: commit checks
  read predicates against the writes of recently committed transactions,
  by precision locking. Structurally BergDB's key modification set with
  predicates instead of key hashes.
* GemStone/S, https://docs.gemtalksystems.com/GemStone64/3.7.x/GS64-ProgGuide-3.7/9-Transactions.htm
  [abstract]: Smalltalk code in the session's process, a snapshot view,
  commit checks write-write conflicts, abort and rerun. ObjectStore,
  Versant, db4o, PJama, JDO and JPA optimistic locking [memory].
* Prevayler (2001), https://prevayler.org; Fowler, "Memory Image" (2011)
  and "The LMAX Architecture" (2011) [memory]; acid-state (Haskell)
  [memory]: command objects run one at a time on an in-memory model,
  journaled and replayed. Frans's v5 cites Prevayler.


Current application platforms
-----------------------------

* **Convex.** Jayakar, "How Convex Works", 2 April 2024,
  https://stack.convex.dev/how-convex-works;
  https://docs.convex.dev/database/advanced/occ [abstract]. Mutations are
  deterministic TypeScript functions run in the backend; one committer; an
  append-only multiversion log; reads at a begin timestamp; read set of
  index ranges; conflict means rerun. A staff reply says historic reads are
  not offered to users [secondary]. The closest current product, ten years
  after BergDB's design.
* Cloudflare Durable Objects, SpacetimeDB, Replicache, Reflect, Zero
  [memory]: single-threaded execution or speculative client reruns, not
  read-set validation.
