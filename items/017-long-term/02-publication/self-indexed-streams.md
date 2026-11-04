017-02, self-indexed streams. The case for a paper
=================================================

Created 2026-11-04 by Claude (Opus 5.5) for Frans Lundberg, for 017-02.
Status: exploration; the novelty judgement is better founded than
011-02's, but still not a closed review.

What of self-indexed streams is new, after a wider search than 011-02's
(the sources are in [literature.md](literature.md)), what a paper would
claim, and what it would need. The candidate concept and its properties P1
to P4 are 011-02's, section 5.


# 1. In short

* Each of P1 to P4 alone is known. A single append-only log (P1):
  Berkeley DB JE, CouchDB, ForestDB, Hyder. Deferred node writes without a
  global cut (P2): LeanStore 2020 and Oracle's MTTR target in place,
  bcachefs's journal pins with a separate journal. History on written
  structures (P3): CouchDB, ForestDB, LogBase, NILFS2, Immortal DB.
  Recovery bounded by a tail target (P4): Oracle, SQL Server, LeanStore,
  JE, UBIFS.
* No system was found with P1 and P2 together in the strict sense, nor
  with P1, P2 and P3, nor with all four. The nearest are Berkeley DB JE
  (P1, P2 with a global checkpoint, P4), ForestDB (P1, P3, P4 with batched
  path copying), FineLine (P1, a different P2, no P3 or P4) and FOEDUS
  (P3 and P4 with separate files and a global gleaner).
* The core of a novelty claim is narrower than "the combination": it is
  how BergDB avoids the wandering tree. Others avoid it by an indirection
  table (LLAMA, F2FS, Redwood), by a stable node address (bcachefs), by
  path copying (CouchDB, LMDB, ForestDB, Hyder) or by a global bottom-up
  checkpoint (JE, UBIFS). BergDB keeps the parent's stale reference and
  resolves it at startup by node id inside the bounded tail (Rule R), so
  that writing a node does not dirty its parent (sis-model.md, section
  5.2), and a deadline per dirty node keeps every needed version inside
  the tail. I found no published system that does this.
* A second distinction no relative has: the method is proved. T1
  (recovery) and T2 (restart invariance) are proved in Lean for any
  partially persistent linked structure that meets A1 to A5, with
  reclaim and eviction (001), and T3 bounds the startup section for
  BergDB's own policy (007-08). Java is checked against the model by
  trace conformance.
* Verdict: a systems paper on self-indexed streams is worth writing. Its
  novelty would hold as a method with a precise contract, not as a list of
  properties. It needs an evaluation that does not exist yet, against
  Berkeley DB JE above all.


# 2. The method as it is in 2026

011-02, section 5.1, describes the method from the 2012 to 2016 sources.
Three points have changed since, and a paper must describe the method as
the code and the model have it now (docs/levels.md, section 5;
sis-model.md, sections 5 and 6):

* What is written when. Each commit takes whole transactions of D (the
  dirty set) from the front of the startup section, oldest first: its
  share of D, in proportion to the stream it adds, and every transaction
  that begins twice the startup distance or more before the end of the
  stream (005-49; 007-03, step 3; 007-07). The taken nodes are written,
  lowest level first; a node that is still dirty after its write goes back
  to D (Rule A), so a node that stays dirty is written once per startup
  section. So the deadline is per got-dirty transaction, and the write
  rate is paced by the stream's growth. "Per-node deadline" in 011-02 is a
  simplification.
* How stale references are resolved. Rule R: at startup, a pointer to a
  node with a version in the startup section is followed to that node's
  newest version there, by node id. The 2012 draft (v5, section 6) used
  prevPos chains instead. Rule R also resolves references to nodes whose
  first version came later (vpos), which the Lean model found.
* What dirty means. A node is dirty when its latest version is not good
  for some time at which it was reachable (sis-model.md, 5.2). Writing a
  child does not dirty the parent. v5 said the opposite ("a node becomes
  dirty when a node it points to is written"); with Rule R it is not
  needed. This is the step that removes the wandering tree without a
  global event, and the step to explain best in a paper.

Bounded startup has three parts, and only the first is proved: the
startup section stays below twice the startup distance (T3, 007-08). The
records at its ends (T4) and a cold start's reads of index nodes on the
rerun's paths that have no version in the section are not bounded by a
proof; the second took about 46 s on s1 at 10M keys and a startup
distance of 50 MB (005-57, docs/levels.md, section 5).


# 3. P1 to P4: what survives

* **P1 Pure append-only.** Known. JE, ForestDB, CouchDB, Hyder, Tango and
  Dolt's journal append only and find the root at the end. Front-only
  reclaim with live data moved to the head is known too (LLAMA's store,
  WiscKey's value log); JE cleans any file. Survives only as part of the
  method.
* **P2 Deferred writes without path copying and without a consistent
  whole-index cut.** Known in other settings: in place (LeanStore's rule
  that a page with changes older than the WAL limit is written before the
  log is truncated; Oracle's MTTR target) and in bcachefs, where nodes do
  not move. Not found where a node's write appends a new version at a new
  place and no global event handles the parent. JE, UBIFS, ForestDB, Tux3
  and LLAMA all have the global event. Survives in this strict form, the
  one BergDB has.
* **P3 Retained history with cheap resident reads.** Known (CouchDB and
  ForestDB snapshots, LogBase, NILFS2, Immortal DB and the TSB-tree, Neon,
  Dolt). What none of them has is that the same written versions are also
  the checkpoint, without path copying. FOEDUS's snapshots serve reads and
  recovery, but are built by a global gleaner into separate files.
* **P4 Recovery by a tail target.** Known (Oracle, SQL Server, LeanStore,
  JE, UBIFS, bcachefs, FOEDUS, LLAMA). BergDB's version is stronger in one
  way, a proved bound on the section (T3), and weaker in another, the
  unbounded cold reads.
* **P1 + P2.** Not found exactly; JE is the closest by far.
* **P1 + P2 + P3, and all four.** Not found.

The stale-pointer resolution at startup is known in pieces: JE's IN
placement by node id and LSN (the closest, verified in JE's source), LogFS
aliases, Tux3's logged pointer changes, FASTER's previous-address fix-up,
Graefe's parent pointers that carry the child's PageLSN. What seems to be
BergDB's own is the scope: the resolution is needed only inside the tail,
because the deadlines keep every version that a resolution needs inside
it, and that is why no checkpoint is needed.

The search has limits: no exhaustive search of patents, and JE's eviction
path (whether an evicted IN is logged provisionally) was not settled.
Absence of a match is not proof of novelty.


# 4. What a paper would claim

As a method with a contract, in the order of their weight:

1. **Storage of a partially persistent linked structure on one
   append-only stream**, with no other durable state: index versions are
   written lazily, each dirty node before its got-dirty transaction leaves
   a tail of the stream; a node's write does not dirty its ancestors;
   startup reads the tail, resolves references by node id inside it, and
   reruns the tail's transactions. (011-02's C1 and C2, sharpened.)
2. **Correctness, machine-checked**: for every run that meets the stated
   assumptions, startup gives back the same structure at every lookup
   time and the same dirty set (T1), and the database then appends the
   same bytes it would have appended without the crash (T2); with reclaim
   and eviction. The assumptions that are checked, not proved, must be
   listed (TREE, A6', A-COPY, T-SCHEME; 005-04), with the conformance
   evidence for Java.
3. **A bound on the tail** for a stated policy (T3): the startup section
   without its last record stays below twice the startup distance, and
   after a decrease comes down with every commit.
4. **One write, three uses**: each written version is the index's
   durability, the checkpoint and the history for as-of reads (C3). Say
   what it costs: bytes per version, reclaim and eviction work.
5. **An instance**: a multiversion B-tree in Java with time and key splits
   and klong nodes (2015-algos), with eviction through handles (009) and
   reclaim (Level 3).

Not to claim: that startup time is bounded by D alone (cold reads, T4),
that there are no write bursts (011-02, section 5.5; Level 3 bursts), or
optimal space and query bounds like the MVBT's (no merges; 011-01, Q1).


# 5. What the paper needs

The evaluation is the largest missing part. No comparison with another
engine has been run; BergDB's measurements so far are against itself
(008, 016) and against the C clone (012).

* **Baselines.** Berkeley DB JE first: the same language, one log, the
  closest storage design, with its checkpointer interval as the knob that
  matches D. Then LMDB (path copying, no replay) through LMDBJava, RocksDB
  through its Java binding (LSM, WAL), Xodus and H2 MVStore (append-only
  Java stores with snapshots). For history: an MVCC store with as-of reads
  (RocksDB with user-defined timestamps, or Xodus snapshots). LeanStore if
  its code allows, as the in-place relative.
* **The headline figure.** Startup time against database size at a fixed
  startup distance, warm and cold, 1M to 100M keys (the large sizes
  first), with JE at matched recovery settings and RocksDB at matched WAL
  size. Startup distances of 50 MB and more only.
* **Write cost.** Stream bytes per user byte (the stream overhead of v5),
  index bytes per commit, and how they change with D, against JE's
  checkpoint bytes and LMDB's and ForestDB's path copies.
* **Latency over time.** p99, p99.9 and maximum of commits and gets, with
  the index writes, reclaim and eviction in the same plot; ZGC or
  Shenandoah, with the collector's pauses shown apart (009, 005-65).
* **History.** As-of lookups by the age of the lookup time, warm and
  cold; the space history costs, with and without reclaim.
* **Crashes.** The crash and power-loss checks that exist (CrashTest,
  PowerLossTest, 011-07) described as an evaluation of T1 and T2 in
  practice.
* **Workloads.** YCSB A to F for comparison, a history-heavy workload of
  its own (audit, as-of reads), and a large random-update workload that
  stresses D.

Other needs: a statement of the assumptions (005-04); the T4 and cold-read
gap closed or stated plainly; probably a co-author or reader from the
database community who knows JE and LeanStore and can say how reviewers
will read it; and a public artifact (the repository, a Zenodo release).


# 6. Reading list, by priority

The first step of 017-02, done with the search of 2026-11-04. Read in the
original, in this order:

1. Berkeley DB JE: the 2006 white paper and `RecoveryManager` (`readINs`,
   `buildINs`), and whether eviction logs INs provisionally. The decisive
   comparison.
2. Haubenschild et al., SIGMOD 2020, section 3.4: the per-page rule.
3. bcachefs, "Principles of Operation": journal pins and reclaim.
4. Sauer, Graefe, Härder, FineLine, PVLDB 2018.
5. Kimura, FOEDUS, SIGMOD 2015: dual pointers and snapshots.
6. Levandoski, Lomet, Sengupta, LLAMA, PVLDB 2013: the mapping-table
   checkpoint and recovery.
7. Ahn et al., ForestDB, IEEE TC 2016 (the paper, not only the wiki).
8. Tonta, Seeger, Soisalon-Soininen, arXiv 2606.09133, 2026: the MVBT line
   and its "ongoing work" on storage; possibly people to contact.
9. Vo et al., LogBase, PVLDB 2012, and Hunter, UBIFS, 2008.
10. Graefe and Kuno, PVLDB 2012, and Graefe et al. on instant recovery.
11. Becker et al. 1996 (MVBT) and Lomet and Salzberg 1989 (TSB-tree), for
    the index part; Driscoll et al. 1986 for the framing.


# 7. A possible title and abstract

My suggestion, to show the shape, not a text to keep:

"Self-Indexed Streams: Lazy Index Persistence on a Single Append-Only
Stream." A multiversion database can keep all its state in one
append-only stream, writing data at once and index nodes only before
their changes leave a bounded tail, with no checkpoint, no separate log,
no fixed root and no path copying. Startup reads the tail only. The
written index versions are at once the durability, the checkpoint and the
history. The method applies to any partially persistent linked
structure; its recovery and restart invariance are machine-checked in
Lean, and the Java implementation is checked against the model by trace
conformance. Measurements against Berkeley DB JE, LMDB and RocksDB show
(to be measured) ...
