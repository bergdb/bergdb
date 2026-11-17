# 030-14. Reads after a crash, a restart and under eviction, end to end

Created 2026-11-17 by Frans Lundberg. Status: open.

030-11's finding 3 closed: the reads' theorems (030-05, 030-08) speak of the
contract's tree, a heap of key nodes with their klongs; the bridge's
(030-07) speak of the abstract model's structure, nodes with entries; the map
from klongs to entries forgets (`BridgeExample4.entries_forget`). So "after a
crash after transaction k, every get and scan at every time gives the plain
map's value" was no theorem. Here it is one, and so are the same claims after
restarts, after a lazy startup, under eviction with handles and after
reclaim's safe cuts, and, after a crash or restarts, for Java's readers with
their search through the skip pointers. Written by an agent of coord-1117
("I" below), the night of 17 to 18 November, on the branch
`030-14-reads-after-crash` from `main` a25b8b03. Frans, 17:39: "proving
correctness is the focus and has priority."


# 1. The result

Kept current; the Log has the times.

- **Proved** (Lean, the standard axioms only), for any history that meets
  every clause in the contract's words (`MeetsFull`, 030-07) and one more,
  K-LEVEL (a key node's kind, segment leaf or inner node, is a function of
  its level; checked on the traces): after a crash after any transaction k,
  after restarts and a crash, after a lazy startup, under any reads and
  evictions with handles and restarts, and after safe cuts of reclaim,
  **every get and every scan, at every time that is still available, gives
  what a plain sorted map gives** after that many transactions. "Still
  available": every time up to k after a crash; every time from the first
  available time on after cuts.
- **What "the reads" are.** Each of the bridge's theorems gives back the
  model's view at a time t (P@t: every node reachable at t, with its entries
  up to t): a startup gives back the structure, a read through the handles or
  a lazy read returns exactly the view, a startup from a cut stream gives the
  same view from the first available time on. The reader here reads that
  view: each node's entries at t decoded into its live klongs, each key
  node's kind from its level, the package's get and scan (Read.lean) on that
  tree from the space root that the root's live top node names. Nothing of
  the reader comes from the history's tree.
- **Java's readers after a crash or restarts** (`crash_java_reads`,
  `restart_java_reads`): if Java's tree after the startup holds the view of
  the startup's structure at t (`HoldsView`: every key node with its level,
  the kind of its level, and klongs at t that are well formed and whose
  entries are the view's; every value), and Java's top is the top that the
  startup's structure holds (`topOfP`: the root's entries and the top nodes'
  root and skip pointers), then Java's get and scan from its search through
  the skip pointers, at a record's time or between two records, give the
  plain map's answer. Proved besides: the model's structure holds the top as
  written (`MeetsFull.topOfP_eq`), and the tree as written holds the view
  (`MeetsBridge.tree_holds`), so the premises are met (`crash_java_tree`).
- **An independent review's finding, fixed** (section 2): the kind of a key
  node is not in the model's structure, and two histories that differ only in
  one node's kind have one model structure and one stream but different
  reads (`FullLeafGap`). My first version (d31fa4e2, landed as d3d98a4e) took
  the kinds from the history's tree; that is not what a startup has.
  Restated: the kinds come from the levels, which the model has and recovery
  gives back, with the new clause K-LEVEL (`KindsOK`), checked by the bridge
  checker on 195 traces (29,735 transactions, keys of up to 5 segments, no
  failure). The review's example is in the package as a test
  (`RecoverLeafGap.lean`): no kind function is met by both of its
  histories, and each history's own reads follow from its own.
- **The step that was missing**, proved once (`MeetsBridge.view_reads`): for
  a history that meets the bridge's clauses and K-LEVEL, the reader of the
  model's view after any transaction k, at any time t up to k, is right.
  Three facts give it: the past is fixed in the model (the view at t of the
  structure after k is the view at t of the structure after t); the map
  keeps the live klongs (`live_klongsOfE`: the klongs that the entries of
  well-formed klongs read as, with W1 to W5, have the same live klongs); and
  a tree that agrees with a sound tree on every node it reaches reads as that
  tree (`Good.transfer`).
- **Not vacuous.** One history of four transactions (030-11's
  `BridgeExample4`: a put; a put that makes a new inner root and a top node
  with a skip pointer; a delete by a bitmap; an overwrite with a touch) meets
  every premise, and the theorems give closed statements of its reads after
  a crash, after restarts, under eviction, and Java's get through the skip
  pointer after a crash (section 6).
- **Premises:** one new clause, K-LEVEL, checked (section 5). For a claim
  about Java one assumption is new in 030-04, 3.5 (item 13): Java's startup
  builds a tree that holds the view and the top that the stream holds (the
  bytes decode to what was written, for a startup).
- **030-11's statement of its section 4.2** ("the same entries give the same
  reads") is false as written (the review); its corrected form is here: the
  same entries, with the kinds of their levels, give the same reads
  (`MeetsBridge.holds_reads`).


# 2. The independent review's finding

From the coordinator, 18:30: a review by another model, read-only on `main`
7ef19685 (`/Users/f/fl/bench/2026-11-17/night/codex1/review.md`, section
2), found that `Rep` (Bridge.lean) keeps a key node's level and entries but
not its kind (`leaf`), which decides whether a klong consumes a key segment
(Read.lean, `getGo`). Its `FullLeafGap.lean`: two histories of one
transaction that differ only in node 3's kind (level 2; a segment leaf or an
inner node) and the key put ([56, 64] or [64]); both meet every clause of
`MeetsFull`; their model structures and streams are equal (`rfl`); their
reads differ. So 030-11's proposed statement was false as written, and a
reader of the recovered structure needs the kind from somewhere.

My first version took it from the history's tree (`leafOf (h.tree k)`). The
theorems were true, and FullLeafGap did not contradict them (each history
has its own tree), but a startup does not have the history's tree. Fixed
(decision 2): the kind comes from the level.

- **K-LEVEL** (`KindsOK kind h`, Recover.lean): every key node of the start
  and of D after every transaction has the kind `kind` of its level. Java's
  traces: a key node in segment s at height e has level 1 + (g - s)(h + 1) +
  e and a segment leaf has height 0 (027-02, section 4, the TREE line), so
  `kind l = ((l - 1) % (h + 1) == 0)` (`kindOfHeight h`). The exporter
  computes the levels from Java's `isSegmentLeaf` (`TraceExport.heightOf`),
  and the clause checks that they agree, node by node.
- **Checked:** `bridgecheck` reports KIND (`kindsOk` for each traced
  transaction, `startKindsOk` for TX 0) and the verdict `kindsHistoryOk`,
  proved to give `KindsOK` for the trace's history (`kindsHistoryOk_meets`).
  On the small, drain and reclaim sets: KIND 0 (section 7). A fault made by
  hand fails it: the TREE line's h set to 0 (`bridge-faults.sh`, `kind-h0`:
  KIND 52, no other clause).
- **FullLeafGap as a test** (`Contract/RecoverLeafGap.lean`, the review's
  definitions and proof of `full` unchanged but for names): `same_model`,
  `same_stream`, `different_reads`; `kinds_exclusive`: no kind function is
  met by both histories (node 3 has level 2 in both); `kinds_leaf`,
  `kinds_inner`: each meets it for its own (h = 0, h = 1); `crash_leaf`,
  `crash_inner`: after a crash, the reader of the same recovered view with
  the kinds of each history's levels scans [56, 64] and [64], each history's
  own plain map.


# 3. The theorems, in plain English beside the Lean

`lean/contract/Contract/RecoverTheorems.lean` and
`RecoverJavaTheorems.lean`; the definitions in `Contract/Recover.lean` and
`Contract/RecoverJava.lean`. `ReadsRight V lf txs t`: the reader of the view
V with the kinds lf is right at t: every get gives `refGet (refMap (txs.take
t))`, every scan that the API allows gives `refScan` of it. In each theorem
the kinds are `kindOf kind V` (each node's kind from its level in V), and
`KindsOK kind h` is a premise.

- `view_reads` (for `MeetsBridge`): the view at any time t ≤ k of the model's
  structure after transaction k reads right at t.
- `crash_reads`: a crash after transaction k keeps the first k + 1 records;
  after a startup from them, every get and scan at every time t ≤ k is right.
- `restart_reads`: the same in a run with a crash and a startup after any
  transactions (restarts), then a crash after transaction k.
- `handles_reads`: in a run with handles (any reads and evictions after each
  transaction, restarts after any), after transaction j the structure that
  the writer holds reads right at every t ≤ j.
- `evict_reads`: in such a run, a read through the handles at any t ≤ j
  returns a view that reads right at t. Eviction changes no answer.
- `lazy_reads`: after a lazy startup from the records of the first k
  transactions (whole, or what a crash leaves), with any reads and writer
  follows that the model admits, a read at any t ≤ k returns a view that
  reads right at t.
- `cut_reads`: after the run with handles, any reads from the first available
  time on and evictions, and restarts from safe cut streams, the structure
  reads right at every t from the first available time to the last
  transaction. `cut_reads_blind`: the same without `PolicyCutOK`, for
  policies that read no stream (the trace checker's).
- `crash_java_reads`, `restart_java_reads`: after a crash after k (also
  after restarts), for any tree that holds the startup's view at t ≤ k with
  the kinds of the levels (`HoldsView`), Java's get and scan (`jget`,
  `jscan`) with the top that the startup's structure holds (`topOfP`), at t,
  at a record's time or between two records (`mid`), are right
  (`JReadsRight`).
- `crash_java_tree`: the same for the tree as written (its premise met:
  `MeetsBridge.tree_holds`).

The premises of each, beside `MeetsFull p h top` and `KindsOK kind h`:
`1 ≤ p.M`; an algorithm `al` with BergDB's still-dirty test
(`al.stillDirty = javaTest`), and for the handles and the cut `al.mark =
true`; the run's transactions are the history's (`hts`, `hcs`); the scope
(`k ≤ n`, `t ≤ k`; for the cut `lastFa ≤ t ≤ n`); for the lazy read `OpsOK`
(the model's physical layer: reads up to k, the writer follows only live
pointers); for the cut `CutOK` at every cut and reads from the first
available time on (`hreads`), and `PolicyCutOK` (or blind policies). All but
`KindsOK` are the bridge theorems' own (030-07, 030-11, section 2.2).


# 4. Decisions

1. **The route: reads as a function of the model's view** (brief item 1).
   030-11, section 4.2 offered two: "the same entries give the same reads"
   (two trees), or "startup's decoding gives back the klongs written"
   (030-04, 3.5, item 5). I took a third that contains the first's core: a
   reader of the model's view at t, proved right for the history's model
   structure, so that each bridge theorem's result (a structure with the same
   nodes, a list of the reachable nodes with their entries at t, a structure
   with the same view from the first available time on) gives the reads at
   once. Reasons:
   - The bridge's theorems do not all give back whole histories: the reads
     under eviction and the lazy reads return the view at t, and after a cut
     the structure keeps only the view from the first available time on
     (`SameFrom`). A statement about two trees with the same entries covers
     recovery only; one about the view covers all five.
   - "Decoding gives back the klongs written" is false of the model
     (`entries_forget`: two klong lists, one entry list); as a premise it
     would be an assumption about Java that contains the whole claim.
   - The reader of the view needs no new object: it is the package's get and
     scan on a tree built from the view, so `get_right`'s proofs are reused
     through `Good.transfer`, not redone.
   The two-tree statement, corrected, follows from the same lemmas: any tree
   that holds the view, with the kinds of its levels, reads as the plain map
   (`MeetsBridge.holds_reads`), and that is Java's side (decision 4).
2. **The kinds come from the levels** (restated at 18:45, after the review;
   section 2). First (d31fa4e2) from the history's tree, `leafOf (h.tree k)`.
   Now from each node's level in the view (`kindOf kind V`), with the clause
   K-LEVEL. Reason: the reader after a crash has only what the stream gives
   back; the level is in the model's structure and recovery gives it back;
   the kind is not, but Java's traces show it is a function of the level
   (the exporter's levels: segment and height). Alternatives rejected: the
   kind in `Rep` alone (the model's nodes have no field for it, and the old
   model is not to be changed); the kind as a premise of the reader (the
   claim would rest on a fact a startup cannot check).
   **Restated:** `view_reads`, `crash_reads`, `restart_reads`,
   `evict_reads`, `handles_reads`, `lazy_reads`, `cut_reads`,
   `cut_reads_blind` (landed in d3d98a4e with `leafOf (h.tree k)`): the
   kinds `kindOf kind V`, and the premise `KindsOK kind h`. Not shown false;
   restated because the first form took the kinds from where a startup
   cannot (the coordinator's word, 18:30). `leafOf` is now a helper of the
   proofs only.
3. **The reader of the view starts from the root's live top node** at t and
   its root pointer (`viewRoot`), the model's space root at t. The view at t
   holds the top node of time t as the root's live child; the older top nodes
   are reached only through skip pointers, which are no live pointers in the
   model. For Java's search through the skip pointers: the model's structure
   holds the history's top (`topOfP_eq`), and Java's search through it finds
   the view's space root at every time (`MeetsFull.findRoot_view`, by TP24).
4. **Java's tree as a premise, said of its data** (`HoldsView`): the key
   nodes' levels, kinds (of their levels), klongs at t well formed and with
   the view's entries, the values; and the top as `topOfP` of the startup's
   structure. Reason: Java's tree after a startup is Java's; what is proved is
   that any tree holding those reads right, and that the tree as written
   holds them (`tree_holds`), so the premise is not vacuous and is exactly
   "the bytes decode to what was written".
5. **One statement for get and scan** (`ReadsRight`, `JReadsRight`), so that
   each case is one theorem.
6. **New files only**, as the common rules ask: `Contract/Recover.lean` and
   `Contract/RecoverJava.lean` (definitions and K-LEVEL, to read and to
   trust), `Contract/RecoverCheck.lean` (K-LEVEL computed),
   `Contract/Proof/Recover.lean`, `Proof/RecoverModel.lean`,
   `Proof/RecoverJava.lean`, `Proof/RecoverTop.lean` (the proofs),
   `Contract/RecoverTheorems.lean`, `Contract/RecoverJavaTheorems.lean` (the
   theorems), `Contract/RecoverExample.lean`, `Contract/RecoverLeafGap.lean`
   (the examples and the review's test); shared files in small hunks
   (`Contract.lean`, `Axioms.lean`, `BridgeCheck.lean`: the KIND check,
   `bridge-faults.sh`: one fault).


# 5. How the proof goes

About 1,700 lines.

- `Proof/Recover.lean`. The live klongs of the entries: the fold of the live
  klongs (`liveOfE`) is the first part of `blive`'s fold, so 030-07's
  `stOf_spec` gives it for klongs with W1 to W5; the decoded klongs (one time
  klong, then the key klongs of the fold) have, for each compare value, that
  pointee (`lookup_live_keysOf`); two lists in order of their compare values
  with the same lookups are one (`eq_of_lookup`): `live_klongsOfE`. Reads
  that agree: `Good.transfer` (a tree that agrees with a sound tree on a set
  of nodes that holds the live pointees of its key nodes is sound there and
  holds the same), `getGo_of_good`, `scanFrom_of_good`, `get_eq_of_agree`,
  `scan_eq_of_agree`.
- `Proof/RecoverModel.lean`. The past is fixed: the model's structure after
  t grows up to t into the one after k (`SIS.Grow`, `grow_apply`); with the
  model's A4 (`PtrsOK`, from the model's run invariant) and `blive`'s
  `LiveSub`, the same nodes are reachable at t (`SIS.reachable_grow`), so the
  views at t are one (`view_later`). At the latest time (`BInv.view_agree`):
  the view's space root is the tree's; every node the tree reaches is
  reachable in the model (`mem_reach_model`), with the entries of its klongs,
  so its decoded klongs have its live klongs; a value has its entry. K-LEVEL
  for every key node of every tree (`MeetsBridge.kinds`, by the frame). Then
  `view_reads_lf` and `view_reads`.
- `Proof/RecoverJava.lean`. A tree that holds the view agrees with the
  history's tree on every node that tree reaches (`live_klongsOfE` twice:
  both lists of klongs have the view's entries): `holds_reads`, `java_reads`.
- `Proof/RecoverTop.lean`. What the model's structure holds of the top
  (`TopHeld`: the root's entries are the top nodes' entries in order, each
  top node its root and skip pointers at its time), by induction with clause
  TB, `TopStep`, `Made` and the model's fresh ids: `topOfP_eq`. The space
  roots at earlier times (`roots_at`), so Java's search finds the view's root
  (`findRoot_view`). The tree as written holds the view (`sub_at`,
  `tree_holds`).
- `RecoverTheorems.lean`, `RecoverJavaTheorems.lean`. Each case from the
  bridge's theorem: `full_recovery` (the same nodes: `SameNodes.view`, and
  `topOfP_congr`), `full_restart` (the same records),
  `bridge_handles_records` (the same nodes), `full_eviction` and
  `bridge_lazy_read` (the list read is the view: `viewOfList_eq`), `full_cut`
  (the same view but the root's entries: `viewTree_congr`).


# 6. Premises and assumptions (brief item 3)

- **New clause: K-LEVEL** (`KindsOK kind h`): every key node has the kind of
  its level. A contract clause in the history's terms, checked on the traces
  by `bridgecheck` (KIND; `kindsHistoryOk_meets` proves that the checker's
  verdict gives the clause), with its fault (`kind-h0`). Not an assumption.
- **New assumption, 030-04, 3.5, item 13** (rewritten at 18:50, narrower than
  the first version): Java's startup builds a tree that holds the model's
  view (`HoldsView`: each key node it reads has the entries that the model's
  startup gives back for it, its klongs well formed, the kind it was written
  with; each value its value) and the top that the stream holds (`topOfP`).
  This is "the bytes decode to what was written" (item 5) for a startup.
  Tested by run B (`conformance.sh`, probe: a restart after a transaction and
  its lookups against the workload) and run E (`ereads=N`, `erestart=K`),
  level 2 to level 4. What item 13 no longer needs: that Java's top search
  finds the right top node, and that Java's reads on such a tree are right
  (both proved).


# 7. The example and the checks (brief item 4)

`Contract/RecoverExample.lean`, from 030-11's `BridgeExample4` (its
`meetsFull`), with the algorithm `h4.al0` (BergDB's still-dirty test,
startup pos 0) and the kinds of h = 1 (`kinds4`: the leaves on level 1, the
inner root on level 2); every statement closed, no premise left:

- after a crash after the fourth transaction (a startup from the five
  records): at time 3 the get of [16] gives 6 and of [8] none (the delete);
  at time 4 the get of [16] gives 9 (the overwrite) (`crash_get16`,
  `crash_get8`, `crash_get16_4`);
- after a crash after the second: the scan at time 2 gives [8] with 5 and
  [16] with 6 (`crash_scan2`);
- with restarts after the first and the third transaction and a crash after
  the fourth: the scan at time 4 gives [16] with 9 (`restart_scan4`);
- with handles, a restart after the third and a read and an eviction after
  the fourth: a read through the handles at time 2 gives a view whose scan
  gives both keys of then (`evict_scan2`);
- Java's get after a crash after the fourth, with the top that the startup
  gives back: at time 1, between the records 1 and 2, through the skip
  pointer of top node 7 to top node 5, [8] gives 5 (`crash_java_get8`); at
  time 3, [16] gives 6 (`crash_java_get16`).

The checks, on the level 2 traces (the small, drain and reclaim sets, copied
from 030-11's clone; java/ unchanged): `bridge-faults.sh` BRIDGE FAULTS OK
(the new fault `kind-h0` fails with KIND 52 and nothing else);
`bridge-check.sh small drain reclaim` BRIDGE OK, 195 traces, 29,735
transactions, KIND 0 (traces with 1 to 5 key segments).


# State

2026-11-17. Branch `030-14-reads-after-crash` in
`/Users/f/fl/bench/2026-11-17/night/s4h/clone`, merged with `main` 556cc927;
the Log has the last gated commit. Done: the brief's items 1 to 4, the
review's finding (K-LEVEL), Java's reads after a crash. Open, in the order I
would take them:

1. Java's reads under eviction and after a cut with Java's top search: the
   top under eviction is the handles' (the super root pinned); after a cut
   the startup rebuilds the root from the top nodes it can read
   (`SameFrom` keeps only the root's live children). Both need a statement of
   what Java's top holds then.
2. K-LEVEL in `contractcheck` too (it reads the TREE line and the KN lines),
   and on the medium and large sets (030-12's traces).
3. The entries of a node at t from its klongs at t
   (`entriesOf (prefixAt ks t) = (entriesOf ks).upTo t` under W1), so that
   `HoldsView` can be said of whole nodes, not of their klongs at t.

To check: `cd lean/contract && lake build`; `lean/contract/gate.sh
556cc927`; `bridge-faults.sh`; `bridge-check.sh small drain reclaim` (the
traces as 030-07's State says). No Java changed.


# Log

2026-11-17, 17:58. Started, on the branch `030-14-reads-after-crash` from
a25b8b03. Read 030-11, 030-04, 030-07 and the package.
18:15 the route chosen (decision 1); `live_klongsOfE` and `Good.transfer`
proved; `MeetsBridge.view_reads` proved.
18:20 the end-to-end theorems and the example; `gate.sh a25b8b03`: GATE OK
(88 theorems). Commit d31fa4e2.
GATED d31fa4e2: reads after a crash, restarts, a lazy startup, eviction with
handles and safe cuts, end to end (`crash_reads`, `restart_reads`,
`lazy_reads`, `evict_reads`, `handles_reads`, `cut_reads`), from the reader
of the model's view (`MeetsBridge.view_reads`); a closed example from
`BridgeExample4`; `gate.sh a25b8b03` GATE OK (88 theorems).
18:30 the coordinator: the independent review's FullLeafGap (section 2).
18:40 K-LEVEL: the clause, the checker's KIND, its fault; the theorems
restated with the kinds from the levels; FullLeafGap as a test; Java's
readers on a tree that holds the view (`holds_reads`, `java_reads`).
18:42 `bridge-check.sh small drain reclaim` BRIDGE OK, KIND 0;
`bridge-faults.sh` BRIDGE FAULTS OK.
18:45 the top that the model's structure holds (`topOfP_eq`), Java's search
finds the view's root (`findRoot_view`), the tree as written holds the view
(`tree_holds`); `crash_java_reads`, `restart_java_reads`, `crash_java_tree`.
Commit c4122360. Merged `main` 556cc927 (d3d98a4e and after): conflicts in
`Contract.lean` and `Axioms.lean`, unioned. `gate.sh 556cc927`: GATE OK (122
theorems).
18:50 on the merged tree: `bridge-faults.sh` BRIDGE FAULTS OK;
`bridge-check.sh small drain reclaim` BRIDGE OK (195 traces, 29,735
transactions, KIND 0). The item, 030-04 3.5 item 13 narrowed, 030's Files.
GATED e9260c8f: K-LEVEL (a key node's kind is its level's), checked by
`bridgecheck` (KIND 0 on 195 traces; fault `kind-h0`), after the independent
review's `FullLeafGap` (in the package as a test, ruled out:
`kinds_exclusive`); the reads restated with the kinds from the view's levels;
Java's reads after a crash and restarts with the top that the stream holds
(`crash_java_reads`, `restart_java_reads`, `crash_java_tree`, `topOfP_eq`,
`tree_holds`); merged `main` 556cc927; `gate.sh 556cc927` GATE OK (122
theorems).
