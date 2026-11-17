# 030-14. Reads after a crash, a restart and under eviction, end to end

Created 2026-11-17 by Frans Lundberg. Status: open.

030-11's finding 3 closed: the reads' theorems (030-05, 030-08) speak of the
contract's tree, a heap of key nodes with their klongs; the bridge's
(030-07) speak of the abstract model's structure, nodes with entries; the map
from klongs to entries forgets (`BridgeExample4.entries_forget`). So "after a
crash after transaction k, every get and scan at every time gives the plain
map's value" was no theorem. Here it is one, and so are the same claims after
restarts, after a lazy startup, under eviction with handles and after
reclaim's safe cuts. Written by an agent of coord-1117 ("I" below), the night
of 17 to 18 November, on the branch `030-14-reads-after-crash` from `main`
a25b8b03. Frans, 17:39: "proving correctness is the focus and has priority."


# 1. The result

Kept current; the Log has the times.

- **Proved** (Lean, the standard axioms only), for any history that meets
  every clause in the contract's words (`MeetsFull`, 030-07): after a crash
  after any transaction k, after restarts and a crash, after a lazy startup,
  under any reads and evictions with handles and restarts, and after safe
  cuts of reclaim, **every get and every scan, at every time that is still
  available, gives what a plain sorted map gives** after that many
  transactions. "Still available": every time up to k after a crash; every
  time from the first available time on after cuts.
- **What "the reads" are here.** Each of the bridge's theorems gives back the
  model's view at a time t (P@t: every node reachable at t, with its entries
  up to t): startup gives back the structure, a read through the handles or a
  lazy read returns exactly the view, a startup from a cut stream gives the
  same view from the first available time on. The reader here reads that
  view: it decodes each node's entries at t into its live klongs (one time
  klong, then a key klong for each compare value that has a pointee, as
  `blive`'s fold gives it) and runs the package's get and scan (Read.lean) on
  that tree, from the space root that the root's live top node names. Each
  key node's kind (segment leaf or inner node) is the one it was written with
  (`leafOf`): the model's entries do not hold it; Java's records do.
- **The step that was missing**, proved once (`MeetsBridge.view_reads`): for
  a history that meets the bridge's clauses, the reader of the model's view
  after any transaction k, at any time t up to k, is right. Three facts give
  it: the past is fixed in the model (the view at t of the structure after k
  is the view at t of the structure after t); the map keeps the live klongs
  (`live_klongsOfE`: the klongs that the entries of well-formed klongs read
  as, with W1 to W5, have the same live klongs); and a tree that agrees with
  a sound tree on every node it reaches reads as that tree (`Good.transfer`).
- **Not vacuous.** One history of four transactions (030-11's
  `BridgeExample4`: a put; a put that makes a new inner root and a top node
  with a skip pointer; a delete by a bitmap; an overwrite with a touch) meets
  every premise, and the theorems give closed statements of its reads after
  a crash, after restarts and under eviction (section 6).
- **No new premise.** The theorems take `MeetsFull` and the premises of the
  bridge's theorems as they stood (al's still-dirty test, the cut's
  `CutOK`, the lazy read's `OpsOK`), and `1 ≤ p.M`. For a claim about Java,
  one assumption is new in 030-04, 3.5 (item 13): Java's tree after a startup
  reads as the model's view (section 5).
- **Not yet stated:** Java's top search through the skip pointers over the
  top nodes that a startup gives back (the reader here starts from the root's
  live top node at t, which TP24 shows is what the search finds on the top as
  written); 030-11's statement for two trees ("the same entries give the same
  reads"). Both are next (State).


# 2. The theorems, in plain English beside the Lean

`lean/contract/Contract/RecoverTheorems.lean`; the definitions in
`Contract/Recover.lean`. `ReadsRight V leaf txs t`: the reader of the view V
with the kinds `leaf` is right at t: every get gives `refGet (refMap (txs.take
t))`, every scan that the API allows gives `refScan` of it.

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

The premises of each, beside `MeetsFull p h top`: `1 ≤ p.M`; an algorithm
`al` with BergDB's still-dirty test (`al.stillDirty = javaTest`), and for the
handles and the cut `al.mark = true`; the run's transactions are the
history's (`hts`, `hcs`); the scope (`k ≤ n`, `t ≤ k`; for the cut `lastFa ≤ t
≤ n`); for the lazy read `OpsOK` (the model's physical layer: reads up to k,
the writer follows only live pointers); for the cut `CutOK` at every cut and
reads from the first available time on (`hreads`), and `PolicyCutOK` (or
blind policies). All are the bridge theorems' own (030-07, 030-11, section
2.2).


# 3. Decisions

1. **The route: reads as a function of the model's view** (brief item 1).
   030-11, section 4.2 offered two: "the same entries give the same reads"
   (two trees), or "startup's decoding gives back the klongs written"
   (030-04, 3.5, item 5). I took a third that contains the first's core:
   a reader of the model's view at t, proved right for the history's model
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
   The two-tree statement of 030-11 follows from the same lemma
   (`live_klongsOfE`) and is next: it says that any tree whose nodes hold
   the view's entries reads as the reader of the view (section 5).
2. **The kinds come from the history's tree** (`leafOf (h.tree k)`). The
   model's nodes have a level, a data flag and entries, not the kind of a
   key node (segment leaf or inner node), and the reads need it. Java writes
   it in the node's record (`KeyNode.isSegmentLeaf`), and a node keeps its
   kind forever (the frame; `MeetsBridge.leaf_later`). Not a premise of the
   theorems; for Java, part of 3.5's item 13.
3. **The reader starts from the root's live top node** at t and its root
   pointer (`viewRoot`), the model's space root at t, not from Java's search
   through the skip pointers. Reason: the view at t holds the top node of time
   t as the root's live child; the older top nodes are reached only through
   skip pointers, which are no live pointers in the model. That Java's search
   finds that top node is TP24 (`top_right`) on the top as written; after a
   startup, recovery gives back every top node with all its entries
   (`full_recovery`); the step between (the top that a startup gives back is
   the top as written) is not stated yet (State, item 1).
4. **One statement for get and scan** (`ReadsRight`), so that each case is
   one theorem.
5. **New files only**, as the common rules ask: `Contract/Recover.lean` (the
   definitions, to read and to trust), `Contract/Proof/Recover.lean` and
   `Contract/Proof/RecoverModel.lean` (the proofs),
   `Contract/RecoverTheorems.lean` (the theorems), `Contract/RecoverExample.lean`
   (the example); shared files only in small hunks (`Contract.lean`,
   `Axioms.lean`). No existing statement is changed.


# 4. How the proof goes

About 900 lines.

- `Proof/Recover.lean`. The live klongs of the entries: the fold of the live
  klongs (`liveOfE`) is the first part of `blive`'s fold, so 030-07's
  `stOf_spec` gives it for klongs with W1 to W5; the decoded klongs (one time
  klong, then the key klongs of the fold) have, for each compare value, that
  pointee (`lookup_live_keysOf`); two lists in order of their compare values
  with the same lookups are one (`eq_of_lookup`): `live_klongsOfE`. Reads
  that agree: `Good.transfer` (a tree that agrees with a sound tree on a set
  of nodes that holds the live pointees of its key nodes is sound there and
  holds the same), `get_of_good`, `scan_of_good` (`get_contents` and
  `scan_contents` from `Good` alone), `get_eq_of_agree`, `scan_eq_of_agree`.
- `Proof/RecoverModel.lean`. The past is fixed: the model's structure after
  t grows up to t into the one after k (`SIS.Grow`, `grow_apply`); with the
  model's A4 (`PtrsOK`, from the model's run invariant) and `blive`'s
  `LiveSub`, the same nodes are reachable at t (`SIS.reachable_grow`), so the
  views at t are one (`view_later`). At the latest time (`BInv.view_agree`):
  the root and the top node of the link are reachable, so the view's space
  root is the tree's; every node the tree reaches is reachable in the model
  (`mem_reach_model`), with the entries of its klongs (all up to t,
  `Timely`), so its decoded klongs have its live klongs; a value has its
  entry of a time up to t (`RepT`). The kinds are fixed (`leaf_later`).
  Then `view_reads`: the tree after t meets the invariants at t with the
  plain map's contents (`Meets.at_time`), its walk's set is closed under live
  pointees (`reachAt_closed`), and `get_eq_of_agree` with `get_contents`.
- `RecoverTheorems.lean`. Each case from the bridge's theorem:
  `full_recovery` (the same nodes: `SameNodes.view`), `full_restart` (the
  same records), `bridge_handles_records` (the same nodes), `full_eviction`
  and `bridge_lazy_read` (the list read is the view: `viewOfList_eq`),
  `full_cut` (the same view but the root's entries: `viewTree_congr`).


# 5. Premises and assumptions (brief item 3)

No premise is new in the theorems (section 2). For a claim about Java's reads
after a startup, the theorems speak of the reader of the model's view, so one
assumption is new, added to 030-04, 3.5 as item 13:

13. **Java's tree after a startup reads as the model's view:** each key node
    that Java's startup or a first touch reads from the stream has the
    entries that the model's startup gives back for it, its klongs well
    formed, and the kind (segment leaf or inner node) it was written with;
    each value its value; and Java's top search finds the root's live top
    node of the time. Tested by run B (`conformance.sh`, probe: a restart
    after a transaction and its lookups against the workload) and run E
    (`ereads=N`: lookups at random times under eviction, `erestart=K`), at
    level 2 to level 4; the record's bytes by 3.5's item 5.

What is left to make item 13 smaller: the two-tree statement (any klongs
with these entries, W1 to W5, read as the reader of the view: 030-11's
statement), and the top search over the top given back (State).


# 6. The example (brief item 4)

`Contract/RecoverExample.lean`, from 030-11's `BridgeExample4` (its
`meetsFull`), with the algorithm `h4.al0` (BergDB's still-dirty test,
startup pos 0); every statement closed, no premise left:

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
  gives both keys of then (`evict_scan2`).


# State

2026-11-17. Branch `030-14-reads-after-crash` in
`/Users/f/fl/bench/2026-11-17/night/s4h/clone`, from `main` a25b8b03; the Log
has the last gated commit. Done: the brief's items 1 to 4 for the reader of
the model's view. Open, in the order I would take them:

1. Java's top search after a startup: the top that the model's structure
   holds (the root's entries and the top nodes' root and skip pointers)
   decoded into the contract's `Top` is the history's top (`top k`), so
   Java's search through the skip pointers over the top given back finds the
   view's space root (TP24).
2. 030-11's two-tree statement: two trees whose key nodes meet W1 to W5 and
   hold the same entries, with the same kinds, values and space roots, read
   the same at every time (needs the entries of a node at t from its klongs
   at t: `entriesOf (prefixAt ks t) = (entriesOf ks).upTo t` under W1).

To check: `cd lean/contract && lake build`; `lean/contract/gate.sh
a25b8b03`. No checker changed; no Java changed.


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
