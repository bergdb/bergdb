# 030-17. Java's readers under eviction and after a cut; K-LEVEL in contractcheck

Created 2026-11-17 by Frans Lundberg. Status: open.

The rest of 030-14 (its State note, items 1 to 3): Java's readers, with
Java's search through the skip pointers, under eviction through the handles
and after reclaim's safe cuts, end to end; what Java's search does after a
cut, when the top nodes before it are gone; K-LEVEL in the contract checker
too. Written by an agent of coord-1117 ("I" below), the night of 17 to 18
November, on the branch `030-17-top-eviction-cut` from `main` 3f1e2fea.
Frans, 17:39: correctness first.


# 1. The result

Kept current; the Log has the times.

- **Proved** (Lean, the standard axioms only), for any history that meets
  every clause in the contract's words (`MeetsFull`) and K-LEVEL: **Java's
  get and scan, from Java's own search through the skip pointers, are right
  under eviction through the handles (with restarts), after a lazy startup,
  and after reclaim's safe cuts**, at every time that is still available, at
  a record's time or between two records: they give what a plain sorted map
  gives after that many transactions (`evict_java_reads`,
  `handles_java_reads`, `lazy_java_reads`, `cut_java_reads`). 030-14 had
  this after a crash and restarts only.
- **What Java's search reads, and so what it does after a cut**
  (`findRoot_from`, `java_search_from`). At a lookup time t the search reads
  the super root, the top nodes made at or after t (down the skip pointers
  whose cached time is at or after t), and at the end the top node of time t
  (the target of the lowest skip pointer): nothing else. So any top that
  holds those as written (`TopFrom f`: the super root, every top node made at
  or after f, the top node of time f; f at or before t) gives the same space
  root as the whole top, the tree's space root of time t. The other top
  nodes may be evicted, or gone with a cut. After a cut, f is the first
  available time: the top nodes made before it are gone, but the top node of
  time f; Java's search at any time from f on follows no skip pointer to a
  gone top node. Before f it may need one (the example: at time 1, without
  top node 5, it finds no space root); the API refuses reads before the
  first available time.
- **The cut stream keeps what the search reads** (`cut_keeps_top`): after
  the run with safe cuts, at every time t from the first available time on,
  the structure that a startup from the cut stream gives back has as the
  root's live child the top node of time t, with its root pointer and skip
  pointers as written. Every top node that `TopFrom f` names is such a one.
  Under eviction the writer's structure holds the whole top as written
  (`handles_top`).
- **The premises**, the same as 030-14's for a crash: Java's tree holds the
  view that the model's theorem gives back (`HoldsView`), and Java's top
  holds the history's top from f (`TopFrom f`). Both are 030-04, 3.5, item
  13, now extended to eviction, the lazy startup and the cut (the bytes of a
  top node loaded again, or read after a cut, decode to what was written).
  They are met by the tree as written and the history's top
  (`evict_java_tree`, `cut_holds`, `TopGood.topFrom`), so the theorems are
  not vacuous.
- **Not vacuous, closed example** (`RecoverCutExample.lean`, from 030-11's
  `BridgeExample4`): a top without top node 5 (time 0) holds the history's
  top from time 2 (`topFrom_cut`); under eviction, Java's get of [16] at
  time 3 gives 6 and of [8] at time 2, between records, gives 5, without top
  node 5; at time 1 the search needs it.
- **K-LEVEL in contractcheck** (brief item 2): `contractcheck` checks KIND
  (every key node of the start and of D after each transaction has the kind
  that its level gives with the TREE line's h), and its verdict is now
  `checkVerdict` (030-15's `contractVerdict` and K-LEVEL), proved
  (`checkVerdict_sound`) to give `MeetsTop` and K-LEVEL for the start tree
  and the tree after every transaction, in the contract's words (`KindsAll`:
  every key node of the tree, not only D's; the frame carries the rest). Its
  fault: `faults.sh`'s `kindh0` (the TREE line's h set to 0: KIND fails, no
  other clause). On the small, drain and reclaim sets: CONTRACT OK, 195
  traces, 29,735 transactions, KIND 0 in both checkers; on the whole medium
  set (`treeconf.sh medium`, 27 traces: m-big, m-mixed, m-long, m-long3,
  m-r-del, m-fifo, m-d8, m-d30, m-d62, 3 seeds each; 13,667 transactions,
  736,718 operations): every trace passes `contractcheck`, KIND 0.
- **One premise for every time** (brief item 3, 030-14's State note item
  3): Java's tree after a startup need only hold the model's structure
  **whole** (`HoldsP`: every node but the root and the top nodes, a key node
  with its level, kind and well-formed klongs whose entries are the node's
  whole history; a value with its value); then it holds the view at every
  time (`MeetsFull.holdsView_whole`), so Java's reads are right at every time
  up to the last transaction after a crash, after restarts and under
  eviction (`crash_java_whole`, `restart_java_whole`, `handles_java_whole`).
  The steps: well-formed klongs cut at t stay well formed, W1 to W5
  (`klongsWf_prefixAt`, `fullOk_prefixAt`), and their entries are the whole
  entries up to t (`entriesOf_prefixAt`, under W1). The tree as written meets
  the premise (`crash_java_tree_whole`); a closed example
  (`crash_whole_get16`). Not for the cut: the structure that a startup from
  a cut stream gives back agrees with the run's only on what a reader from
  the first available time on reaches (`SameFrom`); a node dead before then
  may be missing or hold part of its history, so "Java's tree holds the
  structure whole" is not the premise to ask there; the view's form
  (`HoldsView` at each time from the first available time on) is.
- **Found and fixed: `bridge-faults.sh` failed on `main` 3f1e2fea.** The
  hand-made `test/small.trace` (030-15) has a segment leaf on level 2 with
  the TREE line's h = 3, which K-LEVEL (030-14) refuses: `bridgecheck` gives
  KIND 1, so the fault test's "small PASS" fails, and with it `check.sh` and
  `bridge-check.sh` wherever the small and the reclaim sets are both present
  (level2.sh's step 8b writes small and drain only, so it passes in a fresh
  clone). Fixed in the test trace: h = 0, which its levels fit (decision 4).


# 2. The theorems, in plain English beside the Lean

`lean/contract/Contract/RecoverCutTheorems.lean`; the definition `TopFrom`
in `Contract/RecoverCut.lean`; the proofs in `Contract/Proof/TopFrom.lean`
and `Contract/Proof/RecoverCut.lean`. `JReadsRight s tp t mid txs` and
`HoldsView V lf t s` are 030-14's (RecoverJava.lean).

- `findRoot_from` (any top built by the clauses, `TopGood tp`): if tp' holds
  tp from f (`TopFrom f tp tp'`), then for every t ≥ f and either `mid`,
  Java's search on tp' finds the space root it finds on tp. With
  `findTop_from` (the same top node), `jget_from`, `jscan_from`.
- `java_search_from` (for `MeetsFull`): on any top that holds the history's
  top after k from f, Java's search at any t from f to k finds the space root
  of the tree after t.
- `evict_java_reads`: in a run with handles (reads and evictions after each
  transaction, restarts after any), after the first j transactions, a tree
  that holds the view that a read through the handles at t ≤ j returns, read
  with any top that holds the history's top after j from t: Java's get and
  scan at t are right. `handles_java_reads`: the same for the view of the
  structure that the writer holds. `handles_top`: that structure holds the
  history's top. `evict_java_tree`: the premise met by the tree as written.
- `lazy_java_reads`: after a lazy startup from the records of the first k
  transactions, with any reads and writer follows that the model admits, a
  tree that holds the view that a read at t ≤ k returns, with a top that
  holds the history's top after k from t: right at t.
- `cut_java_reads`: after the run with handles, reads from the first
  available time f on, evictions and restarts from safe cut streams, a tree
  that holds the view of the structure at a time t from f to the last
  transaction, read with any top that holds the history's top from f: right
  at t. `cut_holds`: the tree as written holds that view.
  `cut_keeps_top`: that structure's root has the top node of time t as its
  live child, with its entries as written, at every t from f on.

The premises of each, beside `MeetsFull p h top`, `KindsOK kind h` and `1 ≤
p.M`, are those of 030-14's theorem for the same case (`evict_reads`,
`handles_reads`, `lazy_reads`, `cut_reads`): the algorithm with BergDB's
still-dirty test and marking, the run's transactions the history's, the
scope, `OpsOK` for the lazy read, `CutOK`, `PolicyCutOK` and reads from the
first available time on for the cut. And the two of section 1: `HoldsView`
and `TopFrom`.

Item 3, `Contract/RecoverWholeTheorems.lean` (`HoldsP` in
`Contract/RecoverWhole.lean`, the proofs in `Proof/Prefix.lean` and
`Proof/RecoverWhole.lean`):

- `entriesOf_prefixAt`: under W1, the entries of the klongs that a reader at
  t sees are the entries of all the klongs up to t. `klongsWf_prefixAt`,
  `fullOk_prefixAt`: W1 to W5 hold for them.
- `MeetsFull.holdsView_whole`: a tree that holds the model's structure after
  k whole, with each key node's kind from its level, holds its view at every
  time t up to k.
- `crash_java_whole`, `restart_java_whole`: after a crash after k (also
  after restarts), a tree that holds the startup's structure whole, read
  with the top that structure holds: Java's get and scan right at every
  t ≤ k. `handles_java_whole`: the same under eviction, for the writer's
  structure, with any top that holds the history's top from t.
  `crash_java_tree_whole`: the tree as written holds the startup's
  structure whole.

Item 2, `Contract/KindsCheck.lean`: `KindsAll kind s` (every key node of s
has the kind of its level); `checkVerdict` (the checker's verdict:
`contractVerdict` and K-LEVEL computed); `checkVerdict_sound` (a trace with
that verdict is whole, readable, meets `MeetsTop`, and its start tree and
the tree after each transaction meet `KindsAll` with the TREE line's h).


# 3. Decisions

1. **The top as a premise said of what the search reads** (`TopFrom f`),
   not as the top that the structure after the cut holds (`topOfP`, as
   030-14 did after a crash). Reasons:
   - After a cut the model's root lacks the entries for the top nodes made
     before the cut (`SameFrom` keeps only the root's live children from the
     first available time on), and `topOfP` takes a skip pointer's cached
     time from the root's entry for its target: for a gone target it would
     give a wrong time. Java keeps the cached times in the top node's record
     (`StoredTopNode`: position and time for each skip pointer), which a cut
     does not change. So `topOfP` of the cut structure is not Java's top.
   - Under eviction Java's top is not one object either: the super root is
     in memory, the others are loaded through their handles when the search
     follows a pointer to them, and may have been evicted. What matters is
     only what the search reads, and that is what `TopFrom` says.
   - The statement then says exactly what a gone or evicted top node may
     be: anything, since it is never read.
   The history's top (`top k`) stands for "as written": the model's
   structure holds it (`topOfP_eq`, 030-14; `handles_top`), and the cut
   stream still holds the part that the search reads (`cut_keeps_top`).
2. **The lookup time as f under eviction** (`TopFrom t`): the weakest
   premise, since at t the search reads only what `TopFrom t` names. After
   a cut, f is the first available time of the run (`lastFa`), the time from
   which reads are allowed (`hreads`).
3. **The fuel of the search** (`skipDown`'s `tp.length`) on a top with gone
   nodes is shorter; it is still enough, since the search's steps go to
   distinct top nodes made at or after f, and the kept top has an entry for
   each (the ids of a top built by the clauses are distinct:
   `TopGood.nodup`, `length_from_le`). Not a premise.
4. **`test/small.trace`'s TREE line: h = 0, not 3** (45fc446d). Its key
   nodes are all segment leaves, one on level 1 and one on level 2: with
   h = 3 a level-2 node is an inner node by K-LEVEL, which no Java trace has;
   with h = 0 every segment tree is one leaf high and the levels fit. The
   trace is the review's test input of the strict grammar (030-15); its
   faults still fail for their own reasons, and it passes both checkers.
   Rejected: dropping KIND for traces made by hand (a clause that holds only
   for some traces is no clause).
5. **K-LEVEL in contractcheck as a verdict of its own, joined to 030-15's**
   (`checkVerdict = contractVerdict && K-LEVEL`, Contract/KindsCheck.lean),
   not a change of `contractVerdict`: no existing statement changes, and
   `checkVerdict_sound` has `contractVerdict_sound`'s conclusion and more.
   The clause in the contract's words is said of every key node of every
   tree (`KindsAll`), from the D-only check and the frame (clause 3: a node
   not in D is as it was, a new key node is in D), a little more than the
   bridge's `KindsOK` (D only). The start check is RecoverCheck.lean's
   `startKindsOk` again (`startKindsB`), so that the contract checker does
   not import Mathlib.
6. **Item 3 done although item 1 did not need it.** The brief asks for the
   whole-node form only if 030-14's State note says item 1 needs it; it does
   not (item 1's theorems use `HoldsView` at t, as 030-14's). I did it after
   items 1 and 2 because it makes assumption 13 one statement about a
   startup, true at every time, instead of one per time, and costs no
   statement change (new definitions and theorems beside 030-14's). The
   cut keeps `HoldsView` (section 1).
7. **New files only**, as the common rules ask: `Contract/RecoverCut.lean`
   (the definition, to read and trust), `Contract/RecoverCutTheorems.lean`
   (the theorems), `Contract/Proof/TopFrom.lean`,
   `Contract/Proof/RecoverCut.lean` (the proofs),
   `Contract/RecoverCutExample.lean`, `Contract/KindsCheck.lean` (K-LEVEL
   in the contract checker, with its proof), `Contract/RecoverWhole.lean`
   (`HoldsP`), `Contract/RecoverWholeTheorems.lean`,
   `Contract/Proof/Prefix.lean`, `Contract/Proof/RecoverWhole.lean`; shared
   files in small hunks
   (`Contract.lean`, `Axioms.lean`, `statements.pin`, `ContractCheck.lean`:
   the KIND count and the verdict, `faults.sh`: one fault,
   `test/small.trace`: one line), and 030-04, 3.5, item 13 extended.


# 4. Premises and assumptions

- No new clause for item 1. K-LEVEL (030-14's clause) is now checked by both
  checkers.
- **030-04, 3.5, item 13, extended** (not a new item): Java's tree after a
  startup, a lazy startup, a startup from a cut stream, or with objects
  evicted and loaded again, holds the view the model gives back, and Java's
  top holds, as written, the top nodes its search reads (`TopFrom`). Tested
  by run B (`conformance.sh` probes after restarts, also from the cut
  stream: `conformance.sh reclaim`, level 3), run E (`conformance.sh
  evict`, forced eviction schedules, `ereads`, `erestart`, level 4), and
  `ReclaimReaders` (readers at old lookup times, on a cold cache after a
  restart, while reclaim cuts, level 3; with forced eviction, level 4).


# State

2026-11-17, 21:45. The brief's work list is done: items 1 to 3 proved and
gated, merged with `main` d7966251 (the Log has the commits; the last gated
one is 1e87043b). Branch `030-17-top-eviction-cut` in
`/Users/f/fl/bench/2026-11-17/night/s4k/clone`. Java unchanged.

Open, for whoever takes them:

1. A closed example of `cut_java_reads` with a cut run (BridgeExample4 with
   a cut and its `CutOK` proved); today the cut's theorems are shown not
   vacuous only through their premises (`cut_holds`, `TopGood.topFrom`) and
   the search without a gone top node (`RecoverCutExample.lean`).
2. The whole-node form (`HoldsP`) for the lazy startup, whose read returns
   a list of nodes rather than a structure; and for the cut, a form said of
   the nodes that a reader from the first available time on reaches.
3. The bridge checker's KIND on the medium set's m-d8, m-d30, m-d62 and
   m-fifo (here `contractcheck`'s KIND passed on all 27 medium traces).

To check: `cd lean/contract && lake build`; `lean/contract/gate.sh
d7966251`; traces: `java/build.sh`, then `TREECHECK=none
java/stress/treeconf.sh small` (and drain, reclaim, medium), then
`lean/contract/check.sh small drain reclaim` (runs faults.sh with `kindh0`,
faults-top.sh, bridge-faults.sh first).


# Log

2026-11-17, 21:00. Started, on the branch `030-17-top-eviction-cut` from
3f1e2fea. Read 030-14, 030-11, 030-08, 030-04 3.5 and the package's
Recover, Top and Bridge files; `lake build` passes (80 s).
21:15 `findTop_from`, `findRoot_from` (the search reads only what `TopFrom`
names); the end-to-end theorems under eviction, after a lazy startup and
after the cut; `cut_keeps_top`; the example. `gate.sh 3f1e2fea`: GATE OK
(172 theorems). Commit 3a7d6c87.
GATED 3a7d6c87: Java's readers with Java's top search under eviction, after a
lazy startup and after reclaim's safe cuts (`evict_java_reads`,
`handles_java_reads`, `lazy_java_reads`, `cut_java_reads`); the search reads
only the top nodes that `TopFrom f` names (`findRoot_from`), which the cut
stream keeps (`cut_keeps_top`); a closed example without a gone top node;
030-04 3.5 item 13 extended; `gate.sh 3f1e2fea` GATE OK (172 theorems).
21:22 `bridge-faults.sh` fails on `main` 3f1e2fea: "small: WRONG, expected
PASS" (KIND 1 on `test/small.trace`); fixed by the trace's TREE line (h = 0),
BRIDGE FAULTS OK. Commit 45fc446d.
GATED 45fc446d: fix: `bridge-faults.sh` failed on main 3f1e2fea (and with it
`check.sh` and `bridge-check.sh` where the reclaim set is present):
`test/small.trace`'s TREE line h = 0 so that its levels fit K-LEVEL; no Lean
changed (the gate of 3a7d6c87 holds).
21:28 K-LEVEL in `contractcheck`: `checkVerdict`, `checkVerdict_sound`, KIND
counts, `faults.sh` `kindh0` (FAULTS OK); Java built, the small, drain and
reclaim sets written (`treeconf.sh`, TREECHECK=none); `check.sh small drain
reclaim`: CONTRACT OK (195 traces, 29,735 transactions, KIND 0 in both
checkers; faults.sh, faults-top.sh, bridge-faults.sh first). `gate.sh
3f1e2fea`: GATE OK (173 theorems). Commit d295d76a.
GATED d295d76a: K-LEVEL in `contractcheck` (KIND; `checkVerdict` with
`checkVerdict_sound`: MeetsTop and K-LEVEL for every tree), the fault
`kindh0` in faults.sh; check.sh small drain reclaim CONTRACT OK (195 traces,
KIND 0); `gate.sh 3f1e2fea` GATE OK (173 theorems).
21:35 Item 3: `HoldsP` (the tree holds the structure whole), the prefix
lemmas (`entriesOf_prefixAt`, `klongsWf_prefixAt`, `fullOk_prefixAt`),
`holdsView_whole`; `crash_java_whole`, `restart_java_whole`,
`handles_java_whole`, `crash_java_tree_whole`; the example
`crash_whole_get16`. `gate.sh 3f1e2fea`: GATE OK (182 theorems). Commit
f5ec04d6.
GATED f5ec04d6: Java's reads after a crash, restarts and under eviction with
one premise for every time (`HoldsP`: Java's tree holds the structure whole;
`holdsView_whole` from the prefix lemmas W1 to W5 and `entriesOf_prefixAt`);
the premise met by the tree as written; `gate.sh 3f1e2fea` GATE OK (182
theorems).
21:38 Merged `main` d7966251 (the coordinator had landed 3a7d6c87 and
d295d76a with 030-10's work): `statements.pin` in conflict, rebuilt with
pin.sh. `gate.sh d7966251`: GATE OK (188 theorems; with base 3f1e2fea step 4
would name main's own items/006 file). `check.sh small drain reclaim` on the
merged tree: CONTRACT OK. Commit 1e87043b.
GATED 1e87043b: item 3 (`HoldsP`, the whole-node premise, f5ec04d6) on main
d7966251; `gate.sh d7966251` GATE OK (188 theorems); check.sh small drain
reclaim CONTRACT OK.
21:40 `contractcheck` (KIND in it) on the whole medium set, written here
(`treeconf.sh medium`, TREECHECK=none, 87 s): 27 traces, 13,667
transactions, all pass, KIND 0 (par.sh, 4 parts, about 12 minutes at a load
of 40). The large set started the same way.
