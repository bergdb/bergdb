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
  traces, 29,735 transactions, KIND 0 in both checkers.
- **Found and fixed: `bridge-faults.sh` failed on `main` 3f1e2fea.** The
  hand-made `test/small.trace` (030-15) has a segment leaf on level 2 with
  the TREE line's h = 3, which K-LEVEL (030-14) refuses: `bridgecheck` gives
  KIND 1, so the fault test's "small PASS" fails, and with it `check.sh` and
  `bridge-check.sh` wherever the small and the reclaim sets are both present
  (level2.sh's step 8b writes small and drain only, so it passes in a fresh
  clone). Fixed in the test trace: h = 0, which its levels fit (decision 5).


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
5. **`test/small.trace`'s TREE line: h = 0, not 3** (45fc446d). Its key
   nodes are all segment leaves, one on level 1 and one on level 2: with
   h = 3 a level-2 node is an inner node by K-LEVEL, which no Java trace has;
   with h = 0 every segment tree is one leaf high and the levels fit. The
   trace is the review's test input of the strict grammar (030-15); its
   faults still fail for their own reasons, and it passes both checkers.
   Rejected: dropping KIND for traces made by hand (a clause that holds only
   for some traces is no clause).
6. **K-LEVEL in contractcheck as a verdict of its own, joined to 030-15's**
   (`checkVerdict = contractVerdict && K-LEVEL`, Contract/KindsCheck.lean),
   not a change of `contractVerdict`: no existing statement changes, and
   `checkVerdict_sound` has `contractVerdict_sound`'s conclusion and more.
   The clause in the contract's words is said of every key node of every
   tree (`KindsAll`), from the D-only check and the frame (clause 3: a node
   not in D is as it was, a new key node is in D), a little more than the
   bridge's `KindsOK` (D only). The start check is RecoverCheck.lean's
   `startKindsOk` again (`startKindsB`), so that the contract checker does
   not import Mathlib.
4. **New files only**, as the common rules ask: `Contract/RecoverCut.lean`
   (the definition, to read and trust), `Contract/RecoverCutTheorems.lean`
   (the theorems), `Contract/Proof/TopFrom.lean`,
   `Contract/Proof/RecoverCut.lean` (the proofs),
   `Contract/RecoverCutExample.lean`; shared files in small hunks
   (`Contract.lean`, `Axioms.lean`, `statements.pin`), and 030-04, 3.5, item
   13 extended.


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

2026-11-17, 21:30. Items 1 and 2 done and gated (the Log has the commits).
Next: item 3 (the whole-node form of `HoldsView`), if useful.


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
