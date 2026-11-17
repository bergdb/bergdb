# 030-11. An independent review of the night's proofs

Created 2026-11-17 by Frans Lundberg. Status: done.

A review, with fresh eyes and skeptically, of what three agents proved on
the evening of 17 November on top of the writer's contract (030-05,
reviewed in 030-06): 030-08 (TREE, the top, TP24, Java's get and scan,
`LinesOf`), 030-07 (`MeetsFull` and the bridge to the abstract model:
`RunOK`, TREE, `EvictRunOK`, and so recovery, restarts, lazy reading,
eviction with handles and reclaim's cut by the old proofs) and 030-09 (the
trace's completeness, `historyOk_meets`, Java's `TransCheck`). Written by a
review agent of coord-1117 ("I" below), on the branch `030-11-review` from
`main` 903a228a, from the coordinator's brief of six questions. No existing
statement is changed. Added: one example, one lemma with a corollary, a
fix of the bridge checker (sections 3, 4 and 5), and the words of findings
1, 2 and 5 in 030-04, 030-07 and two Lean headers.


# 1. The result

**Sound, with fixes.** The top theorems are proved (the gate passes, 72
theorems on Lean's three standard axioms), they say what the items claim
once two plain-word points are added (findings 1 and 2), and they are not
vacuous: one history of four transactions, with a top node made, a skip
pointer, a delete, an overwrite and a touch, meets every statement at once
(`BridgeExample4.meetsAll`, new). The bridge's instance of the abstract
model is the trace checker's own (`bspec`, with BergDB's still-dirty test
and marking, as `tracecheck` runs it), and its theorems carry over with no
premise in the abstract model's words. I found no clause that Java fails:
the bridge's clauses pass on 030-07's 195 traces again, and on 15 traces
of the medium and large sets that no one had run them on (20,360
transactions, node sizes 8 to 62).

The findings, most serious first:

1. **Should fix: the restart, lazy and eviction theorems prove the stream
   layer, not that Java's writer repeats itself** (section 2.3). The
   model's instance takes each transaction's change from the history
   (`exec := fun tr _ _ => chs.getD tr ...`, lean/Check/Trace.lean:341;
   `bridge_execRootOK` is `rfl`). "Restarts change no record" means: given
   the same changes, startup gives back the structure and D so that the
   same records follow. That Java's writer makes the same change after a
   restart or with objects evicted is 030-04, 3.5, item 9 (tested), not a
   part of T2. 030-07, section 1 did not say so. Fixed in words: a
   sentence there and in the headers of `BridgeTheorems.lean` and
   `BridgeFull.lean`.
2. **Should fix: 030-04, 3.5 lacks three tested assumptions that the
   bridge's claims rest on** (section 2.2): (10) Java's records and D are
   the model's for the trace's changes (`tracecheck`); (11) a cut of
   reclaim is safe (`CutOK`); (12) a trace's lines are Java's change
   (`LinesOf`, 030-08). Added to 3.5 as items 10 to 12. A fourth,
   `PolicyCutOK`, is now proved for every policy that reads no stream, as
   `tracecheck` takes Java's (`policyCutOK_of_blind`, `full_cut_blind`,
   new), so it is not on the list.
3. **Should, next: reads after a crash, a restart or under eviction are not
   stated end to end** (section 4.2). The reads' theorems speak of the
   contract's tree (klongs), the bridge's of the model's structure
   (entries). `Rep` maps klongs to entries one way, and the map forgets
   (`BridgeExample4.entries_forget`: two well-formed klong lists, one entry
   list). So "after a crash after transaction k, every get gives the plain
   map's value" is no theorem; it needs a statement that the same entries
   give the same reads (section 4.2 has one), or Java's startup decoding
   the klongs written (030-04, 3.5, item 5).
4. **Fixed here: the bridge checker passed a trace that is not whole**
   (section 5). `bridgecheck` did not run 030-09's completeness pass: a
   trace with an ERROR line, one without its DONE line and one cut after
   TX 59 each printed BRIDGE OK (`contractcheck` fails all three). Now
   `BridgeCheck.lean` calls `completeFault`, and `bridge-faults.sh` has the
   three faults; each fails.
5. **Note: `MeetsFull` is not quite all in the contract's words.** Clause
   TB reads the top nodes' and the root's levels from the model's
   structure (`levelIn (h.P j)`, `BridgeTop.lean`:70-71), so from the NEW
   lines; `BridgeFull.lean`:6 says "No clause is in the abstract model's
   words". Harmless (a level is a witness; 030-07's State, item 3); the
   header now says so.
6. **Note: two checkers, two halves.** `bridgecheck`'s verdict is one
   computed value proved to give `MeetsFull`, hence `MeetsTop`;
   `contractcheck`'s is its loop, by reading (030-08, section 5, item 3),
   but only it checks the GET, SCAN, LIVE and SKIPT lines. Neither runs in
   `level2.sh` yet (030-07's State, item 1). Run both.
7. **Note: the bridge checker is slow on large trees** (section 4.1): A5,
   A-COPY, A6' and the touch test membership in lists of the nodes reached
   (`noResOk`, `copyOk`, `adoptOk`, `touchOk`), about quadratic in the
   tree, for every transaction, and the verdict computes it all again.
   l-big62 of the large set (node size 62, 3,000 keys) took 1,032 s, where
   `contractcheck` took 132 s; on small trees the two take about as long.
8. **Note: what the trust rests on** (section 6). Beyond the package, the
   bridge's statements rest on the abstract model's definitions in `lean/`
   (about 3,600 lines), and its proofs on 51,000 lines of the old package;
   the gate pins them (no file outside `lean/contract/` may change) and
   `#print axioms` covers them. 030-06's finding 8 (pin the package's own
   statement files) is still open.

What the three items claim and the Lean says agree in every other point I
checked: TP24, `jget_right` and `jscan_right` (030-08), `LinesOf` and
`java_meetsTop` (030-08), `historyOk_meets` and the completeness checks
(030-09), `MeetsFull`, `fullHistoryOk_meets` and every bridge theorem
(030-07).


# 2. The top theorems in plain words (question 1)

## 2.1 What each says

For a history: a start, then transactions 1, 2, ..., n, each with its
operations, its D, the tree after it, its change in the model's terms (the
trace's NEW, ADD and TOUCH lines), and the top after it.

- **The reads** (030-08, `TheoremsTop.lean`:83-110). If the history meets
  `MeetsTop` (the contract, TREE, the top's clauses): Java's top search
  through the skip pointers finds the space root of every time t, at a
  record's time or between two records (`top_right`); Java's get and scan,
  as written in Lean (`jget`, `jscan`), give what a plain sorted map gives
  after the first t transactions, for every t up to n (`jget_right`,
  `jscan_right`). Also: the invariants and TREE at every time (`inv_right`,
  `tree_right`), R4 and the dead top nodes (`skip_closure`, `skip_dead`).
- **The bridge** (030-07, `BridgeFull.lean`, `BridgeTheorems.lean`). If the
  history meets `MeetsFull`: the abstract model's assumptions hold for its
  instance (`bridge_runOK`, `bridge_treeRunOK`, `bridge_evictRunOK`), and
  the model's structure after transaction j holds the tree after j, every
  key node with the entries of its klongs, every value (`bridge_rep`).
  Then, by the old proofs, for the model's run with BergDB's still-dirty
  test and any take:
  - recovery: startup from the first k + 1 records gives back every node of
    the structure after k with its whole history, and D; so it holds the
    tree after k (`full_recovery`);
  - restarts: a run with a crash and a startup after any transactions
    writes the same records (`full_restart`);
  - lazy reading, eviction with handles: with any reads and evictions and
    restarts, the same records and D, and a read at any time t reaches
    exactly the nodes reachable at t, each as it was at t (`full_eviction`,
    `bridge_lazy_read`, `bridge_handles_*`);
  - reclaim's cut: after safe cuts, the stream is the run's cut at the
    largest cut, D is the run's, and every lookup from the first available
    time on is the run's (`full_cut`, `full_cut_blind`).
- **The checkers** (`fullHistoryOk_meets`, `historyOk_meets`,
  `historyTopOk_meetsTop`): a trace that the checker passes gives a
  history that meets the statement, for the trees the checker builds from
  the lines; `java_meetsTop`: for Java's own trees if the lines are Java's
  change (`LinesOf`).

**Is the instance the real one?** Yes. `BHist.spec` is `bspec h.chs h.p0
true` (`Bridge.lean`), the function `tracecheck` uses
(`TraceCheck.lean`:143), with the changes and the primordial structure
built the same way from the same lines (`BridgeCheck.lean`,
`checkBridgeTrace`). `tracecheck`'s algorithm has `stillDirty := javaTest`
and `mark := true` by default (`Check/Steps.lean`:20-43), which are the two
premises on `al` of the bridge's theorems; its take is Java's, from the
trace, and the theorems hold for any take. So the model's run that the
theorems speak of is the one `tracecheck` compares with Java's records.

**The klong for entry claim.** `entriesOf` (`Bridge.lean`, section 1) is
027-02, section 1's map (`TraceExport.keyEntries`). `mem_blive_entriesOf`
proves that the model's live children of the entries are the pointees of
the live klongs, for klongs with W1 to W5. W5 was added for this, after
`w4_not_enough` showed W4 too weak; that is a restatement made right.

**The 2^48 bound of 030-02.** 030-02 found TP14 and TP19 false as stated
after 2^48 top nodes. The bridge avoids it by a clause, not a premise: TB
asks every top node made to be on a level below the root's (`BridgeTop.lean`:
70-71), and the root's level in the traces is 2^48 + 4 (`NEW 0
281474976710660 I`), so a history meets `MeetsFull` only below that many
top nodes; Java refuses the transaction after (005-02; 030-04, 3.5, item 8).

## 2.2 Every premise of the main theorems

For the reads (`jget_right`, `jscan_right`, `top_right`, `inv_right`,
`tree_right`):

- `MeetsTop p txs s tp`: a contract clause; tested on traces
  (`contractcheck` C1 to C5); for Java's trees through `LinesOf`.
- `t ≤ txs.length`, `mid`: the scope (a time of the history).
- `req.wf`: the API (keys as `Keys.toSegments` makes them); assumption 7.

For the bridge (`full_recovery`, `full_restart`, `full_eviction`,
`full_cut`, and the `bridge_*` theorems that `MeetsBridge` and `MeetsEvict`
give):

- `MeetsFull p h top`: contract clauses; tested on traces (`bridgecheck`
  and `contractcheck`).
- `al.stillDirty = javaTest`, `al.mark = true`: the model's algorithm as
  Java's (definitions, not assumptions); that Java's run is this one is
  tested by `tracecheck` (new assumption 10 below).
- `hts`, `hcs`, `k ≤ ...`, `t ≤ j`: the shape of the run and the scope.
- `OpsOK` (`bridge_lazy_read`): the reads are at times up to k and the
  writer follows only live pointers of reached objects; a premise on the
  operations given, the model's physical layer (lean/SIS/Phys.lean:522).
- `hreads` (`full_cut`): reads only from the first available time on; the
  API's scope after reclaim.
- `CutOK` (the cut's theorems): the cut removes nothing a later read or
  startup needs; tested at every cut of the reclaim traces by `tracecheck`
  (006-26, 3.3); new assumption 11 below.
- `PolicyCutOK al` (`full_cut`): proved here for every algorithm whose two
  policies read no stream (`policyCutOK_of_blind`): a cut keeps every
  record's startup pos and first available time (`SIS.Record.cut`), and
  the clamps read only the last record's. `tracecheck`'s algorithm takes
  Java's choices from the trace (`algoOf`), so it is such a one;
  `full_cut_blind` is `full_cut` without the premise.
- `hK` (`bridge_liveHeight`): the space root's level stays at most K; open,
  030's D4 (bounded startup).
- `1 ≤ p.M` (`MeetsFull.meetsTop`, `MeetsBridge.meets`): trivial.

The assumptions of 030-04, 3.5 that these rest on, with the three this
review adds:

1. The writer's contract (now with TREE, the top, and the bridge's
   clauses): tested per transaction on traces and by Java's `TransCheck`.
2. to 5. Durable synced appends, a torn tail only, one writer, bytes that
   decode to what was written: Java's tests.
6. Java's readers are the package's: the GET, SCAN and LIVE lines.
7. The OP lines are the user's transaction: run B, the unit tests,
   `TransCheck`.
8. A refused transaction changes nothing: `DbTesterLimits`,
   `testRefusedTransUnchanged`, `testEndOfOrdinals`.
9. What run A checks holds in every run (restarts, eviction, reclaim): runs
   B and E, `TransCheck` in every unit test and f-test.
10. **New: Java's records and D are the model's** for the trace's changes:
    `tracecheck` runs the model's step on each traced transaction and
    compares the record written and D (level 2 to level 4). Every bridge
    theorem speaks of the model's stream (`SIS.run h.spec al`).
11. **New: a cut is safe** (`CutOK`): `tracecheck` at every cut of the
    reclaim traces; that BergDB's waits give it (T-SCHEME) is not proved
    (006-26, 3.3).
12. **New: a trace's lines are Java's change** (`LinesOf`, 030-08,
    section 5): 030-09's completeness checks, `tracecheck` (ADD lines
    against the records) and `treecheck` (KN lines against the model's
    writer).

## 2.3 Finding 1 in detail

The abstract model's A1 says that a transaction's change is a function of
the transaction, its time and what it reads (P at i - 1). Restart
invariance (T2) then has two halves: startup gives back what the writer
reads, so the writer makes the same change; and the same change on the
same structure and D writes the same record. With `bspec` the change is
looked up by the transaction's number and ignores what it reads, so the
first half is empty: `ExecRootOK` and A1 hold by `rfl`. What `full_restart`,
`bridge_lazy_restart` and `bridge_handles_records` prove is the second half
and the recovery it needs, which is the core of self-indexed streams. The
first half, for Java's writer, is assumption 9: tested, not proved. This is
not a gap in the proofs (030-04 chose it: the writer is tested, not
proved); it is a gap in the plain words of 030-07, section 1.


# 3. Vacuity (question 2)

Not vacuous.

- 030-07's claim checked: `BridgeExample3.meetsFull` (030-06's three
  transactions: a put; a put that makes an inner root, a new space root
  and with it top node 7 with its skip pointer to top node 5; a delete by
  a bitmap) is proved and in `Axioms.lean`. With `MeetsFull.meetsTop` and
  `MeetsTop.shape` it meets `MeetsTop` and `MeetsShape` too.
- One more, `Contract/BridgeExample4.lean` (new, about 20 s to build):
  the same three, then at time 4 a put of the key [16] that is there, with
  a touch of reclaim's kind. Leaf 6 gets a second key klong of compare value 16
  (the first is then dead and names the old value, which A6' allows);
  value node 8 is made; the touch is `7 4 6`, the super root and the
  put's path. No example before met the touch rules with a touched node.
  `meetsAll` proves, for this one history, `MeetsFull`, `MeetsBridge`,
  `MeetsEvict`, `MeetsTop`, `MeetsShape` and `Meets`. The reads' theorems
  then give, by rewriting and `decide`: at time 1 between two records the
  get of [8] through the skip pointer of top node 7 to top node 5 is 5; at
  time 3 it is none (the delete); at time 3 between records [16] is 6; at
  time 4 it is 9; a scan at time 2 gives both keys. And `full_recovery`
  gives that startup from the five records holds the tree after time 4.

What the examples still do not have: a key of more than one segment in a
bridged history (`ExampleDag` has two segments, but it is the DAG that
TREE refuses), a merge, and a top node with two skip pointers. The traces
have all three.


# 4. Too weak or too strong (question 3)

## 4.1 Runs on Java's traces

With this branch's checkers (the completeness fix in), on Java's traces as
the other agents wrote them (format 3, the exporter of `main`):

- `bridge-check.sh small drain reclaim` (030-07's traces): BRIDGE OK, 195
  traces, 29,735 transactions, 335,902 nodes made, 831,317 entries, 7,368
  touched; 160 s. The same numbers as 030-07's.
- `bridge-faults.sh`: BRIDGE FAULTS OK, the 8 faults of 030-07 and the 3
  new ones each fail, the two good traces pass.
- The medium set, 030-12's traces with `live=1`, the 9 smaller ones
  (m-big, m-mixed, m-long, seeds 1 to 3): BRIDGE OK, 3,360 transactions,
  22,547 nodes made, 54,599 entries; 118 s. Not run: m-d8 and m-d30 (0.5
  and 1.2 GB a trace with their LIVE lines; the old reader that the bridge
  checker also runs reads a trace as one string), with the machine at a
  load of 20 to 30.
- The large set, 030-12's `live=0` traces, one trace a run (l-hot,
  l-mixed, l-long with keys of several segments, l-big62 with node size 62,
  l-few, l-5000): BRIDGE OK, 6 traces, 17,000 transactions, 71,148 nodes
  made, 187,190 entries; 10, 62, 290, 1,032, 83 and 71 s.
- `check.sh small drain reclaim` (with `faults.sh` and `faults-top.sh`
  first): CONTRACT OK, 195 traces, 29,735 transactions, 2,729,666 LIVE
  lines, 75,568 SKIPT lines, no failure; 168 s.
- The contract check on the medium and large sets is 030-12's (all
  CONTRACT OK where done).

No clause failed. So no clause is shown too strong for Java. The clauses
most likely to meet an untraced Java state are the sufficient form of
A-COPY (`copyOk`, 030-07, decision 7: stronger than the model's) and A6'
(a dead klong of a reached node naming a reached node outside its subtree),
both tested only where merges and reclaim reach them.

## 4.2 What a user needs that is missing (finding 3)

- **Reads after a crash, a restart or under eviction.** Proved: the reads
  are right on the tree of the history (`jget_right`); recovery gives back
  the model's structure, which holds that tree's entries (`full_recovery`,
  `Rep`). Not proved: that a tree rebuilt from the entries reads the same.
  `Rep` goes one way, and `entriesOf` is not injective: `[time 0, time 1,
  key 8 2]` and `[time 1, key 8 2]` have one entry list
  (`BridgeExample4.entries_forget`). A statement that would close it:
  for two trees with the same roots, whose key nodes meet W1 to W5 and
  have the same entries, with values the same, every `get` and `scan` at
  every time is the same. With it, "Java's tree after startup has the
  entries that the records hold" (assumptions 5 and 10) and `full_recovery`
  give "after a crash after transaction k, every get and scan at every
  time up to k gives the plain map's value". Perhaps 300 to 600 lines (the
  live klongs at t as a function of the entries at t, `mem_blive_entriesOf`
  is half of it).
- **Threads, bytes, the cache's budget, the Pub layer, reclaim's waits,
  bounded startup**: out of scope by 030-04, section 8, and open in 030's
  D4 and D5. Not new.

## 4.3 Too weak for the claims made

Only in words: findings 1 and 2. The theorems are as strong as the items
say once "for the model's stream" and "given the change" are read into
them.


# 5. The checkers and the clauses (question 4)

- `contractcheck`: `checkTx` is `contractOk && frameCheck`, proved to give
  `Contract` (`checkTx_sound`, 030-06); the loop checks TX j at time j and
  each part, and the whole-trace verdict is the loop, by reading.
  `completeFault` runs first (030-09). I made three faults by hand (an ERROR
  line, no DONE line, a trace cut after TX 59): each fails.
- `bridgecheck`: the per-transaction lines are the definitions as they
  stand; `Made`, `TopStep` and TREE by functions proved to give them; the
  whole-trace verdict `fullHistoryOk` is computed as one value, the one
  `fullHistoryOk_meets` speaks of. It checks the history positionally (step
  j at time j + 1), so a trace numbered wrongly fails the verdict through
  the time klongs. **The gap (finding 4):** no completeness pass, so a
  trace with an ERROR line, without DONE, or cut, passed. The theorem was
  not wrong (it speaks of the lines read), but `bridge-check.sh` alone then
  tested part of a trace, or a trace with the exporter's own report of a
  change it could not express. Fixed: `completeFault` in `main`, as in
  `ContractCheck.lean`; `bridge-faults.sh` has the three faults.
- Both checkers read the trace with two readers (the package's
  `readTrace` and the old `SIS.Check.parseTrace`, for the changes);
  `bridgecheck` compares their transaction numbers, and clause K ties the
  ADD lines (old reader) to the KN lines (new reader), so a disagreement
  fails K.
- What neither checks: that the lines are Java's change (`LinesOf`,
  assumption 12) and that Java's records are the model's (assumption 10):
  `tracecheck` and `treecheck`, the old checkers, do.


# 6. The gate (question 5)

- `lean/contract/gate.sh 903a228a` on `main` as I found it: GATE OK, 67
  theorems; on this branch: GATE OK, 72 theorems (the new ones:
  `BridgeExample4.meetsFull`, `meetsAll`, `entries_forget`,
  `policyCutOK_of_blind`, `full_cut_blind`).
- The package (`lean/contract/*.lean`, `Contract/`, `Contract/Proof/`): no
  `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`,
  `extern`, `opaque`, `partial`, `csimp`, `noncomputable` or `set_option`.
  One instance, `LinearOrder Pos` (proofs only, 030-06), and a
  `Decidable (TreeOk s)` by `inferInstanceAs`.
- `decide`: in the examples, on small trees, checked by the kernel; in
  proofs only on small numbers. No `decide` on a large term.
- The old package in the import closure (117 modules of `lean/`, 51,000
  lines; of `SIS/Tree` only `Val.lean`): no `sorry`, `axiom` or
  `native_decide` (`#print axioms` would show them); four `@[csimp]`
  lemmas in `Check/Fast.lean`, proved equalities that change only the
  compiled checkers; `partial def` only in `SIS/Tree/NoOutsideWrap.lean`,
  a meta tool outside the closure.
- What the gate does not pin: the package's own statement files (030-06,
  finding 8; still open). It does pin `lean/` outside the package, so the
  abstract model's definitions that the bridge's statements use (about
  3,600 lines: `SIS/Basic`, `Stream`, `Startup`, `Algorithm`,
  `Assumptions`, `Phys`, `Handle`, `Reclaim`, `Bound*`, `Check/Trace`'s
  `bspec`) cannot change under it. They were reviewed in 006-26, not here.


# 7. For Frans: what is proved, what is tested, what is neither

**Proved** (Lean, the standard axioms), for any run of transactions in
which each transaction meets the writer's contract with its clauses:

- Every get and every scan, at the latest time and at every earlier time,
  also between two records, gives what a plain sorted map gives. The
  reader starts from Java's own top search through the skip pointers,
  which is proved to find the right top node.
- The tree keeps its invariants and is a tree (no node reached twice) at
  every time.
- The stream layer, for BergDB's tree, by the abstract model's old proofs:
  after a crash that leaves whole records, startup gives back every node
  with all its entries, and the dirty set; restarts, lazy startup and
  eviction with handles change no record and no read of the structure;
  after safe cuts of reclaim, every lookup from the first available time
  on is as before.
- The trace checkers compute exactly the clauses: a trace they pass is a
  history that meets them.

**Given these assumptions, each tested** (030-04, 3.5, with 10 to 12 of
this review): that Java's writer meets the contract and its clauses (the
traces: 210 traces, 50,095 transactions with every clause, and more with
the contract alone; Java's own `TransCheck` in every unit test and
f-test); that Java's searches are the Lean ones; that Java writes the
model's records; that a cut is safe; that a trace's lines are Java's
change; that Java's writer makes the same change after a restart or with
eviction; and the storage assumptions (durable appends, torn tails only,
one writer, bytes decode).

**Neither proved nor tested as one statement:** that reads after a crash or
a restart are right. Each half is proved; the step between them (a tree
rebuilt from its entries reads the same) is not stated (finding 3). Java's
restart tests test the whole.

**Not covered:** threads (readers beside the writer), bytes and checksums,
the cache's budget, the Pub layer, reclaim's waits (only the cut), and
bounded startup's open premises; the fill and the balance (costs, not
correctness).


# 8. Decisions

1. **The bridge checker's completeness gap is fixed here,** not only
   reported. Reason: five lines in `BridgeCheck.lean`, the same call as
   `ContractCheck.lean`'s, no statement touched; the checker's own test
   shows it. 030-07 is done, so the hunk meets no work in flight.
2. **`PolicyCutOK` is proved for policies that read no stream** in a new
   file (`Contract/BridgePolicy.lean`), with `full_cut_blind` beside
   `full_cut`. Reason: it took 30 lines and removes a premise from the
   cut's claim for the run that `tracecheck` tests; `full_cut` stays.
3. **The fourth transaction goes in a new example file**
   (`Contract/BridgeExample4.lean`) built on `BridgeExample3`, not in it.
   Reason: the common rules (new files; shared files in small hunks).
4. **No statement is changed.** The findings are wording, a missing list
   entry, and a missing theorem; none showed a statement false.
5. **The words of findings 1, 2 and 5 are fixed here:** a bullet in 030-07,
   section 1, items 10 to 12 in 030-04, 3.5 (030-09 added items 6 to 9 the
   same way), and the headers of `BridgeTheorems.lean` and
   `BridgeFull.lean` (comments only). Reason: each is a few lines, plainly
   right, and a claim read without them says more than the proofs.
6. **m-d8 and m-d30 of the medium set are not run through the bridge
   checker.** Reason: 0.5 to 1.2 GB a trace, read as one string by the old
   reader, on a machine at a load of 20 to 30; the 9 smaller traces and
   the large set cover the same code paths of the clauses.


# 9. How this was checked

- Read: 030-04 (all), 030-06, 030-07, 030-08, 030-09; in `lean/contract/`
  every statement file (`Statement`, `Tree`, `Reach`, `ShapeStatement`,
  `Top`, `TheoremsTop`, `Theorems`, `Bridge`, `BridgeTop`,
  `BridgeTheorems`, `BridgeFull`, `BridgeBound`, `BridgeHeap`, `History`,
  `Rebuild`, the examples) and the two checkers' `main`; in `lean/`
  `SIS/Basic.lean`, `SIS/Assumptions.lean`, the definitions of `CutOK`,
  `PolicyCutOK`, `OpsOK`, `startupPos`, `firstAvail`, `cutStream`,
  `Record.cut`, `Check/Trace.lean`'s `bspec`, `SIS/Tree/Val.lean`'s `blive`,
  `Check/Steps.lean`'s options; in Java `TopDs.newSuperRoot` and
  `findSuperRootAtTime` (the Lean `findTop` is the same loop: the highest
  skip pointer at or after the time, then the root time, then the lowest
  skip pointer), and where `TransCheck` is turned on.
- The import closure of the package computed from the `import` lines.
- Built and ran in the clone: `lake build`, the gate twice,
  `bridge-check.sh`, `bridge-faults.sh`, `bridgecheck` on 030-12's
  traces, `check.sh` (after `java/build.sh`, which `faults.sh` needs).


# State

2026-11-17. Branch `030-11-review` in
`/Users/f/fl/bench/2026-11-17/night/s4f/clone`, from `main` 903a228a.
The review is written; the Log has the last gated commit. Open, for whoever
takes them:

1. Finding 3: the statement of section 4.2, a new file of the bridge.
2. Finding 7: sets instead of lists in `adoptOk`, `copyOk` and `touchOk`'s
   checks (the statements may stay; a computed form proved equal), before
   the bridge checker joins `level2.sh`.
3. Finding 8: 030-06's finding 8, the gate pinning the package's statement
   files.

Findings 1, 2 and 5 are fixed in words (030-07, section 1; 030-04, 3.5,
items 10 to 12; the headers of `BridgeTheorems.lean` and
`BridgeFull.lean`); finding 4 in the checker.

To check: `cd lean/contract && lake build`; `lean/contract/gate.sh
903a228a`; the traces as 030-07's State says; `bridge-check.sh small drain
reclaim`; `bridge-faults.sh`; `check.sh small drain reclaim`.


# Log

2026-11-17, 17:02. Started, on the branch `030-11-review` from 903a228a.
`gate.sh 903a228a`: GATE OK (67 theorems).
17:07 `bridgecheck` on 030-12's medium traces (9) and large set (6) in the
background; the medium ones BRIDGE OK in 118 s.
17:10 `bridgecheck` passes a trace with an ERROR line, without DONE, cut
(finding 4); fixed, `bridge-faults.sh` BRIDGE FAULTS OK.
17:13 `BridgeExample4` (four transactions, every statement at once),
`policyCutOK_of_blind`, `full_cut_blind`, `entries_forget`.
`bridge-check.sh small drain reclaim` BRIDGE OK (195 traces, 160 s).
17:18 `gate.sh 903a228a`: GATE OK (72 theorems). Commit 222d9bdf.
17:21 `java/build.sh` in the clone; `check.sh small drain reclaim` CONTRACT
OK (168 s).
GATED f63f8ab6: the review written (sound, with fixes; findings 1 to 8),
`BridgeExample4`, `policyCutOK_of_blind`, `full_cut_blind`, `bridgecheck`
requires a whole trace; `gate.sh 903a228a` GATE OK (72 theorems).
17:24 Findings 1, 2 and 5 fixed in words (030-07, 030-04 3.5 items 10 to
12, two Lean headers); GATE OK. Commit accdf158. The large set's first run
had not ended l-5000-1 after 13 minutes of CPU; I stopped it and ran the
set again, one trace a run. l-5000-1 then took 71 s: the first run's
binary had been relinked under it at 17:11 (the completeness fix), which I
take to be the cause, not the checker. A lesson: no rebuild while a run
uses the binary.
17:48 The large set's l-hot, l-mixed, l-long and l-big62: BRIDGE OK (7,000
transactions; l-big62 1,032 s).
17:50 l-few and l-5000: BRIDGE OK; the large set done, 17,000
transactions.
GATED 882b064b: the review done: sound, with fixes; findings 1, 2 and 5
fixed in words, 4 in the checker; `BridgeExample4` (every statement at
once), `policyCutOK_of_blind`, `full_cut_blind`; the bridge's clauses on
the medium and large sets (15 traces, 20,360 transactions); `gate.sh
903a228a` GATE OK (72 theorems).
