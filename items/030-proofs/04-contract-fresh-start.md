# 030-04. The contract approach and a fresh start

Created 2026-11-17 by Frans Lundberg. Status: open.

What Frans and the coordinator (coord-1117) decided on 2026-11-17, between
09:13 and 11:14: the proof work on today's model is paused, and the proofs
start again in a new form, around a contract for the writer. This item
holds the concept, the rules of the fresh start, the decision on Mathlib,
the steps, and the brief for the first step, a spike of about a day. I am
the writer, an agent of coord-1117 (plan 006-30, W1); my sources are the
coordinator's record of the discussion, 030, 006-26, 030-01 and 030-03.


# 1. The result

- **Paused.** The proof line of today's model (030's D1: `l4`, R3, R4) is
  paused from today (Frans, 09:13 and 11:14). It is frozen at the tag
  `proofs-2026-11-17` (commit f4d73289, pushed at 11:17). Nothing is
  deleted. The level scripts and `night.sh` run as before.
- **The contract approach** (decided; Frans, 10:56 and 11:14). The writer
  is no longer proved step by step. One statement, the writer's contract,
  says what must hold when a transaction ends. What a user relies on is
  proved from the contract: every get and scan at every time, and later
  recovery, restarts, eviction and reclaim's cut. That the writer meets
  the contract is tested, one transaction at a time. It is not proved.
  A claim then reads "proved, given these five stated assumptions, each
  of which is tested" (section 3.5), never "BergDB is proved".
- **A fresh start** (decided; Frans, 11:00 and 11:14). The new proofs are
  written from scratch in a new Lean package, `lean/contract/`. They do
  not import the old tree proofs. The old Lean is a quarry. The
  executable model and the trace checkers in `lean/` stay as they are, as
  the test oracle.
- **Mathlib: yes, in the new package only.** The coordinator's decision;
  Frans delegated it at 11:14 (section 5).
- **Lean in the release** (Frans, 11:14): `lean/` stays, labelled work in
  progress; not in the users' documentation; not a feature (step 5).
- **Next: the spike** (section 7). One agent, about a day: the contract in
  English and in Lean, the theorem on gets and scans proved, the contract
  checked on Java's traces, a one-page report. Success and a stall are
  defined in advance, so the spike asks Frans nothing.
- **Waits for Frans: one thing,** when the spike runs (11:14: "Will be
  decided after this is written down").
- **One finding** (section 9): 027's parts on the key tree are stubs, so
  the spike writes the tree's invariants in English itself.


# 2. Frans's words

All of 2026-11-17, to the coordinator.

- 09:13: "I am considering pausing the proof work. This is too much work
  from my side and too much token cost. Cost is too high for uncertain
  progress. I am about to make a public release of BergDB. Today,
  hopefully. The Lean is work in progress and not stable. It is not
  something fit for a release as it is. We could pause this work. But I
  want to be able to restart it in 12 months or so. At that time, AI may
  solve this fast and cheap."
- 10:19: "I have an intuitive feeling that there should be some
  simplification here that makes proving easier."
- 10:45: "We make a clear set of assumptions, a contract for the writer
  implementation. Before and after, the tree invariants must hold. Given
  that, read, scan, restart, reclaim all work, provenly. And the unproved
  Java transaction code can be tested thouroughly. Traces of the tree
  state after a Java transaction can be verfied to match the model. For
  each trace, we can show that the implementation holds. We can test
  millions of transactions, but we will not have a formal proof that every
  untested transaction works."
- 10:56: "Yes, good. I understand. This would be great to get in place. It
  is 80-20. 80 percent of the value, 20 percent of the work. It is very
  practical. Being able to test each transaction in isolation is very
  strong. And assuming that works, we have proofs for the core database
  algorithms. I like this!"
- 11:00: "First I would like to discuss a potential restart of the whole
  proofing. I think we might be stuck in too much dependence on history.
  This step would be a big change. Would the existing Lean model be
  limiting rather then a good start? My intuition is from software
  development. It is often (more often then people think) worth it to
  rewrite the software from scratch. People are afraid of sunken costs,
  but rewrites are often faster than what people think."
- 11:14: "Yes, good. Let's get started as proposed. Write it down. Use an
  agent, Fable at High."
  - On Mathlib: "I don't know. I delegate the decision to you. Feel free
    to download the tools you need."
  - On the spike's time: "Will be decided after this is written down."
  - On Lean in the release: "Keep the Lean, but ensure it is labelled as
    work in progress. Avoid mentioning it in main documentation for the
    user of BergDB. This is only relevant to me or someone else working
    with developing the database, not relevant to a database user. Do not
    "brag" about it as a feaure or benefit. Should not be mentioned in the
    end user documentation."


# 3. The concept

## 3.1 Today: the writer is proved step by step

The model's writer for the key tree mirrors Java step by step: each put
and each delete, with its splits, merges, take-back and root collapse.
The proofs must show that the tree's invariants survive every one of
these steps. That includes states in the middle of a transaction, where
the tree is half changed: a delete leaves one node under the fill (the
hole), the merges move the hole up a level at a time, and the take-back
undoes nodes that the same transaction made.

This is where the hard parts come from: the writer's books (what it notes
during a transaction), the take-back's premises, and `l4` with its moving
hole (030-01, section 1; 030-03, section 1). It is also where the size
comes from. `lean/` holds 279,000 lines. The model and the trace checkers
are about 47,000 of them, by import closure. The rest, about 230,000
lines, is proof, most of it about the writer's steps. After the night of
16 to 17 November (13 agents, about 60 landings) the best top theorem
with no premise known false still rests on `l4` (030's D1).

## 3.2 The contract

A transaction is specified by what holds when it ends, not by its steps.

Given a tree that meets the invariants, and a transaction that the writer
accepts, the writer ends in a tree that:

1. meets the invariants;
2. holds exactly the old contents with the transaction's net change
   applied: each key put has its new value, each key deleted is gone,
   every other key is as it was;
3. has changed or made only nodes that are then in D, the set of dirty
   nodes to be written to the stream; every other node is as it was.

The invariants are those of TP7 (006-26, section 2.3): the key order, the
kinds of the nodes, a live klong in every node, at most M klongs in a
node, every pointer naming a node that exists, and maybe the fill.

The exact wording is for the spike to settle. The points it must settle:

- **The fill rule.** Whether the fill that the merges keep must be an
  invariant of the contract, or whether reads are right without it. `l4`
  is about the fill only. If reads do not need it, it leaves the contract
  and becomes a cost property, tested.
- **Earlier times.** BergDB keeps every earlier state readable. The
  contract must say so. The likely form is in clause 3: a node that
  existed keeps its earlier entries, and new entries carry the
  transaction's time. Reads at an earlier time then see what they saw.
- **What "contents" means.** It must be defined from the tree alone,
  without the algorithms of get and scan. Otherwise the theorem on reads
  says nothing.
- **Accepted transactions.** A transaction that the writer refuses (a
  limit, the bound on top node ordinals of 030-02) changes nothing. The
  contract speaks of the accepted ones.

## 3.3 Proved from the contract

- **Gets and scans.** For any history of transactions in which each one
  meets the contract, starting from the empty tree: every get and every
  scan, at the latest time and at every earlier time, returns what a
  plain map returns. This is TP10 and TP11, now with one premise, the
  contract. It is the spike's theorem.
- **Recovery, restarts, lazy reading, eviction, reclaim's cut.** They
  follow from the contract and the other assumptions of section 3.5. The
  abstract model already takes each transaction's change as given
  (006-26, section 2.1), so its theorems want only that the change meets
  its assumptions (`RunOK`, TREE, A6', A-COPY). The contract must give
  those. This is step 4, and it takes over the goal of 030's D3.

## 3.4 Tested, not proved

That the writer meets the contract. This is the one large assumption,
and each transaction can be tested alone:

- **On traces.** A new check tests the contract on Java's tree before and
  after every traced transaction. A failure names one transaction, with
  the tree before it and after it. No history is needed to reproduce it.
- **In Java.** Java can check the invariants before and after each
  transaction: the whole tree in tests, the changed nodes in production.
  First in the tests (step 4); production only after its cost is
  measured.
- **The step-by-step model stays, unproved, as the oracle.** Java must
  still match it node for node on the traces, as the tree checker tests
  today in `level2.sh`. Nothing of that check is removed.

What is given up against D1's goal: a proof that the model's writer keeps
the invariants. The loss is smaller than it looks. Java was never tied to
the model by a proof, only by traces (006-26, section 2.4), so D1's
finished theorem would also have rested on a test of Java. The contract
puts that test where it is small and exact, on Java's own tree.

## 3.5 The assumptions, in one list

Every claim names these five. No such list existed before (006-26,
section 2.5).

1. **The writer's contract** (section 3.2). Tested per transaction on
   traces and by Java's own check.
2. **A synced append is durable.** Tested by Java's crash and power-loss
   tests.
3. **A crash leaves at most a torn tail.** The same tests.
4. **One writer.** Tested by Java's thread tests.
5. **The bytes decode to what was written.** Tested by the restart
   tests; damaged bytes are found on a best effort only.

A claim then reads: "proved, given these five stated assumptions, each
of which is tested". Step 4 names the exact test beside each assumption.

The theorems speak of the package's readers on the tree that the contract
describes, so a claim about Java's reads rests on four more, each tested
(030-06, finding 6; added by 030-09):

6. **Java's readers are the package's readers:** `KeyNode`'s searches,
   `Dag.getOne`, `Dag.getMany` and the top search
   (`TopDs.findSuperRootAtTime`) give what `get`, `scan` and the space root
   at a time give. Tested by the GET and SCAN lines of every traced
   transaction (`lean/contract/check.sh`, R1), and by the LIVE lines of
   the configurations with `live=1` (`hot`, `d-random`): Java's search of
   every compare value of every node at each of its times, and Java's top
   node at every time, the record times and the times between them (L1).
7. **The OP lines are the user's transaction:** what `Db.putKvs` gives the
   Dag, after the key and value transformations, is what the user's
   transaction asked for. Tested by run B's lookups against the workload
   (`conformance.sh`, `probe=K`), Java's unit tests and f-tests, and
   Java's commit-time check in its tests (030-09, section 3: each key of
   the transaction has its new value at its time).
8. **A refused transaction changes nothing:** everything that may refuse
   a transaction is checked before the go point (bergdb 005-01), so a
   history holds only the transactions that ran. Tested by
   `DbTesterLimits` (L1 to L5: nothing written),
   `DbTesterDelete.testRefusedTransUnchanged` (024-16), and
   `DbTesterRestart.testEndOfOrdinals` (005-02: the keys keep their
   values, no node in the writer's list, and the same after a restart).
9. **What run A checks holds in every run:** the contract is checked on
   the traces' run A, a writer that never restarts or evicts. Java's writer
   after a restart, with eviction and with reclaim is tied to run A by the
   stream comparisons of runs B and E (`conformance.sh`'s probe and evict
   sets, level 2 to level 4), and by Java's commit-time check, which runs
   in every unit test and f-test (030-09, section 3).

The bridge to the abstract model (030-07) speaks of the model's stream and
of the trees that the checkers build from a trace's lines, so a claim about
recovery, restarts, eviction and reclaim's cut rests on three more, each
tested (added by 030-11, finding 2):

10. **Java's records and D are the model's** for the trace's changes:
    `tracecheck` runs the model's step on every traced transaction and
    compares the record written and D (level 2 to level 4).
11. **A cut of reclaim is safe** (`CutOK`): `tracecheck` at every cut of
    the reclaim traces; that BergDB's waits give one is not proved (006-26,
    section 3.3).
12. **A trace's lines are Java's change** (`LinesOf`, 030-08, section 5):
    030-09's completeness checks, `tracecheck` (the ADD lines against the
    records) and `treecheck` (the KN lines against the model's writer).

The reads after a crash, restarts, eviction and the cut (030-14) speak of a
reader of the model's view at a time (P@t), and Java's reads after a startup
of a tree and a top that hold it, so a claim about Java's reads after a
startup rests on one more, tested (added by 030-14):

13. **Java's startup builds what the stream holds:** a tree that holds the
    model's view (030-14, `HoldsView`: each key node that Java's startup or a
    first touch reads has the entries that the model's startup gives back for
    it, its klongs well formed, and the kind, segment leaf or inner node, it
    was written with; each value its value), and the top that the stream
    holds (`topOfP`: the top nodes' root and skip pointers). That Java's
    search and reads are then right is proved (030-14). Tested by run B
    (`conformance.sh`, probe: a restart after a transaction and its lookups
    against the workload) and run E (`ereads=N`: lookups at random times
    under eviction; `erestart=K`), level 2 to level 4; the bytes by item 5.
    The kind's agreement with the level, which the reads after a crash use,
    is a checked clause, K-LEVEL (`bridgecheck`, KIND), not an assumption.

## 3.6 Later, optional

- **The model's writer meets the contract.** Such a proof plugs in as one
  self-contained theorem. It starts from a tree with all invariants, so
  it is easier than today's `l4`, which is used inside a joint induction
  and may use only what that induction has (030-01, section 2.2). Not
  planned now; it is what could restart "in 12 months or so".
- **The Java code itself.** Proving Java is a different and much larger
  kind of project (a Java verifier). Not planned.


# 4. The fresh start

## 4.1 What is new, what is kept, what is frozen

- **New:** a Lean package at `lean/contract/`. Its proofs are written
  from scratch, top-down from the contract. It never imports the old
  tree proofs.
- **A quarry, not a foundation:** the old Lean. A lemma or a definition
  may be copied when it fits. The copy is then the new package's own, and
  the report says what was copied.
- **Kept and used:** the executable model (`lean/SIS/Tree`'s definitions,
  `treeSpec`) and the trace checkers (`tracecheck`, `treecheck`), as the
  test oracle. The level scripts and `night.sh` keep running them.
- **Frozen:** the old proof line, at the tag `proofs-2026-11-17`. Nothing
  is deleted now. The old proofs are deleted only when the new package
  covers what they claimed (step 4).
- **Unchanged:** Java, the stream, the algorithms. The contract approach
  changes how we argue, not what BergDB does.
- **The source of truth** for the new statements: 027 (the algorithms in
  English) and 027-02 (the trace format), not the old Lean. Where 027 has
  no text yet, see section 9.

## 4.2 The rules carried over

From 030's rules and the week's history:

- **Statements speak of reached states, or carry what they need.** The
  contract carries what it needs: it starts from any tree with the
  invariants, so the invariants must be strong enough alone.
- **A statement found false is shown false in Lean,** with a
  counterexample.
- **Why these two:** three premises, `hCoU`, `hU` and `hHL`, were false
  as written, and later `UpHtWalk` (proved false) and `R3Calls` (believed
  false, by reading). Each spoke of every state of some form, also states
  that no run reaches, and the run tests saw only reached states (006-26,
  the correction; 030-01's log; 030-03, section 3). A theorem with a
  false premise holds vacuously.
- **The coordinator's gate:** no `sorry`, no `admit`, no `native_decide`,
  no axiom of its own; the statements unchanged against the gate's base.
- **Statements change only on Frans's word,** once the spike's report has
  fixed them. Only the coordinator lands on `main`.


# 5. Mathlib

**The coordinator's decision (Frans delegated it, 11:14): yes, Mathlib,
in the new package only.**

- **How.** `lean/contract/` is its own Lake project: its own lakefile and
  `lean-toolchain`, pinned to one Mathlib release, built with Mathlib's
  cache, with its own `lake build`. The name is lowercase, distinct from
  `lean/`'s module directories. `lean/`'s build, the trace checkers and
  the level scripts are untouched and stay without Mathlib.
- **Reasons.**
  - The new statements are about finite maps, sorted lists, sets and
    orders. That is Mathlib's home ground.
  - The old package's choice of no library cost many local helper lemmas
    (006-26, section 7: "No library").
  - A fresh start is the moment to choose.
- **Costs.** A few GB of cache; a longer first build; a pinned version to
  move now and then. The spike measures them.
- **The way back.** If the spike uses little of Mathlib, it may drop it
  and say so in its report.
- **Two notes of this item,** not part of the decision. Mathlib is
  imported, never copied into this repository. And the definitions that
  run (the invariants, the contract's check, the trace reader) should not
  need Mathlib, so that the check can later join a level script.


# 6. The steps

1. **This item.** Today.
2. **The freeze** (the coordinator). The tag `proofs-2026-11-17`; D1
   paused in 030's map. 006-29's decisions for Frans (its section 6)
   lapse, except decision 5, 028-15 (A or B), which is about Java.
   (Decision 7 was settled at 08:04, 006-30; decision 8 is the release's
   checklist, not a proof decision.)
3. **The spike** (section 7). One agent, Opus at xhigh, about a day.
   When: Frans decides after reading this item.
4. **If the spike succeeds,** without asking Frans again:
   - recovery, restarts, eviction and reclaim's cut from the contract.
     The abstract model is reused if it fits and rewritten if not; the
     spike's report says which;
   - the list of section 3.5 with the test beside each assumption;
   - Java's commit-time check of the invariants, in its tests;
   - then the old proofs are deleted; the executable model and the
     checkers are kept.
5. **Lean in the release** (Frans, 11:14): `lean/` stays, labelled work
   in progress; not in the users' documentation; not a feature. A
   separate agent does this today (`lean/README.md`: 050f6d93).


# 7. The spike's brief

This section is complete for an agent that knows nothing else.

## 7.1 The task

Find out in about a day whether the contract approach works: state the
writer's contract for BergDB's key tree, prove from it that every get and
scan is right, and check the contract on Java's traces. You ask Frans
nothing; you decide by the rules below and say so in the report.

## 7.2 Read first

- `AGENTS.md` and `items/readme.md` (the rules of the repository).
- 030's readme (the rules of all proof work) and this item, all of it.
- 006-26, sections 1 and 2: the model, how Java is tied to it, what it
  covers.
- 027-02, the trace format, section 4 (format 3: the `OP`, `KN`, `GET`
  and `SCAN` lines).
- For the key tree, in this order: 024-12, sections 2 and 6 (the design
  note and the stated properties; history, not kept current); Java's
  `KeyNode`, `Dag`, `GetMany` and `TopDs` (`java/src/bergdb/dag/`); then
  `lean/SIS/Tree/Node.lean`, `Read.lean`, `Inv.lean` and `Props.lean`,
  about 1,200 lines of definitions. 027-07 and 027-08 are stubs.
- Do not read the old proofs to learn the route. Search them only for a
  lemma you already know you need.

## 7.3 Where you work

- A clone of your own, on a branch `030-04-spike`. Other sessions share
  the main tree.
- The Lean goes in `lean/contract/`, a Lake project of its own with
  Mathlib (section 5). Nothing else under `lean/` changes, and nothing
  under `java/`.
- The report is a new subitem of 030 with the next free number (030-05
  today), with a line in 030's Files.
- Scratch files and logs: `/Users/f/fl/bench/<date>/spike/`, where
  `<date>` is the day you start.
- You do not land on `main`. You report GATED with your commit; the
  coordinator merges.
- The machine is shared. Before a long build, look for another session's
  timing run; the coordinator's start message says how.

## 7.4 What you deliver

- **(a) The invariants and the contract,** in English and in Lean, side
  by side, in a file of statements that a reader can check in an hour.
  Settle the points of section 3.2.
- **(b) The theorem, proved:** every get and scan is right, at the latest
  time and at every earlier time, for any history that meets the
  contract. With it, an example in Lean that the premises can be met
  (the empty tree and one transaction), so that the theorem is not
  vacuous.
- **(c) The fill rule:** whether the contract needs it, with the reason.
- **(d) An executable check of the contract,** run on Java's existing
  traces of the level 2 sets (`java/stress/treeconf.sh small` and
  `drain` write them to `java/build/traces/tree-SET/`). It checks each
  traced transaction alone, and the `GET` and `SCAN` lines against your
  readers. The check must be the contract of (a): the same definition,
  or a proof that they agree. If a gap is left, the report says which.
- **(e) A one-page report:** lines, hours, the share of the week used,
  what Mathlib gave and cost (cache size, build times), what was copied
  from the old Lean, what is next, and for step 4 whether the abstract
  model fits.

## 7.5 Decided in advance

- **Success:** (b) proved in a few thousand lines, and (d) passing on the
  traces. Then step 4 follows without asking Frans.
- **A stall:** the report says why, and the work stops there.
- **A trace that fails (d):** first suspect your contract, then your
  check, then Java. Report the transaction; change no Java.
- **A statement that turns out false:** show it false in Lean with a
  counterexample, then restate it and say so in the report.
- **Mathlib:** take a tagged release, and its toolchain. If a release
  exists for `lean/`'s toolchain (v4.34.1 today), take that one.

## 7.6 The gate

Before you report GATED:

- `lake build` passes in `lean/contract/`;
- no `sorry`, no `admit`, no `native_decide` and no `axiom` declaration
  in it;
- `#print axioms` of the theorems of (b) shows only `propext`,
  `Classical.choice` and `Quot.sound`;
- no file changed outside `lean/contract/`, your report and its line in
  030's Files.

## 7.7 The stop

- The coordinator stops the spike at 10 % of the week's allowance by
  making the file `/Users/f/fl/bench/<date>/spike/STOP`.
- Look for it before each new step, and at least every half hour. When
  it is there: bring the package to a state that builds, commit, write
  the report with what is done and what is not, and end.


# 8. What is not covered

Said here so that no claim overreaches (006-26, section 2.5): bytes (the
record format, checksums, meta blocks); threads (readers beside the
writer, the commit's conflict check); the cache's budget; the Pub
layer's objects; reclaim's iteration (the cut is covered, not the steps
and the waits); bounded startup's open premises (030's D4).

The first version's scope: the contract, gets and scans (the spike), then
recovery and restarts, eviction and reclaim's cut (step 4). The rest
later.


# 9. What I could not settle

- **027 has no text on the key tree yet.** 027-07 (structure and reads),
  027-08 (the writer) and 027-09 (transactions) are stubs; 027-11
  (startup) and 027-13 (reclaim) are written. So the spike's sources for
  the tree are 024-12 and the code (section 7.2), and its deliverable (a)
  is the first English text of the invariants. It could later become
  part of 027-07. Not decided here.
- **How the new package reads traces.** This item's default: no
  dependency on `lean/`'s package (the toolchains may differ); the trace
  reader is written from 027-02 or copied from `lean/Check/`. The
  coordinator may change it before the spike starts.
- **The level 2 traces are not in the main tree today.** The spike makes
  them in its clone; that needs `java/build.sh` and `lake build` in
  `lean/`.
- **Not checked:** the sizes in section 3.1 are the coordinator's
  figures. No Lean was built for this item.


# Log

2026-11-17, 11:19 to 11:26. Written by agent w04 of coord-1117, from the
coordinator's brief (`/Users/f/fl/bench/2026-11-17/w04/brief.md`) of the
discussion with Frans, 09:13 to 11:14. 030's map updated: D0 added, D1
paused.
