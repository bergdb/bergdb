# 030-22. Reclaim's contract, written down

Created 2026-11-19 by Frans Lundberg. Status: open.

The second part of 030's aim, "reclaim chooses only safe cuts" (030-04,
section 3.5, assumption 11; T-SCHEME), written down as a contract, the
way the writer's part was done: a condition at each cut that a checker
can test on a trace, a proof that it gives `CutOK`, and what reclaim must
be shown to do to meet it. A design note, so that Frans can decide when
to attempt the proof. Written by an agent of coord-1118 ("I" below) on
2026-11-19 from 09:42, on the branch `030-22-reclaim-contract`; nothing is
proved here. One check ran in the model (section 5.2).


# Result

For Frans, in plain words. The details are in sections 1 to 8.

- **Reclaim's contract (RC):** four conditions at each cut, all testable
  on a trace. RC1: the cut is at or before the iteration's start, its end
  e and the first available time. RC2: every value that a read at e
  reaches was written at the cut or later. RC3: every index node that a
  read at e reaches has a value below it. RC4: the startup pos has passed
  the first record whose startup pos reached e (Java's two waits, pEnd and
  pSafe). Nothing per step.
- **Soundness** (RC gives `CutOK`: T-SCHEME, stated in the model) is the
  premise of `full_cut`, `cut_java_reads` and `cut_keeps_top`. Half is
  proved since 024-07 (`T_latest`). Open: the older versions that reads at
  earlier times follow, which needs an invariant on superseded versions; a
  proof about the model's take and Rule A, not about the tree or PE.
- **Meeting it:** RC3 from the writer's contract; RC2 by an induction over
  the iteration's steps, with one writer property that the contract lacks
  (a put makes a new value node; PE has it); RC1 and RC4 are Java's
  arithmetic, tested. The false premise ("a key range only shrinks") is
  not used.
- **Evidence:** Java's cuts pass C-CUT on every reclaim trace, which
  covers RC2, RC3 and RC1's order (section 5.1). In the model, T-SCHEME
  with Java's exact waits held in all 72,730 states of a run today (50
  seeds of 60 transactions), most of them with "dangerous" versions that
  no read reaches.
- **Size:** 4,000 to 9,000 lines of Lean, 2 to 4 nights (a judgment). Main
  risk: the invariant. Cheapest first step: the Lean statement and the
  invariant found by running, a few hours.
- **Recommendation:** the proof after Monday's reset (perhaps from
  Monday's day, if the week may run to 99 % then); tonight at most the
  first step.


# 1. What reclaim must give

- **The theorems after cuts take `CutOK` as a premise:** `full_cut`
  (030-07), `cut_reads`, `cut_keeps_top`, `cut_java_reads` (030-14,
  030-17) and `bridge_cut_recover`, `bridge_cut_restart`,
  `bridge_cut_handles`. The premise, `hcut`: at every restart j of the run
  that marks a cut, `CutOK` at the largest cut so far (`cutMax`), in the
  run's state after transaction j + 1. A restart after a cut with no new
  cut marks the same cut again, so `CutOK` must hold at a decided cut in
  every state from the decision until the next cut, not only at the
  decision.
- **The other premise about cuts,** `PolicyCutOK`, is proved for the
  trace's choices (`policyCutOK_of_blind`, 030-11). So `hcut` is the only
  one left. With PE's writer (`pe_full`, 030-21) these theorems hold for
  every history PE writes, given `hcut`.
- **`CutOK c` in the state after transaction k** (lean/SIS/Reclaim.lean;
  001-07, section 2.8), with f the first available time:
  1. c is at or before f;
  2. every version that a read at a time from f to k may follow is at c or
     later: the latest versions of the nodes reachable then, and, through
     each pointer to a live child, the version that Rule R gives and every
     later version of the child (a read in the running process,
     `ReadsPhys`), but not through a version that Rule A put back and that
     is still in D;
  3. every node of D has its latest version at c or later, and each
     reference of it below c names the latest version of a node not in D;
  4. the last record's top is at c or later.
- **How it is tested now:** `tracecheck`'s C-CUT computes `CutOK` at every
  CUT line of the reclaim traces: for every time from f to the cut, the
  whole closure of part 2. 0 failures in 794 CUT lines of 35 traces
  (`conformance.sh reclaim` in `level3.sh`, the night of 2026-11-18, before
  Java's PE). It tests the conclusion. It does not say why it holds, it
  does not split into local facts, and Java could not afford it at a cut.


# 2. The contract

## 2.1 Terms

- Model times are record numbers: transaction i writes record i (001-07,
  section 2.3). sp(j) is the startup pos that record j stores, fa(j) its
  first available time.
- For one iteration (027-13, sections 1.3 to 1.6): **s**, the record at
  its pStart (the table store after the user record at tStart); **c**, the
  record at its pCut (the previous iteration's pStart; s for the first
  iteration); **e**, the record of its last step (tEnd, pEnd); **v**, the
  first record with sp(v) at e or later; **k**, any state from the cut's
  decision on, until the next cut is decided.
- "A read at time t reaches x": x is reachable at t in the model's
  structure, through live pointers (`reachable`). A value node is a data
  node; it has one version, in the record of the transaction that made it.

## 2.2 The four conditions

The cut c, in the state after transaction k, meets RC if:

- **RC1 (order).** c ≤ s ≤ e ≤ fa(k), and c is at or after every earlier
  cut. Java: pCut is the previous iteration's pStart; fa := tEnd when the
  cut is decided; a cut needs pCut after the first available position.
  Soundness uses only c ≤ e ≤ fa(k) and the order of the cuts; c ≤ s is
  for RC2 (section 4.2).
- **RC2 (rewrites).** Every value node that a read at time e reaches has
  its version at c or later. (027-13, section 3, REWRITES.)
- **RC3 (live below).** Every written index node that a read at time e
  reaches has a value node below it at e, through live pointers.
  (LIVEBELOW; `T_cover`'s second premise.)
- **RC4 (the waits).** sp(k) > v. Java (`Reclaim.markSafePositions`,
  `pretruncateIfPossible`; 027-13, sections 1.5 and 1.6): the first call
  whose startup pos is at pEnd or later, the call that appends record v,
  sets pSafe to the stream length after that call's records, so to a
  record after v; the cut needs the startup pos at pSafe or later. So
  Java's cuts meet RC4, and with one record a call they meet it exactly.

Notes:

- **All four are testable from a trace:** RC1 and RC4 from the FA and CUT
  lines and each record's startup pos; RC2 and RC3 in the model's state,
  at time e (the state at the cut keeps every history, so time e can be
  read there).
- **Per step: none** is needed for soundness. A per-step form exists if
  RC2 is to be proved for reclaim's algorithm (section 4.2).
- **Left out, as in the model:** the retain duration (now - R > tEnd), the
  meta block condition (the transaction it names at pCut or later), and
  the table made durable before the physical cut (027-13, sections 1.6 and
  1.7; 001-07, section 5, steps 8 and 9). They are tested as before.

## 2.3 What it needs from the writer

- **For soundness:** what the bridge gives already for a history that
  meets `MeetsFull`: `RunOK`, with Java's still-dirty test and the marking
  (the theorems' `hj` and `hmk`). `T_latest` uses the same.
- **For RC3:** the writer's contract's invariants (`invOk` at each time:
  NonEmptyOK and KindsOK).
- **For RC2, one property more, VAL-NEW:** a put at time i makes a new
  value node, which the key's live klong names at i, and a key that the
  transaction does not write keeps its value node. The writer's contract
  does not say this. Its contents compare values by their hash
  (`contents`; `Op.put` carries the value's hash), so a writer that did
  nothing for a put of the value a key already has meets clauses 1 to 3.
  Reclaim's rewrites are exactly such puts. PE makes a fresh value node
  for every put (`applyGroups`, `fresh`, in Contract/PeWriter.lean) and
  keeps the others' nodes, so a proof for PE is short. Java is tested:
  `treecheck` compares Java's tree with the model's writer node for node
  (`treeconf.sh`, its reclaim set too), and C-CUT fails if a value before
  the cut stays reachable.


# 3. Soundness: RC gives CutOK

## 3.1 The statement

T-SCHEME, in the model's words (`checkSchemeC` in
lean/SIS/ReclaimExample.lean checks it by running; section 5.2 with Java's
waits):

    For a run that meets RunOK, with Java's still-dirty test and the
    marking: if c ≤ e, RC2 and RC3 hold at e, v is the first record with
    sp(v) ≥ e, and k is a state with sp(k) > v and fa(k) ≥ e, then
    CutOK c holds in the state after k.

Then, for BergDB's key tree, a corollary for histories that meet
`MeetsFull`: if every cut mark of the run meets RC at its state, `hcut`
holds; so `full_cut`, `cut_reads`, `cut_keeps_top` and `cut_java_reads`
hold with RC in place of `CutOK`, and for PE with `pe_full`. No existing
statement changes; new ones are added.

## 3.2 The sketch

1. **The latest versions: proved.** RC2 and RC3 at e give, by `T_cover`,
   that every index node reachable at e is in D or has its latest version
   at c or later. With sp(k) ≥ e, `T_latest` then gives: every node
   reachable at a time from e to k has its latest version, if any, at c or
   later. From this follow part 1 (RC1), part 4 (the top is reachable),
   part 2 for the latest versions (`ReadsPhys.latest`), and the first half
   of part 3 for the nodes of D that a read from e on reaches. This is
   001-07's steps 1, 3 and 5 (024-07, section 4.2).
2. **The versions a pointer leads to: open.** A version names, for each
   child, the child's latest version as of its own record (`Inv.ref`), and
   a read in the running process may follow every later version of the
   child too. The danger is a version written between c and v that names
   a version before c of a node whose rewrite was still in D. Why the
   waits exclude it, on paper:
   - such a version was written with a pointee in D, so Rule A put it back
     into D (`javaTest`), and while it is there a read follows it only by
     Rule R (the exception in `ReadsPhys`);
   - every node in D at v got dirty at v or before, so it is taken and
     written again (and perhaps put back again, with a newer version) by
     the first state whose startup pos is past v (RC4);
   - when a node gets dirty, its parent on the access path is marked with
     it (the marking, `markOf`) and is written after it, lowest level
     first (`byLevel`), or put back;
   - so in a state past the waits, a version that a read from e on reaches
     names, for each live child, a version from which every later version
     is at c or later.
   The proof needs an invariant over the versions written since c that
   the existing ones (`Inv`'s good versions; `Inv.fresh`, for the top
   nodes only) do not give. Two facts from running (section 5.2) say
   where the work is:
   - **Reads at the latest time are easy.** In every state checked, a
     node that a read at k reaches and that is not in D has a latest
     version that names the latest version of each child live at k (LNL,
     0 failures). Such reads follow latest versions only, besides D's,
     which `T_latest` covers.
   - **Reads at an earlier time from e on are the hard case.** A node
     reachable at such a time t and no longer at k has a latest version
     that may name an older version of a child, and a read in the running
     process follows every later version of that child. Versions written
     from c to v that name a version before c of a child live at a time
     from e on ("dangerous" versions) exist in half or more of the states
     past the waits, and no read reaches them (`CutOK` holds). The
     invariant must say why: such a version was written before the
     rewrite below it, or while it was in D; the marking and Rule A make
     its ancestors dirty with it, and they are all superseded, lowest
     level first, by versions that name the rewritten nodes; so no version
     that a read from e on reaches names a node of the old chain at or
     before its old version.

   Candidate lemmas, to be checked by running before any proof:
   - LNL at k (it held in every state run);
   - every version written after v names, for each child reachable at
     some time from e up to its record, a version at c or later
     (`T_latest` at the state before it gives this);
   - the put-back chain: a version written with a pointee in D is put
     back, so it is in D until its node is written again, after the
     pointee;
   - the old chain: a version that names a version of y while y has a
     later version belongs to a node that got dirty at or before that
     later version, so it is superseded or in D, unless its node was no
     longer y's parent then (the historical case, 001-07, section 5,
     step 7);
   - and the proof by induction over the transactions from e to k, with
     `T_latest` at each state from v on.
3. **D's references and its unreachable nodes: open, the same
   invariant.** Part 3's second half asks that a node of D whose latest
   version names a version before c names the latest version of a node
   not in D. The delicate case is a node of D that no read from e on
   reaches, kept in D by Rule A (001-07, section 5, step 7): `T12` proves
   that a startup from the cut stream rebuilds such a node right, given
   part 3; that part 3 holds for it is the open part.

R6 (October) found the first form of the statement false by running
(`schemeWitness`: the exception for put-back versions in `ReadsPhys` was
added then), and judged the proof "several days with an uncertain
outcome" (001-07, section 5). Since then only `T_latest` was added.

## 3.3 Where it lives

The statement and its proof are about the abstract model (`SIS`), with
`RunOK` as their only link to the tree. They can be written in
`lean/contract/`, which imports `sis`, to leave `lean/` as it is since
030-18, or beside `CutCover.lean` in lean/SIS/Proof/; the coordinator
decides. The corollary for the tree goes in `lean/contract/`, beside
`BridgeFull.lean`.


# 4. Meeting it

## 4.1 RC3, from the writer's contract

- The contract's invariants at time e say that the space root has a live
  klong unless it is a segment leaf, every key node that a live klong
  names has a live klong (NonEmptyOK), and a segment leaf's live klong
  names a value or a non-empty key node (KindsOK). By induction on the
  level, every key node that a read at e reaches has a value below it,
  provided that some key is live at e.
- Reclaim's last step, at e, puts its row (`/#i/dreclaim/-current.txt`;
  027-13, section 1.4), so a key is live at e.
- The bridge carries it to the model: what the model reaches below a node
  is what the tree's walk reaches (`walk_reachFrom`, `reachFrom_walk`,
  `mem_blive_entriesOf`); the root and the top node of time e have the
  space root below them.
- About 300 to 800 lines; no new assumption. For PE, `pe_full` gives the
  invariants.

## 4.2 RC2, from the iteration

- **A model of the iteration** on the plain map with value nodes; not
  Java's step sizes, only what decides which keys are rewritten. At tStart
  (s - 1), E is the largest live key. Each step, at its own time, scans
  the live keys after the last step's last key, in order, up to a key K at
  most E; puts again, with the same value, each whose value node is before
  c; and K becomes the last key. The last step reaches E. (027-13, section
  1.4; `maintain()`'s steps are the same steps.)
- **The invariant, after each transaction of the iteration:** every live
  key at or before the last key has its value node at c or later. A key
  that was live at its step was rewritten or was already at c or later; a
  key that was not had any later value from a put after s; a later put
  makes a new node after s, at c or later (RC1, c ≤ s); a key that is not
  written keeps its node (VAL-NEW).
- **At e:** the last key is E, so every live key up to E is covered; a key
  above E that is live at e was not live at tStart, so it was put after s.
  Every value that a read at e reaches is a live key's value: RC2.
- **Needs:** VAL-NEW, the contract's contents (a key that is not written
  keeps its value), and that Java's scan gives the map's keys and value
  nodes (030-04, 3.5, assumption 6). About 1,000 to 2,500 lines with
  VAL-NEW for PE and the link from a live key's value to a reachable data
  node through the bridge. Java against the model of the iteration stays
  tested, by RC2 at each cut, or by a line per step in the trace.

## 4.3 RC1 and RC4, Java's arithmetic

pCut is the previous pStart, fa := tEnd at the decision, pSafe is set once
the startup pos is at pEnd, and a cut needs the startup pos at pSafe: a
few lines of Java (027-13, sections 1.5 and 1.6). They stay tested: the
checker tests both at each CUT line. A Lean model of the table is possible
and buys little.

## 4.4 The false premise, and PE

- **The old argument** (001-07, section 5, step 3) covered the index nodes
  by key ranges: every index node that is current at a step whose range
  meets its key range is touched, and "a key range only shrinks when a
  node splits". That is false since 2026.4: LE-b, a left sibling taking an
  emptied child's range, RC (024-06, section 4.4, point 2).
- **Not used here.** Since 024-07 nothing in the route uses key ranges:
  RC3 and `T_cover` cover every index node from the value below it,
  whatever its range was. Nor is the touch needed for `CutOK`:
  `checkSchemeC` without any touch has no failure (024-07, section 4.3;
  section 5.2 below). The touch stays a cost property (`TouchOnPaths`).
- **PE** grows ranges too (a joined list; the first entry's compare value
  set to the empty key; 026-23, section 1.2) and leaves no empty node that
  a read reaches (the contract), so RC3 holds for PE as for the writer
  before it. PE changes nothing in the soundness, which speaks of the
  model's take and Rule A only. RC3 and VAL-NEW come from PE's proofs.
- **Java's PE** (026-25) makes more cuts with reclaim. C-CUT's counts on
  it come from the `night.sh` run that started on 2026-11-19 at 09:49
  (`level3.sh`).


# 5. Checking it now

## 5.1 On Java's traces

- **RC1**, the part that soundness uses: c ≤ fa is C-CUT's CUT-order, and
  e is the CUT's first available time; that c is at or after the previous
  cut is one comparison more. (s is not in the trace; c ≤ s matters only
  for meeting RC2.) **RC3** is CUT-live (`liveBelowFailures`, at the first
  available time, which is e). Both checked at every CUT line.
- **RC2** is implied by CUT-reach: a value node that a read at e reaches
  is reachable from f = e on, and its one version is its latest.
- **RC4** is not checked as such; C-CUT checks the conclusion. A check
  needs v, from the records' startup pos, and one comparison at each CUT
  line: a few lines in Check/Steps.lean.
- So on every reclaim trace that passes C-CUT today (0 of 794 failing),
  RC1 to RC3 hold, and RC4 holds by Java's code. A check of RC alone is
  cheap (RC2 and RC3 are one walk at e) and could run in Java's tests too.

## 5.2 In the model, with Java's waits (today)

`checkSchemeC` (024-07, section 4.3) checks T-SCHEME on example 4 with a
stricter wait than Java's: from the first record whose startup pos is
after e, rather than at e or after. Today I checked it with Java's waits
(v the first record with sp(v) ≥ e, every state with sp(k) > v and
fa(k) ≥ e), on a scratch program over the model's own `checkSchemeC`
pieces (`rewritesB`, `coverB`, `cutOKB`; the source is
[22-reclaim-java-waits.lean.txt](22-reclaim-java-waits.lean.txt), with how
to run it). 20 seeds of 30 transactions, the four startup pos policies:

- **With the touch:** 304 iterations meet RC2 and RC3, 2,595 states past
  Java's waits, 239 of them not in `checkSchemeC`'s; `CutOK` fails in 0.
- **Without any touch:** 280 iterations, 2,268 states, 219 not in
  `checkSchemeC`'s; 0 failures.
- **The hard case is exercised:** in 376 of the 2,595 states with the
  touch (and 308 of the 2,268 without) a read from e on reaches a version
  that is not its node's latest, and in 183 (195) states such a version is
  in a record from c to v. Dangerous versions (from c to v, naming a
  version before c of a child live at a time from e on) exist in 1,396
  (1,069) states. `CutOK` holds in all: no read reaches a dangerous
  version.
- **Where the work is:** LNL at k (section 3.2) holds in all 4,863 states;
  the same at the earlier times from e on, for the nodes reachable then,
  fails in 932 (795) states. So the reads at the latest time follow latest
  versions only, and the invariant is needed for the reads at earlier
  times.
- **The second wait is seldom needed in the example:** of 486 (451)
  states between the two waits (sp at e or later, at most v), `CutOK`
  fails in 0 (2). `pSafeWitness` (001-07, section 2.8) is the known case.
  The example exercises the second wait weakly; the invariant search
  should look for runs that need it.
- **The larger run, 50 seeds of 60 transactions** (5 minutes): with the
  touch 1,552 iterations and 38,093 states past Java's waits (1,402 not in
  `checkSchemeC`'s), without any touch 1,472 and 34,637 (1,330); `CutOK`
  fails in 0 of the 72,730. A read reaches a superseded version in 6,966
  (6,241) states, one from c to v in 1,492 (1,603); dangerous versions
  exist in 28,710 (25,243). LNL at k: 0 failures; at the earlier times:
  18,669 (17,533). Between the waits `CutOK` fails in 0 of 2,915 (18 of
  2,766): the second wait matters, without the touch.
- **100 seeds of 100 transactions** (the T-SCHEME check only): see the
  Log.

So a proof attempt starts from evidence: the statement survives running
in the model with Java's exact waits, including the superseded versions it
must handle, and Java's cuts meet RC and `CutOK` on every reclaim trace.


# 6. Size and risk

A judgment, by step:

1. **The statement and the checks:** T-SCHEME in Lean with Java's waits
   (section 3.1); RC4 in `tracecheck`; the reclaim set run (with Java's
   PE). 200 to 400 lines; hours.
2. **The invariant, found by running:** candidates (section 3.2) checked
   in every state of example 4's runs, as `checkSchemeC` does, with runs
   that need the second wait. Done when one holds on 100 seeds of 100
   transactions and gives parts 2 and 3 on paper. 200 to 500 lines,
   scratch; hours.
3. **The open half, proved in the model:** 2,000 to 5,000 lines; one to
   two nights.
4. **RC3 for the tree:** 300 to 800 lines.
5. **RC2:** the iteration's model, VAL-NEW for PE, the induction: 1,000 to
   2,500 lines; a night.
6. **The top theorem** for PE's histories with reclaim's cuts: 200 to 400
   lines.

In all 4,000 to 9,000 lines, 2 to 4 nights for one or two provers. For
scale: `T_cover` and `T_latest` are 232 lines; the cut proofs of the
model (T8, T9 and T12, with and without handles) about 13,500; PE's writer
about 23,000, in a day and a night.

**The main risk** is step 3's invariant: it speaks of the take, Rule A,
the marking and superseded versions together, and R6 did not find it in
October. If no invariant is found:

- prove part 2 for the lookups' reads (`ReadsAt`) only: not enough, since
  the theorems with eviction use `ReadsPhys`;
- ask whether `ReadsPhys` must still reach every later version of a child
  since handles (009): with handles a read in the running process follows
  the canonical object or a version that Rule R gives. I could not settle
  this in the time. A narrower `ReadsPhys` changes a trusted definition
  and the proofs of T9 and T12 with handles: Frans's word;
- a stronger wait in Java if the invariant needs one: a code change.

**A second risk:** a corner of Java's waits that the model refutes. Section
5.2 covers it for example 4; step 1 runs it on the reclaim set too.

**The cheapest first step:** steps 1 and 2, one agent, half a day at most.
Its output: the Lean statement, an invariant that survives running, and
RC's lines in the checker, run on the reclaim set.


# 7. Recommendation

**The proof (steps 3 to 6) after Monday's reset**, starting in Monday's
day if Frans lets agents use the week to 99 % before the reset at 22:00,
as on 16 November (006-29). Reasons:

- Steps 3 to 6 are 2 to 4 nights. Tonight could not finish them, and a
  half-done step 3 is worth little.
- The week was at 77 % at 06:08 with the stop at 85 %, perhaps 90 %: 8 to
  13 points. The day and night of 18 November took 19 (006-31, section 5).
- The uncertain part is the invariant, which steps 1 and 2 find cheaply.
  As with PE, whose trial gave its go before the proof night, the proof
  is cheaper once the invariant is known.

**Tonight, if the week allows:** steps 1 and 2 (one agent, high effort, a
few hours), so that Monday's provers start from a checked statement and
an invariant. If the stop is raised to 90 % and step 2 finds the invariant
early, step 3 could start the same night; I would not plan on it.

**What changes for 030-04, section 3.5, once proved:** assumption 11
(`CutOK`, tested at every cut by a whole-state check) becomes RC1 and RC4,
Java's arithmetic at each cut, and Java's iteration against its model for
RC2: small, local, tested assumptions. RC3 and the rest are proved.


# 8. Not settled here

- Whether `ReadsPhys` needs every later version of a child since handles
  (section 6).
- The role of the iteration's touch: not needed for `CutOK` in the model;
  whether Java still needs it for anything but its pace (024-07).
- Several records a call: v is the first record whose startup pos is at
  e or later, and Java's pSafe is after the last record of v's call, so
  Java's wait is at least as strong as RC4. RC4 needs no call boundaries,
  which the trace does not mark, and the soundness for RC4 covers Java's
  cuts.
- Bounds and costs (the lag, a step's work): not correctness, 027-13,
  section 4.


# 9. Sources

030's readme (the aim, the rules, the map); 030-04, sections 3 and 3.5;
030-07 (`full_cut`, the bridge's clauses); 030-11 (`PolicyCutOK`); 030-14;
030-17; 030-21 (PE, `pe_full`) and lean/contract/Contract/PeWriter.lean;
006-26, sections 3.3 and 6.1; 024-06, sections 4.2, 4.4 and 5.1; 024-07,
sections 4.2 and 4.3; 001-07, sections 2.3 to 2.5 and 5; 027-13; 026-23,
section 1.2; lean/SIS/Reclaim.lean (`CutOK`, `ReadsPhys`),
lean/SIS/ReclaimTheorems.lean and Proof/CutCover.lean (`T_cover`,
`T_latest`), lean/SIS/ReclaimExample.lean (`checkSchemeB`,
`checkSchemeC`), lean/SIS/Algorithm.lean (the take, Rule A),
lean/SIS/Proof/Run.lean (`Inv`), lean/Check/Steps.lean (C-CUT),
lean/contract/Contract/Statement.lean (the invariants, `contents`);
java/src/bergdb/core/Reclaim.java (`markSafePositions`,
`pretruncateIfPossible`) at c458bfea.


# Log

2026-11-19, 09:42. Started, from coord-1118's brief (030-22), on the
branch `030-22-reclaim-contract` in a clone of `main` c458bfea.

2026-11-19, 09:58. T-SCHEME by running with Java's exact waits (section
5.2), 20 seeds of 30 transactions: 0 failures; the diagnostics of
superseded versions.

2026-11-19, 10:09. 50 seeds of 60 transactions: 0 failures in 72,730
states past Java's waits (section 5.2).
