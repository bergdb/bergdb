# 025-03. The top theorem with no node outside the bounds (F1)

Created 2026-11-14 by Frans Lundberg. Status: steps 1 and 2 done
(2026-11-15); step 3 does not follow from NoOutside (section 3.3).

F1 of 026-16, section 4.2. Frans, 2026-11-14, 13:46: "OK, good; I accept
the recommendation F1."


## 1. The idea

The tree model's descents carry fuel, (G + 1)(H + 2) + 2 steps, from the
bounds G (the largest segment of a key node) and H (the largest height
of a key node in its segment tree). Since 11 November (024-22, MF3) the
model lets a transaction make a key node outside G and H for a moment:
a delete in a full leaf splits it, the split cascades to a new root, and
the same delete's merges and root collapse take that root back (MF1).
Java never writes it, so a trace's H, taken from the nodes written, is
one too low for that moment. The node is noted (`W.outside`) and is an
error only if the transaction ends with it (`boundsOK`). Inside a
transaction "every height is at most H" is therefore false, and the
proofs go around it with the premises `htb`, `hMSF` and `hCoF`.

F1 adds one condition to the top theorem: no transaction of the run
makes a key node outside G and H (each `newKey` within the bounds; 026-16
calls it NoOutside). The theorem holds for every G and H, so for a run
of Java's an H that covers its highest moment is chosen. Java, the
stream format and the model's definitions do not change; the theorem
with the ten premises stays as it is, and the new one goes beside it.


## 2. The steps

1. **The checker.** The tree checker (lean/Check, TreeCheck) runs a
   trace with the trace's own G and H. It gets an option to run with a
   larger H (H + 1 first) and to compare a node's segment and height in
   place of its level number. On the conformance traces: how many
   transactions make a node outside the trace's own bounds, and whether
   H + 1 covers every one. The result goes here (section 3).
2. **The theorem.** Beside the top theorem (LatestTop.lean after 025-02's
   names step): the same conclusion with NoOutside in place of `htb`.
3. **`hMSF` and `hCoF`** as corollaries of the heights' walk under
   NoOutside (`SeenHeightBound` at H, `segFits_of_seenHeight`), as
   026-16, section 4.2, expects; stated for the states a run reaches.
4. **Open, not part of this entry:** a theorem that the model with a
   larger H makes the same tree, the levels apart (026-16, 4.2, "What the
   theorem then says"); now an argument from reading the definitions.

Every step is gated as 025-02's (a full build, the axiom audit, the
trusted closure's fingerprint, the statements unchanged).


## 3. Results

### 3.1 Step 1: the checker with a larger H (2026-11-15)

**The option.** `lake exe treecheck TRACE --hplus` runs every check of
the tree checker with the model at H + 1, `--hplus=K` at H + K
(lean/TreeCheck.lean only). Before the checks, the
trace's levels are moved to H + k (`shiftTrace`): a key node keeps its
segment and height, a top node its ordinal. So the checks that compare
levels (C-T1's nodes made, C-T9's versions) compare segment and height.
Two checks are added:

- NoOutside: in no transaction does the writer at H + k make a key node
  outside G and H + k (`W.outside` empty, a node taken back included);
- SameTree: on Java's structure before each transaction, the writer at
  the trace's own H and at H + k read and make the same nodes, with the
  same klongs, segments and heights, the same values, top node and
  noops, and take back the same nodes.

The line `hplus:` counts the transactions whose writer at the trace's own
H makes a key node outside G and H (its `W.outside` at the end; nothing
removes a node from it, so one taken back is counted), and gives the
least k that covers them. Without the option the checker is as before:
on the 205 traces below its output is that of the checker of `f06e1e6b`,
byte for byte. The model's definitions do not change, nor does the
checker's library (Check/): the new definitions are in TreeCheck.lean,
which no statement imports, so the gate's fingerprint of the trusted
closure stays as it was. (In Check/Tree.lean they changed it: a new
definition took a matcher name from `checkTx`.)

**The traces.** The tree checker's traces of the level scripts
(treeconf.sh), with the seeds of the full scripts:

- small: 7 configurations, 10 seeds each (level2.sh, step 8);
- drain: 11 configurations, 10 seeds (level2.sh, step 8);
- reclaim: 5 configurations, 5 seeds. level2.sh uses 3 seeds of them;
  level3.sh checks the same configurations, 5 seeds, with the trace
  checker (conformance.sh reclaim), here with tree=1.

In all 205 traces, 35,556 transactions, 337,162 operations. The traces
of the quick scripts (2 seeds; reclaim 1) are among them.

**The counts.**

- Transactions that make a key node outside the trace's own G and H: 2
  of 35,556, in 1 trace of 205. The trace is drain's d-long3b-5 (node
  size 8, long3 keys, G = 4, H = 3), transactions 83 and 97. Each makes
  one key node in segment 0 at height 4, H + 1: a new space root. In
  both it is made by a delete (operation 12 of 34, and 5 of 36). The
  delete's merges fill the parents, which split up to a space split at
  the root. The same delete's merges and root collapse then take the
  new root back (the rules split.space3, merge.takeback,
  rc.takeback.space). This is MF1 of 024-22. No node is outside G.
- With H + 1, all 205 traces check (TREE OK), with no failure of
  NoOutside or SameTree. The least k is 1 for d-long3b-5 and 0 for the
  other 204. So H + 1 covers every trace: yes.
- A control: d-long3b-5 with `--hplus=0`, the model at the trace's own
  H, fails NoOutside in transactions 83 and 97, as it should. With
  `--hplus=2` it checks.
- A difference in a count only: the `tree:` line's "key nodes made"
  counts key nodes by level. At H + 1 it counts the two nodes above the
  trace's H, which have no key level at H: 141,569 for drain at H + 1,
  141,567 at H.

**More seeds of drain**, beyond the level scripts: seeds 11 to 40 of the
drain set (treeconf.sh drain 40; its seeds 1 to 10 are the traces above,
byte for byte). 330 traces, 41,700 transactions, 759,001 operations. 3
transactions make a key node outside the trace's G and H, again in
d-long3b only (seeds 21, 22 and 29, H = 3): each one node in segment 0 at
height 4, made by a delete and taken back by the same delete, as above.
All 330 check at H + 1, with no failure of NoOutside or SameTree, and the
default output is that of `f06e1e6b`. The medium set was started too and
stopped: its larger traces take over 5 minutes each to check.

**What it means for step 2.** On these runs a node above the trace's H
is rare, and one level high. For every run, NoOutside holds with the
trace's H + 1, so the theorem of step 2 speaks of these runs of Java with
H + 1. SameTree adds that on these transactions, the moment above H
included, the writer at H + 1 makes the same tree as at H, the levels
apart: step 4's claim, tested here, not proved.

**The commands**, in a clone at this step's commit (java/build.sh and
lake build first):

    cd java
    sh stress/treeconf.sh small 10; sh stress/treeconf.sh drain 10
    sh stress/treeconf.sh reclaim 5
    for t in build/traces/tree-*/*.trace; do
        ../lean/.lake/build/bin/treecheck $t --hplus
    done

Each output's line `hplus:` and last line give the counts. The runs of
2026-11-15 are in /Users/f/fl/bench/2026-11-15/f1/check: the scripts
(treeconf-run.sh, all-run.sh and hplus-one.sh, with one heavy slot),
the traces (traces-205/), the outputs (hplus/, hplus-drain40/), and the
probe that finds the operation that makes the node (probe/).

**Decided by rule**, for Frans to overturn:

- the option moves the trace's levels in one place, before the checks,
  instead of changing each comparison: a smaller change, and every
  check, C-T9 included, then runs at H + k;
- SameTree was not asked for: a few lines, and it tests on Java's
  traces the claim that 026-16, section 4.2, makes by reading;
- with the option, a node outside G and H + k fails the trace
  (NoOutside), so TREE OK answers "no node ever outside";
- the new definitions are in TreeCheck.lean, the checker's command line,
  not in Check/, so that 025-02's gate passes as it is, with no change
  of its fingerprint to judge.

**The gate.** 025-02's gate.sh passed at `81d3c55b` (the trusted
closure's fingerprint and the top theorem's statement as the base's, the
axiom audit, the trace checker's tests), and level2.sh quick passed in
the clone. The checks of section 3.1 ran again with that commit's
checker: the same outputs, on all 535 traces.


### 3.2 Step 2: the theorem without `htb` (2026-11-15)

**Proved**, on the standard axioms: `invGetScanOK_merges_noOutside`
(lean/SIS/Tree/LatestTopNoOutside.lean). For the parameters of
`MergeParamsOK`, theta 0 or at least 2, and the top theorem's premises but
`htb`: after every run within reach in which no transaction makes a key node
outside G and H, the invariants hold at every time, and every get and scan at
every time returns what the reference map returns. The new definition
(lean/SIS/Tree/NoOutsideBase.lean), the only new one that the statement uses:

    def NoOutside (p : Params) (ts : List Tx) : Prop :=
      ∀ j (h : j < ts.length) noops w,
        execW p ts[j] (j + 1) (view (treeSpec p) (treeRun p (ts.take j)) j) = .ok (noops, w) →
        w.outside = []

In words: the writer's state at the end of each transaction has no node noted
in `outside`. `newKey` notes there every key node it makes outside G and H,
and nothing removes a note, also when the node is taken back; so every key
node the run makes, also for a moment in an operation, is within G and H. The
theorem's conclusion:

    ∀ ts, Within p ts → NoOutside p ts →
      (∀ t ≤ ts.length, InvOK p (treeRun p ts) t ∧ PointersOK (treeRun p ts)) ∧
      (∀ t ≤ ts.length, ∀ key, keyWf key = true →
        get p (viewOf (treeRun p ts)) t key = refGet ts t key) ∧
      (∀ t ≤ ts.length, ∀ (req : ScanReq) (limit : Nat), req.wf = true →
        (scan p (viewOf (treeRun p ts)) t req limit).map (fun kv => (kv.key, kv.h)) =
          refScan ts t req limit)

Its premises are `invGetScanOK_merges`'s, word for word, but `htb`: `hp`,
`hth`, `hchk`, `d4`, `l4`, `hU`, `hHL`, `hMSF`, `hCoF`, `hCoU`, `hMF`.

**What it says for Java.** By section 3.1, every traced run of Java's meets
NoOutside with the trace's own H + 1, so the theorem speaks of these runs in
the model at H + 1. That this model makes the same tree as at the trace's H
is SameTree, tested on the traces (3.1), not proved (step 4).

**Why the conclusion is per run.** `InvPreserved p`, `GetOK p` and the like
speak of every run within reach of p. A NoOutside for every run of p would,
by a reading of the rules, make the theorem empty: MF1's moment is not bound
to a trace's H, and a run that grows the tree to height H can meet it there
(a delete whose merges split the parents up to a new root, which the same
delete takes back); not proved. So the theorem speaks of each run with
NoOutside, and its conclusion is the bodies of `InvPreserved`,
`GetOK` and `ScanOK` for that run. The latest time's get and scan are the case
t = ts.length and are left out.

**How it is proved.**

- `htb` had one use, in `htStart_reachedU`: by the doomed transaction, every
  height the writer knows at an operation's start is below the fuel. In a
  run with NoOutside this is direct: no state of a transaction has a node
  outside (a note stays to the end), and every height above H is noted there
  (`HeightMarkedPred`), so every height is at most H
  (`heights_le_H_of_noOutside`).
- The run machinery's definitions (`OpCaseOK`, `StateOK`, `TxSegFitsOK`,
  `DelStepsOK` and 32 more) speak of every transaction within reach. Their
  run predicate R sees the state before a transaction, not the transaction,
  so none of their parameters can say NoOutside. They are restated, in
  namespace `SIS.Tree.N`, where `Within` is `N.Within`: within reach and
  NoOutside. Their text is as in their own files; each has `ofOld`: the
  definition for every run gives it for the runs of `N.Within`.
- The 119 lemmas with a hypothesis over runs are restated in N with their
  proofs as in their own files (NoOutsideRun1.lean to NoOutsideRun3.lean),
  but `htStart_reachedU`, whose bound is from NoOutside, and the 11 that
  passed `htb` on, which no longer take it. The top theorem's proof is as in
  LatestTop.lean.
- Every other lemma they use is used as it is, through a wrapper in N made by
  `n_wrap` (NoOutsideWrap.lean): it takes `N.Within` where the lemma takes
  `Within`, and gives a conclusion that is a restated definition in N's form.
  88 wrappers, each a theorem whose proof applies the lemma.

**The cost.** 6 new files, 4,000 lines; most of it the restated machinery, a
copy of about 3,000 lines of lemmas over runs. The original files do not
change, nor does anything proved.

**The gate.** A copy of 025-02's gate (f1/thm/gate.sh): it also audits the
new theorem, and it allows the trusted closure to differ from the base's by
the line of `NoOutside` only. It differed by that line. Passed at `5f20913a`
(the step's commit with main merged), landed.

**Decided by rule**, for Frans to overturn:

- NoOutside by the state at each transaction's end, not at every state: the
  same, since no note leaves `outside`, and plainer; by `execW`, a trusted
  definition (MergeProps.lean).
- The conclusion per run, as above; the latest time's get and scan left out.
- The premises as the top theorem's, over every run, not only the runs with
  NoOutside: the same text, as asked, though stronger than needed.
- The machinery restated beside the original, not generalized in place:
  nothing proved changes and the original theorem's proof stays as it was;
  the price is the copy. A run machinery that speaks of a set of runs could
  serve both theorems and remove most of the copy (an estimate, not tried).


### 3.3 Step 3: `hMSF` and `hCoF` (2026-11-15)

**They do not follow from NoOutside.** No theorem with fewer premises. Why:

- `hMSF` and `hCoF` speak of every state that meets the reading's invariants
  of the merges' loop and of root collapse (`DelInvF`, `CollGetInvF`): after
  a merge, or a replaceRoot, the state fits the fuel. At the states that a run
  with NoOutside reaches, the bound on the heights is direct, as in 3.2, also
  inside an operation.
- From the bound to the fuel (`segFits_of_seenHeight`) the heights' cache
  (`HtCache`) is needed at the state after the merge: every node not taken
  back has its live children one height below it and not taken back. The
  reading's loop invariants carry no heights. The delete's heights' walk that
  `DelFullFitsOKR` and `UpCascFitsOKR` use goes to the end of the upward loop
  (with `hU` and `hHL`), not into the merges.
- The walk through a merge exists (`ht_merge`), with a named premise, the
  merge's holder (`MergeTailHoldOK`: where the merge takes a node back, no
  kept node holds it). For the whole delete the walk is proved for its checked
  copy (`putKvDelChk2`, whose merges check the holder), and `hchk` carries it
  to `putKv` for the whole operation only, not to the states inside it.
- So the two reduce at best to the heights carried through the merges' loop
  and the collapse, with the merge's holder: a fact of the kind of `hHL` and
  `hchk`, not given by NoOutside. 026-16 (section 4.2) expected corollaries
  because the walk exists for the delete; it does, for the checked copy.

**Two routes**, not tried: the reading of the delete proved over the checked
copy, where the holder is checked, so that the walk is there at every state;
or a weaker cache without "not taken back", which is enough for the fuel (a
path of the writer's tree goes through nodes not taken back only) and which a
merge might keep without the holder, with the walk redone for it.
