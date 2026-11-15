# 025-03. The top theorem with no node outside the bounds (F1)

Created 2026-11-14 by Frans Lundberg. Status: ready (accepted; to start
after 025-02's names step has landed).

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
on the 205 traces below its output is that of the checker of `295b0dbd`,
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
default output is that of `295b0dbd`. The medium set was started too and
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

**The gate.** 025-02's gate.sh passed at `036bedd0` (the trusted
closure's fingerprint and the top theorem's statement as the base's, the
axiom audit, the trace checker's tests), and level2.sh quick passed in
the clone. The checks of section 3.1 ran again with that commit's
checker: the same outputs, on all 535 traces.
