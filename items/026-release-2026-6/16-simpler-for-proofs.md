# 026-16. Simpler algorithms for the remaining proofs: a study

Created 2026-11-14 by Frans Lundberg. Status: done; F1 accepted (Frans, 13:46), its work is 025-03.

What could change in BergDB's algorithms to make the Lean premises that
are still open simpler to prove, without significantly degrading the
database's function or performance.

Frans, 2026-11-14, 12:45: "What could be changed in the BergDB
algorithms to simplify the Lean proofing? Without significantly
degrading the functionality or the performance of the database. The
KISS principle allows us to buy simplicity with lower performance. It
is a tradeoff. I think simplicity here is not only Java code size, but
also the Lean model specification and proofing. Actually, the Lean work
is probably a better measure of algorithm complexity than the size of
the Java code."

Frans, 12:53, on the scope: "Look at only the remaining premises. This
is to limit the scope. To not disturb what is already proven. A later
study could look at the whole model. The reasoning is that we want to
reach a fully proven model first. When we have that, we can extend it a
step at a time. And simplify it a step at a time." Changes to the stream
format may be proposed (marked as such; 026-12).

**Decided.** Frans, 2026-11-14, 13:46, after G, H, the height limit and
the moment of 024-22's MF1 were explained to him: "OK, good; I accept
the recommendation F1." (section 4.2). The work is 025-03; the rest of
the recommendation (section 8) is not decided.

Lean and Java names are those of commit `7ced25db`. A cleanup that
renames proof routes may land after it. Nothing was built or run for
this study. "I" in this study is its writer, an agent of coord-1114,
not Frans. Where a size or an effect is the writer's own estimate, the
text says so. The state of the proofs themselves is in 006-26; this
study does not repeat it.


# 1. Summary

**The ten premises are hard for three reasons. None is a feature that a
user sees.**

- **The level bounds are checked late** (`htb`, `hMSF`, `hCoF`). The
  model lets a transaction make a key node above the height bound if it
  takes the node back before it ends. So "the tree fits the fuel" has to
  be proved state by state inside a delete. This is a rule of the model.
  Java has no fuel.
- **The take-back and the previous versions** (`hchk`, `hU`, `hHL`,
  `hCoU`, `hMF`). The writer applies a transaction's operations one at a
  time, but the record may hold only the net change. A node that the
  transaction made and then left out is taken back. An old node that it
  wrote to and then left out goes back to its version before the
  transaction. The five premises speak of these half-undone states.
- **The B-tree argument of the delete** (`l4`, `d4`): the fill and the
  bound on dead klongs, through a split, the merges and root collapse.

**Recommendation.**

1. **Change no algorithm now for the ten premises.** Every change to the
   writer changes definitions that about 228,000 lines of proof speak of.
   006-26 estimates the open work at one to three prover nights. No
   candidate here saves that much without redoing more.
2. **Make one change of statement, not of algorithm** (section 4.2, F1):
   prove the top theorem for runs in which no key node is made outside
   the level bounds. Java, the stream format and the model's definitions
   stay as they are. `htb` then follows at once, and `hMSF` and `hCoF`
   become corollaries of the heights' bookkeeping that `hchk` needs
   anyway. That is my estimate; it is not tried in Lean.
3. **Decide the stable format's tree rules knowing what they fix**
   (section 8.2). Each candidate that changes the algorithm for real
   changes what a record means: merges in place and net (026-12, SF10),
   a merge without a time split first (024-22, QM2), no limit theta. Each
   removes at most one or two of the ten premises and makes proved parts
   void. So, from the proofs' side: keep format 7's tree rules (SF10,
   option (a)), and prove them. The price: a simplification found later
   is a new record format, with the old rules kept beside it.
4. **Bounded startup: measure before changing** (section 7). Q and Hp
   may grow with the database's age. The one change that would remove
   both is a narrower still-dirty test. It may also save index node
   writes. But it changes the abstract model's proved theorems, so it
   belongs to the later study. K and B are better taken from the nodes a
   transaction makes than from TP32, which has no proof route.
5. **The large simplification is another writer**, one that computes a
   transaction's net change and never takes a node back. That is a
   rewrite: 025-01, not a change to this one.

**What a change would remove, and what is best proved.**

- Removed by a change of statement: `htb`; and, with the heights' walk,
  `hMSF` and `hCoF`.
- Best proved as they are: `l4`, `d4`, `hchk`, `hU`, `hHL`, `hCoU`,
  `hMF`.
- Candidates that touch the stream format, none recommended now: merges
  in place and net (would remove `hMF` and one check of `hchk`); QM2;
  theta 0 (would make `d4` void).

**To measure before deciding:** how many traced transactions make a node
outside the bounds, and whether one more level of height covers them
(for F1); Q and Hp on Java's traces at growing ages (007-09, Q4); and,
if SF10's model run M1 is made, the Lean files it touches.


# 2. How the candidates are judged

**The cost that counts is the Lean that must be redone.** The tree's
proofs are 507 files and 227,923 lines in `lean/SIS/Tree` (006-24,
section 5). They are proofs about the model's writer, `Exec.lean`, rule
by rule. A change to a rule makes the lemmas about that rule void. My
counts of the files that name each mechanism, by text search in the
snapshot, as a rough measure of what a change would touch:

- the fuel or `SegFits`: 279 files;
- `deadOver`, the limit theta: 142;
- the merge: 122;
- the take-back: 114;
- the previous version (`toPrev`): 100;
- LE-b (`emptyKeyNext`): 57;
- `madeFor`: 44;
- `outside` and `boundsOK`, the late check of the level bounds: 28 and 32.

**Three kinds of change, from cheap to dear.**

- **A change of statement.** The theorem gets a condition on the run or
  on the parameters. No definition changes, so nothing proved is
  disturbed. The theorem says less, so the condition must be one that
  Java's runs meet and that a checker can test.
- **A change that keeps every record.** Java and the model do the same
  steps in another order or leave out a dead branch. The stream format
  is untouched. The lemmas about the changed rule are redone.
- **A change of what a record means.** A start reruns a record's puts
  and deletes with the writer's rules (027-03), so a change of a rule is
  a change of the stream format. It must be decided before 2026.6 fixes
  the format (026-12).

**The constraints** (010-01). The Pub API stays, and no candidate here
touches it or P14. S3 (section 7.1) touches the mechanism behind P5, the
startup distance. D1 (section 6.2) is the only candidate that buys
simplicity with performance, as P11 and P13 allow. No candidate adds
work to a transaction, so P1 is not in question.

**The baseline is "just prove it".** A change is worth making only when
it saves more Lean work than it costs. The sources' sizes for the
baseline: 2.5 to 3 hours for a part of `hchk`; "about 1500 to 2500
lines, a night of its own" for `htb` (024-22, section 11.1); no size for
the others. 006-26 estimates one to three prover nights for all ten.

**The three categories.** In this study "proved" means a Lean theorem
with no open premise. "Reduced" means derived from named premises that
are open. "Tested only" means checked on runs. Every premise below is
tested only, with no failure. The top theorem is reduced.


# 3. The premises in scope

**The ten premises of the top theorem.** `invGetScanOK_merges_flat`
(`LatestTopFlat.lean`) gives TP7, TP10 and TP11 for Java's parameters:
the tree keeps its invariants, and every get and scan returns what the
reference map returns. It is reduced to ten premises. 006-26, section
4.3, states each in plain words with its test counts. In short:

- `l4`: a delete with the merges keeps the live counts. The live counts
  are the fill rule: every key node that is not the root of a segment
  tree holds at least m live klongs, an inner root at least two.
- `d4`: such a delete keeps every key node at or below theta dead klongs.
- `hchk` (`OpDelChk2OK`): a delete takes back only nodes that no kept
  node points to.
- `htb` (`TakeBelowFuelDelOK`): a node that a delete takes back has a
  height below the fuel.
- `hMSF` (`MergeFitsOK`) and `hCoF` (`CollapseFitsOK`): after a merge,
  and after a step of root collapse, every segment tree fits the fuel.
- `hU` (`UpUnlinkTreeOK`): after the upward delete's loop the writer's
  tree is a tree.
- `hHL` (`UpHolderLiveRunOK`): at that point no kept node points to a
  node taken back, now or in its version before the transaction.
- `hCoU` (`CollapseUnlinkAllOK`): when root collapse replaces a segment
  root that the transaction wrote to, the tree with the root's previous
  version is a tree.
- `hMF`: every made-for id names a node from before the transaction.

**Bounded startup's tree premises** (007-09, section 5): `RunOK`, TREE,
the fit of a transaction's nodes in a record, H, Hp, Q, A, K, B and Pt.
`bounded_startup` is proved for the abstract model and reduced for
BergDB's tree.

**Other open premises of main results** (006-26, section 5.2): TP14
(`RunOK` for the tree), TP16 (TREE, A6', A-COPY), TP19 (the writer reads
only reachable nodes), TP27 (a value below every index node), and
reclaim's scheme (`CutOK`, tested only).

**What the theorem of 14 November discharges of these: nothing, as the
theorems stand** (006-26, section 5.3). It brings TREE and H near: the
tree and the nodes' heights are derived inside it, in the tree model's
own terms, and no theorem carries them to the abstract model's. It also
derives TP4 (every pointer names a node that exists). All of it rests
on the ten premises.


# 4. Fuel and heights: `htb`, `hMSF`, `hCoF`

## 4.1 The premises, and why they are hard

**The fuel.** The model's descents are recursive functions, and Lean
wants each to end. So each takes a count, the fuel, and stops with an
error when it runs out. The fuel is `Params.fuel` = (G + 1)(H + 2) + 2,
from the level bounds G (segments of a key) and H (height of a segment
tree). Java's loops have no such count. A get is right only if the fuel
suffices, so the proofs must show that every segment tree is at most as
high as the fuel allows, at every state where the proof reads the tree.
That includes the states in the middle of a delete.

**Why that is hard.** A delete can make the tree one level higher for a
moment. A delete in a full leaf splits the leaf, the split can cascade
to a new root, and the merges and root collapse of the same delete then
take the new root back (024-22, MF1). Java never writes such a root.
The trace's H is the height of the nodes Java wrote. So on 11 November
the model was changed to allow it (024-22, MF3): a node made outside G
and H is noted in a list (`W.outside`), and it is an error only if the
transaction ends without taking it back (`boundsOK`).

Since then "every height is at most H" is false inside a transaction.
The proofs go around it:

- between operations by "the doomed transaction": a transaction that
  keeps a node outside the bounds ends in an error, so it is no run
  within reach. This needs `htb` and `hchk`;
- inside an operation by counting: each split, bitmap and merge adds at
  most one to the heights seen. This is where `hMSF` and `hCoF` are
  left. The prover's plan calls it "step 4 (B), the heights inside an
  operation", with no size.

**How far from proved.** `htb`: a reach invariant through all of the
delete's writes, 1,500 to 2,500 lines by the sources. `hMSF`, `hCoF`:
no size given.

## 4.2 Candidate F1: a condition on the run (recommended)

**The change.** The top theorem gets one more condition: no transaction
of the run makes a key node outside G and H. In the model's terms each
transaction ends with `outside` empty. I call it NoOutside here; it is
not a name in the snapshot.

- **Java:** no change.
- **The Lean model:** no definition changes. One hypothesis is added to
  the top theorem, and three premises leave it.
- **Premises.** `htb` goes at once. Every height the writer knows is
  then at most H: a node read from the tree before the transaction has
  its height from its level, which is at most H by the level's formula
  (`Params.heightOf`), and a new node has it from `newKey`, which
  NoOutside bounds. H is below the fuel. For `hMSF` and `hCoF` the same
  fact gives the bound on the heights (`SeenHeightBound` at H) at every
  state, with no counting of steps. The bridge to the fuel exists
  (`segFits_of_seenHeight`). It asks that the heights the writer knows
  are exact at that state. That is the heights' walk, which exists for
  the delete with its checks (`ht_merge`, `ht_replaceRoot`) and is what
  `hchk` pays for. So I expect the two to become corollaries, stated for
  the states that a run reaches, as the prover did for the like premises
  of the full leaf and the stop node (`DelFullFitsOKR`,
  `UpCascFitsOKR`). This is my estimate, not tried in Lean.

**The cost.**

- **Function:** none.
- **Performance:** none.
- **The stream format:** untouched.
- **What the theorem then says.** It speaks of the model run with a
  height bound that covers the transaction's highest moment, not only
  the nodes written. For a given run of operations such an H always
  exists, since the theorem holds for every G and H. The model at H + 1
  makes the same tree as at H; only the nodes' level numbers differ.
  That last sentence is by reading the definitions (the writer reads a
  node's segment and height, never its level); it is not a theorem.
- **Making it:** the tree checker runs the model with the trace's own G
  and H today. To test NoOutside on Java's traces it must run with a
  larger H and compare segment and height instead of the level number.
  A small change to the checker; none to Java or the trace format.
- **Disturbing proved results:** none. The theorem with the ten premises
  stays as it is; the new one is beside it.

**Against "just prove it".** F1 trades about a night (`htb`) and an
unsized piece (`hMSF`, `hCoF`) for one hypothesis that a checker can
test. I think it is worth it. It also removes "the doomed transaction"
from the argument, which is the least direct part of it.

## 4.3 Candidate F2: the model refuses at once

**The change.** `newKey` raises the `bounds:` error when the node is
made, as it did before MF3's fix (`8e78cf65`). `outside` and `boundsOK`
go.

- **Java:** no change. **The stream format:** untouched.
- **Premises:** as F1.
- **Making it:** the checker's change of F1, and it is then needed for
  every trace, not for a test.
- **Disturbing proved results:** the lemmas of the 28 files that name
  `outside` and the 32 that name `boundsOK`, and `Within`, which every
  trusted statement uses, since it asks that each transaction runs
  without an error.

F1 gives the same for less. F2 is the tidy form for the later study,
when the model may be simplified.

## 4.4 Candidates not recommended

- **F3. No fuel: descents that end by the nodes' levels.** A get would
  recurse on the child's level, which is lower. Function, performance
  and format: none. But it changes the trusted reader (`Read.lean`), and
  with it every proof about gets and scans. Frans decided the fuel's
  form on 13 November (TP11, option C). It also would not remove the
  need: a node outside the bounds has a level that is not below its
  parent's.
- **F4. A fixed largest height in Java.** Not needed: the theorem holds
  for every H.
- **F5. A delete that never grows the tree** (QM2, section 6.3). It
  removes MF1's moment. But by my reading of `collapseRoot`, a
  transaction of many puts and then deletes of larger keys can still
  raise a tree and lower it again. So it does not give NoOutside by
  itself. Not run.


# 5. The take-back and the previous versions: `hchk`, `hU`, `hHL`, `hCoU`, `hMF`

## 5.1 The mechanism, and why it is hard

**What Java does.** A transaction's operations are applied one at a
time, in key order. The record holds the net change. Two rules make it
net:

- **The take-back.** A node that the transaction made by a split, and
  then empties, merges or collapses, is never written. Every klong of
  the transaction that names it is pointed elsewhere (`retarget`): to
  the node it replaced (`madeFor`), to the merge's new node, or to the
  root's child. Its id is used up.
- **The previous version.** A node from before the transaction that got
  klongs in it, and is then left out, loses those klongs
  (`toPreviousState`; the model's `toPrev`).

Both exist for the abstract model's assumptions on a change: a new node
is reachable at its time (A3), and entries go only to reachable nodes
(A2). The proved theorems on recovery, restarts and eviction stand on
those two.

**How common it is.** In the model's runs a merge takes back 0.10 to
1.26 nodes, the most in transactions of many deletes; every merge after
a delete's split takes back the split's node (024-22, section 2.9). So
it is no corner case.

**Why it is hard.** Between the steps of a delete the tree is half
undone. After the upward delete's loop, chain nodes are unlinked or
taken back, and the stop node still names one of them. After root
collapse has unlinked a root, and before the segment leaf above names
the child, the root is back at its previous version. The proofs need
"it is still a tree" and "no kept node points to a dropped node" at
such states. Fault 12, fixed in 2026.4, was of this kind: a klong left
naming a root that was taken back (024-11, section 1).

**How far from proved.** `hchk`: one of its checks is proved (the
path's nodes are distinct); 2.5 to 3 hours for the stop node's part; the
holder checks from the proof of TP4; the last from a walk of the
made-for ids. `hMF`: that same walk, the smallest of the ten by 006-26's
estimate. `hU`, `hHL`, `hCoU`: one invariant on previous versions and on
the holders of made nodes, no size given. The prover's note: the key
order of a transaction's operations "seems essential" to it.

## 5.2 Candidate T1: merges in place and net (stream format)

**The change** (024-22, section 2.9; QM1; 026-12, SF10, option (b)). A
node that the transaction made is changed in place by a merge, as a
split already does. The parent's entries of the transaction are the net
change: a klong of the transaction that the transaction deletes is
removed, not marked dead.

- **Java:** fewer nodes made, other ids, fewer bitmaps and shadowed
  klongs in the parent. "Perhaps 60 lines of `merge` and `mergeParent`"
  in the model, by 024-22.
- **Premises.** A merge takes a node back only when both nodes are the
  transaction's. The one case that needs `retarget` goes. If the same
  net rule were taken to the upward delete, `madeFor` would have no use
  left, and `hMF` and one check of `hchk` would go; that step is my
  extension, not in 024-22. `hU`, `hHL` and `hCoU` stay: they are about
  the upward delete and root collapse.

**The cost.**

- **Function:** none.
- **Performance:** a gain, not sized at 1M to 100M keys. Fewer nodes
  made and fewer klongs in parents; MF1's waste goes (one delete: 6 key
  nodes made, 4 taken back). Today a delete with the merges writes 0.91
  to 1.05 times the bytes of a delete without them (024-21, section 1),
  so the room for a gain in bytes is small.
- **The stream format: touched.** Ids and the parents' klongs change, so
  what a start reruns.
- **Making it:** the model, Java, the conformance sets, the C clone.
- **Disturbing proved results:** every lemma on `merge`, `mergeParent`
  and the merge's cleanup, on the tree side and on the reading side.
  122 files name the merge. The cases just closed for the merges (TP10's
  posts for the delete with the merges, the dead bound's merge pieces)
  are redone.

**Against "just prove it":** T1 removes at most `hMF` and a part of
`hchk`, the two smallest of the five, and redoes much more. Not worth
it for the proofs. It may be worth it for the specification's length;
SF10 asks that.

## 5.3 Candidate T2: link first, unlink after, in root collapse

**The change.** `replaceRoot` unlinks the root and then gives the
segment leaf above a klong to the child. Done the other way round, the
root is already out of reach when it goes back to its previous version.
A tree does not depend on a node that nothing reaches.

- **Java:** the same two steps in the other order. I expect the same
  records: the two steps change different nodes. Not tested.
- **Premises:** `hCoU` should become easy, since its hard half is "the
  tree with the root's previous version is a tree".
- **Function, performance:** none. **The stream format:** untouched, if
  the records are equal as expected.
- **Disturbing proved results:** the proved lemmas on `replaceRoot`,
  among them the take-back through a full leaf
  (`replaceRootFullJ2OK_run`).

**Better as a proof step than as a change.** A lemma that the two steps
commute gives the same without touching Java or the model. So this is a
hint for "just prove it". It is my idea, not tried. The upward delete's
loop has no such easy swap: its take-backs and the stop node's split
both use the key access path, which the split changes.

## 5.4 Candidates not recommended

- **T3. Deletes before puts in a transaction.** A put takes nothing back
  (proved). But a delete can split a full leaf, and a later delete of
  the same transaction can merge the split's node. The take-back stays.
- **T4. Write the nodes instead of taking them back.** The record would
  hold nodes that nothing reaches. It breaks A3, on which the abstract
  model's proved theorems stand, and it costs a node write for each of
  the 0.10 to 1.26 take-backs a merge.
- **T5. Limits on what a transaction may hold**, so that it never takes
  a node back. The Pub API stays, and a transaction is one record.
- **T6. A writer that computes the net change of a transaction**: the
  leaves' changes first, then one pass over the structure, each node
  made once. No take-back, no previous version, no `madeFor`. All five
  premises would have no counterpart. This is a new writer and a new
  format, with all of the tree's proofs redone: 025-01, the model-first
  rewrite, which starts from "a proved model first" and a free
  algorithm.

## 5.5 "Just prove it" is the choice here

For all five. The pieces exist: the books of the writer
(`KeepsGoodTaken`), the holders' uniqueness (`liveHolder_unique`), and
since 03:20 the fact that with the merges on the upward delete stops at
a segment leaf (`stopLeaf_of_liveCounts`, proved from the live counts
at the delete's start). The last one makes the upward delete small:
with the fill, a delete empties only a node that is both a root and a
leaf of its segment tree.


# 6. The delete with the merges: `l4`, `d4`

## 6.1 The premises, and why they are hard

`l4` is the fill rule kept by a delete, `d4` the limit theta on dead
klongs kept by a delete. Both are open for three kinds of delete only:
into a full leaf (a split and its cascade, then perhaps merges); the
upward delete; and a delete that leaves a leaf under m live klongs, so
that the merges' loop and root collapse run.

They are hard because they are the B-tree's own argument, with three
rules at once in one operation: the split of a full node, the merges
going up, and theta, which turns a write into a time split when the
node would hold too many dead klongs. `d4` has most of its pieces
proved (the split's cascade, the merge's parent, the merge's last loop).
`l4` needs an invariant that excepts the merged path's nodes until
their merge. 006-26 calls `l4` the largest of the ten.

## 6.2 Candidate D1: no limit theta (stream format)

**The change.** Theta 0: no compaction at the write (024-23's option 2
taken out).

- **Premises:** `d4` is void. The top theorem already holds for theta
  0.
- **Function:** none.
- **Performance:** a loss. With the merges alone a cold database holds
  0.85 dead klongs a live one; with theta 7 it holds 0.36, for 7 % more
  stream bytes (024-18, section 1; measured at 1M keys, not at 10M). A
  dead klong costs 16 bytes at each write of its node, 24 bytes of heap
  while the node is in memory, and a klong more for each lookup that
  passes. Memory a key is a number that BergDB tracks.
- **The stream format: touched** (theta is a rule of format 7).
- **Disturbing proved results:** the put side of the dead bound becomes
  unused; nothing breaks.

**Against "just prove it":** `d4` is mostly mechanical by 006-26, with
its pieces proved. Not worth a format change and the memory.

## 6.3 Candidate D2: merge at once, without the time split (stream format)

**The change** (024-22, MF1's option; QM2). When a delete finds its leaf
full, and the leaf's last version would hold m - 1 live klongs, the
last version is merged with the sibling at once. Today the leaf is
first replaced by its last version, a time split, whose klong can
overflow the parent, and then merged and taken back.

- **Premises.** The first open kind of delete becomes simpler: a full
  leaf is then either split with no merge after, which is the put's
  proved case, or merged at once, which is the third kind. No premise
  goes. MF1's take-backs and its moment of extra height go.
- **Function:** none. **Performance:** a small gain; how often MF1
  happens at 1M to 10M keys is not counted (QM2's default was to count
  first).
- **The stream format: touched.**
- **Disturbing proved results:** the delete's first steps and what
  follows them on the routes for `l4`, `d4` and TP10's posts.

**Against "just prove it":** it removes a case, not a premise. Decide it
with SF10, by the specification's length, not for the proofs.

## 6.4 Candidate D3: the dead bound as a statement of its own

Today the bound on dead klongs is one of the checks of TP7's invariant
(`DeadOK` in `walk`, `Inv.lean`), so TP7 needs `d4`. The bound is about
cost, not about what a read returns. Stated alone (it has a number,
TP39), it would take `d4` out of the theorem on gets and scans and
leave it as the one premise of a theorem on cost. That changes a
trusted definition, TP7's, so it is Frans's call. By the definitions a
get does not count dead klongs, but I could not verify that no reading
proof uses the bound. A change of statement, not of the algorithm.

## 6.5 "Just prove it" is the choice here

For both. No candidate removes `l4`: the fill rule is what the merges
are for.


# 7. Bounded startup's tree premises

## 7.1 Q and Hp, the two that may grow with age

**The premises.** T4 bounds the debt D. With BergDB's still-dirty test
a written node goes back into D if any node it points to is in D, by a
pointer live or dead (`javaTest`; Java's `DbHelper.hasDirtyChild`). So
the bound counts along all pointers:

- Q: the most parents of a node, by pointers live or dead, over the
  whole run.
- Hp: the height of a node of D along all pointers. For a top node this
  follows the skip pointers to older top nodes.

**Why they are hard.** They are not only unproved. Nobody knows that
they stay bounded. A node that a split replaced keeps its pointers to
its old children, so a long-lived node gathers old parents.
`BoundT4JavaExample` is a run of the model where D grows with the
replacements of the past. Neither is measured on Java.

**Candidate S1: measure them** (007-09, Q4, option A; no change). Q and
Hp on Java's traces at growing ages of one database. Cheap, and it says
whether anything more is needed.

**Candidate S2: a weaker premise** (007-09, Q4, option B; proof work,
no change). Count only the parents that point to a node of D, and the
height along live pointers and a top node's pointer to its root. T4's
count is proved again. No proved theorem is disturbed; new ones are
added.

**Candidate S3: a narrower still-dirty test** (an algorithm change).
A written node goes back into D only if it is reachable at the latest
time and points, by a live pointer, to a node of D. A top node goes back
also for a skip pointer to a node of D. A node that is no longer current
is then written at most once more, and stays out of D after that.

- **Premises:** the chains then run through reachable nodes and live
  pointers. Each such node has one parent by TREE, so Q is 1, and Hp is
  the live height H plus the top nodes that the section made. Both
  premises go, and the factor 1 + Q + ... + Q^Hp of the bound with them.
  This is my sketch, not proved. For the exact test without a virtual
  root the like is proved (`T4_debt`, no Q).
- **Function:** none intended.
- **Performance:** a likely gain. With today's test, 20 to 46 percent of
  the index nodes written at a startup distance of 50 MB are nodes that
  are no longer current, and about 10 percent of all index node writes
  are of a dead node that was written already since it died (011-04,
  "Bounds, measured"; 007-01, section 6). Those 10 percent are the
  writes that S3 would skip. "The reads it serves do not need" them, by
  the same source. The figures are from October, before the merges.
- **The stream format:** the records change, as other nodes are written.
  A record carries its got-dirty list (027-03), so I think a reader
  needs no new rule. 027-03 has the list's rules still "to be written",
  so this is not checked.
- **Making it:** Java's test, the model's test, the trace checker.
- **Disturbing proved results:** much. T1, T2, T13 and the handle
  theorems are proved for `javaTest`. The exact test breaks T1 with
  BergDB's virtual root (`exactWitness3`): a start finds an older top
  node only through the skip pointers of newer ones. So the new test
  would be a third one, with recovery and restarts proved again for it.

S3 is the one candidate in this study where simpler proofs and better
performance point the same way. But it touches the abstract model,
which is proved and in scope for the later study, not this one.
**Recommended: S1 now. If Q or Hp grows, S2. Keep S3 for the whole-model
study**, with a measurement of the writes it would save at 10M keys.

## 7.2 K and B, the costs of the merges

**The premises.** K: the nodes a transaction makes unreachable. B: the
sibling nodes its merges read, two a merge. B needs TP32 (an operation
makes at most the tree's height and one merges) and TP33 (the amortized
count). TP32 is open with no proof and no counterexample. K's first
guess, H + 1 an operation, is refuted: one delete made 11 nodes
unreachable at H = 7 (`BoundColdCascadeExample`).

**Why they are hard.** A merge adds klongs to its parent. A full parent
is split, the split can go up to a new root, and the loop then looks
for its node again. So the number of merges and of nodes left out is not
simply the tree's height.

**Candidate C1: count by the nodes made** (a change of statement). Each
merge makes at least one node and leaves out at most two. A split
leaves out one node and makes at least one. The upward delete's chain
and root collapse leave out no more nodes than the path is long. So K
is at most twice the nodes the transaction makes plus its operations'
paths, and B at most twice the nodes it makes, those taken back
included. The writer counts both (`W.made`, `W.merges`).
`bounded_startup` already takes A, the size of a change, as a premise on
the workload; K and B would join it as one premise on what a
transaction makes. Java refuses a transaction whose bound on dirty
nodes is too large (`dirtyNodeBound`); that this bound covers the nodes
made is TP23, tested on traces, not proved. TP32 is then not needed for
bounded startup. The counting lemmas are new Lean; one of the kind
exists (`execW_twoMerges_le_deletes`). The counting above is mine and
not checked in Lean. I expect it to be small beside TP32.

**Candidate C2: T1 or D2** (stream format). Both make a merge add fewer
klongs to its parent or split less, so cascades are rarer. Neither
gives a bound by itself.

**Recommended: C1.** TP32 stays a statement about cost, for later.

## 7.3 The others: bridges and counts, best proved

- **TREE and H.** Derived inside the top theorem in the tree's terms. A
  bridge lemma each (006-26, section 5.3). No change helps.
- **`RunOK` (TP14).** The take-back and the previous version exist to
  meet it (A2, A3). TP4 is derived already. Its level rule (A4) holds
  for the nodes written, since a node outside the bounds is never
  written. Best proved; no size in the sources.
- **Pt**, a top node's pointers: a root pointer and a skip pointer for
  each set bit of an ordinal below 2^48, so at most 49. A small count.
- **A**, the size of a change: a premise on the workload; the tree's
  form is TP20.
- **The fit** (`hfit`), and T3's premise that the debt fits a record:
  measured with a wide margin (028-12). A change that would remove the
  premise is 028-12's option B, a record split for a transaction that
  does not fit. Frans chose option A on 14 November. Not recommended:
  it adds a mechanism to remove a premise that Java's limits already
  keep far away.

## 7.4 The other open premises

TP14 (`RunOK`), TP16 (TREE, A6', A-COPY), TP19 (the writer reads only
reachable nodes), TP27 (a value below every index node) and reclaim's
scheme. I found no change to the algorithm that makes any of them
easier without touching what is proved.

- TP14 and TP16 are the reason for the take-back and the previous
  version, not their victims. T1's net entries would let the stronger
  A6 stand in place of A6' (024-11, section 5.6); that is a point for
  T1 in SF10, a small one.
- TP27 is close to TP7's "a live klong in every node but the space
  root". A bridge, not sized.
- Reclaim's scheme is outside this study: 026-14 proposes to model the
  whole iteration first.


# 8. Ranking and recommendation

## 8.1 The changes worth making, in order

1. **F1, the condition "no node outside the level bounds"** (section
   4.2). No change to Java, the format or the model's definitions.
   Removes `htb`; `hMSF` and `hCoF` become corollaries of the heights'
   walk. Reason: the three premises come from a rule of the model, not
   from BergDB's algorithm.
2. **C1, K and B from the nodes a transaction makes** (section 7.2).
   When bounded startup's premises are taken up. Reason: TP32 has no
   proof route, and the writer already enforces a limit on what a
   transaction makes.
3. **S1, measure Q and Hp** (section 7.1). Before any proof work on
   bounded startup.

None of the three changes Java's behaviour.

## 8.2 What to decide before the stream format is fixed

The candidates that change what a record means: T1 (merges in place and
net), D2 (merge at once), D1 (theta 0), and perhaps S3 (the still-dirty
test). From the proofs' side, none is worth making now:

- each removes at most one or two of the ten premises, the smaller ones;
- each makes proved lemmas void, on the routes that were closed last;
- until those are proved again, the proofs speak of rules that the
  release no longer has.

**So the recommendation for SF10 is option (a): the stable format keeps
format 7's tree rules as they are, and the proofs go on for them.** If
SF10's model run M1 is made, let it also count the Lean files that
option (b) touches, so that the choice has the proofs' cost in it.

**The consequence to accept knowingly.** By SF3 a later change of the
tree rules is a new record format, with the old rules kept for good. So
"simplify a step at a time" after the proofs are done will, for every
step that changes a record, add a rule set, not replace one. Steps that
keep every record stay free: the model's own simplifications, dead
branches, the order of steps. If that price is too high, the other
choice is to leave "what a record's rerun means" out of 2026.6's
promise for one release. I do not recommend that: it weakens the
promise for a study that is not yet made.

## 8.3 The premises best left to proof work

- `l4`, `d4`: the fill and the dead bound. No candidate removes `l4`.
- `hchk`, `hMF`: the checks before a take-back, and the made-for ids.
- `hU`, `hHL`, `hCoU`: the previous versions and the holders; for
  `hCoU`, try the commuting lemma of section 5.3 first.
- TREE, H, `RunOK`, Pt, the fit: bridges and counts.

## 8.4 What to measure before deciding

- **For F1:** on the conformance sets, how many transactions make a node
  outside the bounds, and whether H + 1 covers every one. In the
  provers' random runs no transaction that ended well reached H + 2
  (the scratch searches for TP32); that is not a count on Java's traces.
- **For S1 and S3:** Q and Hp on traces at growing ages. For S3 later,
  the share of index node writes that are of nodes no longer current, at
  10M keys and a startup distance of 50 MB or more.
- **For SF10:** M1, with the count of Lean files touched.
- **For T2:** one conformance run of the model with the two steps of
  `replaceRoot` swapped, to see that every record is equal. Only if the
  commuting lemma is not tried first.


# 9. For a later study of the whole model

Noted, not studied:

- With the merges always on, LE-b at the stop node and the inner stop
  node never run (proved from the live counts). Java could make them a
  `Bug`, and the model could drop the branches, if node sizes below 8
  are given up for the tests.
- F2: the model refuses a node outside the bounds at once.
- F3: descents that end by level, with no fuel.
- S3: the narrower still-dirty test.
- T6: a writer that computes the net change (025-01).
- One name for each proof route, and one top theorem (024-12, section
  1; today's cleanup).


# 10. What I could not verify

- That `hMSF` and `hCoF` follow from the heights' walk under F1. I read
  the definitions and the prover's notes; no Lean was built.
- That the model at a larger H makes the same tree but for the level
  numbers. By reading `newKey` and `gh`; no theorem says it.
- That swapping the two steps of `replaceRoot` gives equal records.
- Whether the reading proofs need the bound on dead klongs (D3).
- Whether S3 needs a new rule for a reader of the stream.
- The counting argument of C1 for K.
- The file counts of section 2 are text searches. They overcount: a file
  that names a rule does not always depend on its details.
- No performance figure here is at 10M keys or more, except where the
  source says so. The costs of T1, D2 and S3 at large sizes are not
  measured.


# Log

2026-11-14. Written for Frans (12:45, 12:53), from the snapshot at
`7ced25db`, 024-12 (section 1), 024-22 (sections 2.9, 3.2, 11.1), 007-09,
006-24, 006-26, 026-12 (SF10), 024-18, 024-21, 024-23, 011-04 and the
coordinator's notes of the prover night. Nothing built, nothing run.
