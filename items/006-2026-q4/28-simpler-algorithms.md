# 006-28 Simpler algorithms for simpler proofs: a study

Created 2026-11-16 by Frans Lundberg. Status: done.

Where the complexity of BergDB's algorithms really is, measured by the
Lean model and its proofs, and the changes to the Java code that would
make the proving significantly easier: the top three.

Frans, 2026-11-16, 08:26: "Simpler algorithms for simpler proofs. Study
the current algorithms of BergDB and how they could be simplified to
simplify the proofing. We have measured complexity and API surface,
amount of Java code and so on. But now when we have a Lean model, it
seems like a good time to check where to complexity is really. Can we
make changes to the Java code to make the prooving significantly easier.
What are the top three changes that would simplify the most. The
assumption is that the Core layer stays approximately the same or scans
are removed. Scans at the Core layer could be removed and we would still
be able to implement scans on top of getOne(). We would not get O(1)
amortized per kv, but O(log(n)) per kv where n is the database size
(total number of kvs)."

**The coordinator's defaults** (coord-1116, 08:28; Frans may overturn
them):

* The whole model, not only the open premises. 026-16 was the narrow
  study (the premises open on 14 November, keeping what is proved); its
  section 9 lists leads for this one.
* Two measures of "easier": the work left from today's `lean/` to the
  goals of 006-26, section 8; and the size of the proofs from scratch
  for the changed algorithm (025-01's model-first rewrite).
* Changes to the stream format may be proposed, marked as such (026-12).
* Lower performance may buy simplicity (Frans, 2026-11-14, in 026-16:
  "The KISS principle allows us to buy simplicity with lower
  performance."), but not a significant loss at large databases (1M to
  100M keys); the cost of each change is stated.

The study follows.

Lean and Java names are those of `main` at `bb255d4b`. Nothing was
built or run for this study but two counting scripts, kept with their
output in [28-simpler-algorithms/](28-simpler-algorithms/). "I" in this
study is its writer, an agent of coord-1116, not Frans. Proved, reduced
and tested have 006-26's strict senses. Where a size or an effect is my
own estimate, the text says so. The state of the proofs is in 006-26 and
006-27, section 8; the narrow study of the premises open on 14 November
is 026-16. This study does not repeat them.


# 1. Summary

**Where the complexity is, by the Lean lines** (section 3).

- **The key tree is 71 % of `lean/`**: 167,243 of 236,184 lines. In Java
  the index (`dag`) is 25 % of the Core's code lines (006-08). The
  stream, startup, reclaim's cut, lazy reading and eviction are 25 % of
  `lean/` together, and their theorems are proved for the model.
- **Inside the tree, the delete is the cost.** The merges, the leaf's
  delete, the upward delete and root collapse are 46 % of the tree's
  lines. The put's own rules are 9 %. The split and its cascade, which
  both use, are 18 %.
- **Three devices that no user sees take 37 % of the tree's lines**: the
  take-back with the previous versions and the writer's books (17.6 %),
  the fuel and the heights (12.6 %), the limit theta on dead klongs
  (6.7 %). The take-back is about 80 lines of the model's writer; 48 %
  of the tree's lines are in theorems that name it. The fuel is not in
  Java at all.
- **Scans are 1.3 %, gets at earlier times 0.6 %**, reclaim's touch
  0.1 %. What a read returns is cheap to prove once the tree's
  invariants hold. Keeping the invariants through a transaction is what
  costs.
- **What is open hangs on the same devices** (section 4): the bridges to
  the abstract model and the cost bounds on the writer's steps one
  operation at a time with its take-back; bounded startup's Q and Hp on
  the still-dirty test's rule over dead pointers; the last fuel premise
  on the fuel.

**No change to Java makes the two premises left (`l4`, `htbL`) cheaper
than proving them.** 026-16 said so for ten premises; with two left it
holds more strongly. The changes below pay for what comes after them, or
for a model written again.

**The top three changes**, by how much proving they remove (section 5):

1. **NW, a writer that computes a transaction's net change**, level by
   level, each node made once (026-16's T6). The take-back, the previous
   versions, the made-for ids, the retarget and every state between
   operations go. Measured from scratch it is the largest: my guess is
   under half of today's 167,000 lines for the same theorems, with no
   trial behind the guess. Measured from today's `lean/` it is negative:
   every proof of the writer is redone. It changes what a record holds,
   so the stream format. The user should see no loss; that is not
   measured. **Recommended: a one-day spike in the model before the
   stable format freezes the tree's rules** (026-12, SF10), not a change
   to today's Java.
2. **RT, Rule A with times**: a written node goes back into D only for
   a pointee's change that the node still serves (a sound form of
   026-16's S3; its sketch there is not sound as worded, section 5.2).
   Q and Hp leave bounded startup, the two premises that nobody knows to
   be bounded. Likely fewer index node writes, where 92 % of a put's
   bytes go at 10M keys (006-19). The price: lazy reading's and the
   handles' theorems are stated for today's test; their proofs are about
   31,000 lines, and how much of them must be restated is not known.
   **Recommended: measure first** (026-16's S1), then a scratch check in
   Lean; decide with bounded startup's work.
3. **OT, one tree**: the merges always on, node sizes from 8; LE-b and
   the inner stop node become a `Bug` in Java and leave the model. Small
   (LE-b: 8,000 lines, 4.8 %, name it) but free: no change of the stream
   at the users' node size, no cost to the user, 5 of the writer's 30
   `Bug` sites gone, and the gap "the merges off" closes by leaving the
   product. **Recommended: after `l4` is proved**, since LE-b's "never
   runs" is derived from `l4`.

There is no third large change to Java within "the Core stays
approximately the same". The next largest cost, the fuel, is the
model's own, and leaves by a change to the model alone (section 5.5).

**Scan removal: no** (section 5.4). No open goal is about a scan. The
scan's proofs are 2,100 to 2,500 lines, all proved, and a scan on top of
the Core needs a "next key" read, which is a scan of one kv with the
same proof. The Core itself scans: reclaim's steps (027-13, 1.4), and
reclaim's safety argument uses the scan's correctness. The user would
pay a descent for each kv.


# 2. How I measured

- **Lines.** `wc` over the `.lean` files of `lean/`, build output
  excluded: 661 files, 236,184 lines, as 006-27, section 8, has it.
- **By rule and by concern** (`count.py`, output `counts.txt`). Each file
  of `lean/SIS/Tree` is cut into declarations: a line that starts a
  theorem, a definition or the like, with the comment before it. A
  declaration gets a **rule**, the part of the writer it is about, from
  its own name, else from its file's name; and a **concern**, the
  invariant it carries, from its file's name. The files are named that
  way: `GetMergeRoot.lean` is the reading (Get) through a merge at a
  root. Each line is counted once in each of the two divisions.
- **By mention** (`mentions.py`, output `mentions.txt`). For each
  mechanism, the declarations whose text names one of its identifiers,
  and their lines. These counts overlap, and they are an upper bound of
  what a change to the mechanism touches.
- **The abstract model** by the prefixes of its proof files (`Handle`,
  `Phys`, `Cut`, `Bound`).
- **Time and lines per premise** from 006-26, 006-27 and 024-12's
  section 1, and `git log --shortstat` on `lean/SIS/Tree`.

**How rough it is.**

- Names can mislead. 18 % of the tree's lines have no rule in their
  name: the run's assembly, the invariants' definitions, frames. A file
  that names a rule does not always depend on its details.
- Lines measure the work that was done, not the least work needed. The
  proofs hold copies: the same walk of a rule once for each concern,
  near-copies for the routes (`TakeMergeRoot` and `TakeMergeRootU`,
  3,604 lines; `NoOutside*`, 4,102 lines of the run's machinery restated;
  the `_D` copies, about 600 lines; about 1,100 unused lines, 006-27).
  So a share says where the effort went. It is not a law of the
  algorithm.
- Nothing was built. I did not check which lemmas a top theorem really
  depends on; `#print axioms` and a dependency walk need a build.


# 3. Where the Lean goes: what is proved

## 3.1 lean/ by part

- `lean/SIS/Tree`, the key tree: 474 files, 167,243 lines, 4,874
  theorems. Definitions 10,131 lines, theorems 148,206.
- `lean/SIS/Proof`, the abstract model's proofs: 108 files, 50,364
  lines, 1,861 theorems.
- `lean/SIS`, its definitions and statements: 51 files, 9,262 lines.
- `lean/BergDB`, the user indexes: 5,220. The checkers: 2,413. The
  programs: 1,682.

**The abstract model's proofs by subject** (50,364 lines, all proved
for the model):

- handles, eviction: 11,491; with reclaim's cuts: 7,641;
- lazy reading: 9,733; with cuts: 2,480;
- recovery, restarts, marking (T1, T2, T13): 8,297;
- the bounds (T3, T4, a cold start's reads): 6,462;
- reclaim's cut (T8, T12, T-COVER, T-LATEST): 3,920;
- the tree's two small bridges: 340.

**Against Java's size** (006-08, section 6.2, code lines of the Core on
26 October): the index (`dag`) 3,617 of 14,677, a quarter. Memory
(`Cache3`, `Eviction`, `Residents`, `Handle`) 930. Reclaim 850. In Lean
the index is seven tenths, eviction and lazy reading 13 %, and reclaim
is only its cut. So Java's line counts understate the index by a factor
of about three, and the earlier measures (code lines, 006-08; the Core
API's 45 public methods and four data methods, 010-01, P12; the
inventories 020-01 and 024-01) could not see where the tree's cost is:
it is in the delete's rules, not in the API.

## 3.2 The tree by the writer's rule

Lines of `lean/SIS/Tree` by the rule a declaration is about:

- the merges (`merge`, `mergeParent`, `mergeUp`, `sibling`): 35,225,
  21.1 %;
- shared, no rule in the name (the run, the invariants, frames):
  30,719, 18.4 %;
- the split and its cascade (`handleFull`, `appendKlongs`): 30,544,
  18.3 %;
- the delete's leaf bitmap and its steps: 18,167, 10.9 %;
- the upward delete, the stop node, LE-b: 16,634, 9.9 %;
- the key node (klongs, searches, encoding): 7,776, 4.6 %;
- new segments: 7,651, 4.6 %;
- root collapse: 7,372, 4.4 %;
- a put into a leaf with room: 7,256, 4.3 %;
- the top node and its skip pointers: 2,529, 1.5 %;
- the scan: 2,013, 1.2 %;
- earlier times: 1,357, 0.8 %.

The rules that only a delete uses sum to 46.3 %; the put's own (new
segments, the leaf with room) to 8.9 %. The split's cascade is used by a
put into a full leaf, a delete's bitmap into a full leaf, a full stop
node and a merge's full parent.

## 3.3 The tree by concern

The same lines by the invariant that a file carries:

- the tree's shape (pointers, kinds, sizes, the writer's cache): 35,180,
  21.0 %;
- **the take-back, previous versions, made-for ids, the books**: 29,494,
  17.6 %;
- the reading, TP10: 28,104, 16.8 %;
- **the fuel and the heights**: 21,032, 12.6 %;
- key order and ranges: 13,968, 8.4 %;
- **dead klongs, theta**: 11,252, 6.7 %;
- no concern in the name: 10,449, 6.2 %;
- the live counts, the fill: 7,363, 4.4 %;
- the key node: 7,251, 4.3 %;
- the scan, TP11: 2,105, 1.3 %;
- earlier times: 1,045, 0.6 %.

The three in bold are 61,778 lines, 37 % of the tree. None of them is
about what a read returns.

**The same by mention** (the share of the tree's lines in declarations
that name the mechanism; the counts overlap):

- the take-back 47.6 %; the previous version 24.1 %; the made-for ids
  17.0 %; the retarget 6.3 %;
- the merge 32.1 %; the fuel 31.7 %; the heights 27.2 %; the split's
  cascade 26.5 %;
- dead klongs 18.6 %; segment roots and leaves 12.8 %; the upward
  delete 10.8 %; root collapse 10.5 %; the fill 7.9 %; LE-b 4.8 %;
- the top node 3.6 %; the scan 2.4 %; earlier times 0.8 %; reclaim's
  touch 0.1 %.

## 3.4 Rules against proofs

The model's writer, `Exec.lean`, is 1,175 lines. Its rules against the
proof lines of 3.2 and 3.3:

| Rule in `Exec.lean` | Its lines | Proof lines |
|---|---|---|
| the take-back, `unlink`, `retarget`, made-for | about 80 | 29,494 |
| the fuel (`Params.fuel`, the descents' counts) | under 20 | 21,032 |
| the merges | 291 | 35,225 |
| the split and its cascade | 168 | 30,544 |
| the upward delete and LE-b | 130 | 16,634 |
| root collapse | 67 | 7,372 |
| the put (`setValue`, `setNode`, `putSegs`) | 59 | 14,907 |
| the scan (in `Read.lean`) | about 165 | 2,105 |

The first two rows are concerns, the others rules, so the rows overlap.
The point stands: the take-back and the fuel are a few lines of
definition and a third of the proofs.

## 3.5 What the counts say

- **A rule is walked once for each concern.** The split's cascade has
  10,322 lines for the tree's shape, 9,463 for the reading, 3,100 for
  the ranges, 2,400 for the dead klongs, 1,700 for the take-back, 1,200
  for the fuel, 1,100 for the fill. The merge the same: 9,630 for the
  take-back, 6,900 for the shape, 5,100 for the reading, 4,400 for the
  ranges. So the size is rules times concerns. Each concern removed
  takes a column away; each rule removed a row.
- **The costly concerns are those of a state inside a transaction.**
  The take-back's books and the fuel inside a delete speak of the
  writer's tree between two steps of one operation. The reading and the
  ranges at a transaction's end are the smaller part.
- **Prover cost followed the same line.** From 16:13 on 13 November to
  03:45, `lean/` grew by 142,295 lines; that day and night used 72 % of
  a week's allowance. Every put case was proved, and nine of the ten
  premises left were about steps that only a delete takes (006-26,
  sections 1 and 7). On 15 November five premises left for 13,500 lines
  and 8 % of a week (006-27, section 8): about 2,700 lines a premise,
  most of them by a change of the theorem that used the premise, not by
  a proof of it as stated. Three of the ten were false as stated
  (006-26's correction), and two more are believed false: all five are
  statements about a state inside a transaction.
- **The abstract model is done, and it is the cheaper part.** It is
  proved for any structure that meets its assumptions; what is open
  there is that BergDB's tree meets them (section 4).


# 4. Where the Lean goes: what is open

For each open goal of 006-26, section 8, the mechanism that makes it
hard.

- **`l4`, a delete keeps the fill** (TP7's last premise but the fuel's).
  Hard because the merges' loop, the split inside a delete and root
  collapse run in one operation, and the fact carried is not local: the
  merged path's nodes are excepted until their merge. 3,000 lines or
  more by copies, much less by 024-12's option (b). The local facts are
  proved (TP34 to TP38: what a merge or a split makes is filled).
  Mechanism: the delete's rules one step at a time.
- **`htbL`, a node taken back is below the fuel.** Hard only because the
  model's readers and descents count steps against one fixed number
  (025-05, sections 3 and 4.5). Java has no fuel. Mechanism: the fuel,
  and the node made above the height bound for a moment (024-22, MF1).
- **TP8, no `Bug`**: tested only. The model's writer has 30 `Bug`
  sites: 11 in the merges, 5 in LE-b, 4 in the take-backs, 3 in the
  upward delete, 7 elsewhere.
- **The bridges TP14 (`RunOK`), TP16 (TREE, A6', A-COPY), TP19.** The
  tree and TP4 are derived inside the top theorem in the tree's own
  terms (klongs, `PutInv`, the writer's overlay). The abstract model
  speaks of entries, live children and reachability. Hard for two
  reasons: two forms of the same structure, and A2 and A3 (entries go
  only to reachable nodes, a new node is reachable), which are exactly
  what the take-back and the previous version exist to keep (026-16,
  section 5.1). Mechanism: the take-back again, and the two forms.
- **Bounded startup.** Q and Hp: the still-dirty test puts a written
  node back into D for any pointee in D, by a pointer live or dead, so
  the bound counts along dead pointers, and the model has runs where D
  grows with the replacements of the past (`BoundT4JavaExample`).
  Mechanism: Rule A over all pointers. K and B: a merge adds klongs to
  its parent, a full parent splits, the loop looks for its node again;
  the first guess for K is refuted. Mechanism: the cascade inside the
  merges' loop. H: a bridge. A, Pt, the fit: counts and a premise on the
  workload.
- **The costs** (TP20 to TP23, TP26, TP31 to TP33). TP32 (a delete
  merges at most once a level) has no proof and no counterexample.
  Mechanism: the same loop, and a transaction's operations applied one
  at a time, each with its own cascades.
- **T-SCHEME, reclaim's waits give safe cuts.** Not hard by a mechanism
  of the tree: the iteration is not in the model at all (027-13, section
  5; 026-14). Its written argument uses three facts of the tree: the
  steps' scans cover every key up to E (so the scan's correctness,
  TP11), a live key below every index node (TP27, from the upward
  delete and the fill), and Rule A at the wait for the safe position.
- **TP24, the skip pointers' search; TP12.** Small, tested only.

So the open work has three roots: the writer's steps inside a
transaction (`l4`, the bridges, K, B, the costs, TP8), Rule A over dead
pointers (Q, Hp), and the fuel (`htbL`). Reclaim is a fourth, of another
kind: not yet modelled.


# 5. The candidates

Each candidate: the change in Java and in the model; the Lean that goes
or shrinks; the open goals made easier; the cost to the user; the stream
format and the APIs; the risk. Two measures of "easier": **left**, the
work left from today's `lean/` to 006-26's goals; **scratch**, the size
of the proofs written from scratch for the changed algorithm (025-01).

## 5.1 NW: a writer that computes the net change

**The change.** Today `Dag.putKv` applies a transaction's operations one
at a time, each with its splits, merges and root collapse, and then
makes the record net: a node made and left out is taken back, an old
node written to and left out goes back to its previous version
(026-16, section 5.1). NW does the work in two passes:

1. the operations, which come in key order, are sorted to their
   leaves, and each leaf's new contents are computed; no node is made,
   split or merged;
2. one pass up the tree, a level at a time: each changed node gets its
   net klongs once; a node over the size is split, one under the fill is
   merged with a neighbour, a root with one child collapses, a new
   segment's tree is built once from all its keys. Each node is made at
   most once, and every node made is linked.

The tree is the same: the same nodes, klongs, searches, fill, theta,
segments, top nodes, gets and scans. Only the order of the writer's
work changes. This is 026-16's T6, taken here as a candidate.

**What goes in Lean.**

- The take-back with `retarget`, `unlink` and `toPrev`, the made-for
  ids, `taken`, `outside` and the doomed transaction, the checked copies
  of the delete (`putKvDelChk2` to `8`), the books of a state between
  operations (`KeepsGoodTaken`, `TakeJ2`, `DelInvJ`): the concern of
  29,494 lines, and a part of every walk that carries it (47.6 % of the
  tree's lines are in declarations that name the take-back).
- MF1, and with it the moment above the height bound: the fuel inside a
  delete has nothing to speak of.
- The rules-times-concerns product of 3.5 shrinks on both sides: one
  walk up the levels in place of a walk for each rule of the delete,
  and the invariants are asked at a transaction's end, not at every
  state between operations.

**Open goals made easier.**

- TP14 (A2, A3) and TP19 hold by construction: a node is made when its
  parent's level links it.
- K, B, TP20, TP23 and TP32 become counts over the levels: a changed
  node is split or merged once, so "at most once a level" is the
  shape of the pass, not a theorem about a loop that looks again.
- `l4` becomes a statement about one level, from TP34 to TP38, which
  are proved.
- TP8: the take-back's 4 `Bug` sites go.
- `htbL` has nothing to speak of: no node is taken back.

**The two measures.**

- **Left: negative.** Every proof about the writer is void: most of the
  148,206 theorem lines of the tree. What stays: the key node (7,800
  lines), the readers and the scan given the invariants, the merge's
  and the split's pure functions (TP34 to TP38), the abstract model.
- **Scratch: the largest gain.** My guess: TP7, TP10 and TP11 in under
  half of today's 167,000 lines. No trial is behind it. The nearest
  evidence: every put case was proved before any delete case, and the
  put's own rules are 9 % of the lines.

**The cost to the user.** None intended. Fewer nodes are made: today a
merge takes back 0.10 to 1.26 nodes, and one delete of MF1 makes 6 key
nodes and takes 4 back (024-22, section 2.9). A delete with the merges
writes 0.91 to 1.05 times a delete's bytes without them (024-21), so
the room for a gain in bytes is small. Write amplification, memory a kv
and the reads are those of the same tree. A transaction's latency: the
second pass is work that the cascades do today; not measured. Nothing
here is measured at 1M to 100M keys.

**The stream format and the APIs.** The Pub API and the Core API stay.
The stream format changes: ids, and which nodes a record holds; a start
reruns a record's operations with the writer's rules (027-03), so the
rules are the format.

**The risk.** High. A new writer is new code in the part where release
2026.4's faults were (fault 12 was a take-back fault, 024-11). The C
clone and the conformance sets follow. Java's traces cannot check the
new model until Java follows it; until then the model is checked by its
own runs (025-01, section 4).

**Why it is here at all.** Because of the stable format. If 2026.6
freezes format 7's tree rules (026-12, SF10, option (a)), a net writer
later is a second record format with the first one's rules kept for
good (SF3). The take-back would then be in the specification, in Java
and in Lean for ever, beside its replacement. 026-16, section 8.2,
named that price and did not recommend waiting "for a study that is not
yet made". This is that study, and its counts say that the take-back is
the largest single cost. So the question of SF10 is no longer (a)
against (b). It is: freeze now, or look at NW first.

**Recommended: a spike, then Frans decides.** One agent-day: NW's
writer as a Lean definition that runs, for the whole tree (segments,
merges, theta), with `walk`'s invariants checked on the model's own
workloads, and its counts beside today's model on the same workloads:
nodes made, klongs written, bytes a transaction. No proof, no Java. The
tree model's first definition took under a day (024-12, 11 November).
The spike
says whether the writer is as short as it sounds, and gives the
user's cost as counts. If it is not clearly simpler, SF10 (a) stands as
026-16 recommended.

## 5.2 RT: Rule A with times

**The mechanism today.** A node written in a record goes back into D if
one of its pointees, live or dead, is in D (`javaTest`; Java's
`DbHelper.hasDirtyChild`). It is cheap and safe: it puts back more than
is needed. A node that a split replaced keeps its pointers to its old
children. While those children are written to, the dead node goes back
into D at each write, and is written again. In October 20 to 46 % of
the index nodes written at a startup distance of 50 MB were no longer
current, and about 10 % of all index node writes were of a dead node
already written since it died (011-04; 007-01, section 6; before the
merges).

**026-16's S3 is not sound as worded.** It lets a node go back only if
it is reachable at the latest time, by a live pointer, so that a dead
node "is written at most once more". By my reading of `dirty`
(`lean/SIS/Stream.lean`): a node is dirty while its latest version is
not good at some time at which it was reachable. Take a node x, dirty
since t0, with a child y that got dirty at t1 after t0, and x replaced
at t2 after t1. A take that writes x and not y leaves x's version with
a reference to y's version before t1. A read at a time between t1 and
t2 goes through x. So x must be written once more after y, and S3's
test does not put it back. This is my reading; it is not checked in
Lean.

**The change, as a sketch.** Keep with each node of D the earliest time
that its latest version does not serve (D has a time for each node
already, the time it got dirty). A written node x goes back into D if a
pointee y is in D with a time at or before the last time at which x
served that pointer: the time the pointer died, or the time x left the
tree. x goes back with the earliest such time, not with the record's
time. A node of the latest tree with a live pointer to a node of D goes
back as today. A dead node leaves D for good once every change from its
own lifetime below it is written.

**What it needs in Lean.**

- Without a virtual root the proofs ask of the test only `StillOK`
  (`Proof/Still.lean`): it looks at P only through its nodes, and it
  puts back every written node that is still dirty. T1, T2, T13, T8,
  T-COVER and T-LATEST are stated so, for either test.
- With a virtual root, which is BergDB's shape, they use the test
  itself (`AlgOK.virtJava`, `Proof/StepInv.lean`): the exact test fails
  T1 there (`exactWitness3`), because a start finds an older top node
  only through the skip pointers of newer ones. RT keeps today's rule
  for the top nodes for that reason. The virtual root's part of the
  proofs must still be shown for it. 35 proof files take the hypothesis
  that the test is `javaTest`.
- Lazy reading and the handles: T1-L, CC, T2-L, T12, T15 and every
  theorem over handles are stated for `javaTest` alone. Their invariant
  (`evLogic_st`: a written node not in D has no pointee in D, and names
  the latest version of each pointee, live or dead) is false for RT at
  dead pointers. 31,345 lines of proof are in the files of lazy reading
  and the handles. How many of them use the invariant at a dead pointer
  I could not find without a build.
- Bounded startup: Q and Hp go, and the factor 1 + Q + ... + Q^Hp of
  the debt's bound with them; the chains run through nodes that died
  within the last sections. `T4_debt` (the exact test, no Q) is the
  model.

**The two measures.**

- **Left:** it removes the two premises that are not just unproved but
  unknown (006-26, section 5.1). Without it, or 026-16's S2, bounded
  startup for BergDB's tree has no known route. Against that: a part of
  31,345 proved lines restated.
- **Scratch:** the abstract model's proofs would be about as large;
  the bound's would be smaller (no chains over dead pointers).

**The cost to the user.** A likely gain: the writes of dead nodes go
(about 10 % of index node writes in October's figures), and index nodes
are 92 % of a put's 867 bytes at 10M keys and 50 MB (006-19). D gets
smaller, so records and the debt at a start do. A time more for each
node of D in memory; the test compares times. Not measured, and
October's figures are from before the merges.

**The stream format.** The records change: other nodes are written. A
record carries its got-dirty list; whether a start can rebuild the
times from it I did not check (027-03 has the list's rules still to be
written, by 026-16).

**The risk.** Medium to high. The test decides what a start can read;
an error loses data after a restart, and only the model and the crash
tests would show it. The sketch is not designed: T2 asks that a restart
rebuilds the same D, times included.

**Recommended: measure, then a scratch check.** First 026-16's S1: Q
and Hp on Java's traces at growing ages, and the share of index node
writes that are of dead nodes at 10M keys with the merges, at a startup
distance of 50 MB or more. If the share is small and Q and Hp stay
small, RT is not worth its risk, and S2 serves the proof. If not: the
test in a scratch copy of the model, `StillOK` proved for it, and a
count of what breaks in `EvLogic.lean`'s users. Decide then, with
bounded startup's work.

## 5.3 OT: one tree

**The change.** With the merges on, the upward delete stops at a
segment leaf: a delete empties only a node that is both the root and
the leaf of its segment tree (`stopLeaf_of_liveCounts`). So LE-b
(`emptyKeyNext`, about 90 lines in `Dag`, 54 in the model) and the
inner stop node's bitmap never run. Java throws a `Bug` there; the
model drops the two branches and the parameter that turns the merges
off; the tests give up node sizes 4 and 6, where the thresholds'
condition fails (TP28).

**What goes in Lean.** The lemmas of LE-b: 51 declarations of 1,528
lines by name; 118 declarations of 8,029 lines (4.8 %) name it. A
branch in each walk of the upward delete (16,634 lines by rule). 5 of
30 `Bug` sites become one that is derived not to be reached.

**Open goals.** TP8 is smaller. "The merges off" (006-26, section 6.1)
is no gap any more: there is no such tree. TP2, the leftmost rule,
which LE-b exists to keep, is no rule of its own.

**The two measures.** Left: a deletion of proofs, some hours of prover
work to cut the branches from the walks; no premise goes. Scratch:
about 5 % less, and one algorithm in place of two.

**The cost to the user:** none. **The stream format:** unchanged at
node sizes from 8; the test sizes below go. **The risk:** low. That
LE-b never runs is derived from the live counts, which come from `l4`,
so today it is reduced, not proved; it is tested (0 of about 6,700
deletes; 024-12, section 1). A `Bug` stops the database if it is ever
wrong, as P7 asks.

**Recommended: after `l4`.** It is 026-16's first lead (section 9).

## 5.4 SC: scans removed from the Core

**The change, as I take it.** `Db.getMany` leaves the Core API, and a
layer above scans by one read a kv. `getOne` gives a value for an exact
key (its Javadoc), so a scan on top of it needs a form that finds the
next key: the least key after a given one at a lookup time. The other
reading, an ordered structure kept in kvs by the layer above, moves the
tree's whole problem up a layer; I do not take it further.

**What goes in Lean: little.**

- The scan's definitions are about 165 lines of `Read.lean`; its proofs
  2,105 lines by file (1.3 %), 2,495 by name, 3,954 by mention (2.4 %).
  All proved. No premise, of the ten or of today's two, is about a scan
  (006-26, section 1).
- A "next key" read is a scan that stops after one kv. Its proof is
  TP11's: the descent to the first key at or after the start, and the
  step to the next node where a leaf has no live key left in the range.
  So most of those lines stay.
- The scan asks nothing of the tree that a get does not ask. Key order
  and the ranges (13,968 lines) serve the searches of a get. The upward
  delete and the merges came from slow scans over deleted keys (020-30,
  024-11), but they are kept for storage and for a transaction's bytes:
  without the merges the index had 15.7 times the key nodes and 3.3
  times the bytes a transaction at 10M keys (024-11, section 1). So no
  rule of the writer goes with the scan.

**Open goals made easier: none.** One gets harder to state: T-SCHEME's
argument that every old value is rewritten rests on the steps' scans
covering every key up to E (027-13, section 3, REWRITES).

**The Core scans for itself.** A step of reclaim scans the live kvs from
the last key to E, keys only since 026-09, and E is found by a backward
scan of one (027-13, 1.3 and 1.4; `Reclaim.java` calls `getMany` at four
places). `NodeCollection`, `Pack` and `DbScan` scan too. So the scan
would leave the API and stay in the code, or reclaim would pay a descent
a key.

**The cost to the user.** A descent for each kv, O(log n). Today at 10M
keys with the default cache a scan costs 2.6 µs a key with its value
and a random get 7.8 µs; at 1M keys 1.3 and 2.2 (024-03, section 3). A
read of the next key in key order finds its path in memory, so it costs
less than a random get: my estimate is 1.5 to 3 times today's scan with
values, and more for a scan of keys only, where the tree walk is the
whole cost. Not measured. The Pub layer's index builds and index reads
are scans.

**The APIs.** P12's four data methods change: `getMany` out, a new form
of `getOne` in. The Pub API can stay.

**Verdict: no.** It removes under 2.5 % of the tree's proved lines at
best, no open goal, no rule of the writer, and it costs every scan and
reclaim. The scan is cheap to prove because it is a reader: all the
cost is in the writer.

## 5.5 Changes to the model alone

Not changes to Java, but they answer "where is the complexity really":
a part of it is the model's own.

- **The fuel.** 21,032 lines by concern; 31.7 % of the tree's lines
  name it. Java has none. Two ways out. (a) Descents that end by the
  key's segments and the node's height: a descent goes one segment or
  one height down at each step, checked against the heights the writer
  keeps (`gh`), with an error where a child is not one lower. The fact
  needed is then local to a pointer, not a bound on a whole tree. (b)
  Readers at a fuel above the state's next id, which every writer state
  fits (`segFits_next_of_putInv`, proved). Left: today (b) is used
  inside a delete (025-05, route P), and `htbL` is what remains;
  025-05, section 4.5, sizes the full form at 4,000 lines or more of
  restated reading, against step 8 for `htbL`. So finish step 8.
  Scratch: no fuel, form (a). It changes the trusted readers, whose
  fuel Frans decided on 13 November (TP11, option C).
- **One walk for all concerns.** By 3.5 a rule is walked once for each
  concern. 024-12's option (b) for `l4`, the delete's obligations over
  an invariant of the consumer's choice, is the step in that direction
  (route P did it for the fuel). It is a statement change, Frans's
  decision 1 of 006-27. The counts support (b).
- **Two forms of the tree.** The writer works on klongs, the abstract
  model on entries. The bridges TP14 and TP16 are partly a translation.
  A new model should state the tree's invariants in the abstract
  model's terms from the start.
- **The dead bound as a statement of its own** (026-16, D3). `d4` is
  proved on the joint route since 15 November, so nothing is left to
  gain.

## 5.6 Others, briefly

- **Merges in place and net, and the merge at once** (026-16's T1 and
  D2; SF10's option (b)). The retarget goes (188 declarations of 10,596
  lines name it) and MF1 goes. But the merge's rules are 21 % of the
  tree and are redone, and no open premise leaves. 026-16 judged it not
  worth it for the proofs; the counts agree. NW contains it.
- **No limit theta** (026-16's D1). The concern is 11,252 lines, all
  proved. It costs memory a key (0.85 dead klongs a live one against
  0.36; 024-18). No.
- **No merges, or merges by reclaim only.** The fill would go, and `l4`
  with it. But LE-b and the inner stop node come back, and the index
  after scattered deletes is 2 to 20 times its size (024-11). No.
- **Write a node instead of taking it back** (026-16's T4). Breaks A3
  and costs up to 1.26 node writes a merge. No.
- **Keys without segments.** New segments are 7,651 lines by rule;
  12.8 % of the lines name segment roots and leaves; root collapse and
  the upward delete's chain exist for segment trees. But a key node of
  fixed 16-byte klongs is what gives the memory a key and the speed. A
  tree with keys of any length in its nodes is another database. Not
  "approximately the same Core". No.
- **A simpler top node.** The skip pointers are 3.6 % by mention; TP24
  is open; the exact still-dirty test fails because of them; Hp and Pt
  come from them. I did not study an alternative. A lead.
- **Reclaim by the stream's order.** A step would read the old stream
  and put again each value that a get still finds there (a value node
  holds its key). REWRITES would need no scan and no E. It is a new
  reclaim with other costs, and reclaim's rules have just become stable
  (027-13). Not studied; a lead for 026-14's addition 1.
- **No history inside the nodes.** Dead klongs, time splits and the
  cascade inside a delete all come from a node holding its past. The
  abstract model's Lemma M rests on it. Not "approximately the same
  Core". No.


# 6. Ranking and recommendation

**By what each removes** (scratch; then left):

1. **NW**, the net writer: the take-back's concern (17.6 %) and the
   states inside a transaction, on which the bridges and the costs
   wait; under half the tree's proofs, by my guess. Left: negative.
2. **RT**, Rule A with times: Q and Hp, the two premises with no known
   route; fewer index node writes. Left: positive for bounded startup,
   at the price of restating a part of lazy reading and the handles.
3. **OT**, one tree: about 5 %, free.
4. The fuel, in the model alone: 12.6 %. Left: finish `htbL`.
5. SF10 (b) with D2: contained in NW; alone not worth it.
6. **SC**, scan removal: under 2.5 %, with a cost. No.

**What to do, in order.**

1. **Go on proving `l4` and `htbL` as they are** (006-27, decisions 1
   and 2). No change here makes them cheaper. For `l4`, option (b).
2. **OT after `l4`.**
3. **Before SF10 is decided: NW's spike**, one agent-day, a model that
   runs and its counts (5.1). Then Frans decides between freezing
   format 7's tree rules and a net writer first. If NW is taken, it is
   025-01's work scoped to the tree's writer: the model and its proofs
   first, then Java. If not, 026-16's recommendation for SF10 stands.
4. **For bounded startup: 026-16's S1 first**, with the share of dead
   nodes' writes at 10M keys; then RT's scratch check or S2.
5. **Keep the scans.**
6. **In the next model, whenever it is written**: no fuel, one walk for
   all concerns, the tree's invariants in the abstract model's terms.

**What I would not do:** change `Dag` now for the proofs' sake. The
tree's top theorem is two premises from proved, and every change to the
writer voids proofs that speak of it rule by rule.


# 7. Questions for Frans

Each with my default, which the study follows.

1. **How is a scan built on `getOne`?** `getOne` finds an exact key
   only. Default: I took your idea as a "next key" form of `getOne`
   (5.4). The verdict is no under either reading.
2. **Is a new writer under the same Core API "approximately the same
   Core"?** Default: yes, since the tree and the reads are the same; so
   NW is a candidate. If no, the top three are RT, OT and nothing large.
3. **May SF10 wait for NW's spike?** Default: yes, one agent-day, when
   usage allows. The format is not frozen for the take-back before the
   spike is read.
4. **May the tests give up node sizes 4 and 6** (OT)? Default: yes,
   after `l4`.
5. **S1's measurement for RT**: Q, Hp and the dead nodes' writes at 10M
   keys. Default: the coordinator plans it when the machine has room; no
   change to Java before it.
6. **The trusted readers' fuel** (TP11, option C, 13 November): may a
   later model end its descents by height instead? Default: not in
   today's model; in the next one.


# 8. What I could not verify

- **Every share is a count by names.** No build, so no dependency walk:
  which lines a top theorem really uses, and which a change would void,
  are not measured.
- **NW's size from scratch.** A guess, with no model and no proof
  behind it. That the pass up the levels is short for BergDB's tree,
  with a node's history, theta and the segments, is what the spike is
  for.
- **NW's cost to the user.** No count of nodes, bytes or time; the
  spike gives the counts, only Java the time.
- **RT.** That S3 is not sound as worded, and that the sketch with
  times is sound, are my readings of `dirty` and `StillOK`; neither is
  checked in Lean. How much of lazy reading's and the handles' proofs
  uses the invariant at dead pointers. Whether a record's got-dirty list
  lets a start rebuild the times. The October figures of dead nodes'
  writes are from before the merges, and Q and Hp are not measured.
- **OT.** That the model's and Java's tests need node sizes 4 and 6 for
  nothing else. LE-b's "never runs" is reduced to `l4`, not proved.
- **SC.** The cost of a "next key" read a kv is an estimate from 024-03's
  get and scan figures, not a run. I did not read `NodeCollection`,
  `Pack` and `DbScan` to see what they scan for.
- **The fuel, form (a).** That descents by segment and height go
  through for a node made outside the level bounds: by reading `newKey`
  and `gh`, not tried.
- **Java's sizes** are 006-08's of 26 October, before the merges; the
  methods' sizes in `Dag` are rough.
- **The earlier measurements** I found are 006-08 (code lines), 010-01,
  P12 (the Core API), 020-01 and 024-01 (inventories), 006-16 (MEM and
  stream bytes). If Frans means another measurement of complexity or
  API surface, I did not find it.


# Log

2026-11-16. Written by an agent of coord-1116; the skeleton at 08:32, the
study complete at 09:07 (times from `date`). Read:
006-26; 006-27, section 8; 026-16; 024-12, section 1; 025-05, sections
1 to 4; 025-01; 026-12 (SF3, SF10); 026-14; 027-13, sections 1, 3 and
5; 010-01 (P11 to P13); 006-08, section 6; 024-03, section 3; 024-11,
section 1; `lean/README.md`; `Exec.lean`, `Read.lean`, `Algorithm.lean`,
`Stream.lean`, `Proof/Still.lean`, `Theorems.lean`, `PhysTheorems.lean`
and `HandleTheorems.lean` in parts; `Db.java`'s and `GetMany.java`'s
Javadoc. Counted `lean/` by directory, the tree by rule, by concern and
by mention (`28-simpler-algorithms/count.py`, `mentions.py`, with
`counts.txt` and `mentions.txt`), the abstract model by subject, the
tree's lines per day from Git. Nothing built, nothing run but the two
scripts. Status set to done.
