# 030-03. The plan for R3: a made-for invariant at afterDelete's call

Created 2026-11-17 by Frans Lundberg. Status: open (the plan; no proof started).

The plan for R3, the branch of root collapse that returns early at a root the
transaction made with no made-for entry. R3 is now the main open piece of `l4`,
the last open premise of the key tree's top theorem `invGetScanOK_merges_noTb`
(lean/SIS/Tree/HtbNoTb.lean), whose other premises `hp` and `hth` are proved for
Java's parameters (`htbL` was proved tonight, 025-05, section 8). I am the writer,
an agent of coord-1116. I wrote it on 2026-11-17 from 02:36, after reading 030-01
(sections 2.3 and 7, and its log from 23:15 on), the provers' final reports of
the night (l4a to l4d), and the Lean on `main` as of 775b0044 (03:00).


# 1. The result

- **`R3Calls` is false as stated**, by my reading (section 3). The call's facts
  say nothing of made-for entries, so a state with no entries at all meets them.
  The smallest counterexample I see has four key nodes at Java's thresholds for
  node size 8. A Lean proof of it: 800 to 2,000 lines, 2 to 4 prover-hours. Not
  recommended now (question 3).
- **R3 holds at the runs, by key order** (section 4). The deleted key k was not
  touched before in its transaction, so its value is from before the
  transaction. A fresh node (made by the transaction, no made-for entry) names
  only fresh nodes. So no node on k's path is fresh, and a split keeps a node's
  status. Root collapse never meets a fresh root on k's path.
- **MFI, exactly** (section 5), has two parts:
  - **MFL**, a link invariant: a fresh node names only fresh nodes, and an inner
    node that names a fresh node is fresh. Kept by every writer function, from
    any state; a stratum-wide invariant like MFB (MadeForOld.lean) and the
    kinds' walk (KdInv, WriterKinds*.lean). Provable as an addition.
  - **ValOld**, the key part: at a delete's start, the key's live klong names a
    node from before the transaction. It is TP10 at the level of node ids for
    one key. Not provable in one night; a narrowed premise at the runs (true,
    tested) until its own step, M6.
  - Together they give **PathOld** at the delete's start: no node on the key's
    path is fresh.
- **What travels to afterDelete's call is SegOld, not MFI** (section 6). The
  call's facts come from the delete's cases in continuation form, and two
  continuation statements about one run do not combine (l4b, 02:01). So MFI is
  used only at the delete's start, where a stratum-wide theorem gives it. What
  travels is "the segment root that root collapse finds is old or has an entry"
  (SegOld). The hole cases and the merges' rounds prove it from what they
  already prove for R1 (which node the descent finds), because every split
  keeps a node's made-for status.
- **Statement change: no.** All additions: new definitions, the hole cases and
  the hole-moving merge rounds generalized with the old lemmas as their
  instances, a new loop without `hR3`, a new top theorem. `R3Calls` and the
  `noL4` family stay, believed vacuous, until the close step (006-27,
  decision 3). The forms are type-checked (section 5).
- **The route** (section 7): steps M0 to M5, 3,200 to 7,200 lines, 2 to 6
  prover-hours; after M0, three provers in parallel; one night. Then M6, ValOld's
  proof, by its own plan: 3,000 to 7,000 lines, uncertain.
- **What else is left of l4** (section 10): one core, R4 (a hole below a
  parent's split or a cascade), in three places; 2,000 to 5,000 lines.
- **For Frans:** six questions with defaults (section 11). None blocks a start.


# 2. R3 as it stands

## 2.1 The two forms

`R3At` (LiveCollapse.lean, prover l4a, 23:46):

    def R3At (key : Key) (g : Nat) (c : Ctx) (v : W) : Prop :=
      ∀ x v1, descendToSegmentRoot key g c v = .ok (x, v1) → ∀ n v2, getNode x c v1 = .ok (n, v2) →
        n.leaf = false → n.firstTime = some c.i → v2.madeFor.lookup x = none → n.onlyLiveKlong = none

In words: at root collapse's start, the root of segment g on the key's path, if
the transaction made it, it has no made-for entry and it is inner, has no single
live klong.

`R3Calls` (LiveAssembly.lean, prover l4b, 01:44):

    def R3Calls (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
      ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
        lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
        topOf p (ctxOf p ts).view z = .ok top →
        ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
        ∀ g v, DelInvJT (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts))
            tx.base tx.base v → PutBook (ctxOf p ts) tx.base top v →
          HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v →
          LiveHoleW key g 0 (ctxOf p ts) (viewOf (treeRun p ts)) v →
          WriterWP (mergeUp key g p.fuel 0 false) (ctxOf p ts) v
            (fun merged v' => merged = true → R3At key g (ctxOf p ts) v')

In words: from every state with the call's facts, the merges' loop, if it
merged, ends where `R3At` holds. Note that v is any state with those facts, not
a state that a run reaches.

## 2.2 Where they are used

- The loop's theorems `writerWP_afterDelete_liveR`, `_liveRF`, `_liveFR` and
  `_liveTR` to `_liveTR9` take `hR3`, R3 after the loop for one call, and pass
  it to `writerWP_collapseRoot_liveW` as `LiveExit ... ∧ R3At ...`.
- `afterDelete_live_runs` and `liveDelSL_of_pieces` take `R3Calls`; the tops
  `invGetScanOK_merges_noL4` to `noL4d` carry it. The coordinator's word at
  02:10: no new top corollary carries it.

## 2.3 Why the branch is there

`collapseRoot` (Exec.lean) returns at `if made && (← replacedBy root).isNone`:
like Java's `Dag.collapseRoot`, it does not collapse a root that the transaction
made other than by a split. A node gets no made-for entry in two ways:

- `setNode` makes a new segment leaf for a prefix that has none
  (`segment.new`): no entry;
- a split or a merge of a node made by the transaction copies that node's entry
  (`setMadeFor second (← replacedBy x)`, `setMadeFor r (← replacedBy x)` in the
  in-place space splits; `setMadeFor m1 (← if lMade then replacedBy l else
  pure (some l))` in `merge`). A copy of no entry is no entry.

Every other new key node gets `some x`. So the fresh nodes (made, no entry) are
the nodes of segment trees that the transaction made under a prefix new in it,
and of their splits and merges.


# 3. Is R3Calls false?

Yes, by my reading; I built nothing in Lean. None of the call's facts mentions
made-for entries: `DelInvJT` (`DelInvT`: `PutInv`, the ranges, the books, the
kinds `KdInv`; `TakeJ2`, which is `J2N` on the node map: `TtReachedN`,
`DeadLiveN`, `OldBelowN`, `OldStartN`, `MadeStartN`, `ValsNoNodeN`), `PutBook`,
`HtInv` and `LiveHoleW`. `KdInv`'s `MadeForSeg` speaks only of entries that
exist. So a state whose `madeFor` is empty meets them, and every node it made is
fresh. l4b found the same at 01:56.

**The smallest counterexample I see.** Java's thresholds at node size 8
(`withMerges`: m = 2, c = h = 4; `mergeParamsOK_withMerges`), theta 0, after the
empty run (ts = []), a transaction whose one operation deletes k = [a, 16], a a
first segment as `keyWf` asks (seven bytes):

- S, the space root of the first state, a segment leaf from before the
  transaction, cached with one klong of the transaction: the long klong (a, R).
- R, made (id at or above B), inner, segment 1, height 1: klongs (0, L1) and
  (24, L2).
- L1, made, a leaf of segment 1, height 0: a live klong (0, y0), a klong
  (16, y1), and the bitmap that deletes it. One live klong, under m: the hole.
- L2, made, a leaf: live klongs (24, y2) and (32, y3), filled.
- y0 to y3 values of the transaction; `madeFor = []`.

The merges' loop from this state: the descent at (1, 0) finds L1 (one live
klong, under 2); its sibling is L2 on the right; 3 live klongs fit in one node
(c = 4); R gets the bitmap for L2's klong and has room (size 3 + 1 ≤ 8), so R
keeps one live klong. The next round finds R, whose parent S is a leaf: the loop
returns `true`. `collapseRoot key 1` finds R inner, made, no entry: it returns.
`R3At` at that state: R inner, made, no entry, one live klong. False.

**What a Lean counterexample takes.** The concrete state, and a proof of each
fact for it: `DelInvJT` (the tree, the ranges, the kinds with the run's kind
oracle, the books, `J2N`), `PutBook`, `HtInv` with the run's height oracle,
`LiveHoleW` (`LiveEdgesH` with the hole L1, `HoleAtW`), `Within` and the run
premise for the empty run (`latestQD_init` and the base lemmas); then the loop
and the collapse run by `simp` or `decide`. By the size of the facts: 800 to
2,000 lines, 2 to 4 prover-hours, with a medium risk that one fact fights a
concrete state. l4d's `upHtWalk_false` was cheap because `HtJ0` is small; these
facts are not.

**Is it worth it?** It would show that the `noL4` family is vacuous for node
size 8; it changes nothing in the route below, which does not use `R3Calls`.
030's rules ask for a counterexample in Lean when a statement is found false.
Question 3; default: not built now.


# 4. Why R3 holds at the runs

1. A transaction's keys strictly increase (`Tx.sorted`, which `Within`
   requires; 024-16), so at the delete of k no earlier operation of the
   transaction had k.
2. A delete reaches `afterDelete` only if k's leaf has a live klong of k's last
   segment (else it is a noop). That klong names k's value, a node from before
   the transaction (below B): the writer keeps every klong at its key's place
   (TP10), and no earlier operation put k. This is **ValOld**.
3. A fresh node names only fresh nodes (MFL (a), section 5), and a node below B
   is not fresh. So k's leaf is not fresh. Each node on k's path names the next
   one by a live klong, so none is fresh (**PathOld**); in particular no
   segment root on k's path.
4. During the delete, a segment root on k's path is replaced only by a split of
   it: a time split's copy (`setMadeFor y (some x)`), a space split's new root
   (`some x`), or in place for a node that the transaction made (`replacedBy x`,
   the node's own entry). Each is old or has an entry if the root was. A merge
   never merges the root (`mergeUp` stops when the found node is the space root
   or its parent is a segment leaf); it changes the root only as the merged
   nodes' parent, in place or by the root's split (as above).
5. So at root collapse's first round the root found is old or has an entry
   (**SegOld**), and `R3At` holds: its premise "made, no entry" is false.

l4b's argument at 01:56 and 02:01 is the same; this is it with the steps named.


# 5. MFI exactly

## 5.1 The forms

The definitions below are type-checked with `lake env lean` against `main`
1d7df8a8's build (the night's land clone), at 03:01 and 03:09; the file, with
`delCaseLive_of_S` proved, is
`/Users/f/fl/bench/2026-11-16/night/r3plan/MFIForms.lean` (93 lines, imports
`SIS.Tree.LiveAssembly` and `SIS.Tree.MadeForOld`). No lemma about MFI is
proved.

    /-- x is a node of the transaction (an id at or above B) with no made-for entry. -/
    def NoMF (B : NodeId) (w : W) (x : NodeId) : Prop :=
      B ≤ x ∧ w.madeFor.lookup x = none

    /-- MFL: along every key klong of every node of the overlay, a node with no made-for
    entry names only such nodes, and an inner node that names one is one. -/
    def MFLinks (B : NodeId) (w : W) : Prop :=
      ∀ x n, w.nodes.lookup x = some n → ∀ c y, Klong.key c y ∈ n.ks →
        (NoMF B w x → NoMF B w y) ∧ (n.leaf = false → NoMF B w y → NoMF B w x)

    /-- The made-for entries are of nodes of the transaction. -/
    def MFKeys (B : NodeId) (w : W) : Prop := ∀ q ∈ w.madeFor, B ≤ q.1 ∧ q.1 < w.next

    /-- MFI's stratum part. -/
    def MFI (B : NodeId) (w : W) : Prop := MFB B w ∧ MFKeys B w ∧ MFLinks B w

    /-- Inside an operation: consecutive nodes of the key access path are linked as
    MFL's klongs are. -/
    def MFPath (B : NodeId) (c : Ctx) (base : View BVal) (w : W) : Prop :=
      ∀ d a q a' x, w.path[d]? = some (a, q) → w.path[d + 1]? = some (a', x) →
        (NoMF B w q → NoMF B w x) ∧
        ((∃ qn, wNode c.p base w q = some qn ∧ qn.leaf = false) → NoMF B w x → NoMF B w q)

    /-- ValOld at a delete's start: the key's live klong names a node from before the
    transaction. -/
    def ValOldAt (B : NodeId) (c : Ctx) (base : View BVal) (w : W) (key : Key) : Prop :=
      ∀ pre cv L n y, key = pre ++ [cv] → KeyLeaf c base w pre cv L n →
        (cv, y) ∈ n.liveAt c.i → y < B

    /-- ValOld at the deletes of the runs of R: the narrowed premise (step M2). -/
    def DelValOldRuns (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
      ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
        lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
        topOf p (ctxOf p ts).view z = .ok top →
        ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
        ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
        ValOldAt tx.base (ctxOf p ts) (viewOf (treeRun p ts)) w key

    /-- PathOld at a delete's start: no node on the key's descent is fresh. -/
    def PathOldAt (B : NodeId) (c : Ctx) (base : View BVal) (w : W) (key : Key) : Prop :=
      ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key w.top.rootKey, ¬ NoMF B w q.1

    /-- SegOld: every root that root collapse's descent finds for segment g is not fresh. -/
    def SegOldW (B : NodeId) (key : Key) (g : Nat) (c : Ctx) (v : W) : Prop :=
      ∀ x v1, descendToSegmentRoot key g c v = .ok (x, v1) → ¬ NoMF B v1 x

and the S form of the delete cases, `DelCaseLiveS`: `DelCaseLive` whose
continuation also gets, at the call,
`(PathOldAt tx.base c base w key → SegOldW tx.base key g c v) ∨ LiveEdges ...`
(w the delete's start). The old form is its instance, with no premise
(`delCaseLive_of_S`, proved in the scratch file).

Notes on the choices:

- `NoMF` is by id (B ≤ x), not by `firstTime`, so that MFL is a statement on
  links alone. `R3At` speaks of `firstTime`; the bridge is that a node the
  transaction did not make has its first time before it (`lt_of_good`,
  `OldStartN`).
- MFL is over the cache (`w.nodes`), as `CacheGood` and `KdInv`'s `cache` are.
  A node of the base view is below B: not fresh, and it names only nodes below B
  (`ViewGood`), so MFL holds along its klongs too.
- MFL is over all key klongs, dead ones too. A fresh node holds only klongs of
  the transaction; an old node's klongs before the transaction name old nodes.
- `MFPath` is not part of the stratum's invariant: `putKv` starts with
  `pathClear`. It is a local invariant of the walk inside an operation.
- ValOld is the premise rather than PathOld because it is the natural statement
  ("a key that the transaction has not touched keeps its value node") and
  the one M6 can prove; PathOld follows from it and MFL (step M2).

## 5.2 Why each part holds at the runs

- MFB, MFKeys: `setMadeFor` is called only with a node just made (`newKey`), and
  with `some x` for an old x or with a recorded entry (MadeForOld.lean's
  header).
- MFL (a): a fresh node is a new segment leaf, or made from a fresh node by a
  split or a merge; its klongs are the transaction's puts (values, fresh),
  long klongs to new segment leaves (fresh), and klongs copied from fresh
  nodes. (b): an inner node's children are in its own segment tree, and a
  segment tree is all fresh or all not (a fresh tree starts at a new segment
  leaf; an old tree's new nodes come from splits of its nodes, `some x` or the
  node's own entry).
- ValOld: section 4, steps 1 and 2.

## 5.3 Which writer steps must keep MFL

Every writer function, at its end (MFL may fail between primitives: `merge`
makes m1 with its klongs before it sets its entry). By my reading of
Exec.lean, the facts each needs are local:

- Reads (`getNode`, the descents, `ghOf`, `climb`, `sibling`): cache a base node,
  which is not fresh and names only old nodes (`ViewGood`). `pathAdd` after a
  search in the path's last node keeps `MFPath`.
- `setValue`: a new value is fresh by `NoMF`'s definition; a leaf's new klong
  to it needs nothing ((a) only asks fresh nodes' targets to be fresh; (b) is
  for inner nodes).
- `setNode`: the new segment leaf is fresh and empty; the segment leaf above
  gets a long klong to it; then maybe `appendKlongs`.
- `handleFullWith x` (all splits): its x is the path's node at `depth` and its
  parent the one above (true at every caller: `setValue`, `setNode`, the
  cascade, `replaceRoot`, `appendDeleteKlong`, `emptyKeyNext`,
  `mergeParent`). New nodes get x's status (`some x` for an old x; x's own
  entry for a made x). Their klongs come from `last` and `ins`; both need a
  precondition: `last`'s targets have the status x's targets have (true for
  `lastVersion`, `lastVersionGivenDel`, LE-b's last version, and the merge's
  last version, whose new targets m1 and m2 have p's status), and `ins`'s targets
  are compatible with x (`MFPath` between x and the split child below). The
  parent gets klongs to the new nodes: compatible by `MFPath`. `toPrev` of an
  old x restores klongs that name old nodes (`CacheGood`'s `Good.old`).
- `merge x d`: p, x and the siblings are linked by p's own klongs (the code
  checks `pn.ptr? ix = some x`; `sibling` reads `pn.ptr?`), so by MFL on p (p
  inner: `mergeUp` checks it) they all have p's status. m1 gets l's status, m2
  r's; their klongs are l's and r's targets. `mergeParent` adds klongs to m1, m2
  (p's status). `retarget p o m1`: o and m1 have p's status. `unlink o`:
  `toPrev`.
- `takeBack x q`: x has an entry (`replacedBy x` is checked), q names x
  (`linkIndex` is checked), so q is not fresh; q's klongs then name the old node
  (below B).
- `takeBackRoot x`: x has an entry (collapse's branch: made and an entry), the
  child is x's klong target, so not fresh by (b); the segment leaf names x
  (checked), so it is not fresh.
- `replaceRoot x`: x is old (collapse's branch: not made), the child is not
  fresh by (b), the segment leaf above is not fresh by `MFPath`; then
  `appendKlongs`.
- `emptyKeyNext`, `appendDeleteKlong`, `unlink`: no new targets, or a split by
  `handleFull` with a last version.
- `newSuperRoot`: the top node only, not in the cache.

If one of these needs a fact of the tree after all, the walk carries the
stratum's facts beside it; stop rule in section 9.


# 6. A separate invariant, or a statement change?

**MFL is a separate stratum-wide invariant, like MFB.** `mfi_ops` (every
operation keeps MFI from any state with `CacheGood`, `ViewGood` and node size at
least 4, as `gmf_ops` keeps MFB) and `stateOK_mfi` (MFI at every state between
operations of a transaction after a run of R, as `stateOK_madeFor`,
LatestTopMadeFor.lean). No premise; an addition. `liveDelSL_of_pieces` already
takes MFB at the delete's start this way.

**It cannot simply be added to the call's facts.**

- The call's facts are made by the delete's cases, in continuation form
  (`DelCaseLive`: for every Q, if `afterDelete` from any state with the call's
  facts ends in Q, then the delete ends in Q). A separately proved invariant
  does not join that form: two continuation statements about one run do not
  combine (l4b, 02:01). I checked the trick of choosing Q to record the call's
  state: each statement gives a state at the call, but not the same one.
- So MFI at the call means threading it through every case's walk: the upward
  walks (LiveUpWalk.lean, LiveUpCascWalk.lean), the full leaf's cases, and
  l4e's stop-node cases, then through the merges' loop, whose rounds would need
  MFL to place the siblings. By my count 3,000 to 6,000 lines of edits in about
  twenty lemmas. Not recommended.

**The route instead** uses MFI only where it is given, at the delete's start,
and carries SegOld:

- At the start: PathOld from ValOld and MFL (step M2).
- At the call: each hole case shows SegOld from its own descent facts. The
  cases already prove which node the merges' descent finds at the call (R1:
  `holeAtW_leaf`, `holeAtW_copy`, `holeAtW_copyG`, `holeAtW_stop`,
  `holeAtW_stopCopy`), and that descent starts with the segment search; it ends
  at the start's root, or at the copy of that root when the changed node is the
  root (`KNode.add_key_searchEq`). A case with no hole gives the live counts
  instead (no merge, no collapse).
- Through the loop: each round that moves the hole up keeps SegOld, from the
  same facts it proves for R1 (`descendToHeight_up`: the path above reads alike,
  so the segment search does too; `descendToHeight_redirect`,
  `_redirectSeg`, `_newRoot`: the new root is the parent's copy, entry
  `some p`). A round that leaves no hole gives the live counts, and then
  `R3At` holds at collapse's first round by the counts (an inner root has two
  live klongs; l4a, 23:46).
- At collapse: SegOld gives `R3At` (`n.firstTime = some c.i` gives B ≤ x).

**Statement change: no.** New definitions (section 5.1, and the S forms below)
and new theorems. The hole cases and the hole-moving rounds are generalized, the
old lemmas their instances (their statements unchanged; the S forms give their
continuations more). Frans's word is needed only to remove `R3Calls` and the
`noL4` family at the close step.


# 7. The route

Each step: a prover, Opus 5.5 at xhigh, under the night's common brief
(`/Users/f/fl/bench/2026-11-16/night/common.md`, rules 1 to 8, or the day's
successor), in its clone (from `main`, branch `proofs-NAME`, built). New lemmas
in new files first (025-05, section 6); default file names below. Sizes are
lines; hours are prover-hours at tonight's speeds (1,000 to 4,000 lines an hour
on planned routes; mechanical walks at the upper end, edits of others' proofs at
the lower).

## Step M0. MFI and SegOld on runs (scratch)

- **What:** a copy of 030-01's step-0 checker
  (`items/030-proofs/01-live-inside-check.lean.txt`, 447 lines; it copies the
  writer's delete from Exec.lean) that also checks:
  - T1, at every state between operations and at every call of `afterDelete`:
    MFB, MFKeys and MFL over the cache;
  - T2, at every delete's start: ValOld and PathOld;
  - T3, at every call of `afterDelete` whose found node at (g, 0) is under the
    fill, and at every round of the merges' loop that leaves a hole: SegOld;
    else the live counts;
  - T4, at root collapse's first round: `R3At`, and how often its premise
    "made, no entry, inner" is met at all.
- **Families:** step 0's 15, `cFamily` and `cFamily2`, and one new: puts under
  new prefixes whose segment trees split in place (fresh inner roots) beside
  deletes under old prefixes whose merges climb to the segment root, and
  deletes of keys under the new prefixes (noops, by T2's argument).
- **Size:** 200 to 400 lines of scratch; under 1 hour; a run of about 3 minutes.
- **Output:** counts, 0 failures, or the smallest failing run. Kept as
  `r3-check.lean.txt` for the coordinator to copy into the item.
- **Gate:** none (no repo change).

## Step M1. MFL as a stratum-wide invariant

- **What:** `MadeForLinks.lean` (the definitions of section 5.1 but the S
  forms), and the walk: `mfi_X` for every writer function X (section 5.3), on
  the pattern of MadeForOld.lean (`KeepsGMF`, its macros) with the node
  contents as the kinds' walk has them (WriterKindsSplit.lean,
  WriterKindsMerge.lean, WriterKindsDelete.lean: their membership lemmas for
  `halves`, `replaceOrAdd`, `mergeKlongs`, `newKlongs`); then `mfi_putKv`,
  `mfi_ops` and `stateOK_mfi`. Also `madeFor_frame`: a writer function adds
  entries only for nodes it makes (ids at or above the next id at its start), so
  a node that exists before it keeps its status; M3 and M4 need it.
- **Size:** 1,500 to 3,000 lines (MadeForOld.lean is 937 lines with no node
  contents; the kinds' walk is 3,404 with an oracle). 1 to 2 hours; two provers
  can split it as the kinds' files are split (puts and splits; deletes, merges
  and collapse).
- **Test:** M0's T1.
- **Gate:** the night's gate (additions only).

## Step M2. ValOld, the premise, and PathOld

- **What:** `R3Start.lean`: `DelValOldRuns` (the narrowed premise), and
  `pathOld_of_valOld`: at a delete's start, ValOld and MFL give PathOld (the
  leaf is not fresh because it names an old node; each node of `fromVisits`
  names the next by a klong, so by (a) none above a non-fresh node is fresh;
  base nodes are below B).
- **Size:** 200 to 500 lines; under 1 hour. Needs M1.
- **Test:** M0's T2.
- **Gate:** the night's gate.
- **Rule 1 of the common brief:** this is a reduction (a narrowed premise, as
  030-01's stop rule for R3 allowed), not a discharge; the coordinator says yes
  to it in the brief, as for step 1 of 030-01.

## Step M3. SegOld at the call: the delete's cases in S form

- **What:** `R3Call.lean`: `DelCaseLiveS` (section 5.1) and the S form of each
  case, the old case lemma its instance by `delCaseLive_of_S`:
  - the hole cases, SegOld from the case's descent facts: the leaf with room
    (`liveDel_room`), the made leaf split in time in place (`liveDel_fullMadeG`),
    the copy below a parent with room (`liveDel_fullTimeRoomG`) and below a made
    parent (`liveDel_fullTimeMadeParent`), the upward delete with room
    (`liveDel_upRoomH`), and l4e's stop-node hole cases (the made stop node in
    time, the stop node's copy below a parent with room or a made parent; these
    are in post-condition form, last bullet);
  - the cases with no hole, the live counts at the call, which each already
    proves before it calls `afterDelete`: the space splits, the copy filled
    through the cascade (`liveDel_fullTimeChainF`), the space root's splits,
    l4e's no-hole stop-node cases;
  - a lemma `segOldW_of_dsr`: the monadic segment search of `SegOldW` from the
    pure one (`dsrFold`, LiveHoleDescent.lean's bridge for `descendToHeight`)
    and the found root's status at the start (`madeFor_frame`).
  - The post-condition pieces (l4e's `UpCascCallOK` and its rests) get a
    separate SegOld lemma joined by `writerWP_and`, since there a statement about
    the end does combine.
- **Size:** 600 to 1,600 lines (50 to 150 a hole case, 10 to 40 a no-hole case);
  1 to 2 hours. Needs only the definitions (M1's first commit, or a small
  definitions file first).
- **Test:** M0's T3 at the calls.
- **Gate:** the night's gate; per group of cases.

## Step M4. SegOld through the merges' loop, and the loop without hR3

- **What:** `R3Loop.lean`:
  - the hole-moving rounds keep SegOld: the merge into one node whose parent has
    room (`liveHoleW_merge_G` and its tail), the parent's time split below q with
    room (`writerWP_mergeTail_liveFullTimeRoundG`), the made parent in place
    (`writerWP_mergeTail_liveMadeRound`), the space root's time split
    (LiveMergeRoot.lean); each round lemma generalized to also conclude SegOld,
    or one separate lemma `SegRoundOK` for the round's program joined by
    `writerWP_and`. The prover takes the smaller by rule and writes why;
  - `MergeLiveOKS`: `MergeLiveOK` with SegOld kept, or the live counts; its
    proved cases from the rounds above; its open rest
    (`MergeTailFullRest9OK`'s cases) in the same form;
  - the loop `writerWP_afterDelete_liveS`: `writerWP_afterDelete_liveTR9` with
    `(SegOldW ... ∨ LiveEdges ...)` at the call for `hR3`, and `R3At` at
    collapse's first round from SegOld (`r3At_of_segOld`: `firstTime = some
    c.i` gives B ≤ x by `OldStartN`).
- **Size:** 600 to 1,500 lines; 1 to 2 hours. Needs only the definitions.
- **Test:** M0's T3 at the rounds, T4.
- **Gate:** the night's gate.

## Step M5. The assembly

- **What:** `R3Assembly.lean`: `afterDelete_live_runsS` (from the call's facts
  and SegOld or the live counts, `afterDelete` ends with the live counts),
  `liveDelSL_of_piecesS` (the cases in S form, PathOld at the start from
  `stateOK_mfi` and `DelValOldRuns`), and the new top theorem, name by rule
  (default `invGetScanOK_merges_noR3`): TP7, TP10 and TP11 for Java's
  parameters from `hp`, `hth`, `DelValOldRuns`, and l4's open R4 pieces in S
  form (section 10). No `R3Calls`.
- **Size:** 300 to 600 lines; under 1 hour.
- **Test:** M0 whole.
- **Gate:** the night's gate; beyond it, `#print axioms` (the standard three)
  and the statement against `invGetScanOK_merges_noL4d`'s: the same conclusion,
  the premises as listed.

## Step M6. ValOld's proof (later, its own plan)

- **What:** `DelValOldRuns` proved: TP10 at the level of node ids for keys the
  transaction has not touched. The get cases (`OpGetCaseOK`, GetAssembly.lean)
  prove `runGet` after an operation equals `runGet` before for other keys, at
  the level of hashes (`wValue`); many of their lemmas take the value function as
  a parameter (`getFromR_split`, `getFromR_collapse`, `getFromR_graft` and more),
  so an id version may be an instance. It must run inside the joint induction
  (it needs `PutInv` and the ranges at every earlier state of the transaction),
  so it also needs a consumer change like 030-01's step 1.
- **Size:** 3,000 to 7,000 lines; 3 to 7 hours; high uncertainty. First a
  1-hour reading spike (an agent at xhigh): are the op cases generic in the
  value function, and what does the induction pass; then the plan.
- **Other way, if the spike says no:** an existential labelling of nodes by
  their key prefix, kept by every writer function like the kinds, with values
  labelled by their keys; it makes ValOld local, but needs the base's labels
  from the run (as `KindsAllOK` is), not small either.

## Step C. The counterexample to R3Calls (optional)

- Section 3's state in Lean: `not_r3Calls` for node size 8. 800 to 2,000 lines,
  2 to 4 hours. Only on Frans's word (question 3).


# 8. The order and what runs in parallel

- **First, one prover:** M0 (under 1 hour), and in the same time a definitions
  file (section 5.1's forms, the S forms) landed alone, so that M3 and M4 can
  start from it.
- **Then three provers:** A takes M1 then M2; B takes M3; C takes M4. They
  share only the definitions file. M5 by whoever ends first, after all three.
- **Beside the R4 work** (section 10): if R4's provers work at the same time,
  they prove their pieces in the S form once the definitions file is on `main`
  (the extra is SegOld at their call or round, or the live counts: small).
  Pieces proved in the old form before that get an S lemma later.
- **One night:** 2 to 6 prover-hours in all, about 2 to 3 hours of clock with
  three provers, if no stop rule fires.


# 9. Tests, the gate, the stop rules

**Tests.** Each step's lemmas are theorems for every state with their
hypotheses; M0's checks test that the hypotheses hold at the runs (T1 to T4).
If a step changes a form, rerun M0 at that point first.

**The gate.** Each proved step is committed on the prover's branch in Frans
Lundberg's name ("030-03: ..." in plain words, no AI names), then

    sh /Users/f/fl/bench/2026-11-16/night/gate-1116.sh <clone> <dir>/gate-N

or the day's successor that the coordinator re-bases on `main`. It builds,
refuses `sorry`, `admit`, axioms of ours, `native_decide`, `implemented_by` and
`extern`, and checks the trusted closure and the old tops' statements. New tops
are checked beyond it (`#print axioms`, the statement against the one they
follow). On GATE PASS: "GATED NAME <commit> gate-N: <theorem> with premises
<list>" to `main`; the coordinator lands.

**Stop rules.**

- The night's: the STOP file, checked before each build and every 20 minutes;
  no new step after 04:30, stop at 05:30 (common brief, rule 7); the week's
  ceiling as the coordinator sets it.
- **M0:** a failure of T1 or T3 at a run means the form is wrong: no proof of
  it. Re-form (for example MFL over reached nodes only) and recheck; after two
  forms that fail, stop and report. A failure of T2 (ValOld) or T4 (`R3At`) at a
  run is a counterexample to `l4` or to the model's key order: build it in Lean,
  stop, report to Frans.
- **M1:** if a writer function needs a fact of the tree to keep MFL (beyond
  `MFPath`, `CacheGood`, `ViewGood` and MFB), write which, and carry the
  stratum's facts beside it for that function only. Past 3,500 lines, stop
  after the current file and report.
- **M3:** if a hole case's SegOld needs more than its own descent facts (a new
  R1), make that case's SegOld part of an open premise in S form, tested by T3,
  and go on.
- **M4:** if generalizing a round passes about 200 lines, or 1,500 in all, stop:
  "the hole-moving rounds keep SegOld" as a narrowed premise at the runs,
  tested by T3, a gated reduction; report.
- **Size:** past 7,500 lines in M0 to M5, stop after the current step and report.
- **MT:** if Frans decides MT, stop at the next gated step (030-01, section 7).
  Under MT a user transaction makes no merge and no root collapse, and a fix
  step starts with no made nodes, so R3 does not arise (030-01, section 8).


# 10. What else is open in l4

Besides R3, one core is left, in three places: R4, a hole (a copy under the
fill) below a parent that splits, or below a cascade. As of 03:00 on `main`:

- **The leaf** (030-01's step 5): `DelFullTimeHole2M`: the leaf's time split
  whose copy is a hole, below a parent that is the space root not made by the
  transaction, or that splits in space (l4b, 02:18; `invGetScanOK_merges_noL4d`'s
  `hR4`).
- **The merge's full parent** (step 3): `MergeTailFullRest9OK` (l4f, 02:45):
  on step 0's runs 69 of the 1,134 full-parent merges are left (1,065 proved):
  one-node merges whose parent's last version is the hole below the cascade or
  below q split in space; a space split below a full inner parent; a made parent
  split in space in place (0 on the runs).
- **The full stop node** (step 6): `UpCascSplitRest7OK` (l4e, 02:59): the stop
  node's copy under the fill below an inner parent without room or compacting,
  not made, or split in space, or the space root.

**The size.** One shared lemma, "a hole's parent splits (in time or in space,
with or without a cascade) and the hole stays the node the descent finds",
would serve all three. l4a measured the general route at 00:04: `chainGLX` with
a hole (about 2,400 lines changed) and a live full split (about 860). My
estimate for the three places with one shared lemma: 2,000 to 5,000 lines, 2 to 5
prover-hours, two provers. It is independent of R3 but for the S form
(section 8).

**So the whole of what is left of l4:** R4 (2,000 to 5,000 lines), R3 by this
plan (3,200 to 7,200), and ValOld's proof (3,000 to 7,000, uncertain); then the
close step. With R4 and R3 done, the top theorem has `hp`, `hth` and
`DelValOldRuns`, a premise at the runs, true and tested.


# 11. Questions for Frans

None blocks a start; each has a default that goes ahead.

1. **The route.** MFI at the delete's start, SegOld carried to the call and
   through the loop, no statement change. Default: yes, M0 to M5 next night.
2. **The residual premise.** ValOld at the runs (`DelValOldRuns`, "a key that the
   transaction has not touched keeps its value node") until M6 proves it.
   Default: yes. Smaller now: PathOld itself as the premise (M1 and M2 move to
   M6; saves 1 to 2 prover-hours now).
3. **The counterexample to `R3Calls`** (step C, 2 to 4 prover-hours). 030's rules
   ask for one when a statement is found false; no new theorem carries
   `R3Calls`. Default: not built; the `noL4` family is marked "believed
   vacuous" (024-12, section 1, already says so) and goes at the close step.
4. **M6, ValOld's proof.** Default: after M0 to M5 land, a 1-hour reading spike,
   then its plan; the night after.
5. **The S form for R4's pieces.** Default: R4's provers prove their pieces in
   the S form once the definitions file is on `main`.
6. **MT.** If decided, R3 does not arise; this plan stops at its next gated step.
   Default: go on until the decision (030's map, D2).


# 12. What I could not check

- No `lake build`, no run. M0 is not written. The definitions of section 5.1 and
  `DelCaseLiveS` type-check against `main` 1d7df8a8's build; no lemma about MFI is
  proved.
- That every writer function keeps MFL with only local facts is my reading of
  Exec.lean (section 5.3), not a proof.
- That each hole case's proof exposes the segment search at the call: read for
  `liveDel_room` (its `hdsr`), and from 030-01's log for the others.
- That the hole-moving merge rounds expose "the path above reads alike" in a
  form that gives SegOld: read from 030-01's log and the lemma names, not their
  proofs.
- The counterexample of section 3: by reading of `mergeUp`, `merge`,
  `mergeParent` and `collapseRoot`; I did not check each conjunct of
  `DelInvJT` and `HtInv` against it.
- Whether the get cases are generic in the value function (M6).
- What the provers landed after 03:00.
- The line counts are estimates by analogy (MadeForOld.lean, the kinds' walk,
  tonight's case and round lemmas), not measured.


# Log

2026-11-17, 02:36 to 03:15. The plan written by an agent of coord-1116. Read:
AGENTS.md, items/readme.md, 030's readme, 030-01 (sections 2.3, 5, 7 and its
log), the final reports of l4a to l4d, the common brief, the gate's header;
in the Lean: Exec.lean's writer (splits, merges, the delete, root collapse,
`setMadeFor`, `replacedBy`), `R3At` and its users (LiveCollapse.lean,
LiveCollapseStep.lean, the merge tails' `writerWP_afterDelete_liveTR*`),
LiveAssembly.lean (`R3Calls`, `liveDelSL_of_pieces`, `noL4`),
MadeForOld.lean and LatestTopMadeFor.lean (MFB, `stateOK_madeFor`), `KdInv`,
`DelInvJT`, `SJ0`, `TakeJ2`, `LeafVals`, LiveDelLeaf.lean (`liveDel_room`),
LiveDelSpaceChain.lean (a no-hole case calls `afterDelete` with `LiveEdges` in
hand), LiveUpCascCall.lean (`UpCascCallOK` is in post-condition form), `Within`
(it requires `Tx.sorted`), the get cases' assembly (GetAssembly.lean,
GetCaseBridge.lean). Made, outside the repo: the forms of
section 5.1 in `/Users/f/fl/bench/2026-11-16/night/r3plan/MFIForms.lean`,
type-checked with `lake env lean` in the night's land clone (`main` 1d7df8a8) at
03:01 and 03:09, no `sorry`. No Lean file of the repo changed; no step of
section 7 started.
