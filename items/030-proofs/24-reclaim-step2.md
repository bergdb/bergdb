# 030-24. Reclaim's proof, step 2

Created 2026-11-19 by Frans Lundberg. Status: open.

The next step of reclaim's proof after 030-23: from `TSchemeGis`, or a
shorter route, to the reads after cuts given only RC at each cut, and if
there is room RC2 and RC3 for the key tree and the top theorem (030-22,
section 6, steps 3 to 6). Coord-1118's brief, 2026-11-19, 13:45: clause
(ii)'s case 2 first, then Rule A's chains; the results of the independent
search made beside 030-23 (a scratch study, not kept) may be used, and
are credited where used. Done by an agent of coord-1118 and one
sub-prover, on the branch `030-24-reclaim-step2`.


# Result

RESULT


# 1. The read half, by the independent search's invariant

- **The route.** 030-23 left part 2 of `CutOK` (the versions that a read
  follows through a pointer besides the latest ones) as `TSchemeReads`, and
  found GIS-J by running, with two open pieces (clause (ii)'s case 2 and Rule
  A's chains). The independent search made beside 030-23 found another
  invariant and proved it in a scratch study against a0a76461: **the read
  invariant** (its I1 and I2). In the state after k with startup pos s, a
  version that a read at a time t may follow and that is written at or
  before s is good at min t s, and its node is reachable then. It needs
  RunOK and Java's Rule A only: no A6', no cut, no iteration.
- **Why it holds** (its proof, in Contract/Proof/OldReads*.lean): a version
  after s is its node's latest (no take after s can have written its node
  again: `sectionLatest_st`); a version after s that Rule A did not put back
  names, for every pointee, a version that was the pointee's latest and
  clean when it was written, so good at every earlier time at which the
  pointee was reachable (`sectionRefsGood_st`; Rule A tests every pointee,
  live or dead); a later version of a node good at a time is good at it too
  (`Inv.newer`); and the reach bookkeeping (`live_child_back`,
  `index_exists_at_startup`). Then by induction on `ReadsPhys`
  (`oldReadsGood_st`).
- **Part 2 from it** (`reads_ge_cut`, `rc_reads`): a version a read follows
  that is written after s is after the cut (s ≥ e ≥ c by the first wait);
  one written at or before s is good at a time from e on at which its node
  is reachable, so at the cut or later (030-23's Lemma G, which the search
  proved the same way). Only the first wait is used; the second is needed
  for D's references (part 3, `rc_dref`).
- **Taken over** unchanged but for the namespace (`Contract.OldReads`), two
  unused names marked, and one unfinished file left out (Retired.lean):
  six files, 903 lines. The statements in Contract/ReclaimReads.lean.
- **Java's Rule A tests dead pointers too**, as the model's `javaTest`
  does: `DbHelper.hasDirtyChild` walks every pointer of the node, live or
  dead, through the child objects in memory, and a node of D is always in
  memory (D is pinned).
- **GIS-J** (030-23) is not needed any more: `TSchemeGis` stays open,
  unused; its proved pieces stay.


# 2. `TScheme` as stated is false without A6'

`TScheme` (030-23) asks `CutOK` of every run that meets `RunOK`. The
independent search found a run of six transactions of a small structure
(its Adoption example) that meets RunOK, RC with c = 1, e = 3, k = 6 and
both waits, and fails `CutOK`'s part 3: transaction 1 moves leaf 3 from its
current parent 1 to the sibling 2, in place of leaf 4, while 1 keeps a dead
pointer to it (A6' fails), so after T(6) node 1 is in D with its latest version 1@2 naming
3@0, while 3's latest version is 3@4. The read half holds there; only D's
references fail. BergDB's key tree meets A6' (the bridge, `bridge_evictRunOK`;
PE through `pe_full`), and the theorems after cuts use the run's own
EvictRunOK (`cutOK_of_rc`), so nothing proved for the tree is affected.
In Lean: `Contract.AdoptionExample.tscheme_false : ¬ TScheme sp al`
(Contract/ReclaimSchemeFalse.lean, commit c6f08672, 495 lines; an example,
so not pinned). The kernel evaluates the run (`decide +kernel`) in a form
that sorts by structural recursion on a fuel (`runK`, with `run_eq : run =
runK` proved for every spec), since `List.mergeSort` is defined by
well-founded recursion, which the kernel does not unfold; RunOK, RC and
the failure of part 3 are then concrete facts, each through a computed
check with a soundness lemma. So 030-23's `TScheme`, a definition used
only as a premise (`tscheme_of_open`, `hcut_of_rc` and the `_rc` theorems),
is false in general; for BergDB the form that holds is `TSchemeReads`
(proved) with `rc_dref` (A6'), and the theorems after cuts that matter are
the `_of_rc` ones.


# 3. RC2 and RC3 for the key tree

RC is in the model's words. RC1 and RC4 are Java's arithmetic at each cut
and stay tested (030-22, section 4.3; `tracecheck` checks them at every
cut since 030-23). RC2 and RC3 are about the tree, and are stated and
proved in the contract's words in Contract/ReclaimTree.lean:

- **RC3** (`rc3_tree`): if some key is live after the iteration's end e
  (its last step puts its row), every written index node that a read at e
  reaches has a value below it. From the writer's contract alone: the
  invariants at e say that each key node a live klong names has a live
  klong, and a segment leaf's live klong names a value or a non-empty key
  node (030-22, section 4.1).
- **RC2 in the contract's words** (`RC2Tree`): every value node that a live
  key names after e was made by a transaction from c on. `idContents` is
  `contents` with the value nodes by id. `rc2_of_tree` carries it to the
  model's RC2.
- **The iteration** (`IterationOK`, c ≤ s ≤ e): every key live before the
  iteration's first step s whose value node was made before c is written,
  put again or deleted, by a transaction from s to e. Java's iteration does
  this: each step scans the live keys of its range at its own time and puts
  again those whose value is before pCut, and the ranges cover every key up
  to E, the largest key live when the iteration began (027-13, section 1.4;
  REWRITES, 027-13, section 3, argued and tested); a key the user wrote
  first is written.
- **VAL-NEW** (`ValNew`, 030-22, section 2.3): in each transaction, a put
  makes a new value node, which the key names after it, and a key that the
  transaction does not write keeps its value node. The writer's contract
  does not say this (it compares values by hash); PE does it
  (`PE.pe_valNew`).
- **RC2 from the iteration** (`rc2_of_iteration`): with VAL-NEW, a key live
  at e was either last written in [s, e] by a put, which made its value
  node then, at s or later, so at c or later; or not written in [s, e], so
  it was live before s with the same value node, which `IterationOK` says
  was made at c or later.
- **The cuts of a run** (`CutsMeetIter`): at each cut mark, the cut is at
  or after the earlier ones, and some iteration with that cut meets
  `IterationOK`, some key is live at its end, its end is at most the first
  available time, and RC4 holds; with VAL-NEW this gives `CutsMeetRC`
  (`cutsMeetRC_of_iter`).
- **The top theorem for PE** (`PE.pe_reclaim_reads`): for every history PE
  writes, with cuts that meet `CutsMeetIter`, Java's reads after the run
  with handles, evictions and restarts from the cut streams are right at
  every time from the first available time on.

STATE-RC


# State

2026-11-19, 14:35. **Proved:** the read half (b529e9e6, section 1);
`TScheme` false without A6' (c6f08672, section 2); RC3 and RC2 for the key
tree (`rc3_tree`, `rc2_of_tree`, `rc2_of_iteration`, `cutsMeetRC_of_iter`;
merged as a77506e9); the top theorems with VAL-NEW as a premise
(`reclaim_java_reads`, `PE.pe_reclaim_reads_of_valNew`; c2f4b3fb, GATE OK,
178 theorems). **Left:** `PE.pe_valNew`, that PE meets VAL-NEW: PE's proofs
(030-21) speak of contents by value hash, and VAL-NEW is about value node
ids (a rewrite puts the same hash), so it needs a new proof: an id-level
copy of PE's contents induction (1,000 lines or more), or a simulation that
PE's run does not read hashes, so that a run with each put given its own
label pins each id (600 to 900 lines). The sub-prover tries the second
from 14:40; until then VAL-NEW is a named premise (`ValNew`).


# Log

2026-11-19, 13:46. Started.

2026-11-19, 13:52. The independent search's Lean (a scratch study against
a0a76461) built unchanged on `main` 1f25b044 but for one file
(Retired.lean, unfinished, dropped); its proofs moved to namespace
`Contract.OldReads`; the new statements in Contract/ReclaimReads.lean.
GATE OK at b529e9e6.

2026-11-19, 14:05. `tscheme_false` proved by the sub-prover (c6f08672,
GATE OK, 172 theorems). RC2 and RC3 for the tree given to it.

2026-11-19, 14:30. RC3, RC2 from the contract's words and from the
iteration, and `CutsMeetRC` from `CutsMeetIter`, proved by the sub-prover
(115a0290, cabec0cc, f046f30f; 997 lines); `pe_valNew` not: see State.
The top theorems with VAL-NEW as a premise added (c2f4b3fb).
