# 030-24. Reclaim's proof, step 2

Created 2026-11-19 by Frans Lundberg. Status: done.

The next step of reclaim's proof after 030-23: from `TSchemeGis`, or a
shorter route, to the reads after cuts given only RC at each cut, and if
there is room RC2 and RC3 for the key tree and the top theorem (030-22,
section 6, steps 3 to 6). Coord-1118's brief, 2026-11-19, 13:45: clause
(ii)'s case 2 first, then Rule A's chains; the results of the independent
search made beside 030-23 (a scratch study, not kept) may be used, and
are credited where used. Done by an agent of coord-1118 and one
sub-prover, on the branch `030-24-reclaim-step2`.


# Result

For Frans, in plain words. Details in sections 1 to 3.

- **Reclaim chooses only safe cuts: proved, given local conditions.** For
  BergDB's key tree (runs with A6'), a cut that meets reclaim's contract RC
  is safe (`cutOK_of_rc`), so recovery, restarts, eviction and Java's reads
  after cuts need only RC at each cut (`full_cut_of_rc`,
  `cut_keeps_top_of_rc`, `cut_java_reads_of_rc`; for every history PE
  writes, `PE.pe_cut_java_reads`).
- **The open half of 030-23 is closed by another route.** The independent
  search made beside 030-23 found an invariant that 030-23's search did not:
  every version a read can follow, if written before the startup pos, is
  good at the read's time clamped to the startup pos. It proved it from the
  model's take and Rule A alone, in a scratch study; its proof is taken over
  (section 1). With it, part 2 of `CutOK` needs only Java's first wait;
  the second wait is needed for D's references. 030-23's GIS-J and its open
  case 2 are no longer needed.
- **`TScheme` as 030-23 stated it is false** (section 2): it speaks of every
  run with RunOK, and a run that moves a child to another parent while the
  old parent keeps a pointer to it (no A6') breaks D's references. Proved
  in Lean; BergDB's tree meets A6', so nothing for BergDB changes.
- **RC2 and RC3 for the key tree: proved** (section 3). RC3 from the
  writer's contract, given a live key at the iteration's end (its row).
  RC2 from the iteration in the contract's words (`IterationOK`: every
  key whose value predates the cut is written again during the iteration)
  and VAL-NEW (a put makes a new value node; other keys keep theirs).
- **The top theorem: proved** (`PE.pe_reclaim_reads`): for every history
  PE writes, with cuts whose iterations meet `IterationOK`, a key live at
  each iteration's end, and Java's arithmetic of the cut (RC1, RC4), Java's
  get and scan after the run with handles, evictions and restarts from the
  cut streams are right at every time from the first available time on.
  PE meets VAL-NEW (`PE.pe_valNew`): PE's writer reads no value hash, so a
  run whose puts each get their own label pins each value node to its put.
- **What stays tested, not proved:** Java's arithmetic of the cut (RC1, the
  order and the first available time; RC4, the two waits), Java's iteration
  against `IterationOK`, and, as for every theorem of the contract, that
  Java's writer is PE and Java's records are the model's.


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
- **Part 2 from it** (`reads_ge_cut`, `rc_reads`; restated as `rc_part2`
  and, with the first wait alone, `rc_part2_first_wait`): a version a read
  follows that is written after s is after the cut (s ≥ e ≥ c by the first
  wait);
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
current parent 1 to the sibling 2, in place of leaf 4, while 1 keeps a
dead pointer to it (A6' fails), so after T(6) node 1 is in D with its
latest version 1@2 naming 3@0, while 3's latest version is 3@4. The read
half holds there; only D's references fail. BergDB's key tree meets A6'
(the bridge, `bridge_evictRunOK`; PE through `pe_full`), and the theorems
after cuts use the run's own EvictRunOK (`cutOK_of_rc`), so nothing proved
for the tree is affected.
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

All proved (section 4 lists the commits): `rc3_tree`, `rc2_of_tree`,
`rc2_of_iteration`, `cutsMeetRC_of_iter`, `PE.pe_valNew` (with
`valNew_of_unique`: VAL-NEW for any history in the contract's words whose
puts have distinct hashes and whose transactions make value nodes only with
hashes they put; and Contract/Proof/PeSim.lean: PE's run on operations
whose hashes are mapped is the image of its run, so its trees by id do not
depend on the hashes), `reclaim_java_reads` and `PE.pe_reclaim_reads`.

What is not proved, and is tested: RC1 and RC4 at each cut (Java's
arithmetic, `tracecheck` since 030-23), `IterationOK` (REWRITES: argued,
gated by the reclaim tests; its consequence RC2 is checked at every cut),
and, as for every theorem of the contract, that Java's writer is PE
(026-25) and that Java's records are the model's (the trace checkers). A
model of the iteration's steps (each scans the live keys of its range at
its own time and puts again those older than pCut; the ranges cover every
key up to E) would make `IterationOK` a theorem about Java's steps; not
done (section 5).


# 4. Files and gates

- **The branch** `030-24-reclaim-step2`, from `main` 1f25b044, in
  lean/contract only but for this item, 030's readme and 027-13:
  - b529e9e6: the read half (Contract/ReclaimReads.lean, and the
    independent search's proofs in Contract/Proof/OldReads*.lean);
  - c6f08672: `tscheme_false` (Contract/ReclaimSchemeFalse.lean);
  - 115a0290, cabec0cc, f046f30f, merged as a77506e9: RC3, RC2 and the
    cuts with the iteration (Contract/ReclaimTree.lean,
    Contract/Proof/ReclaimTree.lean);
  - c2f4b3fb: the top theorems with VAL-NEW as a premise; 34a3b19d:
    `rc_part2_first_wait`;
  - 47f3e32f, e38945f1, merged as 64eac0d8: `valNew_of_unique`,
    `PE.pe_valNew` (Contract/Proof/PeSim.lean) and `PE.pe_reclaim_reads`.
  The sub-prover's commits were made on its branches `030-24-prover`,
  `030-24-tree` and `030-24-valnew` and taken over unchanged.
- **Lean added:** 3,991 lines in 11 new files: the independent search's
  proofs 903, the statements of the read half 208, the counterexample 495,
  RC2, RC3 and the top theorems 1,660, PE's VAL-NEW (PeSim) 725; Axioms.lean
  lists 182 theorems (162 on `main` before).
- **Gate:** `lean/contract/gate.sh 1f25b044` at 64eac0d8: GATE OK (182
  theorems, the standard axioms only; 84 files of the closure, 98 pinned).
  At the head (9d49fbfe, which changes the headers of the search's files,
  and the items after it): steps 1 to 3 and 5 pass, and step 4 lists only
  items/027-algorithms/13-reclaim.md, which the gate does not allow by
  design; `gate.sh` without a base: GATE OK. Java and
  lean/ outside lean/contract did not change; the checkers' package
  (lean/contractcheck) builds only what the checkers import, none of these
  files.


# 5. What is next

- Reclaim's part of 030's aim is proved, given the tested assumptions
  above. Possible next steps, none needed for the aim: a model of the
  iteration's steps that gives `IterationOK` (Java's steps against it
  stay tested, now per step); a check of `IterationOK` itself in
  `tracecheck` (the trace has the cut c and tEnd but not the iteration's
  first step s; with VAL-NEW, `IterationOK` from s gives it from c + 1
  when c < s, and that the trace has); and the cost side (030-22, section
  8).




# State

2026-11-19, 15:05. **Done.** Reclaim's part of 030's aim is proved for
every history PE writes, given the tested assumptions (Result; section 3):
RC gives `CutOK` (the read half by the independent search's invariant),
RC2 and RC3 for the key tree, PE's VAL-NEW, and the top theorem
`PE.pe_reclaim_reads`. Gated at 64eac0d8 and at the head (section 4).
Possible next steps are in section 5.


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

2026-11-19, 14:53. `PE.pe_valNew` proved by the sub-prover, by
relabelling (47f3e32f, e38945f1; 1,359 lines), and `PE.pe_reclaim_reads`
with it; merged as 64eac0d8, GATE OK, 182 theorems. 027-13 updated (the
proved state of T-SCHEME, REWRITES and LIVEBELOW).
