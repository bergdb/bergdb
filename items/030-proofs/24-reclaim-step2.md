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


# State

2026-11-19, 13:55. **The read half is proved; RC gives `CutOK`.** The
independent search's read invariant (its I1 and I2) and its proof, from
RunOK and Java's Rule A alone, are taken over into lean/contract
(Contract/Proof/OldReads*.lean, 903 lines) and gated: `old_reads_good` (in
every reached state, a version that a read at t may follow and that is
written at or before the startup pos s is good at min t s, and its node is
reachable then), `rc_part2` (`CutOK`'s part 2 under RC; it uses only the
first wait), `tschemeReads_holds` (030-23's open half, for every spec),
`cutOK_of_rc` (with `rc_dref`, for runs with A6'), and the theorems after
cuts with RC alone: `full_cut_of_rc`, `cut_keeps_top_of_rc`,
`cut_java_reads_of_rc`, and for every history PE writes
`PE.pe_cut_java_reads`. Commit b529e9e6, `gate.sh 1f25b044`: GATE OK (171
theorems, 97 pinned). So clause (ii)'s case 2 and Rule A's chains of
`TSchemeGis` are no longer needed: `TSchemeGis` is left open, unused.

Next: (1) a Lean counterexample to `TScheme` as stated in 030-23 (every
run with RunOK, without A6'), from the independent search's six-transaction
example; (2) RC3 for the key tree from the writer's contract (030-22,
section 4.1); (3) RC2 from reclaim's iteration (030-22, section 4.2), at
least as a statement.


# Log

2026-11-19, 13:46. Started.

2026-11-19, 13:52. The independent search's Lean (a scratch study against
a0a76461) built unchanged on `main` 1f25b044 but for one file
(Retired.lean, unfinished, dropped); its proofs moved to namespace
`Contract.OldReads`; the new statements in Contract/ReclaimReads.lean.
GATE OK at b529e9e6.
