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

2026-11-19, 14:00. Started from `main` 1f25b044. Reading the independent
search: it reports a read invariant (I1/I2) proved for every reached state
with RunOK and Java's Rule A, and from it part 2 under RC2, RC3 and the
first wait. Next: port it into lean/contract and gate it.


# Log

2026-11-19, 13:46. Started.
