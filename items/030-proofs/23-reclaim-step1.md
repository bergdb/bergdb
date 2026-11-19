# 030-23. Reclaim's proof, step 1

Created 2026-11-19 by Frans Lundberg. Status: done.

The first step of reclaim's proof (030-22, section 6, steps 1 and 2): T-SCHEME
stated in Lean in the form that replaces the premise `hcut` of the theorems
after cuts, with what is in reach proved; RC4 in the trace checker, run on the
reclaim traces; and a search by running for the invariant on superseded
versions that the open half needs. Frans, 11:20: "Let's do it this
afternoon. Or now even." Done by an agent of coord-1118 ("I" below) and one
sub-prover, from 11:21, on the branch `030-23-reclaim-step1`.


# Result

For Frans, in plain words. The details are in sections 1 to 6.

- **Stated** (lean/contract/Contract/ReclaimScheme.lean): T-SCHEME,
  `TScheme`: a cut that meets reclaim's contract RC (030-22's RC1 to RC4 in
  the model's words, `RC`) is safe (`CutOK`). The theorems after cuts are
  restated with RC in place of `CutOK` (`full_cut_rc`, `cut_keeps_top_rc`,
  `cut_java_reads_rc`, and the `_reads` forms below). Once the open part is
  proved, every read after crashes, restarts, eviction and cuts is right for
  every history PE writes, given only RC at each cut: local conditions that
  the checker tests. No existing statement changed.
- **Proved** (standard axioms only, gated; about 1,700 lines of Lean by one
  sub-prover): under RC, all of `CutOK` but one part: parts 1 and 4, part 3
  for every node of D (`rc_parts`, and `rc_dref` for the references below
  the cut, for runs with A6', which the bridge gives for BergDB's tree), and
  part 2 for the latest versions. **Open: part 2 for the older versions**
  that a read follows through a pointer (030-22's "invariant on superseded
  versions"), as one statement, `TSchemeReads`; with it the reads after
  cuts follow (`full_cut_reads`, `cut_keeps_top_reads`,
  `cut_java_reads_reads`).
- **RC in the checker:** `tracecheck` now checks RC1's order of the cuts,
  RC2 and RC4 (Java's two waits) by name at every cut (RC3 was there): 0
  failures at 1,314 cuts (the night's 50 reclaim traces with Java's PE, 954;
  030-12's 30 with the writer before PE, 360); the level 3 run on the
  branch exported its 35 traces again and checked them with RC, OK. Java
  waits longer than RC4 asks (the startup pos is 9 or more records past v
  at every cut), so the traces never test RC4's edge; the model's runs do.
- **The invariant, found by running: GIS-J.** A version at the cut or later
  that comes at or after a version of its node good for a time from the
  iteration's end on, at which the node is reachable, leads every read to
  such versions of its children; a version that Rule A put back and that is
  still in D leads, by Rule R, to such versions. It held in every state of
  the model with Java's exact waits (16,458 states of example 4's random
  runs, 13,816 of them with RC exactly, and 8,992 of longer runs) and at
  every cut of the 50
  traces (15.8 million version-child pairs). It is in Lean, and that it
  gives part 2 is proved (`reads_of_gis`, `tschemeReads_of_gis`).
  Kept too, with no failure: 030-22's candidates LNL, Rule A's order, the
  old chain, and "versions after v" in 030-22's own words; they are pieces,
  not the invariant. Refuted, with counterexamples (section 4.4): "versions
  after v" for every child (77 cuts: unreachable nodes written after v;
  harmless), the plain "references at c or later", "good at the same
  time", and two looser forms of GIS-J.
- **The route for the open part** is `TSchemeGis`: that RC gives GIS-J's
  three clauses. Proved already: Lemma G (`rc_goodc`: a version good at a
  time from e on, at which its node is reachable, is at the cut or later)
  and clause (i) but for versions that Rule A put back
  (`gis_latest_clean`, `gis_latest_dirty`, and with J up to the startup
  pos, `gis_clause1_le_sp`), and clause (ii) for the children that the good
  version itself has (`gis_clause2_case1`). Open: clause (ii)'s case 2, a
  child that PE gave a node after its last good version, named by a
  version that Rule A put back: never in the model's runs, and on the
  traces at 952 of 954 cuts (0.8 % of the pairs), always a child made after
  the iteration's end, whose first version is the one the read follows
  first, and good, in 86 % of them, at its own record; and Rule A's chains
  (clause (iii), and clause (i) after the startup pos for versions put
  back).
- **Estimate for the rest:** the rest of `TSchemeGis` (case 2 and Rule A's
  chains), one night, 1,000 to 4,000 lines, the risk in case 2; then RC2
  and RC3 for the tree and the top theorem (030-22's steps 4 to 6), about
  two nights more. In all 2,500 to 7,700 lines, one and a half to three
  nights (section 5.4).

# 1. The statement

In lean/contract/Contract/ReclaimScheme.lean (the contract package, where
030's new proofs go since 030-04; it imports the abstract model `sis`, and
`lean/` stays as 030-18 left it but for the checker, section 3):

- **RC**, for a run of transactions ts, a cut c, the end e of the iteration
  that decided it (tEnd, the record of its last step) and a state k
  (030-22, section 2.2), in the model's words:
  - `RC2 sp db e c`: every data node reachable at e has its version at c or
    later, in the state after transaction e;
  - `RC3 sp db e`: every written index node reachable at e has a data node
    below it at e; RC2 and RC3 are the premises `hrw` and `hlb` of `T_cover`
    and `T_latest`;
  - `RC4 sp al ts e k`: some record v has its startup pos at e or later, and
    the startup pos of record k is after v. It is the same as the condition
    on the first such v, which 030-22 states: the first is at or before any.
  - `RC sp al ts c e k`: c ≤ e ≤ fa(k), RC2 and RC3 in the state after e,
    and RC4. RC1's c ≤ s (s the iteration's pStart) is not in it:
    soundness does not use it (030-22, section 2.2); it is for meeting RC2.
- **T-SCHEME**, `TScheme sp al`: with Java's still-dirty test and the
  marking, for every run ts that meets `RunOK`, every c, e and k ≤ |ts|: RC
  gives `CutOK sp c (run sp al (ts.take k)) k`. A definition, not a theorem.
- **Its open half**, `TSchemeOpen sp al`: under the same premises, `CutOK`'s
  part 2 (every version that a read at a time from fa(k) to k may follow,
  `ReadsPhys`, is at c or later) and the second half of part 3 (a reference
  below c of the latest version of a node of D names the latest version of
  its node).
- **The cuts of a run**, `CutsMeetRC sp al cs`, for a run with handles and
  cut marks (the form of `full_cut`'s argument): at each mark of a cut c,
  every earlier mark's cut is at most c (RC1's order of the cuts), and c
  meets RC for some e in the state after that transaction.
- **The theorems after cuts with RC**: `full_cut_rc`, `cut_keeps_top_rc` and
  `cut_java_reads_rc` are `full_cut` (030-07), `cut_keeps_top` and
  `cut_java_reads` (030-17) with `(hts : TScheme h.spec al)` and
  `(hrc : CutsMeetRC h.spec al cs)` in place of `hcut`. With `pe_full`
  (030-21) they hold for every history PE writes. Nothing else changed:
  `CutOK`, `full_cut` and the rest are as they were; statements.pin gains
  ReclaimScheme.lean and the new lines of Axioms.lean.
- **The open half since `rc_dref`**, `TSchemeReads sp al`: for every run that
  meets `RunOK` and `EvictRunOK` (TREE and A6'), under RC, part 2 of
  `CutOK`. `full_cut_reads`, `cut_keeps_top_reads` and
  `cut_java_reads_reads` are the theorems after cuts with it in place of
  `TScheme`; the bridge gives `EvictRunOK` for BergDB's key tree
  (`bridge_evictRunOK`). This is the form to prove: `TScheme` speaks of
  every run that meets `RunOK`, and part 3's second half is not known to
  hold without A6'.


# 2. What is proved

By a sub-prover (an agent of coord-1118 too), in six short tasks, each
from statements and paper proofs I wrote; every commit gated (pin.sh, then
`lean/contract/gate.sh a0a76461`: the standard axioms only; after 07c186ce
step 4 lists the checker's files, section 6). The first, commit 8636bae7,
539 lines (ReclaimScheme.lean 244, Contract/Proof/ReclaimScheme.lean 295):

- `rc_latest`: under RC, every node reachable at a time from fa(k) to k has
  its latest version at c or later. From `T_latest`: RC4 gives
  e ≤ sp(v) ≤ v < sp(k) (`lastSp_take_le`: the model clamps the startup pos
  below the record), and RC1 gives fa(k) ≥ e.
- `rc_parts`: under RC, `CutOK`'s part 1 (c ≤ fa(k)), part 2 for the latest
  versions (`ReadsPhys.latest`), the first half of part 3 for every node of
  D, and part 4 (the top). Part 3 for a node of D that no read reaches too:
  its D index d is after sp(k) > v ≥ e, and it got dirty by the marking
  (reachable at d), the touch (reachable at d − 1) or Rule A (written at d),
  so `rc_latest` or the write gives it (`inD_lv_ge`). Part 4 with a virtual
  root needed a new argument: the root child that top(k) names, the newest
  created up to the startup pos s, is a live child of the root at s
  (`reach_top_virt`, from the model's invariant alone).
- `tscheme_of_open`: `TSchemeOpen sp al → TScheme sp al`.
- `hcut_of_rc`: T-SCHEME and `CutsMeetRC` give `full_cut`'s premise `hcut`:
  by RC1's order of the cuts, the largest cut so far is the mark's own
  (`cutMax_take_of_le`).
- `full_cut_rc`, `cut_keeps_top_rc`, `cut_java_reads_rc` (section 1).

Findings of the proof: `rc_parts` uses the marking (`al.mark`) only for part
3 (T13 would give it without); parts 3 and 4 need only e ≤ s(k) of RC4, and
RC1's e ≤ fa(k) is used for part 1 and for the times of part 2.

A second task of the sub-prover, commit c298d5b7 (cherry-picked from
3e5eae2f), 318 lines, gated the same way:

- `rc_dref`: under RC, for a run with TREE and A6' (`EvictRunOK`, which the
  bridge gives for BergDB's key tree: `bridge_evictRunOK`), `CutOK`'s part
  3, second half: a reference below c of the latest version of a node of D
  names the latest version of its node, and that node is not in D.
- `cutOK_of_reads`: for such a run, RC and part 2 give `CutOK`.

So of `CutOK` only part 2 is open, for the versions that a read follows
through a pointer besides the latest ones. A third task, commit ffe559e9
(cherry-picked from 8af9a535), 99 lines: `TSchemeReads` (section 1),
`hcut_of_reads` (`TSchemeReads` and RC at every cut mark give `hcut`, for a
run with A6'), `full_cut_reads`, `cut_keeps_top_reads` and
`cut_java_reads_reads`. Then 8a14e337, mine: the file's header and two
docstrings say so; statements.pin.

A fourth task, commit 04c91123, 173 lines in a new file,
lean/contract/Contract/ReclaimGis.lean: GIS-J in Lean and that it gives part
2 (section 5.1):

- `AfterGood`, `GisI`, `GisJ` (an inductive predicate: I, or a version put
  back and still in D, at c or later, whose children lead by Rule R to
  versions with J) and `GisClauses` (clauses (i) to (iii) at every time from
  the first available time to k), as in section 4.2;
- `reads_of_gis`: in a reached state, GIS-J's clauses give part 2; by
  induction on `ReadsPhys`, with `follow_ge` (Rule R's version is at or
  after the record that the reference names);
- `TSchemeGis` (RC gives GIS-J's clauses, for runs with A6') and
  `tschemeReads_of_gis`: `TSchemeGis sp al → TSchemeReads sp al`.

So the open part is now `TSchemeGis`: that RC gives GIS-J's three clauses.
The proof needs only "c ≤ w.recNo" of I; the rest of I (`AfterGood`) is
what makes clause (ii) true.

A fifth task, commits fede0c91 and 094765b0, 360 lines (ReclaimGis.lean and
a new Contract/Proof/ReclaimGis.lean): the first pieces of `TSchemeGis`.

- `rc_goodc`, Lemma G of section 5.2: under RC (it uses c ≤ e, RC2 and
  RC3 only), a version good for a time from e to k at which its node is
  reachable is at c or later. By induction on the level (`good_ge_below`):
  a node whose history has no entry between e and that time has the same
  live children at both, and a good version names good versions of them at
  or before its record; one with such an entry has its good version after
  e.
- `gis_latest_clean`: clause (i) for the nodes not in D (`rc_latest` and
  `Inv.clean_good`).
- `gis_latest_dirty`: for every node of D whose latest version was not put
  back at its record, reachable or not, that version has GIS's I: the node
  got dirty at its index d by the marking or the touch, so it was
  reachable and clean at d − 1 and its latest version was good then
  (`dirty_good`), which stays true in later states (`good_mono'`); and
  e ≤ d − 1 by RC4.

So clause (i) is proved but for latest versions that Rule A put back
(`GisJ.putBack`); clauses (ii) and (iii) are open.

A sixth task, commits 8793fe89 and 43be8c12, 207 lines:

- `gis_clause2_case1`: clause (ii) in case 1 (the child is live, at its
  time, in a good version of the node at or before the version): the good
  version names the child at a version good for that time (`good_iff`), the
  child is reachable then, so Lemma G puts it at c or later, and a later
  version of the node names a later or the same version of the child
  (`Inv.ref_mono`). It needs neither A6' nor the marking.
- `gis_clause1_le_sp`: clause (i), with J, at the times up to the startup
  pos s(k): by induction on the level; a version put back at its record d
  has d > s(k) ≥ t, so its children live at t are reachable at t, and Rule
  R from it gives each child's latest version (`putBack_follow`).

Left of `TSchemeGis`: clause (i) at the times after s(k) for a version put
back at d < t whose node got entries after d (a node of D can get entries
without being marked again, so the children the version gives at t need
not be reachable at t); clause (ii), case 2; clause (iii).


# 3. RC in the trace checker

- **The change** (commit 07c186ce; lean/Check/Steps.lean, `rcFailures`, and
  its call in lean/TraceCheck.lean's C-CUT, about 40 lines with four `#guard`
  tests): at every CUT line `CUT c f` in TX i, besides C-CUT's checks of
  `CutOK`:
  - `RC1-order`: c is at or after the largest earlier cut (c ≤ f is
    `CUT-order`, and f = fa(i) is `CUT-fa`, as before);
  - `RC2-rewrites`: every data node reachable at f has its version at c or
    later (f is the iteration's end e: Java sets fa := tEnd, 027-13,
    section 1.6);
  - `RC4-waits`: v, the first record whose startup pos is at f or later,
    is before the startup pos of R(i);
  - RC3 was checked already, as `CUT-live`.
  A failure fails C-CUT and the verdict. A new line after C-CUT's reports
  the CUT lines checked, the least margin sp(i) − v, and the CUT lines with
  a margin of 1. 027-13, sections 3 and 5, now say so. No change in
  lean/contract's checkers (028-24 works there today).
- **The run:** the 50 reclaim traces that `night.sh` wrote on 19 November
  at 09:49 (c458bfea, Java's PE, record format 8): level 3's set
  (`conformance.sh reclaim`, 35 traces) and treeconf's reclaim set (15),
  copied from the night's clone. Every trace TRACECHECK OK; 954 CUT lines
  (784 and 170), 0 failures of C-CUT, RC1, RC2, RC3 or RC4
  ([rc-traces.txt](23-reclaim-step1/rc-traces.txt)). Also on 030-12's 30
  reclaim traces (17 November, record format 7, the writer before PE,
  `live=0` and `live=1`): 360 CUT lines, 0 failures; and on the 35 traces
  that the level 3 run below exported: 784 CUT lines, 0 failures.
- **The margin:** at every cut of every set the startup pos is at least 9
  records past v (16 to 24 in the long runs); no CUT line has a margin of
  1. Java's second wait (pSafe) and its retention (now − R > tEnd) wait
  longer than RC4 asks, so the traces do not test RC4's edge; the model's
  runs do (section 4, the states between the waits).
- **Gate:** `java/stress/level3.sh` on the branch: LEVEL 3 OK; its own 35
  traces, 784 CUT lines with RC, 0 failures (section 6).


# 4. The candidates, by running

## 4.1 Where they run

- **The model:** [ReclaimL.lean.txt](23-reclaim-step1/ReclaimL.lean.txt), a
  scratch program over SIS/ReclaimExample.lean (how to run it is in its
  header), as 030-22's `checkSchemeJ`: example 4's random runs
  (`randomTs4`), each iteration with c ≤ pStart and the rewrites
  (`rewritesB`) and the cover (`coverB`, which RC3 gives by `T_cover`; so
  the states are a superset of RC's), v the first record with sp(v) ≥ e,
  and every state k with sp(k) > v and fa(k) ≥ e (Java's exact waits). With
  the touch (`spec4`) and without (`spec4n`). The startup pos policies:
  030-22's four (std: lags 1, 2, 4 and an erratic one) and four with longer
  lags, for the second wait (lag: 6, 9, erratic up to 9 and up to 13).
  Two kinds of run: with the cover, as 030-22 (`std` and `lag`, 20 seeds
  of 40 transactions each), and with RC exactly (`rc`: also RC3 itself,
  `liveBelowB`; all eight policies, 20 seeds of 40 transactions; and 40
  seeds of 50, stopped after its first policy). Longer runs (50 seeds of
  60, 10 of 100) were started and stopped: the machine was at load 100 to
  145 and they would not have ended in time.
- **The traces:** [TraceCand.lean.txt](23-reclaim-step1/TraceCand.lean.txt),
  a scratch program that rebuilds each state as `tracecheck` does (which
  checks that it is the model's) and checks the candidates at every CUT line
  in TX i, with e = f, v from the records' startup pos, and the times
  T = [e, i]; the 50 traces of section 3, 954 CUT lines.

## 4.2 The candidates

In the state after k, for the iteration (c, e, v); T = [e, k]; "x is
reachable at t" is in the structure after k (its view at t does not change
later); "good for t" is the model's `good` (the version's history is the
node's at t, and each child live at t is named at a version good for t).

- **CUTOK**, the conclusion, `CutOK c`.
- **LNLK** (030-22, a): a node reachable at k and not in D has a latest
  version that names the latest version of each child live at k.
- **POSTV** (030-22, b, first form): a version written after v names every
  child that is live in it at a time of T at c or later. **POSTV-R** (b in
  030-22's own words): only the children reachable at a time from e up to
  the version's record.
- **PBORD** (030-22, c, the put-back chain): a version p of x at r with a
  pointee in D after T(r) was put back ((x, r) ∈ D after T(r)), and x's
  next version, if any, comes after a version of that pointee written after
  r; if p is x's latest, (x, r) is in D after T(k).
- **OLDCHAIN** (030-22, d): a version p of x at r that names y's version r0,
  where y's next version r1 is after r and at most k, and x is y's parent at
  r1 (y live in x at r1, x reachable at r1): x has a version after r or is
  in D after T(k).
- **SAFE**: I(p) := p at c or later and every child live at t named at c or
  later; (ii) below for it.
- **GI, GIW, GIR, GIS**, forms of one inductive invariant over all versions
  (not only those reached). With a predicate I on versions, the clauses are
  (i) the latest version of every node reachable at t, t from fa(k) to k,
  has I; (ii) for a version p with I that Rule A did not put back and keep
  in D ((x, p.rec) ∉ D), the first version of each child y live at t in p at
  or after the record p names has I (and so every later one: I below is
  monotone in the record); (iii) for such a p in D, the version that Rule R
  gives has I. If (i) to (iii) hold for every t, every version that a read
  may follow has I (section 5.1). The forms, each with "p at c or later":
  - GI: some version of p's node at or before p is good for t (the same t);
  - GIW: ... good for some time of T;
  - GIR: as GIW, and the node is reachable at some time of T;
  - **GIS**: some version of p's node at or before p is good for a time of T
    at which the node is reachable. G(x), the least such record, is the
    node's threshold.
  - **GIS-J**: GIS with (i) relaxed for the versions that Rule A put back
    and that are still in D: J(p) holds if I(p), or p is such a version, at
    c or later, and the versions that Rule R gives for its children live at
    t have J.
- **GOODC**: a version good for a time of T at which its node is reachable
  is at c or later (lemma G of section 5.2).
- **GIS-CASE2**, a count, not a candidate: the instances of GIS's (ii) for
  which no good version g of x at or before p (for a time t' of T at which x
  is reachable) has the child live at t'; `gis_clause2_case1` proves the
  others. With them, diagnostics: was the child made after e, did the node
  gain it after its last good time, was the version put back at its record,
  does it name no version of the child, is the first version of the child
  at or after its reference the child's first version, and is that version
  good for its own record, at which the child is reachable.
- **PART3B**: `CutOK`'s part 3, second half (C-CUT's `CUT-Dref` on the
  traces).

## 4.3 Results

In the model ([candidates-model.txt](23-reclaim-step1/candidates-model.txt)):

- **The cover runs** (030-22's iterations; 20 seeds of 40 transactions,
  std and lag): 1,616 iterations, 16,458 states past Java's waits, with
  51,000 reads (a time and a version) of a version that is not its node's
  latest, and 40,000 "dangerous" versions (030-22: from c to v, naming a
  version before c of a child live from e on). Between the two waits
  (startup pos at e or later, at most v) `CutOK` fails in 24 states (5 std,
  19 lag): the second wait is exercised, mostly by the lag policies.
  - no failure: CUTOK, LNLK, PBORD, OLDCHAIN, PART3B, GIS's (ii) and (iii),
    GIS-J's (i) and (iii);
  - failing: POSTV's first form (77 states; POSTV-R was added after these
    runs and checked in the `rc` runs), SAFE (9,782 states), GI's (i) (good
    at the same time: most states), GIW's and GIR's (ii) (327 states), GIS's
    (i) without J (525 states), GOODC (968 states, all on iterations without
    RC3: section 4.4);
  - GIS's (ii) outside case 1: never.
- **The `rc` runs** (RC exactly; all eight policies), 20 seeds of 40
  transactions: the subset of the cover runs' iterations that meet RC3
  itself, 1,504 iterations, 13,816 states past the waits, 22 states between
  the waits with `CutOK` failing; with POSTV-R.
  - no failure: CUTOK, LNLK, PBORD, OLDCHAIN, POSTV-R, PART3B, GOODC, GIS's
    (ii) and (iii), GIS-J's (i) and (iii);
  - failing: POSTV's first form (77 states, the same as above), SAFE,
    GI's (i), GIW's and GIR's (ii) (230 states), GIS's (i) without J (467);
  - GIS's (ii) outside case 1: never.
- **40 seeds of 50 transactions, RC exactly**, stopped after the first
  policy (lag 1) with and without the touch, for time: 464 iterations,
  8,992 states past the waits; no failure of CUTOK, LNLK, POSTV, POSTV-R,
  PBORD, OLDCHAIN, PART3B, GOODC, GIS's (ii) and (iii), GIS-J's (i) and
  (iii); GIS's (ii) outside case 1: never.

On the traces (954 CUT lines;
[candidates-traces.txt](23-reclaim-step1/candidates-traces.txt)):

- **No failure at any CUT line:** LNLK (96,705 instances), PBORD (1.2
  million versions with a pointee in D), OLDCHAIN (3.2 million premises),
  POSTV-R (250,724 versions after v), GOODC (4.2 million good versions of
  reachable nodes), and GIS-J: (i), (ii) over 15.8 million pairs, (iii);
  also GIS without J (on the traces no latest version needs J) and GIR.
- **Failing:** POSTV's first form at 77 of 954 CUT lines (section 4.4),
  GIW's (ii) at every CUT line (garbage nodes), and the diagnostic
  UNREACH(ii) at every CUT line: a version with GIR's I often has a live
  child, by its own history, that is not reachable at t (a stale pointer),
  so the closure must not ask the child to be reachable at t.
- **GIS's (ii) outside case 1:** 132,578 of the 15.8 million pairs (0.8 %),
  at 952 of 954 CUT lines; in every one the child was made after e, the
  node gained it after its last good time, and the version is one that
  Rule A put back at its record; the child's first version is the one at
  or after the reference (in 97 % the version names no version of the
  child), and it is good for its own record, at which the child is
  reachable, in 86 %.

## 4.4 The counterexamples

- **POSTV** (first form), r-big-1, TX 182, the cut c = 104 decided with
  e = 156, v = 157: node 86214's version of R(158), after v, names value
  node 107898 at a record before 104. Neither node is reachable at any time
  from e on: 86214 was unlinked while in D and written when the take reached
  it. No read reaches it, so it is harmless. 030-22's form (POSTV-R, the
  children reachable from e to the version's record) holds at every CUT
  line, so every failure of the first form, on 77 CUT lines, names a child
  that is not reachable then; the first example of each failing trace is
  of an unreachable node.
- **SAFE**, example 4: version (30, 3) of a top node is at c = 3 and names
  its tree root's version of R(3), which names a child before c. The plain
  form is not closed: a version at c or later can name children through
  versions written during the iteration, before their own rewrites.
- **GI** (good for the same t), example 4: a top node made by a split at 9
  and written first at 13, put back by Rule A, has no version good for 9.
  Nodes of D need "good for some time".
- **GIW** (good for some time, any node), r-small-1, TX 193 (c = 92,
  e = 173): version (71226, 92) names child 90070 at R(91). Neither is
  reachable from e on: a garbage node's versions are good for every later
  time, since nothing changes it. Hence GIR and GIS.
- **GIR** (good for some time, the node reachable at some time), example 4
  with the lag policies: version (10050, 12) of a tree root made by a split
  at 6 has GIR's I (a version good for some time of T, and the node
  reachable at some time of T, not the same one), and names mid node 1's
  version of R(7), which has no I. GIR fails in 300 of 5,763
  states of the lag runs (20 seeds of 40 transactions); hence GIS, where the
  good version's time is one at which the node is reachable.
- **GOODC on iterations without RC3**, example 4 with the touch: the empty
  leaf of key 3 keeps its version of R(0), good for every later time and
  reachable, below the cut; the touch, not a value below it, made the cover
  hold. With RC3 itself (the `rc` runs) GOODC has no failure.
- **GIS's (i) without J**, example 4: the latest version (10075, 13) of
  that top node is put back and in D, and Rule R leads to its tree root's
  version of R(13), also put back and in D; such chains end at versions
  with I (GIS-J).


# 5. The route for the open half

## 5.1 GIS-J gives part 2 (proved: `reads_of_gis`)

Fix the state after k and a time t from fa(k) to k. Suppose (i) to (iii) of
GIS-J hold. Every version w with `ReadsPhys t w` has J, by induction on the
derivation:

- `latest`: w is the latest version of a node reachable at t: (i).
- `child` from v (with J) to w, a version of a child y live at t in v:
  - if (v.node, v.rec) ∈ D, `ReadsPhys` allows only Rule R's version
    (`follow`): J(v) gives it J if v has J by its second branch, and (iii)
    if by I;
  - otherwise J(v) is I(v), and w is Rule R's version or any version of y
    at or after the record that v names. Rule R's version is at or after
    it too: it is y's newest version in the startup section, or the one
    named; the named record, if in the section, is at most the newest. So
    w is at or after the first version of y at or after the named record,
    which has I by (ii); I is monotone in the record (its two conditions
    are lower bounds on it), so w has I.

J gives c ≤ w.rec, which is part 2. In Lean: `reads_of_gis`, with
`follow_ge` for Rule R's version (section 2).

## 5.2 Why GIS-J holds (in part proved)

- **Lemma G (GOODC): proved** (`rc_goodc`, section 2). A version good for
  a time t' of T at which its node is reachable is at c or later. Checked
  too: GOODC holds in every state of the `rc` runs and at every cut of the
  traces; it fails in the cover runs only on iterations without RC3 (the
  empty leaf, section 4.4).
- **(i): proved but for one kind of version** (`gis_latest_clean`,
  `gis_latest_dirty`; with J at the times up to the startup pos,
  `gis_clause1_le_sp`). Left: at a time after the startup pos, a latest
  version that Rule A put back at its record and that is still in D (the
  last bullet).
- **(ii), case 1: proved** (`gis_clause2_case1`). p has I: c ≤ p.rec, and
  some g at or before p is good for a time t' of T at which x is reachable.
  If the child y live at t in p is live in g at t', then g names y at a
  version good for t' (g is good), y is reachable at t' (x is, and g's
  history is x's at t'), so G(y) ≤ g's reference; Lemma G puts that
  reference at c or later; and p's reference is at or after g's (a later
  version of x names a later or the same version of each pointee,
  `Inv.ref_mono`). So every version of y at or after p's reference has I.
- **(ii), case 2: open.** No good version of x at or before p, for a time
  at which x is reachable, has y live at its time. Never in the model's
  runs (example 4's splits make new tree roots and top nodes; they never
  give an existing node a new child while another child is dirty). On
  Java's traces at 952 of 954 cuts, 132,578 of 15.8 million pairs, and in
  every instance the same three things
  hold (TraceCand's diagnostics): y was made after e; x gained y after its
  last good time (PE gave it a new child: a split or a join); and p is a
  version that Rule A put back at its record, superseded since. More: the
  version of y that a read follows first from p is always y's first
  version; p names no version of y at all in 128,538 of the 132,578 (97 %);
  and y's first version is good for its own record, at which y is
  reachable, in 114,108 (86 %). So p was
  written while y was in D (unwritten, or dirty), and names no version of y
  or one before y's next write; the versions of y that a read can follow
  from p are all after y was made, so after e and at c or later. What is
  left to prove is that the first of them is at or after a version of y
  good for a time at which y is reachable (that it is, GIS's (ii) checks,
  with no failure): presumably y's first clean write after it was made,
  which the take makes once the startup pos passes its index; a proof
  needs what that write names, which is (ii) again one level down, so the
  proof is an induction on the level.
- **(iii)** and the rest of (i): a version that Rule A put back and that is
  still in D. Up to the startup pos it is proved (`gis_clause1_le_sp`, with
  `putBack_follow`: Rule R from such a version gives each child's latest
  version). After it, the version may give, at a later time, children that
  its node no longer has (the node can get entries without being marked
  again while in D), and the induction on the level does not reach them.
  Open; never failing by running (GIS-J's (i) and (iii)).
- **Kept by the writer and by reclaim?** GIS-J is about one state k against
  one iteration. From k to k + 1: T grows, so G(x) can only decrease and I
  only widen; no old version or its references change; the new versions are
  at k + 1 > c, and the clean ones are good for k + 1; D changes by the take
  and Rule A, so a version leaves the second branch of J when its node is
  written again, and must then have I or no longer be followed (PBORD and
  OLDCHAIN say its parents were put back with it and are written after it).
  This is the induction the proof would make; it rests on the model's take
  and Rule A, not on PE: a change only has to meet `RunOK` (with TREE and
  A6' for case 2, which the bridge gives for the key tree). Reclaim's steps
  are ordinary transactions here (puts and a touch). Not checked as an
  induction: the runs check every state, not the step between states.

## 5.2b The other candidates kept

None of them gives part 2 alone; each is a fact a proof of GIS-J can use.

- **LNLK** gives part 2 for the reads at k only; at earlier times from e on
  the latest version of a node no longer reachable at k may name an older
  version of a child (030-22, section 5.2). It is `Inv.clean_good` at time k
  in another form; the writer keeps it as it keeps `Inv`.
- **PBORD** is Rule A's order (step 7 and `byLevel`): a lemma about one
  step, not an invariant over states. `step_taken_refs`, which `rc_dref`
  uses, is its core.
- **OLDCHAIN** is the marking and the touch's rule (a parent on the path of
  a change gets dirty with it, `markOf`, `StepOK.touchUp`), with A6' for
  the children a node lost; `rc_dref`'s proof uses it through A6'
  invariant `EvLogic.clean`.
- **POSTV-R** follows from `T_latest` in the state before each version's
  record (030-22, section 3.2): a step toward clause (ii) for the versions
  written after v. Its first form is false (section 4.4).

## 5.3 Part 3's second half

Proved (`rc_dref`, section 2), by a shorter route than the paper proof I
gave the sub-prover. Take x in D after T(k), with index d > sp(k), whose
latest version w names y at r0 < c. Find a state J from sp(k) to k in which
y exists, is not in D, and has its latest version at r0:

- x got dirty at d by the marking or the touch: J = d − 1. x is not written
  after J (`written_inD`: a node with a version in (J, k] was in D after T(J)
  with an index at most that version's startup pos), so w is its latest
  version at J; x is reachable at J and not in D; the invariant of A6'
  (`EvLogic.clean`, `evLogic_st`, from the eviction proofs) then says that y
  is not in D at J and w names y's latest version at J.
- x was put back by Rule A at d: J = d. w names y's latest version after
  T(d) (`step_taken_refs`), and y is not in D at d, since every node of D at
  d has its latest version at c or later (`inD_lv_ge` at d; RC4 gives
  e ≤ sp(d)).

Then `written_inD` shows that y has no version after J, so its latest
version at k is r0; and y is not in D at k by part 3's first half. My paper
proof (by cases on y's own index) had a gap: the model's invariant gives a
reference only as some prefix of its record, not "no version of y between
r0 and r_x"; `step_taken_refs` gives it for a node the take writes. It uses
of RC only c ≤ e, RC2, RC3 and RC4, not e ≤ fa(k), and not TREE.

## 5.4 Estimate for the rest

A judgment, by step, refining 030-22's section 6 (its steps 1 and 2 are
this item; part 3's second half, Lemma G, clause (i) up to the startup pos
and clause (ii)'s case 1 of its step 3 are proved here):

1. **The rest of `TSchemeGis`** in the model: clause (ii)'s case 2 (a child
   made after e; the probe of section 4.3 says the read first follows the
   child's first version), clause (iii) and clause (i) after the startup
   pos (Rule A's chains): 1,000 to 4,000 lines, one night; the main risk is
   case 2, which only Java's traces produce, so a Lean example of it in the
   model would help first.
2. **RC3 for the tree** (030-22, section 4.1): 300 to 800 lines.
3. **RC2 from the iteration** (030-22, section 4.2), with VAL-NEW for PE:
   1,000 to 2,500 lines; a night.
4. **The top theorem** for PE's histories with reclaim's cuts (RC1 and RC4
   stay tested, as Java's arithmetic): 200 to 400 lines.

In all 2,500 to 7,700 lines, one and a half to three nights for one or two
provers. For scale: this item's Lean is 1,688 lines, written by one
prover in about an hour and a half of six short tasks, from statements and
paper proofs given to it.

# 6. Files and gates

- **The branch** `030-23-reclaim-step1`, from `main` a0a76461, in this
  order:
  - 8636bae7, c298d5b7, ffe559e9, 8a14e337 (ReclaimScheme.lean and its
    proofs), 04c91123, fede0c91, 094765b0, 8793fe89, 43be8c12 (ReclaimGis.lean
    and its proofs): lean/contract only, with Contract.lean, Axioms.lean (21
    new lines) and statements.pin. The sub-prover's commits were made on its
    branches `030-23-prover` and `030-23-gis` and taken over unchanged
    (c298d5b7 and ffe559e9 are cherry-picks of its 3e5eae2f and 8af9a535).
  - 07c186ce: lean/Check/Steps.lean, lean/TraceCheck.lean (RC in C-CUT) and
    027-13's lines.
  - The last commit: this item, its evidence and 030's readme.
- **Gates**, at 43be8c12 in a clean clone:
  - `lean/contract/gate.sh`: GATE OK (162 theorems, the standard axioms
    only; 81 files of the closure, 92 pinned). With the base a0a76461 steps
    1 to 3 and 5 pass and step 4 lists exactly the files of 07c186ce
    (lean/Check/Steps.lean, lean/TraceCheck.lean, 027-13), which the gate
    does not allow by design; the checker's gate is level 3.
  - `java/stress/level3.sh` (full) at 07c186ce: LEVEL 3 OK (21 minutes at
    load 100; its conformance step exported its own 35 reclaim traces and
    checked them with RC: 784 CUT lines, 0 failures, least margin 9). Java
    did not change.
- **Evidence** in [23-reclaim-step1/](23-reclaim-step1/):
  - [rc-traces.txt](23-reclaim-step1/rc-traces.txt): `tracecheck` with RC
    on the 50 traces, per trace;
  - [ReclaimL.lean.txt](23-reclaim-step1/ReclaimL.lean.txt): the candidates
    in the model (a scratch program, how to run it in its header);
  - [TraceCand.lean.txt](23-reclaim-step1/TraceCand.lean.txt): the
    candidates on a trace;
  - [candidates-model.txt](23-reclaim-step1/candidates-model.txt) and
    [candidates-traces.txt](23-reclaim-step1/candidates-traces.txt): the
    runs' output, summed.
- **Where the runs were:** a scratch directory of the day (the clone, the
  traces copied from the night's clone, the outputs); not kept.


# Log

2026-11-19, 11:21. Started, from coord-1118's brief, in a clone of `main`
a0a76461, branch `030-23-reclaim-step1`.

2026-11-19, 11:28. T-SCHEME and RC written as Lean statements (with
`sorry` in my clone only) and given to a sub-prover in its own clone.

2026-11-19, 11:45. The sub-prover's first commit: the proved half and the
theorems after cuts with RC; GATE OK.

2026-11-19, 11:46. RC in `tracecheck`; the night's 50 reclaim traces
checked: 954 CUT lines, 0 failures.

2026-11-19, 11:55 to 12:50. The candidates by running, in the model and
on the traces, in rounds: GIW refuted on the traces (garbage nodes), then
GIR in the model (lag policies), then GIS needing J; GIS-J kept; POSTV's
first form refuted on the traces; case 2 found on the traces and
characterized. The sub-prover meanwhile: `rc_dref`, `TSchemeReads`, GIS-J in
Lean with `reads_of_gis`, Lemma G and clause (i), clause (ii)'s case 1.

2026-11-19, 12:38. Level 3 OK at 07c186ce; 030-12's 30 reclaim traces
checked with RC: 360 CUT lines, 0 failures.
