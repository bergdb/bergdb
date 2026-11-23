# 030-39. An independent review of the guarantees of release 2026.6

Created 2026-11-23 by Frans Lundberg. Status: done (the nine findings and
030-38's eight differences from 030-26 closed, 2026-11-23).

An independent review of 030-38, the guarantees of release 2026.6, by
Codex (gpt-6.1-sol, reasoning high; 026-27, step 3, D3), at 951e15f9:
each guarantee against its theorem's statement in Lean and its check's
script, and each place where the list says more than is proved or
checked. Not of the proofs, which the Lean kernel checks. The reviewer's
report follows as written, with its links made paths in the repository;
its probes are kept outside the repository. What is done about each
finding, and about 030-38's eight differences from 030-26 (026-27, step
5), is in section "Actions". The precedent is 030-33.


## Actions

Each finding and each difference is closed on 2026-11-23: corrected in
030-38, in 030-26 (026-27, step 7) or in the checks, or accepted with its
reason. No statement of a proved theorem is changed.

The findings:

* **F1, C-STEP and the row's key: corrected in the checks.** C-STEP
  checks each step's row at the model's key, `reclaimRowKey` in
  `lean/Check/Steps.lean`: Java's `-current.txt` under `/#i/dreclaim/`,
  as `Keys.toSegments` makes it, which is how a trace writes a key.
  `Contract.ValuesExample.checker_row`, among the gate's theorems, proves
  it equal to `Contract.reclaimRow`, the key at which `StepTx` requires
  the row. Until then C-STEP took the row's key from the trace's first
  step. The reviewer's probe is a `#guard` in `Steps.lean`: C-STEP fails
  its step now (STEP-values, STEP-ops). The check's fault test,
  `lean/test-traces/step-faults.sh`, has a new fault, `row`: every put
  of the row's key made a put of the key [8]. The checker before the
  change passed that trace whole (TRACECHECK OK; C-STEP: 0 of 363
  transactions fail); now C-STEP fails it at each of its 14 steps
  (STEP-ops). 030-38 (G7, link 11), 030-26 (section 4; section 5, item
  11), 027-02 and `lean/TraceCheck.lean` say so.
* **F2, durability and the storage's forcing: corrected** in 030-38 (G12;
  section 4, item 12) and 030-26 (section 4, "The platform"; section 5,
  item 2). G12 holds with hard sync, the storage's default
  (`FileStream(dir)`). With per-append forcing off (`FileStream(dir,
  false)`), a synced transaction survives a crash of the process only;
  a crash of the operating system or a power loss can lose it and can
  leave a hole that recovery does not handle (014-01). PowerLossTest
  models the persistence boundaries; it is not a physical power cycle.
* **F3, reads that reclaim overtakes: corrected** in 030-38 (G14; section
  4, item 13) and 030-26 (section 4; section 5, item 4). A read that
  returns gives the reference answer at its own time; a read can throw
  `LookupTimeNotAvailableException` when a cut overtakes it, also a read
  of the latest state or of a time available when it began, as
  ReclaimReaders allows.
* **F4, a start at every cut: corrected** in 030-38 (G6; section 4, item
  11) and 030-26 (2.5), **and accepted** for release 2026.6: the
  theorem's run starts again from the cut stream at every cut, with its
  memory made anew. A cut that keeps the memory, as Java's, is proved for
  the abstract model of the stream (`SIS.T9_handles`), which no gated
  theorem ties to PE's histories; for Java it is tested (ReclaimStress,
  ReclaimReaders, the reclaim traces). A theorem for PE's histories with
  cuts that keep the memory is proof work for later, not a todo entry.
* **F5, `PolicyCutOK`: corrected** in 030-38 (G6) and 030-26 (2.5): the
  policies choose the same startup position and first available time on
  a stream cut at or before its first available time; this holds for
  policies that read no stream (`Contract.policyCutOK_of_blind`), as the
  trace checker's.
* **F6, `FillOk` in full: corrected** in 030-38 (G8, G9; section 4, item
  14) and 030-26 (2.1): five rules, RootsOK, FillOK, LeftmostOK, DeadOK
  and BalancedOK. Tested by the tree checker's C-T6, which checks the
  first four by name and BalancedOK's levels as KindsOK, and fails a
  trace that breaks one; the contract checker computes `shapeFaults`
  itself and reports its count apart, without failing on it (0 on every
  set of `night.sh` of 2026-11-23). Proposed as a 028 entry, not
  numbered: the contract checker fails a trace with a shape fault
  (`lean/contract/ContractCheck.lean`, a pinned file).
* **F7, value transformations: corrected** in 030-38 (G9; section 4, item
  6) and 030-26 (2.7), **and accepted** for release 2026.6: the theorems
  count the transaction's operations, each key once as a put or a
  delete; `Db.checkDirtyNodes` walks a key with a value transformation as
  a put and as a delete. That this bounds the count of the operation the
  transformation gives is argued (023-11, review B, B2), as the cheap
  estimate and key transformations are (028-21), not proved and not
  tested on purpose. Proposed as a 028 entry, not numbered: a test that
  compares `Db.checkDirtyNodes`' count, with its own arguments, with the
  key nodes a transaction marks, for value and key transformations and
  where the cheap estimate fits.
* **F8, DagTester's node sizes: corrected** in 030-38 (G10) and 030-26
  (section 5, item 14): random histories at node sizes 8, 14, 30 and 62;
  the purpose-made deletes at 8, 14 and 30; the test counts joins, not
  their heights. Proposed as a 028 entry, not numbered: the purpose-made
  deletes at node size 62 too, with an assertion of joins of inner nodes
  at height two or more (joins counted by height).
* **F9, the stream's size and the premises: corrected** in 030-38 (G6;
  section 4, items 9 and 10) and 030-26 (2.3, 2.5, section 4): no theorem
  says that reclaim makes progress or bounds the stream's size;
  `java/stress/large.sh` tests a bound on the kept bytes. 030-26 names
  `HoldsView`, `TopFrom`, `PolicyCutOK` and the times of reads between
  cuts.

030-38's differences from 030-26 (its section 4):

1. The user section's one condition: corrected in 030-26, section 1.
2. The history's bounds: corrected in 030-26, section 1.
3. Scans with an end key: corrected in 030-26, 2.2.
4. Scans across reclaim's namespace: corrected in 030-26, 2.5.
5. `pe_dirtyNodeBound_twoJoinLevels_history` not among the gate's
   theorems: corrected in the gate. `lean/contract/Axioms.lean` lists it
   (and `checker_row`, F1): 254 theorems; `statements.pin` written again
   by `pin.sh`, with Axioms.lean's new hash only (the closure unchanged,
   123 files, 144 pinned). 030-38's G9 cites it; 030-26, 2.7.
6. Db's cheap estimate: accepted for release 2026.6, with the value
   transformations added (F7); 030-38, G9, and 030-26, 2.7, state the
   gap; a 028 entry proposed (F7).
7. The tested part of the dirty-node bound: corrected in 030-26, section
   5, item 14.
8. RestartStress's scripts: corrected in 030-26, section 5, item 5.

The gates, in a clone of `main` at 4583ca02 with these changes (no Java
code changed; level3.sh runs C-STEP on Java's reclaim traces):

```text
lean/contract/gate.sh (with pin.sh first):
  3. the standard axioms only (254 theorems)
  5. the statements pinned: 123 files of the main theorems' closure, 144 pinned
  GATE OK
java/stress/level2.sh: LEVEL 2 OK
java/stress/level3.sh, step 8 (C-STEP):
  C-STEP's fault test: 18 faults found, STEP FAULTS OK
  conformance: traces: 35, TRACECHECK OK: 35; C-CUT 0 of 775 CUT lines fail
  C-STEP: 0 of 21483 transactions fail; 1014 STEP lines, 907 iterations
  across restarts and crashes: traces: 15, TRACECHECK OK: 15
  C-STEP: 0 of 6837 transactions fail; 503 STEP lines, 309 iterations
java/stress/level3.sh: LEVEL 3 OK
```

Nothing is left for Frans to decide but the three 028 entries proposed
above (F6, F7, F8), none needed for the release.


## The report

Reviewed at `951e15f9`. I found the following assurance gaps and imprecisions. None demonstrates a production Java bug.

All **24 cited theorem names** occur in `Axioms.lean`; all **144 pinned file hashes** match. I did not rerun the full contract gate or the night/week/level suites.

**F1 — G7 and section 3, link 11: C-STEP does not establish the theorem’s reserved-row premise. Severity: overclaim.**

- **Claim:** C-STEP checks that Java’s steps follow the model, preserving rewritten values and permitting only the rewrites and reclaim’s row.
- **What it gives:** The checker infers the row key from an exceptional put. It can designate a changed **user value** as the row. The theorem’s `StepTx` instead requires the fixed `reclaimRow`, in reclaim’s reserved namespace.
- **Evidence:** `items/030-proofs/38-guarantees.md:302`; `lean/Check/Steps.lean:986–1008`; `lean/contract/Contract/ReclaimSteps.lean:110–143`. The Lean probe below confirms this checker gap.
- **Correction:** Check the exact model row key, or parameterize the theorem over a checked reserved row key. Until then, disclose row identity as an additional Java-to-model assumption. A C-STEP pass alone does not establish the complete strengthened `StepTx`.

**F2 — G12: sync durability and the torn-tail guarantee omit the storage mode. Severity: overclaim.**

- **Claim:** Every synced transaction survives power loss, and a crash leaves at most a partly written final record.
- **What it gives:** With per-append forcing disabled, the power-loss checker protects the last **forced** acknowledgement, rather than the last sync. It deliberately permits recovery failures from holes in the unforced tail. The public `FileStream(dir, false)` documents both limitations.
- **Evidence:** `items/030-proofs/38-guarantees.md:237–247`; `java/src/bergdb/core/FileStreamPowerLossTester.java:134–144,788–798`; `java/src/bergdb/stream/FileStream.java:261–270`; `java/stress/PowerLossTest.java:19–32`. `java/stress/level3.sh:173–176` runs both modes.
- **Correction:** Restrict the power-loss guarantee to forcing-enabled storage under the stated persistence assumptions. Explain that forcing-disabled sync provides weaker durability and that unforced-tail holes can prevent recovery. Distinguish the modeled power-loss tests from physical power cycling.

**F3 — G14, extending G2/G6/G7: concurrent reads may expire. Severity: overclaim.**

- **Claim:** Reader/writer/reclaim races leave the read guarantees true, which say a retained-time get or scan returns the reference answer.
- **What it gives:** `ReclaimReaders` explicitly accepts `LookupTimeNotAvailableException` when reclaim overtakes a read. A snapshot available when the operation began can expire during it; this also applies to a latest-state request.
- **Evidence:** `items/030-proofs/38-guarantees.md:261–270`; `java/stress/ReclaimReaders.java:29–39,234–254,263–267,302–306`. The slow-scan workload intentionally invites this outcome at `:365–367`. The harness is run by `java/stress/level3.sh:153–161` and `level4.sh:136–150`.
- **Correction:** State that successful reads agree with the reference at their actual snapshot, while reads whose snapshots expire may throw, including when the snapshot was retained at admission.

**F4 — G6/G7: the combined theorem uses a restart at every cut event. Severity: imprecise.**

- **Claim:** Correct reads follow “any run with cuts, handles, evictions and restarts from the cut streams.”
- **What it gives:** The cited PE theorems use `runHandlesCut`. Every `some c` event cuts the stream and immediately rebuilds both the logical state and handle memory. It does not represent arbitrary sequences of live cuts retaining existing memory.
- **Evidence:** `items/030-proofs/38-guarantees.md:131–165`; `lean/contract/Contract/ReclaimSteps.lean:657–673`; `ReclaimValues.lean:349–366`; `lean/SIS/HandleReclaimTheorems.lean:29–43`. The separate live-cut statement is `T9_handles`, at `:45–67`.
- **Correction:** Describe the combined theorem’s cut-and-restart schedule explicitly. Cite and connect the separate live-cut result if the intended claim also covers cuts that retain existing handle memory.

**F5 — G6/G7: the explanation of `PolicyCutOK` describes another property. Severity: imprecise.**

- **Claim:** `PolicyCutOK` means the cache’s choice of nodes “reads nothing of a cut stream.”
- **What it gives:** It requires the policy’s computed **startup position and first available time to remain equal** after removal of a prefix at or before the first available time. This is policy invariance, rather than a condition on cache reads.
- **Evidence:** `items/030-proofs/38-guarantees.md:145–147`; `lean/SIS/Reclaim.lean:148–155`.
- **Correction:** Replace the gloss with that equality requirement. Keep read safety as the conclusion derived from the cut and reader premises.

**F6 — G8/G9: the stated fill rules omit part of `FillOk`. Severity: imprecise.**

- **Claim:** The fill premise is described as two live entries in an inner root and at least `m` in other key nodes, checked by `RootsOK` and `FillOK`.
- **What it gives:** Both cited acceptance and count theorems assume the full `FillOk`, defined by an empty `shapeFaults` result. That includes `LeftmostOK`, `DeadOK` and `BalancedOK` as well as occupancy. In particular, the dead-entry bound is absent from the list’s explanation. Some other shape conditions overlap `Inv`.
- **Evidence:** `items/030-proofs/38-guarantees.md:180–185,202–205`; `lean/contract/Contract/DirtyBoundStatement.lean:12–16,30–33`; `Contract/Shape.lean:48–58`; `Contract/Proof/DnbRoom.lean:384–388`; `Contract/Proof/DnbMain.lean:154–173`.
- **Correction:** Name the full `FillOk` premise and its constituent checks. Avoid presenting the two occupancy checks as its complete definition.

**F7 — G9/G10: value transformations introduce another admission-count gap. Severity: imprecise.**

- **Claim:** G9 connects the proved count to Java’s admission check, qualifying the cheap estimate and key transformations.
- **What it gives:** The theorem bounds `dirtyNodeBound … (opsKd ops)`. Its argument conversion explicitly models transactions without key **or value** transformations. For a value transformation, Java instead supplies both a put and a delete possibility for the key. The cited statements do not establish the relation between that doubled-input count and the effective operation’s count. C-T8 likewise uses the trace’s effective operations.
- **Evidence:** `items/030-proofs/38-guarantees.md:187–223`; `lean/contract/Contract/DirtyBound.lean:335–340`; `Contract/Proof/DnbMain.lean:154–174`; `java/src/bergdb/core/Db.java:3302–3317`; `lean/Check/Tree.lean:335–341`.
- **Correction:** Disclose argument preparation for value transformations as another Java admission link requiring justification. Either prove its sufficiency or identify its separate argument/tests. Add this qualification to section 4’s difference 6.

**F8 — G10: the purpose-made multilevel-delete case does not include size 62. Severity: minor.**

- **Claim:** `DagTester.testDirtyNodeBoundOfPe` supplies deletes joining several levels at node sizes 8, 14, 30 and 62.
- **What it gives:** The routine exercises all four sizes in other cases, including randomized histories. Its explicit multilevel-delete case runs only at **8, 14 and 30**. Its assertion counts total joins, without checking their heights.
- **Evidence:** `items/030-proofs/38-guarantees.md:221–223`; `java/src/bergdb/dag/DagTester.java:1146–1177,1180–1198`. The unit-test invocation is present at `java/before-commit.sh:117–123`.
- **Correction:** Distinguish the four-size general coverage from the three-size purpose-made delete case. If size-62 higher-join coverage is promised, add that case and assert the relevant join depth.

**F9 — Section 4: the differences list omits the removed stream-growth claim. Severity: minor.**

- **Claim:** Section 4 identifies where 030-38 narrows 030-26.
- **What it gives:** All eight enumerated differences check out, including the ungated `_history` name and the corrected RestartStress wiring. But 030-26 also says finite retention keeps the stream from growing without end. G6 drops that promise. The cited read-safety theorem assumes completed iterations; it supplies no completion or stream-size bound.
- **Evidence:** `items/030-proofs/38-guarantees.md:316–362`; `items/030-proofs/26-core-algorithms-proved.md:161–174`; `lean/contract/Contract/ReclaimSteps.lean:79–85,174–181,657–673`.
- **Correction:** Add “no reclaim-progress or stream-size guarantee” to the differences. Also record the explicit representation/policy/read-time premises added around G3–G7 and the qualifications above.

The probes ran successfully:

- `RowScopeProbe.lean` (a probe kept outside the repository), through `lake env lean`, using the installed repository toolchain and no Mathlib download. It changes user key `[8]` from `1` to `999`, omits the reserved row, and receives **`([], 1, some [8])`**: no C-STEP failures, one old key, inferred row `[8]`.
- `PowerLossScopeProbe.java` (a probe kept outside the repository), invoking the existing forcing-disabled checker with seed 1, 600 transactions and one sample per event. Output: **`PROBE: required recoveries=20, holes recovered=0, holes failed=4`**.

Tracked files remain unchanged; only `probes/` is untracked.

Found sound within their stated model scope and tested Java links: **G1, G2, G3, G4, G5, G11 and G13**. For G4/G5, Java recomputing the same changes across runs remains the expressly tested link 9.
