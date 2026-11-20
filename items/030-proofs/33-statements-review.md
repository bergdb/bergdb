# 030-33. An independent review of the statements against 030-26

Created 2026-11-20 by Frans Lundberg. Status: done (all four findings acted on, 2026-11-20).

An independent review (Codex, at Frans's request, 2026-11-20) of the Lean
statements and the definitions under them against 030-26, the public
statement that the core algorithms are proved. Not of the proofs, which
the Lean kernel checked. The reviewer's report follows as written, with
its links made paths in the repository; its probes are kept outside the
repository. What is done about each finding is in section "Actions".


## Actions

* F4: corrected 2026-11-20 (Frans): 030-26, section 5, item 1, and 030's
  readme name the apps' soak and kill rounds (the quick round in
  `week.sh short`).
* F2, F3: corrected 2026-11-20 (Frans): 030-26 says that values are
  tokens in the model and 63-bit hashes on the traces, byte equality
  tested by the functional tests (section 4), and that Java's commit-time
  check is a quick, partial check, not a complete check of the contract
  (section 4; section 5, items 1, 7, 9; section 6; TransCheck's Javadoc).
* F1: closed 2026-11-20 (Frans decided both): the trace check C-STEP
  compares the values a step writes back and refuses other writes
  (030-34); the step model requires the same, and reads after reclaim are
  proved to give the users' values (`PE.pe_reclaim_user_reads_steps`,
  030-35); 030-26, section 2.5.



## Summary

Reviewed main `34d4b59957c32c2d4a58a349b7bfa82e875cde5d`.

**Four findings: 1 high, 2 medium, 1 low.** The most important three are:

1. **High:** `StepsOK` permits reclaim to replace old values with different values. A kernel-checked Lean probe demonstrates this at M = 30, G = 8192, H = 126.
2. **Medium:** the model and trace comparisons represent values by fingerprints. Equality of those numbers is weaker than equality of byte arrays.
3. **Medium:** `TransCheck` checks a local, resident portion of the contract. The public page overstates the additional coverage it supplies outside traces.

The low finding concerns which weekly application rounds enable CC.

These findings concern the assurance claim and its tested links. I have not demonstrated a production Java correctness bug. I found no additional vacuity in the PE writer statements within their stated premises. Tracked repository files remain unchanged; no commits were made.

## Findings

### F1 — High: reclaim’s step predicate does not require preservation of values

**Claim affected.** Section 2.5 describes reclaim steps as writing again the old values they meet. It cites `pe_reclaim_reads_steps` for correct reads after reclaim. See `items/030-proofs/26-core-algorithms-proved.md:158`.

`StepTx` actually requires only:

- every old key met by the scan occurs among the transaction’s put keys;
- at least one put;
- distinct operation keys.

It does not compare the put’s value with the scanned value. It permits additional puts and deletes. Despite its comment, it neither identifies a row key nor checks that a row contains the cursor, end key and cut. See `lean/contract/Contract/ReclaimSteps.lean:103`.

The final read specification compares against `refMap` of **all** history operations, including reclaim’s operations. A wrong maintenance put therefore becomes the reference answer. See `lean/contract/Contract/RecoverJava.lean:54` and `lean/contract/Contract/ReclaimSteps.lean:626`. `IterationOK` similarly requires an old key to have been written, without preserving its value: `lean/contract/Contract/ReclaimTree.lean:293`.

**Verified by a Lean probe.** `StatementProbe.lean:14` (a probe kept outside the repository) uses M = 30, G = 8192, H = 126:

1. Transaction 1 puts `[72] = 5` and `[80] = 6`.
2. Transaction 2 puts `[72] = 999` and `[80] = 888`.
3. PE accepts the history.
4. A completed one-step iteration, with cut 2 and start 1, satisfies `StepsOK`.
5. The resulting contents contain the replacement values. There is no separate row operation.

The same file proves that `StepTx` permits a changed value and an extra delete, establishes `MeetsFull` and K-LEVEL for a related accepted history, and checks that `reclaimStepFailures` reports no failure for the bad step. These examples use `decide +kernel`. The complete wrong-value iteration theorem depends only on `propext` and `Quot.sound`.

**The executable checker has the same omission.** C-STEP discards put values when collecting put keys: `lean/Check/Steps.lean:963`. Writer, contract, bridge and PE-comparison checks can establish that the supplied operations were applied correctly without establishing that reclaim selected the right values.

Java does copy the scanned value in the code inspected: `java/src/bergdb/core/Reclaim.java:918`. Workload tests provide further evidence. That property is nevertheless absent from `StepTx` and C-STEP.

**Consequence.** The cut-safety proof remains substantive: newly written replacement values can safely survive removal of older storage. The missing result is preservation of user contents by maintenance. Either strengthen the step specification and checker, or explicitly retain exact maintenance-value preservation as a tested assumption. The reference specification should distinguish user changes from permitted maintenance changes.

### F2 — Medium: value equality is fingerprint equality

**Claim affected.** The public statement describes byte-array values and promises the plain map’s values: `items/030-proofs/26-core-algorithms-proved.md:21`.

The contract represents a value as `Obj.val (h : Nat)`, explicitly described as its hash. Puts carry that number, and gets return `Option Nat`:

- `lean/contract/Contract/Tree.lean:43`
- `lean/contract/Contract/Statement.lean:228`
- `lean/contract/Contract/Read.lean:41`

The exporter computes FNV-1a in a Java long and clears the sign bit: `java/stress/TraceExport.java:437`. OP, node-value, GET and SCAN lines use this fingerprint. `pecmp` also compares value hashes: `lean/pecmp/PeCmp.lean:236`.

There cannot be an injective mapping from all byte arrays to these 63-bit outputs. Even eight-byte arrays already outnumber the possible fingerprints.

**Evidence: source inspection and counting argument; no collision probe.** I did not construct a collision or demonstrate a Java value fault. Other Java tests perform exact byte comparisons, including `java/stress/TraceExport.java:1854` and `java/src/bergdb/core/TransCheck.java:194`.

**Consequence.** Opaque abstract values are reasonable for these algorithms. The weakness is the lossy projection used for the tested Java link. Section 5 does not explain that equality of model values need not distinguish different bytes. Its storage-decoding assumption does not make the fingerprint injective.

Document this limitation, or export lossless identifiers assigned using byte-array equality. A lossless interpretation would support the byte-value claim without a collision premise.

### F3 — Medium: TransCheck does not check the full writer contract

**Claim affected.** The page describes Java’s own check of the contract after every transaction, including as coverage for cases outside traces: `items/030-proofs/26-core-algorithms-proved.md:313`, `items/030-proofs/26-core-algorithms-proved.md:391`, and `items/030-proofs/26-core-algorithms-proved.md:424`.

Its source explicitly describes narrower coverage:

- no stream reads; nonresident pointers end that part of the check;
- transaction paths and selected reported nodes are visited;
- unchanged nodes outside D, and order, kinds, levels and contents beyond the visited area, are not fully checked.

See `java/src/bergdb/core/TransCheck.java:27`. The implementation skips a value check on `UNKNOWN`, and traverses another key node only when a transaction key passes through it or it was reported interesting: `java/src/bergdb/core/TransCheck.java:194`, `java/src/bergdb/core/TransCheck.java:554`.

The Lean `Frame` quantifies over every old node: `lean/contract/Contract/Statement.lean:337`. The trace checker has a global computation over its reconstructed heap, with a soundness theorem: `lean/contract/Contract/Check.lean:44`, `lean/contract/Contract/Check.lean:97`.

**Evidence: source inspection only.** The attempted Java local-property probe was not successfully built or run and supplies no runtime evidence. No further Java fault probe was run.

**Consequence.** Additional TransCheck workloads are useful evidence, but they do not establish the complete contract on those commits. The public page should describe a local check of resident transaction paths and reported changes, retaining its documented exclusions.

### F4 — Low: the full weekly CC coverage is soak and kill, not quick and kill

Section 5, item 1 names the applications’ “quick and kill rounds”: `items/030-proofs/26-core-algorithms-proved.md:391`.

With no inherited CC setting, full `week.sh` runs `apps-quick` without `with_cc`, followed by `apps-soak-cc` and `apps-kill-cc`. Its short branch runs `apps-quick-cc`: `java/week.sh:179`. The wrapper’s environment variable is confined to its subshell: `java/week.sh:139`.

**Evidence: source inspection only.** Replace “quick” with “soak” for the normal full weekly run, or distinguish the short run.

## What I checked and found right

## Claim-to-theorem map

1. **Transactions, invariants and frame — sections 1 and 2.1.**  
   `pe_meetsTop_start` supplies `MeetsTop` for accepted histories from the empty state, using `pe_step` and preservation of `Inv`: `lean/contract/Contract/Proof/PeTx.lean:174`, `lean/contract/Contract/Proof/PeTx.lean:452`. The contract compares tree contents with independently defined `applyOps`; it is not defined as whatever PE returns. `PeHist` openly restricts histories to accepted transactions: `lean/contract/Contract/PeStatement.lean:46`.

2. **Acceptance and refusal — section 2.1.**  
   `pe_accepts` requires `Inv`, valid put keys, `FuelOk` and `Room`; `pe_refuses` rejects invalid put keys: `lean/contract/Contract/Proof/PeAccept.lean:1111`, `lean/contract/Contract/Proof/PeAccept.lean:1189`.  
   `pe_accepts_java` covers sizes 8, 14, 30 and 62, G = 8192, H = 126, fewer than 2^63 reachable nodes and at most 2^20 operations, conditional on `Inv`, `FillOk` and valid put keys: `lean/contract/Contract/Proof/DnbRoom.lean:378`. The public page discloses that fill-rule preservation is tested.

3. **Latest and historical reads — section 2.2.**  
   `get_right` and `scan_right` cover t at most the history length; scans require `req.wf`: `lean/contract/Contract/Theorems.lean:52`. `jget_right` and `jscan_right` add skip-pointer search, including times between transactions: `lean/contract/Contract/TheoremsTop.lean:87`. The forward-only end-key restriction is explicit in `ScanReq.wf`. Subject to F2, the sorted-map comparison is substantive.

4. **TREE at historical times — section 3.1.**  
   `tree_right` covers every t at most the history length, not just the latest tree: `lean/contract/Contract/TheoremsShape.lean:22`. PE supplies the stronger history through `MeetsTop`.

5. **Crash recovery and restarts — section 2.3.**  
   `pe_full` establishes `MeetsFull` and K-LEVEL under the stated bounds. `full_recovery` handles prefixes of whole abstract records, and `pe_crash_reads` covers reads through k: `lean/contract/Contract/Proof/PeFullProved.lean:14`, `lean/contract/Contract/BridgeFull.lean:73`.  
   `crash_java_reads` and `restart_java_reads` additionally require `HoldsView`: `lean/contract/Contract/RecoverJavaTheorems.lean:34`. This is a representation premise, not a proved byte decoder. Torn-byte handling remains in the declared tested storage/startup links.

6. **Eviction and lazy startup — section 2.4.**  
   `full_eviction` states record/D invariance and correctness of abstract handle reads: `lean/contract/Contract/BridgeFull.lean:95`. `evict_java_reads` and `lazy_java_reads` lift this to the Java-reader model, conditional on representation and top-node premises: `lean/contract/Contract/RecoverCutTheorems.lean:93`. They do not directly assume the desired read equality.

7. **Cut safety — section 2.5.**  
   `iterationOK_of_stepsOK` derives iteration coverage from `StepsOK` and VAL-NEW: `lean/contract/Contract/ReclaimSteps.lean:511`. `cutOK_of_rc` derives all of `CutOK` from RC and the remaining abstract assumptions: `lean/contract/Contract/ReclaimReads.lean:86`. The final PE theorem eliminates a separate VAL-NEW hypothesis using `pe_valNew`. The obsolete `TSchemeOpen` is not a premise of the final theorem. F1 concerns maintenance values, not an unfinished half of `CutOK`.

8. **Dirty-node count — section 2.7.**  
   `pe_dirtyNodeBound_puts` bounds key-node writes for accepted put-only transactions from an invariant state satisfying `FillOk`. Its history corollary still requires `FillOk`: `lean/contract/Contract/Proof/DnbMain.lean:39`. Comparing the executable count with Java’s walk, overflow, fresh-tree, collapse and root calculations revealed no discrepancy in the stated domain. Deletes remain excluded, as disclosed.

## Other premises and boundaries

- **The numerical acceptance bounds are consistent.** Java and `Cfg.java` agree on the thresholds at sizes 8/14/30/62. The top base is 1,040,512. The largest stated fuel expression, at B = 62 and p = 2^20, is 1,091,387,825,856, below 2^40 = 1,099,511,627,776. See `lean/contract/Contract/DirtyBoundStatement.lean:23` and `lean/contract/Contract/Proof/DnbRoom.lean:270`. This does not establish fill-rule preservation.

- **The transaction-count restriction is real and disclosed.** The fewer-than-2^48−1 premise is on history length, not Java’s top-node ordinal. I did not find it silently dropped from the final PE recovery/cut theorem.

- **The final reclaim theorem has additional formal premises.** Besides the short RC1/RC4 description, it takes `PolicyCutOK`, permitted times for intervening reads, `HoldsView` and `TopFrom`: `lean/contract/Contract/ReclaimSteps.lean:630`. `PolicyCutOK` concerns unchanged policy choices after a prefix cut. It follows for the trace checker’s stream-independent policies by `lean/contract/Contract/BridgePolicy.lean:44`. Naming these conditions would make section 5 easier to audit.

- **The combined cut run restarts at each cut event.** It rebuilds handle memory at that event: `lean/SIS/HandleReclaimTheorems.lean:29`. The separate `T9_handles` statement covers a live cut retaining existing memory: `lean/SIS/HandleReclaimTheorems.lean:45`. These schedules should be distinguished when explaining the combined theorem alone.

- **Bridge restart invariance uses fixed changes.** `BHist.spec` uses `bspec`, whose `exec` returns the change indexed by the transaction and ignores the input view: `lean/contract/Contract/Bridge.lean:143`, `lean/Check/Trace.lean:340`. Thus `full_restart` does not prove Java or PE recomputes the same changes after reopening. The page appropriately retains this as tested assumption 9.

- **The dirty-node theorem is not an end-to-end admission or serialized-size proof.** Java usually tries a cheaper count first and may return before calling `Dag.dirtyNodeBound`; transformed keys use another allowance: `java/src/bergdb/core/Db.java:3256`. Those paths are outside this theorem. `keyWrites` counts key nodes, not serialized bytes. I found no counterexample to the other paths.

- **Reclaim progress is not proved.** Stop rules may stop immediately; completion is a hypothesis about the chosen finite iteration. No finite-completion, retention-duration or stream-size theorem follows from `StepsOK`. Section 4 correctly excludes stream-size and cost guarantees.

## Audit of the thirteen tested assumptions

This is a source audit of test wiring, not a rerun of the nightly or weekly suites.

1. **Writer equality:** level2 runs tree sets, contract/bridge checks and pecmp: `java/stress/level2.sh:215`. Ordinary contract/bridge sets are small and drain; tree/pecmp also cover reclaim. Night adds medium and daily sets. F3 qualifies CC; F4 corrects the weekly round name.

2. **Synced durability**, and **3. torn-tail crashes:** the named CrashTest, PowerLossTest and kill runs are wired as described: `java/stress/level2.sh:197`, `java/stress/level3.sh:139`, `java/week.sh:184`. Testing these fault models does not prove the platform premises.

4. **One writer/concurrency:** ReclaimReaders, eviction-reader and InterruptStress steps exist. The page accurately says jcstress runs by hand; it does not promise an automated jcstress gate.

5. **Decoding:** restart and workload comparisons exercise it. Some Java comparisons use exact bytes; Lean trace comparisons have F2’s limitation.

6. **Readers:** GET/SCAN/LIVE/SKIPT comparisons are actual verdict conditions: `lean/contract/Contract/Verdict.lean:64`. They are not merely counts of read lines.

7. **Operations:** the exporter captures the applied key/value hook and emits OP lines from it: `java/stress/TraceExport.java:934`, `java/stress/TraceExport.java:1223`. Trust in the hook/export remains a tested link.

8. **Refusals:** the named tests exist at `java/src/bergdb/core/DbTesterDelete.java:611` and `java/src/bergdb/core/DbTesterRestart.java:2033`. Refused transactions are excluded from `PeHist`; the writer theorem does not prove Java’s refusal behavior.

9. **Behavior across runs:** the stated invariance tests and B/E conformance runs exist. This assumption is necessary because the bridge takes fixed changes. It is openly retained.

10. **Records/dirty sets:** tracecheck executes the abstract record algorithm. The tree checker’s whole-run check also generates its own PE changes: `lean/Check/TreeRun.lean:54`. Policies come from the trace; record comparisons are abstract, not every serialized byte.

11. **Reclaim:** level3 runs step fault tests, reclaim traces and restart/crash traces: `java/stress/level3.sh:179`. RC4 genuinely checks the second wait: `lean/Check/Steps.lean:318`. F1 is the missing value-preservation condition.

12. **Trace fidelity:** the contract verdict requires completeness and parsing before checking history. Reclaim/crash suites reject traces with no cut or no STEP; the crash suite also requires a crash: `java/stress/conformance.sh:356`. These checks do not prove exporter fidelity.

13. **Startup representation:** the stated restart, cold-cache and cut-stream tests are wired into the level scripts. These are tested counterparts of the representation premises, not consequences of the standard Lean axioms alone.

Application traces are replays. Contract/bridge checks use a replay without restart/STEP lines; tracecheck checks the extended restart metadata: `java/stress/apptraces.sh:43`, `java/stress/apptraces.sh:155`.

## Verification performed

- Read the requested documents, statement inventory, pins, main theorem signatures and relevant definitions, Java code, checkers and scripts.
- Built `lean/contract`, tracecheck/treecheck, contractcheck/bridgecheck and pecmp successfully.
- Ran `StatementProbe.lean` successfully, including again after access became read-only. Only unused-simp-argument warnings were emitted.
- Exported one small M = 30 Java trace before that restriction: 30 workload transactions plus two setup transactions; zero exporter errors.
- Verified **TREE OK, TRACECHECK OK, CONTRACT OK, BRIDGE OK and PECMP OK** on that trace. Contractcheck compared 128 GETs and 32 SCANs. Pecmp compared 32 transactions and five new top nodes, with zero differences.
- Ran existing fixtures: `example.trace` passed; `cut.trace`, `stale.trace` and `badhandle.trace` were rejected by the relevant cut/stale-version/handle checks.
- Verified all **112 pinned hashes**, with all **91 statement-closure files** covered. The axiom inventory has 198 entries; the closure excludes examples and reports 162 roots. These counts are consistent.
- Validated 89 file/line link targets in the prepared report.
- Did not audit proof bodies or rerun the full gate, night, week or level suites. The supplied kernel/standard-axiom result was the starting point.
- The attempted Java local-property probe was not successfully built or run. No further Java data-removal probe was made.
- Git checks showed no tracked changes.
