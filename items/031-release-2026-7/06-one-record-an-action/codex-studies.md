# Independent second opinion: 031-05, (c), (d), (e)

Codex's review of the two studies of A1, `study.md` ((e)) and `study-d.md`
((d)), and of (c), on 031-05's prototype, 2026-11-27, 10:44 to 10:54,
before the prototype of (e) was built; its own report, unchanged below.
Its probes and logs (`a1/reproduced/`) are outside the repository.

## Findings

- **[read] Scope:** 2026-11-27, branch `031-05`, `4135ba2a`; both A1 studies are proposals, not implementations.
- **[ran] Evidence:** built with `java/build.sh`, JDK 27; copied the studies' named probes into `a1/reproduced/` and ran them against this checkout's jar. Logs are in `a1/reproduced/logs/`.
- **[read] Notation:** Java filenames below are relative to `java/src/bergdb/`; Lean filenames to `lean/`. “Inferred” identifies design reasoning, including counterexamples to proposed rules; it does not mean an implemented design failed.
- **[read] Action model checked:** 031-05 treats accepted transaction times as inputs, fixes the initial stream/settings, and counts a completed `maintain()` part as an action when a call is interrupted; the comparisons below use that convention.

### E1. Mixed records need per-value provenance, not a record-wide reclaim test

- **[read] Where:** `pubimp/ConnectionImp.java`, `transactionInfoInner`, `isReclaims`, `valueOf`; `core/Db.java`, `getTransInner`; `core/StoredValueNode.java`, `parse`.
- **[ran] Case:** `ExtraProbe` wrote a synthetic mixed record through Core: a new user value, an equal-byte user put, and a reclaim-prefix KV. `getTrans` returned its three nodes; `transactionInfo()` threw `InternalDataException` for the new value and attributed the equal-byte put to time 10000002 instead of its actual 10000003.
- **[inferred] Consequence:** the study's copy mark is necessary. Follow backwards only when the *looked-up value node* is marked copy; filter copies from the originating action's KV list. Equality of bytes cannot identify a copy. Raw Core `getTrans` should still expose the complete record and its marks.
- **[read] Format feasibility:** `StoredValueNode.parse` skips bytes 6–7; they provide space, but serialization, checksum coverage, parsed node metadata and trace export must all preserve the mark.

### E2. The proposed own-record predicate has an empty-record hole

- **[read] Where:** `core/Reclaim.java`, `recordWritten`, `initFromDb`, `isOwnRecord`, `rowA`; study (e), section 10 rule 10.
- **[ran] Case:** `ExtraProbe` appended an empty user commit: its stored record has zero value nodes and today's `isOwnRecord` returns false.
- **[inferred] Missed case:** “every KV is a copy or reclaim key” is vacuously true for that record, although it carries no row holding `appA`. After a preceding application record with no maintenance, startup can recover an older row's `a`, while the running database retained the newer application position; with no table it instead falls back to the empty record's position.
- **[inferred] Fix:** require a maintenance-key witness as well as the universal condition, and ensure every record classified as maintenance persists the correct `a`. Empty commits without maintenance remain application records. The copy mark alone does not supply this invariant.

### E3. The one-record lag is plausible for safety, but it changes the policy

- **[read] Where:** `core/Reclaim.java`, `commitWork`, `lastKeyAt`, `step`, `markSafePositions`, `cutRow`, `pretruncateAt`, `initFromDb`; `core/Db.java`, `store`; `storage/RecoverableStream.java`, `append`, `writeMetaBlock`.
- **[inferred] Checked quantities:** at pre-record length L0, begin with `pStart=L0`, the previous record's `tStart` and its last live key; scan that pre-record state; finish with `pEnd=L0`, `tEnd=tt`; mark safe with `pSafe=L0` using the *previous* startup position. These are computable before append.
- **[inferred] Safety argument:** the takes that justified a pre-record `sp>=pEnd` are already before L0. The new record's take cannot invalidate that history; any nodes it keeps dirty are at L0 or later. The new last step cannot become safe in its own record, nor a newly safe row be cut there, because the old startup position precedes L0.
- **[inferred] Meta blocks:** use the last valid block already in the prefix for the cut predicate. A block produced during this append can enable a cut only in a later action. No prediction of that new block is needed; using it in the current plan would violate the proposed lag.
- **[inferred] Durable point:** decide the cut from old `sp`, old meta-block `lastTrans`, and `tt`; install its pending physical cut only after append, with durability through the resulting record and required block. Reopening must reconstruct the same decision from the stored table.
- **[read] Limitation:** `pretruncateAt` currently obtains that durable point after `storeTable`; none of this mixed-record ordering is built or checked by the studies' size probe.

### E4. Dropping overlapping copies does not by itself lose a live value

- **[read] Where:** `dag/PeWriter.java`, `shortWay`, `LeafFrame.step`; `core/Db.java`, `transformKeys`, `transformValues`, `putKvs`; `core/Reclaim.java`, `step`; `contract/Contract/ReclaimSteps.lean`, `old_live_before`, `step_covers`.
- **[read] Checked claim:** PE creates a new value node even for an equal-byte put; a delete removes the live entry. Key transformations and user value transformations finish before the proposed merge.
- **[inferred] Cases:** an overlapping put therefore supplies a node at/after L0; a delete leaves no live value to save; a value transformation returning the old bytes still supplies a new node, and one returning null deletes. Drop by the *final transformed key*, never the submitted key.
- **[inferred] Refusal:** advance neither `lastKey` nor `rewritten` in live reclaim state until the mixed record succeeds. A refused transformation or admission check must leave the plan unapplied; dropping a copy then publishing progress without the user's put would indeed lose an old live value at a later cut.
- **[inferred] Coverage obligation:** preserve the touch/dirty guarantees for copies, the row and overwritten keys, including replacements and deletes; the old step-only proof does not establish the new mixed-batch case automatically.

### E5. “Skip the step if it does not fit” loses a liveness guarantee

- **[read] Where:** `core/StoredTrans.java`, `valueLimit`, `dirtyLimit`; `core/Db.java`, `checkSize`, `checkDirtyNodes`, `store`; `core/Reclaim.java`, `step`; study (e), section 2; 024-17, section 5.3.
- **[inferred] Missed workload:** at a lowered record limit, keep submitting admissible transactions that leave less room than the next old live value requires, without writing that key. If the first copy is never admitted, the scan cannot pass it; reclaim can remain stuck indefinitely while the stream grows. No later smaller transaction or `maintain()` is guaranteed.
- **[inferred] Assessment:** this is determinism without progress, not merely a one-record delay. It breaks a bound on stream kept that assumes commits advance reclaim. It need not lose data if the cut continues to wait.
- **[read] Release distinction:** 024-17 gives substantial room at release limits, but its 1.51 GB bound is for the existing user batch. The study does not derive the mixed batch's bound, including row/table writes, dirty nodes, touch and future whole-transaction takes.
- **[inferred] Requirement:** prove a maintenance reserve at supported limits, or specify a progress mechanism when room is exhausted; do not claim “less maintenance keeps both rules” as a space-bound argument. Existing `MAX_STEP_SIZE` already limits pace, so even with room the original bound must be re-established for the changed schedule.

### E6. Planning before the go point is safe only with explicit lifecycle rules

- **[read] Where:** `core/Db.java`, `executeLocked`, `stmCheckConflicts`, `stmRecordKeys`, `fail`, `assertDbStateIsActive`; `core/DbClock.java`, `transactionBegin`, `currentTime`, `lookupTime`.
- **[inferred] STM:** reserve `tt` before the scan, retain the write lock, and check conflicts before planning. `lookupTime(MAX)` then reads the previous completed transaction; concurrent readers get times below `tt`. No writer can invalidate the scan. Pure copies need not enter user conflict hashes because they change no logical value; actual transformed user writes still must.
- **[inferred] Stop/P7:** use detached rows and no live counters or cuts while planning. A stop-induced refusal before the go point writes nothing; explicitly handle that case, cancel the reserved transaction time and restore transformed transaction inputs if reuse is supported. Other plan failures invoke P7; after mutation begins, any failure requires restart.
- **[inferred] Ordering requirement:** no ordinary refusal may follow plan application. A stop just after the last scan read needs an explicit admission decision; moving code earlier does not itself create that check. Failure after append but before `apply` is recoverable only if startup restores everything `apply` would install.
- **[read] P1 check:** `executeLocked` already holds the write lock through maintenance, but publishes `transactionEnd` before it; `getTransInner` can wait for that lock, and `transactionInfoInner` calls it.
- **[inferred] P1 verdict:** (e) delays visibility until after the scan and still makes queued commits wait for it. Ordinary latest gets can read the previous state without waiting for this scan; record readers can wait for the writer. One larger batch/take is not proved cheaper than separate ones. The study's “confirmed” 20 ms conclusion is unsupported; no timing run here establishes it.

### D1. The deferred byte also defers a meta block and changes the close decision

- **[read] Where:** `core/NodeStream.java`, `appendNodes`, `getLength`, `readRecordHeader`, `readTransBytes`; `core/Db.java`, `store`, `ExecuteData.begin/end`; `storage/RecoverableStream.java`, `append`, `writeMetaBlock`.
- **[ran] Missed boundary:** `ExtraProbe` left the closing byte at position 199999 pending. Length was 199999 and valid-block `lastTrans` was -1; appending that byte with rule M produced length 200128 and `lastTrans=199952`.
- **[inferred] Consequence:** the missing byte can represent 129 bytes of logical advancement, including an eager block. A cut waiting only for that block can become due *at the close*. “The loop finished, therefore nothing is due after close” does not follow; define that work as belonging to the next unit, or explicitly simulate the closing block. `LastByteProbe` never tests this decision.
- **[inferred] Required separation:** track physical appended bytes, logical record end (including any eager block), and publicly closed end. Take pacing, positions, statistics and next-record alignment must use the appropriate one. Writer-local pending reads need to cover `TransIterator` and `getTrans`, not just raw node reads; otherwise the missing last byte looks like damage.

### D2. Sync from the writer is a missed self-dependency

- **[read] Where:** `core/Db.java`, `executeLocked`, `sync`; `core/Trans.java`, `Listener`; `core/NodeStream.java`, `getAppendedEnd`.
- **[inferred] Case:** a transaction listener runs before maintenance and calls `sync(t.lastPos)`. Under (d), that position requires the unit's close, but the same thread must return from the listener to close it. Re-entering the Java write monitor does not wait for a future close; waiting explicitly deadlocks, while returning early falsely promises durability.
- **[inferred] Fix required:** move such callbacks after close, or explicitly refuse same-thread sync of an open unit. Synthesizing its pending byte for reads cannot make it durable. The study's unconditional rule “sync inside an open unit waits” is incomplete.

### D3. Tail removal crosses the storage and encryption contracts

- **[read] Where:** `stream/AppendOnlyStream.java`, length/append contract; `stream/FileStream.java`, `append`, `pretruncate`, `forceDirectory`; `stream/SalsaStream.java`, constructor, `append`, `read`; `storage/StorageManager.java`, `append`.
- **[ran] Split encryption:** `ExtraProbe` reproduced identical ciphertext for whole versus split appends in 12 selected layouts near a meta block. Splitting alone works; this does not test truncation or units.
- **[ran] Additional failure mechanism:** using a throwaway tail-trimmable stream, opened `SalsaStream` at physical EOF 100, trimmed its underlying stream to 40, then appended. Reading the new plaintext at 40 did not round-trip: the encryption cursor still represented the old EOF.
- **[inferred] Consequence:** deciding E in plaintext recovery and cutting later requires propagation/reset of encryption and buffering positions, not just a FileStream truncation. Even resetting the cursor leaves the study's acknowledged keystream-reuse problem when different plaintext replaces the discarded tail. Neither is solved by the split-append probe.
- **[inferred] Cross-file rule:** remove later files last-to-first, force directory removals, truncate/force the boundary file, and only then append replacement bytes; inject a crash after every persistence operation. Today's front-cut implementation is not evidence that this new tail-cut protocol works.

### D4. A tail-length bound does not establish that damage is discardable

- **[read] Where:** `storage/RecoverableStream.java`, `recover`, `checkLastTransSpos`, `fixLastTransactionIfNeeded`; `core/NodeStream.java`, `readRecordHeader`, `TransIterator.next`; `stream/AppendOnlyStream.java`, crash contract.
- **[inferred] Case:** an entirely present record with an impossible size or invalid marker must fail, not be reclassified as an incomplete unit and silently cut merely because the suffix fits the bound. A valid-looking 10-to-11 corruption is indistinguishable from an open unit without stronger integrity evidence; the existing prefix-interruption assumption must remain explicit.
- **[inferred] Recovery obligations:** distinguish malformed data from EOF truncation; restore the last valid block *below E*; keep its named closing record through front cuts; handle E exactly at a block boundary and crashes during tail deletion. These are new storage assumptions outside the existing Lean theorems.
- **[inferred] Backup consequence:** an uncoordinated file copy spanning removal and reuse of tail positions can combine the old suffix with new prefix bytes and fail to represent any stream prefix. A stopped, settled copy or a barrier excluding truncation/reuse is required; merely saying startup itself writes nothing does not protect a concurrent copy.

### D5. The stop problem is real; the proposed repair remains unbuilt

- **[read] Where:** `core/Db.java`, `stop`, `closeStorage`, `executeLocked`; `core/Reclaim.java`, `transactionCompleted`, `catchUp`.
- **[ran] Reproduction:** the original `StopProbe 1 20000 2000 30` again returned normally in 30/30 targeted calls and wrote maintenance in 0/30 after the hook called `stop()` following the user record.
- **[inferred] Consequence for (d):** retaining that behavior would acknowledge a transaction whose unit startup discards. Admitted-unit maintenance must bypass STOPPING refusal, including its reads, and `execute()` must return only after close. A failure before close must throw; a close followed by a caller-visible failure remains an ambiguous committed outcome.

### Shared proof and reproduction limits

- **[read] Lean:** `SIS/Algorithm.lean:step`, `SIS/Theorems.lean:T1_crash/T2_restart`, and `SIS/ReclaimTheorems.lean:T12_restartCut` concern given transaction lists, whole-record prefixes, and safe cuts with `PolicyCutOK`; they neither choose maintenance nor implement torn-byte recovery.
- **[inferred] Comparison:** (e) fits one abstract transaction per action, but must generalize `Contract/ReclaimSteps.lean:StepTx/StepOpOK` for user deletes/puts and prove mixed coverage. (d) fits boundaries within the same given list, but needs an additional byte-to-closed-unit recovery/acceptance bridge. (c) needs a deterministic, terminating due-loop policy preserved by recovery and cuts. None obtains the owner's full claim merely by citing T2 or estimating proof lines.
- **[ran] Study (e):** all six `OneRecordProbe` configurations reproduced the source logs exactly: seeds 1–6, respectively `(N,sd,keys,maxv,multi,node)` = `(5000,2000,200,3000,10,default)`, `(5000,2000,200,3000,60,default)`, `(5000,2000,20,3000,60,default)`, `(20000,20000,5000,300,10,default)`, `(10000,5000,2000,3000,10,8)`, `(3000,50000,200,30000,10,default)`; D2 throughout.
- **[ran] Correction:** largest hypothetical merged records were 38,088 / 51,416 / 38,880 / 36,944 / 38,400 / 333,408 bytes. The study's section 2 calls the first figure the six-workload maximum; that is false. These are sums of old separate records, not measured sizes or dirty-node bounds of a mixed implementation.
- **[ran] Study (d):** all three `UnitProbe` workloads reproduced its figures using seeds 1/2/3 and `(N,sd,keys,maxv)` = `(20000,2000,200,3000)`, `(20000,100000,10000,1000)`, `(20000,1000000,100000,100)`: maintenance after 1,643/885/215 commits, later-record meta blocks 74/57/14, zero due predicates after 60,000 calls. `LastByteProbe` reproduced 4,563/4,563 identical final layouts; `StopProbe` reproduced 30/30 as above.
- **[ran] (c) check:** original D2 `P2CrashProbe 22 300 2000 both` reproduced F3's final-action gap: 383/384 equal continuations for each of crash and stop. A throwaway `VariantCProbe` added catch-up and clock release after startup; it obtained 384/384 for each, with the same reference digest `8ce693555342fe87`.
- **[read] Limits of those runs:** neither A1 design was built, so no run proves its safety, P1, space bound or Lean refinement. The (c) wrapper tests startup completion, not the proposed production deletions or P7 repair; no full gate, Lean build, night, week or timing script was run.

## Verdict and first three tests

- **[inferred] Build (c).** It preserves separate records, existing transaction inspection, per-record limits and the storage contract; it has the smallest new failure surface. Put all due work inside P7 handling, complete it before startup returns, remove D1 and between-call holds, decide setter behavior explicitly, and make the after-row accounting durable/reconstructible rather than silently accepting the prototype's undercharge.
- **[inferred] (e) is a credible later simplification**, after fixing the empty-record classifier and proving guaranteed maintenance room, mixed coverage and cut ordering. Its apparent single-record simplicity currently moves complexity into admission, provenance and reclaim's contract. **(d) is my last choice:** it introduces tail rewriting, recovery, sync and encryption obligations to avoid bounded startup catch-up.
- **[inferred] Exact scope:** (c) and (e) retain today's aborted torn record, so continuation can be a function of the actual recovered stream and accepted actions, but cannot equal the uninterrupted byte stream from accepted actions alone while ignoring torn bytes. If that stronger equality at every byte is mandatory, neither qualifies as written; design a separately specified tail-atomic storage layer first, addressing (d)'s findings, rather than claiming the existing recovery does it.
- **[inferred] Test 1 — due-prefix closure:** exhaust every record boundary of commit/maintain/setter workloads, including the final action; repeatedly interrupt startup catch-up too. Compare bytes and decided cuts with the canonical completed prefix, check clock release and zero writes from a later refused action, then repeat after physical front cuts and with torn tails under the explicitly weaker torn-stream contract.
- **[inferred] Test 2 — P7 and stop:** inject failure/stop before mutation, after row/table mutation, during append, and after append before memory installation for B/S/P/C. Require either refusal with unchanged live state, a completed accepted prefix, or a failed database refusing reads until restart; verify stopped accepted values and idempotent recovery.
- **[inferred] Test 3 — reclaim safety and pace:** force old live values, overlapping puts/deletes and transformations, tiny reserves, lowered record limits and sustained large commits; verify historical/latest gets and transaction provenance before/after cuts and restart, exact recoverable charges, and a stated progress/kept-space bound. Run C-STEP/C-CUT on the resulting boundary traces before broader gates.
