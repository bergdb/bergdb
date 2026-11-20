# 030-35. Reclaim preserves users' values

Created 2026-11-20 by Frans Lundberg. Status: done.

Frans decided to close 030-33, finding F1, in the proof (2026-11-20):
strengthen reclaim's steps to copy the values they read, forbid other
user operations, and prove reads against the users' operations alone.
The former theorem established cut safety against all operations,
including maintenance writes; that reference could accept a wrong
maintenance value as the answer.


## 1. Result and top theorem

**`Contract.PE.pe_reclaim_user_reads_steps`**, in
`lean/contract/Contract/ReclaimValues.lean`: for every accepted history
PE writes from the empty tree, with reclaim's maintenance transactions
designated and meeting the local conditions below, iterations following
the strengthened step model, and the existing cut and reader premises,
reads after the run with cuts, handles, eviction and restarts give the
users' values at every lookup time retention keeps. The reference applies
the users' operations only; it excludes every designated maintenance
transaction, including every step of the iterations used for cuts.

The precise meaning of reads is `JUserReadsRight`:

* Every get of a key outside reclaim's reserved prefix agrees with the
  users-only reference, including absence after a user delete.
* Every scan whose range excludes that prefix agrees directly with the
  users-only reference, forward or backward, at every requested limit.
* For every scan range and raw Core limit, removing reserved rows from
  the result leaves a prefix of the users-only scan: the values are the
  users' values and no user key is skipped. Reserved rows may consume
  slots in the raw Core limit.
* Exhausting any scan range and removing reserved rows before taking a
  user limit gives exactly the users-only scan, for every limit. The
  proof supplies a finite exhaustion bound, the full map's size; the
  theorem needs no size bound as a premise.

The reserved prefix is `/#i/dreclaim/`. User keys here mean every key
outside that prefix; even other internal namespaces are protected. A raw
Core scan crossing the prefix can return reclaim's rows. Equality of
that raw result with a map containing no reserved rows would be false.

The top theorem retains PE's premises: accepted transactions, distinct
operation keys, `Cfg.Ok`, the top-base bound of 2^62, fewer than
2^48 - 1 transactions, and M at least 1. It retains the cut premises:
Java's still-dirty test and marking, policies that read no cut stream,
ordered cuts, the iteration's end no later than the first available
time, RC4's waits, and handle reads only at available times. The tree
and top must hold the recovered view (`HoldsView`, `TopFrom`), as in
030-25. Both record times and times between records are covered (`mid`).


## 2. The strengthened local model

`StepTx h c j out ops` now names the state immediately before the step,
after transaction j. Its old clauses remain, with a real row put in
place of an unspecified nonempty set of puts:

1. Every old key the scan met is put.
2. The transaction puts reclaim's current row, `-current.txt` under its
   prefix; the model fixes its key as `reclaimRow`.
3. Operation keys are distinct.
4. Each operation meets `StepOpOK`: it is the current-row put, or a put
   of an old key actually met by the scan, with the value that key had
   immediately before the step. There are no deletes.

This forbids extra user puts, puts of unscanned or non-old keys, changed
rewrite values and deletes. It also protects scanned internal keys other
than the current row. The row can replace its own rewrite and has an
arbitrary new value: it records progress. Its contents remain opaque in
this model. `reclaimKey` and `reclaimRow` use the compare-value encoding
of the public prefix and row name; `reclaimRow_reserved` proves that the
fixed row is inside that namespace.

`StepsFrom` supplies the actual step's j to `StepTx`. The scan, stop
rules, cursor chain, end key, cut bound, end-of-scan condition and
between-step user transactions are unchanged.

`IterationOK` is unchanged. Its purpose is coverage for cut safety:
every old key is written during the iteration, by a step or by the user.
A user's intervening put or delete must remain allowed. Value
preservation is proved separately for maintenance, then composed with
the existing cut proof; it is not asserted of an iteration's user
operations.


## 3. An independent reference and its proof

The history explicitly designates maintenance at zero-based transaction
indexes. `MaintenanceOK` requires each such transaction to be either:

* a step satisfying `StepTx` for its own pre-step scan; or
* a transaction whose operations all stay inside reclaim's namespace,
  such as its table, row or filler stores.

This covers maintenance between steps and unfinished iterations as well
as the iterations eventually used for cuts. `CutsMeetMaintenanceSteps`
additionally requires every step of each cut's witnessing iteration to
be designated maintenance. It gives the old `CutsMeetSteps` without
changing its cut conditions.

`userTransactions` replaces each maintenance transaction with an empty
transaction and keeps the other transactions' operations outside
reclaim's namespace. It preserves the history's length and times. In
particular, lookup time t still means the first t original transactions,
not the first t user transactions. Its `refMap` is built from those
operations alone, never from maintenance outputs or the final tree.

The proof has three parts:

1. `StepTx.put_value` extracts the pre-step value and the old scanned
   key; `StepTx.no_delete` forbids deletes. `StepTx.preserves_users`
   proves that applying a step changes no user-map entry: putting an
   existing value back into the sorted map changes nothing, and the
   current row is reserved. Namespace-only stores preserve the same
   projection.
2. `user_contents_at` inducts over every transaction of the history.
   At maintenance times the user map stays fixed; at user times the
   actual user puts and deletes are applied. `user_refMap` consequently
   equates the old full reference restricted to user keys with the
   independent reference, at every history time. Neither equality is
   assumed in `MaintenanceOK` or in the top theorem.
3. `JReadsRight.users` transfers gets and scans using that equality.
   `reclaim_user_reads_steps` composes it with the existing reclaim
   read theorem; `PE.pe_reclaim_user_reads_steps` supplies PE's proved
   writer contract, K-LEVEL and VAL-NEW.

The example remains a history PE accepts: four initial values, a
namespace-only store, two steps with the real current-row key, and
between the steps a user insert, value change and delete. Its user
reference omits all three maintenance transactions. The preservation
theorem is instantiated at every time and the final user map is checked.
Separate kernel-checked regressions reject a wrong value, an extra put,
an extra delete and a missing row (`ValuesExample`).


## 4. Pinned statements and compatibility

Frans authorized the statement changes for this correction (2026-11-20).
The changed existing pinned declarations are:

* `StepTx`: adds j and the pre-step value condition, restricts every
  operation to an old scanned put or the fixed row, and requires the row.
* `StepsFrom`: passes each step's own j to that stronger premise.
* `step_covers`: its `StepTx` premise now includes the step's j.
* `stepsFrom_lastTx`: its resulting `StepTx` includes the last step's j.

These existing statements have unchanged type text but inherit the
stronger step premise through those definitions; their conclusions are
unchanged:

* `StepsOK`: its `StepsFrom` clause uses the stronger step contract.
* `CutsMeetSteps`: its iterations use that stronger `StepsOK`.
* `stepsFrom_covers`: coverage from stronger local steps.
* `stepsFrom_bounds`: bounds from the stronger step sequence.
* `StepsOK.ends`: first and last bounds for stronger iterations.
* `iterationOK_of_stepsOK`: the original coverage conclusion from
  stronger iterations, for every allowed first time s.
* `iterationOK_steps`: the same coverage from first to last step.
* `stepsOK_live`: the same nonempty end state, now witnessed by the
  required current row rather than an arbitrary put.
* `cutsMeetIter_of_steps`: the same cut-iteration conclusion from
  stronger steps.
* `reclaim_java_reads_steps`: the same all-operations read conclusion
  from stronger steps.
* `PE.pe_reclaim_reads_steps`: the same PE all-operations read conclusion
  from stronger steps.

No declaration of `ReclaimTree.lean` or `RecoverJava.lean` changed.
In particular, `IterationOK`, `CutsMeetIter`, `JReadsRight` and the
030-24 theorems keep their statements. The new user-read theorem is
added beside them. All existing theorems still build.

New pinned definitions are `reclaimKey`, `reclaimRow`, `userKey`,
`StepOpOK`, `MaintenanceOK`, `userTransactions`, `JUserReadsRight` and
`CutsMeetMaintenanceSteps`. The new main theorems are the ten non-example
entries added to `Axioms.lean`: `reclaimRow_reserved`,
`StepTx.put_value`, `StepTx.no_delete`, `StepTx.preserves_users`,
`user_contents_at`, `user_refMap`, `JReadsRight.users`,
`CutsMeetMaintenanceSteps.cutsMeetSteps`, `reclaim_user_reads_steps` and
`PE.pe_reclaim_user_reads_steps`. Seven example entries check the
positive instance and the rejections. `statements.pin` is regenerated
with `pin.sh` in this change, after the build.

The pin-file changes are the hashes of `Axioms.lean` and
`ReclaimSteps.lean`, the new `ReclaimValues.lean`, and the unchanged
`Proof/Good.lean`, newly in the statements' closure because the new
step-preservation theorem names its sorted-map relation `KvLt`.


## 5. Scope and remaining links

The maintenance-value gap of 030-33, F1, is closed in the proof. There is
no remaining Lean preservation obligation and no user-reference equality
left as a premise. Java's trace checker is a separate change; this item
does not establish that it checks the strengthened relation. Java's
transaction designations, namespace encoding, exact step operations,
cursor and row interpretation, cut arithmetic, writer and reader links
to the model remain tested links or explicit input premises.

The proof uses the contract's abstract `Nat` values. It does not remove
030-33, F2: Java's trace comparison represents byte values by
fingerprints. Exact byte-array preservation in Java, the row's serialized
cursor fields, threads, performance and resource bounds are not proved
here. No Java file or file under `lean/Check/` changed.


## 6. Sentences for 030-26, section 2.5

030-26 is unchanged here, as requested for this work. Its section 2.5
should replace its step and read claims with these sentences:

> Each step puts every old key its scan met, with the value the key had
> immediately before the step, and puts its current row under reclaim's
> reserved prefix. It puts no other key and deletes none; the row may
> replace its own rewrite. The last step's scan reaches the end.
>
> For every accepted history PE writes, with all reclaim maintenance
> transactions meeting this step model or writing only reclaim's reserved
> namespace, and with the existing cut and reader premises, reads after
> cuts, handles, eviction and restarts agree with the reference made from
> the users' operations alone at every retained lookup time:
> `Contract.PE.pe_reclaim_user_reads_steps` (030-35). Maintenance
> transactions contribute no operations to that reference and do not
> change its lookup times. Gets and scans in user ranges agree directly,
> including scan limits. For ranges crossing reclaim's namespace, raw
> Core scans can also return its rows; removing those rows gives a prefix
> of the user reference, and exhausting the range before applying the
> user limit gives the complete users-only scan.


## 7. Validation

From `bf9b3428`, with the changes left uncommitted (2026-11-20):

```text
lake build
Build completed successfully (3361 jobs).
sh lean/contract/pin.sh
pin.sh: 114 files pinned in lean/contract/statements.pin
sh lean/contract/gate.sh
1. lake build passes
2. no sorry, admit, native_decide or axiom
3. the standard axioms only (215 theorems)
5. the statements pinned: 93 files of the main theorems' closure, 114 pinned
GATE OK
sh lean/contract/pins.sh
the pins' own test: a changed and a removed pinned file fail, as they must
114 files have their pinned hashes (lean/contract/statements.pin)
PINS OK
```

The new top theorem's axiom line is:

```text
'Contract.PE.pe_reclaim_user_reads_steps' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`git diff --check` passes. Java, `lean/Check/`, `ReclaimTree.lean`,
`RecoverJava.lean` and 030-26 have no diff. The seven source changes are
`Contract.lean`, `Axioms.lean`, `ReclaimSteps.lean`,
`ReclaimStepsExample.lean`, the new `ReclaimValues.lean` and
`ReclaimValuesExample.lean`, and `statements.pin`, all under
`lean/contract/`. This subitem and 030's Files list complete the change.


## State

2026-11-20. **Done.** The strengthened model, users-only reference,
preservation proof, top theorem and examples build; GATE OK, the standard
axioms only, and PINS OK. The separate Java checker link and the proposed
030-26 wording remain as described in sections 5 and 6.


## Log

2026-11-20. Created the subitem; strengthened the step model and proved
preservation of the users' reference at every time and reads after cuts.

2026-11-20. Completed the build, regenerated the pins, and passed the
gate and independent pin check. Status changed to done. No commit.
