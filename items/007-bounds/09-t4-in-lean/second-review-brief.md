# Review: T4's and the cold start's definitions and assumptions in Lean (bergdb 007)

You review, read only, the trusted part of new Lean theorems about BergDB, an append-only key-value
database for Java with a Lean 4 model of its algorithms. Repository: the current directory (a clone of
main). Do not edit any file. Your final message is the report.

## What to review

The trusted definitions and assumptions that new theorems rest on, written today from prose:

- lean/SIS/BoundT4.lean (spAt, spIter, levelOf, onAccessPath, changeAt, RecordBound, RecordByDebt,
  DebtByChanges)
- lean/SIS/BoundT4Java.lean (DebtByChains, PtrBelow, DebtByChainsH, PtrHeightLe, ptrParents, ...)
- lean/SIS/BoundCold.lean (rerunReach, removedAt), lean/SIS/BoundColdDrop.lean (DropStep, DropRunOK)
- the statements: lean/SIS/BoundT4Theorems.lean, BoundT4JavaTheorems.lean, BoundColdTheorems.lean,
  BoundColdDTheorems.lean (and any Bound*Theorems file next to them)
- the examples checked by running: lean/SIS/BoundT4Example.lean, BoundT4JavaExample.lean,
  BoundColdDropExample.lean

Context: the prose they come from is items/007-bounds/01-startup-bound.md (007-01, sections 5 and 6;
note the dated note of 2026-11-13 in section 6) and items/007-bounds/03-plan.md (007-03, step 6).
items/007-bounds/09-t4-in-lean.md (007-09) is today's write-up; read it last, after forming your own
view. The existing model's assumptions (RunOK, A1 to A6', TREE as TreeRunOK, javaTest, exactTest,
lazyStartup, handleStartup, handleStartupPos) are in lean/SIS/*.lean; the Java code is in java/src
(bergdb.core: TransSeq, DbStarter, NodeCollection, StartupPos, IDirtyNodes; bergdb.storage).

## Questions, in order of value

1. Faithfulness: does each definition say what the prose says, no more and no less? Where it says
   less or more, quote both and say what differs.
2. Vacuity: could a theorem be true for a trivial reason, such as assumptions no realistic run
   meets, a quantifier over an empty set, a bound that is always true, or a definition that makes the
   conclusion hold by construction? The examples show some runs that meet RunOK and TREE; check
   whether they also meet each theorem's other premises.
3. Truth for Java: is each assumption true of what Java's code does? In particular RunOK's parts,
   TREE, DropStep (a change makes unreachable at most as many nodes as entries ...; the children of a
   node made unreachable stay reachable), ptrParents <= Q, virt = false where it appears, and that
   the model's lazy startup and its count of objects made match Java's reads. Give the class and
   method for each judgement.
4. Anything else a careful reviewer of a proof's trusted base would flag (a definition with an
   off-by-one, a time index that is shifted, a missing case).

## Rules

- Read only. Do not run `lake build` of the whole project (the machine is shared); `lake env lean
  FILE` of a single file is fine if you need to evaluate something.
- Be concrete: file and line, quote the Lean, quote the prose or the Java.
- If all is well on a point, one line saying so is enough.

## Report

At most about 40 lines, as a list: for each finding, the severity (wrong / unclear / fine), the file
and line, what is wrong or doubtful, and what you would change. End with one line per question 1 to 4:
your overall verdict.
