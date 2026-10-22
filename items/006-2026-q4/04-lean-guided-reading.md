006-04 Guided reading of the Lean model
=======================================

Created 2026-10-22 by Frans Lundberg. Plan written by Claude (Opus 5.5,
Claude Code) at Frans's request.

Frans reads the trusted part of [lean/](../../lean/README.md): the
definitions and the theorem statements, against
[docs/sis-model.md](../../docs/sis-model.md). Claude guides, one session of
about an hour at a time, and teaches the Lean syntax as it comes up. The
proofs (`lean/SIS/Proof/`, about 40,000 lines) are not read: Lean has
checked them.

The goal is that Frans can say, for each definition and statement, whether
it says what sis-model.md says. That check is what makes the proofs mean
something: Lean proves that the statements follow from the definitions, but
only a reader can check that they are the right definitions and statements.

Background: F1-011 in the f1 repo (learning Lean). The general route,
Theorem Proving in Lean and the Natural Number Game, teaches how to write
proofs, which Frans does not need here, and would take too long.


What is read
============

The core, for T1 and T2: about 840 lines in six files. The lean/README.md
table "What to read" maps each file to its sections of sis-model.md.

| Session | sis-model.md | Lean | Lean syntax met on the way |
|---|---|---|---|
| 1 | 2, 3.1 to 3.3 | SIS/Basic.lean | `notation`, `def`, `structure`, `abbrev`, `List`, `Option`, dot notation, implicit arguments `{V : Type}`, `deriving` |
| 2 | 4, 5 | SIS/Stream.lean | pattern matching, recursive definitions, Bool-valued tests and `decide` |
| 3 | 6.1, 6.3 | SIS/Algorithm.lean | functions as fields (`Algo`), `let`, `run` as a fold over the transactions |
| 4 | 6.2, 3.4 | SIS/Startup.lean, SIS/Assumptions.lean | `Prop`-valued definitions (`SpecOK`, `StepOK`, `RunOK`), `∀`, `∃`, `inductive` predicates |
| 5 | 9 | SIS/Theorems.lean | reading a theorem: parameters, hypotheses, conclusion; `let` in a statement; `#print axioms` |

Later, if wanted: section 15 against SIS/Phys.lean, SIS/Evict.lean,
SIS/Reclaim.lean and their theorem files, SIS/PhysTheorems.lean and
SIS/ReclaimTheorems.lean (about 1,700 lines more).

Optional throughout: the example files (SIS/Example.lean and the other
`*Example.lean`) run the definitions on small cases with `#eval` and
`#guard`. They are not trusted, but they show what a definition does.


How a session goes
==================

1. Frans reads the sis-model.md sections on paper (printed 2026-10-22).
2. The Lean file side by side, in VS Code with the Infoview. Claude explains
   each definition: what it says in sis-model.md terms, and the Lean syntax
   it uses. Frans can try `#check`, `#eval` and `#print` in a scratch file.
3. For each definition, the questions:
   * Does it say what the text says? Anything in the text that the Lean
     lacks, or anything the Lean adds?
   * Where the Lean chooses a representation (node ids as `Nat`, P as a
     list of pairs, a history as a list of entries), does the choice lose
     anything?
4. Findings go into the log below. A finding that needs a fix in `lean/` or
   `docs/` becomes an entry in item 005.


What to check in the theorems
=============================

Session 5 and the end of session 4.

* The conclusion: is it the claim of sis-model.md section 9? For example,
  `T1_recovery` says that startup from the run's stream gives a P
  equivalent to the run's P at every time, and the same D.
* The hypotheses: are they the assumptions of section 3.4, and no more?
  A hypothesis that can never hold makes a theorem empty. `RunOK` is the
  main one; `hst` restricts the still-dirty test to BergDB's (or the exact
  test with a written root).
* That the hypotheses can hold: the examples check them on concrete runs
  with `runOKB`, a Bool version of `RunOK` (SIS/Example.lean). `runOKB` is
  not proved equal to `RunOK`, so this is evidence, not proof; compare the
  two by reading.
* No `sorry`: `#print axioms` on each theorem shows only Lean's standard
  axioms (lean/README.md, "Build and run").


Log
===

2026-10-22. Created, with the plan above. sis-model.md printed (8 pages,
CUPS job Brother_Bonjour-103; the printer was not found at first). First
session planned for the morning of 2026-10-23.
