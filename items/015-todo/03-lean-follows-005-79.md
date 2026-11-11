015-03. Implement: Lean follows 005-79's integer take
=====================================================

Status: open. Kind: Implement. Created 2026-11-03 by Frans Lundberg.

After release 2026.2, optional. Lean is a tool, not a release artifact
(Frans, 2026-11-03, 15:31, 016-01's D7).

What: after 005-79's Part B, Lean's `javaTake`, TakeCheck's 300 numbers and
`BoundExample.lean`'s bits describe the old double rule of the take. They
stay true of Lean's `Float` functions, but no longer of Java's take. Bring
them to the fixed-point rule, and `share` and `dither` into integers, as
005-79's step 8 describes; or keep lean/README.md's sentence that says so.

Why: the trace conformance of `level2.sh` to `level4.sh` follows by itself
(the checker takes each record's sp from the trace), so nothing fails; but
the model's description of Java's take is out of date.

Done when: `lake build` is clean with no sorry and no new axiom, and
TakeCheck compares Lean's integer take with Java's.

First step: 005-79, "Plan for 2026.2", step 8.

Found 2026-11-03 in 005-79's plan.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:35, by the coordinator: `lean/`'s `Bound.lean` (line 133)
and `BoundExample.lean` (line 83) name `TransSeq.dither`, which 005-79
removed; 007-08's `TakeCheck.java` calls it (015-19).

2026-11-07, by agent f13 of coord-1107 (021-03): when this entry is done
and 007-08's `TakeCheck.java` compiles against `main` again, TakeCheck
joins 021-03's step, `java/stress/lean-tests.sh` (a step of
`java/night.sh`), if it takes a few minutes or less.

2026-11-11, done by 024-09 (section 5.2), on `main` since `379d8acf`
(Frans, 11:05, on closing it when the branch lands: "yes"):
`lean/SIS/Bound.lean` has the take in integers (`shareFp`, `ditherFp`
and Java's test in `javaPace`), `BoundExample.lean`'s `#guard`s are
Java's numbers, and `java/stress/TakeCheck.java` (015-19) compiles in
the build and runs as `TakeCheck check` in `level2.sh`, step 7: Java's
take on 300 cases against the same numbers as Lean's, so a change of the
arithmetic on either side fails `level2.sh`. Not compared: the take
inside a traced run; C-S still takes each record's startup pos from
Java. TakeCheck is in `level2.sh`, not in `lean-tests.sh` as the note
above proposed.

