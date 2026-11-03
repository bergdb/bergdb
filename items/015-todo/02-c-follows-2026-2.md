015-02. Implement: the C clone follows 2026.2's Java changes
============================================================

Status: open. Kind: Implement. Created 2026-11-03 by Frans Lundberg.

After release 2026.2. Frans, 2026-11-03, 15:31 (016-01, D7): "The C code
does not need to be updated for 2026.2 in this work. Only Java code will be
included in the release." So the C clone (012) does not follow the
release's changes, and its cross tests against Java differ where Java's
bytes changed.

What: port to the C clone the Java changes of 2026.2 that C has a
counterpart for:

* 005-79's integer take (Part B changes the take's bytes, so C's
  `cross.sh` fails until C follows; 005-79, "Plan for 2026.2", step 9);
* 005-69's `SystemClock` promise;
* 005-78's retain duration in the stream, if Frans chooses a form.

Why: the C clone is a second implementation of the Core, compared byte for
byte with Java (012); it only checks Java while it writes the same bytes.

Done when: C's own tests and its cross tests against Java pass on the
Java of the day.

First step: list the Java commits since `release-2026.1` that change the
Core's bytes or its promises, against 012's last cross run.

Found 2026-11-03 in the plans of 005-79 and 005-69 (016-05).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:35, by the coordinator: C's cross-test generator
`c/test/cross/java/Vectors.java` calls `TransSeq.dither`, which 005-79
removed, so it no longer compiles against `main` (015-19).
