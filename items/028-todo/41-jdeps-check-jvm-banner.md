028-41. Fix: build.sh's jdeps check and the JVM's "Picked up" line
==================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: `java/build.sh`'s check 2 of the release jar writes both outputs
of `jdeps --missing-deps` to `build/release-jar/jdeps.txt` and fails the
build if that file is not empty. With `JAVA_TOOL_OPTIONS` set (or
`_JAVA_OPTIONS`), the JVM that runs jdeps prints its own line on standard
error, `Picked up JAVA_TOOL_OPTIONS: -Xmx1g`, and the build fails with
"it uses classes that it does not hold (jdeps --missing-deps)", though no
class is missing. Found by 026-26 (S4-B1), on `main` at `bdf7c1ba` and on
release 2026.5 (`3611130c`), 3 runs of 3 on each.

Why: a valid environment, such as a heap cap for every JVM of a build on
a shared machine, makes the build fail falsely. A build-script fault, not
a fault of the database: no released jar is affected, so it is not in
033's register of released bugs.

Frans: none.

Done when: `JAVA_TOOL_OPTIONS=-Xmx1g sh java/build.sh` builds; a use of
a missing class still fails the check; `java/before-commit.sh` BEFORE
COMMIT OK.

First step: reproduce with `JAVA_TOOL_OPTIONS=-Xmx1g sh java/build.sh`.


Result
------

`java/build.sh` writes jdeps's output to `build/release-jar/jdeps-out.txt`
and drops the JVM's lines `Picked up NAME: ...` and `NOTE: Picked up
NAME: ...` from it into `jdeps.txt`, which the check reads as before.
Every other line, a missing class among them, still fails the build. The
comment of check 2 cites this entry.

On the branch `026-26-app-hunt` (2026-11-20):

* `JAVA_TOOL_OPTIONS=-Xmx1g sh java/build.sh`: the build of `main`
  (591251a5) fails as found; with the fix it builds, `jdeps-out.txt`
  holds the banner alone and `jdeps.txt` is empty. The same with
  `_JAVA_OPTIONS=-Xmx1g`.
* `sh java/build.sh` with neither set: builds, as before.
* The filter on a sample of the three banner forms and a line of jdeps
  for a missing class (`bergdb.pub.Foo -> org.example.Missing not
  found`): only the last line is kept.
* `java/before-commit.sh`: BEFORE COMMIT OK (63 s).

The hunt's reproduction, `BuildOptionsRepro.java`, asserts that the build
fails, so it was not landed; the command above is the reproduction.


Log
---

2026-11-20. Registered by an agent of coord-1120, from 026-26's S4-B1.

2026-11-20. Done by the same agent, on the branch `026-26-app-hunt`.
