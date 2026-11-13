021-29. Fix: unit tests that wait with no timeout
=================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: two unit tests wait with no limit (024-35, finding 9; 006-17,
section 6.3, point 10; 024-01, TT4, "hangs first"):

* `java/src/bergdb/pubimp/PubTesterOutput.java`, lines 190, 198 and 201:
  `keyChanged.waitForEvent()`, `readDone.waitForEvent()`, `thread.join()`;
* `java/src/bergdb/pubimp/PubTester.java`, lines 788, 804 and 808:
  `modifiedKey1.waitForEvent()`, `getDone.waitForEvent()`, `thread.join()`.

Other test threads are joined with no limit too, such as
`PubTesterOutput.java:246`, `PubTester.java:1652` and `PubTester.java:4245`
(line numbers of 2026-11-13, main `b3f64bb1`).

Why: a fault in the code under test then hangs the test, and with it
before-commit.sh or a night step, instead of failing it with a message;
the night loses the step's time and the rest of its steps.

Frans: none.

Done when: every unbounded `waitForEvent()` and `join()` of a test
thread in the unit tests and f-tests has a limit (`waitForEvent(long)`
exists; `join(ms)` followed by an assertion that the thread has ended),
generous enough for a loaded machine (021-28), with a failure message
that names the wait; `java/before-commit.sh` prints `BEFORE COMMIT OK`.
An index build's `start().join()` is not a test thread's join and is
left as it is, unless it can hang (then a line here says so).

First step: grep `java/src` and `java/src-dev` test classes for
`waitForEvent()` and `.join()` with no argument, and list them here.


Log
---

2026-11-13. Registered by coord-1113 (Frans, 06:38: "Yes, register them"),
from coord-1112's handover (006-23, section 6, point 3) and 024-35, finding 9.
