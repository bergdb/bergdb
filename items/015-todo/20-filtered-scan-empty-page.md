015-20. Fix: a filtered scan takes an empty page for the end of its range
=========================================================================

Status: done. Kind: Fix. Created 2026-11-03 by
Frans Lundberg.

For 2026.2: a wrong answer in normal use (016-06, section 6).

What: A typed primary scan (`usePrimary`) silently leaves out every later object when one page of about 100 entries holds no object (100 or more other entries in the directory). A wrong answer, through the Pub API in normal use.

Source: review R3, R3-F12 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F12), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F12, made a test.


State
-----

2026-11-03, 20:30: done; reviewed (no fault) and committed after the
combined gate. Earlier:

2026-11-03, 19:53: the fix, its test and the gate done in the clone
`/Users/f/fl/bench/016/015-20/repo` (from `c657764`); handed off for
review (`/Users/f/fl/bench/016/015-20/handoff/`). Open: the review, the
combined gate, the commit in `main`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 19:46 to 19:53, in `/Users/f/fl/bench/016/015-20/repo` from
`main` at `c657764`: the fix.

* **The cause** (as R3-F12 and verify-1 say): `UseIndexBuilderImp`'s
  `IterStopCondition` ends a page after 100 entries within the prefix
  (or 50 MB, or 1 s), filtered ones included; when the last of them is
  not an object, the page ends without it, and a page of only filtered
  entries is empty. `IndexIterator.hasNext` took an empty page for the
  end, and the next page's start key came only from returned entries.
* **The fix**, in `UseIndexBuilderImp`: the stop condition records the
  key of the last entry it visited within the prefix (`lastKey`) and
  whether a limit ended the page (`endedAtLimit`). The next page starts
  after `lastKey`, returned or filtered out; `hasNext` takes another page
  while a page is empty and a limit ended it, and ends only on an empty
  page that the end of the prefix or of the database ended (also when
  `Dag.getMany` finds no root and calls neither `handleKvt` nor `eod`).
  The later pages use the first page's actual lookup time, as before.
  Each page visits at least one entry, so the loop advances. A secondary
  index filters nothing, so its pages are as before.
* **The test**: `PubTesterPrimary.testFilteredPages` (unit): 100 Strings
  then an object in `/a/`; an object, 250 Strings and an object in `/b/`,
  forward, backward and with `kvs()`. On the code before the fix it fails
  with `Expected '[z]', got '[]'`; with it, it passes. verify-1's
  `FilteredScanVariants` gives the expected count in all five of its
  cases with the fix.
* **Gate**: `BEFORE COMMIT OK (113 s)`, 19:51:53. No stream byte and no
  Pub API signature changes.

2026-11-03, 20:30, by the coordinator (016-05, H5): reviewed by an agent
that did not write it (`/Users/f/fl/bench/016/015-20/handoff/review-findings.md`):
no fault; the new tests fail on the parent and pass on the change; the
mutants are caught. Its nits:
* nit: the byte and time limits of a page (50 MB, 1 s) take the same path
  and have no test (R3-T12 asks for one).
Gated with 015-20, 015-22 and 015-21 together on `main` (the gate line in
the commit).
