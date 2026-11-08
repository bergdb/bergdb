021-09. Fix: `PubKeys.udir2idir` accepts directories that are not well-formed
=============================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-08 by Frans Lundberg.

What: `PubKeys.udir2idir` accepts a user directory that does not start
with '/' or that holds an empty part, such as "p/" and "/p//". The callers
that need a well-formed directory check it themselves: the primary scan's
`dir()` since 020-10's step P1 (ae68938), the index definition since step
I0 (7aca256), and `IndexBuilder.dir()` in step I2. Found by the agent of
020-10's step I0 (coord-1108's night of 2026-11-08), from the code.

Why: one rule for what a directory is, in one place, so that no caller
takes a directory that another refuses (020-01's principle of one
promise per feature).

Done when: `udir2idir` refuses such directories (`IllegalArgumentException`
naming the rule), every caller relies on it, a test of the cases;
`BEFORE COMMIT OK`; a line in `releases/next.md`.


Log
---

2026-11-08. Registered by coord-1108 from a finding of the agent of
020-10's step I0.

2026-11-08. Done by the agent of 020-10's step I0 (coord-1108's night,
006-15).

* `PubKeys.udir2idir` refuses a directory that does not start with '/'
  ("udir must start with '/'") and one with "//" anywhere ("udir cannot
  contain \"//\""), before it converts; until now nothing checked the
  start, and its loop missed a "//" at the end. The root "/" stays a
  directory.
* Every caller relies on it: `IndexBuilderImp.dir` (unchanged: it called
  it already, and now refuses "p/" and "/p//"), `UsePrimaryBuilderImp.dir`
  (its own two checks, from step P1, removed) and `IndexDefinition`'s
  `dir` (its own check, from step I0, removed). The callers were found
  with grep over `src`, `src-dev`, `src-icu` and `stress`. No literal
  directory given to a `dir()` call breaks the rule but the Javadoc
  example of `IndexBuilder`, `dir("employees/")`, now "/employees/", with
  its `@throws` line (two lines of step I2's file).
* Tests: `PubKeys.testUdir2idirRefusesBadDirs` with the new cases
  ("a/" was taken before), and `testDirCallersRefuseBadDirs`: the index
  builder, the primary scan and an index's definition refuse "p/",
  "a/b/", "//", "/p//" and "/p//q/", and take "/" (the index builder
  took "p/" before).
* `releases/next.md`: left to the coordinator (the night's rule).

`BEFORE COMMIT OK (123 s)` (2026-11-08; 1329 unit tests, 87 f-tests). The
run before failed once in the Core's `EvictionAccountingTester`
(`testAccounting`, seed 2, batch 12: the audit's INV-SLOT), which passed
three times alone and in the next gate; reported to the coordinator, not
this entry's.
