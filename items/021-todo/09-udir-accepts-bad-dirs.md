021-09. Fix: `PubKeys.udir2idir` accepts directories that are not well-formed
=============================================================================

Status: open. Kind: Fix. Frans: none.
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
