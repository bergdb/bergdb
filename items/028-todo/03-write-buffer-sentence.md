028-03. Fix: the package's write buffer sentence
================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: bergdb.pub's package.html, "Good to know", says each started
database holds a write buffer of 10 MB.

Why: since 026-07 it is 64 KiB, growing to 10 MB while it writes fast and
back after 2 idle seconds; a user sizes the heap for many databases from
it.

Frans: none.

Done when: the sentence says so, as
`DatabaseBuilder.startupDistanceInMb()` does, and names the cache budget
(a fifth of the heap by default, for each database) as what many databases
in one JVM must set.

First step: the sentence and `DatabaseBuilder`'s paragraph side by side.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-1).
