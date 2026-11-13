028-05. Fix: the Core API names the transformations
===================================================

Status: open. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: Db's "The Core API" does not list `ValueTransformation` and
`KeyTransformation`, nor what `KeyTransformation.transform()` must use
(`Trans.kvs`, `Kv.getKey()` and `setKey()`, `Trans.writeKeyHashes`,
`Keys.hash()`).

Why: by its last sentence they are internal, though 026-06 changed them as
Core API.

Frans: none.

Done when: the list names them.

First step: Db's paragraph and KeyTransformation's.


Log
---

2026-11-13. Registered by coord-1113, from 026-13, section 5 (U13-6).
