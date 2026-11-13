028-05. Fix: the Core API names the transformations
===================================================

Status: done (2026-11-13). Kind: Fix. Frans: none.
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

2026-11-13. Done by an agent of coord-1113, in the commit "028-03, 028-05, 028-06: the write buffer, the transformations and
maintain() in the Javadoc (documentation only)" on branch 028-jdoc:
Db's "The Core API" now names `ValueTransformation` and
`KeyTransformation`, which `Trans.Builder`'s put() takes, and what a key
transformation uses: `Trans.kvs`, `Kv.getKey()` and `setKey()`,
`Trans.writeKeyHashes`, `Trans.tt` and `Keys.hash()`. Also
`KeyTransformation.transform()` now says that a transformation that
changes the key sets `trans.writeKeyHashes[index]` to `Keys.hash()` of
the new key, as the Pub's does (`RwEnvironmentImp.entryTransformation()`):
`Db.transformKeys()` does not compute it again, and `stmRecordKeys()`
records it for the conflicts. `java/before-commit.sh` printed `BEFORE COMMIT OK`.
