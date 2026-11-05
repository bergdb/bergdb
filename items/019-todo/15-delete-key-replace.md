019-15. Fix: with key replace enabled, a delete's key is not replaced
====================================================================

Status: waiting. Kind: Fix. Frans: decision.
Created 2026-11-05 by Frans Lundberg.

What: `Connection.setEnableKeyReplace(true)` makes a transaction replace
`${transactionTime}` in "a database key" by its transaction time
(`Connection`'s Javadoc: "occurrences of the string "${transactionTime}"
in a database key will be replaced by the the unique transactionTime of
the transaction when it is executed"). A put's key is replaced; a
delete's is not. `RwEnvironmentImp.delete` makes its `MapKey` without
the key transformation (`setKv(new MapKey(..., null), null)`), and for
an object key (no suffix) it puts an `ObjectInfo` with the key as
written into `objectOps`; `RwEnvironmentImp.put(String, Object)` gives
its `MapKey` `getKeyTransformation(ikey)`. Every delete goes there:
`Connection.delete`, `WBuilder.delete` and `RwEnvironment.delete`.

So, with key replace enabled:

* `c.delete("/r/${transactionTime}")` deletes the key
  `/r/${transactionTime}` as written, if it exists (a put with key
  replace disabled wrote it), where the Javadoc says it deletes
  `/r/000000000001234567` (that transaction's time), which cannot exist;
* `transactionInfo().kvs()` of such a transaction lists the delete with
  the key as written;
* a put and a delete of `/r/${transactionTime}` in one transaction: the
  last call wins, on the key as written (015-40's `MapKey` equality), so
  the put is lost and the delete is of the key as written; a put and then
  a delete of a key without the placeholder gives the same "no entry".

Shown by a probe (2026-11-05, on `main`, 45cfb4f):

```text
put with replace: replaced; literal still literal
delete with replace: literal key now null
w delete with replace: literal key now null
```

Why: found by harness 6.7, the Pub API's promises (018-04), the night
006-12: with nothing skipped (`-Dbergdb.promise.skip=none`), seed 3,
step 4493:

```text
c1.transactionInfo(), expected the transaction at 245540, its keys (the reference's KVs
  [/c=..., /d/f=..., /r/000000000000245540=(delete), /v.bin=...]): expected
  '[/c, /d/f, /v.bin]', got '[/c, /d/f, /r/${transactionTime}, /v.bi...'
```

(The expected keys leave out a delete of a key that had no entry, which
`kvs()` may leave out: 018-04, question Q4.) In 2026.2 and 2026.1 too, by
reading: the delete has had no transformation since key replace was
written; 015-40 (2026-11-05) states it ("the delete's MapKey, which has
no transformation").

Frans: decision. The options:

* **(a) A delete's key is replaced too, as the Javadoc says.**
  `RwEnvironmentImp.delete` gives its `MapKey` the key transformation
  when key replace is on, and the object-key path does the same: the
  `objectOps` entry is turned into a delete whose key is transformed in
  `createTrans`, as a put's is. A delete with `${transactionTime}` then
  deletes a key that cannot exist (the time is new), so it has no effect
  but its KV in the transaction, as a delete of a missing key. A workload
  that deletes such a key with key replace on writes other bytes (the
  replaced key); no other workload changes. About 10 lines and a test;
  the harness's SKIP line goes.
* **(b) The Javadoc says that only a put's key is replaced.** A
  sentence in `Connection.setEnableKeyReplace`: "A delete's key is taken
  as written: it is not replaced." No code change; the harness's
  reference takes (b) as the promise, and its SKIP line goes.

Recommendation: (a). One rule for every key of a transaction, which is
what the Javadoc says now and what a user who reads it expects; a delete
that names `${transactionTime}` is then harmless. With (b), a delete and
a put of the same placeholder key in one transaction act on two keys,
which is harder to explain.

Done when: Frans has chosen; for (a), a test of the three deletes
(`Connection`, `WBuilder`, `RwEnvironment`), on a key with and without a
suffix, that fails before the fix and passes after it, the SKIP line of
`PubPromiseTester` removed, and `before-commit.sh`; for (b), the
Javadoc, the reference changed and the SKIP line removed.

First step: Frans's decision.


Log
---

2026-11-05. Registered by harness 6.7's agent of the night 006-12
(018-04). Waiting for Frans's decision: a change of what a delete does
under key replace, and of the bytes it writes.
