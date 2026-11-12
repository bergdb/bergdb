# 024-37. CA3: the Core refuses a caller's writes at its own keys

Created 2026-11-12 by Frans Lundberg. Status: done on the branch
`ca3-core-keys`, head `9b3fd89d` (not on `main`); gated (section 5).

Frans, 2026-11-12, 14:34: "CA3, as recommended." CA3 (024-01, section
5.3; 020-11, section 11; 022-06-2, U2-8; 024-35, finding 2): a Core put
of seven bytes at `/#i/dreclaim/-settings.txt` was taken, and after it
every start failed with `InternalDataException`: the database never
opened again. By 010-04, R5 (the Core API never destroys the KV store: a
caller's mistake is refused with an exception and the database goes on)
that is a bug. The recommendation: the Core refuses a caller's puts and
deletes at the keys it writes itself; its own writes pass.

Done by the agent "ca3" of the day's coordinator, in its own clone.


## 1. In short

* **Refused**: the key `/#i/-dummy`, and reclaim's directory
  `/#i/dreclaim/` with every key under it (and the directory key
  itself). Nothing else: the Pub API's keys under `/#i/` (`/#i/didef/`,
  `/#i/dient/`, `/#i/didel/`, `/#i/dii/`) are written as before.
* **By whom, when, with what**: the public `Trans.Builder` calls that
  take a key (`put` and `delete` in each form, also a put with a key
  transformation, by its key as written) refuse it at the call with
  `IllegalArgumentException`, which spoils the builder, as a key over
  L2 does. `Db.execute()` refuses, before the go point, with a
  `DbException`: a KV at such a key that the Core's own calls did not
  make (`putLongKey()`, `deleteLongKey()`, a `Kv` set in `t.kvs` by
  hand), in `checkSize()` before the write lock; and a key that a key
  transformation gives, in `Db.transformKeys`, where the transformed
  keys get their keys as written back (as for L2).
* **The Core's own writes pass** by package-private builder calls,
  `putCore()` and `deleteCore()`, which mark the `Kv` (`Kv.coreWrite`,
  package-private, so no caller can set it); reclaim's internal
  transactions (`Trans.isInternal`) are not checked at all, since a step
  copies the Core's keys as any live KV with `putLongKey()`.
* **Reads** of the Core's keys are allowed, as before.
* **Tests**: `DbTesterCoreKeys` (new, 2 tests); two existing tests
  changed in their own commit (section 4).


## 2. The keys the Core writes itself

Found by a grep of `java/src` for `/#`, `INTERNAL_PREFIX`, `dreclaim`
and `DUMMY_KEY` (the `bergdb.core`, `storage`, `stream` and `dag`
packages):

| Key                          | Written by                                          |
|------------------------------|-----------------------------------------------------|
| `/#i/-dummy`                 | `Db.setStartupDistance()`, 200 kB, stays live       |
| `/#i/dreclaim/-settings.txt` | `Reclaim.setSettings()` (retain, fraction)          |
| `/#i/dreclaim/-table.txt`    | `Reclaim.storeTable()`                              |
| `/#i/dreclaim/-current.txt`  | each reclaim step (its row, a value transformation) |
| `/#i/dreclaim/-fill.txt`     | `maintain()`'s filler, put and deleted (024-32)     |

A start reads the settings, the table and the row and refuses what does
not parse (`InternalDataException`); a record with a KV under
`/#i/dreclaim/` is taken for one of reclaim's (005-42; 021-17). So the
whole directory is reserved, not only today's four files: a later
release may add a file there. The dummy is reserved as the one key, not
`/#i/-` as a prefix: no start reads it, but a delete of it changes what
reclaim copies, and the Core writes nothing else directly in `/#i/`.

The test of a key, `Trans.coreKey(long[])`: first `Trans.ownKey()`
(the key starts with 01 25, the bkey of `/#`; one compare of the first
segment, so a user's key costs nothing more), then equal to
`DbConstants.DUMMY_KEY`, equal to `Reclaim.KEY_PREFIX_SKEY`, or with it
as a byte prefix (`Keys.isPrefix`).


## 3. The rule and how it is checked

What: a put or a delete at one of the keys of section 2, asked by a
caller of the Core API, is refused before anything is written, and the
database goes on (010-04, R5).

When and by whom:

1. At the `Trans.Builder` call (`put(byte[], byte[])`, `put(long[],
   byte[])`, `put(long[], KeyTransformation, byte[],
   ValueTransformation)`, `put(String, ...)`, `delete(...)`):
   `checkNotCoreKey()` after the L2 check, with
   `IllegalArgumentException`. Why this type: it is what the Core API
   gives for a bad key argument (a null key, no segment, a key over L2;
   020-27, Q2), and the builder's refusal rule (024-26, U26-5) applies
   to it unchanged.
2. At `Db.execute()`, for a transaction that is not reclaim's:
   `Db.checkCoreKeys()` in `checkSize()` (keys as written) and a loop in
   `Db.transformKeys()` (keys as transformed), with `DbException`. Why
   this type: these are refusals of a transaction at the commit, as L1,
   L3 and a transformed key over L2 are; the caller may not have passed a
   bad argument to any call (a key transformation decides the key at the
   commit).

The internal path: `putCore()` and `deleteCore()` (package-private in
`Trans.Builder`) skip step 1 and mark the `Kv`, which step 2 lets pass;
reclaim's transactions skip step 2 by `isInternal`. Users: `Db`'s dummy
in `setStartupDistance()` (a transaction that is not internal, so the
mark matters), `Reclaim`'s settings, table, row and filler.

Javadoc: `Db`'s class Javadoc ("Keys and the layers above", a new
paragraph "The Core's own keys are refused"), `Db.execute()`'s
`DbException`, `Trans.Builder`'s class Javadoc and each call's Throws,
and `Connection.transactionInfo()` (a fake reclaim record now comes only
from a damaged stream). `releases/next.md`: Core API and Known issues.


## 4. Tests

New, `bergdb.core.DbTesterCoreKeys` (unit):

* `testCallersWritesRefused`: after `setStartupDistance()` and
  `setRetainDuration()` (the Core's own writes pass), for each of eight
  keys (the dummy, the directory, the four files, `-other.txt` and
  `dx/-y` under it) each of the eight public put and delete calls is
  refused with `IllegalArgumentException`, and `putLongKey()` and
  `deleteLongKey()` with a `DbException` from `execute()`; the
  transaction count is unchanged. Nine neighbours are taken
  (`/#i/-dummy2`, `/#i/-dumm`, `/#i/dreclaimx/-a`, `/#i/dreclai/-a`, the
  Pub API's `/#i/didef/-n`, `/#i/dient/dn/-k`, a marker, `/#i/-other`,
  `/#j/dreclaim/-settings.txt`). The database takes the next
  transaction, and a restart reads the settings and the dummy as the
  Core wrote them. This is CA3's case: seven bytes at
  `/#i/dreclaim/-settings.txt`, now refused, and the restart works.
* `testKeyTransformationRefused`: a key transformation from `/t` to each
  of the eight keys: `execute()` refuses with `DbException`, nothing of
  the transaction is written (also its other KV), the KV has its key as
  written back, and the database goes on and restarts.

The Pub API's index writes: they go through `putLongKey()` and
`deleteLongKey()` at `/#i/di...`, in user transactions, so step 2 runs
on them and passes them. Covered by `bergdb.pubimp.PubTesterIndex`,
`PubTesterIndexJobs` and `IndexDefinitionTester` in the unit tests, and
by `level1.sh`'s index runs.

Changed existing tests, their own commit (`9b3fd89d`), both following
directly from the refusal:

* `DbTesterRestart.testMalformedSettingsRefusedAtStart` put malformed
  settings with the public `put(String, String)` to check that a start
  refuses them. It now uses `putCore()`; its assertions are unchanged.
* `PubTester.testTransactionInfoOfAFakeReclaimRecord` (021-17, R17-1)
  wrote a user value and a KV at `/#i/dreclaim/-fake.txt` through `Db`
  and expected `transactionInfo()` to refuse the record with
  `InternalDataException`. That record can no longer be written through
  the API: the test now expects the put refused with
  `IllegalArgumentException`, nothing written, the database going on.
  `transactionInfo()`'s own check stays in the code, for a damaged
  stream, but no unit test reaches it now (it would need a stream edited
  by hand).


## 5. Gates

On the branch head (section 6), each in a slot:

| Gate                | Result                                          |
|---------------------|-------------------------------------------------|
| `before-commit.sh`  | BEFORE COMMIT OK, 65 s (unit 1699, F 89, demos) |
| `stress/level1.sh`  | LEVEL 1 OK                                      |
| `stress/level3.sh`  | LEVEL 3 OK, 11.5 min; 35 traces, C-CUT 0 of 799 |


## 6. State

2026-11-12, 14:59. **Done and gated.**

* **Clone** `/Users/f/fl/bench/2026-11-12/ca3/clone`, branch
  `ca3-core-keys` from `main` at `2cf42560`, in Frans's name:
  `915356bf` (the change, `DbTesterCoreKeys`, Javadoc,
  `releases/next.md`), `9b3fd89d` (the two changed tests, section 4).
  Not pushed; the coordinator lands it. The clone's `lean/.lake` is a
  copy of the main tree's, not tracked.
* **Gates** on `9b3fd89d`: before-commit, level1, level3 OK (section 5).
* **Merge with main** (`c49351e1`, 024-36 and 027 since the base): a
  trial merge conflicts only in `releases/next.md`, Known issues, where
  024-36 and this item each add an entry: keep both. Nothing else
  overlaps (024-36 is `FileStream`; 027's reference edits merge).
* **For 010-04, R5's case list** (not edited here, only this file is
  mine): "024-37: a Core put or delete at the Core's own keys made a
  database that never started; refused since 2026-11-12."
* **Not done**: no unit test reaches `transactionInfo()`'s check of a
  fake reclaim record any more (section 4); it would need a stream edited
  by hand. `core/doc-files/key-encoding.md` not changed.
* **To continue**: land the branch, resolving `releases/next.md`.
