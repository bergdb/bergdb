028-34. Decide: transactionInfo() in the Pub API, or the walk in the Core
=========================================================================

Status: open. Kind: Decide. Frans: to decide (no decision on 2026-11-20).
Created 2026-11-20 by Frans Lundberg.

What: `Connection.transactionInfo()` (Pub API) gives the time and the
user's KVs of the transaction that wrote the value of the connection's
last `get()`. With it, a user walks the versions of a key, newest first:
a `get()`, then `transactionInfo().time()` t, then a `get()` at the
lookup time t less one unit, and so on (its Javadoc). Together with gets
and scans at any lookup time, this gives a value's history within the
retention, at the cost of one lookup a step, with nothing extra stored.

How it is made today: on top of the Core API, in
`ConnectionImp.transactionInfo()`:

* `Db.getOne(lookupTime, key, GetData)` gives `GetData.tpos`, the stream
  position of the transaction that stored the value;
* `Db.internal().getTrans(tpos)` reads that transaction (`StoredTrans`);
* a record of reclaim's (a step that copied the value forward) is
  followed back: a get at the step's time less one unit, and its
  transaction, until a user's transaction (021-17);
* the KVs are filtered to the user's (no index entries, no keys outside
  the Pub API; 018-04, 020-22) and converted to Pub keys.

Two pieces are not in the Core API: reclaim's records are recognised by
reclaim's key prefix (`Reclaim.KEY_PREFIX_SKEY`, internal), and the call
uses `Db.internal().getTrans()`, which takes the position as the
database's own (a record there that is no committed transaction is
damage and fails the database), where the public `Db.getTrans()`
refuses it as the caller's mistake.

What it has cost: faults and fixes in 005-30, 005-34, 005-82, 015-62,
021-13, 021-17, 021-27 and 024-37 (a get during the store of the
transaction, positions inside a record, damaged records, reclaim's
copies). It ties reclaim's design: reclaim's copies must stay
recognisable and traceable to the write. Neither the Lean model (030)
nor 027 covers it. About 50 calls in the Pub testers use it, and
KillRestartHarness's check.

`GetData.kvTime` is not the time of the write: it is the time of the
key node entry, which PE and reclaim make anew (021-19). The time of the
write needs the transaction.

Similar features elsewhere: Datomic (as-of databases, the history of a
fact), XTDB (entity history, queries at a time), immudb (an append-only
key-value store with the history of a key), SQL:2011 system-versioned
tables (`FOR SYSTEM_TIME AS OF`, `BETWEEN`).

Why: the Pub API is the stable API; a feature that stays in it should be
tested and, where it matters, proved; a feature that goes should leave
its use possible on the Core (010-01, P12: features on top of the Core).

Frans: to decide between the options; he takes no decision on
2026-11-20.


Options
-------

* **Option 1: keep `transactionInfo()` as it is**, with more tests,
  possibly with the model's scope extended to it. What a proof would
  state: the walk back from a value gives the user's transaction that
  wrote it, never one of reclaim's, for a value whose write is at or
  after the first available lookup time; close to what 030-25 proved of
  reclaim's steps. More tests: the walk under reclaim and restarts in
  the harnesses (KillRestartHarness checks it already) and in the user
  apps.
* **Option 2: remove it from the Pub API, and make the walk available
  through the Core API.** The Core gets a stable way to the transaction
  that wrote a value: either a public test whether a `StoredTrans` is
  reclaim's, or a Core method that follows reclaim's copies back itself
  (the loop of `ConnectionImp` moved into the Core). `TransactionInfo`,
  the loop and the filter leave `pubimp` (about 200 lines and their
  tests); a later Pub call can be built on the Core's again.

Done when: Frans has chosen; the choice is recorded here with its date,
and the work it needs is an entry or a release item's subitem.


Log
---

2026-11-20. Created (coord-1120), with both options as Frans named them.
