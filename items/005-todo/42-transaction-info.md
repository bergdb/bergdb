005-42. Decide: what transactionInfo() gives: internal KVs, and reclaim's rewrites
=================================================================================

Status: done; decided A1 and B2 (Frans, 2026-10-25), and done the same day.
Kind: decide. Created 2026-10-25.

From a TODO of 2016 in `ConnectionImp.transactionInfo()`: "we cannot in
general convert keys to ukey (strings). How to handle in Pub Layer?".
Found in the review of the TODO markers in `java/` (006-05, T12) by Claude
(Opus 5.5, Claude Code), with a probe; added at Frans's request ("as
proposed"). The TODO is now a comment that points here. The probe and its
output are in [42-transaction-info/](42-transaction-info/).


The issue
---------

`Connection.transactionInfo()` gives "information about the transaction
that wrote the last value retrieved with the get() method": its time
(`TransactionInfo.time()`) and its KVs (`kvs()`), a `Kv` for each value
node of the record. In two cases it gives what the API does not promise.

**Internal KVs.** A record can hold KVs under the internal prefix `/#i/`
(`DbConstants.INTERNAL_PREFIX`), which are not the user's: the entries of
an index, the rows of reclaim. Their keys are not ukeys, and their `key()`
throws. Probe A: an index on the long field `salary` of `/e/`, a put of
`/e/x`, a get of it. `kvs()` has 2 KVs, and the first is the index entry,
whose `key()` throws `IllegalArgumentException`: "ikey cannot be converted
to valid ukey, ikey: /#i/di/demp-salary/~...". So a loop over `kvs()` that
calls `key()` fails for every transaction that writes an index entry.
`Kv.ikey()`, "Used internally, not intended for the Pub API user", throws
`UnsupportedOperationException` ("not implemented") for every KV here.

**Reclaim's rewrites.** Reclaim rewrites each live value stored before its
cut point, in internal transactions of its own (its steps), so that the
front of the stream can be cut. A get of such a value gives the step's
position, and `transactionInfo()` then describes the step. Probe B: a put
of `/a` at 1 s, then 20,000 puts of other keys a second apart, with a
retention of 100 s and a startup distance of 1 MB; a get of `/a` at
20,001 s. `time()` is 14,078 s, not 1 s, and `kvs()` holds reclaim's row
`/#i/dreclaim/-current.txt`, whose `key()` throws, and `/a`. The put's own
transaction, the one the user knows, may be cut from the stream by then.
docs/problem.md, Q9 (2026-10-13), removed `Kv.time()` because reclaim
changes it, and kept `TransactionInfo.time()` as "the transaction time";
after a rewrite it is the time of reclaim's step.

| Probe | `time()` | `kvs()` |
|---|---|---|
| A: a put that writes an index entry | the put's | the index entry, whose `key()` throws; `/e/x` |
| B: `/a`, rewritten by reclaim | 14,078 s, reclaim's step | reclaim's row, whose `key()` throws; `/a` |

The tests of today, `PubTester.testTransactionInfo1` and
`testTransactionInfoAfterRestart`, have neither an index nor reclaim.


The options
-----------

For the internal KVs:

* **A1. Leave them out of `kvs()`.** A KV whose key starts with the
  internal prefix is not the user's, and every ikey made from a ukey has
  `d` or `-` after each `/`, so none of the user's starts with `/#`. A
  change in `transactionInfo()` only.
* **A2. Keep them, with a key that can be read.** `key()` gives the ikey
  for them, or null. The user then sees index entries and reclaim's rows,
  for which the API has no words.

For a value that reclaim has rewritten:

* **B1. Document it.** `transactionInfo()` describes the transaction that
  last wrote the value to the stream, which can be one of reclaim's.
* **B2. Refuse it.** When the record is reclaim's, throw
  `LookupTimeNotAvailableException`, which the Javadoc of
  `transactionInfo()` already names for "the database has reclaimed the
  transaction": the transaction that wrote the value is gone, or will be
  at the next cut. Reclaim's steps and its table are transactions of their
  own, and each holds a KV under `/#i/dreclaim/`, which tells them apart.
* **B3. Keep the original.** Store the time of the transaction that wrote
  a value in its value node, and let reclaim copy it: Q9's exact write
  time, a format change of 8 bytes a value (or a varint), not planned.
  `time()` then gives that time; the other KVs of that transaction cannot
  be given once it is cut.
* **B4. Remove `transactionInfo()`.** A question for 005-05: what the
  published API holds.

And `Kv.ikey()`: implement it here (the ikey is at hand), or leave it to
Frans's note in `Kv` of 2014: "ikey() should probably be hidden from Pub
API. Maybe two interface CoreKv and Kv."

Proposed: A1 and B2. They keep the promise of the Javadoc as it is written,
with an exception that it already declares, and need no format change. B3
can come on top of them later, if an exact write time is wanted (Q9).


Done when
---------

* As decided. For A1 and B2: `transactionInfo()` leaves out the KVs under
  the internal prefix, and throws `LookupTimeNotAvailableException` for a
  record of reclaim's; the Javadoc of `Connection.transactionInfo()` and
  `TransactionInfo.kvs()` says so.
* Unit tests: a put that writes an index entry (only the user's KVs, and
  every `key()` works); a value that reclaim has rewritten (the
  exception), in `PubTester` with a test clock, as probe B but smaller.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S for A1 and B2. Any time; best before 005-05's decision on publishing, as
it concerns the Pub API.


Frans, 2026-10-25
-----------------

Asked, before release 2026.1 (008), what the release should do with it:
"A1 + B2 as proposed".


Outcome
-------

2026-10-25, by Claude (Opus 5.5, Claude Code), A1 and B2 as proposed, on
`da8bbc1`:

* `ConnectionImp.transactionInfo()` leaves out the KVs under the internal
  prefix, `DbConstants.INTERNAL_PREFIX_SKEY`, so every `key()` of
  `kvs()` works.
* It throws `LookupTimeNotAvailableException` for a record of reclaim's: one
  that holds a KV under reclaim's prefix, `/#i/dreclaim/`, now
  `Reclaim.KEY_PREFIX_SKEY`. Every step stores reclaim's row in the
  transaction that rewrites the values, and the table is a transaction of
  its own with no user value, so the test finds every rewrite, and no user
  transaction holds such a KV.
* The Javadoc of `Connection.transactionInfo()` and `TransactionInfo.kvs()`
  says so. `Kv.ikey()` still throws "not implemented"; not part of the
  decision.
* Tests, in `PubTester`, which fail without the change:
  `testTransactionInfoWithIndex` (a put that replaces an index entry, and
  one more KV: two KVs, the user's), `testTransactionInfoAfterReclaim` (a
  value that reclaim has rewritten: the exception, with the core's builder
  as `testFirstAvailableLookupTime2`, so that reclaim cuts soon; a value
  written after the cut still gives its transaction). Before the change:
  "ikey cannot be converted to valid ukey", and "a value that reclaim
  rewrote gave a transaction at 121000001; /a was put at 10000000".
* The probe again ([probe-after.txt](42-transaction-info/probe-after.txt)):
  part A gives one KV, `/e/x`; part B throws the exception.
* `before-commit.sh` passes; see 005-45's outcome, which was gated with
  it.


The probe
---------

In [42-transaction-info/](42-transaction-info/): `TransactionInfoProbe.java`,
parts A and B, through the Pub API; `probe.sh JAR WORK_DIR` compiles it
against a build and runs it; `probe-output.txt`, its output on `98ac9eb`
with 005-40 and 005-43, uncommitted at the time; `probe-after.txt`, on
`da8bbc1` with the change.
