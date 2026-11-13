021-todo
========

Created 2026-11-06 by Frans Lundberg. Status: done (2026-11-13):
every entry closed; new entries go to 028-todo.

Short tasks for release 2026.4, "a bug-free database" (020): faults to
fix, things to investigate, decisions to prepare, changes to make, each
done and closed in a day or two, mostly by an AI agent, unattended or
after a decision or answers from Frans. Each entry is a subitem with its
own ID. Every open entry is done before release 2026.4, unless Frans
makes an exception.

The theme of 2026-4 is "bug-free". This is a theme, a direction. It helps us
to focus. We mean that there should be no known bugs before the release.

019-todo keeps the entries for release 2026.3 (a bug-free Core, 018);
its open entries stay there until they close. A new entry goes here when
it is for 2026.4: the non-Core part (user indexes, objects and their
serialization, 020-01), or work that Frans has put after 2026.3. A new
entry for 2026.3's Core still goes to 019 until 2026.3 is released.


Rules
=====

The rules of 019-todo hold here (019's readme, "Rules": what goes where,
the entry's form, the `Frans:` field, taking an entry, the numbers), with
021 for 019:

* An entry is a file `nn-short-name.md`, or a directory `nn-short-name/`
  with a `readme.md`: what, why, Frans's input, when it is done, and the
  first step, then a Log.
* Entries are numbered 021-01 to 021-99, the next after the highest
  issued; while a coordinator runs, a session asks it for the number
  (013-02).
* An idea to consider some day goes to 017-07; an open-ended topic to
  017; a larger piece of 2026.4's work with a plan becomes a subitem of
  020.


The list
========

Two tables, as in 019: what is left to do, and what is closed (newest
first). A subitem's own `Status:` line is the source.


Open
----

| ID | Kind | What | Frans | Status |
|---|---|---|---|---|


Closed
------

| ID | Kind | What | Frans | Status | Closed |
|---|---|---|---|---|---|
| [021-28](28-tests-fixed-time-limits.md) | Fix | Unit tests with fixed time limits fail under load | none | done | 2026-11-13 |
| [021-29](29-tests-wait-without-timeout.md) | Fix | Unit tests that wait with no timeout | none | done | 2026-11-13 |
| [021-27](27-gettrans-inside-record.md) | Decide | getTrans inside a record fails the database | decision | done | 2026-11-12 |
| [021-25](25-reclaim-fifo.md) | Investigate | Reclaim stops cutting a FIFO in time order | decision | done | 2026-11-11 |
| [021-06](06-read-side-ill-formed-utf8.md) | Investigate | Ill-formed UTF-8 from another writer, read by Java | answers | done | 2026-11-09 |
| [021-10](10-entries-suffix-dot-in-dir.md) | Fix | A '.' in a directory makes no key there an object key | none | done | 2026-11-09 |
| [021-11](11-pointer-type-at-start.md) | Fix | A damaged pointer naming a node of another type was linked by node id | none | done | 2026-11-09 |
| [021-12](12-key-node-outside-section-unchecked.md) | Fix | A damaged key node read before the startup section made a start throw AssertionError | none | done | 2026-11-09 |
| [021-13](13-transaction-info-race.md) | Fix | transactionInfo() while another thread wrote could fail the database (2026.1 to 2026.3 too) | none | done | 2026-11-09 |
| [021-14](14-buffered-read-overflow.md) | Fix | A read whose end overflows a long gave an array exception or stale bytes, not EOFException | none | done | 2026-11-09 |
| [021-15](15-node-texts-not-deterministic.md) | Fix | Refusal texts of a start named nodes by identity hash, different in every run | none | done | 2026-11-09 |
| [021-16](16-long-keys-overflow-the-stack.md) | Fix | A key of about 90 KB or more overflowed the stack: a start failed, a put failed the database | none | done | 2026-11-09 |
| [021-17](17-transaction-info-after-reclaim.md) | Fix | transactionInfo() refused uncut transactions after reclaim had copied the value (2026.1 to 2026.3 too) | none | done | 2026-11-09 |
| [021-18](18-prefix-scan-stops-at-prefix-key.md) | Fix | GetMany.Prefix stopped at a key equal to the prefix (since 2017) | none | done | 2026-11-09 |
| [021-19](19-kv-time-of-a-later-transaction.md) | Doc | A KV's time is its key node entry's time, not the write's: Javadoc made exact (decided 2026-10-13) | none | done | 2026-11-09 |
| [021-20](20-database-directory-reused.md) | Fix | A database's directory deleted and made again: the old database wrote into the new one | none | done | 2026-11-09 |
| [021-21](21-rw-environment-threads.md) | Fix | An RwEnvironment used by several threads lost puts and failed the database; used after return | none | done | 2026-11-09 |
| [021-22](22-shared-connection-guard.md) | Fix | A Connection shared by threads gave wrong reads and failed the database; now refused | none | done | 2026-11-09 |
| [021-23](23-huge-array-put.md) | Fix | A put of an object over 2 GB stored threw OutOfMemoryError (in rw(), failed the database) | none | done | 2026-11-09 |
| [021-24](24-directory-check-after-force.md) | Fix | A directory replaced during the force before a new stream file got that file | none | done | 2026-11-09 |
| [021-26](26-clock-past-max.md) | Fix | A currentTime() past the end refused later puts | none | done | 2026-11-09 |
| [021-09](09-udir-accepts-bad-dirs.md) | Fix | `PubKeys.udir2idir` accepts "p/" and "/p//" | none | done | 2026-11-08 |
| [021-08](08-object-reader-nesting-depth.md) | Fix | The object reader has no limit on nesting depth | none | done | 2026-11-07 |
| [021-07](07-object-reader-format-errors.md) | Fix | The object reader's format errors are not BadFormatException | none | done | 2026-11-07 |
| [021-05](05-core-string-puts-lone-surrogate.md) | Fix | The Core's String puts write '?' for a lone surrogate | none | done | 2026-11-07 |
| [021-04](04-lone-surrogates-in-objects.md) | Decide | A lone surrogate in a String inside an object | decision | done | 2026-11-07 |
| [021-03](03-lean-checks-by-hand-only.md) | Fix | Lean's test programs by hand only; TakeCheck | none | done | 2026-11-07 |
| [021-01](01-pub-javadoc-d30-rest.md) | Fix | Pub Javadoc: DataFormatException, dated history, Time | none | done | 2026-11-07 |
| [021-02](02-lean-readme-log-and-tables.md) | Fix | lean/README.md: a log, wide tables, a Claude line | none | done | 2026-11-07 |

Status values: open, waiting (for Frans's input), in progress, done,
dropped, moved (to an item of its own or to 017). Kinds: Fix (a known
fault), Investigate (find out, then propose), Decide (a question for
Frans, prepared by an investigation), Implement (a decided change).
Frans: none, answers, decision.


Files
=====

* [01-pub-javadoc-d30-rest.md](01-pub-javadoc-d30-rest.md). 021-01, Fix:
  the Pub API's Javadoc: `DataFormatException` not marked as the object
  code's, dated history sentences, `Time.utc` and `resolve` without
  `BadFormatException` (d30's read-through; 006-13, morning list, point 1).
* [02-lean-readme-log-and-tables.md](02-lean-readme-log-and-tables.md).
  021-02, Fix: `lean/README.md`'s dated log to an item, its wide tables,
  and the "Written by Claude" lines of it and `docs/sis-model.md` to a
  log (as 006-12's point 10, option (b)).
* [03-lean-checks-by-hand-only.md](03-lean-checks-by-hand-only.md).
  021-03, Fix: sistest, phystest and reclaimtest into an unattended step
  (`night.sh`), and TakeCheck with 015-03.
* [04-lone-surrogates-in-objects.md](04-lone-surrogates-in-objects.md).
  021-04, Decide: a lone surrogate in a String inside an object, stored
  as '?' (keys and values refuse it): refuse, store faithfully, or keep
  (006-13, morning list, point 2).
* [05-core-string-puts-lone-surrogate.md](05-core-string-puts-lone-surrogate.md).
  021-05, Fix: the Core's `Trans.Builder.put(String, String)` and
  `Keys.toBytes` write '?' for a lone surrogate; refuse it, as 021-04's
  option (1) says.
* [06-read-side-ill-formed-utf8.md](06-read-side-ill-formed-utf8.md).
  021-06, Investigate: a key or a string that is not well-formed UTF-8 in
  a stream from another writer (the C clone's keys), which Java repairs so
  that two keys read as one; with 020-01's object spec (F1, question 5).
* [07-object-reader-format-errors.md](07-object-reader-format-errors.md).
  021-07, Fix: bytes that are not a well-formed object give an
  `AssertionError` (failing the database in `rw()`), a
  `NegativeArraySizeException` or an `IllegalArgumentException` from the
  reader, not `BadFormatException` (found in 020-04, section 10).
* [08-object-reader-nesting-depth.md](08-object-reader-nesting-depth.md).
  021-08, Fix: an object nested deeper than the writer's limit, from
  another writer, can give a `StackOverflowError` at a read, failing the
  database in `rw()`.
* [09-udir-accepts-bad-dirs.md](09-udir-accepts-bad-dirs.md). 021-09,
  Fix: `PubKeys.udir2idir` accepts directories that are not well-formed,
  such as "p/" and "/p//" (found in 020-10's step I0).
* [10-entries-suffix-dot-in-dir.md](10-entries-suffix-dot-in-dir.md).
  021-10, Fix: `Entries.suffix` takes the last '.' of the whole key, so a
  '.' in a directory's name makes no key there an object key.
* [11-pointer-type-at-start.md](11-pointer-type-at-start.md). 021-11, Fix:
  a pointer that the Core links by node id, at a start (rule 4) and by the
  writer, is not checked for its node's type, as a follow checks it
  (019-32); found by reading in the C port (022-01).
* [12-key-node-outside-section-unchecked.md](12-key-node-outside-section-unchecked.md).
  021-12, Fix: a key node that a start reads from before its startup
  section is not validated, as the section's are, and a damaged one made
  the start throw an `AssertionError`.
* [13-transaction-info-race.md](13-transaction-info-race.md). 021-13,
  Fix: `Connection.transactionInfo()` while another thread wrote failed
  the database, in 2026.1 to 2026.3 too (020-24-01, U1-1 and U1-2);
  `Db.getTrans` waits for the writer. On `main` as `f66bf25`.
* [14-buffered-read-overflow.md](14-buffered-read-overflow.md). 021-14,
  Fix: a read whose end, position + length, overflows a long gave an
  array exception or stale bytes, not `EOFException` (found by the C
  port, 022). On `main` as `9bf82c1`, and `a2fa9df` for `OneFileStream`
  on Linux and Android.
* [15-node-texts-not-deterministic.md](15-node-texts-not-deterministic.md).
  021-15, Fix: a start's refusal texts named a node by its identity
  hash, different in every run (from 022). On `main` as `9bb6c0f`.
* [16-long-keys-overflow-the-stack.md](16-long-keys-overflow-the-stack.md).
  021-16, Fix: a key of about 90 KB or more overflowed the stack: a
  start failed, a put failed the database (020-24-05, U5-1 and U5-2);
  the walks made loops, and a start's rerun linear (Q2). On `main` as
  `01d5352` and `520963d`. Q1, the writer's quadratic still-dirty loop
  for long keys, is for Frans (020-11, section 11).
* [17-transaction-info-after-reclaim.md](17-transaction-info-after-reclaim.md).
  021-17, Fix: `transactionInfo()` refused a value that reclaim had
  rewritten (020-24-06, U6-1); it follows reclaim's copies back. On
  `main` as `89a7e56`, and `cf67d0c` for the review's R17-1.
* [18-prefix-scan-stops-at-prefix-key.md](18-prefix-scan-stops-at-prefix-key.md).
  021-18, Fix: `GetMany.Prefix` and `PrefixN` stopped at the prefix's
  own key, since 2017 (020-24-09, U9-1). On `main` as `a009b6a`.
* [19-kv-time-of-a-later-transaction.md](19-kv-time-of-a-later-transaction.md).
  021-19, Doc: a KV's time (`Kvt.time`, `GetData.kvTime`) is its key
  node entry's time, not the write's (020-24-09, U9-3); the Javadoc made
  exact on `main` as `779a123`; options for a later release in the
  entry.
* [20-database-directory-reused.md](20-database-directory-reused.md).
  021-20, Fix: a database whose directory was deleted and made again
  wrote its next stream files into the new one (020-24-10, U10-1); a
  lock by the real path and a check of the directory. On `main` as
  `2557286`.
* [21-rw-environment-threads.md](21-rw-environment-threads.md). 021-21,
  Fix: an `RwEnvironment` used by several threads lost puts and failed
  the database, and took puts after its action returned (020-24-11,
  U11-1 and U11-3). On `main` as `1e4d349`.
* [22-shared-connection-guard.md](22-shared-connection-guard.md).
  021-22, Fix: a `Connection`, an iterator or a `WBuilder` shared by
  threads gave wrong reads and failed the database (020-24-11, U11-2 and
  U11-6); now refused, or the builder's calls taken one at a time. On
  `main` as `a39295c`.
* [23-huge-array-put.md](23-huge-array-put.md). 021-23, Fix: a put of an
  object too large to store threw `OutOfMemoryError`, and in `rw()`
  failed the database (020-24-12, U12-1); now refused before anything is
  copied. On `main` as `7fec115`.
* [24-directory-check-after-force.md](24-directory-check-after-force.md).
  021-24, Fix: a directory replaced during the force before a new stream
  file got that file (Codex's round 4, W1, on 021-20; 020-23, section
  6). On `main` as `c66e824`, and `03ce6ec` for reviewer v2's wording
  (020-23, section 7). `SecureDirectoryStream`, which would close the
  window that is left, is for a later release.
* [25-reclaim-fifo.md](25-reclaim-fifo.md). 021-25, Investigate:
  reclaim stops cutting a FIFO of keys in time order (022-06-3, U3-1
  and U3-2), in Java too and in 2026.3 alike, so not a regression; the cause
  in three parts; a known issue in `releases/next.md` (`69600f9`; the
  item `c6e60ba`). Fix (c), the key access path cleared up to a
  high-water mark, which ends 020-24-14's U14-1 slowdown of puts, on
  `main` as `e3b9787`. Fixes (a) and (b) change the stream: for Frans.
* [26-clock-past-max.md](26-clock-past-max.md). 021-26, Fix: one
  `currentTime()` with the clock past the end (after 2^56 - 1025)
  refused every later user transaction until a restart, a regression of
  020-23's Z1, never released (022-06-2, U2-1). On `main` as `8d405c9`.
* [27-gettrans-inside-record.md](27-gettrans-inside-record.md). 021-27,
  Decide: `Db.getTrans` at a position inside a committed record fails
  the database (022-06-2, U2-4): reproduced in Java, not fixed; the test
  `DbTester.testGetTransInsideARecord` on `main` as `d0a59aa`. Options A
  to D for Frans: C (keep, and say it plainly) for 2026.4, A (tell a bad
  position from damage on the failure path) after it.


Log
===

2026-11-06. Created the item, at Frans's request (15:51): "I would like
us to start preparing for 2026.4 work. I would like a new todo list for
this work." It replaces the rule of 10:58 the same day (006-13), that
the list for 2026.4 would open at 2026.3's release. By coord-1106.

2026-11-09. The open row of 021-25 and the Files entries of 021-13 to
021-27, with their commits on `main`, by coord-1109.

2026-11-11. 021-25 done: fixed by 023's unlink at the delete in release
2026.4 (its own workload, ReclaimFifo, on the release commit: 139 cuts in
1M transactions, a 15 MB directory, against 15 cuts and 135 MB on `main`
before 023; 020-31, section 4).

2026-11-13. New todo entries go to 028-todo since today (Frans, 10:18);
no entry here is open. The item done (Frans, 10:20: "Yes.").
