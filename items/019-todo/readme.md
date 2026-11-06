019-todo
========

Created 2026-11-05 by Frans Lundberg. Status: open.

Short tasks on BergDB: faults to fix, things to investigate, decisions to
prepare, changes to make, each done and closed in a day or two. Most are
for an AI agent to do unattended, alone or after a limited input from
Frans: a decision between options, or answers to questions. Each entry is
a subitem with its own ID.

It takes the new entries after 015-todo, whose list is getting full:
since 2026-11-05, every new todo entry goes here. The entries open in 015
stay there until they close.


Rules
=====

What goes where
---------------

* **Here**: a task with a clear "Done when" that an agent can finish and
  close in a day or two, its gates and timed runs included. Every open
  entry is done before the next release, unless Frans makes an exception
  (Frans, 2026-11-05, 12:16).
* **017-07, "To consider"**: an idea that Frans may consider some day,
  not a todo for the next release.
* **017-long-term**: open-ended, long-term and strategy topics, with no
  fixed "Done when", that need Frans's thinking (017's rules).
* **An item of its own**: bounded work larger than a day or two, with a plan,
  several steps or a status that stays open for a while (the items
  readme, "Small work").
* **006-2026-q4**: small work done at once at Frans's request, such as a
  summary or a review. An entry here is a task registered for later.
* An entry that turns out larger than a day or two moves to an item of its own;
  one that turns out open-ended is moved to 017 by Frans (017's rules).
  Its row moves to Closed with status moved, and its file stays with a
  link to where the work went.


Entries
-------

* An entry is a file `nn-short-name.md`, or a directory `nn-short-name/`
  with a `readme.md` when it has scripts or results. It says what, why,
  Frans's input, when it is done, and the first step:

      019-nn. Fix: a short title
      ==========================

      Status: open. Kind: Fix. Frans: none.
      Created 2026-11-05 by Frans Lundberg.

      What: the fault or the task, and where it is.

      Why: what goes wrong, or what it is for; the source (a review, a
      test, a night's run).

      Frans: none; or the questions; or the options, each in full.

      Done when: the test, the gate, the measurement or the decision
      that closes it.

      First step: what an agent does first.


      Log
      ---

      2026-11-05. Registered by <session or Frans>.

* The `Frans:` field says what the entry needs from Frans:
  * `none`: an agent does it all, unattended;
  * `answers`: questions, written in the entry, that Frans answers
    before the step that needs them;
  * `decision`: options, each described in full in the entry with its
    consequences, and a recommendation; Frans chooses, then an agent
    finishes the entry. A Decide entry always has it.
* An agent prepares Frans's input unattended: it investigates, writes the
  questions or the options with their evidence, and sets the status to
  `waiting`. Frans's answer goes into the entry's log, quoted, with its
  date and time, and the status goes back to `open`.
* An agent, or a night's coordinator (013-01, 013-02), may take an open
  entry without asking. It sets the status to `in progress` and names its
  session in the entry's log, so that no other session takes it. If it
  stops before the entry is done, it writes a State note in the entry, so
  that another session can go on.
* Entries are numbered 019-01 to 019-99, the next after the highest
  issued; while a coordinator runs, a session asks it for the number
  (013-02). When the numbers run out, a new todo item continues the list.


The list
========

Two tables: what is left to do, and what is closed. A subitem's own
`Status:` line is the source. When an entry closes (done, dropped or
moved), its row moves from Open to Closed in the same edit, with the date
it closed; Closed is newest first. Files stay where they are, so links to
them keep working.


Open
----

| ID | Kind | What | Frans | Status |
|---|---|---|---|---|
| [019-07](07-record-header-checksum.md) | Implement | A checksum of the record header, at the next RECORD_FORMAT change | decision | waiting |
| [019-15](15-delete-key-replace.md) | Fix | Key replace: a delete's key is not replaced | decision | waiting |


Closed
------

| ID | Kind | What | Frans | Status | Closed |
|---|---|---|---|---|---|
| [019-22](22-warmup-keeps-large-value.md) | Fix | A transaction's warmup kept a value over 1 MiB | none | done | 2026-11-06 |
| [019-21](21-start-rerun-undercounted.md) | Fix | A start's rerun changes counted nodes, no recount | none | done | 2026-11-06 |
| [019-20](20-replaced-node-undercounted.md) | Fix | A node grown and replaced stays counted below its bytes | none | done | 2026-11-06 |
| [019-10](10-read-unchecked-goes-on.md) | Fix | An unchecked read failure leaves the database going on | decision | done | 2026-11-06 |
| [019-09](09-close-unreported-background-failure.md) | Fix | close() silent on a failed flush | decision | done | 2026-11-05 |
| [019-08](08-dbtime-to-utc-threads.md) | Fix | dbTimeToUtc() from several threads gave wrong strings | none | done | 2026-11-05 |
| [019-02](02-stream-bad-length-exceptions.md) | Fix | Streams refuse a bad length with other exceptions | none | done | 2026-11-05 |
| [019-01](01-metablock-version-high-bytes.md) | Fix | A meta block's version: bytes 6 and 7 unchecked | none | done | 2026-11-05 |
| [019-05](05-exists-malformed-key.md) | Fix | exists() answers false for a malformed key | decision | done | 2026-11-05 |
| [019-06](06-perf-harness-old-jar.md) | Fix | Harness fails on 2026.2's jar | none | done | 2026-11-05 |
| [019-04](04-remove-seekfirstpos.md) | Implement | Remove seekFirstPos() from AppendOnlyStream | none | done | 2026-11-05 |
| [019-03](03-get-that-copies.md) | Decide | A get that always copies a byte[] value | decision | moved | 2026-11-05 |

Status values: open, waiting (for Frans's input), in progress, done,
dropped, moved (to an item of its own or to 017). Kinds: Fix (a known
fault), Investigate (find out, then propose), Decide (a question for
Frans, prepared by an investigation), Implement (a decided change).
Frans: none, answers, decision.


Files
=====

* [01-metablock-version-high-bytes.md](01-metablock-version-high-bytes.md).
  019-01, Fix: a meta block's version is read as 2 bytes, so bytes 6 and
  7 are not checked (R6-F3, from 015-74).
* [02-stream-bad-length-exceptions.md](02-stream-bad-length-exceptions.md).
  019-02, Fix: the streams refuse a negative length, or one past the
  array, with other exceptions than the `IllegalArgumentException` that
  `AppendOnlyStream` promises; found by 018-02's harness.
* [03-get-that-copies.md](03-get-that-copies.md). 019-03, Decide: a get
  that always copies a `byte[]` value; moved to 017-07, section 1.
* [04-remove-seekfirstpos.md](04-remove-seekfirstpos.md). 019-04,
  Implement: `seekFirstPos()` removed from `AppendOnlyStream` and every
  stream, with harness 6.3's checks of it (Frans, 2026-11-05, option (a)).
* [05-exists-malformed-key.md](05-exists-malformed-key.md). 019-05, Fix:
  `Connection.exists()` answered `false` for a malformed key, where `get()`
  and an rw-transaction's `exists()` throw; now it throws too (Frans,
  2026-11-05, option (a)).
* [06-perf-harness-old-jar.md](06-perf-harness-old-jar.md). 019-06, Fix:
  `performance.sh`'s harness does not compile against 2026.2's jar:
  `Perf.java` uses 005-47's `FileStream(File, boolean)`, which 2026.2
  lacks.
* [07-record-header-checksum.md](07-record-header-checksum.md). 019-07,
  Implement: a checksum of the record header, in its 3 unused bytes, at
  the next change of `RECORD_FORMAT`, with Frans's approval of the format
  change; from 015-73's option (c). Not for 2026.3 (Frans, 2026-11-05,
  15:35).
* [08-dbtime-to-utc-threads.md](08-dbtime-to-utc-threads.md). 019-08,
  Fix: `DbUtil.dbTimeToUtc()` formatted with one static `SimpleDateFormat`,
  so readers that built a `LookupTimeNotAvailableException` at once got
  another thread's time (015-63's fault in the Core; review R2, B1).
* [09-close-unreported-background-failure.md](09-close-unreported-background-failure.md).
  019-09, Fix: `close()` returns normally after a background write
  failure that no call met, and reports it nowhere (review R1 of night
  006-12, B2); now it throws `StreamIoException` (Frans, 2026-11-05,
  option (a)).
* [10-read-unchecked-goes-on.md](10-read-unchecked-goes-on.md).
  019-10, Fix: an unchecked exception or `Error` from a read of the
  storage is thrown as it is, and the database goes on, where an
  `IOException` fails it; found by harness 6.2 (018-03).
* [15-delete-key-replace.md](15-delete-key-replace.md). 019-15, Fix:
  with key replace enabled, a delete's key is not replaced, where the
  Javadoc says every key's `${transactionTime}` is; found by harness 6.7
  (018-04); waiting for Frans's decision.
* [20-replaced-node-undercounted.md](20-replaced-node-undercounted.md).
  019-20, Fix: a key node that its transaction grew and then replaced
  stayed counted below its bytes until its eviction; found by 018-05's
  harness.
* [21-start-rerun-undercounted.md](21-start-rerun-undercounted.md).
  019-21, Fix: a start counted the startup section's nodes before its
  rerun of the transactions changed them; found by 018-05's harness.
* [22-warmup-keeps-large-value.md](22-warmup-keeps-large-value.md).
  019-22, Fix: a transaction's warmup read with `Dag.CACHE_ALL` and so
  kept a key's old value over 1 MiB in memory; found by 018-05's harness.


Log
===

2026-11-05. Created the item, at Frans's request (09:38): "The list of
015 is already getting full. New todo entries should be added to the new
nnn item. It is similar to 015. The new item [...] is for tasks that can
be done and closed in a short time; a day or so. Open-ended tasks,
long-term tasks, strategy tasks belong to 017. The new nnn entries
(subitems) are mostly tasks that AI can solve completely unattended or
unattended after limited input from Frans like decisions and answers to
questions." Since then every new todo entry goes here; 015 keeps its open
entries.

2026-11-05. 019-01 registered by session bergdb-e8, at Frans's word
(10:47), from 015-74's optional code change (R6-F3).

2026-11-05. 019-02 registered: found by the harness of the stream
contract (018-02).

2026-11-05. 019-03 registered by session bergdb-e8, from Frans's words
of 12:00 on 015-47 ("for another time").

2026-11-05, 12:16. Frans: every open entry is done before the next
release, unless he makes an exception; an entry takes "a day or two", not
"about a day" (in his words: "Yes, this is a good rule. Add this. And
relax the thing about fixing within one day. Make it 'a day or two'.").
019-03 moved to 017-07, "To consider", section 1: an idea, not a todo.

2026-11-05. 019-04 registered by session bergdb-e8, at Frans's decision
(12:30, option (a)), and taken by its agent.

2026-11-05. 019-05 registered by session bergdb-e8, at Frans's word
(12:35), from the agent that wrote 015-62's Javadoc of `exists()`.

2026-11-05. 019-04 done: `seekFirstPos()` removed from
`AppendOnlyStream` and every stream, with harness 6.3's checks of it;
BEFORE COMMIT OK, CORE BUILD OK, LEVEL 3 OK.

2026-11-05. 019-06 registered by session bergdb-e8, from 019-04's
agent's finding (`Perf.java` uses `FileStream(File, boolean)`, which
2026.2's jar lacks), and taken by its agent.

2026-11-05. 019-06 done: `Perf.java` opens its stream with
`FileStream(dir)`, and with `perf.noforce=1` finds 005-47's
`FileStream(File, boolean)` by reflection, failing plainly where it is
missing; the harness compiles against 2026.2's jar and main's again
(2026.1's lacks `bergdb.pub.util.SyncLevel`, 005-56); BEFORE COMMIT OK.

2026-11-05. 019-05 done: at Frans's choice (12:56, option (a)), a
connection's `exists()` throws `IllegalArgumentException` for a malformed
key, as `get()` and an rw-transaction's `exists()` do; the Javadoc says
so; BEFORE COMMIT OK.

2026-11-05. 019-07 registered in night 006-12, at Frans's decision on
015-73 (15:35, to session bergdb-a2: "Yes. Go ahead."): option (a) for
2026.3, and (c), a checksum of the record header, here, for the next
change of `RECORD_FORMAT`. Status waiting: not for 2026.3, Frans's
exception to the rule that an open entry is done before the release.

2026-11-05. 019-01 done in night 006-12: a meta block's version is read
as an int, and a block whose bytes 6 or 7 are not 0 is refused at the
start with `VersioningStreamException`; every BergDB writes 0 there;
BEFORE COMMIT OK.

2026-11-05. 019-02 done in night 006-12: every stream's `read()` and
`append()` refuse a range outside the array with
`IllegalArgumentException` before anything changes (`Util.checkRange`);
harness 6.3 passes without the line "019-02" in `StreamContract.SKIP`;
BEFORE COMMIT OK.

2026-11-05. 019-08 registered in night 006-12, from review R2's finding
B1, and done: `DbUtil.dbTimeToUtc()` formats with a `DateTimeFormatter`,
as `Time` does since 015-63; the strings are unchanged; BEFORE COMMIT OK.

2026-11-05. 019-09 registered in night 006-12, from review R1's
re-review of 3cb19f7 (B2): `close()` returns normally after a background
write failure that no call met. Status waiting: Frans decides whether
`close()` throws there (options (a) to (c), (a) recommended).

2026-11-05, 20:50. 019-09: Frans chose option (a). Done in night 006-12:
`close()` throws `StreamIoException` for a failure of the storage that no
call reported; a close of a database that has failed returns normally.

2026-11-05. 019-15 registered by harness 6.7's agent of the night 006-12:
found by the harness of the Pub API's promises (018-04); waiting for
Frans's decision.

2026-11-06. 019-10 registered by harness 6.2's agent of the night 006-12:
found by the harness of failures and interrupts in storage (018-03).

2026-11-06. 019-10 done in the night 006-12: an unchecked exception or
`Error` of the stream's read fails the storage, and so the database.

2026-11-06. 019-20 and 019-21 registered and done in night 006-12: found
by harness 6.5, eviction's accounting (018-05).

2026-11-06. 019-22 registered and done in night 006-12: found by harness
6.5 (018-05).

2026-11-06, 03:10. 019-10: review R5's F1 and F2 (an `Error` of a read is
now wrapped, not thrown as it is) wait for Frans's decision, options (a)
and (b) in the entry.
