021-todo
========

Created 2026-11-06 by Frans Lundberg. Status: open.

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
| [021-06](06-read-side-ill-formed-utf8.md) | Investigate | Ill-formed UTF-8 from another writer, read by Java | answers | open |
| [021-09](09-udir-accepts-bad-dirs.md) | Fix | `PubKeys.udir2idir` accepts "p/" and "/p//" | none | open |
| [021-10](10-entries-suffix-dot-in-dir.md) | Fix | A '.' in a directory makes no key there an object key | none | open |


Closed
------

| ID | Kind | What | Frans | Status | Closed |
|---|---|---|---|---|---|
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


Log
===

2026-11-06. Created the item, at Frans's request (15:51): "I would like
us to start preparing for 2026.4 work. I would like a new todo list for
this work." It replaces the rule of 10:58 the same day (006-13), that
the list for 2026.4 would open at 2026.3's release. By coord-1106.
