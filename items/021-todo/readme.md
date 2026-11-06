021-todo
========

Created 2026-11-06 by Frans Lundberg. Status: open.

Short tasks for release 2026.4, "a bug-free database" (020): faults to
fix, things to investigate, decisions to prepare, changes to make, each
done and closed in a day or two, mostly by an AI agent, unattended or
after a decision or answers from Frans. Each entry is a subitem with its
own ID. Every open entry is done before release 2026.4, unless Frans
makes an exception.

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

Status values: open, waiting (for Frans's input), in progress, done,
dropped, moved (to an item of its own or to 017). Kinds: Fix (a known
fault), Investigate (find out, then propose), Decide (a question for
Frans, prepared by an investigation), Implement (a decided change).
Frans: none, answers, decision.


Files
=====

None yet.


Log
===

2026-11-06. Created the item, at Frans's request (15:51): "I would like
us to start preparing for 2026.4 work. I would like a new todo list for
this work." It replaces the rule of 10:58 the same day (006-13), that
the list for 2026.4 would open at 2026.3's release. By coord-1106.
