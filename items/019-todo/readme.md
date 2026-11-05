019-todo
========

Created 2026-11-05 by Frans Lundberg. Status: open.

Short tasks on BergDB: faults to fix, things to investigate, decisions to
prepare, changes to make, each done and closed in about a day. Most are
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
  close in about a day, its gates and timed runs included.
* **017-long-term**: open-ended, long-term and strategy topics, with no
  fixed "Done when", that need Frans's thinking (017's rules).
* **An item of its own**: bounded work larger than a day, with a plan,
  several steps or a status that stays open for a while (the items
  readme, "Small work").
* **006-2026-q4**: small work done at once at Frans's request, such as a
  summary or a review. An entry here is a task registered for later.
* An entry that turns out larger than a day moves to an item of its own;
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

2026-11-05. Created the item, at Frans's request (09:38): "The list of
015 is already getting full. New todo entries should be added to the new
nnn item. It is similar to 015. The new item [...] is for tasks that can
be done and closed in a short time; a day or so. Open-ended tasks,
long-term tasks, strategy tasks belong to 017. The new nnn entries
(subitems) are mostly tasks that AI can solve completely unattended or
unattended after limited input from Frans like decisions and answers to
questions." Since then every new todo entry goes here; 015 keeps its open
entries.
