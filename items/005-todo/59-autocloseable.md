005-59. Decide: `Db` and `Database` as `AutoCloseable`
=====================================================

Status: open. Kind: decide. Created 2026-10-27.

From 005-55's question 6, registered at Frans's request (2026-10-27: "Add
Question 6 as a new 005 entry."), by Claude (Opus 5.5, Claude Code).


The issue
---------

Since 005-55 (`cec0032`) an application must call `stop()` or `close()`
on each database it starts: nothing else stops it (the notes for the next
release, [releases/next.md](../../releases/next.md)). Java's usual means
for such a resource is `java.lang.AutoCloseable`: a `try`-with-resources
block closes it, also when the block throws, and IDEs and static checkers
(Eclipse's "resource leak", IntelliJ's "AutoCloseable used without
try-with-resources", SpotBugs) warn about one that is never closed. Today
neither type implements it:

* `Db` (the Core Layer) has `stop()`, which starts the close in a thread of
  its own and returns at once, and `close()`, which waits until the close is
  done (005-35).
* `Database` (the Pub API, an interface; `DatabaseImp`) has only `stop()`,
  which clears the thread-local connections and calls `Db.stop()`: it does
  not wait.

So `try (Db db = ...)` does not compile, and none of the warnings applies.
The tests close their databases by hand (005-55, about 190 of them).


Options
-------

A. **Both implement `AutoCloseable`, and `Database` gets a `close()` that
   waits.** `Db implements AutoCloseable`: its `close()` is already the
   right method (it throws no checked exception, so the declaration is
   `public void close()`, which narrows `AutoCloseable.close() throws
   Exception`). `Database extends AutoCloseable` with a new `void close()`:
   stops the database as `stop()` does and waits until it is closed
   (`DatabaseImp`: the thread-local connections cleared, then
   `Db.close()`). `stop()` stays as it is. A `try`-with-resources block then
   leaves nothing running when it ends, as a test wants (005-55 chose
   `close()` in the core's tests for that reason). About 15 lines, Javadoc
   included, and a test of each through `try`-with-resources.
B. **Both implement `AutoCloseable`, and `Database.close()` is `stop()`.**
   The same as A, but `Database.close()` returns at once, as `stop()` does.
   Simpler, and the same as today's `stop()`; but `Db.close()` and
   `Database.close()` then mean different things, and a block that ends
   does not mean a closed database.
C. **Only `Db`.** `Db implements AutoCloseable`; the Pub API stays with
   `stop()`. The smallest change, but the Pub API is the one applications
   use.
D. **Neither.** As today: `stop()` and `close()` by hand, as documented
   since 005-55. No change of the API; no warnings from IDEs.

Recommended: A. It is a small addition, not a change: every call of today
keeps working. `close()` that waits is what `AutoCloseable` users expect
of a file or a socket, and the same name then means the same in both
layers.


Questions
---------

1. A, B, C or D?
2. With A or B: is `Database.close()` part of the next release's API (a
   line in [releases/next.md](../../releases/next.md))? Recommended: yes.
3. With A: should the tests move to `try`-with-resources? Recommended: no,
   not as a task of its own; new tests may use it.


Done when
---------

(With A.) `Db` and `Database` implement `AutoCloseable`; `Database.close()`
waits until the database is closed; tests of both through
`try`-with-resources, also with a block that throws; the Javadoc of
`stop()` and `close()` of both say which waits; a line in
`releases/next.md`; `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Size and order
--------------

S. Independent of the rest; after 005-55 (done).
