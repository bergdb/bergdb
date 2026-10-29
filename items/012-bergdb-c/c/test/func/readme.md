Functional tests (bergdb 012-01, 6.4): C programs that use `include/bergdb.h` only, linked by `build.sh` into one program, `func`, which `before-commit.sh` runs in the test build and in the release build under `leaks`.

* `f_api.c` (012-09): a database created and read, refusals, transformations, allocation failures in turn; its `main` lists every file's table and runs `func --child ...` for `f_durable.c`.
* `f_start.c` (012-10): restarts after every transaction, crash cuts at every position, the open's refusals.
* `f_reclaim.c` (012-11): reclaim in a directory, a pending cut made at the open.
* `f_settings.c` (012-13): the status equal to Java's (`java/StatsProbe.java`'s lines), the setters, the open's checks, errors, keys, clocks, sync, the debug calls, close and calls from callbacks.
* `f_durable.c` (012-13): durability: the program itself as a child process killed with `SIGKILL` after execute, after sync, with a record partly written and at random moments (`BERGDB_DURABLE_ROUNDS`, 6 by default); `BERGDB_IN_USE` from another process; a write that fails (`RLIMIT_FSIZE`).
