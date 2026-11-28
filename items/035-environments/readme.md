035-environments
================

Created 2026-11-26 by Frans Lundberg. Status: open.

The environments that BergDB runs in, examined on their own: the
operating system, the file system, the disk and the JVM, for what
BergDB relies on. Frans created it on 2026-11-26, from 031-02's
finding F1 (a kill of a writing process on macOS left zeros within a
file's length; 028-60): BergDB's promises of durability, startup and
pauses rest on assumptions about the machine under it, which so far
were tested only through BergDB and found broken by chance.

The work here does not depend on BergDB's code: it tests the
environment with programs of its own, in ways that matter to BergDB.
Its results feed BergDB through other items: the storage contract
(014-01, section 7) and its provider `FileStream`, 027-14 (storage),
and 028 entries where BergDB must cope with what an environment does,
or a limit stated in the documentation.


Scope
=====

* **Correctness**: does the environment keep what BergDB assumes? After
  a kill of the process, a file is a prefix of what was appended;
  forced bytes survive; a force reaches the disk (on macOS, `fsync`
  against `F_FULLFSYNC`); truncation, renaming and deletion of files;
  whether a directory needs a sync. Later, a power loss (a virtual
  machine stopped hard).
* **Performance**: the latency of a force, write throughput, random
  reads cold and warm, the page cache, and the JVM's pauses by
  collector: the numbers behind P1 (010-01) and the startup bounds
  (007). Timing results are kept apart from correctness results, as
  in BergDB's tests (028-23).
* **Environments**: F53 (macOS, APFS, Apple silicon, its internal SSD)
  and s1 (Linux on a virtual private server) first. Others, such as
  Windows and Android, when there is a need (Frans, 2026-11-26: not
  now).


Rules
=====

* **The probes live here**, in the subitem that uses them: small Java
  programs of one file each that use no BergDB code, run with `java
  Probe.java` (the JDK's source-file mode, no build), so that any
  machine with a JDK runs them. AGENTS.md puts experiments in items,
  not in `java/`. A probe that becomes a standing check of BergDB (a
  step of `week.sh`, or of the release checklist, 034-02) moves to
  `java/` when that is decided.
* **Each environment is described** where its results are: the
  machine, the operating system and its version, the file system, the
  disk, the JDK; results without them cannot be compared.
* **A finding says** what was seen, how often, how to reproduce it,
  what is known of its cause and what is a hypothesis, and what it
  means for BergDB, with the item or 028 entry that takes it on.


Files
=====

* [035-01](01-zero-tail-after-kill/readme.md): zeros within a file's
  length after a kill of a writing process (macOS, APFS; 031-02, F1):
  the cause, and whether other systems do it.
* [035-02](02-stale-bytes-after-kill/readme.md): a deleted file's bytes
  within a file's length after a kill (APFS; 035-01, section 7): on
  F53's internal SSD too or not, and what a start of BergDB does with
  an older stream file's records inside the last file.
* [035-03](03-append-only-storage.md): append-only storage, what
  BergDB may take for granted: what append-only means for the stream
  and for the files, the faults a crash may leave by environment, and a
  fault model for the storage contract (014-01, section 7), from which
  028-77 is decided. Not started.


Log
===

2026-11-26. Created (Frans), with 035-01.

2026-11-26. 035-02 created (Frans).

2026-11-26. 035-01, section 12: the zero-tail cut that BergDB makes
(028-60, part 2; Frans's decision).

2026-11-28. 035-03 created (Frans), with 028-77; not started.
