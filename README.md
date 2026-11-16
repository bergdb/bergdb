BergDB
======

BergDB is an embedded, append-only key-value database for Java. It runs
inside your Java process, keeps every transaction in one append-only
stream of files, and lets you read the database as it was at an earlier
time.

* **One stream.** The stream is the only durable storage: no write-ahead
  log and no separate index files. Data, index and history are all
  records in the stream.
* **Self-indexed.** Index nodes are written into the stream lazily, as
  the writes go on. A start reads only the tail of the stream, so the
  time to open a database does not grow with its size.
* **History.** A read can be made at any time that is still kept, and
  sees the database as it was then, its indexes included.
* **Larger than memory.** Eviction keeps the database within a memory
  budget, and reclaim cuts the front of the stream when a finite
  retention allows it.
* **Small.** One jar with no dependencies beyond the JDK. No server, few
  settings.

The Core is a key-value store of byte arrays. The Pub API on top of it
stores strings, byte arrays and objects under path-like keys, with
secondary indexes.


Status: a preview
-----------------

**BergDB is a preview. Do not use it in production.**

* There is no promise about the stream format or the API until a stable
  release. A database made by one release may not open in the next:
  release 2026.5 refuses the databases of 2026.4 and earlier. There is no
  upgrade tool; read the data with the old release and put it with the
  new one.
* The latest release is 2026.5, of 2026-11-13, tag `release-2026.5`. Its
  notes, [releases/2026.5/readme.md](releases/2026.5/readme.md), say what
  it is, how it was tested and what is known not to work. The `main`
  branch moves ahead of it.
* It is tested on JDK 17 and 27, on macOS and Linux, and on an Android
  emulator (the Core from API level 33, objects from 34), not on a phone.

TO CHECK (Frans): where users get the jar. Today each release's jar is in
`releases/VERSION/`; if the jars move to GitHub Releases, say so here.


Try it
------

You need a JDK 17 or later and a Unix shell (macOS or Linux).

    java/build.sh               # builds the jar for users, java/build/bergdb-release.jar
    java/before-commit.sh       # unit tests, f-tests and demos (2 minutes; needs python3, perl)
    java/javadoc-pub.sh         # the Pub API's Javadoc, in java/build/javadoc-pub/

A first program:

```java
import bergdb.pub.Connection;
import bergdb.pub.Database;
import bergdb.pub.Factory;
import bergdb.pub.Time;

public class Hello {
    public static void main(String[] args) throws Exception {
        try (Database db = Factory.database().create("hello-db").start()) {
            Connection c = db.connection();
            Time first = c.put("/fruit/apple", "red").getTime();
            c.put("/fruit/apple", "green");
            System.out.println(c.get("/fruit/apple", String.class));   // green

            c.setLookupTime(first);                                    // read the past
            System.out.println(c.get("/fruit/apple", String.class));   // red
            c.sync();                                                  // wait until durable
        }
    }
}
```

    javac -cp java/build/bergdb-release.jar Hello.java
    java -cp java/build/bergdb-release.jar:. Hello

`create` makes a new database in a new or empty directory; `open` opens
an existing one. More examples are in `java/src-dev/bergdb/demo/`
(`GetStarted1` to `GetStarted5`).

The API is the packages `bergdb.pub` and `bergdb.pub.util`. The Core's
`bergdb.core.Db` is a lower-level API of byte-array keys and values, less
stable and less safe. Anything else that is public in the jar is not
API. [java/readme.txt](java/readme.txt) says more about the build, and
[java/build.sh](java/build.sh) and the other scripts say what they do in
their headers.

What a running database needs:

* `stop()` or `close()` for every database that is started.
* The ZGC collector (`-XX:+UseZGC`), or Shenandoah without generations,
  for short pauses. With G1, eviction brings pauses of hundreds of
  milliseconds.
* Storage that returns the bytes as they were written. BergDB's checks
  for damaged bytes are a best effort.
* `-XX:+ExitOnOutOfMemoryError`: an `Error`, such as `OutOfMemoryError`,
  fails the database, and the process should end.


Known issues and limits
-----------------------

The full list is in the release notes,
[releases/2026.5/readme.md](releases/2026.5/readme.md), "Known issues and
limits". The ones a user meets first:

* **The format changes between releases** (above).
* **Limits.** A key is at most 111 bytes, a value at most 8 MiB, a
  transaction at most 500 operations and 32 MiB. A call over a limit
  throws and writes nothing.
* **No replication, no encryption.** For a backup, copy the stream's
  files; against the loss of a disk, use a mirrored disk.
* **The startup distance.** The default, 50 MB, suits up to about 10M
  keys; beyond that, use 200 to 1000 MB. At a fixed startup distance, the
  stream bytes written for each put grow with the number of keys.
* **Reclaim keeps more than the live data.** With a finite retention,
  the stream holds the kept history and, beyond it, up to about 6 times
  the live data.
* **Each database allocates a 10 MB write buffer at its start**, whatever
  its size.
* **Not everything is proved** (see "The Lean model" below), and
  concurrency is tested, not proved.


How it works
------------

The design is described in item 027, the algorithms of BergDB
([items/027-algorithms](items/027-algorithms/readme.md)). It is still
being written. Until it is, read 027-01, a snapshot of 2026-11-12: the
feature levels, what works and the evidence
([levels.md](items/027-algorithms/01-docs-2026-11-12/levels.md)), and the
model of self-indexed streams
([sis-model.md](items/027-algorithms/01-docs-2026-11-12/sis-model.md)).
The stream format is 027-03 and the trace format 027-02, both kept
current. The principles that BergDB is built by are 010-01
([items/010-principles](items/010-principles/readme.md)).

The work itself is recorded in `items/`: plans, experiments, measurements
and reports ([items/readme.md](items/readme.md)). Documents and code
comments cite them by number, such as `027-01` or `010-01, P5`.


The Lean model
--------------

TO CHECK (Frans): what this paragraph claims.

`lean/` holds a model of BergDB's algorithm in Lean 4: the stream and
recovery, bounded startup, reclaim, eviction and the key tree, with
theorems about them. Some of the theorems are proved; others are stated
and still open. [lean/README.md](lean/README.md) says which. The proofs
are about the model, not about the Java code. The Java code is checked
against the model: its runs are traced, and the traces are replayed in
the model. Concurrency and resource bounds are not in the model. To check
the proofs, install [elan](https://github.com/leanprover/elan) and run
`cd lean && lake build`.


Repository
----------

* `java/`: the implementation, its build scripts and its tests.
* `lean/`: the Lean model and its proofs.
* `items/`: the work items, the design documents among them.
* `releases/`: each release's notes and checksums.
* `docs/log.md`: the development log.

BergDB was first developed from 2012 to 2017, with releases from 2013 to
2015. The work went on in October 2026 from the 2017 source: it fixed the
bugs that had stopped it, made a model of the algorithm, and added
reclaim and eviction. Much of the 2026 code, tests, documentation and
Lean development was written by Frans Lundberg together with AI
assistants.


Contributing and security
-------------------------

Bug reports and ideas are welcome; [CONTRIBUTING.md](CONTRIBUTING.md)
says what is accepted. To report a vulnerability, see
[SECURITY.md](SECURITY.md); do not open a public issue for it.


Copyright and licence
---------------------

Copyright 2013-2026 Frans Lundberg.

Licensed under the Apache License, Version 2.0: see [LICENSE](LICENSE)
and [NOTICE](NOTICE).

TO CHECK (Frans): the name. "BergDB" is Frans Lundberg's name for this
software. The licence gives no right to use it, except to say where the
code comes from (Apache License 2.0, section 6).
