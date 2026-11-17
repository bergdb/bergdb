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
* **Code only.** Java code is all that is needed, for the advanced
  features too: a transaction is a Java method, an index is made by a
  call, and a query is a loop over Java objects. No query language and
  no schema files.
* **Features.** Atomic transactions, written in Java code only. Scans
  of the keys of a directory and of an index, forward and backward.
  Secondary indexes on the fields of stored objects, and compound ones,
  on up to 8 fields. Historic queries with every feature of the queries
  at the current time.
* **Small.** One jar with no dependencies beyond the JDK. No server, few
  settings.

The Core is a key-value store of byte arrays. The Pub API on top of it
stores strings, byte arrays and objects under path-like keys, with
secondary indexes.


Status
------

BergDB has been tested thoroughly, release by release. Whether that is
enough for your use is yours to judge: the code, the tests and each
release's test results are all in this repository.

How the latest release, 2026.5 (2026-11-13, tag `release-2026.5`), was
tested on its release commit:

* 1,700 unit tests, 89 functional tests and 26 longer tests, all passed,
  on macOS with JDK 27 and on Linux with JDK 17 and 27; the unit tests
  also on an Android emulator.
* A thousand kills of a process in the middle of its writes, each
  followed by a restart that checks every transaction for lost or changed
  data; power-loss tests of the stream's files on Linux.
* Fuzz tests of the API and of the index, concurrency tests with
  jcstress, and Java's index checked, transaction by transaction, against
  an independent model of the algorithm on generated workloads.
* Programs written against the public API alone, as a user writes them.
* Most of it in one seven-hour run; the release notes,
  [releases/2026.5/readme.md](releases/2026.5/readme.md), section
  "Verification", list each step and its result.

No bug is known in 2026.5. The API and the stored format will likely
change before a stable release: a database made by one release may not
open in the next (2026.5 refuses those of 2026.4 and earlier). There is
no upgrade tool; read the data with the old release and put it with the
new one. The `main` branch moves ahead of the latest release.

Each release's jar and Javadoc are on the repository's GitHub Releases
page, under the release's tag; `releases/VERSION/` holds its notes and
checksums. Or build the jar from source, as below.


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

`create` opens the database in the directory, or makes a new one if there
is none; `open` only opens an existing one and never makes one.

Stored Java objects, a transaction, an index and a query of the past,
in `Accounts.java`:

```java
import bergdb.pub.*;

public class Accounts {
    public static class Account {                    // a plain Java class
        public String owner;
        public long balance;
        public Account() {}
        public Account(String o, long b) { owner = o; balance = b; }
    }

    public static void main(String[] args) {
        try (Database db = Factory.database().memory().start()) {
            Connection c = db.connection();
            db.indexBuilder("by-balance").dir("/acc/").type("long").field("balance")
                    .start().join();                 // a secondary index
            c.put("/acc/1001", new Account("Ann", 100));
            c.put("/acc/1002", new Account("Bob", 20));
            c.put("/acc/1003", new Account("Cecilia", 60));
            Time before = c.currentTime();

            c.rw(env -> {                            // a transaction: Ann pays Bob 30
                Account from = env.get("/acc/1001", Account.class);
                Account to = env.get("/acc/1002", Account.class);
                from.balance -= 30;
                to.balance += 30;
                env.put("/acc/1001", from);
                env.put("/acc/1002", to);
            });

            for (Account a : c.usePrimary(Account.class).dir("/acc/").objects()) {
                System.out.println(a.owner + " " + a.balance);   // in key order
            }
            for (Account a : c.useIndex("by-balance", Account.class)
                    .from(50, true).backward().objects()) {      // largest first
                System.out.println("50 or more: " + a.owner + " " + a.balance);
            }
            c.setLookupTime(before);                 // the same query, in the past
            for (Account a : c.useIndex("by-balance", Account.class)
                    .from(50, true).backward().objects()) {
                System.out.println("50 or more, before: " + a.owner + " " + a.balance);
            }
        }
    }
}
```

Compiled and run as `Hello`, it prints:

    Ann 70
    Bob 50
    Cecilia 60
    50 or more: Ann 70
    50 or more: Cecilia 60
    50 or more: Bob 50
    50 or more, before: Ann 100
    50 or more, before: Cecilia 60

`Account` is an ordinary class with public fields and a public
no-argument constructor: a put stores the object, and a get or a scan
gives it back as an `Account`. `rw` runs its action as one atomic
transaction: both puts are made, or neither, and if another transaction
changes what the action has read, the action runs again. The index is
kept as the data changes, in the same transactions. `memory()` gives a
database in memory, gone when it closes; `create`, as above, keeps one
in a directory.

More examples are in `java/src-dev/bergdb/demo/` (`GetStarted1` to
`GetStarted5`), and the Javadoc's page of the package `bergdb.pub` goes
through the calls one by one.

The API is the packages `bergdb.pub` and `bergdb.pub.util`. The Core's
`bergdb.core.Db` is a lower-level API of byte-array keys and values, less
stable and less safe. Anything else that is public in the jar is not
API. [java/readme.txt](java/readme.txt) says more about the build, and
[java/build.sh](java/build.sh) and the other scripts say what they do in
their headers.

What a running database needs:

* `stop()` or `close()` for every database that is started.
* The ZGC collector (`-XX:+UseZGC`), or Shenandoah without generations,
  for short pauses. With G1, eviction (dropping cached data from memory
  when the cache's budget is reached) brings pauses of hundreds of
  milliseconds.
* Storage that returns the bytes as they were written. BergDB's checks
  for damaged bytes are a best effort.
* `-XX:+ExitOnOutOfMemoryError`: an `Error`, such as `OutOfMemoryError`,
  fails the database, and the process should end.


Known issues
------------

No bug is known in release 2026.5. Two things to plan for:

* **The API may change** between releases.
* **The stream format may change** between releases (Status, above).


Limits
------

A key is at most 111 bytes, a value at most 8 MiB, a transaction at most
500 operations and 32 MiB; a call over a limit throws and writes nothing.
The release notes, [releases/2026.5/readme.md](releases/2026.5/readme.md),
"Known issues and limits", give the rest.


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


Repository
----------

* `java/`: the implementation, its build scripts and its tests.
* `lean/`: a model of the algorithm, used in testing; work in progress.
* `items/`: the work items, the design documents among them.
* `releases/`: each release's notes and checksums.
* `docs/log.md`: the development log.

BergDB was first developed from 2012 to 2017, with releases from 2013 to
2015. The work went on in October 2026 from the 2017 source: it fixed the
bugs that had stopped it and added reclaim and eviction. The 2026 code,
tests and documentation was written by Frans Lundberg together with AI
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

"BergDB" is Frans Lundberg's name for this software. The licence gives
no right to use the name, except to say where the code comes from
(Apache License 2.0, section 6).
