017-02, code-only transactions. What they are and whether they are new
=====================================================================

Created 2026-11-04 by Claude (Opus 5.5) for Frans Lundberg, for 017-02.
Status: exploration.

BergDB's read-write transactions are plain Java code: an `Action` that
reads, computes and writes, with no query language. They rest on
optimistic validation (what the code and Frans's notes call the STM
approach) and on as-of reads of the multiversion map. This report finds
the early descriptions, explains the mechanism as the code has it in
2026, compares it with other work (sources in
[literature.md](literature.md), "Transactions") and judges what is new.
006-11 (Codex, 2026-10-30) measured the STM's value and cost; this report
does not repeat that.


# 1. In short

* The description Frans remembers is the "An RW transaction" example of
  KissDB's get-started page, a payment between two accounts in an
  anonymous `Action`: `get-started.html` and `GetStarted4.java` in
  release 2013.1.130606 of 6 June 2013 (section 2). The design is older:
  August 2008 (STM and MVCC, "just Java"), January and February 2012 (the
  read set, the read time, two-level STM), October 2012 (the Bank demo and
  the `Action` and environment API).
* The mechanism: the first read fixes a read time, every read of the run is
  an as-of read at that time, the keys read form a read set of 64-bit
  hashes, and the commit, under the single writer lock, refuses the
  transaction if any read key was written after the read time; the
  library then reruns the code. Only the effects (the keys and values
  written) go to the stream.
* For the Pub API, whose action can make only point reads, this gives
  serializability in commit order, provided every read goes through the
  environment and the action has no outside effects (section 3.4). Not
  proved.
* None of the parts is new, and the combination is not new either:
  JVSTM with the Fénix framework (Java, versioned boxes, 2005 to 2008),
  Hyder (CIDR 2011), FoundationDB (alpha January 2012), Omid (EuroSys
  2012) and Convex (2022 to 2024) have it, each with differences. What may
  be BergDB's own is a design point, not a principle: an embedded Java
  store whose transaction snapshot is the same as-of mechanism as its
  long-retention historic queries, a fixed-size binned hash set as the
  whole conflict memory, and a stream of effects that makes the replay of
  the startup section independent of the code.
* Worth a section of a BergDB paper and a blog post. A short workshop
  paper only with a proof of the isolation level (Lean), range reads that
  are safe against phantoms, and measured rerun rates.


# 2. Where the description is, and its history

All in F1-007 (repo f1, `a/007-bergdb-261012/`, Frans's archive), unless
the line says otherwise:

* **2008-08-04 to 2008-08-16**, `bergdb/doc/log-old/2008-2011-log.txt`.
  Frans studies STM and MVCC and decides for the "STM approach" with MVCC:
  no transaction description language, "just Java", and the transaction's
  effects, not its description, sent between replicas. He notes the
  limits: long read transactions over hot data (summing all balances of a
  bank) and hot spots (a counter increased by every payment), and that
  MVCC with a retention of, say, 30 minutes would serve the first. He
  wrote then that STM for databases not entirely in memory seemed "a
  brand new approach"; section 5 says what is known of that.
* **January 2012**, `bergdb/doc/2012/2012-01-thoughts-on-transactions.txt`.
  A transaction is read, compute, write. An STM transaction "can be viewed
  as a write-only transaction with an additional set of keys and a time
  (the read time)"; if none of the keys was modified after the read time,
  the writes are applied, else the client rereads and retries. The
  modification record: 64-bit key hashes in 4-second intervals, with a
  limit on how long a read-write transaction may take.
* **January 2012**, the self-indexed streams draft v5 (docs/sources),
  section 3.3: a bank transfer, "move all money from account B to account
  A", as the example of why a transaction in the stream must be
  decomposable into self-sufficient item transactions: "set B to 0 and A
  to 30" can be replayed on a part of the state, "add B's balance to A"
  cannot. That is the link between the two ideas (section 3.5).
* **5 February 2012**, `bergdb/doc/2012/2012-02-two-level-stm.txt` and the
  log of 120206 to 120209 (`log-old/2012-log.txt`): key-level STM for the
  client, node-level STM inside the database; "first tests of two-STM
  approach. They work."
* **October 2012**, `bergdb/doc/2012/2012-10-notes.txt` and
  `2012-09-notes.txt`: the Bank demo application, "to find required DB
  features", with `getCustomer(ReadInterface ri, String id)` used both in a
  read and in an rw `Action`; `2012-09-index.txt` and `2012-11-notes.txt`
  show payments with secondary indexes. 2012-10-16 (`2012-log.txt`):
  virtual keys, "wonder if it is novel?" (section 3.3).
* **6 June 2013**, the 2013 to 2017 Git bundle (`bergdb-git.bundle`),
  commit `f3d750e`, "RELEASE 2013.1.130606! Demo code and
  get-started.html": `KissDB/src/kissdb/pub/doc-files/get-started.html`,
  section "An RW transaction", and `KissDB/src/kissdb/demo/GetStarted4.java`.
  Two accounts of 100; the action reads both, throws if the first has less
  than the amount, moves 30 and sets both; "the run method may execute
  more than once if there are many concurrent users of the database. This
  is due to the STM (software transactional memory) approach". The same
  page says of a write transaction of two objects that it is "comparable
  to the highest SQL isolation level: serializable" and that a user will
  "never ever have to deal with phantom reads". The test
  `KissDB/src/kissdb/test/Concurrency.java` (first commit `76c4792`, the
  same day) runs concurrent payments and a payment counter.
* **2013-09 and 2013-10**: `bergdb.test.manual.PaySweden` (`47a5c5f`) and
  "PayDemo works, 1M accounts" (`fa2c69d`, 2013-10-16).
* **Today**, in this repository: `Action`, `RwEnvironment`,
  `Connection.rw`, `RwTransaction`, `RwEnvironmentImp` (`java/src/bergdb/pub`
  and `pubimp`), and `Db.stmCheckConflicts`, `KeyModSet` in the Core. The
  get-started page and the demo classes are not in the 2017 source that
  this repository continues from.

So the Java code description is of 2013, from a design of 2012 and a
decision of 2008. Frans's "2012 era" fits: the API with `Action` and the
environment is in the October 2012 notes, and the page was released in
June 2013.


# 3. The mechanism

From the code as of 2026-11-04.


## 3.1 How a transaction reads

* The application calls `connection.rw(action)`. `RwTransaction.executeRw`
  calls `action.run(env)` on the caller's thread, outside the writer lock.
* The first read in the run (`env.get` or `env.exists`) reads at the latest
  lookup time and remembers that time as the read time. Every later read
  of the same run is an as-of read at the read time: a historic lookup in
  the multiversion map, the same lookup a `Connection` makes with
  `setLookupTime`. So the run sees one consistent snapshot, takes no lock,
  and no writer waits for it.
* Each read adds the 64-bit hash of its key to the read set, also when the
  key is absent. The public `RwEnvironment` has point reads only: no range
  reads and no index iterators. Internally, index maintenance reads with
  `getMany` and adds the hashes of the keys it gets, plus virtual keys
  (3.3).
* Writes (`put`, `delete`) are only recorded in the environment. Outputs
  for the caller (`setOutput`) too.


## 3.2 How it commits

* After the run, the environment adds the index entries, builds a Core
  transaction (`Trans`) with the read time, the read hashes and the
  writes, and calls `Db.execute`.
* Before the go point and under the one writer lock, `stmCheckConflicts`
  asks the key modification set, for each read hash, whether a commit
  later than the read time wrote that hash. If one did, a
  `RerunException` refuses the transaction; nothing has changed (docs/levels.md,
  section 3).
* If none did, the transaction gets its time, its writes go into the
  multiversion map, the time becomes a lookup time, the written hashes go
  into the key modification set (`stmRecordKeys`), and the record is
  appended to the stream: the keys and values written, not the code.
* On a refusal, `executeRw` clears the outputs, waits (10 ms, doubled up to
  about 10 s, no limit on the count) and runs the action again from the
  start, with a new read time.
* A write-only transaction (`c.w().put(...).execute()`) has no read set
  and never conflicts.


## 3.3 How conflicts are detected

* `KeyModSet` holds (time, key hash) pairs of recent commits in 4 rotating
  bins of 32,000 additions each (128,000 in all). Its reach counts writes,
  not seconds: a burst of writes shortens it.
* A read time older than the oldest bin is a conflict (the safe side), and
  so is a read time before the last recovered commit after a restart
  (005-70). A hash collision gives only a false conflict.
* Virtual keys: keys that are never stored, whose hashes are written and
  read only to make transactions conflict. Adding an index writes the
  virtual key of each directory it covers; storing an object reads the
  virtual key of its directory; so an object stored while an index is
  added is rerun. This is the mechanism of FoundationDB's explicit
  conflict ranges [memory], and the means for range safety in section 6.


## 3.4 What isolation it gives

My reading, not proved:

* For the Pub API: serializable in the order of the commit times. Each
  committed rw transaction read the state as of its read time, and no key
  it read was written between its read time and its commit, so it would
  have read the same values at its commit time. Write skew is prevented,
  since a read key's later write is a conflict whether or not the
  transaction writes it. Readers outside transactions read snapshots at a
  lookup time.
* Conditions: every read of the action goes through `env` (a read through
  the `Connection` inside `run` is not validated); the action has no
  effects outside the database (a rerun repeats them); it does not depend
  on anything but its reads and its inputs.
* No phantoms through the Pub API, but only because the action cannot
  scan. That is a limit of what can be written: "sum all balances, then
  write" cannot be a validated transaction. The 2013 page's claim of no
  phantom reads holds in that sense.
* The Core API (`Db.trans().lookupTime(t).keyRead(k)...`) leaves the read
  time and the read set to the caller (006-11, section 2).
* Strict serializability, that a transaction sees every commit that
  returned before it began, also depends on when a commit becomes visible
  (015-27) and is not claimed here.


## 3.5 What the STM and the history each contribute

* The history gives the snapshot. Without as-of reads, the run would need
  locks or would read a mix of states, and validating it would need a
  version per read value (as in TL2 or JPA). With them, the run reads one
  state without locks, and a read never waits for the writer. The
  retention also means a long run never fails for lack of old versions;
  only the key modification set's reach limits it, and the two windows are
  sized apart.
* The STM gives isolation for writes that depend on reads: the read set,
  the check at commit, the rerun. It lets application work run in
  parallel outside the writer lock: 006-11 measured 1.7 times the
  throughput with about 9 microseconds of computation per transaction and
  6.9 times with about 94, against a serial control (006-11, section 10).
* The stream gets only the effects. The code runs, perhaps several times,
  in the application's process, and only the committed run's writes are
  stored. That makes every stored transaction self-sufficient in v5's
  sense ("set A to 30", not "add B's balance to A"), so startup can rerun
  the tail's transactions on the state as of the startup pos without the
  application's code, and the rerun is deterministic whatever the code
  did. Prevayler, acid-state and Calvin store the command and must run
  deterministic code at recovery; BergDB does not.


# 4. Comparison

(a) code in the host language, rerun on a conflict; (b) as-of snapshot
reads in a durable multiversion store; (c) read-set validation at commit
against later commits. "hist." means that the same versions also serve
user queries of the past.

| System | Year | (a) | (b) | (c) |
|---|---|---|---|---|
| Kung, Robinson | 1981    | no                | no                      | yes                 |
| POSTGRES       | 1987    | no                | yes, hist.              | no                  |
| GemStone/S     | 1980s   | Smalltalk         | snapshot view           | write-write only    |
| JVSTM, Fénix   | 2005–08 | Java              | in memory               | yes, one lock       |
| Clojure STM    | 2008    | Clojure           | in memory               | write-write only    |
| Percolator     | 2010    | client            | Bigtable                | write-write only    |
| Hyder          | 2009–11 | in-process        | the log is the database | read set in the log |
| FoundationDB   | 2012 α  | retry loop        | 5 s window              | ranges              |
| Omid, WSI      | 2011–12 | client            | HBase versions          | bounded oracle      |
| Datomic        | 2012    | tx functions      | yes, hist.              | by hand (`cas`)     |
| Xodus          | 2014    | Java              | snapshots               | any commit          |
| CockroachDB    | 2015 on | client SQL        | yes, hist. (`AS OF`)    | read refresh        |
| Convex         | 2022–24 | server TypeScript | internal only           | ranges              |
| BergDB         | 2012–13 | Java              | yes, hist.              | key hashes, binned  |

The rows are summaries from literature.md, at the tags given there; most
of the pre-2012 rows are [memory] and must be read before they are cited.

What each closest relative lacks against BergDB, briefly:

* JVSTM and Fénix: versions in memory only, kept while a transaction
  needs them; durability in MySQL; no historic queries.
* Hyder: a distributed shared log on flash, a copied path per transaction;
  the same principle, a different storage method.
* FoundationDB: a distributed client and server, versions for 5 seconds,
  no historic queries; range conflicts (no phantoms).
* Convex: the code runs in the server's sandbox, which makes reruns safe;
  range read sets; no historic queries for users.
* Datomic: as-of is its centre, but there is one transactor and no
  automatic validation of a peer's reads.


# 5. What is new

Known, with the earliest source found: backward validation in one
critical section (1981); versions that serve both concurrency and the past
(1987; `AS OF` on a transaction, 2005); Java transactions on versioned
data, validated under one lock, rerun, write-only never conflicting
(JVSTM, 2005 to 2006); hashed signatures of recent writes (RingSTM, 2008);
a bounded conflict memory where an old snapshot means conflict (Omid
2011, FoundationDB); all three parts in a durable, append-only
multiversion store (Hyder, 2011). Frans's 2008 note that STM for a
database not entirely in memory was new was close to the edge then: JVSTM
on MySQL was in production, but it was not published as a database.

Possibly BergDB's own, as a combination and a design point:

1. An embedded, single-process Java database in which the rw
   transaction's snapshot and the user's historic queries are one
   mechanism, with a long retention, so that versions never limit a
   transaction and the conflict memory is sized apart.
2. A conflict memory that is only a fixed-size, time-binned set of key
   hashes, independent of the database's size and of the number of open
   transactions.
3. Code-only transactions on top of a stream of effects, so that the
   tail's replay at startup (the self-indexed stream) needs neither the
   code nor deterministic code. This is the point that ties the
   transaction model to the storage method, and the one I would put in a
   paper.

None is a new principle. They are worth stating and measuring, not worth
a research paper of their own.


# 6. Is it worth a publication

* **A section of a BergDB systems paper**: yes, one or two pages, with
  point 3 of section 5, the isolation level stated with its conditions,
  006-11's measurements, and an honest related-work paragraph (Kung and
  Robinson, JVSTM, Hyder, Omid, FoundationDB, Datomic, Convex).
* **A blog post or essay**: yes, and the easiest to do well. A possible
  story: a payment in eight lines of Java, how it works, and how a design
  of 2012 has the shape that FoundationDB and Convex reached; with the
  dated notes as evidence and without claiming priority over JVSTM or
  Hyder.
* **A short workshop paper** (PaPoC, MPLR; [options.md](options.md)): only
  with three things that do not exist yet:
  1. A proof, in Lean, of the isolation level: a small model of the read
     time, the read set, the binned key modification set with its reach
     and the "older than the reach is a conflict" rule, and a theorem that
     every committed history is serializable in commit order. Small next
     to the existing model, and the kind of result a reviewer can check.
  2. Range reads in `RwEnvironment` that are safe against phantoms: for
     example a virtual key per directory, written by every put and delete
     in the directory and read by a scan of it (conflicts at directory
     granularity), or finer, per key-prefix bucket. Its cost measured.
  3. Rerun rates and tail latency under contention (hot accounts, a
     payment workload like TPC-C's Payment, the 2008 "counter increased
     by every payment"), the false-conflict rate against the set's size,
     and a retry policy with a first quick rerun instead of 10 ms.
* **A research paper on the transactions alone**: no; the novelty is not
  there.
