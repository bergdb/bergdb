# 031-06. The history of reclaim's own records

A history study of 2026-11-27 (09:19 to 09:35, read-only): why reclaim,
which does its work at the application's commits, writes it in internal
transactions with records of their own, after the user's record, and not
in one record with the user's writes. No reason was ever recorded: the
separate records follow from the design of July 2012, in which reclaim
is a "process" that could run in a thread or piggyback, and the
one-record alternative was not weighed for reclaim before 2026-11-25. For
the index nodes' writes it was: on 2014-11-01 Frans merged them into the
user's record.

The sources are Frans's notes and development logs of 2008 to 2016, the
Git history of 2013 to 2017 (the first commits of this repository), and
this repository's items, code and development log. The passages of
Frans's notes and logs are quoted with his approval (2026-11-27); two
spelling slips are corrected.


## 1. Timeline

* **2008-08-02** (Frans's development log of 2008 to 2011):
  deterministic transactions are a goal (010-02, under P2). Nothing on
  reclaim.
* **2009-11-03** (the same log): the first reclaim idea, a "maintenance
  task that re-writes old data". It writes "W*0.5 amount of data to
  refresh old data and W to write new data" in "small computational
  pieces", maybe "embedded in calling thread". The rewrites and the new
  data are counted as separate amounts. Nothing on records.
* **2012-02-06** (Frans's log of 2012 and his notes of February 2012 on
  a two-level STM): an "internal transaction" here means the node-level
  STM half of a user transaction. This is another sense of the word, not
  reclaim.
* **2012-05** (Frans's notes of May 2012): "DONE! Deterministic stream"
  for SET operations (031-05, section 13).
* **2012-07-17** (Frans's notes of July 2012 on space reclaim; his log's
  entry of the day: "Stream space reclaim. On paper."): the algorithm and
  its variations: a separate thread, a low-priority thread, run at low
  load, or "piggyback" on existing transactions. Reclaim's writes are
  limited "to a factor of the ordinary transaction size", "5 MB of
  reclaim transactions" per "10 MB of ordinary transactions".
* **2012-07-23** (the same notes, "Algo fix"): 'a separate space reclaim
  "process" (separate thread or piggy-back on other transactions)'. A
  rewritten KV "will get the current DB time as its new timestamp". The
  work is paced so that "the rewrite transaction will not occupy more
  than 40% of the stream". The iteration table is kept as KVs under an
  internal prefix.
* **2012-08-08 to 08-13** (Frans's log of 2012 and his notes of August
  2012, "DONE! Stream space reclaim"): SpaceReclaim implemented in
  KissDB. The code of 2012 is not in Git: the repository of before
  2013-06-06 was kept as a backup, which is not among the sources.
* **2013-01** (comments marked "1301 Frans" in `Reclaim.java` and
  `Db.java`): the call of `transactionCompleted()` moved inside the
  write lock "to KISS the reclaim stuff". On 2013-01-29 the end comment
  of the class: SpaceReclaim listens to
  `DB.TransactionListener.transactionCompleted()`, "runs piggyback in the
  thread that executes an ordinary external transaction", and is "quite
  independent from the rest of the code". Also 2013-01-25 (Frans's notes
  of January 2013): the evict design prefers "Piggyback - no background
  thread. Keeping with 'tradition'."
* **2013-06-06** (commit 1f4d0b6e, the first commit of the Git history,
  `KissDB/src/kissdb/core/Reclaim.java` and `Db.java`): reclaim as built.
  Each step is a `Trans` with `keyRead`, `readTime` and
  `isInternal = true`, committed with `db.execute(t)`. A
  `RerunException` drops the step: "will be run again since lastKey not
  updated". The table goes in its own internal transactions. The pacing
  sums the record sizes of internal and external transactions separately
  (`gotInternal`, `gotExternal`, `t.lastPos - t.tpos + 1`). The
  `TransactionListener` Javadoc: "SpaceReclaim needs to run database
  transactions to fulfill its need."
* **2014-09-27** (commit a4e42d1f, "Separated kv transactions and node
  transactions"; Frans's development log of the day, "DONE! Separate kv
  and node transactions"): on the kv2 branch the index nodes' writes got
  records of their own. The 1301 comment was reworded in this commit to
  "However, fundamentally, it does not have to belong to the block."
* **2014-10-31** (Frans's development log): reruns at startup use
  `Db.execute()`, and the "internal state" (Dag, KvTransSeq) must be the
  same before and after a restart. Frans's notes of the third quarter of
  2014: in a rerun, "Reclaim is not used". Reclaim's records are rerun
  like any others.
* **2014-11-01** (Frans's development log): DECISION, kv and index
  storage merged "into one transaction. Like it was before." This is the
  only recorded weighing of one record against separate records, and it
  is about the index writes.
* **2015-12-28** (Frans's notes of the fourth quarter of 2015): "a
  restart can be inserted between any two transactions without affecting
  the bytes in the stream" (P2's source). The same notes plan to
  "Separate k-trans and i-trans", then on 2016-03-17: "maybe not?"
* **2016-03-03** (Frans's document on the algorithms of 2015, section
  13): "An index transaction may be executed as an add-on (piggy-back) to
  a kv transaction. It could also be executed independently of kv
  transactions, initiated by the database itself."
* **2016-04-01 and 2016-05-05** (Frans's notes on startup): "two types of
  transactions: user transactions [...] and internal transactions
  initiated by the database itself". An internal transaction "does not
  modify the external database state as visible to a database user".
  This is the index take; the algorithms document of 2015 puts "space
  reclaim [...] not in the scope".
* **2017-08-01**: the last commit of the old history. Reclaim is
  unchanged in structure.
* **2026-10-13/14** (the development log, `docs/log.md`, 2026-10-13;
  commits 0257e0ba and 0eb07c8f): the 2017 reclaim, never tested with
  restarts after a cut, was reworked: ten bugs fixed, its state put in
  the table, the touch added. The separate records were kept without
  discussion. The allowance now counts the bytes rewritten, no longer the
  internal records' sizes ("its own table writes used the allowance").
* **2026-10-16** (001-07, section 2.1): the Lean model's mapping. "Every
  executed transaction is a record", with three kinds (user
  transactions, steps, table stores) and "zero to five internal records"
  between two user transactions. The model followed Java; it did not
  choose.
* **2026-10-19 and 2026-11-05** (005-02; 015-55): 1,024 top node
  ordinals and 1,024 database times are kept for "the internal
  transactions that run after a user transaction".
* **2026-10-25** (005-42, A1 and B2; 021-17 later): `transactionInfo()`
  gives the user's KVs only and recognizes "a record of reclaim's".
  "Reclaim's steps and its table are transactions of their own, and each
  holds a KV under `/#i/dreclaim/`, which tells them apart."
* **2026-11-05** (015-53): a `stop()` during reclaim's work after a
  commit is caught (`DbStoppingException`), and the user's transaction
  stays committed. 015-50: a step too large for the record limit failed
  the database at every restart, and was fixed by splitting steps.
* **2026-11-12** (024-32, section 2.8): `maintain()`: "Reclaim's steps in
  the model do not come with user transactions [...] Nothing ties a step
  to a user record." So `maintain()` needed no new kind of record.
* **2026-11-13** (027-13, section 1.1): "Reclaim writes only in
  transactions of its own, each with its own time", a description of the
  code with no reason given.
* **2026-11-19** (028-26; 027-13, section 1.4, 4b): a step needs a
  second record, "the row again", because "the row is a value of the
  transaction whose dirty bytes it counts". A record cannot hold a count
  of itself.
* **2026-11-25** (028-54; 031-03, section 5): the crash between a user
  record and its maintenance records is registered (028-54). In 031-03,
  "w in the application's own record" was weighed and not built, because
  of 027-13's rule.
* **2026-11-26** (031-05; its independent review, `review-fable.md`,
  answer 4): Frans's goal is every write a function of the stream and the
  user actions. The review said that maintenance inside the user's
  record "would end the question, but redesigns the step: not now."


## 2. The quotes

Frans's own words first, then the statements of 2026.

* Frans's development log of 2008 to 2011, 2009-11-03:

  > To make sure old data is finally removed from DB, we can have a
  > maintenance task that re-writes old data from back in the TStream.
  > [...] We write W*0.5 amount of data to refresh old data and W to
  > write new data [...]. NO checkpointing - only continuous operation by
  > small computational pieces at a time. No stop-the-world of course. No
  > maintenance really, it can even be embedded in calling thread so no
  > threads need to be started by KissDB itself - it would act as a
  > "passive" library.

* Frans's notes of July 2012 on space reclaim, 2012-07-17:

  > * The algo could run "piggyback" on existing transactions. This
  > allows a deterministic stream (good for testing) and guaranteed zero
  > CPU load when DB not used. Having no background threads is a tempting
  > proposal.
  >
  > * The amount written to stream by this reclaim algo should be
  > limited. It seems reasonable to limit it to a factor of the ordinary
  > transaction size. For example, if 10 MB of ordinary transactions have
  > been added, maybe 5 MB of reclaim transactions would be allowed
  > (50%).

* The same notes, 2012-07-23, two passages:

  > * Have a separate space reclaim "process" (separate thread or
  > piggy-back on other transactions). Let 40% (example) of the
  > transaction size appended to the stream be dedicated to this process.

  > Do this iteration "slowly" in a manner the rewrite transaction will
  > not occupy more than 40% of the stream.

* A comment in `Reclaim.java` of 2013-01-29, the class's end comment
  (in the first commit, 1f4d0b6e of 2013-06-06, and still at the end of
  `java/src/bergdb/core/Reclaim.java`):

  > 130129 Frans. SpaceReclaim is setup to listen to
  > DB.TransactionListener.transactionCompleted() events from DB.
  > SpaceReclaim uses these calls to run its methods. Current implement
  > does not start new threads, but runs piggyback in the thread that
  > executes an ordinary external transaction.
  >
  > This functionality is quite independent from the rest of the code.
  > It will be possible to easily try different reclaim algorithms :-).

* A comment in `Db.executeInner` of January 2013 (in the first commit,
  1f4d0b6e), as reworded in the commit a4e42d1f of 2014-09-27, and so
  today in `java/src/bergdb/core/Db.java`:

  > 1301 Frans. The below line moved to inside the synchronized
  > (writeLock) block to KISS the reclaim stuff. However, fundamentally,
  > it does not have to belong to the block.

* The Javadoc of `Db.TransactionListener`, in the first commit
  (2013-06-06) and unchanged today:

  > Exceptions specified below are allowed since SpaceReclaim needs to
  > run database transactions to fulfill its need.

* Frans's development log, 2014-11-01, on the index nodes' writes:

  > Sat. I am considering merging storeKv / storeIndex transaction
  > storage together into one transaction. Like it was before.
  > In a way, I like the idea of decoupling kvTransactions from internal
  > indexTransactions due to startupPos increase. The piggyback approach
  > is not the only possible approach; decoupling would allow
  > experimenting with other approaches. For example: write index
  > transactions in background when db usage is low. But, putting them
  > together reduces some variability and might be easier for me to
  > handle; especially the startup transaction reruns.
  >
  > DECISION: Go for merged storeKv/storeIndex nodes approach. A more
  > decoupled approach could be entertained once everything works.

* 027-01's `sis-model.md`, section 2 (2026), on the same point:

  > In the 2017 code, this is the user transaction with its piggybacked
  > internal transaction, which writes index nodes. startup.md describes
  > them as two transactions; one record per transaction is simpler and
  > loses nothing.

* 027-13, section 1.1 (2026-11-13):

  > **Internal transactions.** Reclaim writes only in transactions of its
  > own, each with its own time; user transactions are refused in the
  > last 1,024 times and top node ordinals, kept for them. Reclaim reacts
  > to user transactions only.

* 031-03, section 5 (2026-11-25):

  > **w in the application's own record.** Reclaim adds its table to the
  > first user transaction after a begin: atomic, no window. But a user
  > transaction then holds a key of reclaim's, against "reclaim writes
  > only in transactions of its own" (027-13, section 1.1). Not built.

* 031-05's independent review, `review-fable.md`, answer 4 (2026-11-26):

  > Maintenance inside the user's own record would end the question, but
  > redesigns the step: not now.


## 3. The reasons, one by one

Each possible reason is one of three: documented (a source states it as
a reason), visible in the code or the history only (no text gives it as
the reason), or neither.

* **A process that could run in a thread or piggyback: visible in the
  notes, close to documented.** 2012-07-23: 'a separate space reclaim
  "process" (separate thread or piggy-back on other transactions)'. A
  thread has no user transaction to ride on, so its rewrites must be
  transactions of their own. The listener design of 2013 ("quite
  independent from the rest of the code"; "fundamentally, it does not
  have to belong to the block") keeps reclaim outside the user's commit.
  When piggyback was chosen, the structure of transactions stayed. The
  notes describe the process, not the layout of the records: no text
  says that this is why the records are separate.
* **Modularity, to try other reclaim algorithms: documented as the
  reason for the listener (2013-01-29).** Not stated as the reason for
  separate records.
* **Pacing by record sizes: visible (the notes of 2012, the code of
  2013).** The share of "reclaim transactions" against "ordinary
  transactions" was measured as the sizes of separate records
  (`Iteration.gotInternal` and `gotExternal`, 2013 to 2017). In one mixed
  record that split is less direct. Since 2026-10-13 the allowance counts
  the bytes rewritten, so this reason is gone.
* **Refusals and the STM: visible in the code of 2013; no text gives it
  as the reason.** The step was an optimistic transaction of its own:
  `keyRead`, a `readTime` at the step's lookup, and on `RerunException`
  "will be run again". So a conflict of reclaim's never refused the
  user's commit, and a refusal of the user's never touched reclaim's
  step. Today every refusal before the go point applies only to user
  transactions (`checkSize`, `refuseIfTopOrdinalsUsed`,
  `checkDirtyNodes`, `transformValues`, the core-key and key-bytes checks
  in `transformKeys`). Reclaim's records come after the user's go point,
  where any failure fails the database (015-50 was such a case).
* **A step's put colliding with the user's write of the same key:
  neither; never mentioned.** Today a transaction holds one KV a key
  (`transformKeys`, 024-16; `putKvs`). The step's scan reads the state
  after the user's commit (`GetMany` at `Long.MAX_VALUE`, 026-05). In
  one record, the step would have to skip the user's keys.
* **Times (tStart, a rewrite's own time): neither.** The fix of
  2012-07-23 only says that a rewrite gets "the current DB time". In one
  record it would get the user's time, and nothing in the notes objects
  to that. The 1,024 kept times and ordinals (015-55, 005-02) are a
  consequence of separate records, not a cause.
* **Positions that name records: visible in the code of 2026.** pStart
  is the length after the user's record. pEnd is the step's own
  position, and pSafe the length after the call's internal records
  (015-54). The "row again" (028-26) exists because "the row is a value
  of the transaction whose dirty bytes it counts". A record cannot store
  facts about itself that are known only once it is written, so some of
  reclaim's stores need a later record in any design. This is a
  constraint of 2026, not the original reason.
* **getTrans, transactionInfo and replication (one record, one user
  transaction): a consequence of 2026.** 005-42 (2026-10-25) and 021-17
  depend on reclaim's records being their own: they identify them by the
  `/#i/dreclaim/` KV. The old notes do not tie the separate records to
  `getTrans`. Replication was removed on 2026-11-04 (005-11), so it is no
  obstacle today. How it treated internal records was not checked.
* **`maintain()` without a commit: a consequence of 2026 (024-32).** The
  separate records made `maintain()` cheap: "Nothing ties a step to a
  user record". It still needs records of its own in any design.
* **P1, the 20 ms pause: not a reason (visible in the code).** The
  internal records are written under the same write lock in the same
  `execute()` call, before it returns (`Db.executeInner`,
  `reclaimTransactionListener.transactionCompleted`). The pause is the
  same with one record or several. 007-07: "a commit that carries a step
  is slower".
* **Determinism (P2): documented, but for piggyback, not for separate
  records.** 2012-07: piggyback "allows a deterministic stream". The
  notes do not say whether piggybacked work should share the user's
  transaction.


## 4. Was the one-record alternative weighed?

* For reclaim, 2009 to 2017: not found. The notes, the logs and every
  commit message of the old history were searched ("piggy", "internal
  trans", "reclaim", "decoupl", "same record").
* For the index writes: yes, and one record won (2014-11-01, section 2:
  less variability, easier startup reruns). The startup notes of 2016
  still describe two transactions. 027-01's `sis-model.md` (2026): "one
  record per transaction is simpler and loses nothing."
* In 2026: only 031-03 (2026-11-25, for w only, not built because of
  027-13's rule) and the independent review of 031-05 (2026-11-26, "not
  now"). Neither looked into the reasons, and no item gave the
  alternative a section with its costs.


## 5. What one record takes today

The prototype of one record an action is 031-06's readme: the design as
built (section 2), its evidence (section 4) and its costs (section 5).


## 6. Not found

* The KissDB code of August 2012, the first SpaceReclaim: the Git
  repository of before 2013-06-06 was kept as a backup, which is not
  among the sources. The notes of July 2012 and January 2013 cover the
  design.
* Frans's paper notes: his logs refer to "paper notes" several times
  (for example 2014-09-27); they are not among the sources.
* Any reason, at any date, why the rewrites are not in the user's
  record. Searched: all of Frans's notes and logs of 2008 to 2016, the
  old Git history's code and messages, this repository's items,
  `docs/log.md`, the Java sources and the Lean model. The repository's
  history before it went public (029) has the same mentions as today's
  tree.
* Frans's document on the algorithms of 2015 and his paper on
  self-indexed streams were searched for "piggy", "internal" and
  "reclaim" only. His notes in word-processor files were not read.


## 7. The end of the separate records

Frans decided on 2026-11-27 that every accepted action appends exactly
one record (031-06, section 8): a commit's record holds the maintenance
that reclaim owes, and reclaim's records of their own end.
