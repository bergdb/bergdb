# P2 extended: a draft wording

A proposal for Frans, 2026-11-27, by the lead (lead-1127). Not a change of
010: only Frans edits the principles, and he does so after the design is
made to work (Frans, 2026-11-27 08:41). Written for design (e), one record
an action (031-06), which A1 became on 2026-11-27 (readme.md, section 8);
section 5 says what would have changed with (c).

Sources: 010-01's P2 as it stands; 031-05, section 4.3 (the first draft);
the Fable review of 031-05 (F2, F3, F4, F11); the decisions of 2026-11-27
(the part is the unit and has its own time, 11:16; a deterministic stream
for every write, 08:36).


## 1. The principle, short

> **P2. A deterministic stream.** What is appended to the stream is a
> function of the stream as it is and of the accepted user actions that
> follow, their contents, their times and their order, and of nothing
> else. A user action is a transaction, a setting, or a part of a
> `maintain()` call; each accepted action appends one record, decided from
> the stream before it and from the action. The database appends nothing
> else, by itself or in between. So the stream alone determines what
> follows, with no memory of how it was written: a restart, a stop or a
> crash between any two records changes no byte.

Second version, 2026-11-27 11:50, after Frans's answers: the stream as it
is comes first, and the user actions that follow it, as Frans asked;
"user action" is the precise word for the unit (W1); a partial append is
the name of the storage's one expected fault (W3). Third version, 12:08:
the stream is from the cut to the end, and no setting outside the stream
affects the bytes (section 2).


## 2. The terms

* **The stream** is the bytes from reclaim's last cut to the end, by
  position (Frans, 2026-11-27). A cut is decided in a record, so where
  the stream begins is in the stream too. Bytes before the cut that the
  storage still holds, and when it removes them, belong to the storage's
  implementation of the stream, not to the stream: nothing reads them.
* **A user action**, an action for short, is a call of the Core's `Db`
  that may append:
  * a transaction: `execute()`;
  * a setting that commits: `setStartupDistance`, `setRetainDuration`,
    `setReclaimInternalFraction`;
  * a part of a `maintain(budget)` call. A call does the parts that fit
    its budget; each part is an action of its own.
  * The Pub layer's index jobs (the build of a new index, the cleanup of
    a deleted one) are user actions too (Frans, 2026-11-27): the user
    starts them, and to the Core their commits are transactions like any
    other. When each of them comes among the other actions is part of the
    order, which is given.
* **Its time** is the database time the action gets when it begins, taken
  from the clock as a transaction's time is. It is an input, as the
  action's contents are.
* **Accepted.** An action is accepted when its record is in the stream,
  whole.
  * A call that returns has had its actions accepted. A call that is
    refused appends nothing.
  * After a crash, a stop or a failure inside a call, an action is
    accepted if its record is whole in the stream at the next start, and
    not otherwise.
* **The stream as it is** is whatever the storage holds when the actions
  begin: a new database's creation, the records of earlier actions, and
  what a partial append left (section 4, point 1). The principle asks
  nothing about how it came to be.
* **Nothing else is given.** No setting outside the stream affects the
  bytes (Frans, 2026-11-27: this is to be avoided): a setting that does is
  stored in the stream, by an action or at the creation, and a start
  reads it from there. One setting in the code breaks this, and one did
  until 2026-11-27 (section 4, point 5). When encryption comes back, its
  key is the one exception: the stored bytes depend on it, and it cannot
  be in the stream (Frans, 2026-11-27).


## 3. The statement

For a stream S as it is, and every sequence of accepted
actions A1 to An that follow, each with its contents and its time, there
is one stream S + (A1 .. An), and:

1. **One record an action.** S + (A1 .. An) is S + (A1 .. A(n-1))
   followed by one record, the record of An.
2. **Decided from the stream and the action.** The record of An is a
   function of the stream before it, S + (A1 .. A(n-1)), and of An: its
   contents, its time, and for a part, that it is a part. This includes all that the database adds to
   the record by itself: the index nodes it takes, and reclaim's copies,
   rows, tables and cut decisions. Nothing else decides a byte: not the
   clock after the action's time is taken, not timing or threads, not the
   cache, not durability, not memory that a start does not rebuild from
   the stream.
3. **Nothing in between.** Nothing is appended between two actions, and a
   start appends nothing. No work is ever owed to the stream: after every
   record the stream is complete as it stands.
4. **Interruptions.** Whatever restarts, stops and crashes come between
   the records, whatever calls are refused, and whatever the timing, the
   threads and the cache: the stream at any moment is S + (A1 .. Ak), A1
   to Ak the actions accepted until then.
5. **No memory.** S + (A1 .. An) is the same stream as (S + (A1 .. Ak)) +
   (A(k+1) .. An): the stream reached is all that the later actions depend
   on. This is what makes a stream a function of the existing stream and
   the actions, and it is point 2 said for a sequence.

Frans's goal of 2015-12-28, "a restart can be inserted between any two
transactions without affecting the bytes in the stream", is point 4 for
restarts and transactions. Point 4 extends it to stops and crashes, and
to every action.


## 4. The limits, stated

1. **A partial append.** The storage's one expected fault is an append
   that is written in part: after a crash, the stream's tail may hold part
   of a record, or zeros (035-01; 028-60). The recovery of a start keeps
   or drops such a tail by its rules (014-01), and the uninterrupted run
   has no such bytes. So point 4 holds for a crash between two appends.
   After a partial append, the stream as the start leaves it is the
   stream as it is, and the actions continue from it by the same function
   (Frans accepted this, 2026-11-27, W3).
2. **Acceptance need not be deterministic**, as in P2 today: the STM may
   refuse a transaction, a database under overload may refuse one, and a
   restart may change which requests are accepted. Runs with other
   accepted actions give other streams. A refused request leaves the
   stream unchanged and does not affect the bytes of later actions.
3. **The times are inputs.** The principle does not say which time an
   action gets, only that the stream is a function of it. A `maintain()`
   call is not one action: what a call writes depends on the times its
   parts get. A cut can become due in the middle of a call.
4. **The creation** of a database is not an action: its id is random and
   it has a time. It is part of the stream as it is (031-05, Q5).
5. **Settings outside the stream that affect the bytes:**
   * the crypto key, until 2026-11-27. Encryption left the API in 2026.4
     (020-28), and its code was kept for a later design (017-10) and used
     by tests. Frans had it removed (028-69, `1809e04c`);
   * the reclaim step reserve (`DbBuilder.reclaimStepReserve`), which
     decides where a step splits, at its default too (review-fable.md,
     F7). Open as 028-68, decided in the landing's step 2 (readme.md,
     section 9).


## 5. If A1 had become (c)

With (c), an action appends its own record and then the maintenance it
makes due, as records of their own, and a start appends what a crash or a
stop left due. Then:

* point 1 reads "one or more records, the action's own first";
* point 3 reads "a start appends only what the last action left due";
* point 4 reads "the stream is a prefix of S + (A1 .. Ak) that ends at a
  record boundary, and the next start completes it to S + (A1 .. Ak)".

The short text of section 1 loses "each accepted action appends one
record" and "changes no byte", and gains the completion by the start.


## 6. How it is checked

* **Tested:** a crash and a stop at every record boundary, inside commits
  and inside `maintain()` calls, the continued stream compared with the
  uninterrupted one; the number of records equal to the number of
  accepted actions; `StreamDigest` and `RestartInvariance`; concurrent
  runs replayed by one thread at the logged times.
* **To be proved (Lean):** points 1 to 4 for the model, where an action is
  one transaction that `step` appends: `T1_crash`, `T2_restart` and
  `T12_restartCut` as they are, and a theorem that the plan depends only
  on what a restart preserves.
* **Stays tested:** that Java's plan reads only the stream before the
  record and the action; the clock (every record's time later than every
  time handed out); torn records.


## 7. Open for Frans

* **W1.** Answered (Frans, 2026-11-27): "action", or "user action" where
  precision is needed; the index jobs' commits are user actions.
* **W2.** Whether the setters stay actions of their own (as here) or
  become `execute()` calls in the API (031-05, Q1 (b)).
* **W3.** Answered (Frans, 2026-11-27): accepted, under the name of the
  fault, a partial append.
* **W4.** Limit 4: the creation as part of the stream as it is (here), or
  as action 0 with its id and time as inputs.
* **W5.** Whether the README's sentence ("The same transactions in the
  same order give the same bytes") is reworded with it.
* **W6.** Answered (Frans, 2026-11-27): the crypto code is removed
  (028-69); on its return the key is the one exception.
* **W7.** The step reserve: 028-68 (a constant, a value stored at the
  creation, or a setting with a record of its own).
