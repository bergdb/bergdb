005-12. Transaction outputs: study them, then test or remove
===========================================================

Status: open. Kind: investigate. Created 2026-10-20.


The task
--------

In Frans's words (2026-10-20): have a look at transaction outputs; study
them, and then either ensure that they are tested and work, or remove
them. The entry says why the feature is valuable, if it is.

Found in 005-10, where the Pub API's `RwEnvironment.setOutput` and
`Transaction.getOutput` came up as unused (G1): nothing in the repository
calls them, nor their implementations. They stay until this entry is done.


What they are
-------------

A read-write transaction runs an `Action` (`Connection.rw(action)`). The
action reads through its `RwEnvironment` and writes through it; it can
also call `env.setOutput(name, value)`. When the transaction has
committed, the caller gets the values with `transaction.getOutput(name)`
(`RwTransaction`; a `WTransaction`, a write-only transaction, has none and
throws `NoSuchObjectException`). The outputs live in memory only; they are
not written to the database.

An action may run more than once: the transactions are optimistic (an STM,
software transactional memory; `Action`'s Javadoc), and a run whose reads
were changed by another transaction before its writes are applied is run
again (`RerunException`). Before each new run the outputs are cleared
(`RwEnvironmentImp.clearOutput`), and the caller gets those of the run that
committed (`RwTransaction`, `rw.output = env.getOutputMap()`).


Why it can be valuable
----------------------

It is the way to return a result from a transaction that may run more
than once. A value that the action computes from what it read, such as
the balance after a payment, an id it chose, or whether a condition held,
is only right if it comes from the run that committed. A variable of the
caller that the action sets can hold a value from a run that was thrown
away, unless the action resets it at every run; outputs do that by
construction. The source keeps Frans's note of 2013-05-30, in
`RwEnvironment.java`: "Added setOutput(). It *is* needed. Makes code less
ugly." (It had been removed on 2013-04-16, "I was in doubt".)

It is not transaction metadata stored with the transaction, such as who
ran it; Frans found that idea interesting (2026-10-20). The transaction
time is there already (`Transaction.getTime`,
`Connection.transactionInfo().time()`); more would be a feature of its
own, perhaps an entry here.


Questions
---------

1. Does it work: an output set in an action is the caller's after commit;
   after a rerun, only the committed run's outputs are there; a name that
   was not set throws `NoSuchObjectException`; null names and values are
   refused; a write-only transaction has none. Also with several threads
   that make actions run again.
2. Is the API right: `getOutput` throws for a missing name, where
   `Connection.get` returns null for a missing key (whose Javadoc wrongly
   says that it throws `NoSuchObjectException`, 005-10); the value type
   is `Object`; the outputs are a `HashMap` that is handed over, not
   copied.
3. Is it used anywhere: in the demos, the tests, the documents
   (`overview-pub.html`)? Should a demo show it?
4. The alternative: actions that return a value (a `Function`-like
   action), and what that would cost the API.


Done when
---------

Either the outputs have unit tests for 1 (and the Javadoc is right), with
the four gates passing; or Frans decides to remove them, and the API's
methods, their implementations, `NoSuchObjectException` if nothing else
throws it, and the documents' mentions go. In both cases the reason is
recorded here.


First step
----------

Write the unit tests of 1 on a scratch clone and see whether they pass.


Size and order
--------------

S. Independent of the other entries. Touches the Pub API, so best before
005-05's decision on publishing.
