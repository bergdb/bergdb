005-12. Transaction outputs: a consistent API, then tests
=========================================================

Status: open. Kind: decide. Created 2026-10-20.


The task
--------

In Frans's words (2026-10-20): have a look at transaction outputs; study
them, and then either ensure that they are tested and work, or remove
them. The entry says why the feature is valuable, if it is.

In Frans's words (2026-10-22): "I do think there is a need for
.setOutput() and getOutput()." "This is *not* about transaction meta
data. This is a separate feature. I believe it is valuable. Deleting the
feature is not an option any more." "About the API, please suggest a
design. The current API seem inconsistent."

So the outputs stay. The task is now: Frans decides the API, from the
proposal below; then it is changed as decided, documented and tested.

Found in 005-10, where the Pub API's `RwEnvironment.setOutput` and
`Transaction.getOutput` came up as unused (G1): nothing in the repository
calls them, nor their implementations.


What they are
-------------

A read-write transaction runs an `Action` (`Connection.rw(action)`). The
action reads through its `RwEnvironment` and writes through it; it can
also call `env.setOutput(name, value)`. When the transaction has
committed, the caller gets the values with `transaction.getOutput(name)`.
Outputs are the action's results for the caller of `rw`, as a method's
return value is for its caller. They live in memory only; they are not
written to the database.

An action may run more than once: the transactions are optimistic (an STM,
software transactional memory; `Action`'s Javadoc), and a run whose reads
were changed by another transaction before its writes are applied is run
again (`RerunException`). Before each new run the outputs are cleared
(`RwEnvironmentImp.clearOutput`), and the caller gets those of the run that
committed (`RwTransaction.executeRw`, `rw.output = env.getOutputMap()`).

Outputs are not transaction metadata. Metadata would be stored with a
transaction in the database, such as who ran it, for anyone to read later,
as the transaction time is now (`Transaction.getTime`,
`Connection.transactionInfo().time()`). An output is never stored, and
only the caller of `rw` gets it. Metadata would be a feature of its own,
not part of this entry.


Why they are needed
-------------------

They return a result from an action that may run more than once. A value
that the action computes from what it read, such as the balance after a
payment, an id it chose, or whether a condition held, is only right if it
comes from the run that committed. Without outputs, the action sets a
variable of the caller and must reset it at the start of every run;
otherwise a value set by a run that did not commit survives when the
committed run takes another path. Nothing enforces the reset, tests
without contention pass without it, and the wrong value shows only when
transactions compete. Outputs reset by construction.

The repository does it by hand twice: `PubTester.testRw1` and `testRw2`
return their values in static fields, and `IndexBuilderImp.createStep`
resets its state at each run ("Resetting stuff is important; an Action
may be rerun."). Java 8's lambdas do not help: a lambda captures only
effectively final local variables, so a result needs a one-element array
or an `AtomicReference`. Frans, 2013-05-30, in `RwEnvironment.java`:
"Added setOutput(). It *is* needed. Makes code less ugly." (It had been
removed on 2013-04-16, "I was in doubt".)


The current API
---------------

```java
// RwEnvironment
public void setOutput(String name, Object value);

// Transaction
public Object getOutput(String name);
```

It is inconsistent with the rest of the Pub API, and with itself:

1. A missing output throws; a missing entry does not. `getOutput` throws
   `NoSuchObjectException` for a name that was not set, where
   `Connection.get` and `RwEnvironment.get` return null for a missing
   key. `Transaction`'s Javadoc does not say that it throws, and the only
   way to ask whether an output is there is to catch the exception.
2. Untyped. `get(key, Class<TYPE>)` returns the type that the caller asks
   for; `getOutput` returns `Object`, for the caller to cast.
3. A method that one kind of transaction always refuses. `getOutput` is in
   `Transaction`, which `put`, `delete`, `w().execute()` and `rw` all
   return; a w-transaction has no action and no outputs, and
   `WTransaction.getOutput` always throws.
4. Name or key. The interfaces say `name`; `getOutput`'s implementations
   say `key` (`getOutput(String key)`, "key == null not allowed"), the
   API's word for a database key.
5. Different checks. `setOutput` refuses a null name, an empty name and a
   null value; `getOutput` refuses a null name only. (`setOutput`'s
   message has a typo: "The empty is not allowed for 'name'.")
6. The rules are not written down. No Javadoc says that outputs are in
   memory only, that a rerun clears them, that the caller gets those of
   the committed run, or that setting a name again replaces its value.

As far as reading the code shows, the implementation does what "What they
are" says. No test checks it.


Proposal
--------

Claude (Opus 5.5, Claude Code), 2026-10-22, for Frans to decide. Keep the
two methods and their names, and make them behave as `put` and `get` do:
null is refused when setting and means "not set" when getting, and the
getter is typed as `get` is.

```java
// RwEnvironment

/**
 * Sets an output of the transaction: a result for the caller of
 * Connection.rw, who gets it with Transaction.getOutput once the
 * transaction has committed. Outputs live in memory only; they are not
 * stored. If the action is run again, the outputs of the earlier run are
 * cleared first, so the caller gets those of the run that committed.
 * Setting a name again replaces its value.
 *
 * @throws IllegalArgumentException if name is null or empty, or if value
 *             is null.
 */
public void setOutput(String name, Object value);

// Transaction

/**
 * Returns the output that the action set with the given name in the run
 * that committed (RwEnvironment.setOutput), or null if it set none. A
 * w-transaction has no action and no outputs: null for every name.
 *
 * @param clazz The class of the output, or a superclass of it (Long.class
 *             for a long, which setOutput gets boxed).
 * @throws IllegalArgumentException if name is null or empty, or if clazz
 *             is null.
 * @throws ClassCastException if the output is not an instance of clazz.
 */
public <TYPE> TYPE getOutput(String name, Class<TYPE> clazz);
```

In use, a payment that is made only if the money is there:

```java
Transaction t = c.rw(env -> {
    Account a = env.get("/accounts/0", Account.class);
    if (a.balance < amount) {
        env.setOutput("paid", false);
        return;
    }
    a.balance -= amount;
    env.put(a);
    env.setOutput("paid", true);
    env.setOutput("balance", a.balance);
});

if (t.getOutput("paid", Boolean.class)) {
    long balance = t.getOutput("balance", Long.class);
}
```

Against the six points:

1. Null for a missing output, as `get` gives for a missing key; a result
   that is not null is the test of whether an output is there.
   `NoSuchObjectException` goes, as nothing else throws it (005-10, G1b).
2. Typed by a class, as `get` is. For `get` the class says how to build
   the object from the stored bytes; for `getOutput` it checks and casts
   the object that the action set.
3. A w-transaction answers null and stays a `Transaction`: no new type
   for `rw` to return.
4. `name` everywhere, also in the messages.
5. The same check of the name in both methods.
6. The Javadoc above, and a sentence in `Action.run` and in
   `Connection.rw`: the action's results go to the caller as outputs.

Also:

* `RwEnvironment`'s Javadoc says that the environment is valid only while
  `Action.run` runs. An action that keeps it and calls `setOutput` later
  changes the outputs of a committed transaction, as the map is handed
  over, not copied; a `put` or a `delete` made then is lost silently.
  Refusing every call after the run (`IllegalStateException`) would make
  that an error; optional.
* A demo: `GetStarted4`, the payment, prints the payer's balance from an
  output, a few lines. `overview-pub.html` shows no rw-transaction and
  stays as it is.


Not proposed
------------

* An action that returns its result, `R run(RwEnvironment env)`: the
  other way to get the committed run's result by construction, and
  typed. It gives one value, where outputs give several by name; and it
  cannot be an overload of `rw`: with `rw(Action)` and `<R> R rw(Fn<R>)`,
  even `c.rw(env -> env.put("/a", "b"))` does not compile ("reference to
  rw is ambiguous", javac with `--release 8`, tried 2026-10-22). So it
  needs a second action type and a second method with a name of its own,
  and the caller loses the `Transaction` (its time, `sync`) unless the
  result comes wrapped in one.
* Typed keys, an `Output<T>` object for each name
  (`env.setOutput(BALANCE, 5L)`, `t.getOutput(BALANCE)`): checked at
  compile time and safe from a misspelt name, but a new class in the API.
* `<TYPE> TYPE getOutput(String name)`, the type taken from the
  assignment: shorter, but unchecked. A wrong type fails at the
  assignment, not in `getOutput`, and in `println(t.getOutput("x"))` the
  type is `Object`.
* Throwing for a missing output, as today: a misspelt name fails at
  once, but an output that is set on some paths only then needs a third
  method to ask for it, and it differs from `get`. With null, a misspelt
  name fails where the result is first used.


Tests
-----

Unit tests, in `PubTester` or a tester of their own, for the API as
decided:

1. An output set in an action is the caller's after commit; several
   names; a name set twice keeps the last value.
2. After a rerun, only the committed run's outputs are there: a first run
   that sets an output that the committed run does not set leaves nothing
   of it. As in `testRw2`: a second connection changes a key that the
   action has read, and the action sets another output for the new value.
3. A name that was not set gives null; a w-transaction gives null.
4. Null and empty names, null values and a null class are refused; a
   wrong class throws `ClassCastException`.
5. Several threads increment one counter in rw-transactions, so that
   their actions run again, and each sets the value it wrote as an
   output: the outputs are 1 to n, each once.


Done when
---------

Frans has decided the API, and it is changed as decided: `RwEnvironment`,
`Transaction` and their implementations, the Javadoc (also of
`Action.run` and `Connection.rw`), `NoSuchObjectException` if it goes,
and the tests above, with `java/before-commit.sh` printing `BEFORE
COMMIT OK`. The decision and its reasons are recorded here.


First step
----------

Frans decides on the proposal, or changes it. Then, on a scratch clone:
tests 1, 2 and 5 against today's code (does the clearing at a rerun
work?), then the change.


Size and order
--------------

S. Independent of the other entries. Touches the Pub API, so best before
005-05's decision on publishing.


Found on the way
----------------

* `Connection`'s class Javadoc shows `c.rw(...).execute()`; `rw` has
  executed at once since 2014-07-20 (its log), so it is `c.rw(...)`.
* `WTransaction.sync(SyncLevel)` waits for the database's last
  transaction (`Db.sync(syncLevel)`), not for its own position as its
  `sync()` and `RwTransaction`'s do: right, but it can wait longer than
  it needs to.
* An action that writes nothing still commits: it takes the writer's
  lock and gets a transaction time and a record in the stream
  (`Db.executeInner`, `NodeStream.appendNodes`). With outputs, an action
  that only reads and returns a result is natural; whether such a
  transaction should skip the commit is a question of its own.
