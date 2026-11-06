017-07. To consider
===================

Created 2026-11-05 by Frans Lundberg. Status: open (a collection).

Small ideas for BergDB that Frans may consider some day: not a fault, not
a todo, too small for a topic of its own. Each is a numbered section:
what it is, where it came from, the options if any, and Frans's notes.
None is worked on until Frans takes it up; then it becomes an entry of
the todo list (019) or an item of its own, and its section says where it
went.

Started at Frans's request on 2026-11-05 (12:16), when 019-03 was moved
here: "Make a subitem called nn-to-consider or similar."


## 1. A get that always copies a byte[] value

Moved from 019-03 on 2026-11-05. State: to consider.

What: since 015-47's option (c) (Frans, 2026-11-05, 12:00), a get of a
`byte[]` value returns the database's own array, zero-copy, and the
Javadoc says that it must not be changed; the put copies the caller's
array. Should the Pub API also offer a get that always returns a copy?

Where it came from: Frans, 2026-11-05, 12:00, choosing the zero-copy
gets: "For another time, we could discuss supporting get operations that
always copy the byte arrays. That should be doable, right? Some
getAndCopy() methods or something. Or just some setting possibly. Not
sure. But this is for another time." It is doable: the copy is one
`clone()` at the edge of the Pub API, where 015-47's first fix (39cbbec)
had it.

The options:

* **(a) No new API.** A caller that wants its own array copies it:
  `byte[] b = c.get(key, byte[].class).clone();`. The Javadoc of the gets
  shows this (it already says "copy them first, with clone()"). Nothing
  to add or test (P11); the cost is paid only where a copy is wanted.
* **(b) A copying method**, such as `getCopy(key)` on `ReadInterface`
  (and so on `Connection` and `RwEnvironment`), returning a fresh array.
  One more method of each read interface, with its tests and Javadoc; it
  does what (a)'s line does.
* **(c) A setting on the connection**, such as
  `Connection.setCopyOnGet(true)`, so that every get of that connection
  copies. A program can then hand arrays to code it does not trust
  without changing each call; but it is a setting (P10), and a reader of
  a get cannot tell from the call whether its array may be changed.
* **(d) A read-only view**, such as `get(key, ByteBuffer.class)`
  returning `asReadOnlyBuffer()`: no copy and safe, but a new form of get,
  worth it only if a program needs large values without copies and
  without trust.

Claude's view when it was registered: (a), with the line in the Javadoc;
(b) or (d) when a program needs them.

Related, from the same discussion: skipping the put's copy is not
proposed; skipping a get's copy for values read from the stream became
moot with option (c).


## 2. startupDistance in the meta block, not in an internal KV

Added 2026-11-05. State: to consider.

What: the startup distance is the only setting in the meta block
(`MetaBlock` v154, offset 40, 4 bytes) that a start does not need before
it can read a KV. A start takes the startup position from the last
record; only the writer uses the distance afterwards (`Db`: the start
reads `meta.getStartupDistance()` into its params, and the writer's take
uses it). To get a change into the stream, `Db.setStartupDistance`
writes a dummy transaction (`/#i/-dummy`) of
`RecoverableStream.META_BLOCK_DISTANCE` bytes, to force a meta block with
the new value.

Where it came from: the discussion of 015-87's F1 (2026-11-05), where
Frans set the rule that the meta block is for what cannot be stored in
other ways (13:04): "I think the general idea of the meta block is for
settings that cannot be stored in other ways. Only for this. Once the
database has started, further settings should be storage in internal
KVs." Frans, 13:12: "Add a note to 017-07 about startupDistance in the
meta block. Startup distance was not in each transaction before, so it is
in the meta block for historical reasons."

What a move would mean: an internal KV (beside 015-87's
`/#i/dreclaim/-settings.txt`, or its own), read at the end of a start and
written by a transaction when it changes; the dummy transaction goes. It
is a change of the format (018-01, section 2: Frans approves). Old streams
keep the distance in their meta blocks, so a start reads the meta block's
value when the KV is missing. The C clone (012) follows only when it ports
a release that has it.

The builder side: `DatabaseBuilder.startupDistanceInMb` is ignored for an
existing database (its meta block's value wins), and the same reasoning as
015-87's (Log, 2026-11-05, 13:23: set only by the setter, no builder
value) would apply. Frans, 13:23: "that is for 017-07 unless we work on it
to be included in 2026.3. Tempting. But let's get 87 done first."


## 3. Refusing an oversized transformation result

Added 2026-11-05. State: to consider.

What: a value transformation's result above `StoredTrans.valueLimit()`
fails the database today when its record does not fit (015-51, decided
2026-11-05): it is the caller's fault, as an exception from the
transformation is, and the transaction is not in the stream. A refusal
would leave the database running, as for a value given directly above
the limit, which `Db.checkSize` refuses before the go point. Only Core
API callers can meet it: the Pub API uses no value transformation.

Where it came from: Frans, 2026-11-05, 21:03, choosing R7's first option
for 015-51: "'a' for 015-51. And also add the possibility of a refusal to
the to-consider list of the long-term item."

Why it is not simple: a refusal must come before the go point; after it,
whatever throws fails the database (005-01), so a check there cannot
refuse. A transformation runs after the go point, in `Db.putKvs`, and it
needs what is known only there:

* the transaction's time, its `transTime`, which
  `dbClock.transactionBegin()` gives at the go point;
* the previous value, which `putKvs` reads at that time
  (`getOne(x.trans.tt, ...)`), for the key that a key transformation may
  have changed;
* for reclaim's row (`Reclaim.step`), the bytes of the index nodes that
  the step's touch and puts made dirty (`Trans.dirtiedBytes`), known only
  after the puts.

The options:

* **(a) As it is.** The contract is written down: the Javadoc of
  `ValueTransformation.transform` and docs/levels.md, section 3 (015-51).
  Nothing to add.
* **(b) The transformations run before the go point**, R7's second option
  (016-06's R7, section R7-F2), so that a result can be refused. It
  changes when they run: the time and the previous value need another
  source, and reclaim's row cannot run there at all.
* **(c) A refusal for user transformations only.** Reclaim's own row is
  kept as it is: 015-50 keeps a step's values within the limit, and the
  1/8 of the record left besides `valueLimit()` takes the row. A user
  transaction's transformations would run after
  `dbClock.transactionBegin()`, which gives the time, and before the
  puts; a result above the limit refuses the transaction. `DbClock` then
  needs a way to give the begun time back (it has `transactionBegin` and
  `transactionEnd`, nothing between), and the previous values read before
  the puts must be checked against today's reading, for a transaction
  that puts a key twice or whose key transformation changes the key.
* **(d) A declared bound.** A transformation states the largest result it
  can return, and `Db.checkSize` counts that bound instead of the input
  value, before the go point. A result above its own bound stays the
  caller's fault, as in (a). It narrows the fault, it does not remove it;
  one more method of `ValueTransformation`.


## 4. A clear place for the database's design

From Frans, 2026-11-06, 10:31, when the error model was decided (019-10).
State: to consider, after release 2026.3.

What: one clear place for the database's design, such as its error
model, in an item that other items, the code and the Javadoc can
reference by ID.

Where it came from: Frans, 2026-11-06, 10:31: "I would like a clear place
to put database design information like this. In some item we can
reference. Not sure how to now. Restructuring design documentation can be
a separate todo for later, not this 2026.3 release. We could look at it
wholistically after 2026.3."

What is there now: the design is spread over `docs/levels.md` (kept up to
date with the code; the error model goes into its section 3 for now),
`docs/sis-model.md`, the principles (010-01), the Javadoc of `Db` and the
Pub API, and design subitems such as 001-08 to 001-11 and 009-05
(006-07 moved them out of `docs/`).


## 5. Reads wholly in the file without BufferedStream's monitor (reader scaling)

From 015-86's Option 4, 2026-11-06. State: to consider, after release
2026.3.

What: every read of the stream enters `BufferedStream`'s monitor for its
bounds check (`BufferedStream.read`: the failure flag, and the lengths
that tell which part of the read is in the file and which in the write
buffer): about 1.2 million entries a second with 8 readers. A read wholly
in the file could check volatile lengths and the failure flag without the
monitor, and only a read that touches the buffer would take it.

Where it came from: 015-86's Option 4 (Options for Frans's decision,
2026-11-06). With the fix and 8 readers on F53, the samples found readers
BLOCKED most in `BufferedStream.read`, and the class "blocked" was 110 of
the 1,026 gets over 10 ms, 17 percent of their time: the most such a
change could remove there. But on a full machine blocking less may not
lower the count: by the fix's experience, readers that block less stay
runnable more and lose their cores more often. So it is not 015-86's fix.

Why it may matter: reader scaling, on machines with more cores, where one
monitor that every read enters may limit the readers; and 010-01, P1's aim
that readers are never blocked, and its "To look at" (Frans, 2026-10-26):
"every place where a reader can wait today, and for how long".

The measurement to make first: with fewer readers than cores (4 to 7 on
F53), or on a machine with more cores, the readers' share of time blocked
on this monitor, and how it grows with the readers. If it is small, there
is nothing to do.

The risks and costs: a second, lock-free path in a class that is critical
for concurrency, beside the storage thread's appends, cuts and failures;
its argument (a read that passes the check without the monitor reads only
bytes that are in the file), its tests, `before-commit.sh` and the level
scripts, and a `parts` run as 015-86's; about 3 to 5 agent-hours (015-86's
estimate). KISS (010-01, P13): only if the measurement shows that the
monitor holds the readers back.

Frans, 2026-11-06, 11:09 to 11:11, when he closed 015-86: "How about
Option 4 for a later release. Should that be a thing to consider?" To the
coordinator's answer (yes, as reader scaling rather than as 015-86's fix;
not 2026.3, because of its target of a bug-free Core and the risk in a
core storage class under concurrent appends; measure first): "Yes, both."
