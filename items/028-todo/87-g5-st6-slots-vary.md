028-87. Investigate: G5's ST6 changes from run to run near its limit
=====================================================================

Status: done: the count's variation is eviction's timing; the pass does not vary.
Kind: Investigate. Frans: none.
Created 2026-11-28 by Frans Lundberg.

What: `java/stress/count-gates.sh`, a functional gate of `night.sh`, has
one measure whose count changes from run to run of the same build: G5's
ST6, "cache table slots over the larger of 2.0 times the twin's and the
tables' floor 65536", 58,672 slots (value 0.895, margin 1.12) in the
night of 2026-11-28 and a few hundred different in reruns, while every
other count of the gates is the same in every run. Found by 028-86.

Why: a functional gate must not depend on timing (028-23); one that
varies by run and sits near its limit could fail by chance.

Frans: none.

Done when: the variation's cause shown, its range over at least 20 runs
of G5, and the measure made deterministic, or a safe margin shown and
stated in the gate's header.

First step: `count-gates.sh`'s header, `CountGates.slotGate`, 024-33
and `Cache3.Table`'s shrink; runs of `CountGates g5`.


Result
------

Done 2026-11-28 by an agent of lead-1127, in a clone of `main` at
01232710, rebased onto main twice. The count varies with the timing of
eviction's batches; whether ST6 passes does not, by a bound of the
shrink's rule. The measure and its limit are unchanged; the gate prints
the two figures of that bound, and its header and `slotGate`'s comment
state the range and the bound.

### 1. Where the count varies

The slots are the sum of the lengths of the 4,096 HashMap tables of the
node table (`Cache3`). In every run G5's emptied database holds 9
handles and every one of its maps has a table of 16 slots or none: a
shrink to no entries (`Table.shrinkIfSparse`) makes a new HashMap, whose
table is null until its next put. So the count is 16 times the maps with
a table, and what varies is how many maps were left with no table:

    G5 g5-emptied slots by table length: 0: 425 maps, 0 entries, 425 empty; 16: 3671 maps, 9 entries, 3662 empty;
    G5 g5-emptied slots by table length: 0: 420 maps, 0 entries, 420 empty; 16: 3676 maps, 9 entries, 3667 empty;

The other six gate lines of G5, other than the heap's, were the same in
every run of a base in section 3.

### 2. The cause: eviction's batches by time

The emptied database's fill of 1M keys passes the default budget of 200
MB of resident bytes, so the capacity controller evicts (`Eviction`): a
batch after a transaction ends after 2 ms (`BATCH_NANOS`) and then wakes
the eviction thread, whose batches run between the writer's transactions
and end when the writer waits for the write lock. Which handles leave a
map, and at which removal a map shrinks to no entries, follow the timing.
Shown by runs of `CountGates g5`:

* Default: varies (section 3).
* `BATCH_NANOS` without a time bound (a patched `Eviction` first on the
  class path, not committed): still varies, 58,592 to 58,848 slots in 4
  runs; the eviction thread's batches remain.
* `-Devictbudget=1000000000000` (no budget eviction; the dead hand of
  023-05 runs as before, with its own 2 ms bound): 63,072 slots, 154
  maps without a table, in each of 8 runs (4 on 01232710 and 4 on
  67d12ae3). So the dead hand's and `maintain()`'s time bounds do not
  change the count here; the budget's eviction does.

### 3. The range

94 runs of `CountGates g5`, two at a time beside other heavy runs (load
average 12 to 20), on three bases of `main`.

* Slots 58,576 to 59,008 (value 0.894 to 0.900, margin 1.11 to 1.12),
  408 to 435 maps without a table, no slot above 16 a map; every run
  passed.
* 50 runs on 01232710: 58,608 to 59,008; 22 on 67d12ae3: 58,576 to
  58,992; 22 on a40a39c6: 58,688 to 58,928.

### 4. Why it cannot fail by chance

After every removal from a map, `shrinkIfSparse` shrinks it if its
entries are under 1/8 of its capacity, so a table of more than 16 slots
belongs to a map that holds at least 1/8 of its slots. The one
exception is HashMap's doubling of a table under 64 slots that gets a
bin of 8 (`treeifyBin`) while `Table.capacity` is 16, which that field's
comment and `testBinsStaySmall` show to be rare; it is in the printed
"slots above 16", 0 in every run. Without it the slots above 16 are at
most 8 times the handles, and with Z maps without a table

    slots <= 16 (4096 - Z) + 8 H,

which is over the floor, 65,536, only if Z < H / 2. G5's M11 gate holds
the handles to the larger of twice the twin's and the twin's plus 10, 18
(the twin has 8): ST6 can fail only with fewer than 9 maps without a
table, where every run had 408 or more, and 154 without budget eviction.
A failure of ST6 at these settings is a map that kept a large table, the
fault 024-33 fixed, not the timing.

G4's ST6 was not studied here: its limit is twice the twin's, 120,768
against 64,624 slots in the night of 2026-11-28 (margin 1.87).

### 5. The change

* `CountGates.slotGate` prints, before the gate, the maps without a
  table and the slots above 16 a map, of the emptied database and the
  twin: `G5 ST6 emptied: 429 maps without a table, 0 slots above 16 a
  map; twin: 4088, 0`.
* `slotGate`'s comment and `count-gates.sh`'s header ("Kind") state the
  variation, its range and the bound.

### 6. Gates

On the branch rebased onto a5541854 (028-86 on `main`), the code as it
lands (only this section added after):

    BEFORE COMMIT OK (83 s)
    COUNT GATES OK
    COUNT GATES OK

`count-gates.sh` took 128 and 149 s; G5's ST6 in its two runs:

    G5 ST6 cache table slots over the larger of 2.0 times the twin's and the tables' floor 65536 (58832 / 128) value 0.898 limit 1.000 margin 1.11 PASS
    G5 ST6 cache table slots over the larger of 2.0 times the twin's and the tables' floor 65536 (58560 / 128) value 0.894 limit 1.000 margin 1.12 PASS

with 419 and 436 maps without a table, 0 slots above 16 (the second
just outside the 94 runs' range of section 3); G4's ST6 64,528 and
64,608 slots, margin 1.87.

Before, on 67d12ae3, `count-gates.sh` failed twice on G4's M5 (34 /
13 against 2), night.sh's failure that 028-86 explained and that its
limit, on `main` since a5541854, passes; ST6 passed in both.


Log
---

2026-11-28. Registered by lead-1127 from 028-86's finding; taken by an
agent of lead-1127 (Investigate).

2026-11-28. Done by that agent: sections 1 to 6; the gates on the
branch rebased onto a5541854.
