# 027-02. BergDB trace format

Moved from docs/trace-format.md on 2026-11-12; kept current.

The format of the traces that connect the Java code with the Lean model: what
Java writes and the checker reads. Kept up to date with the exporter and the
checker. Until 2026-10-26 it was section 9 of the Level 2 alignment, now
[011-11](../011-docs-archive/11-level2-alignment.md), which has its
history (written 2026-10-15 for F1-008-11, WP B3, and extended by items 001
and 009); the mapping α that the traces express is in 011-11, section 2,
and for handles in [009-05](../009-handles/05-handles-alignment.md).

The exporter (`java/stress/TraceExport.java`) writes a trace of a Java run in
the terms of the Lean model; the trace checker (`lake exe tracecheck` in
`lean/`, `lean/Check/Trace.lean`) reads it and checks it against the model.
`java/stress/conformance.sh` runs both, and the level scripts run it.

A trace is a text file in UTF-8, one item per line, tokens separated by one
space. Lines starting with `#` are comments; empty lines are ignored.
Numbers are decimal natural numbers. `-` stands for "none". Every id is a
model id (011-11, 2.2): a Java id, or 0 for the root.

## 1. Entries

An entry value is one of (011-11, 2.4):

| Tokens | Value | `ptrs` |
|---|---|---|
| `K c y` | key klong: compare value c, child y | [y] |
| `D n c1 ... cn` | delete bitmap: deletes the key entries before it with compare values c1 ... cn | [] |
| `R y` | top node's root pointer to key node y | [y] |
| `S j z` | top node's skip pointer j to top node z | [z] |
| `T z` | the root's entry for top node z | [z] |
| `V h` | value node data, h a hash of the bytes | [] |

## 2. Lines

    TRACE 1                      format version, first line
    CONFIG text                  workload parameters, seed, bergdb commit
    TX i                         starts transaction i (record R(i)); TX 0 is R(0)
    NEW x level kind             a node created by T(i); kind I (index) or D (data)
    ADD x t entry                an entry added to node x by T(i), at time t = i
    REC i sp top src [z]         record R(i): sp(i) and top(i) (record index or -);
                                 src is field (Java stores it) or derived (computed
                                 by the exporter from the stream); z, the node of
                                 the version top names (since 2026-10-16, WP E3)
    VER x kind                   a version of node x in R(i), in Java's order
    H t entry                    the version's history, one line per entry, in order
    F y r                        the version's reference for pointee y: record r
    GD x1 x2 ...                 gd(i), in Java's order
    DIRTY x1 d1 x2 d2 ...        D after T(i)
    LIVE x t y1 y2 ...           Java's live children of x at time t (optional)
    PROBE i ok|fail text         run B (011-11, 2.9): a restart after T(i) and its checks
                                 (D, lookups), or the stream comparison at the
                                 end; fail with what went wrong
    ERROR text                   a problem the exporter found (counts as a failure)
    END i                        ends transaction i
    DONE n                       last line: the last record, R(n) (n transactions
                                 after R(0); with reclaim, the records of the user
                                 transactions, of the setters and of the parts of
                                 maintain())

Since bergdb 028-15 the start that creates a database commits a record after
the primordial one: an internal transaction that puts the startup distance's
KV, `/#i/-sd` (027-03, sections 14.2 and 15). The exporter's run
A records it through the hooks as any record, R(1), with `kind=table` under
reclaim; its first hook records R(0) before it changes the tree. So the first
user transaction is R(2) of a trace, and a trace's T(1) puts the KV. Since
bergdb 028-13 the KV holds the default, 50 MB, and the exporter sets the
run's sd (CONFIG's `sd`) with `Db.setStartupDistance` right after the start:
R(2), a user transaction that puts the KV again, and the workload's first
transaction is R(3).

Format 2 (`TRACE 2`, since 2026-10-16, bergdb item 001, WP L5; the checker
still reads format 1) adds, from the item's plan (001-01, 8.2):

    SKIPT j t                    after a top node version's H lines: its skip
                                 slot j caches time t (the time index of the
                                 target's root time, Java's pointersTime; M29 of 001-08)
    FIRST x n r kind cut         run B: a first touch of a stream pointer to
                                 node x after the restart after T(i) (in TX i,
                                 up to the next restart, the startup's own
                                 rerun included): the pointer names record n
                                 after Rule R (- for a vpos); Java took record
                                 r (- for a canonical object); kind is
                                 canonical, version (read from the stream) or
                                 snapshot (the node table's object); cut is 1
                                 if the version read was cut back to the
                                 startup time

With reclaim (the exporter's `retain=S`, since 2026-10-17, bergdb item 001,
WP R2; 001-07, 2.7), every executed transaction is a record, each an ordinary
`TX` block. Since bergdb 031-06 (one record an action, 2026-11-27) every
accepted action appends exactly one record: a commit's record holds its
transaction and the maintenance that reclaim owes, decided from the stream
before the record (an iteration's begin, a step, the safe positions, a cut's
decision: the step's copies, reclaim's row `-current.txt` and its table
`-table.txt` under `/#i/dreclaim/`); a part of `maintain()` is a record of its
own, an empty internal transaction that carries the part's maintenance; a
setter's record carries none. Until 031-06 reclaim's steps and table stores were
internal records of their own after the user transaction's. The comment line of
a `TX` block gives `kind=step` (a record that carries a step of reclaim: a
commit's or a part's), `user` (a commit without a step), `part` (a part
without a step) or `table` (BergDB's own internal records: the settings, the
creating start's startup distance), and `copies=N`, the copies among its puts.
Since bergdb 015-87 the exporter's call of `setRetainDuration`, before the
first user transaction, commits reclaim's settings
(`/#i/dreclaim/-settings.txt`) in a record of their own, internal and
marked `kind=table`: R(3) since bergdb 028-13 (2026-11-19), after the
startup distance's R(2) (R(2) from 028-15, 2026-11-18, R(1) before), and
the workload's first transaction is R(4); its calls after a restart
write nothing. The
startup distance's record of `Db.setStartupDistance`, a user transaction
that carries no maintenance, is marked `kind=user`. Format 2 then also
has:

    TOUCH x1 x2 ...              in TX i, after the ADD lines: the index nodes
                                 T(i)'s touch visited (Db.touchPaths: the paths
                                 of its step's copies and of reclaim's row, since
                                 031-06; of all its keys, the copies and the row,
                                 until then; a key range until 024-07), sorted
    FA t                         in TX i, when it changes: fa(i), the first
                                 available time, as a model time
    CUT c t                      in TX i: Java decided a cut at R(i): records
                                 before c may go; t is the first available time
    PHYSCUT c                    in TX i: after R(i), the stream's first position
                                 moved; R(c) is the first record that starts at
                                 or after it

`FA`, `CUT` and `PHYSCUT` come after `DIRTY`. Run B also restarts right after
each call that decided a cut, and looks up only from the first available time
on; its `PROBE` lines are in the block of the last record of the call (since
bergdb 031-06 a commit's call has one record, its own; until then, with
reclaim, the last of reclaim's records after it).

With eviction (the exporter's `rune=S`, since 2026-10-18, bergdb item 001,
WP J4; 001-08, 7.3), run E executes run A's workload with a
forced eviction schedule (S: values, every or random; from J7 also budget,
the capacity controller), and format 2 also has:

    SLOT x y r kind              in TX i, at the end of the call whose last
                                 record is R(i): run E's resident canonical
                                 object of node x has a slot for pointee y
                                 that serializes record r (- for a vpos);
                                 kind is canon (a memory slot to y's
                                 canonical object), mem (to another object,
                                 or to a value), stream, or dead (a stream
                                 slot below the stream's first position)

SLOT lines come after the FIRST lines of their transaction, sorted. Run E's
`PROBE` line (its stream against run A's) is in the last record's block. The
checker's C-P checks the SLOT lines against the model's INV-SLOT.

With handles (since 2026-10-26, bergdb item 009, step 4c;
009-05, section 4), run E also writes its memory as the
model's memory with handles (lean/SIS/Handle.lean, `HMem`), at the same
moments as the SLOT lines and after them:

    HMEM k c                     in TX i, at the end of the call whose last
                                 record is R(i): run E's last startup read
                                 R(0) to R(k) (its Rule R), and R(c) is the
                                 first record that starts at or after the
                                 stream's first position (0 without a cut)
    HTABLE y h                   the node table's entry for node y: handle h
    HANDLE h y state a w         handle h of node y, h the same in every state
                                 of run E: state live, loading or dead; it
                                 holds object a (- for none); w is the record
                                 of its written position (- for none)
    HOBJ a y kind r e x          object a of node y, a numbered in its state:
                                 kind canon or snap; r is the record of its
                                 position (- if it has none: a vpos); e is the
                                 number of entries of its history, and x the
                                 history's hash (below; first traces: none)
    HPTR a y r h                 a pointer of object a to index node y: its
                                 reference names record r (- for a vpos); it
                                 holds handle h (- for none)

The handles are the table's and those that a pointer of an object holds; the
objects, those that the handles hold, the super root and D's. Values have no
handles and are left out. A history's hash is FNV-1a with 64 bits (offset
basis 0xcbf29ce484222325, prime 0x100000001b3, modulo 2^64) over its entries
in order, each written as on an H line, `t entry` with the tokens of section 1 in
decimal ASCII and one space between them, and a newline after it; written as
an unsigned decimal (TraceExport's `historyHash`, the checker's `historyHash`
in lean/Check/Trace.lean). The checker's C-H checks these lines against the
model's invariants with handles (lean/SIS/HandleTheorems.lean). The
exporter's `ereads=N` adds N lookups at random times after each transaction of
run E (a `PROBE` fail line if one is wrong), and `erestart=K` a restart of run
E after every K-th transaction; the lines of that transaction are then the
startup's state, and HMEM's k is the transaction's last record.

FIRST lines come after the `PROBE` lines of their transaction. With `live=1`,
the root's `LIVE` lines cover every time t ≤ i on each record, at the record's
own time and at the last Java time before the next record (F1-008-13's
review-13-claude, 5.2: so that C-V compares the search's predecessor branch too).

Within `TX i`, the order is: `NEW` lines, `ADD` lines, `REC`, the versions
(`VER` with its `H` and `F` lines), `GD`, `DIRTY`, `LIVE`, `PROBE` blocks, then
`END`. `ADD` lines are in the order the entries stand in each node, so that
applying them gives Java's order of entries. A comment line after the
`ERROR` lines counts the key nodes that no top node reaches: nodes that a
later key of their transaction replaced (M1 of 011-11), which the checker reports as A3
failures. Since record format 8 the writer, PE, writes each node once and
replaces no node that its own transaction made (bergdb 026-25), so the
line does not appear; the level scripts' traces of 026-25 had none.

The root (id 0) appears in `TX 0` as a node, and gets an `ADD 0 i T z` for each
top node z that T(i) creates.

Levels are those of 011-11, 8.4, computed after the run, so a trace is written when
its run ends.

The exporter reports as `ERROR` what α cannot express: a change that is not
new nodes plus entries at time i (an entry removed or changed, a node whose
kind changed), a stored position that is not the start of a version, a
version whose node is unknown, a stream pointer in a run without restarts,
and M4's assertion (011-11, 7.1).

## 3. Example

A hand-made trace (ids and numbers shortened): R(0) with the top node 3 and
the empty root key node 5; T(1) puts one key; T(2) changes nothing, and the
startup pos moves to 1, so that R(2) writes the nodes of D.

    TRACE 1
    CONFIG example
    TX 0
    NEW 0 9 I
    NEW 3 8 I
    NEW 5 1 I
    ADD 0 0 T 3
    ADD 3 0 R 5
    REC 0 0 0 field
    VER 3 I
    H 0 R 5
    F 5 0
    VER 5 I
    DIRTY
    END 0
    TX 1
    NEW 7 0 D
    ADD 7 1 V 123
    ADD 5 1 K 40 7
    REC 1 0 0 field
    VER 7 D
    H 1 V 123
    GD 3 5
    DIRTY 3 1 5 1
    END 1
    TX 2
    REC 2 1 2 field
    VER 3 I
    H 0 R 5
    F 5 2
    VER 5 I
    H 1 K 40 7
    F 7 1
    GD
    DIRTY
    END 2
    DONE 2

The checker builds P(0) from `TX 0`, and P(i) from P(i−1) and the `NEW` and
`ADD` lines of `TX i`. `exec` of the instance returns, for transaction i, the
changes of `TX i`.

## 4. Format 3: the lines of the tree model

Format 3 (`TRACE 3`, since 2026-11-11, bergdb 024-12, section 2.6) is
format 2 with the lines that the tree model needs (lean/SIS/Tree/*.lean):
each transaction's operations, the key nodes as klongs, and reads of Java.
The exporter writes them with the property `tree=1`; `lake exe treecheck`
(lean/TreeCheck.lean, lean/Check/Tree.lean) reads them, and `tracecheck`
reads over them. Since record format 8 (bergdb 026-25) `treecheck`'s
writer is PE (lean/SIS/Tree/Pe.lean, a copy of the proved writer of
030-21 on the model's tree): it runs each transaction's OP lines and
compares Java's result node for node, with the ids; until then it ran the
model's old writer (lean/SIS/Tree/Exec.lean, still built for `treetest`).
`java/stress/treeconf.sh` runs the exporter and `treecheck`. A key is
written as `n c1 ... cn`: the number of its segments and their compare
values (`Keys.toSegments`); `-` stands for no key.

    TREE m g h k mb mc sa th     after CONFIG: the node size M; the bounds of
                                 the levels, G (the largest segment index of a
                                 key node, 0 for the first segment's trees) and
                                 H (the largest height of a key node in its
                                 segment tree, 0 for a segment leaf); k, the
                                 primordial key node. A key node in segment s
                                 at height e has level 1 + (g - s)(h + 1) + e,
                                 the top node with ordinal o the level
                                 2 + g(h + 1) + h + o (section 2's NEW lines).
                                 Since record format 7 (bergdb 024-21, 024-22)
                                 the writer's thresholds, in their roles in
                                 PE since record format 8 (bergdb 026-25;
                                 027-08): mb, m, the least live klongs of a
                                 key node that a transaction changes and that
                                 is not a root: a smaller one is joined with
                                 a neighbour (Dag.minFill; 1 below node size
                                 8, where nothing is joined); mc, c, the most
                                 entries of a joined node: a longer joined
                                 list is cut into parts of at most c
                                 (Dag.mergeCap); sa, h: a list of at most h
                                 entries that its node cannot take is one new
                                 node, a longer one is cut into parts of at
                                 most the cut size, M / 2, which the line
                                 does not give: the checker computes it
                                 (Dag.splitAbove, Dag.cutSize; lean/SIS/Tree/
                                 Pe.lean, cutSize): 8, 17 and 17 at node size
                                 30. Until format 8 sa was rule O's h, the
                                 most klongs of a last version that a time
                                 split kept, and mc the most live klongs of a
                                 merge's one new node. Since 024-23 a ninth
                                 token, th: option 2's theta, the most dead
                                 klongs a key node holds after a write
                                 (Dag.theta: 7 at node size 30, 2 at 8;
                                 a node size below 8, where it was 0,
                                 is refused since 028-38). The checker
                                 reads a line of 7 numbers too (theta 0,
                                 off), of 4 (2026.4's writer: no
                                 merges, h = M / 2), and of 6 (sa = mc); its
                                 writer is PE in each case
    BASE b                       in TX i, i > 0, first: the id of the first node
                                 that T(i) makes; the following get b + 2,
                                 b + 4 and so on, in the order Java makes them
                                 (Db.setIdOfNode; a delete's marker uses one);
                                 since record format 8 PE's order (027-03,
                                 section 8.2): a value or a delete's marker
                                 when its operation is applied at its segment
                                 leaf, a segment tree's new key nodes when
                                 that tree is emitted, the space root's tree
                                 bottom-up, the top node last
    OP P key v                   in TX i, after BASE, in the order the Dag gets
                                 them (Db.putKvs; since record format 8 one
                                 batch, in strictly increasing key order,
                                 Dag.putKvs): a put of the key, v the
                                 value's hash (as V's, section 1)
    OP C key v                   a copy (since bergdb 031-06): a put of a step
                                 of reclaim, the value that its scan read put
                                 again, whose value node has the copy mark (byte
                                 6, 027-03); the exporter reads the mark from the
                                 record's bytes (StoredValueNode.isCopy) and
                                 checks that the marked keys are the plan's
                                 copies (Maintenance.Plan.copyKeys). To the
                                 tree model and the contract's writer a put
    OP D key                     a delete that deleted
    OP N key                     a delete that changed nothing (not in the
                                 record)
    ACT P key v                  with `steps=1` (since bergdb 031-06), in TX i,
    ACT D key                    after the OP lines: the operations of the
                                 record's action as submitted, a put with its
                                 value's hash or a delete, in the order given:
                                 a user transaction's as the exporter's workload
                                 built it, before Db sees it; the Trans of
                                 BergDB's own actions as Db executed it (a
                                 setter's, the creating start's); none for a part
                                 of `maintain()`, whose action is empty
    KN x l n k1 ... kn           in TX i, after the ADD lines: key node x after
                                 T(i), for each key node that T(i) made or whose
                                 klongs it changed in any way, a diff of the
                                 klongs (in TX 0: every key node; until 030-09
                                 a diff of the entries, which left out a node
                                 whose klongs were changed or removed): l is 1 for
                                 a segment leaf, 0 for an inner node; then its
                                 n klongs in order, each `T t` (a time klong, t
                                 a model time), `K c y` (a key klong: compare
                                 value c, pointee y) or `B b` (a delete bitmap:
                                 bit j of the number b set if it deletes klong
                                 j; cumulative, as Java's; b < 2^62, since
                                 Java's bitmap has 62 bits, for the klongs 0 to
                                 61: Klong, Dag.MAX_NODE_SIZE)
    GET t key v                  in TX i, after the KN lines: Dag.getOne of the
                                 key at model time t, after T(i), gave the value
                                 with hash v, or `-` for none
    SCAN t d a b n start end r kv1 ... kvr
                                 in TX i, after the GET lines: Dag.getMany at
                                 model time t, after T(i): d is F (forward) or
                                 B (backward); a is 1 if the start key is
                                 inclusive, b if the end key is; n is the limit
                                 (GetMany.GetN); start and end are keys or `-`;
                                 r results follow, each a key and its value's
                                 hash

The `OP C` lines are in the grammar that the contract's checkers read; the ACT
lines are not (`lineKinds`), so their traces (`treeconf.sh`) have none, as they
have no STEP lines.

The writer's contract is checked on format 3 too (`lake exe contractcheck`
in `lean/contract/`, `lean/contract/check.sh`; bergdb 030-04, 030-05 and
030-09). It reads a trace only if it is whole: the first line `TRACE 3`, no
`ERROR` line and no line of a kind not in this section or section 2, the
transactions numbered 0, 1, 2, ... each from `TX i` to `END i`, and the last
line `DONE n`; in each transaction a `NEW` line only for a node not made
before, every `ADD` line at time i, a `KN` line for every key node made, an
`ADD x i V h` line for every value made, an `ADD z i R y` line for every top
node made, one `GD` and one `DIRTY` line (Contract/Complete.lean). Since
bergdb 030-15 every line must also parse whole by the grammar of this
section, section 1 and section 2 (`lineFault`): exactly the tokens of its
kind, each of its form, a number of decimal digits only, one space between
tokens (but in `CONFIG` and `PROBE` text); the lines of a transaction in
the order given in section 2 (`BASE` and `OP` first, then `NEW`, `ADD`,
`KN`, `GET`, `SCAN`, `TOUCH`, `REC`, the versions, `GD`, `DIRTY`, `FA`,
`CUT` and `PHYSCUT`, `LIVE`, `PROBE`, `FIRST`, `SLOT`, the handles' lines);
`TX i`, i > 0, starting with `BASE`; `TX 0` without `BASE`, `OP`, `GET`,
`SCAN`, `TOUCH`, `FA`, `CUT` or `PHYSCUT`; the `TREE` line with 4, 6, 7 or
8 numbers. Since bergdb 030-19 also: every `B b` klong with b < 2^62; no
`PROBE` line that fails (run B's and run E's checks fail a trace as an
`ERROR` line does); and the reads of every `TX i`, i > 0: the same number
of `GET` lines in each, at least one, and one `SCAN` line, so that a trace
exported with `gets=0` fails. The bridge checker (`lake exe bridgecheck`)
reads a trace only if it is whole in the same way. The contract checker's
`LIVE` lines, with `live=1`, are checked against the package's search and the space
root at each time.

A transaction with a TOUCH line (a step of reclaim; section 2) touches the
paths of the keys of its copies (`OP C`) and of reclaim's row (Db.touchPaths,
Maintenance.Plan.touchKeys; since bergdb 031-06, when a step came to ride in a
commit's record beside the action's operations, whose paths it does not touch;
from 024-07 to 031-06 the paths of all the keys of its OP lines, its copies and
its row): the tree model's `touchOf` of those keys must give the TOUCH line
(`treecheck`'s C-T5), and the tree model's own run (C-T9) touches the same
keys. (Until 024-07 the touch was a key range, and format 3 had its bounds as
RANGEF and RANGET lines, on 2026-11-11 only.)

Since bergdb 030-27 (2026-11-19) the exporter's property `steps=1`, with
reclaim and `tree=1`, adds one line to each step of reclaim, from its
iteration's row in Java's memory (`Reclaim.IterationInfo`):

    STEP t0 c L L' eod           in TX i, a step of reclaim (a record with a
                                 TOUCH line), after CUT and before PHYSCUT:
                                 t0, the record of the iteration's tStart
                                 (the state at pStart); c, the first record
                                 at or after its pCut, as on a CUT line; L
                                 and L', lastKey before the step and after
                                 it, keys or `-` for none; eod 1 if the
                                 step's scan passed the end and ended the
                                 iteration (the row done, its tEnd the
                                 step's time), else 0. Since bergdb 031-06 L
                                 is read from the row before the record
                                 (Db.TestHooks.beforeApply), L' and eod from
                                 the row that the record holds (the plan's)

`tracecheck`'s C-STEP checks them against the model of the steps (bergdb
030-25, `StepsOK`), on the tree model's reads (lean/Check/Steps.lean,
`stepCheck`): per STEP line, at the step's state (after T(i - 1), the state
before the record, which the step's scan reads), L is the L' of the
iteration's step before (none for its first), c ≤ t0 + 1, L' is L or a key
of the range (the live keys after L up to E, the greatest key live after
T(t0)), with eod the range's last key, and the record writes every KV of the
range up to L' whose value node was made before c (STEP-puts): a copy (OP C),
or, since bergdb 031-06, an operation of the action at its key, its put or
delete (Java leaves out a copy at a key that the action writes), or reclaim's
put of its row or table there; its operations have distinct keys; since bergdb
030-34 (2026-11-20) each copy with the value that the scan read, the key's
value before the record as the tree model reads it (its hash, as V's), and
each copy of such a KV (STEP-values, STEP-ops). Until 031-06 the step was a
record of its own, and STEP-ops required its operations to be those puts and
the row's put, and no delete. Since 031-06 C-STEP checks every record against
its action as submitted, its ACT lines (STEP-action, `actionFailures`): its
operations have distinct keys, one operation a key, as the contract's
`MaintenanceOK` takes it of every record (since 2026-11-27, 031-06's
review-main, R7; until then STEP-ops tested it in a step's record only); the
operations that are not copies are the action's, each operation of the action
among them with its value (a delete as `OP D` or, if it deleted nothing,
`OP N`; of two operations of a key in the ACT lines, the last), and every other
is a put at a key of reclaim's reserved prefix `/#i/dreclaim/` (the row, the
table); no copy is at a key that the action writes, and copies are in a step's
record only. So a record's effect on the keys outside reclaim's prefix is its
action's and its copies', and its copies put again the values the scan read.
The row's key is the model's, `reclaimRow`:
Java's `-current.txt` under `/#i/dreclaim/` (bergdb 030-39, F1; from
2026-11-20 to 2026-11-23 C-STEP took it from the trace's first step, the
key of its one put that was not such a rewrite), and every step must put
the row at it. Also: a STEP line in every record with a TOUCH line and
in no other; and per CUT line, the iteration with its c has its last
step, with eod, at the CUT's first available time. The STEP
line is not part of the grammar that the contract's checkers read
(`lineKinds`), so their traces (`treeconf.sh`) have none; the traces of
`conformance.sh reclaim` have them.

Since bergdb 030-31 (2026-11-20) run A may restart its database: the
exporter's `restart=K` (a sync, `stop()` and a start from a copy of the
stream after every K-th user transaction's call), `crash=K` (the database
fails right after the K-th step's record is durable, inside its call, and
starts again from a copy of the stream; since bergdb 031-06 the step's record
is a commit's or a part's, and its STEP line is made at its record) and a recorded
application's restarts (`workload=F`). The start appends no record; the
last record before it gets the lines:

    RESTART k                    in TX i, after the reclaim lines: run A's
                                 database started again after R(i), k is
                                 `stop` or `crash`; one a transaction
    RESUME t0 c L E              with `steps=1`, after RESTART: the iteration
    RESUME -                     in progress that the start read from the
                                 stream (`Reclaim.currentIteration()`), its
                                 t0, c and L as on a STEP line and E its
                                 endKey, the greatest key live at tStart (`-`
                                 for none); `-` alone for no iteration

Until bergdb 031-06 a step that the crash ended had its STEP line from the row
that the start read, the row the step committed (its L' and eod); since then a
step's record holds its row, and the STEP line is made at the record. C-STEP's
STEP-resume
checks each RESUME line: the row is the iteration's row as its last step
left it (the same c, lastKey that step's L', the iteration not ended by a
step with eod), or, for an iteration without a step yet, lastKey none
after an iteration ended by a step with eod, with a later t0 and c ≤ t0 +
1; its E is the greatest key live after T(t0); and the first step after
the restart goes on from it (its t0, c and L the RESUME line's). The
contract's checkers do not read RESTART and RESUME lines (`lineKinds`):
their traces of a recorded application are replayed without its restarts
(`apprestarts=0`), which writes the same records.

The reads of the GET and SCAN lines are at random times from the first
available time on, of keys of the workload, `gets=N` GET lines and one
SCAN line a transaction (default 4; with `gets=0` none), from a generator
of their own: a trace's workload is the same with and without `tree=1`.

A key node made without an entry has one time klong and no other (`KN x l
1 T t`): the primordial key node, and an empty space root that a
transaction made (since record format 8: PE's space root left with no
entry, when it was an inner node, or a segment leaf that could not take
the transaction's bitmap; until then a space root that a delete emptied
by a time split). Its history is empty, so the ADD lines do not show it;
the tree model has an entry for it, the marker (lean/SIS/Tree/Node.lean,
`marker`: a delete entry without compare values), which `treecheck` adds
to a key node made without entries and leaves out when it compares
entries.
