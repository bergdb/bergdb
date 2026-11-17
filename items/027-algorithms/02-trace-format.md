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
                                 after R(0); with reclaim, user transactions and
                                 reclaim's records)

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
WP R2; 001-07, 2.7), every executed transaction is a record:
the user transactions, and reclaim's steps and table stores, each an ordinary
`TX` block, with `kind=user`, `step` or `table` in its comment line. Since
bergdb 015-87 the exporter's call of `setRetainDuration`, before the first
user transaction, commits reclaim's settings (`/#i/dreclaim/-settings.txt`)
in a record of their own, R(1), internal and marked `kind=table`; its calls
after a restart write nothing. Format 2 then also has:

    TOUCH x1 x2 ...              in TX i, after the ADD lines: the index nodes
                                 T(i)'s touch visited (Db.touchPaths: the paths
                                 of its keys; a key range until 024-07), sorted
    FA t                         in TX i, when it changes: fa(i), the first
                                 available time, as a model time
    CUT c t                      in TX i: Java decided a cut at R(i): records
                                 before c may go; t is the first available time
    PHYSCUT c                    in TX i: after R(i), the stream's first position
                                 moved; R(c) is the first record that starts at
                                 or after it

`FA`, `CUT` and `PHYSCUT` come after `DIRTY`. Run B also restarts right after
each call that decided a cut, and looks up only from the first available time
on; its `PROBE` lines are in the block of the last record of the call (the
user record without reclaim).

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
failures.

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
reads over them. `java/stress/treeconf.sh` runs the exporter and
`treecheck`. A key is written as `n c1 ... cn`: the number of its segments
and their compare values (`Keys.toSegments`); `-` stands for no key.

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
                                 the writer's thresholds: mb, the least live
                                 klongs of a key node that is not a root
                                 (Dag.minFill; 1 below node size 8, where
                                 nothing merges); mc, the most live klongs of
                                 a merge's one new node (Dag.mergeCap); sa,
                                 rule O's h, the most klongs of a last version
                                 that a time split keeps (Dag.splitAbove): 8,
                                 17 and 17 at node size 30. Since 024-23 a
                                 ninth token, th: option 2's theta, the most
                                 dead klongs a key node holds after a write
                                 (Dag.theta: 7 at node size 30; 0 below 8,
                                 none). The checker reads a line of 7 numbers
                                 too (theta 0, off), of 4 (2026.4's writer: no
                                 merges, h = M / 2), and of 6 (sa = mc)
    BASE b                       in TX i, i > 0, first: the id of the first node
                                 that T(i) makes; the following get b + 2,
                                 b + 4 and so on, in the order Java makes them
                                 (Db.setIdOfNode; a delete's marker uses one)
    OP P key v                   in TX i, after BASE, in the order the Dag gets
                                 them (Db.putKvs): a put of the key, v the
                                 value's hash (as V's, section 1)
    OP D key                     a delete that deleted
    OP N key                     a delete that changed nothing (not in the
                                 record)
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
                                 j; cumulative, as Java's)
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
8 numbers. The bridge checker (`lake exe bridgecheck`) reads a trace only
if it is whole in the same way. The contract checker's
`LIVE` lines, with `live=1`, are checked against the package's search and the space
root at each time.

A transaction with a TOUCH line (a step of reclaim; section 2) touches the
paths of all the keys of its OP lines (Db.touchPaths, since bergdb 024-07):
the tree model's `touchOf` of those keys must give the TOUCH line. (Until
024-07 the touch was a key range, and format 3 had its bounds as RANGEF and
RANGET lines, on 2026-11-11 only.)

The reads of the GET and SCAN lines are at random times from the first
available time on, of keys of the workload, `gets=N` GET lines and one
SCAN line a transaction (default 4), from a generator of their own: a
trace's workload is the same with and without `tree=1`.

A key node made without an entry has one time klong and no other (`KN x l
1 T t`): the primordial key node, and a space root that a delete emptied
by a time split. Its history is empty, so the ADD lines do not show it;
the tree model has an entry for it, the marker (lean/SIS/Tree/Node.lean,
`marker`: a delete entry without compare values), which `treecheck` adds
to a key node made without entries and leaves out when it compares
entries.
