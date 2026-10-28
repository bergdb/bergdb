012-07. Task: the index nodes
=============================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: not started**; approved with 012-01 by Frans's
go (012-01, 9.1).
Phase B (012-01, section 8). Effort: max. After: 012-04, 012-06.


# 1. The goal

The nodes of the index in C, ported faithfully from `dag`: klongs, key
nodes with their versions, value nodes, top nodes and the top node
structure, with pointers and their serialized references; their writers,
to the bytes Java writes. This is BergDB's core data structure, and the
largest single port (`KeyNode` alone is 1,219 code lines).

Done when:

1. `Klong` complete: every type of klong, its time, length and compare
   value, the order of klongs.
2. Key nodes: their klongs and pointers, the versions and the time index,
   `searchLte` and `searchEq` at a time, adding and changing entries, the
   delete bitmap, `toPreviousState`, the checks (`check()`), and the
   splits and replacements at the maximum node size, as `KeyNode` does
   them.
3. Value nodes, and top nodes with `TopDs`: the super root, top node
   ordinals (up to 2^48 − 1, 005-02), root times, skip pointers,
   `findRoot` at a time, new top nodes.
4. Pointers: a memory pointer or a stream pointer, the node's position and
   id, vpos, and the serialized reference as Java decides it (`Handle`,
   009). The representation chosen here also serves eviction (012-12).
5. Writers: `StoredKeyNode.toLongs`, `StoredTopNode.toLongs`,
   `StoredValueNode.toBytes`, with their checksums; every node of every
   reference stream, parsed (012-06) and written again, gives its bytes.
6. Java's tests of these classes ported where C has the behaviour:
   `KeyNodeTester`, `TopTester`, the `@Nano` tests of `KeyNode`, `Klong`,
   `TopNode`, `TopDs`, `ValueNode`. All pass.


# 2. Read first

* Java, `dag`: `Klong` (191 code lines), `KeyNode` (1,219), `TopNode`
  (245), `ValueNode` (171), `TopDs` (136), `Node` (38), `Pointer` (47),
  `Spos` (26), `Handle` (73), `KlongWithPointer`, `PutData`, `GetData`,
  `OpData`, `AccessData`, `Keys`; their testers.
* `docs/sis-model.md` (nodes, versions, pointers), 011-11 (how Java maps
  onto the model), 009-02, section 3 and 009-05 (handles, serialized
  references), 005-02 (ordinals), 005-50 (node sizes); 012-01, 4.5
  (memory).
* 012-02, sections 6 and 7.


# 3. The work

1. **Design first**, written in this file before the code: the C structs
   of the nodes and of a pointer; how a node is identified (id, the
   canonical object, the node table); what a "handle" is in C
   (recommended: as Java's, a small struct per node with the node's id,
   its object or none, and `writtenPos`, so that a pointer's serialized
   reference is decided as Java decides it; live in the node table, or
   dead after an eviction and freed when no pointer holds it; Java's
   LOADING state serves concurrent loaders, which C does not have); and
   memory as 012-01, 4.5 says. For that, list every field in Java that
   holds an index object, a handle or a value beyond a call (the holders
   that count), and every place that changes such a field, so that each
   change keeps the counts; and the pending list with its safe points.
2. Port `Klong`, then `KeyNode` method by method, keeping Java's names in
   comments (`/* KeyNode.searchLte */`) so that a reader can follow both.
3. `ValueNode`, `TopNode`, `TopDs`.
4. The writers, and the round trip of done item 5 as a test over
   012-05's streams.
5. The ported tests.


# 4. Tests

The ported Java tests; the round trip of every node of the reference
streams; random tests of a key node against a simple model (a sorted list
of (compare value, time, entry)) for searches at random times after
random changes, under the sanitizers; after each change, the recount of
012-01, 4.5 agrees with the counts, and after the last free the
allocator's count is 0.


# 5. Notes

* Faithful before clever (012-01, 4.2): the split points, the order of
  entries, when a TIME klong is added, the sizes at which a node is
  replaced: all as Java, since they decide the bytes. Where Java's code
  looks wrong, write it in this file's notes and keep Java's behaviour; a
  real bug goes to 005 (012-01, section 9).
* Java's integer arithmetic (012-04's rules) matters most here: klongs
  pack lengths, types and times into 64-bit numbers.


# 6. Progress

Not started.
