# 024-04. The aim of release 2026.5: solid algorithms

Created 2026-11-11 by Frans Lundberg. Status: open.

The theme and the aims of release 2026.5, as Frans decided them on
2026-11-11 in a discussion with the day's coordinator (coord-1111). This
is the document that the release's other work cites: "024-04, aim 2".


## 1. The aim

**Release 2026.5: solid algorithms.**

1. **Bugs first**, as always. Frans: "Bugs are always prio."
2. **Operations are proportional.** No known case at 1M to 100M keys
   where a Core operation costs time, bytes written or memory out of
   proportion to its work.
3. **Storage is proportional.** The KVs stored cost disk and memory in
   proportion to their count and size. What is deleted or outside the
   kept history costs nothing, eventually: Frans's rule for deletes
   (020-30, section 1), now the general one.
4. **The model matches.** The Lean model describes the algorithm the code
   runs, 2026.4's delete path included, and the proofs hold for it.

In one line: **cost follows value**; both storage and operations are
proportional to the value they bring to the user.

Aim 2 is 010-01's P4 (maintenance proportional to the user's work) and
P1 (no stop-the-world), asked of every Core operation at large sizes.


## 2. Frans's words

2026-11-11, to the coordinator:

* 06:44: "The internal core algorithms of the database must be right.
  This is what we want to prove correct. And not change later."
* 06:50, on aims 2 and 4: "That is good! Also, something about KVs stored
  do not cost (disk, memory) out of proportion to its count and size. So,
  both storage and operations are proportional to the value they bring to
  the user." Aim 3 and the one line come from this.
* 06:50, asked whether "solid" is mainly the worst-case behaviour or
  mainly the model and the proof catching up: "Both."
* On the wording of section 1: "Create a subitem nn-aim for this release
  theme/aims as stated by you above".


## 3. Why solid algorithms

* **The Core's algorithms are what is proved and what is kept.** A proof
  is worth its cost only on an algorithm that stays, so the algorithms
  are made right first, then proved, and then not changed.
* **Release 2026.4 changed them, and work is left.** Its cleanup (023)
  gave the Core a new delete path. Measured at 10M keys afterwards
  (024-03), two old faults stood out: the last touch of a reclaim
  iteration (section 7, CL7) and the underfilled nodes after scattered
  deletes (section 5, CL2). And the Lean model was not changed for the
  new deletes: it has no delete rule of its own (docs/sis-model.md,
  section 3.4; 024-06).
* **Everything else rests on them.** What a database writes, the C
  clone, the specification of the format and its stability follow the
  algorithms, and can settle only when the algorithms have (section 5).


## 4. Making it checkable

"Proportional" needs constants. Aims 2 and 3 each become a short list of
bounds, each with a test, as 023-03 did for the deletes (its tests T1 to
T12 and pass criteria C1 to C12, counts against a twin before times).
024-05 has the list of known cases, the proposed bounds and the tests;
024-06 has the gap between the model and the code.

The cases known when the release began, from 024-03 (release 2026.4 on
F53, one run each), and where each went:

| Aim | Case                    | Measured at 10M keys           | Where it went     |
|---|---|---|---|
| 2   | CL7, the last touch     | a record of 206 MB, 21 s       | fixed, 024-07     |
| 2, 3 | CL2, the underfill     | 11 to 16 x the twin's nodes    | merges, 024-11    |
| 3   | MEM, heap bytes a KV    | 327, against 129.6 at 1M KVs   | key shape, 024-08 |

* **CL7.** Once a reclaim iteration with keys in time order, a step made
  the whole index dirty: commits of 20.6 and 22.2 s, records of 191 to
  206 MB, growing with the live keys; old. It was also two faults (the
  record limit near 104M keys, a small heap: 024-07, 020-33). Fixed: a
  step makes dirty the paths of its own puts only.
* **CL2.** All but every 30th key deleted: reclaim does not bring the
  node count down; after 300,000 transactions of overwrites, scans 4.6
  times slower than the twin's, 3.3 times the bytes written a
  transaction, 2.6 times the stream kept. The fix is merges at the
  delete, with a bound on every key node's fill (024-11; the thresholds
  measured in 024-14).
* **MEM.** Not a cost that grows with the count: the test's keys of
  exactly 7 bytes each get a key node of their own (024-08). The cost
  of key shape is within aim 3 (Frans, section 7): documented, with a
  bound and its runs (024-15).

Two rules that the aim led to, each an item of its own:

* **One operation a key in a transaction, strictly** (024-16): a
  transaction fails at the commit when key transformations make two of
  its keys one key.
* **Limits** (024-17): a key at most 256 bytes, the one limit for a
  user to remember; the limits of a transaction and of a value generous,
  checked in the user's terms; the internal bounds (the nodes edited, a
  record's bytes) proved from them.


## 5. Not in this release: a stable stream format

A stream format that later releases promise to read is the theme of
release 2026.6 (026), when the algorithms have stopped moving. In
2026.5:

* **The specification's draft (024-02) is kept current** with the code.
* **Its cheap strictness questions may still be done**: Q14 (reserved
  bytes are zero) and Q16 (an unknown node type or format is refused),
  in 024-02, section 20. Not yet decided by Frans.
* **An algorithm that costs a new record format may take it**: 2026.5
  may refuse to open 2026.4's databases (Frans, 2026-11-10, 19:49, and
  2026-11-11, 07:23).


## 6. The order of work: model first

Frans, 2026-11-11, 07:23: "I want the proofs. The question is when. What
comes first? If we are sure the algos are indeed correct, then we can do
code first, then model. But, model-first seems attractive to me to
verify our thinking before coding." The coordinator's proposal, which he
accepted (07:27: "Yes, start it."):

A model is a definition in Lean that can be run, with its invariants and
its cost bound stated; it takes days and makes every rule exact before
Java exists. A proof is the costly part and breaks when the design
moves. So, for each algorithm change of 2026.5:

1. a design note;
2. the Lean definition, with the invariants and the bound stated as
   properties to prove;
3. the model run against small exhaustive cases and the fuzz;
4. Java, checked against the model by the conformance steps;
5. the proofs, when the change has settled.

Two exceptions:

* **Proof first** where the model already exists and the property is one
  of safety: whether the last touch's fix keeps the cut correct is
  settled against the model's cut conditions before the fix is called
  done (024-07).
* **Code first** where the code exists: 2026.4's key tree is modelled
  after the fact (024-12). Proofs start in 2026.5 on its old and stable
  parts (search, put, the splits).

Not code first in general, as the algorithms are not known to be right:
023-08's reviews found fault 12 in a branch that had passed level1 to
level4, and the argument for reclaim's scheme rests on a premise that
2026.4 made false (024-06; written again in 024-09).

For 2026.5, "the model matches" (aim 4) so means: the tie repaired
(024-09), the key tree in Lean and run against Java (024-12), new
changes through the model first, the proofs begun on the stable parts
and finished as the algorithms settle.


## 7. Log

2026-11-11. Written (06:55 to 06:57) from the coordinator's wording of
the aim, approved by Frans, and Frans's words of 06:44 and 06:50. The
figures of sections 3 and 4 were checked against 024-03, 023-07, 024-01
and 024-02.

2026-11-11, 07:30. Section 6 added (the order of work, Frans 07:23 and
07:27). Section 4's MEM case is explained by 024-08: the shape of the
keys, not their count.

2026-11-11, 07:30. Frans, asked whether the cost of key shape (024-08:
a stretch of 7 key bytes that no other key shares costs a key node of
its own) is within aim 3: "Yes." So it is documented, with a bound and
its Mem runs (024-08, option (a)); no fix is studied in 2026.5.

2026-11-11, 10:55. Rewritten in place at Frans's word (10:50: "Rewrite
it to reduce or remove "a stable stream format". Less about changes.
Overwrite in place so to say, is better here."): the document states
the aim as it is. Sections 3 to 5 written anew, section 4 with where
each case went; sections 1 and 6 unchanged. For the record: from
2026-11-10, 19:54, to 2026-11-11, 06:44, the release's theme was "a
stable stream format", now 2026.6's (026). Frans's words of 06:44 in
full: "I first though that "stable stream" should be the theme of the
release. But after sleeping on it, I am more more leaning towards "solid
algos". Release 4 changed quite a bit. And there is some more work to
do. The internal core algorithms of the database must be right. This is
what we want to prove correct. And not change later. So, solid
algorithms perhaps comes before a "stable stream"?"

