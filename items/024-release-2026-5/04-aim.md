# 024-04. The aim of release 2026.5: solid algorithms

Created 2026-11-11 by Frans Lundberg. Status: open.

The theme and the aims of release 2026.5, as Frans decided them on
2026-11-11 in a discussion with the day's coordinator (coord-1111). The
theme changes from "a stable stream format" (2026-11-10, 19:54; 024's
log) to **solid algorithms**. This is the document that the release's
other work cites: "024-04, aim 2".


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

* 06:44: "I first though that "stable stream" should be the theme of the
  release. But after sleeping on it, I am more more leaning towards
  "solid algos". Release 4 changed quite a bit. And there is some more
  work to do. The internal core algorithms of the database must be right.
  This is what we want to prove correct. And not change later. So, solid
  algorithms perhaps comes before a "stable stream"?"
* 06:50, on aims 2 and 4: "That is good! Also, something about KVs stored
  do not cost (disk, memory) out of proportion to its count and size. So,
  both storage and operations are proportional to the value they bring to
  the user." Aim 3 and the one line come from this.
* 06:50, asked whether "solid" is mainly the worst-case behaviour or
  mainly the model and the proof catching up: "Both."
* On the wording of section 1: "Create a subitem nn-aim for this release
  theme/aims as stated by you above".


## 3. Why the algorithms come first

The coordinator's reasons, in short:

* **The stream format is the algorithms' output**, so it cannot be stable
  before they are. 2026.4 showed it: the cleanup (023) took the record
  format from 5 to 6, with the same byte layout and a new meaning of a
  record's deletes, and a start refuses format 5 (023-07, section 5.8;
  024-02, "What it builds on").
* **The known open work is algorithmic and changes what is written.**
  The last touch of a reclaim iteration (024-03, section 7, CL7) and the
  underfilled nodes after scattered deletes (024-03, section 5, CL2) are
  the two faults measured at 10M keys. A fix of the last touch changes
  the bytes a database writes, not the format (024-01, section 4.7).
  Merges, the fix of the underfill, are the piece that 2026.4 put off
  with a format cost: out of format 6 they need a later format that
  refuses 2026.4's databases, or two rerun paths (023-07, section 9.1,
  Z12; 024-02, section 20, Q1).
* **A proof is worth its cost only on algorithms that stay.** Today the
  Lean model is not changed for 2026.4's deletes: it has no delete rule
  of its own (docs/sis-model.md, section 3.4).


## 4. Making it checkable

"Proportional" needs constants. Aims 2 and 3 each become a short list of
bounds, each with a test, as 023-03 did for the deletes (its tests T1 to
T12 and pass criteria C1 to C12, counts against a twin before times).

The known cases against the aim today, from 024-03 (release 2026.4 on
F53, one run each):

| Aim | Case                              | Measured at 10M keys                        |
|---|---|---|
| 2   | CL7, the last touch (section 7)   | a record of 191 to 206 MB, a commit of 21 s |
| 2   | CL2, the underfill (section 5)    | 11 to 16 x the twin's key nodes             |
| 3   | MEM, heap bytes a KV (section 3)  | 327; at 1M KVs 129.6; key shape (024-08)    |

* **CL7.** Once a reclaim iteration with keys in time order; the commits
  took 20.6 and 22.2 s. At 1M live keys: 17 MB and 1.7 s. It grows with
  the live keys, and is old (2026.3 too).
* **CL2.** All but every 30th key deleted. Reclaim does not bring the
  node count down (55 iterations). After 300,000 transactions of
  overwrites: scans 4.6 times slower than the twin's, 3.3 times the bytes
  written a transaction, 2.6 times the stream kept; so a case of aim 3
  too.
* **MEM.** 129.6 at 1M KVs is the figure that `level1.sh`'s MEM limit
  guards (129 to 130). At 10M KVs the same method gives 2.5 times that,
  in 2026.3 as in 2026.4.

Two investigations own the details:

* **024-05**, the aim against the known cases: the list, the bounds, the
  tests.
* **024-06**, the model gap: what the Lean model covers of 2026.4's
  algorithm.


## 5. The stream format

The stable stream format follows in release 2026.6 (026), when the algorithms
have stopped moving. Until then:

* **The specification's draft (024-02) is kept current** with the code.
* **Its cheap strictness questions may still be done in 2026.5**: Q14
  (reserved bytes are zero) and Q16 (an unknown node type or format is
  refused), in 024-02, section 20. They prepare stability without
  promising it. Not yet decided by Frans.
* **Not changed by the new theme:** 2026.5 need not open 2026.4's
  databases (Frans, 2026-11-10, 19:49; 024's log), so an algorithm that
  costs a new record format may take it.


## 6. Log

2026-11-11. Written (06:55 to 06:57) from the coordinator's wording of
the aim, approved by Frans, and Frans's words of 06:44 and 06:50. The
figures of sections 3 and 4 were checked against 024-03, 023-07, 024-01
and 024-02.
