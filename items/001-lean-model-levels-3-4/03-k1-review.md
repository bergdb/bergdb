001-03. The K1 review: the Level 4 design
==========================================

By Claude (Opus 5.5, Claude Code), 2026-10-17, for Frans Lundberg. WP E7 of
the plan [01-plan.md](01-plan.md) (section 3, K1); the work is logged in
[02-progress.md](02-progress.md). Stage 2 of the plan, the Level 4 model, is
done: every theorem it asks for is proved. K1 needs your decision, because one
of its conditions for an automatic pass does not hold.


1. What to decide
=================

K1 decides the Level 4 design. It passes automatically if "Option K, every
theorem of stage 2 proved, A6 and TREE hold on every Java run checked, and no
format or public API change is needed" (plan, section 3). Three of the four
hold. A6 does not: it fails in 5 of 68,901 Java-tier transactions. The proofs
do not use A6; they use a weaker form, A6', and a second property, A-COPY,
which both hold in every Java transaction checked.

1. **The reference rule: Option K, under TREE, A6' and A-COPY instead of A6.**
   Recommended. Option K keeps Level 2's rule (every version names the latest
   version of every pointee, live or dead), so the records, the format and
   every existing database stay as they are. Option F would change the
   records and the format. Section 3 below says what the three assumptions
   are and how they were checked.
2. **The Java changes** of
   [level4-alignment.md, section 6](08-level4-alignment.md): six
   before eviction (WP R8), which keep every record (checked byte for byte
   against `l34-base`), and the eviction work of J1 to J10. Recommended as
   listed.
3. **One change to the trusted Lean model that E5 made**: rule 4 (the
   startup links the pinned objects' slots by node id) now links the root's
   object too, not only D's objects
   ([level4-alignment.md, 5.13](08-level4-alignment.md); register
   M44). It asks nothing of Java, whose virtual root holds the super root by
   reference, and changes no record. Recommended to accept.
4. **Format and public API**: no change is needed. Nothing to decide.

If you confirm 1 to 3, K1 has passed: R3 to R8 and stage 4 may start. Please
record your decision in [02-progress.md](02-progress.md), under "Frans's go
and decisions", or give it in the prompt.


2. What is proved
=================

All in `lean/SIS/PhysTheorems.lean`, the trusted statements, each with a
comment in plain English; the proofs are in `lean/SIS/Proof/Evict*.lean`
(about 10,900 lines). Each depends only on Lean's standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). The runs are those of
BergDB's algorithm (`javaTest`, with marking) that meet the Level 2
assumptions (`RunOK`), those of the physical layer (`PhysRunOK`) and those
of stage 2 (`EvictRunOK`: TREE, A6', A-COPY), with any cache schedule: any
reads, unswizzles and releases after each transaction.

| Theorem | In plain English | WP |
|---|---|---|
| T-CACHE (`TC_records`) | The physical writer with eviction appends exactly the model's records and leaves the model's D; INV-CAN, INV-SNAP and INV-SLOT hold after every operation | E3 |
| D closed upward (`T15_closed`) | A written current node with a node of D below it is in D; a current node not in D has no pointee in D and names the latest version of each pointee | E3 |
| T-READ (`TR_view`, `TR_view_restarts`) | A read through the Level 4 loader at any time up to the last record gives P at that time, in every state such a run reaches | E4, E5 |
| T2-C (`T2_cache`) | With restarts after any transactions (the Level 4 startup), the records and D are still the model's, so restarts change no record; the invariants hold for the last startup | E5 |
| T-PIN (`TP_pins`) | Every object outside the pinned set (D's canonical objects and the root's object) may be evicted at any transaction boundary: it has been written, and unswizzling its memory slots and releasing it removes it; the theorems above hold for every schedule | E6 |
| T-INDEX | The physical writer computes references from slots, the pinned set by node id and Rule R's section map; never from a map of every node id. By the definitions ([level4-alignment.md, 5.14](08-level4-alignment.md)) | E6 |

Stage 1's theorems, which stage 2 builds on: lemma M (`LM_newer`,
`LM_ruleR`, `LM_cutTo`), T1-L (`T1_lazy`), CC (`CC_canonical`) and T2-L
(`T2_lazy`). The proofs' outlines are in
[level4-alignment.md](08-level4-alignment.md), 5.11 to 5.14.


3. What is assumed, and how it was checked
==========================================

The three assumptions of stage 2 are properties of each transaction of a
run, in `lean/SIS/Evict.lean` (`EvictStep`, `CopyStep`, `EvictRunOK`). They
are checked on Java's runs, not proved for Java.

* **TREE** (`treeAt`): every node reachable at i, the root aside, is the
  live child at i of exactly one node reachable at i.
* **A6'** (`adoptAt`, no adoption, the weaker form): for every node x
  reachable at i and every pointee y of x that is not a live child of x at
  i, y is a data node, or not reachable at i, or reachable at i from x
  through live pointers. A6, the stronger form that the plan assumed, asks
  that y be a data node or not reachable.
* **A-COPY** (`CopyStep`, added by E3): every pointer of a new entry of
  transaction i names a node that i creates, a node of the writer's paths,
  or a pointee of one.

| Check | Transactions | TREE | A6 | A6' | A-COPY |
|---|---|---|---|---|---|
| Java tier (`java/stress/A2A3Check2.java`), the 21 configurations of level2-alignment.md, 10.5 | 68,901 | 0 failures | 5 failures | 0 | 0 (of 487,786 new pointers) |
| Lean tier (the checker), small set | 3,700 (A4); 6,760 (A-COPY) | 0 | 0 | — | 0 |
| Lean tier, medium set | 3,360 (A4); 3,369 (A-COPY) | 0 | 0 | — | 0 |
| Lean tier, large set (C3, 12 traces) | 34,012 | 0 | 0 | — | 0 |

The five A6 failures are of one kind: a transaction creates the root of the
next key segment's tree and splits it in place (`Dag.spaceSplitInPlace`),
so the segment leaf's earlier klong of the same transaction, to the split
node, becomes a dead pointer to a node that is still below the leaf
([level4-alignment.md, section 4](08-level4-alignment.md)). That is
what A6' allows.

Checked by running on the model's own examples (examples 2, 3 and 5, with
restarts and four cache schedules; `lake exe phystest 20 40 evict`): 25,600
transactions, no failure of the records, D, the reads or the invariants
(E2). Each theorem was checked by running before its proof (the E3 to E6
entries of the progress log).


4. The changes
==============

To the trusted Lean model (`lean/README.md`, "Changes to the trusted
part"): a new file `lean/SIS/Evict.lean` (E2), the physical layer with
eviction, in which E3 changed three things before committing it (the
writer's walk, the slot of a new pointer, A-COPY; level4-alignment.md, 5.10)
and E5 one (rule 4 and the root's object); and the new statements in
`lean/SIS/PhysTheorems.lean`. Nothing of Level 2 or stage 1 changed.

To the checker and the Java tier: the diagnostics A6, TREE and A-COPY
(`lean/Check/Steps.lean`; `java/stress/A2A3Check2.java`).

To `java/src/` in this run: A3's fix of the top node ordinals (`7f8f2e1`,
register M30) and L5's test-only hook for first touches
(`NodeCollection.FirstTouchListener`, `0cbb4b3`, off unless a test sets it);
and, after E7, R2's and P3's test-only hooks (`Db.TestHooks`, `fa6059b` and
`3b65759`; null unless a test sets them) and a test accessor
(`Reclaim.lastCutRow`). None of them is K1's subject, and none changes a
record (the byte comparison against `l34-base` after each). Every change of
section 6 is still to be made (R8, the J WPs).

The commits of stage 2: `55241f9` (E1), `640c846` (E2), `25ade9d` (E3),
`095ae73` (E4), `099fc57` (A-COPY on Java), `fe99e16` (E5), `7d28376` (E6),
and this WP's.


5. The Java work, estimated
===========================

At the plan's sizes (S up to 2 hours of agent time, M 2 to 8, L 8 to 24):
R8 (M), J1 (M), J2 (M), J3 (L), J4 (M), J5 (M), J6 (M), J7 (M to L), J8 (M),
J9 (S) and J10 (S to M), about 24 to 114 hours in all, besides machine time
for the larger-than-memory run (J8) and the soak with eviction (P4). R8
comes after the Level 3 model (R3 to R7), which also waits for K1; J1 after
K3. The stage 2 WPs of the model took less than their sizes (E1 to E7: about
6.3 hours against 16 to 66 planned), but Java work runs the gates (about 20
minutes a time) and the byte comparison for each change.


6. How to reproduce the decisive checks
=======================================

In `lean/` (Lean 4.34.1, no Mathlib):

    lake build                      # every proof; no warnings
    lake exe phystest 20 40 evict   # the model with eviction, run (2.5 min)

and `#print axioms` of the theorems above, as `lean/README.md` shows. In
`java/`, after `./build.sh`, the Java tier (TREE, A6, A6', A-COPY):

    java -ea <config> -cp build/bergdb.jar:build/stress bergdb.dag.A2A3Check2

for each configuration of
[level2-alignment.md, 10.5](../011-docs-archive/11-level2-alignment.md) (for example
`-Dmaxnode=8 -Dkeys=1000 -Dn=50 -Dexact=1 -Dops=40 -Ddel=25 -Dlong=1
-Dseeds=10`, which shows A6's failures); its summary has a line for A6, A6'
and TREE, and one for A-COPY; `-DdebugA6=1` prints each failure. The Lean
tier: `java/stress/conformance.sh small` (or `medium`, `large`), whose
checker lists the diagnostics of each trace.


7. Open risks
=============

1. **TREE, A6' and A-COPY are checked, not proved, for Java.** A later
   change to Java's splits or to `TopDs.newSuperRoot` could break them, and
   no gate fails today if one does: `level2.sh` runs the Java tier on three
   configurations but tests other lines of its summary, and the checker's
   diagnostics do not fail `TRACECHECK`. Making them gate checks is small
   (in R8 or J4); C-P (J4) will also check INV-SLOT itself on Java's
   physical states.
2. **The model is sequential.** Readers beside the writer and beside
   eviction are Java's (Q8, M39, J5), checked by tests, not proved.
3. **Java's pins beyond the model's** (the record being written, the objects
   of an operation in progress) are atomic in the model (5.8). J1's audit
   checks the pinned set at transaction boundaries.
4. **R8 changes the code that writes every record** (`resolvePointers`, the
   loader, the startup). The proofs say the model's rule gives today's
   records; the byte comparison against `l34-base` checks that Java's does.
5. **Time.** Stage 2's time box of 60 hours started at 2026-10-16 23:14;
   stage 2 used about 6.3 hours of it (to 2026-10-17 05:31).
