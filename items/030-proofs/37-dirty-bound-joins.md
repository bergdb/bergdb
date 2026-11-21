# 030-37. The dirty-node bound through joins

Created 2026-11-21 by Frans Lundberg. Status: open.

Extend 030-36's mixed-operation bound through PE's joins, retaining
030-29's and 030-36's statements. The unrestricted bound is the target.
The result below covers all leaf joins and one level of inner joins,
and, after every history PE writes from the empty tree, needs no fill
premise (section 9); higher inner joins remain open.

## 1. Result

The top theorem is `Contract.PE.pe_dirtyNodeBound_twoJoinLevels`, next
to the earlier theorems in `Contract/Proof/DnbMain.lean`:

```lean
theorem pe_dirtyNodeBound_twoJoinLevels {b G H : Nat} (hb : 8 ≤ b)
    {t i : Time} {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
    (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (hNo : NoHigherJoins (Cfg.java b G H) i s ops)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s t (opsKd ops)
```

In words: from a state satisfying PE's invariant and the fill rules,
every accepted transaction of puts and deletes with valid original keys
writes at most Java's dirty-node count, provided it joins only segment
leaves and inner nodes immediately above leaves. There is no limit on
the number of those joins, including their recursive leaf rebalances,
untouched neighbours and groups already joined. This holds throughout
the tree, at every depth and key segment, at every node size b ≥ 8,
including 8, 14, 30 and 62.

`pe_dirtyNodeBound_twoJoinLevels_hist` states the same bound for the next
transaction after every history PE writes from the empty tree. Earlier
transactions are unrestricted and may contain higher joins. The current
fill rules, original-key validity and the next transaction's restriction
on higher joins remain premises.

`pe_dirtyNodeBound_heightTwo` needs no join restriction when the space
tree has height at most two and every operation has a one-segment key.
The transaction may grow the tree, empty it, or collapse the root.

The complete leaf-join case is also retained separately:
`pe_dirtyNodeBound_noInnerJoins` and its history form allow every leaf
join, at every depth and segment, while excluding inner joins.
`pe_dirtyNodeBound_leafJoins` and its history form discharge that
restriction for a space tree of height at most one and one-segment keys.

## 2. The restriction on higher joins

`NoHigherJoinsAt` follows PE's old-tree routing, including existing
next-segment trees below leaves. Fresh trees use the independent
fresh-tree bound. At an inner node, every successful child plan at every
fuel and accumulator must either have children of height at most one,
leave fewer than two nonempty children, or find no changed small child.

Thus joins at heights zero and one are unrestricted. At height two and
above, the loop must stop after empty-child removal. The predicate
contains no bound on writes, deletes, Java's count or the number of
joins. It is a sufficient structural condition; no equivalence with a
monitor of just one execution is claimed.

## 3. All leaf joins

`joinLoop_leaf_account` proves the complete leaf loop. Each join consumes
at least one changed small leaf: concatenating payload lists cannot
leave a small result unless both inputs were small. Untouched neighbours
have the old fill rule; planned and previously joined neighbours have
their actual decisions. For j joins:

- key-write cost grows by at most 2j;
- new parent entries grow by at most 3j;
- the child list loses exactly j entries;
- the number of remaining changed small leaves plus j is at most its
  initial value.

`kids_leaf_resources` gives a joint budget for empty-child removal and
the small leaves. An old non-root leaf has at least m entries, so each
empty or small planned leaf consumes a counted delete. The same delete
is not charged once for an empty child and again for a retained small
child. `rebalance_leaf_budget` includes the whole loop and renaming the
parent's first separator; the node induction and root settling then give
the leaf-join transaction theorem.

The retained examples (`DnbJoinsExample`) are histories from the empty
tree at all four supported sizes. Each deletion transaction makes two
leaf joins, includes an untouched neighbour and a previously joined
group, and obtains its bound from the history theorem. Kernel
computations also check that exactly two joins occur.

## 4. One level of inner joins

The false step of 028-21 is not used. An inner group may remain small
after joining a non-small neighbour, then absorb another non-small
neighbour.

`LeafReady` records the actual exit condition of a leaf rebalance. A
remaining small leaf must be alone; its parent's entry list has length
one. The sharper leaf estimate is that a leaf join grows the total
number of parent entries by at most one. Consequently, two individually
rebalanced lists of leaves need at most one further leaf join
(`rebalance_leaf_pair`), including arbitrary cut parts.

For an inner group, the potential counts its changed small inner node
plus its remaining small leaves. `inner_leaf_join_pair` includes the
recursive leaf rebalance and proves that one inner join:

- increases the full key-write cost by at most four;
- increases new parent entries by at most three;
- consumes at least one unit of the combined potential.

If the joined inner node remains small after absorbing a non-small
neighbour, the recursive leaf join consumes the pending small leaf.
This is the case the paper argument missed. The potential still falls.

`joinLoop_inner_leaf_account` proves those estimates for any number of
inner joins. `planned_inner_leaf_resources` and
`plan_inner_resourcesTwo` prove that the initial potential comes from
Java's counted deletes. If a small leaf remains alone, its formerly
filled parent has also lost another child, giving separate allowances
for the small leaf and small parent, even when m = 2. Empty children
and retained potentials use disjoint parts of the budget
(`kids_inner_leaf_resources`).

`rebalance_inner_leaf_budget` consumes at most the four-node reserve per
delete of the children. It proves the parent's loss and changed-entry
estimates, including empty-child removal and renaming. The mutual node
and segment-tree induction (`plan_tree_twoJoinLevels`), root settling,
emit accounting and the unchanged `dirtyNodeBound_eq_sb` give section
1's top theorem.

## 5. What remains

The unrestricted task is not closed.

1. Joins of inner nodes at height two and above. Their recursive
   rebalances can themselves perform repeated inner joins. The
   one-level proof's leaf-pair lemma does not cover that recursion.
2. Fill preservation for states not reached by a PE history: the
   state theorems keep `FillOk` or `RootFilled` as a premise. For every
   history PE writes from the empty tree it is proved (section 9).
3. The complete input domain, including invalid or out-of-range deletes
   removed by `dropNoops`. Original-operation `keyOk` remains a premise.
   Db's cheap estimate and transformation accounting are also outside
   the result, as in 030-29, section 1.

No claim is made that every transaction Java admits is now covered.

## 6. Pinned statements

No statement present at base 591251a5 changes. The old puts and no-join
theorems and their proofs are retained. The only previously pinned files
whose hashes change are `Axioms.lean` (additional axiom checks) and
`Contract/Proof/DnbMain.lean` (new imports and theorems).

`pin.sh` regenerates `statements.pin`: 137 files, previously 125. The
new pinned closure consists of `DnbDelDrop`, `DnbInnerBudget`,
`DnbInnerJoins`, `DnbInnerLeaves`, `DnbInnerLoop`, `DnbLeafJoins`,
`DnbLeafRebalance`, `DnbLeavesDefs`, `DnbLeavesPlan`, `DnbTwoDefs`,
`DnbTwoResources` and `PeSettle`, all in `Contract/Proof/`. Existing
`DnbDelDrop` and `PeSettle` are unchanged; they enter the closure because
the new statements use their definitions. These are file-level pins;
no earlier theorem type is weakened or replaced.

## 7. Proposed sentences for 030-26, section 2.7

030-26 is left unchanged. After its no-join result, replace the remaining
sentences about joins with:

> The bound also covers every join of segment leaves and every join of
> inner nodes immediately above leaves, including repeated joins with
> untouched neighbours and already joined groups, and the recursive leaf
> rebalances (`Contract.PE.pe_dirtyNodeBound_twoJoinLevels`, 030-37).
> This holds at every depth and key segment, under the same state, fill
> and original-key conditions, provided no higher inner nodes join. The
> same conditional bound holds after every history PE writes from the
> empty tree (`pe_dirtyNodeBound_twoJoinLevels_hist`). For joins of inner
> nodes at height two or above, the general bound remains tested, not
> proved. Fill preservation and coverage of invalid deletes removed
> before planning also remain open.

## 8. Validation

On the uncommitted tree, `lake build`, `pin.sh` and the gate passed:

```text
1. lake build passes
2. no sorry, admit, native_decide or axiom
3. the standard axioms only (244 theorems)
5. the statements pinned: 116 files of the main theorems' closure, 137 pinned
GATE OK
```

The independent pin check printed:

```text
the pins' own test: a changed and a removed pinned file fail, as they must
137 files have their pinned hashes (lean/contract/statements.pin)
PINS OK
```

## 9. The fill premise proved for histories

Added after sections 1 to 8 were written, in the same work. The root of
every tree PE writes from the empty tree is filled (`RootFilled`, in
`Contract/Proof/DnbFillHistory.lean`): `pe_rootFilled_hist`, for every
history, higher joins in it included. With it:

- `pe_dirtyNodeBound_twoJoinLevels_filled`: the two-level bound of
  section 1 with `RootFilled` in place of `FillOk`.
- `pe_dirtyNodeBound_twoJoinLevels_history`: after every history PE
  writes from the empty tree, the next transaction's key-node writes are
  at most Java's count, with no fill premise. What stays restricted is
  the next transaction: no joins of inner nodes at height two or above
  (`NoHigherJoins`), and valid original keys.
- `pe_dirtyNodeBound_heightTwo_history`: the same with no join premise,
  when the next transaction has one-segment keys and the space tree has
  height at most two.

Section 7's sentences for 030-26 apply with the fill condition dropped
for histories. The re-pinned tree's checks, on 2026-11-21:

```text
3. the standard axioms only (252 theorems)
5. the statements pinned: 123 files of the main theorems' closure, 144 pinned
GATE OK
144 files have their pinned hashes (lean/contract/statements.pin)
PINS OK
```

No statement present at base 591251a5 changes; `Axioms.lean` and
`DnbMain.lean` gain checks and theorems only.

## State

2026-11-21. All leaf joins and one level of inner joins are proved,
including transaction and history bounds; for histories from the empty
tree without a fill premise (section 9). Higher inner joins and the
original-key premise remain open. Changes are left in
the working tree; no commit is made.

## Log

2026-11-21. Continued the leaf-join proof, rebuilt it, proved the
sharper leaf-entry estimate, the recursive leaf-pair result, the inner
join potential and its delete budget, and the two-level transaction
and history theorems. The gate and pin check pass. Later the same
night: the fill premise proved for every PE history (section 9); the
work stopped on a usage limit before re-pinning, and the tree was
re-pinned and gated when it was landed.
