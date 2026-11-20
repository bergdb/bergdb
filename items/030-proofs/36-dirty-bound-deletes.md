# 030-36. The dirty-node bound with deletes

Created 2026-11-20 by Frans Lundberg. Status: open.

Extend 030-29's bound on PE's key-node writes from puts to transactions
with deletes, including joins and root collapse, at node sizes 8, 14, 30
and 62. The target is every admitted transaction from every retained
state and every history from the empty tree. The result below is partial:
the complete no-join case is proved; the general joins remain open.

## 1. Result

`Contract.PE.pe_dirtyNodeBound_noJoins` is the new top theorem, next to
030-29's puts theorem in `Contract/Proof/DnbMain.lean`:

```lean
theorem pe_dirtyNodeBound_noJoins {b G H : Nat} (hb : 8 ≤ b)
    {t i : Time} {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out}
    (hI : Inv (Cfg.java b G H) t s tp next) (hfill : FillOk b H s)
    (hkeys : ∀ op ∈ ops, keyOk (Cfg.java b G H) op.key = true)
    (hNo : NoJoins (Cfg.java b G H) i s ops)
    (hw : peTx (Cfg.java b G H) i s tp next ops = some o) :
    keyWrites o.ws ≤ dirtyNodeBound b s t (opsKd ops)
```

In words: at every node size b of at least 8, take a state satisfying
PE's `Inv` and the fill rules checked by `FillOk`. A transaction may
contain both puts and deletes, with every original key well formed and
within the model's segment limit. If its planned children satisfy the
no-join condition and PE accepts it, the number of key nodes written is
at most the unchanged model of Java's `Dag.dirtyNodeBound`, evaluated
at the state's latest time t.

This includes deletion of entries, removal of empty children, an emptied
segment tree, an emptied space root, repeated root collapse, puts that
cut nodes, fresh segment trees and new roots above cuts. Only joins of
small nonempty children are excluded. The node-size premise covers 8, 14, 30 and 62.

`pe_dirtyNodeBound_noJoins_hist` gives the same conditional result for
the next transaction after **any** `PeHist` from the empty tree. Previous
transactions may have contained joins. The current state's fill rules
and the next transaction's no-join condition remain premises; the
history theorem does not establish them.

`pe_dirtyNodeBound_leaf` removes the no-join premise when the space root
is a segment leaf and every operation has a one-segment key. It retains
the state, fill, key-validity and acceptance premises. There is no limit
on the number of deletes in this corollary, and the result may cut the
root and grow the tree.

The statements and proofs of `pe_dirtyNodeBound_puts` and
`pe_dirtyNodeBound_puts_hist` are unchanged. Java's count, PE's writer,
Java, the trace checkers and 030-26 are unchanged.

## 2. The no-join condition

`NoJoins` and `NoJoinsAt`, in `Contract/Proof/DnbDelDefs.lean`, follow
the old tree using the same routing as PE and `sbPlan`. At a leaf they
follow the existing next-segment trees for the groups whose keys go on;
new trees use the independent fresh-tree proof. At an inner node they
follow each nonempty routed operation group to its child.

At each inner node the definition also checks successful `planKids`
calls at every fuel and accumulator, with the parent's `Shaped` premise.
After empty children are filtered out, either fewer than two children
remain, or `findSmall` finds no changed small child. Thus the first
iteration of the join loop stops. A lone small child is allowed; this
also permits repeated root collapse.

The condition concerns the list length, child sizes and change flags.
It contains no inequality on writes or on Java's count. It is
sufficient; no equivalence with an execution monitor at the transaction's
particular fuel and accumulator is claimed.

## 3. Proof

The completed parts of 030-29's delete groundwork are integrated with
its existing definitions and proofs. The incomplete interface is
replaced by the explicit no-join condition above.

- **Fresh trees, with arbitrary puts and deletes:** `fresh_le_del` and
  `fresh_le_del_ftb` bound their key writes by Java's `freshTreeBound`
  of their puts. Deletes alone from no tree write no key node.
- **A segment leaf:** `leaf_stepD` counts each changed compare value,
  including deletion of an existing next-segment tree. The loss estimate
  is strengthened to `oldLive.length ≤ finalList.length + nd`: every
  lost live entry consumes a counted delete. The final list's growth,
  decision and key writes satisfy `PlanSpecD`.
- **Empty children:** `kids_drop` bounds the children before rebalance.
  Every empty child requires at least one counted delete. Dropping them
  reduces the write cost; retained children supply at most the parent
  entries Java counts. The parent's list loses at most nd entries.
- **The parent's first separator:** after an empty child is removed,
  renaming the first entry to zero adds at most one to the added count
  and one to the removed count. A deletion pays for these changes.
  With no deletes the first entry is already zero. Consequently the
  total changes fit the propagated entries plus Java's `4 * nd` klongs.
- **Inner nodes:** `inner_stepD` uses those counts and
  `rebalance_filter_only`; `dec_parts_ov_of_zero` then relates PE's
  replacement or cut to Java's overflow count. `plan_tree_noJoins`
  closes the mutual induction for nodes and segment trees.
- **Root settling:** `settle_one` proves that collapsing a root into
  its child, repeatedly if necessary, increases no key-write cost.
  `tree_stepD` and `space_stepD` handle empty roots, collapses and new
  roots above cuts. An emptied inner space root writes its new empty
  leaf within the old root's allowance.
- **The transaction:** `pe_keyWrites_le_sb_noJoins` combines the plan,
  settling and emit bounds, including the empty transaction.
  030-29's unchanged `dirtyNodeBound_eq_sb` converts the structural
  count to Java's walk. The history result uses `pe_meetsTop` to obtain
  `Inv` at the last state.

The four-node allowance is retained explicitly in `PlanSpecD.kw` as a
reserve. The no-join proof does not establish that this reserve suffices
for arbitrary joins.

## 4. A local join result

`leaf_join_cost` in `Contract/Proof/DnbDelJoin.lean` proves a single join
of two **planned segment leaves**, with their actual `decideNode`
decisions at Java's parameters. The first leaf is changed and small;
both bases have at most b klongs and their final lists meet the normal
growth estimate. If `mkNode` makes their joined leaf, then:

- its key-write cost is at most the two separate costs plus 2;
- its new parent entries are at most their separate new entries plus 3;
- if the joined leaf is small, the other leaf was small too.

This is a local result, not a bound for `joinLoop`, one join per level,
or a transaction with joins. In particular it does not justify
028-21's false step for inner joins: an inner join rebalances one level
down, and the joined list's length can shrink there. The constructed
case of 030-29, section 4, remains relevant.

`DnbDelFacts` also retains the parameter and decision facts and proves
that a join shortens its list by one, and that rebalance exits with
fewer than two children or no changed small child. Those exit facts
alone do not count the joins.

## 5. Examples

`Contract/DnbDeletesExample.lean` proves the premises of the new history
theorem can hold with an effective deletion. At each of 8, 14, 30 and 62,
a PE history puts two keys, then deletes one and puts a third. The
history, acceptance, fill and no-join premises are proved. The top
history theorem supplies the bound. Independent kernel computations
show that the old key was present before and is gone after, the new key
is present, and the second transaction writes one key node.

A separate kernel computation at size 8 grows a tree with three leaves
from the empty tree, then deletes all keys in two leaves. The space
root collapses to the remaining old leaf: zero key nodes written, bound
152. `collapse_case` checks this concrete execution and the fill rules.
`collapse_noJoins` proves the no-join premise at every successful fuel
and accumulator, and `collapse_bound` obtains its bound from the general
history theorem as well.

These are proofs by kernel reduction. No random-test count is added to
030-29's evidence.

## 6. What remains

The requested unrestricted theorem is **not proved**.

1. Extend the node induction through `rebalance` when it joins small
   nonempty children. This includes the loop of leaf joins, untouched
   neighbours and already joined groups. The local leaf lemma of
   section 4 does not close that loop.
2. Account for joins of inner nodes and their recursive rebalance one
   level down. A joined node can remain small and absorb another
   non-small neighbour. The induction needs accounting for those
   repeated joins and the pending chains of lone small children. The
   present loss and reserve fields do not establish this accounting.
3. Establish the fill rules throughout PE histories to remove `hfill`.
   As in 030-29, `Inv` and `PeHist` alone do not supply `FillOk` in this
   proof. It remains a checked premise, including in the history form.
4. Remove or discharge the original-operations `keyOk` premise for the
   full input domain. The current theorem does not cover invalid or
   out-of-range deletes that `dropNoops` removes. It also does not add a
   proof for Db's cheap estimate or its transformation accounting
   (030-29, section 1).

Next proof work starts at `PlanSpecD`, `kids_drop`, `leaf_join_cost` and
`inner_stepD`. The existing no-join induction and top theorems can remain
as special cases while the join accounting is extended.

## 7. Pinned statements and files

No theorem present at the base commit changes its type. The old puts theorems
are preserved verbatim. `Contract/Proof/DnbMain.lean` changes to import
the delete proof and add the new theorems; `Axioms.lean` adds their
axiom checks and the checks of the supporting results and examples.
The new statements' closure is pinned with `pin.sh`.

At base bdf7c1ba, 114 files were pinned; the final manifest pins 125.
The only previously pinned files whose hashes change are:

- `Axioms.lean`: twelve additional axiom checks.
- `Contract/Proof/DnbMain.lean`: the new theorems and their import;
  neither old puts declaration nor its proof changes.

Six new proof files are pinned: `DnbDelDefs`, `DnbDelFacts`, `DnbDelJoin`,
`DnbDelLeaf`, `DnbDelTree` and `DnbFreshDel`, all in `Contract/Proof/`.
Five existing, unchanged files enter the trusted closure and are newly
pinned: `DnbDefs`, `DnbLeaf`, `DnbPlan`, `PeAbs` and `PeInst` in the same
directory. They define the new statements' fill, routing, resource and
virtual-node premises. `statements.pin` is regenerated by `pin.sh`.
No other previously pinned file changes.

New Lean files in `lean/contract/`:

- `Contract/Proof/DnbDelDefs.lean`: operations, the no-join condition and
  the induction statements.
- `Contract/Proof/DnbFreshDel.lean`: new trees with puts and deletes.
- `Contract/Proof/DnbDelLeaf.lean`: mixed-operation leaves and their loss.
- `Contract/Proof/DnbDelTree.lean`: settling, empty roots and collapses.
- `Contract/Proof/DnbDelKids.lean`: a child's entries in its parent.
- `Contract/Proof/DnbDelDrop.lean`: dropping empty children.
- `Contract/Proof/DnbDelEntries.lean`: renaming and decision estimates.
- `Contract/Proof/DnbDelPlan.lean`: the mutual no-join induction.
- `Contract/Proof/DnbDelTop.lean`: the transaction against `sbTop`.
- `Contract/Proof/DnbDelFacts.lean`: decisions and rebalance's exit.
- `Contract/Proof/DnbDelJoin.lean`: the local planned-leaf join.
- `Contract/DnbDeletesExample.lean`: effective deletes at all four
  sizes and a root-collapse instance of the general theorem.

`Contract.lean` imports the new join proof and examples. The existing
Java model of the count and the writer are unchanged.

## 8. Proposed sentences for 030-26, section 2.7

030-26 is left unchanged. Add after its puts result:

> The bound is also proved for transactions of puts and deletes whose
> planned children satisfy the no-join condition, under the same state
> and fill rules and with well-formed keys within the model's segment
> limit (`Contract.PE.pe_dirtyNodeBound_noJoins`, 030-36). This includes
> removal of empty children and root collapse. The same conditional
> bound holds after every history PE writes from the empty tree
> (`pe_dirtyNodeBound_noJoins_hist`).

Replace the sentence starting "For transactions with deletes the bound
is tested, not proved" by:

> For transactions with deletes that join small nonempty nodes, the
> general bound remains tested, not proved. A local join of two planned
> segment leaves is bounded in 030-36; repeated joins, especially inner
> joins rebalanced one level down, remain open.

## 9. Validation

On the final uncommitted tree, after `lake build` and `sh
lean/contract/pin.sh`, `sh lean/contract/gate.sh` printed:

```text
1. lake build passes
2. no sorry, admit, native_decide or axiom
3. the standard axioms only (227 theorems)
5. the statements pinned: 104 files of the main theorems' closure, 125 pinned
GATE OK
```

`sh lean/contract/pins.sh` printed:

```text
the pins' own test: a changed and a removed pinned file fail, as they must
125 files have their pinned hashes (lean/contract/statements.pin)
PINS OK
```

The final build has no warnings. Both old puts declarations and their
proofs were compared with the base and are unchanged. Java, `lean/Check/`,
030-26, `DirtyBound.lean`, `DirtyBoundStatement.lean` and `PeWriter.lean`
are unchanged. `git diff --check` passes; the additions were checked for
private data. No commit is made.

## State

2026-11-20. Partial result: mixed transactions without joins, empty-child
removal and root settling proved, with state and history theorems. A local
planned-leaf join is bounded. The general join proof and removal of the
fill premise remain open. Changes are left uncommitted.

## Log

2026-11-20. Created the item. Integrated the delete groundwork, proved
the leaf loss estimate, empty-child and separator counts, the no-join
induction and top theorems, the leaf-root corollary, and the local leaf
join. Added examples at all four node sizes and a root collapse.
