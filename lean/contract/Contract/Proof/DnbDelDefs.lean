/-
bergdb 030-36: what the induction says of PE's plan of a transaction of puts
and deletes against Java's count, node by node (`PlanSpecD`), and of a
segment's tree from its root (`TreePD`); the operations (`OpsD`).

With deletes a node can lose entries, be emptied or collapsed into its
only child. The no-join induction retains the four-node allowance for each
delete through a node (`4 * nd`) as an explicit reserve (`T ≥ nd`). Extending
this accounting through the loop of joins remains open.
-/
import Contract.Proof.DnbTop

namespace Contract.PE

open DNB PeProof

/-- Operations at segment g: well-formed keys of more than g segments, puts
and deletes. -/
def OpsD (g : Nat) (ops : List Op) : Prop :=
  ∀ op ∈ ops, keyWf op.key = true ∧ g < op.key.length

/-- The calls selected by the same routing as PE and the bound. At an
inner node, after empty children are removed, the join loop stops immediately:
there is fewer than two children or no changed small child. A lone small child
is allowed, including through a chain of root collapses. -/
def NoJoinsAt (cf : Cfg) (i : Time) (s : Tree) :
    Nat → NodeId → Nat → List Op → Prop
  | 0, _, _, _ => True
  | fs + 1, x, g, ops =>
    match DNB.getKey s x with
    | none => True
    | some n =>
      let lv := live n.ks
      if n.leaf then
        ∀ cv ∈ touched g ops,
          match lv.lookup cv with
          | none => True
          | some y => subsOf g ops cv ≠ [] → NoJoinsAt cf i s fs y (g + 1) (subsOf g ops cv)
      else
        (∀ e ∈ lv.zip (route (segAt g) lv ops), e.2 ≠ [] →
          NoJoinsAt cf i s fs e.1.2 g e.2) ∧
        ∀ (f h : Nat) (a : Acc) (es : List (Nat × VN)) (a' : Acc),
          Shaped cf s g (h + 1) x →
          planKids cf i s f g (h + 1) lv (route (segAt g) lv ops) a = some (es, a') →
          (es.filter (fun e => !e.2.isEmpty)).length < 2 ∨
            findSmall cf (es.filter (fun e => !e.2.isEmpty)) = none

/-- No joins at the calls routed from the space root. Empty child removal
and root collapse are allowed. This is an extra premise, not a property
proved for arbitrary deletes. -/
def NoJoins (cf : Cfg) (i : Time) (s : Tree) (ops : List Op) : Prop :=
  match s.root with
  | none => True
  | some r => NoJoinsAt cf i s (s.fuel r) r 0 ops

/-- What the induction says of a node x of the tree before, planned into v at
height h of segment g (`isRoot`: a segment tree's root), against Java's count r
of x with the same operations. -/
structure PlanSpecD (b : Nat) (s : Tree) (g h : Nat) (x : NodeId) (isRoot : Bool) (v : VN)
    (acc acc' : Acc) (r : SR) : Prop where
  shape : ∃ n es Fl dec, DNB.getKey s x = some n ∧ v = .node (some x) g h false es Fl dec ∧
    (∀ k, dec = .parts k → 0 < r.ov ∧ k ≤ r.parts) ∧
    (live n.ks).length ≤ Fl.length + r.nd ∧
    Fl.length ≤ (live n.ks).length + (Fl.filter (isAdded (live n.ks))).length
  kw : ∃ T, r.nd ≤ T ∧ kw acc' + vcost v + rootT b r isRoot + 4 * T ≤ kw acc + r.cnt
  up : r.up = (if isRoot = true ∧ 0 < r.nd then r.ci else 0) +
    (if r.ov = 0 then 0 else if isRoot = true then r.ov + 1 else r.parts)
  parts : r.ov ≠ 0 → r.ov + 1 ≤ r.parts
  ci : r.nd ≠ 0 → h ≠ 0 → 1 ≤ r.ci

/-- What the induction says of a segment's tree from its root y (`planTree`),
against Java's count r of y as a tree's root: the key nodes written; a tree
emptied has a delete through its root; a new root, or the same, is y itself
unless Java gives the leaf above a klong for it. -/
def TreePD (y : NodeId) (res : Option NodeId) (acc acc' : Acc) (r : SR) : Prop :=
  kw acc' ≤ kw acc + r.cnt ∧ (res = none → 0 < r.nd) ∧ (∀ y', res = some y' → y' = y ∨ 1 ≤ r.up)

/-- plan at fuel F meets `PlanSpecD`. -/
def PlanPD (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
    (fs : Nat), Shaped cf s g h x → (∃ lo hi, Good s x lo hi) → Filled cf s isRoot x →
    OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoJoinsAt cf i s fs x g ops →
    plan cf i s F x g h ops acc = some (v, acc') →
    PlanSpecD b s g h x isRoot v acc acc' (sbPlan b s fs x g ops isRoot)

/-- planTree from a root at fuel F meets `TreePD`. -/
def TreePPD (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (y : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId) (acc' : Acc)
    (fs : Nat), Shaped cf s g (htIn cf s y) y → (∃ lo hi, Good s y lo hi) → Filled cf s true y →
    (∀ n, DNB.getKey s y = some n → live n.ks ≠ []) →
    OpsD g ops → ops ≠ [] → s.fuel y ≤ fs → NoJoinsAt cf i s fs y g ops →
    planTree cf i s F (some y) g ops acc = some (res, acc') →
    TreePD y res acc acc' (sbPlan b s fs y g ops true)

end Contract.PE
