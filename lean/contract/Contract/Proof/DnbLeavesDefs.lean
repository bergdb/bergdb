/-
bergdb 030-37: leaf joins are unrestricted throughout every segment tree.
Only joins of inner nodes are excluded by `NoInnerJoinsAt`. The predicate
contains structural conditions on the actual routing and successful child
plans, and no bound on writes or on Java's count.
-/
import Contract.Proof.DnbLeafRebalance

namespace Contract.PE

open DNB PeProof

/-- Follow the old tree as PE routes operations. At inner nodes of height
at least two, the join loop must stop after dropping empties. At height
one, all joins of segment leaves are permitted. -/
def NoInnerJoinsAt (cf : Cfg) (i : Time) (s : Tree) :
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
          | some y => subsOf g ops cv ≠ [] → NoInnerJoinsAt cf i s fs y (g + 1) (subsOf g ops cv)
      else
        (∀ e ∈ lv.zip (route (segAt g) lv ops), e.2 ≠ [] →
          NoInnerJoinsAt cf i s fs e.1.2 g e.2) ∧
        ∀ (f h : Nat) (a : Acc) (es : List (Nat × VN)) (a' : Acc),
          Shaped cf s g (h + 1) x →
          planKids cf i s f g (h + 1) lv (route (segAt g) lv ops) a = some (es, a') →
          h = 0 ∨ (es.filter (fun e => !e.2.isEmpty)).length < 2 ∨
            findSmall cf (es.filter (fun e => !e.2.isEmpty)) = none

def NoInnerJoins (cf : Cfg) (i : Time) (s : Tree) (ops : List Op) : Prop :=
  match s.root with
  | none => True
  | some r => NoInnerJoinsAt cf i s (s.fuel r) r 0 ops

theorem noInnerJoinsAt_leaf {cf : Cfg} {i : Time} {s : Tree} {fs x g : Nat}
    {ops : List Op} {n : KNode} (hk : DNB.getKey s x = some n) (hl : n.leaf = true)
    (he : ∀ op ∈ ops, op.key.length = g + 1) : NoInnerJoinsAt cf i s fs x g ops := by
  cases fs with
  | zero => trivial
  | succ fs =>
    simp only [NoInnerJoinsAt, hk, hl, ↓reduceIte]
    intro cv _
    cases (live n.ks).lookup cv with
    | none => trivial
    | some y =>
      intro hn
      apply False.elim (hn ?_)
      unfold subsOf
      rw [List.filter_eq_nil_iff]
      intro op hop
      have hp := he op (List.mem_of_mem_filter hop)
      simp [endsAt, hp]

/-- No inner-node join is possible when the tree has height at most one
and the operations end at its segment. Leaf joins remain unrestricted. -/
theorem noInnerJoinsAt_shallow {cf : Cfg} {i : Time} {s : Tree} {fs x g h : Nat}
    {ops : List Op} (hsh : Shaped cf s g h x) (hh : h ≤ 1)
    (he : ∀ op ∈ ops, op.key.length = g + 1) : NoInnerJoinsAt cf i s fs x g ops := by
  cases h with
  | zero =>
    obtain ⟨n, _, hk, _, hl, _, _⟩ := shaped_getKey hsh
    exact noInnerJoinsAt_leaf hk (by simpa using hl) he
  | succ h =>
    have h0 : h = 0 := by omega
    subst h0
    cases fs with
    | zero => trivial
    | succ fs =>
      obtain ⟨n, hobj, hk, hlev, hl, _, _⟩ := shaped_getKey hsh
      have hleaf : n.leaf = false := by simpa using hl
      obtain ⟨_, hkids⟩ := shaped_inner hsh hobj
      have hkD : DNB.getKey s x = some n := hk
      simp only [NoInnerJoinsAt, hkD, hleaf, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro e hem _
        have hmem := (List.of_mem_zip hem).1
        obtain ⟨m, _, hkm, _, hlm, _, _⟩ := shaped_getKey (hkids e.1.1 e.1.2 hmem)
        exact noInnerJoinsAt_leaf hkm (by simpa using hlm) (fun op hop => he op
          ((route_sub (segAt g) (live n.ks) ops e.2 (List.of_mem_zip hem).2).subset hop))
      · intro f ht a es a' hs _
        left
        obtain ⟨m, _, hkm, hlevm, _, _, _⟩ := shaped_getKey hs
        rw [hk] at hkm
        cases hkm
        simp only [Cfg.lev] at hlev hlevm
        omega

theorem noInnerJoins_shallow {cf : Cfg} {i : Time} {s : Tree} {ops : List Op}
    (hsh : ∃ r, s.root = some r ∧ Shaped cf s 0 (htIn cf s r) r)
    (hh : ∀ r, s.root = some r → htIn cf s r ≤ 1)
    (he : ∀ op ∈ ops, op.key.length = 1) : NoInnerJoins cf i s ops := by
  obtain ⟨r, hr, hs⟩ := hsh
  simpa only [NoInnerJoins, hr] using
    noInnerJoinsAt_shallow (i := i) (fs := s.fuel r) hs (hh r hr) he

/-- The mixed-operation node induction with arbitrary leaf joins. -/
def PlanLeaves (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
    (fs : Nat), Shaped cf s g h x → (∃ lo hi, Good s x lo hi) → Filled cf s isRoot x →
    OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoInnerJoinsAt cf i s fs x g ops →
    plan cf i s F x g h ops acc = some (v, acc') →
    PlanSpecD b s g h x isRoot v acc acc' (sbPlan b s fs x g ops isRoot)

def TreeLeaves (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (y : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId) (acc' : Acc)
    (fs : Nat), Shaped cf s g (htIn cf s y) y → (∃ lo hi, Good s y lo hi) → Filled cf s true y →
    (∀ n, DNB.getKey s y = some n → live n.ks ≠ []) →
    OpsD g ops → ops ≠ [] → s.fuel y ≤ fs → NoInnerJoinsAt cf i s fs y g ops →
    planTree cf i s F (some y) g ops acc = some (res, acc') →
    TreePD y res acc acc' (sbPlan b s fs y g ops true)

end Contract.PE
