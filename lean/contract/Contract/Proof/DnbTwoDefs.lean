/-
bergdb 030-37: leaf joins and joins of inner nodes immediately above
leaves are unrestricted, at every depth and through every key segment.
Only joins of inner nodes at height two or more are excluded.
-/
import Contract.Proof.DnbInnerPlanResources

namespace Contract.PE

open DNB PeProof

/-- Follow PE's routing. Children of height zero or one may join; above
that, the join loop must stop after empty children are removed. -/
def NoHigherJoinsAt (cf : Cfg) (i : Time) (s : Tree) :
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
          | some y => subsOf g ops cv ≠ [] → NoHigherJoinsAt cf i s fs y (g + 1) (subsOf g ops cv)
      else
        (∀ e ∈ lv.zip (route (segAt g) lv ops), e.2 ≠ [] →
          NoHigherJoinsAt cf i s fs e.1.2 g e.2) ∧
        ∀ (f h : Nat) (a : Acc) (es : List (Nat × VN)) (a' : Acc),
          Shaped cf s g (h + 1) x →
          planKids cf i s f g (h + 1) lv (route (segAt g) lv ops) a = some (es, a') →
          h ≤ 1 ∨ (es.filter (fun e => !e.2.isEmpty)).length < 2 ∨
            findSmall cf (es.filter (fun e => !e.2.isEmpty)) = none

def NoHigherJoins (cf : Cfg) (i : Time) (s : Tree) (ops : List Op) : Prop :=
  match s.root with
  | none => True
  | some r => NoHigherJoinsAt cf i s (s.fuel r) r 0 ops

theorem noHigherJoinsAt_leaf {cf : Cfg} {i : Time} {s : Tree} {fs x g : Nat}
    {ops : List Op} {n : KNode} (hk : DNB.getKey s x = some n) (hl : n.leaf = true)
    (he : ∀ op ∈ ops, op.key.length = g + 1) : NoHigherJoinsAt cf i s fs x g ops := by
  cases fs with
  | zero => trivial
  | succ fs =>
    simp only [NoHigherJoinsAt, hk, hl, ↓reduceIte]
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

/-- A tree of height at most two with operations ending at its segment
can have only the two levels of joins covered here. -/
theorem noHigherJoinsAt_shallow {cf : Cfg} {i : Time} {s : Tree} {fs x g h : Nat}
    {ops : List Op} (hsh : Shaped cf s g h x) (hh : h ≤ 2)
    (he : ∀ op ∈ ops, op.key.length = g + 1) : NoHigherJoinsAt cf i s fs x g ops := by
  induction fs generalizing x g h ops with
  | zero => trivial
  | succ fs IH =>
    cases h with
    | zero =>
      obtain ⟨n, _, hk, _, hl, _, _⟩ := shaped_getKey hsh
      exact noHigherJoinsAt_leaf hk (by simpa using hl) he
    | succ h =>
      obtain ⟨n, hobj, hk, hlev, hl, _, _⟩ := shaped_getKey hsh
      have hleaf : n.leaf = false := by simpa using hl
      obtain ⟨_, hkids⟩ := shaped_inner hsh hobj
      have hkD : DNB.getKey s x = some n := hk
      simp only [NoHigherJoinsAt, hkD, hleaf, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro e hem _
        exact IH (hkids e.1.1 e.1.2 (List.of_mem_zip hem).1) (by omega)
          (fun op hop => he op ((route_sub (segAt g) (live n.ks) ops e.2
            (List.of_mem_zip hem).2).subset hop))
      · intro f ht a es a' hs _
        left
        obtain ⟨m, _, hkm, hlevm, _, _, _⟩ := shaped_getKey hs
        rw [hk] at hkm; cases hkm
        simp only [Cfg.lev] at hlev hlevm
        omega

theorem noHigherJoins_shallow {cf : Cfg} {i : Time} {s : Tree} {ops : List Op}
    (hsh : ∃ r, s.root = some r ∧ Shaped cf s 0 (htIn cf s r) r)
    (hh : ∀ r, s.root = some r → htIn cf s r ≤ 2)
    (he : ∀ op ∈ ops, op.key.length = 1) : NoHigherJoins cf i s ops := by
  obtain ⟨r, hr, hs⟩ := hsh
  simpa only [NoHigherJoins, hr] using
    noHigherJoinsAt_shallow (i := i) (fs := s.fuel r) hs (hh r hr) he

/-- The mixed-operation node induction with two levels of joins. -/
def PlanTwo (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (x : NodeId) (g h : Nat) (ops : List Op) (acc : Acc) (v : VN) (acc' : Acc) (isRoot : Bool)
    (fs : Nat), Shaped cf s g h x → (∃ lo hi, Good s x lo hi) → Filled cf s isRoot x →
    OpsD g ops → ops ≠ [] → s.fuel x ≤ fs → NoHigherJoinsAt cf i s fs x g ops →
    plan cf i s F x g h ops acc = some (v, acc') →
    PlanSpecD b s g h x isRoot v acc acc' (sbPlan b s fs x g ops isRoot)

def TreeTwo (b : Nat) (cf : Cfg) (i : Time) (s : Tree) (F : Nat) : Prop :=
  ∀ (y : NodeId) (g : Nat) (ops : List Op) (acc : Acc) (res : Option NodeId) (acc' : Acc)
    (fs : Nat), Shaped cf s g (htIn cf s y) y → (∃ lo hi, Good s y lo hi) → Filled cf s true y →
    (∀ n, DNB.getKey s y = some n → live n.ks ≠ []) →
    OpsD g ops → ops ≠ [] → s.fuel y ≤ fs → NoHigherJoinsAt cf i s fs y g ops →
    planTree cf i s F (some y) g ops acc = some (res, acc') →
    TreePD y res acc acc' (sbPlan b s fs y g ops true)

end Contract.PE
