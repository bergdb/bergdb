/-
Depth in a tree (bergdb 024-22, `OpTreeOK`): in a tree every reached node has
one depth, the length of every path to it from the root (`PathLen.depth_unique`);
a child is one deeper than its parent, so no node is reached from a node below
it, and the path to a parent never passes through its child: a change of the
child does not change what reaches the parent (`tReach_updN_parent`).
-/
import SIS.Tree.WriterTreeInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The lookup with node x replaced by m. -/
def updN (N : NodeId → Option KNode) (x : NodeId) (m : KNode) : NodeId → Option KNode :=
  fun z => if z = x then some m else N z

theorem updN_self (N : NodeId → Option KNode) (x : NodeId) (m : KNode) : updN N x m x = some m := by
  simp [updN]

theorem updN_ne (N : NodeId → Option KNode) (x : NodeId) (m : KNode) (z : NodeId) (h : z ≠ x) :
    updN N x m z = N z := by
  simp [updN, h]

/-- A path of n links from r to z. -/
inductive PathLen (N : NodeId → Option KNode) (t : Time) (r : NodeId) : NodeId → Nat → Prop
  | root : PathLen N t r r 0
  | link {x : NodeId} {c : Nat} {y : NodeId} {n : Nat} :
      PathLen N t r x n → TLink N t x c y → PathLen N t r y (n + 1)

theorem PathLen.reach {N : NodeId → Option KNode} {t : Time} {r z : NodeId} {n : Nat}
    (h : PathLen N t r z n) : TReach N t r z := by
  induction h with
  | root => exact TReach.root
  | link _ hl ih => exact TReach.link ih hl

theorem TReach.pathLen {N : NodeId → Option KNode} {t : Time} {r z : NodeId}
    (h : TReach N t r z) : ∃ n, PathLen N t r z n := by
  induction h with
  | root => exact ⟨0, PathLen.root⟩
  | link _ hl ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, PathLen.link hn hl⟩

/-- In a tree all paths to a node have one length. -/
theorem PathLen.depth_unique {N : NodeId → Option KNode} {t : Time} {r : NodeId}
    (hT : TreeOK N t r) : ∀ n z m, PathLen N t r z n → PathLen N t r z m → n = m := by
  intro n
  induction n with
  | zero =>
    intro z m h1 h2
    cases h1 with
    | root =>
      cases h2 with
      | root => rfl
      | link hp hl => exact absurd hl (hT.rootFree _ _ hp.reach)
  | succ n ih =>
    intro z m h1 h2
    cases h1 with
    | link hp1 hl1 =>
      cases h2 with
      | root => exact absurd hl1 (hT.rootFree _ _ hp1.reach)
      | link hp2 hl2 =>
        obtain ⟨he, _⟩ := hT.oneLink _ _ _ _ _ hp1.reach hp2.reach hl1 hl2
        subst he
        rw [ih _ _ hp1 hp2]

/-- A path from a node x down to z of n links. -/
inductive PathFromLen (N : NodeId → Option KNode) (t : Time) : NodeId → NodeId → Nat → Prop
  | refl (x : NodeId) : PathFromLen N t x x 0
  | link {x y : NodeId} {c : Nat} {z : NodeId} {n : Nat} :
      PathFromLen N t x y n → TLink N t y c z → PathFromLen N t x z (n + 1)

theorem PathLen.append {N : NodeId → Option KNode} {t : Time} {r x : NodeId} {a : Nat}
    (h1 : PathLen N t r x a) : ∀ {z b}, PathFromLen N t x z b → PathLen N t r z (a + b) := by
  intro z b h2
  induction h2 with
  | refl => exact h1
  | link _ hl ih => exact PathLen.link ih hl

/-- In a tree, no reached node is reached again from a node below it. -/
theorem TreeOK.no_cycle {N : NodeId → Option KNode} {t : Time} {r : NodeId} (hT : TreeOK N t r)
    {x : NodeId} (hx : TReach N t r x) {k : Nat} (hk : 0 < k) (hc : PathFromLen N t x x k) : False := by
  obtain ⟨a, ha⟩ := hx.pathLen
  have h2 := ha.append hc
  have := PathLen.depth_unique hT a x (a + k) ha h2
  omega

/-- Nodes reached by paths no longer than n, in a lookup that agrees with N but
on x, are reached in it, if every path to x is longer. -/
theorem tReach_updN_of_short (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m : KNode) :
    ∀ n z, PathLen N t r z n → (∀ k, PathLen N t r x k → n < k) → TReach (updN N x m) t r z := by
  intro n z h
  induction h with
  | root => intro _; exact TReach.root
  | @link p c y n hp hl ih =>
    intro hx
    have hpx : p ≠ x := by
      intro he; subst he; have := hx n hp; omega
    have h1 := ih (fun k hk => by have := hx k hk; omega)
    obtain ⟨pn, hpn, hc⟩ := hl
    exact TReach.link h1 ⟨pn, by rw [updN_ne N x m p hpx]; exact hpn, hc⟩

/-- In a tree, what reaches a node q still reaches it when q's child x is
changed. -/
theorem tReach_updN_parent (N : NodeId → Option KNode) (t : Time) (r q x : NodeId) (k : Nat)
    (m : KNode) (hT : TreeOK N t r) (hq : TReach N t r q) (hl : TLink N t q k x) :
    TReach (updN N x m) t r q := by
  obtain ⟨a, ha⟩ := hq.pathLen
  apply tReach_updN_of_short N t r x m a q ha
  intro b hb
  have := PathLen.depth_unique hT (a + 1) x b (PathLen.link ha hl) hb
  omega

/-- A change of a node that is not reached keeps a tree, and what it reaches. -/
theorem treeOK_updN_unreach (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m : KNode)
    (hT : TreeOK N t r) (hx : ¬ TReach N t r x) : TreeOK (updN N x m) t r :=
  treeOK_of_agree N _ t r hT (fun z hz => updN_ne N x m z (fun he => hx (he ▸ hz)))

theorem tReach_updN_unreach (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m : KNode)
    (hx : ¬ TReach N t r x) : ∀ z, TReach (updN N x m) t r z → TReach N t r z :=
  tReach_of_agree N _ t r (fun z hz => updN_ne N x m z (fun he => hx (he ▸ hz)))

/-- What the lookup after a change reaches (`treeOK_transfer_gone`'s premises):
nodes reached before or new, none gone. -/
theorem tReach_transfer_gone (L L' : NodeId → Option KNode) (t : Time) (r r' : NodeId)
    (New Gone : NodeId → Prop) (tr : NodeId → Nat → NodeId × Nat)
    (hr' : (r' = r ∧ ¬ Gone r) ∨ (New r' ∧ ∀ y c, (TReach L t r y ∨ New y) → ¬ Gone y →
      ¬ TLink L' t y c r'))
    (hlinks : ∀ u c v, (TReach L t r u ∨ New u) → ¬ Gone u → TLink L' t u c v →
      New v ∨ (¬ Gone v ∧ ∃ y0 c0, TReach L t r y0 ∧ TLink L t y0 c0 v ∧ tr y0 c0 = (u, c)))
    (hNewGone : ∀ z, New z → ¬ Gone z) :
    ∀ y, TReach L' t r' y → (TReach L t r y ∨ New y) ∧ ¬ Gone y := by
  intro y hy
  induction hy with
  | root =>
    rcases hr' with ⟨h, hg⟩ | ⟨h, _⟩
    · rw [h]; exact ⟨Or.inl TReach.root, hg⟩
    · exact ⟨Or.inr h, hNewGone _ h⟩
  | @link u c v _ hl ih =>
    rcases hlinks u c v ih.1 ih.2 hl with h | ⟨hg, y0, c0, hy0, hl0, _⟩
    · exact ⟨Or.inr h, hNewGone v h⟩
    · exact ⟨Or.inl (TReach.link hy0 hl0), hg⟩

/-- The time split of x below q to a new node y with some of x's live klongs,
in general: q's new node has a klong k to y and else q's live klongs. The tree
is kept; it reaches the nodes reached before and y, not x. -/
theorem treeOK_timeSplit_gen (N N' : NodeId → Option KNode) (t : Time) (r q L y : NodeId)
    (qn n m qn' : KNode) (k1 : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t)
    (hLn : N L = some n)
    (hN'q : N' q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = k1 ∧ z = y) ∨ (c ≠ k1 ∧ (c, z) ∈ qn.liveAt t))
    (hN'y : N' y = some m)
    (hmsub : ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ y → N' z = N z)
    (hfy : N y = none) (hfresh : ∀ u c', TReach N t r u → ¬ TLink N t u c' y) :
    TreeOK N' t r ∧ ∀ z, TReach N' t r z → (TReach N t r z ∨ z = y) ∧ z ≠ L := by
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hLy : L ≠ y := fun h => by rw [h, hfy] at hLn; cases hLn
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hql : ∀ c' z, TLink N' t q c' z → (c' = k1 ∧ z = y) ∨ (c' ≠ k1 ∧ (c', z) ∈ qn.liveAt t) := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'q] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hq' c' z hc
  have hyl : ∀ c' z, TLink N' t y c' z → TLink N t L c' z := by
    intro c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hN'y] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact ⟨n, hLn, hmsub c' z hc⟩
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ y → ∀ c' z, TLink N' t u c' z → TLink N t u c' z := by
    intro u h1 h2 h3 c' z hl
    obtain ⟨mm, hm, hc⟩ := hl
    rw [hother u h1 h2 h3] at hm
    exact ⟨mm, hm, hc⟩
  have hnotR : ∀ z, z = y → ¬ TReach N t r z := by
    intro z hz; rw [hz]; exact not_reach_fresh N t r y hT hfy hfresh
  have hr' : (r = r ∧ ¬ (fun z => z = L) r) ∨ ((fun z => z = y) r ∧ ∀ y' c, (TReach N t r y' ∨
      (fun z => z = y) y') → ¬ (fun z => z = L) y' → ¬ TLink N' t y' c r) :=
    Or.inl ⟨rfl, fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)⟩
  have hlinks : ∀ u c' z, (TReach N t r u ∨ (fun z => z = y) u) → ¬ (fun z => z = L) u →
      TLink N' t u c' z → (fun z => z = y) z ∨ (¬ (fun z => z = L) z ∧ ∃ y0 c0, TReach N t r y0 ∧
        TLink N t y0 c0 z ∧ (fun u c' => if u = L then (y, c') else (u, c')) y0 c0 = (u, c')) := by
    intro u c' z hu hug hl
    have huL : u ≠ L := hug
    by_cases huy : u = y
    · rw [huy] at hl
      have hl0 := hyl c' z hl
      refine Or.inr ⟨fun hz => ?_, L, c', hL, hl0, by simp [huy]⟩
      have hz' : z = L := hz
      rw [hz'] at hl0
      exact hT.no_self_link L c' hL hl0
    · have huR : TReach N t r u := hu.elim id (fun h => absurd h huy)
      by_cases huq : u = q
      · rw [huq] at hl
        rcases hql c' z hl with ⟨_, h⟩ | ⟨hc, hm⟩
        · exact Or.inl h
        · have hl0 : TLink N t q c' z := ⟨qn, hqn, hm⟩
          refine Or.inr ⟨fun hz => ?_, q, c', hq, hl0, by simp [hqL, huq]⟩
          have hz' : z = L := hz
          rw [hz'] at hl0
          exact hc (hLpar q c' hq hl0).2
      · have hl0 := hOld u huL huq huy c' z hl
        refine Or.inr ⟨fun hz => ?_, u, c', huR, hl0, by simp [huL]⟩
        have hz' : z = L := hz
        rw [hz'] at hl0
        exact huq (hLpar u c' huR hl0).1
  have hNewGone : ∀ z, (fun z => z = y) z → ¬ (fun z => z = L) z := by
    intro z hz hzg
    have h1 : z = y := hz
    have h2 : z = L := hzg
    exact hLy (h2.symm.trans h1)
  refine ⟨?_, ?_⟩
  · apply treeOK_transfer_gone N N' t r r (fun z => z = y) (fun z => z = L)
      (fun u c' => if u = L then (y, c') else (u, c')) hT hnotR hr' hlinks
    · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
      have hz' : z = y := hz
      have hone : ∀ v d, (TReach N t r v ∨ v = y) → v ≠ L → TLink N' t v d z → v = q ∧ d = k1 := by
        intro v d hv hvg hl
        rw [hz'] at hl
        by_cases hvy : v = y
        · rw [hvy] at hl; exact absurd (hyl d y hl) (hfresh L d hL)
        · have hvR : TReach N t r v := hv.elim id (fun h => absurd h hvy)
          by_cases hvq : v = q
          · rw [hvq] at hl
            rcases hql d y hl with ⟨hd, _⟩ | ⟨_, hm⟩
            · exact ⟨hvq, hd⟩
            · exact absurd ⟨qn, hqn, hm⟩ (hfresh q d hq)
          · exact absurd (hOld v hvg hvq hvy d y hl) (hfresh v d hvR)
      obtain ⟨a1, b1⟩ := hone u c' hu hug hl1
      obtain ⟨a2, b2⟩ := hone u' c'' hu' hug' hl2
      exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact hNewGone
    · by_cases hrq : r = q
      · rw [hrq, hN'q]; exact ⟨_, rfl⟩
      · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
        obtain ⟨rm, hrm⟩ := hT.rootKey
        have hry : r ≠ y := fun h => by rw [h, hfy] at hrm; cases hrm
        rw [hother r hrL hrq hry]; exact ⟨rm, hrm⟩
  · intro z hz
    obtain ⟨h1, h2⟩ := tReach_transfer_gone N N' t r r (fun z => z = y) (fun z => z = L)
      (fun u c' => if u = L then (y, c') else (u, c')) hr' hlinks hNewGone z hz
    exact ⟨h1, h2⟩

end SIS.Tree
