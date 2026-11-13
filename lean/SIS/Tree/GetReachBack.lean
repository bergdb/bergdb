import SIS.Tree.GetNewRoot
import SIS.Tree.WriterTreeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The nodes a tree reaches are reached after a split (bergdb 024-12, TP10):
the cascade's virtual trees, level by level, keep every node but the ones they
replace (`tReach_transport`); with it, a node made below the cascade, a new
segment root, is reached in the writer's state after the cascade, so the fuel
premise of that state (`SegFits`) reaches it. -/

/-- Reach carried from V to V': the nodes V reaches from r but x are reached in
V' from r', when the links in V from the nodes it reaches but x are V''s (but
those to x), and x's children in V are reached in V'. -/
theorem tReach_transport (V V' : NodeId → Option KNode) (t : Time) (r r' x : NodeId) (xv : KNode)
    (hVx : V x = some xv)
    (hroot : r ≠ x → TReach V' t r' r)
    (hlink : ∀ u c z, TReach V t r u → u ≠ x → TReach V' t r' u → TLink V t u c z → z ≠ x →
      TLink V' t u c z)
    (hchild : ∀ c z, (c, z) ∈ xv.liveAt t → TReach V' t r' z) :
    ∀ z, TReach V t r z → z ≠ x → TReach V' t r' z := by
  intro z hz
  induction hz with
  | root => exact hroot
  | @link u c z hu hl ih =>
    intro hzx
    by_cases hux : u = x
    · subst hux
      obtain ⟨m, hm, hc⟩ := hl
      rw [hVx] at hm; cases hm
      exact hchild c z hc
    · exact TReach.link (ih hux) (hlink u c z hu hux (ih hux) hl hzx)

/-- A live klong of qn stays live when klongs of other compare values are put. -/
theorem addKeys_liveAt_keep (t : Time) (qn : KNode) (ins : List (Nat × NodeId))
    (hw : klongsWf qn.ks = true) (ht : ∀ s, Klong.time s ∈ qn.ks → s ≤ t) (c : Nat) (z : NodeId)
    (hc : (c, z) ∈ qn.liveAt t) (hne : ∀ q ∈ ins, q.1 ≠ c) :
    (c, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) qn).liveAt t := by
  apply KNode.addKeys_liveAt_of_fold t ins qn hw ht c z
  have h0 : qn.live.lookup c = some z := by
    rw [KNode.liveAt_of_times qn t ht] at hc
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup qn) c z hc
  rw [h0]
  clear h0
  induction ins with
  | nil => rfl
  | cons q rest ih =>
    simp only [List.foldl_cons]
    have hq : (q.1 == c) = false := by
      have := hne q (List.mem_cons_self ..)
      simpa using this
    simp only [pairLookupStep, hq, Bool.false_eq_true, ↓reduceIte]
    exact ih (fun q' hq' => hne q' (List.mem_cons_of_mem _ hq'))

/-- The search at a live compare value finds its klong. -/
theorem KNode.searchLte_of_live (n : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (c : Nat) (z : NodeId) (hc : (c, z) ∈ n.liveAt t) :
    (n.searchLte t c).map (·.y) = some z := by
  have hs := n.searchLte_spec t c
  cases hr : n.searchLte t c with
  | none =>
    rw [hr] at hs
    have := hs.2.mp rfl (c, z) hc
    simp at this
  | some f =>
    rw [hr] at hs
    obtain ⟨hmem, hle, hbest⟩ := hs.1 f rfl
    have h1 := hbest (c, z) hc (by simp)
    simp only [decide_eq_true_eq] at hle h1
    have hfc : f.c = c := by omega
    rw [KNode.liveAt_of_times n t ht] at hmem hc
    have a := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) _ _ hmem
    have b := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) _ _ hc
    rw [hfc, b] at a
    simp only [Option.map_some, Option.some.injEq] at a ⊢
    exact a.symm

/-- The klongs ins put into qn, the first of compare value K, the klong of x: a
live klong of qn to another node than x stays live. -/
theorem insOK_keep (t : Time) (qn : KNode) (ins : List (Nat × NodeId)) (hins : InsOK qn ins)
    (K : Nat) (hhead : ∀ a, ins.head? = some a → a.1 = K)
    (hw : klongsWf qn.ks = true) (ht : ∀ s, Klong.time s ∈ qn.ks → s ≤ t) (x : NodeId)
    (hKx : (K, x) ∈ qn.liveAt t) (c : Nat) (z : NodeId) (hc : (c, z) ∈ qn.liveAt t) (hz : z ≠ x) :
    (c, z) ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) qn).liveAt t := by
  have hL := KNode.liveAt_of_times qn t ht
  have hcK : c ≠ K := by
    intro he
    subst he
    rw [hL] at hKx hc
    have a := lookup_of_mem_nodup _ (KNode.live_keys_nodup qn) _ _ hKx
    have b := lookup_of_mem_nodup _ (KNode.live_keys_nodup qn) _ _ hc
    rw [a] at b
    simp only [Option.some.injEq] at b
    exact hz b.symm
  apply addKeys_liveAt_keep t qn ins hw ht c z hc
  rcases hins with ⟨k, y, rfl⟩ | ⟨k, F, sc, S, rfl, hks, hsc⟩
  · intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    have := hhead (k, y) rfl
    simp only at this ⊢
    omega
  · intro q hq
    have hk := hhead (k, F) rfl
    simp only at hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with hq | hq
    · subst hq; simp only; omega
    · subst hq
      simp only
      intro he
      subst he
      rw [hL] at hc
      have := hsc _ _ hc (by omega)
      omega

/-- A node with the live klongs of another, both by time t, has its live klongs
at t. -/
theorem liveAt_of_lookup_eq (n1 n2 : KNode) (t : Time) (h1 : ∀ s, Klong.time s ∈ n1.ks → s ≤ t)
    (h2 : ∀ s, Klong.time s ∈ n2.ks → s ≤ t) (hl : ∀ c, n1.live.lookup c = n2.live.lookup c)
    (c : Nat) (z : NodeId) (h : (c, z) ∈ n2.liveAt t) : (c, z) ∈ n1.liveAt t := by
  rw [KNode.liveAt_of_times _ t h2] at h
  rw [KNode.liveAt_of_times _ t h1, mem_iff_lookup _ (KNode.live_keys_nodup n1), hl]
  exact (mem_iff_lookup _ (KNode.live_keys_nodup n2) c z).mp h

/-- A new root's two klongs are live. -/
theorem rootPair_liveAt (t : Time) (F S : NodeId) (sc : Nat) (hsc : 0 < sc) :
    (0, F) ∈ (⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).liveAt t ∧
    (sc, S) ∈ (⟨false, newKlongs t [(0, F), (sc, S)]⟩ : KNode).liveAt t := by
  have hnd : ([(0, F), (sc, S)].map Prod.fst).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, List.nodup_nil, and_true, not_false_eq_true]
    omega
  exact ⟨(mrg_newKlongs_liveAt_iff false t _ hnd 0 F).mpr (by simp),
    (mrg_newKlongs_liveAt_iff false t _ hnd sc S).mpr (by simp)⟩

/-- What N reaches is reached after a change of a node N does not reach. -/
theorem tReach_updN_keep (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m : KNode)
    (hx : ¬ TReach N t r x) : ∀ z, TReach N t r z → TReach (updN N x m) t r z := by
  intro z hz
  induction hz with
  | root => exact TReach.root
  | @link u c z hu hl ih =>
    obtain ⟨mm, hm, hc⟩ := hl
    have hux : u ≠ x := fun he => hx (he ▸ hu)
    exact TReach.link ih ⟨mm, by rw [updN_ne _ _ _ _ hux]; exact hm, hc⟩

/-- A node a tree reaches is reached after a change of that node. -/
theorem tReach_updN_self (N : NodeId → Option KNode) (t : Time) (r x : NodeId) (m : KNode)
    (hT : TreeOK N t r) (hx : TReach N t r x) : TReach (updN N x m) t r x := by
  obtain ⟨a, ha⟩ := hx.pathLen
  cases ha with
  | root => exact TReach.root
  | @link p c _ k hp hl =>
    have hpx : p ≠ x := by
      intro he
      subst he
      have := PathLen.depth_unique hT _ _ _ hp (PathLen.link hp hl)
      omega
    have hrp : TReach (updN N x m) t r p := tReach_updN_of_short N t r x m k p hp
      (fun k' hk' => by have := PathLen.depth_unique hT _ _ _ hk' (PathLen.link hp hl); omega)
    obtain ⟨mm, hm, hc⟩ := hl
    exact TReach.link hrp ⟨mm, by rw [updN_ne _ _ _ _ hpx]; exact hm, hc⟩

/-- The order a chain node i that space splits below an inner parent needs for
the reach after the split: a leaf's compare values from the parent's klong K i
on, an inner node's but its first above it (the walk's ranges, `NodeRange`). -/
def ChainOrd (c : Ctx) (K : Nat → Nat) (Nn : Nat → KNode) (i : Nat) : Prop :=
  ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
    c.p.splitAbove < ((Nn i).lastVersion c.i).size →
    ∀ c' z, (c', z) ∈ (Nn i).live → if (Nn i).leaf = true then K i ≤ c' else (c' = 0 ∨ K i < c')

/-- A compare value names one node among the live klongs. -/
theorem liveAt_cv_unique (n : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (c : Nat) (z1 z2 : NodeId) (h1 : (c, z1) ∈ n.liveAt t) (h2 : (c, z2) ∈ n.liveAt t) : z1 = z2 := by
  rw [KNode.liveAt_of_times n t ht] at h1 h2
  have a := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) _ _ h1
  have b := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) _ _ h2
  rw [a] at b
  simpa using b

/-- A live klong below the divider (prover putinv's `live_below_divider`). -/
theorem live_below_divider' (n : KNode) (r : Nat × NodeId) (h2 : 2 ≤ n.live.length)
    (hr : (n.live.drop (n.live.length / 2)).head? = some r) : ∃ a ∈ n.live, a.1 < r.1 := by
  have hleft := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  obtain ⟨a, ha⟩ : ∃ a, a ∈ n.live.take (n.live.length / 2) := by
    cases h : n.live.take (n.live.length / 2) with
    | nil =>
      exfalso
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this
      omega
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  exact ⟨a, List.mem_of_mem_take ha, hleft a ha⟩

/-- With `ChainOrd`, the divider of a space split below an inner parent is above
the parent's klong to the node. -/
theorem chainOrd_div (c : Ctx) (K : Nat → Nat) (Nn : Nat → KNode) (i : Nat)
    (hord : ChainOrd c K Nn i) (hNR : ¬ ChainRoom c (Nn i)) (hql : (Nn (i - 1)).leaf = false)
    (hsp : c.p.splitAbove < ((Nn i).lastVersion c.i).size) (ins : List (Nat × NodeId))
    (hins : InsOK (Nn i) ins) (h2 : 2 ≤ (Nn i).live.length) :
    K i < (halves (Nn i).leaf c.i ((Nn i).lastVersion c.i) ins).2.2 := by
  obtain ⟨r, hr⟩ := divider_exists (Nn i) (by omega)
  have hrm := divider_mem_live _ r hr
  have hsc := divider_pos' _ r h2 hr
  obtain ⟨a, more, hins_eq, hside⟩ := hins.side r hrm
  obtain ⟨hdiv, _, _⟩ := halves_links (Nn i).leaf c.i (Nn i) rfl a more r hr hsc hside
  rw [← hins_eq] at hdiv
  rw [hdiv]
  obtain ⟨a0, ha0, ha0r⟩ := live_below_divider' (Nn i) r h2 hr
  have hr1 := hord hNR hql hsp r.1 r.2 hrm
  have ha1 := hord hNR hql hsp a0.1 a0.2 ha0
  cases hl : (Nn i).leaf with
  | true =>
    simp only [hl, ↓reduceIte] at ha1
    omega
  | false =>
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr1
    rcases hr1 with h | h
    · omega
    · exact h

end SIS.Tree
