/-
The writer's tree kept by its rules (bergdb 024-22, `OpTreeOK`). Here the first
rule: a put of a key of one segment into a segment leaf with room
(`writerWP_put_room_tree`), the case of `GetFrame.lean`'s `writerWP_put_room`:
the leaf's links are its long segments' klongs, and the put adds a short one.
-/
import SIS.Tree.WriterTree
import SIS.Tree.GetFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Lists and nodes -/

theorem mem_of_lookup_nodup {β : Type} (l : List (Nat × β)) (a : Nat) (b : β)
    (h : l.lookup a = some b) : (a, b) ∈ l := by
  obtain ⟨l1, l2, hl, _⟩ := List.lookup_eq_some_iff.mp h
  rw [hl]; simp

theorem lookup_of_mem_nodup {β : Type} (l : List (Nat × β)) (hn : (l.map Prod.fst).Nodup)
    (a : Nat) (b : β) (h : (a, b) ∈ l) : l.lookup a = some b := by
  induction l with
  | nil => cases h
  | cons q l ih =>
    rcases q with ⟨a', b'⟩
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.mp h with hm | hm
    · simp only [Prod.mk.injEq] at hm
      rcases hm with ⟨h1, h2⟩
      subst h1; subst h2
      simp
    · have hne : a ≠ a' := by
        intro he
        apply hn.1
        rw [← he]
        exact List.mem_map.mpr ⟨(a, b), hm, rfl⟩
      have hb : (a == a') = false := by simpa using hne
      simp only [List.lookup_cons, hb]
      exact ih hn.2 hm

/-- A key klong added at time t keeps every other live klong at t. -/
theorem KNode.add_key_liveAt_other (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (hc : c ≠ cv) (h : (c, y) ∈ (n.add t (.key cv v)).liveAt t) : (c, y) ∈ n.liveAt t := by
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  rw [KNode.liveAt_eq_live_prefix,
    prefixAt_of_times _ t (fun k hk s hs => by subst hs; exact ht' s hk)] at h
  rw [KNode.liveAt_eq_live_prefix, prefixAt_of_times n.ks t (fun k hk s hs => by subst hs; exact ht s hk)]
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c y h
  have hlk := KNode.add_key_live_lookup_of_wf n t cv c v hw
  have hb : (cv == c) = false := by simpa using (Ne.symm hc)
  simp only [hb, Bool.false_eq_true, ↓reduceIte] at hlk
  have hl' : (({ leaf := n.leaf, ks := n.ks } : KNode).live).lookup c = some y := by
    rw [← hlk]; exact hl
  exact mem_of_lookup_nodup _ c y hl'

/-! ## A change whose links are links of the tree -/

/-- A change whose links, from the nodes it reaches, are links of the tree
keeps the tree. -/
theorem treeOK_of_sublinks (L L' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (ht : TreeOK L t r) (hroot : ∃ n, L' r = some n)
    (hsub : ∀ x c y, TLink L' t x c y → TLink L t x c y) : TreeOK L' t r := by
  have hb : ∀ y, TReach L' t r y → TReach L t r y := by
    intro y hy
    induction hy with
    | root => exact TReach.root
    | link _ hl ih => exact TReach.link ih (hsub _ _ _ hl)
  refine ⟨hroot, ?_, ?_⟩
  · intro x c hx hl
    exact ht.rootFree x c (hb x hx) (hsub x c r hl)
  · intro x c x' c' y hx hx' hl hl'
    exact ht.oneLink x c x' c' y (hb x hx) (hb x' hx') (hsub x c y hl) (hsub x' c' y hl')

/-- The key of one segment: its compare value is no long segment's. -/
theorem keyWf_single_segLen (cv : Nat) (h : keyWf [cv] = true) : segLen cv ≠ 7 := by
  simp only [keyWf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-! ## A put into a segment leaf with room -/

/-- A put of a key of one segment into a segment leaf with room (no split, no
compaction) keeps the writer's tree: the leaf gets a short segment's klong,
which is no link. The premises are `writerWP_put_room`'s that the tree needs. -/
theorem writerWP_put_room_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (hkey : keyWf [cv] = true)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hr02.1, hr02.2.2.1]; exact ht
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel w.top.rootKey w2 ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr02.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  obtain ⟨hwf, htimes, hroom, hdead⟩ := hleaf L n hvisL hn hnl
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = true := by
    rw [hnext3, hdead]; simp [hroom]
  simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
  suffices hfin : ∀ w6 : W, w6.taken = w.taken → w6.top = w.top →
      (∀ x, w6.nodes.lookup x = if x = L then some (n.add c.i (.key cv w.next))
        else w3.nodes.lookup x) →
      TreeOK (wNode c.p base w6) c.i w6.top.rootKey by
    refine hfin _ hr03.2.2.1 hr03.2.1 ?_
    intro x; simp only; rw [lookup_upsert, hnext3]
  intro w6 h6taken h6top h6nodes
  have hLt : w.taken.contains L = false := ht (L, cv) hvisL
  have hN : ∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x := by
    intro x hx
    rw [← hr03.1]
    simp only [wNode, h6taken, h6nodes, hx, ↓reduceIte, hr03.2.2.1]
  have hNL : wNode c.p base w6 L = some (n.add c.i (.key cv w.next)) := by
    simp only [wNode, h6taken, hLt, Bool.false_eq_true, ↓reduceIte, h6nodes]
  have hleaf' : (n.add c.i (.key cv w.next)).leaf = true := by
    unfold KNode.add; split <;> (try split) <;> exact hnl
  have hseg := keyWf_single_segLen cv hkey
  rw [h6top]
  apply treeOK_of_sublinks (wNode c.p base w) (wNode c.p base w6) c.i w.top.rootKey hT
  · by_cases hr : w.top.rootKey = L
    · rw [hr, hNL]; exact ⟨_, rfl⟩
    · rw [← hN _ hr]; exact hT.rootKey
  · intro x c' y hl
    obtain ⟨m, hm, hc, hs⟩ := hl
    by_cases hx : x = L
    · subst hx
      rw [hNL] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      have h7 := hs hleaf'
      have hne : c' ≠ cv := fun he => hseg (he ▸ h7)
      exact ⟨n, hn, KNode.add_key_liveAt_other n c.i cv w.next hwf htimes c' y hne hc,
        fun _ => h7⟩
    · rw [← hN x hx] at hm
      exact ⟨m, hm, hc, hs⟩

end SIS.Tree
