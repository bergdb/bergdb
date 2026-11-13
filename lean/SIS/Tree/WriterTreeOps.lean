/-
The writer's tree kept by its rules (bergdb 024-22, `OpTreeOK`). Here the first
rule: a put of a key of one segment into a segment leaf with room
(`writerWP_put_room_tree`), the case of `GetFrame.lean`'s `writerWP_put_room`:
the leaf's klong of the key names the new value, which nothing named before.
-/
import SIS.Tree.WriterTreeVisits

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Lists and nodes -/

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

/-- A key klong added at time t: the live klongs at t are the new one and the
others of the node. -/
theorem KNode.add_key_liveAt_mem (n : KNode) (t : Time) (cv : Nat) (v : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) (y : NodeId)
    (h : (c, y) ∈ (n.add t (.key cv v)).liveAt t) :
    (c = cv ∧ y = v) ∨ (c ≠ cv ∧ (c, y) ∈ n.liveAt t) := by
  by_cases hc : c = cv
  · subst hc
    left
    refine ⟨rfl, ?_⟩
    have ht' := KNode.add_times n t (.key c v) (fun s h => by cases h) ht
    rw [KNode.liveAt_eq_live_prefix,
      prefixAt_of_times _ t (fun k hk s hs => by subst hs; exact ht' s hk)] at h
    have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c y h
    have hl2 : ({ leaf := (n.add t (.key c v)).leaf, ks := (n.add t (.key c v)).ks } : KNode).live.lookup c =
        (n.add t (.key c v)).live.lookup c := rfl
    rw [hl2, KNode.add_key_live_lookup_of_wf n t c c v hw] at hl
    simp at hl
    exact hl.symm
  · exact Or.inr ⟨hc, KNode.add_key_liveAt_other n t cv v hw ht c y hc h⟩

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


/-- A node that is no node of the lookup and that no link of the tree names is
not reached (a fresh id). -/
theorem not_reach_fresh (L : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (ht : TreeOK L t r) (hy : L y = none) (hf : ∀ u c, TReach L t r u → ¬ TLink L t u c y) :
    ¬ TReach L t r y := by
  intro h
  cases h with
  | root => obtain ⟨m, hm⟩ := ht.rootKey; rw [hm] at hy; cases hy
  | link hu hl => exact hf _ _ hu hl

/-! ## A put into a segment leaf with room -/

/-- A put of a key of one segment into a segment leaf with room (no split, no
compaction) keeps the writer's tree: the leaf's klong of the key names the new
value, the next id, which no link of the tree names and which is no node of the
writer's. The other premises are `writerWP_put_room`'s that the tree needs. -/
theorem writerWP_put_room_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hnext : wNode c.p base w w.next = none)
    (hfresh : ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' w.next) :
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
  have hLy : L ≠ w.next := fun he => by rw [he, hnext] at hn; cases hn
  have hyN : wNode c.p base w6 w.next = none := by rw [← hN _ (Ne.symm hLy)]; exact hnext
  have hyR : ¬ TReach (wNode c.p base w) c.i w.top.rootKey w.next :=
    not_reach_fresh _ _ _ _ hT hnext hfresh
  have hLR : TReach (wNode c.p base w) c.i w.top.rootKey L := by
    have := eqVisits_tPath (wNode c.p base w) c.i w.top.rootKey cv c.p.fuel w.top.rootKey 0
      TPath.root L cv hvisL
    exact tPath_reach _ _ _ _ _ this.1
  rw [h6top]
  apply treeOK_transfer_gone (wNode c.p base w) (wNode c.p base w6) c.i w.top.rootKey
    w.top.rootKey (fun z => z = w.next) (fun _ => False) (fun u c' => (u, c')) hT
  · intro z hz; rw [hz]; exact hyR
  · exact Or.inl ⟨rfl, id⟩
  · intro u c' v hu _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hx : u = L
    · subst hx
      rw [hNL] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      rcases KNode.add_key_liveAt_mem n c.i cv w.next hwf htimes c' v hc with ⟨_, hv⟩ | ⟨_, hmem⟩
      · exact Or.inl hv
      · exact Or.inr ⟨id, u, c', hLR, ⟨n, hn, hmem⟩, rfl⟩
    · by_cases huy : u = w.next
      · rw [huy, hyN] at hm; cases hm
      · rw [← hN u hx] at hm
        have huR : TReach (wNode c.p base w) c.i w.top.rootKey u := by
          rcases hu with h | h
          · exact h
          · exact absurd h huy
        exact Or.inr ⟨id, u, c', huR, ⟨m, hm, hc⟩, rfl⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl hl'
    rw [hz] at hl hl'
    have hone : ∀ x d, (TReach (wNode c.p base w) c.i w.top.rootKey x ∨ x = w.next) →
        TLink (wNode c.p base w6) c.i x d w.next → x = L ∧ d = cv := by
      intro x d hx hl0
      obtain ⟨m, hm, hc⟩ := hl0
      by_cases hxL : x = L
      · subst hxL
        rw [hNL] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        rcases KNode.add_key_liveAt_mem n c.i cv w.next hwf htimes d w.next hc with
          ⟨hd, _⟩ | ⟨_, hmem⟩
        · exact ⟨rfl, hd⟩
        · exact absurd ⟨n, hn, hmem⟩ (hfresh x d hLR)
      · by_cases hxy : x = w.next
        · rw [hxy, hyN] at hm; cases hm
        · rw [← hN x hxL] at hm
          have hxR : TReach (wNode c.p base w) c.i w.top.rootKey x := by
            rcases hx with h | h
            · exact h
            · exact absurd h hxy
          exact absurd ⟨m, hm, hc⟩ (hfresh x d hxR)
    obtain ⟨h1, h2⟩ := hone u c' hu hl
    obtain ⟨h3, h4⟩ := hone u' c'' hu' hl'
    exact ⟨h1.trans h3.symm, h2.trans h4.symm⟩
  · intro _ _ h; exact h
  · by_cases hr : w.top.rootKey = L
    · rw [hr, hNL]; exact ⟨_, rfl⟩
    · rw [← hN _ hr]; exact hT.rootKey

end SIS.Tree
