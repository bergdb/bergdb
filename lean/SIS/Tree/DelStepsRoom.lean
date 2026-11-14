/-
Case (4)'s delete steps, a leaf that keeps a live klong and has room for the
bitmap, the merges on (bergdb 024-12, TP7 and TP10): `DelInvF` at
`afterDelete`'s start (`delInvF_after_bitmap`) from the state between
operations; the take-back's facts after the bitmap (`takeJ2_after_bitmap`).
-/
import SIS.Tree.DelStepsWalk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `SegFits` holds for a larger depth. -/
theorem segFits_mono (N : NodeId → Option KNode) (t : Time) (d d' : Nat) (r : NodeId)
    (h : SegFits N t d r) (hd : d ≤ d') : SegFits N t d' r :=
  fun x hx => SegDepthLe.mono N t d x (h x hx) d' hd

/-- `DelInvF` at the state v after a delete's bitmap in the key's leaf L with
room, from the state w between operations (PutInv, the walk's ranges, inner
children, the fuel premise) and the books at v. -/
theorem delInvF_after_bitmap (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w w3 v : W) (pre : List Nat) (cv : Nat) (rk L : NodeId) (n : KNode)
    (hI : PutInv c base w) (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hr03 : ReadsAs c.p base w w3) (hLt : w.taken.contains L = false)
    (h1 : v.taken = w3.taken) (h2 : v.top = w3.top) (h3 : v.vals = w3.vals)
    (h7 : ∃ n', v.nodes = upsert w3.nodes L n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
        (∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') ∧
        BitmapOf n n' c.i cv)
    (hbv : PutBook c B top0 v) :
    DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) v := by
  obtain ⟨n', hnodes, hl', hwf', ht', hlk', _⟩ := h7
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hnt := hI.times L n hn
  have hnwf := hI.wf L n hn
  have hLt3 : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
  have hN : ∀ y, wNode c.p base v y = if y = L then some n' else wNode c.p base w y := by
    intro y
    rw [← hr03.1]
    by_cases hy : y = L
    · subst hy
      simp only [wNode, h1, hLt3, Bool.false_eq_true, ↓reduceIte, hnodes, lookup_upsert]
    · simp only [wNode, h1, hnodes, lookup_upsert, hy, ↓reduceIte]
  have hvL : wNode c.p base v L = some n' := by rw [hN L]; simp
  have hvo : ∀ y, y ≠ L → wNode c.p base v y = wNode c.p base w y := by
    intro y hy; rw [hN y]; simp [hy]
  have htop : v.top = w.top := by rw [h2, hr03.2.1]
  have htk : v.taken = w.taken := by rw [h1, hr03.2.2.1]
  have hvals : v.vals = w.vals := by rw [h3, hr03.2.2.2.1]
  have hlive := liveAt_iff_of_delete_lookup n n' c.i cv hnt ht' hlk'
  have hsub : ∀ c' z, (c', z) ∈ n'.liveAt c.i → (c', z) ∈ n.liveAt c.i :=
    fun c' z h => ((hlive c' z).mp h).1
  -- the tree
  have hT : TreeOK (wNode c.p base v) c.i v.top.rootKey := by
    rw [htop]
    exact treeOK_of_node_shrink _ _ c.i _ L n n' hI.tree hn hvL hvo hsub
  have hTT : PutInvT c base v := by
    have hI3 := putInv_of_readsAs c base w w3 hI hr03
    have hn3 : wNode c.p base w3 L = some n := by rw [hr03.1]; exact hn
    exact putInvT_shrink c base w3 v hI3 L n n' hn3 hl' ht'
      (fun c' z h => by
        rw [← KNode.liveAt_of_times _ c.i ht'] at h
        rw [← KNode.liveAt_of_times _ c.i hnt]
        exact hsub c' z h) h1 h2 hvL
      (fun y hy => by rw [hvo y hy, hr03.1])
  have hG := putInvG_of_book c base B top0 v hB hbv
  have hPI : PutInv c base v := putInv_of_parts c base v hG hT hTT.1 hTT.2
  -- reach only shrinks
  have hRS : ∀ u, ReachS (wNode c.p base v) c.i v.top.rootKey u →
      ReachS (wNode c.p base w) c.i w.top.rootKey u := by
    rw [htop]
    apply reachS_closed _ _ _ (fun y => ReachS (wNode c.p base w) c.i w.top.rootKey y) ReachS.root
    intro y yn cc z hy hyn hz
    by_cases hyx : y = L
    · subst hyx
      rw [hvL] at hyn; cases hyn
      exact ReachS.step y n cc z hy hn (hsub cc z hz)
    · rw [hvo y hyx] at hyn
      exact ReachS.step y yn cc z hy hyn hz
  -- the fuel premise
  have hF1 : SegFits (wNode c.p base v) c.i (c.p.fuel - 1) v.top.rootKey :=
    segFits_transfer _ _ c.i _ _ _ hF hRS (fun u un' _ hun' hl => by
      by_cases hu : u = L
      · subst hu; rw [hvL] at hun'; cases hun'; rw [hl', hnl] at hl; cases hl
      · rw [hvo u hu] at hun'
        exact ⟨un', hun', hl, fun c' y hy => ⟨c', hy⟩⟩)
  refine ⟨hPI, hG, ?_, ?_, ?_, ?_, B, top0, hB, hbv⟩
  · rw [htop]
    exact rangeOrder_shrink _ _ c.i _ L n n' hR hn hN hl' hsub
  · intro y yn cc z hy hyn hyl hz
    have hyw := tReach_reachS _ _ _ _ hy
    have hyR : TReach (wNode c.p base w) c.i w.top.rootKey y := reachS_tReach _ _ _ _ (hRS y hyw)
    by_cases hyx : y = L
    · subst hyx; rw [hvL] at hyn; cases hyn; rw [hl', hnl] at hyl; cases hyl
    · rw [hvo y hyx] at hyn
      obtain ⟨m, hm⟩ := hICE y yn cc z hyR hyn hyl hz
      by_cases hzx : z = L
      · exact ⟨n', by rw [hzx]; exact hvL⟩
      · exact ⟨m, by rw [hvo z hzx]; exact hm⟩
  · simp only [Nat.add_sub_cancel]
    exact segFits_mono _ _ _ _ _ hF1 (by omega)
  · intro key' hk'
    have hwfv : ∀ x xn, ReachS (wNode c.p base v) c.i v.top.rootKey x → wNode c.p base v x = some xn →
        klongsWf xn.ks = true := fun x xn _ h => hPI.wf x xn h
    have hwfw : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
        klongsWf xn.ks = true := fun x xn _ h => hI.wf x xn h
    rw [wGetAt_eq_wGet c base v _ (by omega) hwfv hF1, wGetAt_eq_wGet c base w _ (by omega) hwfw hF]
    have hV : ∀ y, wValue base w y = wValue base v y := by
      intro y; simp only [wValue, htk, hvals]
    obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w v L pre cv rk n n' hfuel htop
      (fun x hx => (hvo x hx).symm) hn hvL hnl (by rw [hl']; exact hnl)
      (fun c' hc' => by
        rw [KNode.searchEq_live n c.i hnwf hnt, KNode.searchEq_live n' c.i hwf' ht', hlk' c']
        have hb : (c' == cv) = false := by simpa using hc'
        rw [hb]; rfl)
      hrk (keyWf_last_notin pre cv hkey) hvisL (hI.keyUniq pre cv rk hkey hrk)
      (fun _ _ _ _ y _ _ _ _ _ => hV y)
    by_cases hk : pre ++ [cv] = key'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hown, KNode.searchEq_live n' c.i hwf' ht', hlk' cv]
      simp
    · have hk2 : (pre ++ [cv] == key') = false := by simpa using hk
      simp only [hk2, Bool.false_eq_true, ↓reduceIte]
      exact hother key' hk' (fun h => hk h.symm)

/-- `TakeJ2` at the state v after a delete's bitmap in the reached leaf L with
room, its klong of cv naming no node, below B or a value (state-level
`writerWP_appendDeleteKlong_j2D`). -/
theorem takeJ2_after_bitmap (c : Ctx) (base : View BVal) (B : NodeId) (w3 v : W) (cv : Nat)
    (L : NodeId) (n : KNode) (hpos : 0 < c.i) (hJ : TakeJ2 c base B w3)
    (hlk : w3.nodes.lookup L = some n) (htk : w3.taken.contains L = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hxR : TReach (wNode c.p base w3) c.i w3.top.rootKey L)
    (hcvN : ∀ y, (cv, y) ∈ n.liveAt c.i → wNode c.p base w3 y = none)
    (hcvv : ∀ y, (cv, y) ∈ n.liveAt c.i → y < B ∨ y ∈ w3.vals.map (·.1))
    (ht : v.taken = w3.taken) (htop : v.top = w3.top) (hv : v.vals = w3.vals)
    (h7 : ∃ n', v.nodes = upsert w3.nodes L n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
        (∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') ∧
        BitmapOf n n' c.i cv) :
    TakeJ2 c base B v := by
  obtain ⟨n', hnodes, _, _, ht', hlk', hbm⟩ := h7
  have hx : wNode c.p base w3 L = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hN' : wNode c.p base v = updN (wNode c.p base w3) L n' := by
    funext z
    by_cases hz : z = L
    · rw [hz, updN_self]
      simp only [wNode, ht, htk, Bool.false_eq_true, ↓reduceIte, hnodes, lookup_upsert]
    · simp only [updN, hz, ↓reduceIte, wNode, ht, hnodes, lookup_upsert]
  have hlive := liveAt_iff_of_delete_lookup n n' c.i cv hnt ht' hlk'
  have hreach := reach_updN_keep (wNode c.p base w3) c.i w3.top.rootKey L n n' hx (by
    intro cc u hm
    by_cases hc : cc = cv
    · rw [hc] at hm; exact Or.inr (hcvN u hm)
    · exact Or.inl ⟨cc, (hlive cc u).mpr ⟨hm, hc⟩⟩)
  unfold TakeJ2
  rw [htop, hv, hN']
  refine j2_change_one (wNode c.p base w3) _ c.i w3.top.rootKey w3.top.rootKey B _ L n n' hJ hx
    (updN_self _ _ _) (fun z hz => by simp [updN, hz]) (bitmapOf_prefix n n' c.i cv hbm hpos)
    (bitmapOf_firstTime n n' c.i cv hbm)
    (deadLiveK_bitmap n n' c.i cv B _ hbm hnt (deadLiveK_of_N _ _ _ _ hJ.2.1 L n hx) hcvv hlive)
    hreach (fun _ => ?_)
  rcases hreach L hxR with h | h
  · exact h
  · rw [h] at hx; cases hx

end SIS.Tree
