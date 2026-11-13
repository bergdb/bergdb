/-
The writer's merge keeps every reading (bergdb 024-12, TP10's `OpGetOK`;
024-22): the merge's last part, `mergeTail`, from the siblings to the parent
with room, keeps `wGet` of every key (`writerWP_mergeTail_get`), the
siblings' compare values in their ranges; the whole merge of two nodes the
transaction did not make, the ranges from putinv's `RangeOrder`
(`writerWP_merge_get`).
-/
import SIS.Tree.WriterGetMergeOp
import SIS.Tree.WriterGetMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The parent after a merge: its live klongs as the merge leaves them. -/
theorem mrg_parent_liveAt (pn : KNode) (t : Time) (il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (l r : NodeId) (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ t)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) :
    (∀ cc z, (cc, z) ∈ (mergeParentNode pn t il cL m1 ir cR none).liveAt t ↔
      (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt t ∧ cc ≠ cL ∧ cc ≠ cR)) ∧
    (∀ (m2 : NodeId) (g : Nat) cc z,
      (cc, z) ∈ (mergeParentNode pn t il cL m1 ir cR (some (m2, g))).liveAt t ↔
      (cc = g ∧ z = m2) ∨ (cc ≠ g ∧ cc = cL ∧ z = m1) ∨
        (cc ≠ g ∧ cc ≠ cL ∧ cc ≠ cR ∧ (cc, z) ∈ pn.liveAt t)) := by
  have hhtd := htd_last pn
  have hpn : ∀ cc z, (cc, z) ∈ pn.liveAt t ↔ pn.live.lookup cc = some z := by
    intro cc z
    rw [KNode.liveAt_of_times pn t hpt, mem_iff_lookup _ (KNode.live_keys_nodup pn)]
  refine ⟨?_, ?_⟩
  · intro cc z
    have hmt : ∀ s, Klong.time s ∈ (mergeParentNode pn t il cL m1 ir cR none).ks → s ≤ t := by
      rw [mergeParentNode_eq]
      exact mpNode_times pn t il cL m1 ir cR none _ _ _ (hhtd _) hpt
    rw [KNode.liveAt_of_times _ t hmt, mem_iff_lookup _ (KNode.live_keys_nodup _),
      mergeParentNode_eq, mpNode_live_lookup pn t il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc, hpn]
    case htd =>
      intro h
      cases hg : pn.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
    by_cases h1 : cc = cL
    · subst h1
      simp only [↓reduceIte, Option.some.injEq]
      constructor
      · intro h; exact Or.inl ⟨trivial, h.symm⟩
      · rintro (⟨_, h⟩ | ⟨_, h, _⟩)
        · exact h.symm
        · exact absurd rfl h
    · by_cases h2 : cc = cR
      · subst h2
        simp [h1]
      · simp only [h1, h2, ↓reduceIte, false_and, false_or, ne_eq, not_false_eq_true, and_true,
          and_self]
  · intro m2 g cc z
    have hmt : ∀ s, Klong.time s ∈ (mergeParentNode pn t il cL m1 ir cR (some (m2, g))).ks →
        s ≤ t := by
      rw [mergeParentNode_eq]
      exact mpNode_times pn t il cL m1 ir cR (some (m2, g)) _ _ _ (hhtd _) hpt
    rw [KNode.liveAt_of_times _ t hmt, mem_iff_lookup _ (KNode.live_keys_nodup _),
      mergeParentNode_eq, mpNode_live_lookup pn t il cL m1 ir cR (some (m2, g)) _ _ _ l r hpwf hL
        hLL hR hRL hc ?htd ?hrip cc, hpn]
    case htd =>
      intro h
      cases hg : pn.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
    case hrip =>
      intro h y g' heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨_, rfl⟩ := heq
      simp at h
      exact h.1.1
    simp only
    by_cases h0 : cc = g
    · subst h0
      simp only [↓reduceIte, Option.some.injEq]
      constructor
      · intro h; exact Or.inl ⟨trivial, h.symm⟩
      · rintro (⟨_, h⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · exact h.symm
        · exact absurd rfl h
        · exact absurd rfl h
    · by_cases h1 : cc = cL
      · subst h1
        simp only [h0, ↓reduceIte, Option.some.injEq, false_and, ne_eq, not_false_eq_true,
          true_and, false_or, not_true_eq_false, and_false, or_false]
        exact ⟨fun h => h.symm, fun h => h.symm⟩
      · by_cases h2 : cc = cR
        · subst h2
          simp [h0, h1]
        · simp only [h0, h1, h2, ↓reduceIte, false_and, ne_eq, not_false_eq_true, true_and,
            false_or]

/-- The second node's first compare value g of a merge into two: above cL and
0, and below every compare value of the parent above cR that is above the right
node's. -/
theorem mrg_two_g (inner : Bool) (cL cR : Nat) (lvL lvR : List (Nat × NodeId)) (h g : Nat)
    (yg : NodeId) (hs : CvSorted (mergeList inner cR lvL lvR)) (hh : 1 ≤ h)
    (hg : ((mergeList inner cR lvL lvR).drop h).head? = some (g, yg)) (hlr : cL < cR)
    (hL : ∀ q ∈ lvL, q.1 < cR ∧ (inner = true → q.1 = 0 ∨ cL < q.1) ∧ (inner = false → cL ≤ q.1))
    (hR : ∀ q ∈ lvR, (inner = true → q.1 = 0 ∨ cR < q.1) ∧ (inner = false → cR ≤ q.1)) :
    cL < g ∧ 0 < g ∧ (∀ k, cR < k → (∀ q ∈ lvR, q.1 < k) → g < k) := by
  have hmemg : (g, yg) ∈ (mergeList inner cR lvL lvR).drop h := List.mem_of_head? hg
  -- the right part's keys
  have hRs : CvSorted (if inner then renameHead cR lvR else lvR) := by
    unfold mergeList at hs
    exact List.Pairwise.sublist (List.sublist_append_right _ _) hs
  have hRge : ∀ q ∈ (if inner then renameHead cR lvR else lvR), cR ≤ q.1 := by
    intro q hq
    cases inner with
    | true =>
      simp only [↓reduceIte] at hq hRs
      cases hl : lvR with
      | nil => rw [hl] at hq; simp [renameHead] at hq
      | cons a rest =>
        rw [hl] at hq hRs
        simp only [renameHead, List.mem_cons] at hq hRs
        rcases hq with rfl | hq
        · exact Nat.le_refl _
        · have := (List.pairwise_cons.mp hRs).1 q hq
          simp at this; omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      exact (hR q hq).2 rfl
  have hRlt : ∀ k, cR < k → (∀ q ∈ lvR, q.1 < k) →
      ∀ q ∈ (if inner then renameHead cR lvR else lvR), q.1 < k := by
    intro k hk hlk q hq
    cases inner with
    | true =>
      simp only [↓reduceIte] at hq
      rcases mem_renameHead cR lvR q hq with h1 | h1
      · omega
      · exact hlk q (List.mem_of_mem_tail h1)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      exact hlk q hq
  have hcls : ∀ q ∈ mergeList inner cR lvL lvR, q ∈ lvL ∨ q ∈ (if inner then renameHead cR lvR else lvR) := by
    intro q hq
    unfold mergeList at hq
    exact List.mem_append.mp hq
  -- a klong before g
  obtain ⟨a, ha, hag⟩ : ∃ a ∈ mergeList inner cR lvL lvR, a.1 < g := by
    have hsplit := List.take_append_drop h (mergeList inner cR lvL lvR)
    have hs' := hs
    rw [← hsplit] at hs'
    have hpa := (List.pairwise_append.mp hs').2.2
    obtain ⟨y, hy⟩ : ∃ y, y ∈ (mergeList inner cR lvL lvR).take h := by
      cases ht : (mergeList inner cR lvL lvR).take h with
      | nil =>
        have hlen := congrArg List.length ht
        simp only [List.length_take, List.length_nil] at hlen
        have hd : (mergeList inner cR lvL lvR).drop h ≠ [] := by
          intro he; rw [he] at hg; simp at hg
        have : h < (mergeList inner cR lvL lvR).length := by
          by_cases hc : h < (mergeList inner cR lvL lvR).length
          · exact hc
          · exact absurd (List.drop_eq_nil_of_le (by omega)) hd
        omega
      | cons y _ => exact ⟨y, by simp⟩
    exact ⟨y, List.mem_of_mem_take hy, hpa y hy (g, yg) hmemg⟩
  have hgE : (g, yg) ∈ mergeList inner cR lvL lvR := List.mem_of_mem_drop hmemg
  refine ⟨?_, by omega, ?_⟩
  · rcases hcls _ hgE with hgl | hgr
    · obtain ⟨hgc, hgi, hgo⟩ := hL _ hgl
      cases inner with
      | true =>
        rcases hgi rfl with h0 | h0
        · simp at h0; omega
        · exact h0
      | false =>
        have hcg : cL ≤ g := hgo rfl
        rcases hcls a ha with hal | har
        · have := (hL a hal).2.2 rfl; omega
        · have := hRge a har; simp at hgc; omega
    · have := hRge _ hgr; omega
  · intro k hk hlk
    rcases hcls _ hgE with hgl | hgr
    · have := (hL _ hgl).1; simp at this; omega
    · exact hRlt k hk hlk _ hgr

/-- The merge's tail keeps the reading of every key: two siblings l and r under a
reached inner parent p with room, which the transaction did not make, merged into
one node or two; the siblings' compare values in their ranges. -/
theorem writerWP_mergeTail_get (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hclt : cL < cR) (hcap : 1 ≤ c.p.mergeMax)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (htimesN : ∀ y yn, N y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, N y = some yn → klongsWf yn.ks = true) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w3 key) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hlR : TReach N c.i root l := TReach.link hp hlink_l
  have hrR : TReach N c.i root r := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  obtain ⟨hlm, hlt⟩ := hch cL l ln hpL hln
  obtain ⟨hrm, hrt⟩ := hch cR r rn hpR hrn
  have hlm' : (ln.firstTime == some c.i) = false := by simpa using hlm
  have hrm' : (rn.firstTime == some c.i) = false := by simpa using hrm
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  unfold mergeTail
  simp only [hlm', hrm', hcvL, hcvR, Bool.false_eq_true, ↓reduceIte]
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hsortE := mrg_mergeList_sorted ln rn c.i (!xn.leaf) cR hlt hrt hlrange hrrange hrhead
  have hndE : ((mergeList (!xn.leaf) cR ln.live rn.live).map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hsortE.imp (by intro a b hab; omega))
  have hll' : ln.leaf = !(!xn.leaf) := by rw [hll]; simp
  have hrl' : rn.leaf = !(!xn.leaf) := by rw [hrl]; simp
  have hm1notR : ¬ TReach N c.i root nx := not_reach_fresh N c.i root nx hT (hfree nx (Nat.le_refl _)).1
    (hfreshT nx (Nat.le_refl _))
  obtain ⟨hparOne, hparTwo⟩ := mrg_parent_liveAt pn c.i il cL nx ir cR l r hpwf hpt hL hLL hR hRL hc
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_ghOf_frame x c _) ?_
  intro gh w4 ⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩
  simp only [writerWP_pure]
  refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
  intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
  refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
  intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
  -- the ids
  have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
  subst hm1
  have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hw6p : w6.nodes.lookup p = some pn := by
    rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
  have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
    rw [h6n, h5n, lookup_append_single_self]
    rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
    exact hnone3 m1 (Nat.le_refl _)
  have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
  have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
    intro y hyx hym
    rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; exact hym), hlk4 y hyx]
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
  have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hhtd := htd_last pn
  -- the parent after
  have hpliveAt : ∀ (m2 : Option (NodeId × Nat)),
      ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR m2).liveAt c.i →
      (mergeParentNode pn c.i il cL m1 ir cR m2).live.lookup cc = some z := by
    intro m2 cc z hm
    rw [KNode.liveAt_of_times _ c.i (by
      rw [mergeParentNode_eq]
      exact mpNode_times pn c.i il cL m1 ir cR m2 _ _ _ (hhtd _) hpt)] at hm
    exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hm
  have hlm1 : l ≠ m1 := by omega
  have hrm1 : r ≠ m1 := by omega
  have hpm1 : p ≠ m1 := by omega
  have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
  rw [hw4m1] at hw6m1
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
  have hcl : ∀ y, (∀ q ∈ [(l, false), (r, false)], y ≠ (q : NodeId × Bool).1) ↔ (y ≠ l ∧ y ≠ r) := by
    intro y; simp
  have hoBool : ∀ q ∈ [(l, false), (r, false)], (q : NodeId × Bool).2 = false := by simp
  have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
    intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpL' : (cL, l) ∈ pn.liveAt c.i := hpL
  cases hsec : second with
  | none =>
    rw [hsec] at hmkd
    have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR none c w6 hw6p hroom
      (hdead _ _ _ _ _ _)) ?_
    intro _ w7 ⟨h7n, h7t, h7top, _, h7v, _, _, _⟩
    refine writerWP_mono (writerWP_mergeCleanup_unmadeV _ c [(l, false), (r, false)] w7 hoBool) ?_
    intro _ w8 ⟨h8t, h8top, _, h8v, h8l⟩
    try simp only [writerWP_pure]
    have h8t' : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
    have h8l' : ∀ y, y ≠ l → y ≠ r → w8.nodes.lookup y =
        (upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none)).lookup y := by
      intro y hyl hyr; rw [h8l y ((hcl y).mpr ⟨hyl, hyr⟩), h7n]
    have h8v' : w8.vals = w3.vals := by rw [h8v, h7v, h6v, h5v, h4v]
    have hV8 : wValue base w8 = wValue base w3 := wValue_congr' base w8 w3 h8t' h8v'
    intro key
    unfold wGet
    rw [hV8, h8top, h7top, h6top', hN3, h3top]
    refine getFromR_mergeOne N (wNode c.p base w8) (wValue base w3) c.i c.p.fuel root p l r m1 pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR none) ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
      hT hp hpn hpleaf hpL hpR hclt hadj hln hrn hll' hrl' hlrange hrrange hrhead ?_ rfl ?_ ?_
      (by rw [mrg_mergeParentNode_leaf]; exact hpleaf) (hparOne) ?_ hm1notR htimesN
      (newKlongs_times c.i first) ?_ hwfN (klongsWf_newKlongs c.i first) key
    · simp only [wNode, h8t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte, hw6m1]
    · intro cc z
      rw [mrg_newKlongs_liveAt_iff _ c.i first (by rw [hfirst]; exact hndE) cc z, hfirst]
    · simp only [wNode, h8t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' p hpl hpr, lookup_upsert]
      simp
    · intro y hyp hyl hyr hym
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h8t'
      rw [h8l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      exact h6old y (hyx y hyl hyr) hym
    · rw [mergeParentNode_eq]
      exact mpNode_times pn c.i il cL m1 ir cR none _ _ _ (hhtd _) hpt
  | some ksg =>
    obtain ⟨ks2, g2⟩ := ksg
    rw [hsec] at hmkd
    have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
      rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
    intro m2 w7 ⟨hm2, h7n, h7t, h7top, _, h7v, _, _⟩
    have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
    subst hm2'
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c w7) ?_
    intro _ w8 ⟨h8n, h8t, h8top, _, h8v, _⟩
    try simp only [writerWP_pure]
    have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
        hlk4 _ (by omega)]
      exact hnone3 _ (by omega)
    have hw8p : w8.nodes.lookup p = some pn := by
      rw [h8n, h7n, h6next, h5next, hw4m1, lookup_append_single_ne _ _ _ _ (by omega)]
      exact hw6p
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c
      w8 hw8p hroom (hdead _ _ _ _ _ _)) ?_
    intro _ w9 ⟨h9n, h9t, h9top, _, h9v, _, _, _⟩
    refine writerWP_mono (writerWP_mergeCleanup_unmadeV _ c [(l, false), (r, false)] w9 hoBool) ?_
    intro _ w10 ⟨h10t, h10top, _, h10v, h10l⟩
    try simp only [writerWP_pure]
    have h10t' : w10.taken = w3.taken := by rw [h10t, h9t, h8t, h7t, h6taken]
    have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
        ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
      intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
    have h10l' : ∀ y, y ≠ l → y ≠ r → w10.nodes.lookup y =
        (upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)))).lookup y := by
      intro y hyl hyr; rw [h10l y ((hcl y).mpr ⟨hyl, hyr⟩), h9n]
    have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
    have h10v' : w10.vals = w3.vals := by rw [h10v, h9v, h8v, h7v, h6v, h5v, h4v]
    have hV10 : wValue base w10 = wValue base w3 := wValue_congr' base w10 w3 h10t' h10v'
    -- the halves of the merged klongs
    obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
    have hElen : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
      rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
      · exact h
      · exfalso
        unfold splitMerged at hmkd
        simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
          ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
    have hlnL : ∀ q ∈ ln.live, q.1 < cR ∧ ((!xn.leaf) = true → q.1 = 0 ∨ cL < q.1) ∧
        ((!xn.leaf) = false → cL ≤ q.1) := by
      intro q hq
      have hq' : (q.1, q.2) ∈ ln.liveAt c.i := by rw [KNode.liveAt_of_times ln c.i hlt]; exact hq
      exact ⟨hlrange _ _ hq', hllow _ _ hq'⟩
    have hrnR : ∀ q ∈ rn.live, ((!xn.leaf) = true → q.1 = 0 ∨ cR < q.1) ∧
        ((!xn.leaf) = false → cR ≤ q.1) := by
      intro q hq
      have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
      exact hrrange _ _ hq'
    obtain ⟨hgL, hg0, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
      (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
      hclt hlnL hrnR
    have hgU : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → g2 < k := by
      intro k z hk hkc
      apply hgU0 k hkc
      intro q hq
      have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
      exact hrup k z hk hkc _ _ hq'
    have hnd1 : (first.map Prod.fst).Nodup := by
      rw [hE1]
      exact List.pairwise_map.mpr ((hsortE.sublist (List.take_sublist _ _)).imp
        (by intro a b hab; omega))
    have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
      hsortE.sublist (List.drop_sublist _ _)
    have hnd2 : (ks2.map Prod.fst).Nodup := by
      rw [hE2]
      apply List.pairwise_map.mpr
      apply List.Pairwise.imp (R := fun a b : Nat × NodeId => a.1 < b.1)
        (by intro a b hab; omega)
      generalize hb : (!xn.leaf) = b at hsortD hgs ⊢
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact hsortD
      | true =>
        simp only [↓reduceIte]
        apply renameHead_sorted 0 _ hsortD
        intro q hq
        cases hd : (mergeList true cR ln.live rn.live).drop
            (((mergeList true cR ln.live rn.live).length + 1) / 2) with
        | nil => rw [hd] at hq; simp at hq
        | cons a tl =>
          rw [hd] at hq hgs hsortD
          simp only [List.head?_cons, Option.some.injEq] at hgs
          subst hgs
          simp only [List.tail_cons] at hq
          have := (List.pairwise_cons.mp hsortD).1 q hq
          simp at this; omega
    intro key
    unfold wGet
    rw [hV10, h10top, h9top, h8top, h7top, h6top', hN3, h3top]
    refine getFromR_mergeTwo N (wNode c.p base w10) (wValue base w3) c.i c.p.fuel root p l r m1
      (m1 + 2) (m1 + 2 + 2) pn ln rn (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)))
      ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ (!xn.leaf) cL cR
      (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg
      hT hp hpn hpleaf hpL hpR hclt hadj hln hrn hll' hrl' hlrange hrrange hrhead hgs hgL hgU
      ?_ rfl ?_ ?_ rfl ?_ ?_ (by rw [mrg_mergeParentNode_leaf]; exact hpleaf)
      (hparTwo (m1 + 2) g2) ?_ ?_ (by omega) (by omega) htimesN hwfN
      (newKlongs_times c.i first) (newKlongs_times c.i ks2) ?_
      (klongsWf_newKlongs c.i first) (klongsWf_newKlongs c.i ks2) key
    · simp only [wNode, h10t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
    · intro cc z
      rw [mrg_newKlongs_liveAt_iff _ c.i first hnd1 cc z, hE1]
    · simp only [wNode, h10t', hm2T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' _ (by omega) (by omega), lookup_upsert]
      simp only [show m1 + 2 ≠ p by omega, ↓reduceIte]
      rw [h8l, lookup_append_single_self _ _ _ hw6m2]
    · intro cc z
      rw [mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 cc z, hE2]
    · simp only [wNode, h10t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' p hpl hpr, lookup_upsert]
      simp
    · intro y hyp hyl hyr hym hym2
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h10t'
      rw [h10l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ hym2]
      exact h6old y (hyx y hyl hyr) hym
    · intro z hz
      have hzn : m1 ≤ z := by rcases hz with hz | hz | hz <;> omega
      exact ⟨(hfree z hzn).1, hfreshT z hzn⟩
    · rw [mergeParentNode_eq]
      exact mpNode_times pn c.i il cL m1 ir cR (some (m1 + 2, g2)) _ _ _ (hhtd _) hpt

/-- `sibling` reads the node that klong i of p names, of the kind asked. -/
theorem writerWP_sibling_leaf (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (base : View BVal) (hvc : ViewCoherent c base) :
    WriterWP (sibling p pn i inner) c w (fun sn v => pn.ptr? i = some sn.1 ∧
      ReadsAs c.p base w v ∧ v.nodes.lookup sn.1 = some sn.2 ∧
      (w.taken.contains sn.1 = false → wNode c.p base w sn.1 = some sn.2) ∧ w.nodes <+: v.nodes ∧
      (∀ z, (v.nodes.lookup z).isSome = true → (w.nodes.lookup z).isSome = true ∨
        (c.view z).isSome = true) ∧ sn.2.leaf = !inner) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s hs
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_getNode_all s c w base hvc) ?_
    intro sn v ⟨h1, h2, h3, h4, h5⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i hne
      simp only [writerWP_pure]
      refine ⟨hs, h1, h2, h3, h4, h5, ?_⟩
      cases hl : sn.leaf <;> cases inner <;> simp_all

/-- The writer's merge keeps the reading of every key: x at depth d merged with a
sibling under a reached inner parent with room, neither made by the
transaction, the walk's ranges kept (`RangeOrder`). -/
theorem writerWP_merge_get (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ pn.size + 4 ≤ c.p.M ∧
        (∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (htimesN : ∀ y yn, wNode c.p base w y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, wNode c.p base w y = some yn → klongsWf yn.ks = true) :
    WriterWP (merge x d) c w (fun _ w' => ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    exact ⟨by simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz], htz⟩
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hpleaf, hroom, hdead, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn
      have hmemL : (cL, l) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cR r rn hmemR hrn
      refine writerWP_mono (writerWP_mergeTail_get c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hroom hdead hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT
        hpleaf hclt hcap hadj hll hrl
        (fun cc z h => hlr2 cR r hmemR hclt cc z h)
        (by
          intro cc z h
          have h1 := hlr1 cc z h
          rw [hll] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
              · rcases Nat.eq_zero_or_pos cc with hcc | hcc
                · exact Or.inl hcc
                · exact Or.inr (by omega)
              · exact Or.inr (h0 hc0)
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            rcases Nat.eq_zero_or_pos cL with hc0 | hc0
            · omega
            · exact h1.1 hxl hc0)
        (by
          intro cc z h
          have h1 := hrr1 cc z h
          rw [hrl] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · exact Or.inr (h0 (by omega))
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            exact h1.1 hxl (by omega))
        (fun k z hk hkc cc z' h => hrr2 k z hk hkc cc z' h)
        htimesN hwfN) ?_
      intro _ w' h key
      rw [h key]
      unfold wGet
      rw [hr3.1, hr3.2.1, wValue_congr' base w3 w hr3.2.2.1 hr3.2.2.2.1]
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn0, hpn, hm⟩⟩
    have hptrk : ∀ i cv y, LastLive pn0.ks pn0.lastBitmap i cv → pn0.ptr? i = some y →
        pn0.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    refine writerWP_mono (writerWP_getNode_all x c w1 base hvc) ?_
    intro xn w2 ⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · rcases hsrc1 z h with h' | h'
        · exact hidn z h'
        · exact hidv z h'
      · exact hidv z h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn0 cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn0 cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn0.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- the step after a sibling is read: both nodes known
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (∀ z, (w3.nodes.lookup z).isSome = true → (wb.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes ∧
              (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) := by
          intro wb i cv sn w3 hrb hpreb hsrcb hl hp hr3 hpre3 hsrc3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3, ?_⟩
          · rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
          · intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrcb z h
            · exact hidv z h
        -- the right sibling, read from a state wb
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
          intro wb ia0 cva hrb hpreb hsrcb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 hkx hLx hka hLa
            hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, _, hwn3, hpre3, hsrc3, hsl⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 hkb hLb hkx hLx
              hbx (by
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 hLa hax (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
