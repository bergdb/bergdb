/-
Root collapse at the space root keeps every reading (bergdb 024-12, TP10's
`OpGetOK`; 024-22): an inner root whose only live klong is the empty key's
gives way to its child, which reads every key as the root did, given fuel for
the tree below it (`getFromR_collapse`); with it the writer's loop of collapses
keeps the reading (WriterGetCollapseLoop.lean).
-/
import SIS.Tree.WriterGetMergeMade
import SIS.Tree.WriterTreeCollapse
import SIS.Tree.GetSegRoot
import SIS.Tree.FuelPaths
import SIS.Tree.WGetAt

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The only live klong -/

/-- `onlyLiveKlong`'s fold so far: with no choice yet every key klong is
deleted; with a choice every kept key klong has its compare value. -/
def OnlyAll (ks : List Klong) (del : List Nat) (acc : Option (Option (Nat × Nat))) : Prop :=
  (acc = some none → ∀ j c' y', ks[j]? = some (.key c' y') → j ∈ del) ∧
  (∀ i c, acc = some (some (i, c)) → ∀ j c' y', ks[j]? = some (.key c' y') → j ∉ del → c' = c)

theorem onlyAll_step (ks : List Klong) (del : List Nat) (acc : Option (Option (Nat × Nat)))
    (k : Klong) (ha : OnlyAll ks del acc) :
    OnlyAll (ks ++ [k]) del (onlyStep del acc (k, ks.length)) := by
  obtain ⟨hn, hs⟩ := ha
  have hget : ∀ j c' y', (ks ++ [k])[j]? = some (.key c' y') →
      ks[j]? = some (.key c' y') ∨ (j = ks.length ∧ k = .key c' y') := by
    intro j c' y' h
    rcases Nat.lt_or_ge j ks.length with hj | hj
    · left; rw [getElem?_append_single_lt _ _ _ hj] at h; exact h
    · rcases Nat.lt_or_ge ks.length j with hj' | hj'
      · rw [getElem?_append_single_gt _ _ _ hj'] at h; cases h
      · have : j = ks.length := by omega
        subst this
        rw [getElem?_append_single_eq] at h
        simp only [Option.some.injEq] at h
        exact Or.inr ⟨rfl, h⟩
  unfold onlyStep
  cases acc with
  | none => exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
  | some cur =>
    simp only
    cases k with
    | time t =>
      refine ⟨fun h j c' y' hj => ?_, fun i c h j c' y' hj hdj => ?_⟩
      · rcases hget j c' y' hj with h1 | ⟨_, he⟩
        · exact hn h j c' y' h1
        · cases he
      · rcases hget j c' y' hj with h1 | ⟨_, he⟩
        · exact hs i c h j c' y' h1 hdj
        · cases he
    | del b =>
      refine ⟨fun h j c' y' hj => ?_, fun i c h j c' y' hj hdj => ?_⟩
      · rcases hget j c' y' hj with h1 | ⟨_, he⟩
        · exact hn h j c' y' h1
        · cases he
      · rcases hget j c' y' hj with h1 | ⟨_, he⟩
        · exact hs i c h j c' y' h1 hdj
        · cases he
    | key c0 y0 =>
      simp only
      by_cases hd : del.contains ks.length = true
      · simp only [hd, ↓reduceIte]
        refine ⟨fun h j c' y' hj => ?_, fun i c h j c' y' hj hdj => ?_⟩
        · rcases hget j c' y' hj with h1 | ⟨hj1, _⟩
          · exact hn h j c' y' h1
          · rw [hj1]; simpa using hd
        · rcases hget j c' y' hj with h1 | ⟨hj1, _⟩
          · exact hs i c h j c' y' h1 hdj
          · exact absurd (by rw [hj1]; simpa using hd) hdj
      · simp only [hd, Bool.false_eq_true, ↓reduceIte]
        cases cur with
        | none =>
          refine ⟨fun h => (by cases h), fun i c h j c' y' hj hdj => ?_⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨_, rfl⟩ := h
          rcases hget j c' y' hj with h1 | ⟨_, he⟩
          · exact absurd (hn rfl j c' y' h1) hdj
          · cases he; rfl
        | some pc =>
          rcases pc with ⟨i0, cv⟩
          simp only
          split
          · exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
          · rename_i hne
            refine ⟨fun h => (by cases h), fun i c h j c' y' hj hdj => ?_⟩
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨_, rfl⟩ := h
            have hc0 : c0 = cv := by simpa using hne
            rcases hget j c' y' hj with h1 | ⟨_, he⟩
            · have := hs i0 cv rfl j c' y' h1 hdj
              omega
            · cases he; rfl

theorem onlyAll_fold (del : List Nat) (ks : List Klong) :
    OnlyAll ks del (ks.zipIdx.foldl (onlyStep del) (some none)) := by
  have key : ∀ rs : List Klong, OnlyAll rs.reverse del
      (rs.reverse.zipIdx.foldl (onlyStep del) (some none)) := by
    intro rs
    induction rs with
    | nil =>
      refine ⟨fun _ j c' y' hj => ?_, fun _ _ h => by cases h⟩
      simp at hj
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact onlyAll_step rs.reverse del _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- A node with an only live klong i naming y: its live klongs are that one. -/
theorem onlyLiveKlong_live_iff (n : KNode) (i : Nat) (y : NodeId) (h : n.onlyLiveKlong = some i)
    (hy : n.ptr? i = some y) :
    ∃ c, n.ks[i]? = some (.key c y) ∧ ∀ c' z, (c', z) ∈ n.live ↔ c' = c ∧ z = y := by
  have hfA := onlyAll_fold n.lastBitmap n.ks
  have hfO := onlyOK_fold n.lastBitmap n.ks
  unfold KNode.onlyLiveKlong at h
  simp only at h
  split at h
  · rename_i i0 c0 hr
    simp only [Option.some.injEq] at h
    subst h
    have hr' : n.ks.zipIdx.foldl (onlyStep n.lastBitmap) (some none) = some (some (i0, c0)) := hr
    obtain ⟨⟨y1, hy1⟩, hd, hlater⟩ := hfO i0 c0 hr'
    have hall := hfA.2 i0 c0 hr'
    have hy1y : y1 = y := by simp only [KNode.ptr?, hy1, Option.some.injEq] at hy; exact hy
    subst hy1y
    have hLL : LastLive n.ks n.lastBitmap i0 c0 :=
      ⟨⟨y1, hy1⟩, hd, fun j y' hij hj => hlater j c0 y' hij hj⟩
    have hlk0 := keyLookup_of_last n.lastBitmap c0 n.ks i0 y1 hy1 hLL
    refine ⟨c0, hy1, fun c' z => ⟨fun hm => ?_, fun ⟨h1, h2⟩ => ?_⟩⟩
    · have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup n) c' z hm
      rw [KNode.live_lookup] at hlk
      obtain ⟨j, hj, hjd⟩ := keyLookup_some_kept n.lastBitmap c' z n.ks hlk
      have hc' := hall j c' z hj hjd
      subst hc'
      rw [hlk0] at hlk
      exact ⟨rfl, (Option.some.inj hlk).symm⟩
    · subst h1; subst h2
      apply bk_mem_of_lookup
      rw [KNode.live_lookup]
      exact hlk0
  · cases h

/-! ## The reading after a root collapse -/

/-- The root R, inner, whose only live klong is the empty key's to y, gives way
to y: every key reads from y in N', which agrees with N but at R, as from R in
N, when R's segment tree is shallower than the fuel (`SegDepthLe`). -/
theorem getFromR_collapse (N N' : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (R y : NodeId) (n : KNode) (hT : TreeOK N t R) (hRn : N R = some n)
    (hRl : n.leaf = false) (hlive : ∀ c z, (c, z) ∈ n.live ↔ c = 0 ∧ z = y)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hother : ∀ x, x ≠ R → N' x = N x)
    (hwf : ∀ x xn, ReachS N t R x → N x = some xn → klongsWf xn.ks = true)
    (hdepth : SegDepthLe N t (fuel - 1) R) :
    ∀ key, getFromR N' V t fuel key y = getFromR N V t fuel key R := by
  have hRy : (0, y) ∈ n.liveAt t := by
    rw [KNode.liveAt_of_times n t hnt]; exact (hlive 0 y).mpr ⟨rfl, rfl⟩
  obtain ⟨d', hd', hch⟩ := hdepth.of_inner hRn hRl
  obtain ⟨f, hf⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  have hlink : TLink N t R 0 y := ⟨n, hRn, hRy⟩
  have hyR : y ≠ R := fun h => hT.rootFree R 0 TReach.root (by rw [h] at hlink; exact hlink)
  have hlinks : ∀ x xn c z, ReachS N t R x → N x = some xn → (c, z) ∈ xn.liveAt t →
      ¬ (fun u => u = R) z := by
    intro x xn c z hx hxn hm hz
    exact hT.rootFree x c (reachS_tReach N t R x hx) (by rw [← hz]; exact ⟨xn, hxn, hm⟩)
  have hsame : ∀ x, ReachS N t R x → ¬ (fun u => u = R) x → N' x = N x :=
    fun x _ hx => hother x hx
  have hyS : ReachS N t R y := tReach_reachS N t R y (TReach.link TReach.root hlink)
  have hfirst : ∀ c, getEqR N' t c fuel y = getEqR N t c fuel R := by
    intro c
    rw [getEqR_avoid N N' t R (fun u => u = R) hsame hlinks c fuel y hyS hyR, hf,
      getEqR_fuel_mono N t c d' y (hch 0 y hRy) (f + 1) f (by omega) (by omega)]
    simp only [getEqR, hRn, hRl, Bool.false_eq_true, ↓reduceIte]
    have hs := KNode.searchLte_of_max n t hnt c 0 y ((hlive 0 y).mpr ⟨rfl, rfl⟩) (by omega)
      (fun q hq _ => by have := ((hlive q.1 q.2).mp hq).1; omega)
    cases hfd : n.searchLte t c with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      simp only [hs]
  exact getFromR_newRoot_sim N N' V t fuel R y (fun u => u = R) hfirst hwf hsame hlinks

/-! ## The writer's collapse loop at the space root -/

theorem writerWP_newSuperRoot_frameV (y : NodeId) (c : Ctx) (w : W) :
    WriterWP (newSuperRoot y) c w (fun _ w' => w'.top.rootKey = y ∧ w'.taken = w.taken ∧
      w'.nodes = w.nodes ∧ w'.vals = w.vals) := by
  unfold newSuperRoot note fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · simp only [writerWP_set, writerWP_bind, writerWP_modify]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [writerWP_bind, writerWP_modify, writerWP_get, writerWP_set, writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem writerWP_replaceRoot_spaceV (x : NodeId) (only : Nat) (n : KNode) (child : NodeId) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hptr : n.ptr? only = some child) :
    WriterWP (replaceRoot x 0 only) c w (fun _ w' => w'.top.rootKey = child ∧ w'.taken = w.taken ∧
      w'.vals = w.vals ∧ ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold replaceRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  rw [hptr]
  simp only [note, writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_unlink_frameV x c _) ?_
  intro _ w1 ⟨h1t, _, _, h1v, h1l⟩
  refine writerWP_mono (writerWP_newSuperRoot_frameV child c w1) ?_
  intro _ w2 ⟨h2r, h2t, h2n, h2v⟩
  exact ⟨h2r, by rw [h2t, h1t], by rw [h2v, h1v], fun y hy => by rw [h2n, h1l y hy]⟩

theorem writerWP_takeBackRoot_spaceV (x : NodeId) (only : Nat) (n : KNode) (child : NodeId) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hptr : n.ptr? only = some child) :
    WriterWP (takeBackRoot x 0 only) c w (fun _ w' => w'.top.rootKey = child ∧
      w'.taken = x :: w.taken ∧ w'.nodes = w.nodes ∧ w'.vals = w.vals) := by
  unfold takeBackRoot
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  rw [hptr]
  simp only [note, writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_newSuperRoot_frameV child c _) ?_
  intro _ w2 ⟨h2r, h2t, h2n, h2v⟩
  refine (writerWP_takenBack_iff x c w2 _).mpr ?_
  exact ⟨h2r, by simp only; rw [h2t], h2n, h2v⟩

/-- What root collapse at the space root keeps for the reading: `CollInv`, the
reading of a state w0, every segment tree reached shallower than the fuel
(`SegFits`), the reached nodes well formed and of no value. -/
def CollGetInv (c : Ctx) (base : View BVal) (w0 w : W) : Prop :=
  CollInv c base w ∧ (∀ key, wGet c.p c.i base w key = wGet c.p c.i base w0 key) ∧
  SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey ∧
  (∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
    klongsWf yn.ks = true) ∧
  (∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
    wValue base w y = none)

/-- `CollGetInv` with the reading and the fuel premise at a fuel f. -/
def CollGetInvF (c : Ctx) (base : View BVal) (w0 w : W) (f : Nat) : Prop :=
  CollInv c base w ∧ (∀ key, wGetAt c.p c.i base w f key = wGetAt c.p c.i base w0 f key) ∧
  SegFits (wNode c.p base w) c.i (f - 1) w.top.rootKey ∧
  (∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
    klongsWf yn.ks = true) ∧
  (∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
    wValue base w y = none)

theorem collGetInv_of_readsAsF (fuelR : Nat) (hfR : 2 ≤ fuelR) (c : Ctx) (base : View BVal) (w0 w v : W) (hr : ReadsAs c.p base w v)
    (h : CollGetInvF c base w0 w fuelR) : CollGetInvF c base w0 v fuelR := by
  have hV : wValue base v = wValue base w := wValue_congr' base v w hr.2.2.1 hr.2.2.2.1
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨collInv_of_readsAs c base w v hr h1, fun key => ?_, ?_, ?_, ?_⟩
  · rw [← h2 key]; unfold wGetAt; rw [hr.1, hr.2.1, hV]
  · rw [hr.1, hr.2.1]; exact h3
  · rw [hr.1, hr.2.1]; exact h4
  · rw [hr.1, hr.2.1, hV]; exact h5

/-- One collapse step keeps `CollGetInv`: the root r, inner, with only the live
klong (0, y), the super root now naming y, the values kept, nothing else changed
but r and its taking back. -/
theorem collGetInv_stepF (fuelR : Nat) (hfR : 2 ≤ fuelR) (c : Ctx) (base : View BVal) (w0 w w' : W) (y : NodeId) (n : KNode)
    (h : CollGetInvF c base w0 w fuelR) (hrn : wNode c.p base w w.top.rootKey = some n) (hrl : n.leaf = false)
    (hlive : ∀ cc z, (cc, z) ∈ n.live ↔ cc = 0 ∧ z = y)
    (htop : w'.top.rootKey = y) (hv : w'.vals = w.vals)
    (ht : ∀ z, z ≠ w.top.rootKey → w'.taken.contains z = w.taken.contains z)
    (hn : ∀ z, z ≠ w.top.rootKey → w'.nodes.lookup z = w.nodes.lookup z) : CollGetInvF c base w0 w' fuelR := by
  obtain ⟨hI, hG, hD, hW, hNV⟩ := h
  have hnt := hI.2.2.1 _ n TReach.root hrn
  have hRy : (0, y) ∈ n.liveAt c.i := by
    rw [KNode.liveAt_of_times n c.i hnt]; exact (hlive 0 y).mpr ⟨rfl, rfl⟩
  have hl : TLink (wNode c.p base w) c.i w.top.rootKey 0 y := ⟨n, hrn, hRy⟩
  have hN : ∀ z, z ≠ w.top.rootKey → wNode c.p base w' z = wNode c.p base w z := by
    intro z hz; simp only [wNode, ht z hz, hn z hz]
  have hy : ∃ m, wNode c.p base w y = some m := hI.2.2.2 _ n 0 y TReach.root hrn hrl hRy
  obtain ⟨_, hreach⟩ := treeOK_collapse_reach (wNode c.p base w) (wNode c.p base w') c.i
    w.top.rootKey y 0 hI.1 hl hy hN
  have hV : wValue base w' = wValue base w :=
    wValue_eq_of_taken base w w' hv (fun z => z = w.top.rootKey) (fun z hz => ht z hz)
      (fun z hz => by rw [hz]; exact ⟨hI.2.1 _ TReach.root, hNV _ n TReach.root hrn⟩)
  refine ⟨collInv_step c base w w' y 0 hI hl (fun m hm => by rw [hrn] at hm; cases hm; exact hrl)
    htop ht hn, fun key => ?_, ?_, ?_, ?_⟩
  · rw [← hG key]
    unfold wGetAt
    rw [hV, htop]
    exact getFromR_collapse (wNode c.p base w) (wNode c.p base w') (wValue base w) c.i fuelR
      w.top.rootKey y n hI.1 hrn hrl hlive hnt hN
      (fun x xn hx hxn => hW x xn (reachS_tReach _ _ _ _ hx) hxn) (hD _ ReachS.root) key
  · -- what y reaches after, r reached before, with the same nodes
    rw [htop]
    refine segFits_transfer _ _ c.i _ _ _ hD (fun u hu => ?_) (fun u un' hu hun' hl => ?_)
    · exact tReach_reachS _ _ _ _ (hreach u (reachS_tReach _ _ _ _ hu)).1
    · have hur := (hreach u (reachS_tReach _ _ _ _ hu)).2
      rw [hN u hur] at hun'
      exact ⟨un', hun', hl, fun c' y' hy' => ⟨c', hy'⟩⟩
  · intro z zn hz hzn
    rw [htop] at hz
    obtain ⟨h1, h2⟩ := hreach z hz
    rw [hN z h2] at hzn
    exact hW z zn h1 hzn
  · intro z zn hz hzn
    rw [htop] at hz
    obtain ⟨h1, h2⟩ := hreach z hz
    rw [hN z h2] at hzn
    rw [hV]
    exact hNV z zn h1 hzn

end SIS.Tree
