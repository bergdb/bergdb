/-
Root collapse with the live counts (bergdb 030-01, step 4): from the merges'
loop's exit form after a merge (`LiveExit key g c base true`: the live counts
but at the root of segment g that collapse's descent finds), every run of
`collapseRoot key g` ends with `LiveEdges`.

A round of collapse finds the segment root x. If x is a leaf, or has no only
live klong (so, being the hole's, two at least: `two_le_live_of_onlyNone`), the
live counts hold (`liveEdges_of_segRoot`: x is the space root or a segment
leaf names it). A root that the transaction made with no made-for entry returns
early (030-01's stall point R3), here a premise (`CollapseMadeRootOK`). Else x
has one live klong, and its child takes its place (`takeBackRoot`,
`replaceRoot`); after that step the live counts hold (`CollapseStepLiveOK`), and
the next round returns.
-/
import SIS.Tree.LiveMergeRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## A node with no only live klong -/

/-- `onlyLiveKlong`'s fold fails only at two live key klongs of different
compare values. -/
theorem onlyStep_none_fold (del : List Nat) (ks : List Klong) :
    ks.zipIdx.foldl (onlyStep del) (some none) = none →
      ∃ j1 j2 c1 c2 y1 y2, ks[j1]? = some (.key c1 y1) ∧ j1 ∉ del ∧
        ks[j2]? = some (.key c2 y2) ∧ j2 ∉ del ∧ c1 ≠ c2 := by
  have key : ∀ rs : List Klong, OnlyOK rs.reverse del
      (rs.reverse.zipIdx.foldl (onlyStep del) (some none)) ∧
      (rs.reverse.zipIdx.foldl (onlyStep del) (some none) = none →
        ∃ j1 j2 c1 c2 y1 y2, rs.reverse[j1]? = some (.key c1 y1) ∧ j1 ∉ del ∧
          rs.reverse[j2]? = some (.key c2 y2) ∧ j2 ∉ del ∧ c1 ≠ c2) := by
    intro rs
    induction rs with
    | nil => exact ⟨fun i c h => (by cases h), fun h => (by simp at h)⟩
    | cons k rs ih =>
      obtain ⟨hok, hnone⟩ := ih
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      refine ⟨onlyOK_step rs.reverse del _ k hok, fun h => ?_⟩
      have hlift : ∀ (j c : Nat) (y : NodeId), rs.reverse[j]? = some (Klong.key c y) →
          (rs.reverse ++ [k])[j]? = some (Klong.key c y) := by
        intro j c y hj
        have hjl : j < rs.reverse.length := (List.getElem?_eq_some_iff.mp hj).1
        rw [getElem?_append_single_lt _ _ _ hjl]; exact hj
      generalize hacc : rs.reverse.zipIdx.foldl (onlyStep del) (some none) = acc at h hok hnone
      unfold onlyStep at h
      cases acc with
      | none =>
        obtain ⟨j1, j2, c1, c2, y1, y2, h1, d1, h2, d2, hne⟩ := hnone rfl
        exact ⟨j1, j2, c1, c2, y1, y2, hlift _ _ _ h1, d1, hlift _ _ _ h2, d2, hne⟩
      | some cur =>
        simp only at h
        cases k with
        | time _ => cases h
        | del _ => cases h
        | key c0 y0 =>
          simp only at h
          split at h
          · cases h
          · rename_i hd
            cases cur with
            | none => cases h
            | some pc =>
              rcases pc with ⟨i0, cv⟩
              simp only at h
              split at h
              · rename_i hne
                obtain ⟨⟨yi, hyi⟩, hdi, _⟩ := hok i0 cv rfl
                refine ⟨i0, rs.reverse.length, cv, c0, yi, y0, hlift _ _ _ hyi, hdi, ?_, ?_, ?_⟩
                · rw [getElem?_append_single_eq]
                · simpa using hd
                · intro he; rw [he] at hne; simp at hne
              · cases h
  have := (key ks.reverse).2
  rwa [List.reverse_reverse] at this

/-- `keyLookup` finds a compare value that a kept key klong has. -/
theorem keyLookup_ne_none_of_kept (del : List Nat) (c : Nat) :
    ∀ (xs : List (Klong × Nat)) (acc : Option NodeId),
      (acc ≠ none ∨ ∃ y j, (Klong.key c y, j) ∈ xs ∧ j ∉ del) →
      xs.foldl (keyLookupStep del c) acc ≠ none := by
  intro xs
  induction xs with
  | nil =>
    intro acc h
    rcases h with h | ⟨_, _, h, _⟩
    · exact h
    · cases h
  | cons q qs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases q with ⟨k, i⟩
    rcases h with h | ⟨y, j, hm, hj⟩
    · left
      unfold keyLookupStep
      cases k with
      | key a z =>
        simp only
        split
        · exact h
        · split
          · simp
          · exact h
      | _ => exact h
    · rcases List.mem_cons.mp hm with he | he
      · left
        cases he
        unfold keyLookupStep
        simp [hj]
      · right; exact ⟨y, j, he, hj⟩

/-- A node with no only live klong but a live klong has two at least. -/
theorem two_le_live_of_onlyNone (n : KNode) (h : n.onlyLiveKlong = none) (hne : n.live ≠ []) :
    2 ≤ n.live.length := by
  have hkept : ∀ j c y, n.ks[j]? = some (.key c y) → j ∉ n.lastBitmap →
      c ∈ n.live.map Prod.fst := by
    intro j c y hj hd
    have hk : keyLookup n.ks n.lastBitmap c ≠ none :=
      keyLookup_ne_none_of_kept n.lastBitmap c n.ks.zipIdx none
        (Or.inr ⟨y, j, List.mem_zipIdx_iff_getElem?.mpr hj, hd⟩)
    rw [← KNode.live_lookup] at hk
    cases hl : n.live.lookup c with
    | none => exact absurd hl hk
    | some z => exact List.mem_map.mpr ⟨(c, z), bk_mem_of_lookup _ _ _ hl, rfl⟩
  have h' : (match n.ks.zipIdx.foldl (onlyStep n.lastBitmap) (some none) with
      | some (some (i, _)) => some i
      | _ => none) = none := h
  generalize hr : n.ks.zipIdx.foldl (onlyStep n.lastBitmap) (some none) = r at h'
  cases r with
  | none =>
    obtain ⟨j1, j2, c1, c2, y1, y2, h1, d1, h2, d2, hne12⟩ := onlyStep_none_fold n.lastBitmap n.ks hr
    have := two_le_length_of_mem _ _ _ (hkept j1 c1 y1 h1 d1) (hkept j2 c2 y2 h2 d2) hne12
    simpa using this
  | some cur =>
    cases cur with
    | some ic => rcases ic with ⟨i, c⟩; simp at h'
    | none =>
      exfalso
      apply hne
      have hall := (onlyAll_fold n.lastBitmap n.ks).1 hr
      cases hl : n.live with
      | nil => rfl
      | cons q rest =>
        exfalso
        have hq : n.live.lookup q.1 = some q.2 :=
          lookup_of_mem_nodup _ n.live_keys_nodup q.1 q.2 (by rw [hl]; exact List.mem_cons_self)
        rw [KNode.live_lookup] at hq
        obtain ⟨j, hj, hjd⟩ := keyLookup_some_kept _ _ _ _ hq
        exact hjd (hall j q.1 q.2 hj)

/-! ## The exits of a round -/

/-- The live counts from the hole's form with at most the segment root x a
hole, when x is the space root or a segment leaf names it (`SegDesc`), and x is
a leaf or has two live klongs. -/
theorem liveEdges_of_segRoot (c : Ctx) (base : View BVal) (v : W) (x : NodeId)
    (Hl : NodeId → Prop) (hT : TreeOK (wNode c.p base v) c.i v.top.rootKey)
    (h : LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl) (hHl : ∀ y, Hl y → y = x)
    (hsd : SegDesc c base x v)
    (hx : ∀ xn, wNode c.p base v x = some xn → xn.leaf = true ∨ 2 ≤ (xn.liveAt c.i).length) :
    LiveEdges c.p (wNode c.p base v) c.i v.top.rootKey := by
  obtain ⟨_, ps, _, hlf, hend, _, hlast⟩ := hsd
  refine liveEdges_of_oneHole c.p _ c.i _ x Hl h hHl (fun xn hxn _ hl => ?_) ?_
  · rcases hx xn hxn with h1 | h1
    · rw [hl] at h1; cases h1
    · exact h1
  · intro u un cc xn hu hun hc hxn hne
    rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, hLl⟩
    · -- x is the space root: no link names it
      exfalso
      have hxr : x = v.top.rootKey := by rw [← hend, hps]; rfl
      exact hT.rootFree u cc hu (by rw [← hxr]; exact ⟨un, hun, hc⟩)
    · -- the segment leaf L names x, and only L
      rw [hps] at hlf
      obtain ⟨ln0, hln0, hk⟩ := LinkedFrom.last _ _ k x ps0 _ hlf
      rw [hL, hLn] at hln0
      cases hln0
      have hLR : TReach (wNode c.p base v) c.i v.top.rootKey L := by
        have := LinkedFrom.pathLen _ _ _ _ hlf ps0.length (by simp)
        have hnat : nodeAt v.top.rootKey (ps0 ++ [(some k, x)]) ps0.length = L := by
          rw [nodeAt_append_left _ _ _ _ (Nat.le_refl _), nodeAt_last, hL]
        rw [hnat] at this
        exact this.reach
      have huL := (hT.oneLink u cc L k x hu hLR ⟨un, hun, hc⟩ ⟨ln, hLn, hk⟩).1
      rw [huL, hLn] at hun
      cases hun
      refine ⟨hne, fun _ hxl => ?_, fun hl' => by rw [hLl] at hl'; cases hl'⟩
      rcases hx xn hxn with h1 | h1
      · rw [hxl] at h1; cases h1
      · exact h1

/-- R3 at the start of root collapse (030-01, section 2.3; checked on runs by
step 0's C4, a branch that never ran): the segment root that the first round
finds, if the transaction made it with no made-for entry and it is inner, has no
only live klong. -/
def R3At (key : Key) (g : Nat) (c : Ctx) (v : W) : Prop :=
  ∀ x v1, descendToSegmentRoot key g c v = .ok (x, v1) → ∀ n v2, getNode x c v1 = .ok (n, v2) →
    n.leaf = false → n.firstTime = some c.i → v2.madeFor.lookup x = none → n.onlyLiveKlong = none

/-- A step of root collapse at a segment root x that is the only hole and has
one live klong, the empty key's: after it, the live counts hold (bergdb 030-01,
step 4; an obligation here). -/
def CollapseStepLiveOK (c : Ctx) (base : View BVal) (B : NodeId) : Prop :=
  ∀ (x : NodeId) (v : W) (n : KNode) (only : Nat) (w0 : W) (F : Nat) (top0 : Top)
    (Hl : NodeId → Prop),
    CollGetInvF c base w0 v F → RangeOrder (wNode c.p base v) c.i v.top.rootKey →
    PutBook c B top0 v → SegDesc c base x v →
    LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey Hl → (∀ y, Hl y → y = x) →
    v.nodes.lookup x = some n → n.leaf = false → n.onlyLiveKlong = some only →
    n.cv? only = some 0 →
    (n.firstTime = some c.i → (v.madeFor.lookup x).isSome = true →
      WriterWP (takeBackRoot x (v.path.length - 1) only) c v
        (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey)) ∧
    (n.firstTime ≠ some c.i →
      WriterWP (replaceRoot x (v.path.length - 1) only) c v
        (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey))

set_option maxHeartbeats 4000000 in
/-- Root collapse with the live counts (bergdb 030-01, step 4), at a fuel F while
the next id is below F (the stratum's `collSteps_JW` for the tree): from the
live counts, or from the exit form after a merge with R3, every run ends with
the live counts, given the collapse's step (`CollapseStepLiveOK`). -/
theorem writerWP_collapseRoot_liveW (fuelR : Nat) (hfR : 2 ≤ fuelR) (key : Key) (g : Nat) (c : Ctx)
    (base : View BVal) (hvc : ViewCoherent c base) (w0 : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (KO : KindOracle) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hpos : 0 < c.i) (hSL : CollapseStepLiveOK c base B) :
    ∀ fuel v, CollInvJW c base w0 fuelR (fun u => u.next < fuelR) B top0 KO B B v →
      (v.next < fuelR → LiveEdges c.p (wNode c.p base v) c.i v.top.rootKey ∨
        (LiveExit key g c base true v ∧ R3At key g c v)) →
      WriterWP (collapseRoot key g fuel) c v
        (fun _ v' => v'.next < fuelR → LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  have hS := collSteps_JW fuelR hfR key g c base hvc w0 B top0 hB KO B hv hk hICEk hsa2
    (fun u => u.next < fuelR) (fun _ _ hle hlt => Nat.lt_of_le_of_lt hle hlt)
    (collFitsW_next c base w0 fuelR) B hpos (replaceRootFullJ2OKC_holds c base fuelR hfR B hpos hsa2)
  intro fuel
  induction fuel with
  | zero => intro v _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro v hI hL
    unfold collapseRoot
    simp only [writerWP_bind, writerWP_read]
    intro x v1 hdsr
    have hI1 := (hS.desc v hI x v1 hdsr).1
    have hP1 := (hS.desc v hI x v1 hdsr).2
    have hr1 : ReadsAs c.p base v v1 := writerWP_descendToSegmentRoot_readsU key g c base hvc v x v1 hdsr
    intro n v2 hget
    obtain ⟨hI2, hP2, hl2, hp2⟩ := hS.get x v1 hI1 hP1 n v2 hget
    have hr2 : ReadsAs c.p base v1 v2 := (writerWP_getNode_reads x c v1 base hvc n v2 hget).1
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hnx : v2.next = v.next := by rw [hr2.2.2.2.2, hr1.2.2.2.2]
    -- the round's live facts at v2: at most x a hole
    have hround : v2.next < fuelR → (LiveEdges c.p (wNode c.p base v2) c.i v2.top.rootKey ∨
        (∃ Hl, LiveEdgesH c.p (wNode c.p base v2) c.i v2.top.rootKey Hl ∧ (∀ y, Hl y → y = x)) ∧
        R3At key g c v) := by
      intro hlt
      rw [hr02.1, hr02.2.1]
      rcases hL (by rw [← hnx]; exact hlt) with h | ⟨hX, hR3⟩
      · exact Or.inl h
      · refine Or.inr ⟨⟨_, hX, fun y hy => (hy.2 x v1 hdsr).symm⟩, hR3⟩
    -- an exit where x is a leaf or has two live klongs
    have hexit : v2.next < fuelR → (∀ xn, wNode c.p base v2 x = some xn → xn.leaf = true ∨
        2 ≤ (xn.liveAt c.i).length) →
        LiveEdges c.p (wNode c.p base v2) c.i v2.top.rootKey := by
      intro hlt hx
      rcases hround hlt with h | ⟨⟨Hl, hX, hHl⟩, _⟩
      · exact h
      · exact liveEdges_of_segRoot c base v2 x Hl (hI2.2 hlt).1.1.1 hX hHl (hP2 hlt) hx
    have hxw : v2.next < fuelR → wNode c.p base v2 x = some n := by
      intro hlt
      have hxt : v2.taken.contains x = false := (hI2.2 hlt).1.1.2.1 x (hP2 hlt).1
      simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hl2]
    have htx : v2.next < fuelR → ∀ s, Klong.time s ∈ n.ks → s ≤ c.i := by
      intro hlt
      exact (hI2.2 hlt).1.1.2.2.1 x n (hP2 hlt).1 (hxw hlt)
    by_cases hleaf : n.leaf = true
    · simp only [hleaf, ↓reduceIte, writerWP_pure]
      intro hlt
      exact hexit hlt (fun xn hxn => by rw [hxw hlt] at hxn; cases hxn; exact Or.inl hleaf)
    · have hleaf' : n.leaf = false := by simpa using hleaf
      simp only [hleaf', Bool.false_eq_true, ↓reduceIte]
      unfold replacedBy
      simp only [writerWP_bind, writerWP_get, writerWP_pure]
      -- a node with no only live klong but a live one has two
      have htwo : v2.next < fuelR → n.onlyLiveKlong = none → 2 ≤ (n.liveAt c.i).length := by
        intro hlt hon
        rw [KNode.liveAt_of_times n c.i (htx hlt)]
        refine two_le_live_of_onlyNone n hon ?_
        rcases hround hlt with h | ⟨⟨Hl, hX, hHl⟩, _⟩
        · have hRk := (h.1 n)
          intro h0
          obtain ⟨_, ps, _, hlf, hend, _, hlast⟩ := hP2 hlt
          rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, _⟩
          · have hxr : x = v2.top.rootKey := by rw [← hend, hps]; rfl
            have := (hRk (by rw [← hxr]; exact hxw hlt)).1
              (by rw [KNode.liveAt_of_times n c.i (htx hlt)]; exact h0)
            rw [hleaf'] at this; cases this
          · rw [hps] at hlf
            obtain ⟨ln0, hln0, hk⟩ := LinkedFrom.last _ _ k x ps0 _ hlf
            rw [hL, hLn] at hln0
            cases hln0
            have hLR : TReach (wNode c.p base v2) c.i v2.top.rootKey L := by
              have := LinkedFrom.pathLen _ _ _ _ hlf ps0.length (by simp)
              have hnat : nodeAt v2.top.rootKey (ps0 ++ [(some k, x)]) ps0.length = L := by
                rw [nodeAt_append_left _ _ _ _ (Nat.le_refl _), nodeAt_last, hL]
              rw [hnat] at this
              exact this.reach
            have := (h.2 L ln k x n hLR hLn hk (hxw hlt)).1
            rw [KNode.liveAt_of_times n c.i (htx hlt)] at this
            exact this h0
        · obtain ⟨_, ps, _, hlf, hend, _, hlast⟩ := hP2 hlt
          intro h0
          rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, _⟩
          · have hxr : x = v2.top.rootKey := by rw [← hend, hps]; rfl
            have := (hX.1 n (by rw [← hxr]; exact hxw hlt)).1
              (by rw [KNode.liveAt_of_times n c.i (htx hlt)]; exact h0)
            rw [hleaf'] at this; cases this
          · rw [hps] at hlf
            obtain ⟨ln0, hln0, hk⟩ := LinkedFrom.last _ _ k x ps0 _ hlf
            rw [hL, hLn] at hln0
            cases hln0
            have hLR : TReach (wNode c.p base v2) c.i v2.top.rootKey L := by
              have := LinkedFrom.pathLen _ _ _ _ hlf ps0.length (by simp)
              have hnat : nodeAt v2.top.rootKey (ps0 ++ [(some k, x)]) ps0.length = L := by
                rw [nodeAt_append_left _ _ _ _ (Nat.le_refl _), nodeAt_last, hL]
              rw [hnat] at this
              exact this.reach
            have h1 := hX.2 L ln k x n hLR hLn hk (hxw hlt)
            have hxx : ¬ Hl x → False := by
              intro hn
              have := (h1.1 hn).1
              rw [KNode.liveAt_of_times n c.i (htx hlt)] at this
              exact this h0
            by_cases hHx : Hl x
            · have := h1.2 hHx
              rw [KNode.liveAt_of_times n c.i (htx hlt)] at this
              exact this h0
            · exact hxx hHx
      split
      · -- a made root with no made-for entry: R3
        rename_i hmr
        simp only [writerWP_pure]
        intro hlt
        refine hexit hlt (fun xn hxn => ?_)
        rw [hxw hlt] at hxn; cases hxn
        right
        refine htwo hlt ?_
        rcases hround hlt with h | ⟨_, hR3⟩
        · -- with the live counts, an inner segment root has two live klongs
          have hmade : n.firstTime = some c.i ∧ v2.madeFor.lookup x = none := by
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hmr
            exact hmr
          cases hon : n.onlyLiveKlong with
          | none => rfl
          | some only =>
            exfalso
            -- one live klong under a segment leaf or at the space root: not `LiveEdges`
            have hone : n.live.length ≤ 1 := n.onlyLiveKlong_some_cnt_le_one only hon
            obtain ⟨_, ps, _, hlf, hend, _, hlast⟩ := hP2 hlt
            rcases hlast with hps | ⟨ps0, k, L, ln, hps, hL, hLn, _⟩
            · have hxr : x = v2.top.rootKey := by rw [← hend, hps]; rfl
              have := (h.1 n (by rw [← hxr]; exact hxw hlt)).2 hleaf'
              rw [KNode.liveAt_of_times n c.i (htx hlt)] at this
              omega
            · rw [hps] at hlf
              obtain ⟨ln0, hln0, hk⟩ := LinkedFrom.last _ _ k x ps0 _ hlf
              rw [hL, hLn] at hln0
              cases hln0
              rename_i hLl
              have hLR : TReach (wNode c.p base v2) c.i v2.top.rootKey L := by
                have := LinkedFrom.pathLen _ _ _ _ hlf ps0.length (by simp)
                have hnat : nodeAt v2.top.rootKey (ps0 ++ [(some k, x)]) ps0.length = L := by
                  rw [nodeAt_append_left _ _ _ _ (Nat.le_refl _), nodeAt_last, hL]
                rw [hnat] at this
                exact this.reach
              have := (h.2 L ln k x n hLR hLn hk (hxw hlt)).2.1 hLl hleaf'
              rw [KNode.liveAt_of_times n c.i (htx hlt)] at this
              omega
        · have hmade : n.firstTime = some c.i ∧ v2.madeFor.lookup x = none := by
            simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at hmr
            exact hmr
          exact hR3 x v1 hdsr n v2 hget hleaf' hmade.1 hmade.2
      · rename_i hmr
        split
        · -- no only live klong
          rename_i hon
          simp only [writerWP_pure]
          intro hlt
          refine hexit hlt (fun xn hxn => ?_)
          rw [hxw hlt] at hxn; cases hxn
          exact Or.inr (htwo hlt hon)
        · rename_i only honly
          split
          · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
          · rename_i hcv
            have hcv' : n.cv? only = some 0 := by simpa using hcv
            unfold pathSize
            simp only [writerWP_bind, writerWP_get, writerWP_pure]
            -- the step and the next round, from the next id's growth if it is past F
            have hfc2 : FreshCache B v2 := hI2.1
            have hrest : ∀ {g' : M Unit}, KeepsFreshCache B g' →
                (v2.next < fuelR → WriterWP g' c v2 (fun _ v3 =>
                  CollInvJW c base w0 fuelR (fun u => u.next < fuelR) B top0 KO B B v3 ∧
                  LiveEdges c.p (wNode c.p base v3) c.i v3.top.rootKey)) →
                WriterWP (g' >>= fun _ => collapseRoot key g f) c v2
                  (fun _ v' => v'.next < fuelR →
                    LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
              intro g' hkg hstep
              rw [writerWP_bind]
              by_cases hlt : v2.next < fuelR
              · exact writerWP_mono (hstep hlt) (fun _ v3 ⟨hI3, hL3⟩ => ih v3 hI3 (fun _ => Or.inl hL3))
              · refine writerWP_mono (hkg c v2 hv hfc2) ?_
                rintro _ v3 ⟨hfc3, hle3⟩
                refine writerWP_mono (freshCache_collapseRoot key g f c v3 hv hfc3) ?_
                rintro _ v' ⟨_, hle'⟩ hlt'
                exact absurd (Nat.lt_of_le_of_lt (Nat.le_trans hle3 hle') hlt') hlt
            have hhole : v2.next < fuelR → ∃ Hl, LiveEdgesH c.p (wNode c.p base v2) c.i
                v2.top.rootKey Hl ∧ ∀ y, Hl y → y = x := by
              intro hlt
              rcases hround hlt with h | ⟨h, _⟩
              · exact ⟨fun _ => False, liveEdgesH_of_liveEdges _ _ _ _ _ h, fun _ h' => h'.elim⟩
              · exact h
            split
            · rename_i hmade
              have hm : n.firstTime = some c.i := by simpa using hmade
              have hrb : (v2.madeFor.lookup x).isSome = true := by
                simp only [hmade, Bool.true_and, Option.isNone_iff_eq_none] at hmr
                cases h : v2.madeFor.lookup x with
                | none => exact absurd h hmr
                | some _ => rfl
              refine hrest (freshCache_takeBackRoot x _ only) (fun hlt => ?_)
              obtain ⟨Hl, hX, hHl⟩ := hhole hlt
              obtain ⟨hCI, hR, hpb, _⟩ := hI2.2 hlt
              exact writerWP_mono (writerWP_and (hS.stepT x v2 n only hI2 hP2 hl2 hleaf' hm hrb honly hcv')
                ((hSL x v2 n only w0 fuelR top0 Hl hCI hR hpb (hP2 hlt) hX hHl hl2 hleaf' honly hcv').1
                  hm hrb)) (fun _ _ h => h)
            · rename_i hmade
              have hm : n.firstTime ≠ some c.i := by simpa using hmade
              refine hrest (freshCache_replaceRoot x _ only) (fun hlt => ?_)
              obtain ⟨Hl, hX, hHl⟩ := hhole hlt
              obtain ⟨hCI, hR, hpb, _⟩ := hI2.2 hlt
              exact writerWP_mono (writerWP_and (hS.stepR x v2 n only hI2 hP2 hl2 hleaf' hm honly hcv')
                ((hSL x v2 n only w0 fuelR top0 Hl hCI hR hpb (hP2 hlt) hX hHl hl2 hleaf' honly hcv').2
                  hm)) (fun _ _ h => h)

/-- Root collapse from the exit form after a merge, with R3 at its start
(bergdb 030-01, step 4): from the stratum's invariant with no fit and the books,
every run ends with the live counts, given the collapse's step. -/
theorem writerWP_collapseRoot_live (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (KO : KindOracle) (B : NodeId) (hv : ViewIdsBelow B c.view)
    (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove)
    (hpos : 0 < c.i) (top0 : Top) (hB : PutBase c base B) (hSL : CollapseStepLiveOK c base B)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v)
    (hX : LiveExit key g c base true v) (hR3 : R3At key g c v) :
    WriterWP (collapseRoot key g c.p.fuel) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  obtain ⟨u, hA⟩ := hJ
  intro r v' he
  have hF : c.p.fuel + 1 ≤ max (c.p.fuel + 1) (v'.next + 1) := Nat.le_max_left _ _
  have hp2 : 2 ≤ max (c.p.fuel + 1) (v'.next + 1) :=
    Nat.le_trans (by unfold Params.fuel; omega) hF
  have hn : v'.next < max (c.p.fuel + 1) (v'.next + 1) :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  have hle : v.next ≤ v'.next :=
    (freshCache_collapseRoot key g c.p.fuel c v hB.good.ids hpb.fresh r v' he).2
  obtain ⟨⟨⟨hP, _, hR, hICE, hFv, _, _⟩, hbk, hik⟩, hJ2, hBn⟩ := hA _ hF (Nat.lt_of_le_of_lt hle hn)
  have hCI : CollInvJW c base v (max (c.p.fuel + 1) (v'.next + 1))
      (fun u => u.next < max (c.p.fuel + 1) (v'.next + 1)) B top0 KO B B v := by
    refine ⟨hpb.fresh, fun _ => ⟨⟨⟨hP.tree, fun y hy => hP.untaken y (tReach_reachS _ _ _ _ hy),
      fun y yn _ h => hP.times y yn h, fun y yn cc z hy hyn hl hc => hICE y yn cc z hy hyn hl hc⟩,
      fun _ => rfl, hFv, fun y yn _ h => hP.wf y yn h, fun y yn _ h => hP.keyNoValue y yn h⟩,
      hR, hpb, hbk, hik, hJ2, hBn⟩⟩
  exact writerWP_collapseRoot_liveW _ hp2 key g c base hvc v B top0 hB KO hv hk hICEk hsa2 hpos hSL
    c.p.fuel v hCI (fun _ => Or.inr ⟨hX, hR3⟩) r v' he hn

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts, the live merge (`MergeLiveOK`), the collapse's step
(`CollapseStepLiveOK`) and R3 after the merges' loop, every run ends with the
live counts. -/
theorem writerWP_afterDelete_liveR (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (KO : KindOracle) (B : NodeId)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c) (hICEk : ICEFromKinds c base KO B)
    (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax) (hpos : 0 < c.i)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hkw : ViewKlongsWf c.p c.view) (top0 : Top)
    (hB : PutBase c base B) (hML : MergeLiveOK c base B H) (hSL : CollapseStepLiveOK c base B)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) := by
  unfold afterDelete
  simp only [writerWP_bind, writerWP_read, hm, ↓reduceIte]
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
    (writerWP_mergeUp_live key g c base hvc KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB hML
      c.p.fuel 0 false v hJ hpb hhi hLH (fun _ => rfl))
    (writerWP_mergeUp_delJAE key g c base hvc hpos KO B hv hk hICEk hsa2 hcap B c.p.fuel 0 false v hJ))
    (putBook_mergeUp key g c.p.fuel 0 false c base B top0 hB v hpb)) hR3) ?_
  rintro merged v1 ⟨⟨⟨hX, hJ1⟩, hpb1⟩, hR31⟩
  split
  · rename_i hmg
    exact writerWP_collapseRoot_live key g c base hvc KO B hv hk hICEk hsa2 hpos top0 hB hSL v1 hJ1 hpb1
      (by rw [← hmg]; exact hX) (hR31 hmg)
  · rename_i hmg
    simp only [writerWP_pure]
    refine liveEdges_of_liveEdgesH c.p _ c.i _ _ hX (fun _ _ hH => absurd hH.1 hmg) ?_
    intro _ _ _ _ _ _ _ _ _ hH
    exact absurd hH.1 hmg

/-! ## A collapse step on node maps -/

/-- The space root r, the only hole, inner with a live klong naming y, is
replaced by y: the live counts hold from y in any node map that agrees but at r. -/
theorem liveEdges_collapseSpace (p : Params) (N N' : NodeId → Option KNode) (t : Time) (r y : NodeId)
    (rn : KNode) (c0 : Nat) (Hl : NodeId → Prop) (hT : TreeOK N t r)
    (h : LiveEdgesH p N t r Hl) (hHl : ∀ z, Hl z → z = r) (hrn : N r = some rn)
    (hrl : rn.leaf = false) (hy : (c0, y) ∈ rn.liveAt t) (hm : p.merges = true)
    (hmb : 2 ≤ p.mergeBelow) (hN' : ∀ z, z ≠ r → N' z = N z) :
    LiveEdges p N' t y := by
  have hlk : TLink N t r c0 y := ⟨rn, hrn, hy⟩
  have hyr : y ≠ r := fun he => hT.rootFree r c0 TReach.root (by rw [← he] at hlk ⊢; exact hlk)
  have hnotH : ∀ z, z ≠ r → ¬ Hl z := fun z hz hH => hz (hHl z hH)
  have hreach : ∀ u, TReach N' t y u → TReach N t r u ∧ u ≠ r := by
    intro u hu
    induction hu with
    | root => exact ⟨TReach.link TReach.root hlk, hyr⟩
    | @link u c z _ hl ih =>
      obtain ⟨m, hm', hc⟩ := hl
      rw [hN' u ih.2] at hm'
      have hl' : TLink N t u c z := ⟨m, hm', hc⟩
      exact ⟨TReach.link ih.1 hl', fun he => hT.rootFree u c ih.1 (by rw [← he]; exact hl')⟩
  refine ⟨fun yn hyn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · rw [hN' y hyr] at hyn
    obtain ⟨h1, _, h3⟩ := (h.2 r rn c0 y yn TReach.root hrn hy hyn).1 (hnotH y hyr)
    have := h3 hrl hm
    exact ⟨fun hE => absurd hE h1, fun _ => by omega⟩
  · obtain ⟨huR, hur⟩ := hreach u hu
    rw [hN' u hur] at hun
    have hzr : z ≠ r := fun he => hT.rootFree u c huR (by rw [← he]; exact ⟨un, hun, hc⟩)
    rw [hN' z hzr] at hzn
    exact (h.2 u un c z zn huR hun hc hzn).1 (hnotH z hzr)

/-- A segment root x, the only hole, inner with one live klong naming y, below
the segment leaf L: L's klong k names y instead, and x is left behind. The live
counts hold in any node map that agrees but at L and x. -/
theorem liveEdges_collapseSeg (p : Params) (N N' : NodeId → Option KNode) (t : Time)
    (r L x y : NodeId) (ln ln' xn : KNode) (k c0 : Nat) (Hl : NodeId → Prop) (hT : TreeOK N t r)
    (h : LiveEdgesH p N t r Hl) (hHl : ∀ z, Hl z → z = x)
    (hL : TReach N t r L) (hLn : N L = some ln) (hLl : ln.leaf = true) (hk : (k, x) ∈ ln.liveAt t)
    (hxn : N x = some xn) (hxl : xn.leaf = false) (hxy : (c0, y) ∈ xn.liveAt t)
    (hm : p.merges = true) (hmb : 2 ≤ p.mergeBelow)
    (hN'L : N' L = some ln') (hl'l : ln'.leaf = ln.leaf)
    (hl' : ∀ c z, (c, z) ∈ ln'.liveAt t → (c = k ∧ z = y) ∨ ((c, z) ∈ ln.liveAt t ∧ c ≠ k))
    (hl'len : (ln.liveAt t).length ≤ (ln'.liveAt t).length)
    (hN' : ∀ z, z ≠ L → z ≠ x → N' z = N z) :
    LiveEdges p N' t r := by
  have hlkx : TLink N t L k x := ⟨ln, hLn, hk⟩
  have hxR : TReach N t r x := TReach.link hL hlkx
  have hlky : TLink N t x c0 y := ⟨xn, hxn, hxy⟩
  have hyR : TReach N t r y := TReach.link hxR hlky
  have hxr : x ≠ r := fun he => hT.rootFree L k hL (by rw [← he]; exact hlkx)
  have hyx : y ≠ x := fun he => hT.no_self_link x c0 hxR (by rw [← he] at hlky ⊢; exact hlky)
  have hLx : L ≠ x := fun he => hT.no_self_link L k hL ⟨ln, hLn, by rw [← he] at hk; exact hk⟩
  obtain ⟨dL, hdL⟩ := TReach.pathLen hL
  have hyL : y ≠ L := by
    intro he
    have h2 : PathLen N t r y (dL + 1 + 1) := PathLen.link (PathLen.link hdL hlkx) hlky
    rw [he] at h2
    have := PathLen.depth_unique hT _ _ _ hdL h2
    omega
  have hnotH : ∀ z, z ≠ x → ¬ Hl z := fun z hz hH => hz (hHl z hH)
  -- the only link to x is L's by k
  have honlyx : ∀ u c, TReach N t r u → TLink N t u c x → u = L ∧ c = k :=
    fun u c hu hl => hT.oneLink u c L k x hu hL hl hlkx
  have hreach : ∀ u, TReach N' t r u → TReach N t r u ∧ u ≠ x := by
    intro u hu
    induction hu with
    | root => exact ⟨TReach.root, Ne.symm hxr⟩
    | @link u c z _ hl ih =>
      obtain ⟨m, hm', hc⟩ := hl
      by_cases huL : u = L
      · subst huL
        rw [hN'L] at hm'
        cases hm'
        rcases hl' c z hc with ⟨_, hz⟩ | ⟨hold, hck⟩
        · subst hz; exact ⟨hyR, hyx⟩
        · have hl0 : TLink N t u c z := ⟨ln, hLn, hold⟩
          exact ⟨TReach.link ih.1 hl0, fun he => hck (honlyx u c ih.1 (by rw [← he]; exact hl0)).2⟩
      · rw [hN' u huL ih.2] at hm'
        have hl0 : TLink N t u c z := ⟨m, hm', hc⟩
        exact ⟨TReach.link ih.1 hl0, fun he => huL (honlyx u c ih.1 (by rw [← he]; exact hl0)).1⟩
  refine ⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · by_cases hrL : r = L
    · rw [hrL, hN'L] at hrn
      cases hrn
      refine ⟨fun _ => by rw [hl'l]; exact hLl, fun hl0 => ?_⟩
      rw [hl'l, hLl] at hl0; cases hl0
    · rw [hN' r hrL (Ne.symm hxr)] at hrn
      exact ⟨(h.1 rn hrn).1, (h.1 rn hrn).2 (hnotH r (Ne.symm hxr))⟩
  · obtain ⟨huR, hux⟩ := hreach u hu
    by_cases huL : u = L
    · subst huL
      rw [hN'L] at hun
      cases hun
      rcases hl' c z hc with ⟨_, hz⟩ | ⟨hold, hck⟩
      · subst hz
        rw [hN' z hyL hyx] at hzn
        obtain ⟨h1, _, h3⟩ := (h.2 x xn c0 z zn hxR hxn hxy hzn).1 (hnotH z hyx)
        have := h3 hxl hm
        exact ⟨h1, fun _ _ => by omega, fun hl0 => by rw [hl'l, hLl] at hl0; cases hl0⟩
      · have hl0 : TLink N t u c z := ⟨ln, hLn, hold⟩
        have hzx : z ≠ x := fun he => hck (honlyx u c huR (by rw [← he]; exact hl0)).2
        have hzu : z ≠ u := fun he => hT.no_self_link u c huR ⟨ln, hLn, by rw [he] at hold; exact hold⟩
        rw [hN' z hzu hzx] at hzn
        exact childOK_grow p t ln _ zn zn ((h.2 u ln c z zn huR hLn hold hzn).1 (hnotH z hzx))
          hl'l rfl (Nat.le_refl _)
    · rw [hN' u huL hux] at hun
      by_cases hzL : z = L
      · subst hzL
        rw [hN'L] at hzn
        cases hzn
        exact childOK_grow p t un un ln _ ((h.2 u un c z ln huR hun hc hLn).1 (hnotH z hLx))
          rfl hl'l hl'len
      · have hl0 : TLink N t u c z := ⟨un, hun, hc⟩
        have hzx : z ≠ x := fun he => huL (honlyx u c huR (by rw [← he]; exact hl0)).1
        rw [hN' z hzL hzx] at hzn
        exact (h.2 u un c z zn huR hun hc hzn).1 (hnotH z hzx)

end SIS.Tree
