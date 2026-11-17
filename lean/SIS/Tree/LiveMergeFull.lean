/-
The merge's tail where its parent goes `full` (bergdb 030-01, step 3's rest):
the parent split in time below a grandparent with room, the merge into one node.
The hole moves from the parent to the parent's copy, which the grandparent's
klong names instead (`writerWP_handleFull_timeRoom_liveGh`); the merged nodes and
the parent are left behind, so the cleanup changes nothing the tree reaches; the
next round's descent finds the copy (`descendToHeight_redirect`). The rest of
`MergeTailFullOK` is a narrower premise, `MergeTailFullRestOK`.
-/
import SIS.Tree.LiveMergeTail

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## `mergeParent`'s `full` -/

/-- `mergeParent` where its branch with room is not taken: `handleFull` of the
parent's last version `mergeFullLast`, compacting exactly when the parent had
room. -/
theorem writerWP_mergeParent_fullB (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (post : Unit → W → Prop)
    (hlk : w.nodes.lookup p = some pn) (hnB : ¬ MergeParentRoom c pn il cL m1 ir cR m2)
    (hfullP : ∀ (last : KNode) (compact : Bool) (s : String),
      mergeFullLast pn c.i cL m1 cR m2 = some last →
      compact = decide (pn.size + mergeParentNeed c.i pn il ir cR m2 ≤ c.p.M) →
      WriterWP (handleFull depth p last compact) c ({ w with trail := s :: w.trail } : W) post) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w post := by
  cases m2 with
  | none =>
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_if
    · intro hfit
      apply writerWP_if
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          apply hfullP
          · simp only [mergeFullLast] at hks ⊢
            simp only [hks]
          · exact (decide_eq_true hfit).symm
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro hd
        exact absurd ⟨hfit, Bool.eq_false_iff.mpr hd⟩ hnB
    · intro hfit
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        apply hfullP
        · simp only [mergeFullLast] at hks ⊢
          simp only [hks]
        · exact (decide_eq_false hfit).symm
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
  | some yg =>
    obtain ⟨y, g⟩ := yg
    unfold mergeParent
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known p pn c w hlk]
    apply writerWP_if
    · intro hfit
      apply writerWP_if
      · intro _
        simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
        split
        · rename_i ks hks
          by_cases hg : g = cR
          · have hgb : (g != cR) = false := by simp [hg]
            simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
            split
            · rename_i ks2 hks2
              apply hfullP
              · simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
              · exact (decide_eq_true hfit).symm
            · exact writerWP_throw _ _ _ _
            · exact writerWP_throw _ _ _ _
          · have hgb : (g != cR) = true := by simp [hg]
            simp only [hgb, ↓reduceIte] at hks ⊢
            apply hfullP
            · simp only [mergeFullLast, hgb, ↓reduceIte, hks]
            · exact (decide_eq_true hfit).symm
        · exact writerWP_throw _ _ _ _
        · exact writerWP_throw _ _ _ _
      · intro hd
        exact absurd ⟨hfit, Bool.eq_false_iff.mpr hd⟩ hnB
    · intro hfit
      simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
      split
      · rename_i ks hks
        by_cases hg : g = cR
        · have hgb : (g != cR) = false := by simp [hg]
          simp only [hgb, Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_pure] at hks ⊢
          split
          · rename_i ks2 hks2
            apply hfullP
            · simp only [mergeFullLast, hgb, Bool.false_eq_true, ↓reduceIte, hks, hks2]
            · exact (decide_eq_false hfit).symm
          · exact writerWP_throw _ _ _ _
          · exact writerWP_throw _ _ _ _
        · have hgb : (g != cR) = true := by simp [hg]
          simp only [hgb, ↓reduceIte] at hks ⊢
          apply hfullP
          · simp only [mergeFullLast, hgb, ↓reduceIte, hks]
          · exact (decide_eq_false hfit).symm
      · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _

/-! ## The heights' cache through the merge's steps -/

/-- `getNode` adds to the cache at most an entry of its own node. -/
theorem writerWP_getNode_ghL (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun _ w' => ∀ y, y ≠ x → w'.gh.lookup y = w.gh.lookup y) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · exact (writerWP_pure _ c w _).mpr (fun _ _ => rfl)
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        intro y hy
        have hb : (y == x) = false := by simp [hy]
        simp only [List.lookup, hb]
    · exact writerWP_throw _ _ _ _

/-- `newKey` adds to the cache only the new node's entry. -/
theorem writerWP_newKey_ghL (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W) :
    WriterWP (newKey g h leaf ks) c w (fun x w' => ∀ y, y ≠ x → w'.gh.lookup y = w.gh.lookup y) := by
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    intro y hy
    have hb : (y == w.next) = false := by simp [hy]
    simp only [List.lookup, hb]

/-- The merge's last loop changes the cache and the nodes only at its own
nodes and p, and keeps the path and the super root. -/
theorem writerWP_mergeCleanup_frameL (p m1 : NodeId) (c : Ctx) :
    ∀ (xs : List (NodeId × Bool)) (w : W),
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => w'.top = w.top ∧ w'.path = w.path ∧ ∀ y, y ≠ p → (∀ q ∈ xs, y ≠ q.1) →
        w'.gh.lookup y = w.gh.lookup y ∧ w'.nodes.lookup y = w.nodes.lookup y) := by
  intro xs
  induction xs with
  | nil =>
    intro w
    rw [List.forIn_nil]
    exact (writerWP_pure _ c w _).mpr ⟨rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | cons q qs ih =>
    intro w
    rw [List.forIn_cons]
    have hrest : ∀ w1 : W, w1.top = w.top → w1.path = w.path →
        (∀ y, y ≠ p → y ≠ q.1 → w1.gh.lookup y = w.gh.lookup y ∧
          w1.nodes.lookup y = w.nodes.lookup y) →
        WriterWP (forIn qs PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))) c w1
        (fun _ w' => w'.top = w.top ∧ w'.path = w.path ∧ ∀ y, y ≠ p → (∀ q' ∈ q :: qs, y ≠ q'.1) →
          w'.gh.lookup y = w.gh.lookup y ∧ w'.nodes.lookup y = w.nodes.lookup y) := by
      intro w1 h1top h1path h1
      refine writerWP_mono (ih w1) ?_
      intro _ w2 ⟨h2top, h2path, h2⟩
      refine ⟨h2top.trans h1top, h2path.trans h1path, fun y hyp hy => ?_⟩
      obtain ⟨a2, b2⟩ := h2 y hyp (fun q' hq' => hy q' (List.mem_cons_of_mem _ hq'))
      obtain ⟨a1, b1⟩ := h1 y hyp (hy q List.mem_cons_self)
      exact ⟨a2.trans a1, b2.trans b1⟩
    split
    · simp only [writerWP_bind]
      unfold retarget
      simp only [writerWP_bind, writerWP_read]
      refine writerWP_mono (writerWP_and (writerWP_getNode_ghL p c w) (writerWP_getNode_frame p c w)) ?_
      intro n w1 ⟨h1, _, h1top, _, _, h1path, _, h1n⟩
      split
      · simp only [putNode, takenBack, note, writerWP_bind, writerWP_modify, writerWP_pure]
        refine hrest _ h1top h1path (fun y hyp _ => ⟨h1 y hyp, ?_⟩)
        show (upsert w1.nodes p _).lookup y = _
        rw [lookup_upsert, if_neg hyp, h1n y hyp]
      · simp only [takenBack, note, writerWP_bind, writerWP_modify, writerWP_pure]
        exact hrest _ h1top h1path (fun y hyp _ => ⟨h1 y hyp, h1n y hyp⟩)
    · simp only [writerWP_bind]
      unfold unlink
      simp only [writerWP_bind, writerWP_read]
      refine writerWP_mono (writerWP_and (writerWP_getNode_ghL q.1 c w)
        (writerWP_getNode_frame q.1 c w)) ?_
      intro n w1 ⟨h1, _, h1top, _, _, h1path, _, h1n⟩
      split
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine hrest _ h1top h1path (fun y _ hyq => ⟨h1 y hyq, ?_⟩)
        show (upsert w1.nodes q.1 _).lookup y = _
        rw [lookup_upsert, if_neg hyq, h1n y hyq]
      · simp only [writerWP_bind, writerWP_pure]
        exact hrest _ h1top h1path (fun y _ hyq => ⟨h1 y hyq, h1n y hyq⟩)

/-- `ghOf` changes the cache only at its own node. -/
theorem writerWP_ghOf_ghL (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf x) c w (fun _ w' => ∀ y, y ≠ x → w'.gh.lookup y = w.gh.lookup y) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_ghL x c w) ?_
  intro _ w1 h1
  simp only [writerWP_get]
  split
  · exact (writerWP_pure _ c w1 _).mpr h1
  · exact writerWP_throw _ _ _ _

/-- `setMadeFor` keeps the cache. -/
theorem writerWP_setMadeFor_gh (m : NodeId) (o : Option NodeId) (c : Ctx) (w : W) :
    WriterWP (setMadeFor m o) c w (fun _ w' => w'.gh = w.gh) := by
  unfold setMadeFor
  split
  · simp only [writerWP_modify]
  · exact (writerWP_pure _ c w _).mpr rfl

/-! ## Reach -/

/-- A node reached at depth k is reached in a map that agrees on every node
reached above depth k. -/
theorem tReach_of_pathLen_agree (N N' : NodeId → Option KNode) (t : Time) (r : NodeId) :
    ∀ z k, PathLen N t r z k → (∀ u j, PathLen N t r u j → j < k → N' u = N u) →
      PathLen N' t r z k := by
  intro z k h
  induction h with
  | root => intro _; exact PathLen.root
  | @link u c y n hu hl ih =>
    intro hag
    obtain ⟨un, hun, hc⟩ := hl
    refine PathLen.link (ih (fun u' j hu' hj => hag u' j hu' (by omega))) ⟨un, ?_, hc⟩
    rw [hag u n hu (by omega)]; exact hun

/-- The nodes reached after a redirect (`liveEdgesH_redirect`'s situation): the
copy y, or a node reached before that is neither x nor y. -/
theorem redirect_reach (V N' : NodeId → Option KNode) (t : Time) (r q x y : NodeId)
    (qn qn' xl : KNode) (k1 : Nat)
    (hT : TreeOK V t r) (hq : TReach V t r q) (hqn : V q = some qn) (hk : (k1, x) ∈ qn.liveAt t)
    (hxn : V x = some xl) (hyV : V y = none) (hyf : ∀ u c, TReach V t r u → ¬ TLink V t u c y)
    (hN'y : N' y = some xl) (hN'q : N' q = some qn')
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t → (c = k1 ∧ z = y) ∨ ((c, z) ∈ qn.liveAt t ∧ c ≠ k1))
    (hN' : ∀ z, z ≠ q → z ≠ x → z ≠ y → N' z = V z) :
    ∀ u, TReach N' t r u → (TReach V t r u ∧ u ≠ x ∧ u ≠ y) ∨ u = y := by
  have hlkx : TLink V t q k1 x := ⟨qn, hqn, hk⟩
  have hxR : TReach V t r x := TReach.link hq hlkx
  have hxr : x ≠ r := fun he => hT.rootFree q k1 hq (by rw [← he]; exact hlkx)
  have hyr : y ≠ r := by
    intro he; obtain ⟨m, hm⟩ := hT.rootKey; rw [← he, hyV] at hm; cases hm
  have honlyx : ∀ u c, TReach V t r u → TLink V t u c x → u = q ∧ c = k1 :=
    fun u c hu hl => hT.oneLink u c q k1 x hu hq hl hlkx
  obtain ⟨dq, hdq⟩ := TReach.pathLen hq
  have hchild : ∀ c z, (c, z) ∈ xl.liveAt t → z ≠ x ∧ z ≠ y := by
    intro c z hz
    have hl : TLink V t x c z := ⟨xl, hxn, hz⟩
    exact ⟨fun he => hT.no_self_link x c hxR (by rw [he] at hl; exact hl),
      fun he => hyf x c hxR (by rw [← he]; exact hl)⟩
  intro u hu
  induction hu with
  | root => exact Or.inl ⟨TReach.root, Ne.symm hxr, Ne.symm hyr⟩
  | @link u c z _ hl ih =>
    obtain ⟨m, hm', hc⟩ := hl
    rcases ih with ⟨huR, hux, huy⟩ | huy
    · by_cases huq : u = q
      · subst huq
        rw [hN'q] at hm'
        cases hm'
        rcases hq' c z hc with ⟨_, hz⟩ | ⟨hold, hck⟩
        · exact Or.inr hz
        · have hl0 : TLink V t u c z := ⟨qn, hqn, hold⟩
          refine Or.inl ⟨TReach.link huR hl0, fun he => hck (honlyx u c huR (by rw [← he]; exact hl0)).2,
            fun he => hyf u c huR (by rw [← he]; exact hl0)⟩
      · rw [hN' u huq hux huy] at hm'
        have hl0 : TLink V t u c z := ⟨m, hm', hc⟩
        exact Or.inl ⟨TReach.link huR hl0, fun he => huq (honlyx u c huR (by rw [← he]; exact hl0)).1,
          fun he => hyf u c huR (by rw [← he]; exact hl0)⟩
    · subst huy
      rw [hN'y] at hm'
      cases hm'
      obtain ⟨hzx, hzy⟩ := hchild c z hc
      exact Or.inl ⟨TReach.link hxR ⟨xl, hxn, hc⟩, hzx, hzy⟩

/-- The hole's form depends only on the nodes reached. -/
theorem liveEdgesH_congr_reach (p : Params) (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (Hl : NodeId → Prop) (h : LiveEdgesH p N t r Hl) (hag : ∀ z, TReach N t r z → N' z = N z) :
    LiveEdgesH p N' t r Hl := by
  have hR : ∀ z, TReach N' t r z → TReach N t r z := by
    intro z hz
    induction hz with
    | root => exact TReach.root
    | @link u c y _ hl ih =>
      obtain ⟨m, hm, hc⟩ := hl
      rw [hag u ih] at hm
      exact TReach.link ih ⟨m, hm, hc⟩
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · rw [hag r TReach.root] at hrn; exact h.1 rn hrn
  · have huN := hR u hu
    rw [hag u huN] at hun
    have hyN : TReach N t r y := TReach.link huN ⟨un, hun, hc⟩
    rw [hag y hyN] at hyn
    exact h.2 u un c y yn huN hun hc hyn

/-! ## The descent's steps, its heights, and a search after a redirect -/

/-- Each step of the descent below the segment root is `searchLte` of the node
before at the key's compare value. -/
theorem dhP_step (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time)
    (cv h : Nat) :
    ∀ f z ext, dhP Rd Gh t cv h f z = some ext → ∀ (i : Nat) (e : Option Nat × NodeId),
      ext[i]? = some e →
      ∃ u n fd, (z :: ext.map (·.2))[i]? = some u ∧ Rd u = some n ∧ n.searchLte t cv = some fd ∧
        e = (some fd.c, fd.y) := by
  intro f
  induction f with
  | zero => intro z ext h1; simp [dhP] at h1
  | succ f ih =>
    intro z ext h1 i e he
    unfold dhP at h1
    split at h1
    · rename_i n gz hz hRz hGz
      split at h1
      · cases h1; simp at he
      · split at h1
        · cases h1
        · split at h1
          · cases h1
          · rename_i fd hfd
            cases hrest : dhP Rd Gh t cv h f fd.y with
            | none => rw [hrest] at h1; cases h1
            | some ext' =>
              rw [hrest] at h1
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              cases i with
              | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at he
                exact ⟨z, n, fd, rfl, hRz, hfd, he.symm⟩
              | succ i =>
                simp only [List.getElem?_cons_succ] at he
                obtain ⟨u, n', fd', hu, hn', hfd', he'⟩ := ih fd.y ext' hrest i e he
                refine ⟨u, n', fd', ?_, hn', hfd', he'⟩
                simpa using hu
    · cases h1

/-- `GradedL` at a position: an inner node is one height above the next. -/
theorem gradedL_get (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) :
    ∀ (L : List NodeId) (i : Nat) (a b : NodeId) (n : KNode), GradedL Rd Gh L → L[i]? = some a →
      L[i + 1]? = some b → Rd a = some n → n.leaf = false →
      ∃ g1 h1 g2 h2, Gh a = some (g1, h1) ∧ Gh b = some (g2, h2) ∧ h1 = h2 + 1 := by
  intro L
  induction L with
  | nil => intro i a b n _ ha; simp at ha
  | cons z rest ih =>
    intro i a b n hg ha hb hn hl
    cases rest with
    | nil => simp at hb
    | cons z2 rest2 =>
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hb
        subst ha; subst hb
        exact hg.1 n hn hl
      | succ i =>
        simp only [List.getElem?_cons_succ] at ha hb
        exact ih i a b n hg.2 ha hb hn hl

/-- After q's klong k1, the one `searchLte` finds at cv, is pointed to y by a
new klong, `searchLte` finds y. -/
theorem searchLte_add_key (qn : KNode) (t : Time) (cv k1 : Nat) (y : NodeId) (fd : Found)
    (hwf : klongsWf qn.ks = true) (htm : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hfd : qn.searchLte t cv = some fd) (hc : fd.c = k1) :
    ∃ fd', (qn.add t (.key k1 y)).searchLte t cv = some fd' ∧ fd'.y = y := by
  have hat := KNode.add_times qn t (.key k1 y) (fun s h => by cases h) htm
  have hq' : ∀ c' z, (c', z) ∈ (qn.add t (.key k1 y)).liveAt t →
      (c' = k1 ∧ z = y) ∨ ((c', z) ∈ qn.liveAt t ∧ c' ≠ k1) := by
    intro c' z hmm
    rw [KNode.liveAt_of_times _ t hat] at hmm
    have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
    rw [KNode.add_key_live_lookup_of_wf qn t k1 c' y hwf] at hlk'
    by_cases hck : k1 = c'
    · subst hck; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
    · have hb : (k1 == c') = false := by simpa using hck
      rw [hb] at hlk'
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
      refine Or.inr ⟨?_, Ne.symm hck⟩
      rw [KNode.liveAt_of_times qn t htm]
      exact bk_mem_of_lookup _ c' z hlk'
  have hky : (k1, y) ∈ (qn.add t (.key k1 y)).liveAt t := by
    rw [KNode.liveAt_of_times _ t hat]
    apply bk_mem_of_lookup
    rw [KNode.add_key_live_lookup_of_wf qn t k1 k1 y hwf]
    simp
  obtain ⟨hs1, _⟩ := KNode.searchLte_spec qn t cv
  obtain ⟨hmem, hle, hmax⟩ := hs1 fd hfd
  simp only [decide_eq_true_eq] at hle hmax
  obtain ⟨hs1', hs2'⟩ := KNode.searchLte_spec (qn.add t (.key k1 y)) t cv
  cases hr : (qn.add t (.key k1 y)).searchLte t cv with
  | none =>
    exfalso
    have := (hs2'.mp hr) (k1, y) hky
    simp only [decide_eq_false_iff_not] at this
    rw [← hc] at this
    exact this hle
  | some f' =>
    refine ⟨f', rfl, ?_⟩
    obtain ⟨hmem', hle', hmax'⟩ := hs1' f' hr
    simp only [decide_eq_true_eq] at hle' hmax'
    rcases hq' f'.c f'.y hmem' with ⟨_, h⟩ | ⟨hold, hne⟩
    · exact h
    · exfalso
      have h1 := hmax (f'.c, f'.y) hold hle'
      have h2 := hmax' (k1, y) hky (by rw [← hc]; exact hle)
      simp only at h1 h2
      rw [hc] at h1
      exact hne (by omega)

/-- The descent at (g, h) that found x at depth d, its parent p and p's parent q
inner: q's `searchLte` at the key's compare value finds the klong k1 of the
path's entry for p. -/
theorem descend_qsearch (key : Key) (g h : Nat) (c : Ctx) (S S1 : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q : NodeId) (pn qn : KNode) (k1 : Nat)
    (hpk : S1.path[d - 1]? = some (some k1, p)) (hpn : rdN c S p = some pn) (hpl : pn.leaf = false)
    (hq : (S1.path[d - 2]?).map (·.2) = some q) (hqn : rdN c S q = some qn) (hql : qn.leaf = false) :
    ∃ cv fd, key[g]? = some cv ∧ qn.searchLte c.i cv = some fd ∧ fd.c = k1 := by
  obtain ⟨root, P0, cv, ext, hdsr, hcv, hdh, hp1, hd1, -⟩ :=
    writerWP_descendToHeight_rd key g h c S d S1 hS
  obtain ⟨hlast, hpre, hnil⟩ := dsrP_shape (rdN c S) c.i c.p.fuel key g _ root P0 hdsr
  obtain ⟨B, hB⟩ := List.getLast?_eq_some_iff.mp hlast
  have hL : S1.path.map (·.2) = B ++ (root :: ext.map (·.2)) := by
    rw [hp1, List.map_append, hB]; simp
  have hlenL : S1.path.length = B.length + 1 + ext.length := by
    have := congrArg List.length hL
    simp only [List.length_map, List.length_append, List.length_cons] at this
    omega
  have hlenP : P0.length = B.length + 1 := by
    have := congrArg List.length hB
    simp only [List.length_map, List.length_append, List.length_cons, List.length_nil] at this
    omega
  have hdL : d = B.length + ext.length := by
    have h2 : (P0 ++ ext).length = B.length + 1 + ext.length := by rw [← hp1]; exact hlenL
    rw [hd1]; omega
  have hBleaf : ∀ z, B.getLast? = some z → ∃ n, rdN c S z = some n ∧ n.leaf = true := by
    intro z hz
    by_cases hg : key.take g = []
    · have := hnil hg
      rw [this] at hB
      simp only [List.map_cons, List.map_nil] at hB
      have hBn : B = [] := by
        cases B with
        | nil => rfl
        | cons a l => simp at hB
      rw [hBn] at hz; cases hz
    · obtain ⟨yl, nl, hyl, hnl, hll⟩ := hpre hg
      rw [hB, List.dropLast_concat, hz] at hyl
      cases hyl
      exact ⟨nl, hnl, hll⟩
  have hidx : ∀ i z, i < B.length → (S1.path[i]?).map (·.2) = some z → B[i]? = some z := by
    intro i z hi hz
    rw [← List.getElem?_map, hL, List.getElem?_append_left hi] at hz
    exact hz
  have hp' : (S1.path[d - 1]?).map (·.2) = some p := by rw [hpk]; rfl
  have hext : 2 ≤ ext.length := by
    rcases Nat.lt_or_ge ext.length 2 with hlt | hge
    · exfalso
      have hlastB : B.getLast? = B[B.length - 1]? := List.getLast?_eq_getElem?
      rcases Nat.lt_or_ge ext.length 1 with h0 | h1
      · have hz := hidx (d - 1) p (by omega) hp'
        have : d - 1 = B.length - 1 := by omega
        rw [this, ← hlastB] at hz
        obtain ⟨n, hn, hnl⟩ := hBleaf p hz
        rw [hpn] at hn; cases hn; rw [hpl] at hnl; cases hnl
      · have hz := hidx (d - 2) q (by omega) hq
        have : d - 2 = B.length - 1 := by omega
        rw [this, ← hlastB] at hz
        obtain ⟨n, hn, hnl⟩ := hBleaf q hz
        rw [hqn] at hn; cases hn; rw [hql] at hnl; cases hnl
    · exact hge
  -- the entry for p is the descent's step at q
  have he : ext[ext.length - 2]? = some (some k1, p) := by
    rw [hp1, List.getElem?_append_right (by omega), hlenP] at hpk
    have : d - 1 - (B.length + 1) = ext.length - 2 := by omega
    rw [this] at hpk
    exact hpk
  obtain ⟨u, n, fd, hu, hn, hfd, hfe⟩ := dhP_step (rdN c S) (rdG c S) c.i cv h c.p.fuel root ext hdh
    (ext.length - 2) _ he
  have huq : u = q := by
    have hz : (S1.path.map (·.2))[d - 2]? = some q := by rw [List.getElem?_map]; exact hq
    rw [hL, List.getElem?_append_right (by omega)] at hz
    have : d - 2 - B.length = ext.length - 2 := by omega
    rw [this] at hz
    rw [hz] at hu
    exact (Option.some.inj hu).symm
  rw [huq, hqn] at hn
  cases hn
  simp only [Prod.mk.injEq, Option.some.injEq] at hfe
  exact ⟨cv, fd, hcv, hfd, hfe.1.symm⟩

/-! ## The merge's tail: the parent split in time below a grandparent with room -/

set_option maxHeartbeats 16000000 in
/-- A merge into one node whose parent p goes `full` (`¬ MergeParentRoom`) and
splits in time (it compacts, or its last version has at most `splitAbove`
klongs), p not made by the transaction, below its parent q with room for the
copy's klong and no compaction: the hole moves from p to p's copy nx + 2, which
q's klong k1 names instead; the merged nodes and p are left behind; the nodes
below nx but p, q, l and r keep their lookups; the copy has p's entry in the
heights' cache. -/
theorem writerWP_mergeTail_liveFullTime (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (x : NodeId) (d' : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (q : NodeId) (qn : KNode) (k1 : Nat) (hqP : PathLen N c.i root q d') (hNq : N q = some qn)
    (hk : (k1, p) ∈ qn.liveAt c.i) (h3q : w3.nodes.lookup q = some qn)
    (h3pq : (w3.path[d']?).map (·.2) = some q) (h3pk : w3.path[d' + 1]? = some (some k1, p))
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqroom : qn.size + 2 ≤ c.p.M) (hqdead : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hpnew : pn.firstTime ≠ some c.i) (hone : mergeM2 c xn ln rn cR nx = none)
    (hnB : ¬ MergeParentRoom c pn il cL nx ir cR none)
    (htime : ∀ last, mergeFullLast pn c.i cL nx cR none = some last →
      pn.size + mergeParentNeed c.i pn il ir cR none ≤ c.p.M ∨ last.size ≤ c.p.splitAbove)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x (d' + 2) p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => res = 1 ∧
        LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun y => y = nx + 2) ∧
        (∀ y, y ≠ p → y ≠ q → y ≠ l → y ≠ r → y < nx → w'.nodes.lookup y = w3.nodes.lookup y) ∧
        (∃ yn, w'.nodes.lookup (nx + 2) = some yn) ∧
        w'.nodes.lookup q = some (qn.add c.i (.key k1 (nx + 2))) ∧
        w'.gh.lookup (nx + 2) = w3.gh.lookup p ∧
        (∀ y, y ≠ p → y ≠ l → y ≠ r → y < nx → w'.gh.lookup y = w3.gh.lookup y) ∧
        w'.top = w3.top) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hc : cL ≠ cR := Nat.ne_of_lt hclt
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ r := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
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
  -- the sibling of the hole is filled: the two hold m live klongs or more
  have hsib : c.p.mergeBelow ≤ ln.live.length + rn.live.length := by
    have hok : ∀ s sn, N s = some sn → (∃ cs, (cs, s) ∈ pn.liveAt c.i) → s ≠ x →
        c.p.mergeBelow ≤ (sn.liveAt c.i).length := by
      intro s sn hs ⟨cs, hcs⟩ hsx
      exact ((hLive.2 p pn cs s sn hp hpn hcs hs).1 (fun h => hsx (hHl s h))).2.2 hpleaf hm
    rcases hxlr with hx | hx
    · have := hok r rn hrn ⟨cR, hpR⟩ (by rw [hx]; exact hlr.symm)
      rw [KNode.liveAt_of_times rn c.i hrt] at this
      omega
    · have := hok l ln hln ⟨cL, hpL⟩ (by rw [hx]; exact hlr)
      rw [KNode.liveAt_of_times ln c.i hlt] at this
      omega
  have hmb : 2 ≤ c.p.mergeBelow := hMP.1
  -- the grandparent q, one above p
  have hpP : PathLen N c.i root p (d' + 1) := PathLen.link hqP ⟨qn, hNq, hk⟩
  have hqp : q ≠ p := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hpP; omega
  have hlP : PathLen N c.i root l (d' + 2) := PathLen.link hpP hlink_l
  have hrP : PathLen N c.i root r (d' + 2) := PathLen.link hpP hlink_r
  have hql : q ≠ l := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hlP; omega
  have hqr : q ≠ r := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hrP; omega
  have hqnx := hlt_nx q qn hNq
  have hqT : w3.taken.contains q = false := by
    have := hN3 ▸ hNq
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
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
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have hElen : (mergeList (!xn.leaf) cR ln.live rn.live).length = ln.live.length + rn.live.length :=
    by simpa using congrArg List.length (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
  -- the new nodes: their klongs name children of l or r, and they are filled
  have hsrcE : ∀ z, z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro z hz
    rw [mergeList_map_snd] at hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact hq'⟩
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact hq'⟩
  have hnewT : ∀ ks : List (Nat × NodeId), ∀ s, Klong.time s ∈
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).ks → s ≤ c.i := by
    intro ks s hs
    simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.mem_map, reduceCtorEq, and_false,
      exists_false, or_false] at hs
    omega
  have hnewSrc : ∀ ks : List (Nat × NodeId), (∀ z, z ∈ ks.map Prod.snd →
      z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd) → ∀ cc z,
      (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro ks hks cc z hmem
    have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks cc z hmem
    exact hsrcE z (hks z (List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩))
  have hnewFill : ∀ ks : List (Nat × NodeId), CvSorted ks → c.p.mergeBelow ≤ ks.length →
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i ≠ [] ∧
      c.p.mergeBelow ≤ (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length := by
    intro ks hks hlen
    have hcnt : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length =
        ks.length := by
      rw [KNode.liveAt_of_times _ c.i (hnewT ks)]
      exact newKlongs_cnt_of_sorted _ _ _ hks
    refine ⟨fun h0 => ?_, by rw [hcnt]; exact hlen⟩
    have : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length = 0 := by
      rw [h0]; rfl
    omega
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_and (writerWP_ghOf_reads x c _ base hvc) (writerWP_ghOf_ghL x c _))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4, h4gh⟩
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, nx ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hxnx : x < nx := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hcl' : ∀ y, y ≠ l → y ≠ r → ∀ q ∈ [(l, lMade), (r, rMade)], y ≠ (q : NodeId × Bool).1 := by
    intro y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ q ∈ [(l, lMade), (r, rMade)], (q : NodeId × Bool).1 ≠ p := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  have hlr' : ∀ (q : NodeId × Bool), q ∈ [(l, lMade), (r, rMade)] → q.1 = l ∨ q.1 = r := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
    intro z hz cc hmem h1 h2
    rcases hz with hz | hz
    · rw [hz] at hmem
      exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hmem⟩ hlink_l).2
    · rw [hz] at hmem
      exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hmem⟩ hlink_r).2
  have hmpT : ∀ il' cL' m1' ir' cR' m2', ∀ s, Klong.time s ∈
      (mergeParentNode pn c.i il' cL' m1' ir' cR' m2').ks → s ≤ c.i := by
    intro il' cL' m1' ir' cR' m2'
    rw [mergeParentNode_eq]
    exact mpNode_times pn c.i _ _ _ _ _ _ _ _ _ (htd_last pn _) hpt
  try dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
      (writerWP_newKey_ghL _ _ _ _ c _)) ?_
    intro m1 w5 ⟨⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩, h5gh⟩
    refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
      (writerWP_setMadeFor_gh _ _ c _)) ?_
    intro _ w6 ⟨⟨h6n, h6t, h6top, h6next, h6v, h6p⟩, h6gh⟩
    try dsimp only at hm1 h5n h5t h5top h5next h5v h5p h5m
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, h4n, h3next, lookup_append_single_self]
      rw [hlk4 _ (by omega)]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym, hlk4 y hyx]
    have h6next' : w6.next = m1 + 2 := by rw [h6next, h5next, h4n, h3next]
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hm1R : ¬ TReach N c.i root m1 :=
      not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    have hqx : q ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hqm1 : q ≠ m1 := by omega
    have h6path : w6.path = w3.path := by rw [h6p, h5p, h4p]
    have hw6N : ∀ y, y ≠ m1 → wNode c.p base w6 y = N y := by
      intro y hym
      have : wNode c.p base w6 y = wNode c.p base w4 y := by
        simp only [wNode, h6t, h5t, h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym]
      rw [this, hr4.1]; exact congrFun hN3 y
    have hw6q : w6.nodes.lookup q = some qn := by rw [h6old q hqx hqm1, h3q]
    cases hsec : second with
    | some ksg =>
      exfalso
      have h1 : mergeM2 c xn ln rn cR m1 = none := hone
      simp [mergeM2, hmk, hsec] at h1
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mergeParent_fullB p pn (d' + 1) il cL m1 ir cR none c w6 _ hw6p hnB ?_
      intro last compact s7 hlast hcomp
      obtain ⟨hlastT, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hcLm1 : (cL, m1) ∈ last.liveAt c.i := by
        rw [KNode.liveAt_of_times last c.i hlastT]
        apply bk_mem_of_lookup
        rw [(mergeFullLast_lookup pn c.i cL m1 cR none last hlast).2.1 rfl cL]
        simp
      -- the tree with p's node replaced by its last version
      have hVp : updN (wNode c.p base w6) p last p = some last := updN_self _ _ _
      have hVm1 : updN (wNode c.p base w6) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
        simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
      have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
        intro y hyp hym
        rw [updN_ne _ _ _ _ hyp, hw6N y hym]
      have hmn : ∀ cc z, (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i →
          (cc, z) ∈ mergeList (!xn.leaf) cR ln.live rn.live := by
        intro cc z hm'
        have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm'
        rw [hfirst] at this; exact this
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [hfirst] at hz; exact hz
      have hTV : TreeOK (updN (wNode c.p base w6) p last) c.i root :=
        treeOK_mergeOneAfter N _ c.i root p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩
          (!xn.leaf) cL cR hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
          hVm1 hmn hVp (hnoneL rfl) (fun y hyp _ _ hym => hVN y hyp hym)
      have hVreach := mergeV_reach N (updN (wNode c.p base w6) p last) c.i root p l r m1 none pn ln rn
        last cL cR hT hp hpn hpL hpR hln hrn hVp
        (fun cc z hm' => by
          rcases hnoneL rfl cc z hm' with ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h))
        (fun m mn hm' hmn' cc z hz => by
          rcases hm' with hm' | hm'
          · rw [hm', hVm1] at hmn'
            cases hmn'
            exact hnewSrc first hsrc1 cc z hz
          · cases hm')
        (fun y hyp _ _ hym _ => hVN y hyp hym) hm1R (fun m hm' => by cases hm')
      have hqRV : TReach (updN (wNode c.p base w6) p last) c.i root q := by
        refine (tReach_of_pathLen_agree N _ c.i root q d' hqP (fun u j hu hj => ?_)).reach
        have hup : u ≠ p := by
          intro he; rw [he] at hu; have := PathLen.depth_unique hT _ _ _ hu hpP; omega
        have hum : u ≠ m1 := fun he => hm1R (he ▸ hu.reach)
        exact hVN u hup hum
      have hVq : updN (wNode c.p base w6) p last q = some qn := by rw [hVN q hqp hqm1, hNq]
      have hy0 : m1 + 2 ≠ m1 := by omega
      have hfreshV : ∀ u c', TReach (updN (wNode c.p base w6) p last) c.i root u →
          ¬ TLink (updN (wNode c.p base w6) p last) c.i u c' (m1 + 2) := by
        intro u c' hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hnoneL rfl c' (m1 + 2) hc' with ⟨_, h⟩ | ⟨h, _, _⟩
          · exact hy0 h
          · exact hfreshT (m1 + 2) (by omega) p c' hp ⟨pn, hpn, h⟩
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' (m1 + 2) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · exact hfreshT (m1 + 2) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
            · exact hfreshT (m1 + 2) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
          · rcases hu1 with hu1 | hu1 | hu1
            · rw [hVN u hup hum] at hun
              exact hfreshT (m1 + 2) (by omega) u c' hu1 ⟨un, hun, hc'⟩
            · exact hum hu1
            · cases hu1
      have hLV : LiveEdgesH c.p (updN (wNode c.p base w6) p last) c.i root (fun z => z = p) := by
        have hfirstS : CvSorted first := by rw [hfirst]; exact hsortE
        have hmlen : first.length = ln.live.length + rn.live.length := by rw [hfirst, hElen]
        obtain ⟨hmne, hmfill⟩ := hnewFill first hfirstS (by rw [hmlen]; exact hsib)
        refine liveEdgesH_mergeOne c.p N _ c.i root p l r m1 pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ cL cR Hl hT hp hpn hpleaf hpL hpR hln hrn hm1R hVm1
          (hnewSrc first hsrc1) (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
          (by rw [hrl, hll]) hmne hmfill hVp hleafl (hnoneL rfl) (fun h0 => by rw [h0] at hcLm1; cases hcLm1)
          (fun y hyp hyl hyr hym => hVN y hyp hym)
          (fun y hy => by
            have hyx := hHl y hy
            rcases hxlr with h | h
            · exact Or.inl (hyx.trans h)
            · exact Or.inr (hyx.trans h))
          hLive
      have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
        rcases htime last hlast with h | h
        · rw [hcomp, decide_eq_true h]; rfl
        · have h' : ¬ (last.size > c.p.splitAbove) := by omega
          simp [h']
      unfold handleFull
      show WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) p [] last compact)
        c ({ w6 with trail := s7 :: w6.trail } : W) _
      rw [← hlasteq] at hTV hqRV hfreshV hLV hVq
      have hnx6 : w6.next = m1 + 2 := h6next'
      refine writerWP_mono (writerWP_handleFull_timeRoom_liveGh d' p q pn qn k1 last compact c base
        ({ w6 with trail := s7 :: w6.trail } : W) hw6p (by show w6.taken.contains p = false; rw [h6taken]; exact hpT)
        hw6q (by show w6.taken.contains q = false; rw [h6taken]; exact hqT) hqp
        (by show p < w6.next; omega) (by show q < w6.next; omega) hpnew hcs
        (by show (w6.path[d']?).map (·.2) = some q; rw [h6path]; exact h3pq)
        (by show w6.path[d' + 1]? = some (some k1, p); rw [h6path]; exact h3pk)
        hqwf hqtm hqroom (hqdead _) hk (by show TreeOK _ c.i w6.top.rootKey; rw [h6top']; exact hTV)
        (by show TReach _ c.i w6.top.rootKey q; rw [h6top']; exact hqRV)
        (by show wNode c.p base w6 w6.next = none; rw [hnx6, hw6N (m1 + 2) hy0]; exact (hfree _ (by omega)).1)
        (by show w6.nodes.lookup w6.next = none
            rw [hnx6, h6old (m1 + 2) (by omega) hy0]; exact hnone3 _ (by omega))
        (by show w6.taken.contains w6.next = false; rw [hnx6, h6taken]; exact (hfree _ (by omega)).2)
        (by show ∀ u c', TReach _ c.i w6.top.rootKey u → ¬ TLink _ c.i u c' w6.next
            rw [h6top', hnx6]; exact hfreshV)
        (by show LiveEdgesH c.p _ c.i w6.top.rootKey (fun z => z = p); rw [h6top']; exact hLV)) ?_
      rintro _ w8 ⟨hL8, h8l, h8y, h8q, h8t, h8top, h8path, h8next, h8gy, h8gh⟩
      change w8.nodes.lookup w6.next = _ at h8y
      change w8.nodes.lookup q = some (qn.add c.i (.key k1 w6.next)) at h8q
      change w8.gh.lookup w6.next = w6.gh.lookup p at h8gy
      change ∀ u, u ≠ w6.next → w8.gh.lookup u = w6.gh.lookup u at h8gh
      change w8.taken = w6.taken at h8t
      change w8.top = w6.top at h8top
      change ∀ z, z ≠ q → z ≠ p → z ≠ w6.next → w8.nodes.lookup z = w6.nodes.lookup z at h8l
      change LiveEdgesH c.p (wNode c.p base w8) c.i w8.top.rootKey (fun z => z = w6.next) at hL8
      rw [hnx6] at h8y h8q h8gy h8l hL8 h8gh
      have h8pT : w8.taken.contains p = false := by rw [h8t, h6taken]; exact hpT
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_wNode p m1 c base hvc _ w8 hne' h8pT)
        (writerWP_mergeCleanup_frameL p m1 c _ w8)) ?_
      rintro _ w9 ⟨⟨h9top, _, _, _, h9w, _, _⟩, h9top', _, h9fr⟩
      have h8yT : w8.taken.contains (m1 + 2) = false := by rw [h8t, h6taken]; exact (hfree _ (by omega)).2
      have h8qT : w8.taken.contains q = false := by rw [h8t, h6taken]; exact hqT
      have hN8y : wNode c.p base w8 (m1 + 2) = some ⟨pn.leaf, last.ks⟩ := by
        simp only [wNode, h8yT, Bool.false_eq_true, ↓reduceIte, h8y]
      have hN8q : wNode c.p base w8 q = some (qn.add c.i (.key k1 (m1 + 2))) := by
        simp only [wNode, h8qT, Bool.false_eq_true, ↓reduceIte, h8q]
      have hN8 : ∀ z, z ≠ q → z ≠ p → z ≠ m1 + 2 →
          wNode c.p base w8 z = updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩ z := by
        intro z hzq hzp hzy
        rw [updN_ne _ _ _ _ hzp]
        simp only [wNode, h8t, h8l z hzq hzp hzy]
      have hat := KNode.add_times qn c.i (.key k1 (m1 + 2)) (fun s h => by cases h) hqtm
      have hq' : ∀ c' z, (c', z) ∈ (qn.add c.i (.key k1 (m1 + 2))).liveAt c.i →
          (c' = k1 ∧ z = m1 + 2) ∨ ((c', z) ∈ qn.liveAt c.i ∧ c' ≠ k1) := by
        intro c' z hmm
        rw [KNode.liveAt_of_times _ c.i hat] at hmm
        have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
        rw [KNode.add_key_live_lookup_of_wf qn c.i k1 c' (m1 + 2) hqwf] at hlk'
        by_cases hck : k1 = c'
        · subst hck; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
        · have hb : (k1 == c') = false := by simpa using hck
          rw [hb] at hlk'
          simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
          refine Or.inr ⟨?_, Ne.symm hck⟩
          rw [KNode.liveAt_of_times qn c.i hqtm]
          exact bk_mem_of_lookup _ c' z hlk'
      have hVp' : updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩ p = some ⟨pn.leaf, last.ks⟩ :=
        updN_self _ _ _
      have hyV : updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩ (m1 + 2) = none := by
        rw [updN_ne _ _ _ _ (by omega), hw6N (m1 + 2) hy0]; exact (hfree _ (by omega)).1
      have h8top' : w8.top.rootKey = root := by rw [h8top, h6top']
      have hR8 := redirect_reach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) (wNode c.p base w8)
        c.i root q p (m1 + 2) qn _ _ k1 hTV hqRV hVq hk hVp' hyV hfreshV hN8y hN8q hq' hN8
      rw [hlasteq] at hR8
      have hnot : ∀ z, TReach (wNode c.p base w8) c.i root z → z ≠ p ∧ z ≠ l ∧ z ≠ r := by
        intro z hz
        rcases hR8 z hz with ⟨hzV, hzp, _⟩ | hzy
        · obtain ⟨_, hzl, hzr⟩ := hVreach z hzV
          exact ⟨hzp, hzl, hzr⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
      have h9top0 : w9.top = w3.top := by rw [h9top, h8top, h6top, h5top, h4top]
      have hfr9 : ∀ y, y ≠ p → y ≠ l → y ≠ r →
          w9.gh.lookup y = w8.gh.lookup y ∧ w9.nodes.lookup y = w8.nodes.lookup y :=
        fun y hyp hyl hyr => h9fr y hyp (hcl' y hyl hyr)
      refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, h9top0⟩
      · rw [h9top, h8top']
        refine liveEdgesH_congr_reach c.p (wNode c.p base w8) _ c.i root _ (by rw [← h8top']; exact hL8) ?_
        intro z hz
        obtain ⟨hzp, hzl, hzr⟩ := hnot z hz
        exact h9w z hzp (hcl' z hzl hzr)
      · intro y hyp hyq hyl hyr hylt
        rw [(hfr9 y hyp hyl hyr).2, h8l y hyq hyp (by omega),
          h6old y (by rcases hxlr with h | h <;> rw [h] <;> omega) (by omega)]
      · exact ⟨_, by rw [(hfr9 (m1 + 2) (by omega) (by omega) (by omega)).2, h8y]⟩
      · rw [(hfr9 q hqp hql hqr).2, h8q]
      · rw [(hfr9 (m1 + 2) (by omega) (by omega) (by omega)).1, h8gy, h6gh, h5gh p hpm1,
          h4gh p hpx]
      · intro y hyp hyl hyr hylt
        rw [(hfr9 y hyp hyl hyr).1, h8gh y (by omega), h6gh, h5gh y (by omega),
          h4gh y (by rcases hxlr with h | h <;> rw [h] <;> omega)]

set_option maxHeartbeats 16000000 in
/-- `writerWP_mergeTail_liveFullTime` for a merge into two nodes: no hole before
the split (`liveEdges_mergeTwo`), and p's copy is filled as p was, so no hole
after it. -/
theorem writerWP_mergeTail_liveFullTime2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (x : NodeId) (d' : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (Hl : NodeId → Prop) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hclt : cL < cR) (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (q : NodeId) (qn : KNode) (k1 : Nat) (hqP : PathLen N c.i root q d') (hNq : N q = some qn)
    (hk : (k1, p) ∈ qn.liveAt c.i) (hqleaf : qn.leaf = false) (h3q : w3.nodes.lookup q = some qn)
    (h3pq : (w3.path[d']?).map (·.2) = some q) (h3pk : w3.path[d' + 1]? = some (some k1, p))
    (hqwf : klongsWf qn.ks = true) (hqtm : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (hqroom : qn.size + 2 ≤ c.p.M) (hqdead : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hpnew : pn.firstTime ≠ some c.i) (htwo : (mergeM2 c xn ln rn cR nx).isSome = true)
    (hnB : ¬ MergeParentRoom c pn il cL nx ir cR (mergeM2 c xn ln rn cR nx))
    (htime : ∀ last, mergeFullLast pn c.i cL nx cR (mergeM2 c xn ln rn cR nx) = some last →
      pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR nx) ≤ c.p.M ∨
        last.size ≤ c.p.splitAbove)
    (hLive : LiveEdgesH c.p N c.i root Hl) (hHl : ∀ y, Hl y → y = x) :
    WriterWP (mergeTail c x (d' + 2) p pn xn leftSome l ln il r rn ir) c w3
      (fun res w' => res = 2 ∧ LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hc : cL ≠ cR := Nat.ne_of_lt hclt
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hlr : l ≠ r := fun h => hc (hT.oneLink p cL p cR l hp hp hlink_l (by rw [h]; exact hlink_r)).2
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
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
  -- the sibling of the hole is filled: the two hold m live klongs or more
  have hsib : c.p.mergeBelow ≤ ln.live.length + rn.live.length := by
    have hok : ∀ s sn, N s = some sn → (∃ cs, (cs, s) ∈ pn.liveAt c.i) → s ≠ x →
        c.p.mergeBelow ≤ (sn.liveAt c.i).length := by
      intro s sn hs ⟨cs, hcs⟩ hsx
      exact ((hLive.2 p pn cs s sn hp hpn hcs hs).1 (fun h => hsx (hHl s h))).2.2 hpleaf hm
    rcases hxlr with hx | hx
    · have := hok r rn hrn ⟨cR, hpR⟩ (by rw [hx]; exact hlr.symm)
      rw [KNode.liveAt_of_times rn c.i hrt] at this
      omega
    · have := hok l ln hln ⟨cL, hpL⟩ (by rw [hx]; exact hlr)
      rw [KNode.liveAt_of_times ln c.i hlt] at this
      omega
  have hmb : 2 ≤ c.p.mergeBelow := hMP.1
  -- the grandparent q, one above p
  have hpP : PathLen N c.i root p (d' + 1) := PathLen.link hqP ⟨qn, hNq, hk⟩
  have hqp : q ≠ p := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hpP; omega
  have hlP : PathLen N c.i root l (d' + 2) := PathLen.link hpP hlink_l
  have hrP : PathLen N c.i root r (d' + 2) := PathLen.link hpP hlink_r
  have hql : q ≠ l := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hlP; omega
  have hqr : q ≠ r := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hT _ _ _ hqP hrP; omega
  have hqnx := hlt_nx q qn hNq
  have hqT : w3.taken.contains q = false := by
    have := hN3 ▸ hNq
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
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
  have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
      (first, second) := hmk
  have hElen : (mergeList (!xn.leaf) cR ln.live rn.live).length = ln.live.length + rn.live.length :=
    by simpa using congrArg List.length (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
  -- the new nodes: their klongs name children of l or r, and they are filled
  have hsrcE : ∀ z, z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro z hz
    rw [mergeList_map_snd] at hz
    rcases List.mem_append.mp hz with h | h
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact hq'⟩
    · obtain ⟨q', hq', he⟩ := List.mem_map.mp h
      exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact hq'⟩
  have hnewT : ∀ ks : List (Nat × NodeId), ∀ s, Klong.time s ∈
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).ks → s ≤ c.i := by
    intro ks s hs
    simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.mem_map, reduceCtorEq, and_false,
      exists_false, or_false] at hs
    omega
  have hnewSrc : ∀ ks : List (Nat × NodeId), (∀ z, z ∈ ks.map Prod.snd →
      z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd) → ∀ cc z,
      (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i →
      (∃ c0, (c0, z) ∈ ln.liveAt c.i) ∨ (∃ c0, (c0, z) ∈ rn.liveAt c.i) := by
    intro ks hks cc z hmem
    have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks cc z hmem
    exact hsrcE z (hks z (List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩))
  have hnewFill : ∀ ks : List (Nat × NodeId), CvSorted ks → c.p.mergeBelow ≤ ks.length →
      ({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i ≠ [] ∧
      c.p.mergeBelow ≤ (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length := by
    intro ks hks hlen
    have hcnt : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length =
        ks.length := by
      rw [KNode.liveAt_of_times _ c.i (hnewT ks)]
      exact newKlongs_cnt_of_sorted _ _ _ hks
    refine ⟨fun h0 => ?_, by rw [hcnt]; exact hlen⟩
    have : (({ leaf := !!xn.leaf, ks := newKlongs c.i ks } : KNode).liveAt c.i).length = 0 := by
      rw [h0]; rfl
    omega
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_and (writerWP_ghOf_reads x c _ base hvc) (writerWP_ghOf_ghL x c _))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4, h4gh⟩
  have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
  have hnone3 : ∀ z, nx ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := h3src z (by rw [h']; rfl); omega
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hxnx : x < nx := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpT : w3.taken.contains p = false := by
    have := hN3 ▸ hpn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
  have hcl' : ∀ y, y ≠ l → y ≠ r → ∀ q ∈ [(l, lMade), (r, rMade)], y ≠ (q : NodeId × Bool).1 := by
    intro y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ q ∈ [(l, lMade), (r, rMade)], (q : NodeId × Bool).1 ≠ p := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  have hlr' : ∀ (q : NodeId × Bool), q ∈ [(l, lMade), (r, rMade)] → q.1 = l ∨ q.1 = r := by
    intro q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
    intro z hz cc hmem h1 h2
    rcases hz with hz | hz
    · rw [hz] at hmem
      exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hmem⟩ hlink_l).2
    · rw [hz] at hmem
      exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hmem⟩ hlink_r).2
  have hmpT : ∀ il' cL' m1' ir' cR' m2', ∀ s, Klong.time s ∈
      (mergeParentNode pn c.i il' cL' m1' ir' cR' m2').ks → s ≤ c.i := by
    intro il' cL' m1' ir' cR' m2'
    rw [mergeParentNode_eq]
    exact mpNode_times pn c.i _ _ _ _ _ _ _ _ _ (htd_last pn _) hpt
  try dsimp only
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
      (writerWP_newKey_ghL _ _ _ _ c _)) ?_
    intro m1 w5 ⟨⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩, h5gh⟩
    refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
      (writerWP_setMadeFor_gh _ _ c _)) ?_
    intro _ w6 ⟨⟨h6n, h6t, h6top, h6next, h6v, h6p⟩, h6gh⟩
    try dsimp only at hm1 h5n h5t h5top h5next h5v h5p h5m
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, h4n, h3next, lookup_append_single_self]
      rw [hlk4 _ (by omega)]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym, hlk4 y hyx]
    have h6next' : w6.next = m1 + 2 := by rw [h6next, h5next, h4n, h3next]
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hm1R : ¬ TReach N c.i root m1 :=
      not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    have hqx : q ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hqm1 : q ≠ m1 := by omega
    have h6path : w6.path = w3.path := by rw [h6p, h5p, h4p]
    have hw6N : ∀ y, y ≠ m1 → wNode c.p base w6 y = N y := by
      intro y hym
      have : wNode c.p base w6 y = wNode c.p base w4 y := by
        simp only [wNode, h6t, h5t, h6n, h5n, h4n, h3next, lookup_append_single_ne _ _ _ _ hym]
      rw [this, hr4.1]; exact congrFun hN3 y
    have hw6q : w6.nodes.lookup q = some qn := by rw [h6old q hqx hqm1, h3q]
    cases hsec : second with
    | none =>
      exfalso
      have h1 : (mergeM2 c xn ln rn cR m1).isSome = true := htwo
      simp [mergeM2, hmk, hsec] at h1
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hcap : 1 ≤ c.p.mergeMax := by have := hMP.1; have := hMP.2.1; omega
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElt : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
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
      obtain ⟨hgL, _, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hg2 : g2 ≠ cR → pn.live.lookup g2 = none := by
        intro hne
        cases hlg : pn.live.lookup g2 with
        | none => rfl
        | some z =>
          exfalso
          have hm : (g2, z) ∈ pn.liveAt c.i := by
            rw [KNode.liveAt_of_times pn c.i hpt]; exact bk_mem_of_lookup _ _ _ hlg
          rcases hadj g2 z hm with h1 | h1
          · omega
          · have hgt : cR < g2 := by omega
            have := hgU0 g2 hgt (fun q hq => hrup g2 z hm hgt q.1 q.2 (by
              rw [KNode.liveAt_of_times rn c.i hrt]; exact hq))
            omega
      -- the halves: sorted, filled, naming children of l or r
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hS1 : CvSorted first := by rw [hE1]; exact hsortE.sublist (List.take_sublist _ _)
      have hS2 : CvSorted ks2 := by
        rw [hE2]
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
      have hlen1 : first.length = ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE1, List.length_take]; omega
      have hlen2 : ks2.length = (mergeList (!xn.leaf) cR ln.live rn.live).length -
          ((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2 := by
        rw [hE2]
        split <;> simp [renameHead_length, List.length_drop]
      have hmb2 := hMP.2.1
      obtain ⟨hmne1, hmfill1⟩ := hnewFill first hS1 (by omega)
      obtain ⟨hmne2, hmfill2⟩ := hnewFill ks2 hS2 (by omega)
      have hsnd := splitMerged_map_snd (!xn.leaf) c.p.mergeMax _ first ks2 g2 hmkd
      have hsrc1 : ∀ z, z ∈ first.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_left _ hz
      have hsrc2 : ∀ z, z ∈ ks2.map Prod.snd →
          z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        intro z hz; rw [← hsnd, List.map_append]; exact List.mem_append_right _ hz
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mono (writerWP_and (writerWP_newKey_frame _ _ _ _ c _)
        (writerWP_newKey_ghL _ _ _ _ c _)) ?_
      intro m2 w7 ⟨⟨hm2, h7n, h7t, h7top, h7next, h7v, h7p, h7m⟩, h7gh⟩
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_and (writerWP_setMadeFor_frame _ _ c _)
        (writerWP_setMadeFor_gh _ _ c _)) ?_
      intro _ w8 ⟨⟨h8n, h8t, h8top, h8next, h8v, h8p⟩, h8gh0⟩
      try simp only [writerWP_pure]
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next']
      subst hm2'
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6p]
      have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [h8n, h7n, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        rw [h8n, h7n, h6next', lookup_append_single_self]
        rw [h6old _ (by omega) (by omega)]
        exact hnone3 _ (by omega)
      have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
        intro y hyx hym hym2
        rw [h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
      have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree (m1 + 2) (by omega)).2
      have hm2N : N (m1 + 2) = none := (hfree (m1 + 2) (by omega)).1
      have hm2R : ¬ TReach N c.i root (m1 + 2) :=
        not_reach_fresh N c.i root (m1 + 2) hT hm2N (hfreshT (m1 + 2) (by omega))
      have hlm2 : l ≠ m1 + 2 := by omega
      have hrm2 : r ≠ m1 + 2 := by omega
      have hpm2 : p ≠ m1 + 2 := by omega
      have hm2eq : mergeM2 c xn ln rn cR m1 = some (m1 + 2, g2) := by
        simp [mergeM2, hmk, hsec]
      rw [hm2eq] at hnB htime
      have h8path : w8.path = w3.path := by rw [h8p, h7p, h6path]
      have hw8N : ∀ y, y ≠ m1 → y ≠ m1 + 2 → wNode c.p base w8 y = N y := by
        intro y hym hym2
        have : wNode c.p base w8 y = wNode c.p base w6 y := by
          simp only [wNode, h8t, h7t, h8n, h7n, h6next', lookup_append_single_ne _ _ _ _ hym2]
        rw [this, hw6N y hym]
      have hw8q : w8.nodes.lookup q = some qn := by rw [h8old q hqx hqm1 (by omega), h3q]
      have h8next' : w8.next = m1 + 4 := by rw [h8next, h7next, h6next']
      have h8top' : w8.top.rootKey = root := by rw [h8top, h7top, h6top']
      refine writerWP_mergeParent_fullB p pn (d' + 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p hnB ?_
      intro last compact s9 hlast hcomp
      obtain ⟨hlastT, hleafl, _, hsomeL⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
      have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
        cases last with
        | mk lf ks => simp only at hleafl; rw [hleafl]
      have hlk2 := (mergeFullLast_lookup pn c.i cL m1 cR _ last hlast).2.2 (m1 + 2) g2 rfl
      have hlen9 : pn.live.length ≤ last.live.length :=
        live_len_mergeTwo pn last cL cR g2 m1 (m1 + 2) hlk2 (by omega)
          ⟨r, by rw [KNode.live_lookup]; exact keyLookup_of_last _ _ _ ir r hR hRL⟩ hg2
      have hlen10 : (pn.liveAt c.i).length ≤ (last.liveAt c.i).length := by
        rw [KNode.liveAt_of_times pn c.i hpt, KNode.liveAt_of_times last c.i hlastT]; exact hlen9
      have hVp : updN (wNode c.p base w8) p last p = some last := updN_self _ _ _
      have hVm1 : updN (wNode c.p base w8) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
        simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
      have hVm2 : updN (wNode c.p base w8) p last (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        rw [updN_ne _ _ _ _ (by omega)]
        simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
      have hVN : ∀ y, y ≠ p → y ≠ m1 → y ≠ m1 + 2 → updN (wNode c.p base w8) p last y = N y := by
        intro y hyp hym hym2
        rw [updN_ne _ _ _ _ hyp, hw8N y hym hym2]
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [hsnd, mergeList_map_snd, List.map_append]
      have hTV : TreeOK (updN (wNode c.p base w8) p last) c.i root :=
        treeOK_mergeTwoAfter N _ c.i root p l r m1 (m1 + 2) pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
          hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
          hm2N (hfreshT _ (by omega)) (by omega) hE hVm1
          (fun cc z hm' => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm') hVm2
          (fun cc z hm' => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm') hVp
          (hsomeL (m1 + 2) g2 rfl) (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2)
      have hVreach := mergeV_reach N (updN (wNode c.p base w8) p last) c.i root p l r m1 (some (m1 + 2))
        pn ln rn last cL cR hT hp hpn hpL hpR hln hrn hVp
        (fun cc z hm' => by
          rcases hsomeL (m1 + 2) g2 rfl cc z hm' with ⟨_, h⟩ | ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inl (by rw [h]))
          · exact Or.inr (Or.inr h))
        (fun m mn hm' hmn' cc z hz => by
          rcases hm' with hm' | hm'
          · rw [hm', hVm1] at hmn'
            cases hmn'
            exact hnewSrc first hsrc1 cc z hz
          · simp only [Option.some.injEq] at hm'
            rw [hm', hVm2] at hmn'
            cases hmn'
            exact hnewSrc ks2 hsrc2 cc z hz)
        (fun y hyp _ _ hym hym2 => hVN y hyp hym (fun h => hym2 (by rw [h])))
        hm1R (fun m hm' => by
          simp only [Option.some.injEq] at hm'
          rw [hm']; exact hm2R)
      have hqRV : TReach (updN (wNode c.p base w8) p last) c.i root q := by
        refine (tReach_of_pathLen_agree N _ c.i root q d' hqP (fun u j hu hj => ?_)).reach
        have hup : u ≠ p := by
          intro he; rw [he] at hu; have := PathLen.depth_unique hT _ _ _ hu hpP; omega
        have hum : u ≠ m1 := fun he => hm1R (he ▸ hu.reach)
        have hum2 : u ≠ m1 + 2 := fun he => hm2R (he ▸ hu.reach)
        exact hVN u hup hum hum2
      have hVq : updN (wNode c.p base w8) p last q = some qn := by
        rw [hVN q hqp hqm1 (by omega), hNq]
      have hfreshV : ∀ u c', TReach (updN (wNode c.p base w8) p last) c.i root u →
          ¬ TLink (updN (wNode c.p base w8) p last) c.i u c' (m1 + 4) := by
        intro u c' hu ⟨un, hun, hc'⟩
        obtain ⟨hu1, _, _⟩ := hVreach u hu
        by_cases hup : u = p
        · rw [hup, hVp] at hun; cases hun
          rcases hsomeL (m1 + 2) g2 rfl c' (m1 + 4) hc' with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
          · omega
          · omega
          · exact hfreshT (m1 + 4) (by omega) p c' hp ⟨pn, hpn, h⟩
        · by_cases hum : u = m1
          · rw [hum, hVm1] at hun; cases hun
            rcases hnewSrc first hsrc1 c' (m1 + 4) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
            · exact hfreshT (m1 + 4) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
            · exact hfreshT (m1 + 4) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
          · by_cases hum2 : u = m1 + 2
            · rw [hum2, hVm2] at hun; cases hun
              rcases hnewSrc ks2 hsrc2 c' (m1 + 4) hc' with ⟨c0, h⟩ | ⟨c0, h⟩
              · exact hfreshT (m1 + 4) (by omega) l c0 (TReach.link hp hlink_l) ⟨ln, hln, h⟩
              · exact hfreshT (m1 + 4) (by omega) r c0 (TReach.link hp hlink_r) ⟨rn, hrn, h⟩
            · rcases hu1 with hu1 | hu1 | hu1
              · rw [hVN u hup hum hum2] at hun
                exact hfreshT (m1 + 4) (by omega) u c' hu1 ⟨un, hun, hc'⟩
              · exact hum hu1
              · exact hum2 (Option.some.inj hu1)
      have hLE : LiveEdges c.p (updN (wNode c.p base w8) p last) c.i root :=
        liveEdges_mergeTwo c.p N _ c.i root p l r m1 (m1 + 2) pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR Hl hT hp hpn hpleaf
          hpL hpR hln hrn hm1R hm2R hVm1 hVm2
          (fun mn hmn cc z hmem => by
            rcases hmn with h | h <;> subst h
            · exact hnewSrc first hsrc1 cc z hmem
            · exact hnewSrc ks2 hsrc2 cc z hmem)
          (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not])
          (by show (!!xn.leaf) = ln.leaf; rw [hll, Bool.not_not]) (by rw [hrl, hll])
          ⟨hmne1, hmne2⟩ ⟨hmfill1, hmfill2⟩ hVp hleafl
          (fun cc z hm' => by
            rcases hsomeL (m1 + 2) g2 rfl cc z hm' with ⟨_, h⟩ | ⟨_, h⟩ | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr h))
          hlen10 (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2)
          (fun y hy => by
            have hyx := hHl y hy
            rcases hxlr with h | h
            · exact Or.inl (hyx.trans h)
            · exact Or.inr (hyx.trans h))
          hLive
      have hLV := liveEdgesH_of_liveEdges c.p _ c.i root (fun z => z = p) hLE
      have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
        rcases htime last hlast with h | h
        · rw [hcomp, decide_eq_true h]; rfl
        · have h' : ¬ (last.size > c.p.splitAbove) := by omega
          simp [h']
      have hy0 : m1 + 4 ≠ m1 := by omega
      have hy2 : m1 + 4 ≠ m1 + 2 := by omega
      unfold handleFull
      show WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) p [] last compact)
        c ({ w8 with trail := s9 :: w8.trail } : W) _
      rw [← hlasteq] at hTV hqRV hfreshV hLV hVq hVreach
      refine writerWP_mono (writerWP_handleFull_timeRoom_liveGh d' p q pn qn k1 last compact c base
        ({ w8 with trail := s9 :: w8.trail } : W) hw8p (by show w8.taken.contains p = false; rw [h8taken]; exact hpT)
        hw8q (by show w8.taken.contains q = false; rw [h8taken]; exact hqT) hqp
        (by show p < w8.next; omega) (by show q < w8.next; omega) hpnew hcs
        (by show (w8.path[d']?).map (·.2) = some q; rw [h8path]; exact h3pq)
        (by show w8.path[d' + 1]? = some (some k1, p); rw [h8path]; exact h3pk)
        hqwf hqtm hqroom (hqdead _) hk (by show TreeOK _ c.i w8.top.rootKey; rw [h8top']; exact hTV)
        (by show TReach _ c.i w8.top.rootKey q; rw [h8top']; exact hqRV)
        (by show wNode c.p base w8 w8.next = none
            rw [h8next', hw8N (m1 + 4) hy0 hy2]; exact (hfree _ (by omega)).1)
        (by show w8.nodes.lookup w8.next = none
            rw [h8next', h8old (m1 + 4) (by omega) hy0 hy2]; exact hnone3 _ (by omega))
        (by show w8.taken.contains w8.next = false; rw [h8next', h8taken]; exact (hfree _ (by omega)).2)
        (by show ∀ u c', TReach _ c.i w8.top.rootKey u → ¬ TLink _ c.i u c' w8.next
            rw [h8top', h8next']; exact hfreshV)
        (by show LiveEdgesH c.p _ c.i w8.top.rootKey (fun z => z = p); rw [h8top']; exact hLV)) ?_
      rintro _ w10 ⟨hL10, h10l, h10y, h10q, h10t, h10top, _, _, _, _⟩
      change w10.nodes.lookup w8.next = _ at h10y
      change w10.nodes.lookup q = some (qn.add c.i (.key k1 w8.next)) at h10q
      change w10.taken = w8.taken at h10t
      change w10.top = w8.top at h10top
      change ∀ z, z ≠ q → z ≠ p → z ≠ w8.next → w10.nodes.lookup z = w8.nodes.lookup z at h10l
      change LiveEdgesH c.p (wNode c.p base w10) c.i w10.top.rootKey (fun z => z = w8.next) at hL10
      rw [h8next'] at h10y h10q h10l hL10
      have h10pT : w10.taken.contains p = false := by rw [h10t, h8taken]; exact hpT
      refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w10 hne' h10pT) ?_
      rintro _ w11 ⟨h11top, _, _, _, h11w, _, _⟩
      have h10yT : w10.taken.contains (m1 + 4) = false := by
        rw [h10t, h8taken]; exact (hfree _ (by omega)).2
      have h10qT : w10.taken.contains q = false := by rw [h10t, h8taken]; exact hqT
      have hN10y : wNode c.p base w10 (m1 + 4) = some ⟨pn.leaf, last.ks⟩ := by
        simp only [wNode, h10yT, Bool.false_eq_true, ↓reduceIte, h10y]
      have hN10q : wNode c.p base w10 q = some (qn.add c.i (.key k1 (m1 + 4))) := by
        simp only [wNode, h10qT, Bool.false_eq_true, ↓reduceIte, h10q]
      have hN10 : ∀ z, z ≠ q → z ≠ p → z ≠ m1 + 4 →
          wNode c.p base w10 z = updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩ z := by
        intro z hzq hzp hzy
        rw [updN_ne _ _ _ _ hzp]
        simp only [wNode, h10t, h10l z hzq hzp hzy]
      have hat := KNode.add_times qn c.i (.key k1 (m1 + 4)) (fun s h => by cases h) hqtm
      have hq' : ∀ c' z, (c', z) ∈ (qn.add c.i (.key k1 (m1 + 4))).liveAt c.i →
          (c' = k1 ∧ z = m1 + 4) ∨ ((c', z) ∈ qn.liveAt c.i ∧ c' ≠ k1) := by
        intro c' z hmm
        rw [KNode.liveAt_of_times _ c.i hat] at hmm
        have hlk' := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c' z hmm
        rw [KNode.add_key_live_lookup_of_wf qn c.i k1 c' (m1 + 4) hqwf] at hlk'
        by_cases hck : k1 = c'
        · subst hck; simp at hlk'; exact Or.inl ⟨rfl, hlk'.symm⟩
        · have hb : (k1 == c') = false := by simpa using hck
          rw [hb] at hlk'
          simp only [Bool.false_eq_true, ↓reduceIte] at hlk'
          refine Or.inr ⟨?_, Ne.symm hck⟩
          rw [KNode.liveAt_of_times qn c.i hqtm]
          exact bk_mem_of_lookup _ c' z hlk'
      have hVp' : updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩ p = some ⟨pn.leaf, last.ks⟩ :=
        updN_self _ _ _
      have hyV : updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩ (m1 + 4) = none := by
        rw [updN_ne _ _ _ _ (by omega), hw8N (m1 + 4) hy0 hy2]; exact (hfree _ (by omega)).1
      have h10top' : w10.top.rootKey = root := by rw [h10top, h8top']
      have hR10 := redirect_reach (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) (wNode c.p base w10)
        c.i root q p (m1 + 4) qn _ _ k1 hTV hqRV hVq hk hVp' hyV hfreshV hN10y hN10q hq' hN10
      have hnot : ∀ z, TReach (wNode c.p base w10) c.i root z → z ≠ p ∧ z ≠ l ∧ z ≠ r := by
        intro z hz
        rcases hR10 z hz with ⟨hzV, hzp, _⟩ | hzy
        · obtain ⟨_, hzl, hzr⟩ := hVreach z hzV
          exact ⟨hzp, hzl, hzr⟩
        · rw [hzy]; exact ⟨by omega, by omega, by omega⟩
      have hag : ∀ z, TReach (wNode c.p base w10) c.i root z → wNode c.p base w11 z = wNode c.p base w10 z := by
        intro z hz
        obtain ⟨hzp, hzl, hzr⟩ := hnot z hz
        exact h11w z hzp (hcl' z hzl hzr)
      have hL11 : LiveEdgesH c.p (wNode c.p base w11) c.i root (fun z => z = m1 + 4) :=
        liveEdgesH_congr_reach c.p (wNode c.p base w10) _ c.i root _ (by rw [← h10top']; exact hL10) hag
      have hR11 : ∀ z, TReach (wNode c.p base w11) c.i root z → TReach (wNode c.p base w10) c.i root z := by
        intro z hz
        induction hz with
        | root => exact TReach.root
        | @link u c0 y _ hl ih =>
          obtain ⟨m, hm', hc0⟩ := hl
          rw [hag u ih] at hm'
          exact TReach.link ih ⟨m, hm', hc0⟩
      -- p was filled under q, and its copy has at least its live klongs
      have hpOK : ChildOK c.p c.i qn pn := by
        refine (hLive.2 q qn k1 p pn hqP.reach hNq hk hpn).1 (fun hHp => ?_)
        have := hHl p hHp
        rcases hxlr with h | h
        · exact hpl (this.trans h)
        · exact hpr (this.trans h)
      have hrootne : root < m1 := by obtain ⟨rn0, hrn0⟩ := hT.rootKey; exact hlt_nx _ _ hrn0
      refine ⟨rfl, ?_⟩
      rw [h11top, h10top']
      refine liveEdges_of_oneHole c.p (wNode c.p base w11) c.i root (m1 + 4) _ hL11 (fun y hy => hy)
        (fun _ _ he => absurd he (by omega)) ?_
      intro u un cc yn hu hun hcc hyn hne
      have hu10 := hR11 u hu
      obtain ⟨hup, hul, hur⟩ := hnot u hu10
      rw [h11w u hup (hcl' u hul hur)] at hun
      have hyn10 : wNode c.p base w11 (m1 + 4) = wNode c.p base w10 (m1 + 4) :=
        h11w _ (by omega) (hcl' _ (by omega) (by omega))
      rw [hyn10, hN10y] at hyn
      cases hyn
      rcases hR10 u hu10 with ⟨huV, _, huy⟩ | huy
      · by_cases huq : u = q
        · rw [huq, hN10q] at hun
          cases hun
          refine ⟨hne, ⟨fun h => ?_, fun _ hmg => ?_⟩⟩
          · rw [KNode.add_leaf, hqleaf] at h; cases h
          · have := hpOK.2.2 hqleaf hmg
            rw [hlasteq]; omega
        · exfalso
          rw [hN10 u huq hup huy] at hun
          exact hfreshV u cc huV ⟨un, hun, hcc⟩
      · exfalso
        rw [huy, hN10y] at hun
        cases hun
        rw [hlasteq] at hcc
        rcases hsomeL (m1 + 2) g2 rfl cc (m1 + 4) hcc with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
        · omega
        · omega
        · exact hfreshT (m1 + 4) (by omega) p cc hp ⟨pn, hpn, h⟩

/-! ## At a round: the narrow case of `MergeTailFullOK` -/

/-- The case of the merge's tail that `writerWP_mergeTail_liveFullTime` (into one
node) and `writerWP_mergeTail_liveFullTime2` (into two) prove: the merge's parent
p, not made by the transaction, goes `full` and splits in time (it compacts, or
its last version has at most `splitAbove` klongs), below its inner parent q (at
depth d - 2) with room for one more klong and no compaction. -/
def MergeFullTimeRoom (c : Ctx) (v3 : W) (d : Nat) (p : NodeId) (pn xn ln rn : KNode)
    (il cL ir cR : Nat) : Prop :=
  pn.firstTime ≠ some c.i ∧
  (∀ last, mergeFullLast pn c.i cL v3.next cR (mergeM2 c xn ln rn cR v3.next) = some last →
    pn.size + mergeParentNeed c.i pn il ir cR (mergeM2 c xn ln rn cR v3.next) ≤ c.p.M ∨
      last.size ≤ c.p.splitAbove) ∧
  2 ≤ d ∧ ∃ (q : NodeId) (qn : KNode) (k1 : Nat), (v3.path[d - 2]?).map (·.2) = some q ∧
    v3.path[d - 1]? = some (some k1, p) ∧ v3.nodes.lookup q = some qn ∧ qn.leaf = false ∧
    qn.size + 2 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false

set_option maxHeartbeats 16000000 in
/-- `MergeTailFullOK` in its case `MergeFullTimeRoom`: at a round with
`MergeLiveOK`'s facts, the merge's tail keeps the hole's form one height up, the
hole p's copy, which the next round's descent finds (`descendToHeight_redirect`:
the descent reads alike above q, q's klong of the key's path names the copy,
and the copy has p's height, one above x's). -/
theorem writerWP_mergeTail_liveFullTimeRound (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p)
    {B : NodeId} {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode)
    (hS : descendToHeight key g h c v = .ok (d, v1)) (hd : 0 < d)
    (hr13 : ReadsAs c.p base v1 v3) (hk13 : ObsKept c v1 v3) (hp13 : v3.path = v1.path)
    (hLH : LiveHoleW key g h c base v)
    (hJ3 : DelInvJ c base w0 k0 F KO B B v3) (hP3 : PathOK c v3 d X K Nn)
    (hb1 : Book B c v1) (hi1 : HtInv H B c v1) (hpf1 : PathFreeTo v1 v1.path.length)
    (hx : (v3.path[d]?).map (·.2) = some x) (hpath : (v3.path[d - 1]?).map (·.2) = some p)
    (hplk : v3.nodes.lookup p = some pn) (hpleaf : pn.leaf = false)
    (hxlk : v3.nodes.lookup x = some xn)
    (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
    (ir cL cR : Nat) (w3 : W) (hr3 : ReadsAs c.p base v3 w3)
    (h3p : w3.nodes.lookup p = some pn) (hk3 : ObsKept c v3 w3)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR) (hclt : cL < cR)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hxlr : x = l ∨ x = r) (hln : wNode c.p base v3 l = some ln) (hrn : wNode c.p base v3 r = some rn)
    (hpre3 : v3.nodes <+: w3.nodes) (hpath3 : w3.path = v3.path)
    (hnB : ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next))
    (hN : MergeFullTimeRoom c v3 d p pn xn ln rn il cL ir cR) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey)) := by
  obtain ⟨hpnew, htime, hd2, q, qn, k1, hq3, hk3', hq3lk, hqleaf, hqroom, hqdead⟩ := hN
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  have hd2' : d' + 2 - 2 = d' := by omega
  have hd1' : d' + 2 - 1 = d' + 1 := by omega
  rw [hd2'] at hq3
  rw [hd1'] at hk3' hpath
  have hI : PutInv c base v3 := hJ3.1.1.1
  have hRO : RangeOrder (wNode c.p base v3) c.i v3.top.rootKey := hJ3.1.1.2.2.1
  obtain ⟨hX, hK, hS2, hlinkK, _⟩ := id hP3
  have hXi : ∀ i, i ≤ d' + 2 → ∀ z, (v3.path[i]?).map (·.2) = some z → z = X i := by
    intro i hi z hz; have := hX i hi; rw [hz] at this; exact Option.some.inj this
  have hpX := hXi (d' + 1) (by omega) p hpath
  have hqX := hXi d' (by omega) q hq3
  have hxX := hXi (d' + 2) (Nat.le_refl _) x hx
  have hNlk : ∀ i, i ≤ d' + 2 → wNode c.p base v3 (X i) = some (Nn i) := by
    intro i hi
    obtain ⟨a, b⟩ := hS2 i hi
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hqn : Nn d' = qn := by
    have := (hS2 d' (by omega)).1; rw [← hqX, hq3lk] at this; exact (Option.some.inj this).symm
  have hpnN : Nn (d' + 1) = pn := by
    have := (hS2 (d' + 1) (by omega)).1; rw [← hpX, hplk] at this; exact (Option.some.inj this).symm
  have hk1 : K (d' + 1) = k1 := by
    have := hK (d' + 1) (by omega) (by omega)
    rw [hk3'] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.1.symm
  have hkq : (k1, p) ∈ qn.liveAt c.i := by
    have := hlinkK (d' + 1) (by omega) (by omega)
    rw [← hk1, hpX, ← hqn]; exact this
  have hpn : wNode c.p base v3 p = some pn := by rw [hpX, ← hpnN]; exact hNlk _ (by omega)
  have hNq : wNode c.p base v3 q = some qn := by rw [hqX, ← hqn]; exact hNlk _ (by omega)
  have hxn : wNode c.p base v3 x = some xn := by
    obtain ⟨a, b⟩ := hS2 (d' + 2) (Nat.le_refl _)
    rw [← hxX] at a b
    rw [hxlk] at a
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, hxlk]
  have hdep : ∀ i, i ≤ d' + 2 → PathLen (wNode c.p base v3) c.i v3.top.rootKey (X i) i :=
    pathOK_depth c base v3 (d' + 2) X K Nn hP3
  have hqP : PathLen (wNode c.p base v3) c.i v3.top.rootKey q d' := by rw [hqX]; exact hdep d' (by omega)
  have hpP : PathLen (wNode c.p base v3) c.i v3.top.rootKey p (d' + 1) := by
    rw [hpX]; exact hdep _ (by omega)
  have hpR := hpP.reach
  have hpRS := tReach_reachS _ c.i _ _ hpR
  have hfree : ∀ z, v3.next ≤ z → wNode c.p base v3 z = none ∧ v3.taken.contains z = false := by
    intro z hz
    have hl : v3.nodes.lookup z = none := by
      cases h' : v3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI.ids.1 z (by rw [h']; rfl); omega
    have ht : v3.taken.contains z = false := by
      cases h' : v3.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    refine ⟨?_, ht⟩
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hl, (hI.fresh z hz).1]
  have hfreshT : ∀ z, v3.next ≤ z → ∀ u c', TReach (wNode c.p base v3) c.i v3.top.rootKey u →
      ¬ TLink (wNode c.p base v3) c.i u c' z := by
    intro z hz u c' hu hl
    obtain ⟨un, hun, hc⟩ := hl
    have := hI.links u un c' z (tReach_reachS _ _ _ _ hu) hun hc
    omega
  have hmemL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hmemR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i (hI.times p pn hpn)]
    apply bk_mem_of_lookup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  obtain ⟨hlr1, _⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cL l ln hmemL hln
  obtain ⟨hrr1, _⟩ := mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cR r rn hmemR hrn
  have hlr2 := (mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cL l ln hmemL hln).2
  have hrr2 := (mrg_child_range (wNode c.p base v3) c.i v3.top.rootKey hRO p pn hpRS hpn
    hpleaf cR r rn hmemR hrn).2
  -- the round's descent
  obtain ⟨_, _, _, _, _, _, _, _, _, hk01⟩ := writerWP_descendToHeight_rd key g h c v (d' + 2) v1 hS
  have hr01 : ReadsAs c.p base v v1 := writerWP_descendToHeight_readsU key g h c base hvc v _ v1 hS
  have hk03 := hk01.trans hk13
  have hHl : ∀ y, HoleAtW key g h c v y → y = x := by
    intro y hy
    have h1 := hy (d' + 2) v1 hS
    rw [← hp13, hx] at h1
    exact (Option.some.inj h1).symm
  have hN3 : wNode c.p base v3 = wNode c.p base v := by rw [hr13.1, hr01.1]
  have htop3 : v3.top = v.top := hk03.2.2
  have hLive : LiveEdgesH c.p (wNode c.p base v3) c.i v3.top.rootKey (HoleAtW key g h c v) := by
    rw [hN3, htop3]; exact hLH
  have hql : q ≠ l := by
    intro he
    have h2 : PathLen (wNode c.p base v3) c.i v3.top.rootKey l (d' + 1 + 1) :=
      PathLen.link hpP ⟨pn, hpn, hmemL⟩
    rw [← he] at h2; have := PathLen.depth_unique hI.tree _ _ _ hqP h2; omega
  have hqr : q ≠ r := by
    intro he
    have h2 : PathLen (wNode c.p base v3) c.i v3.top.rootKey r (d' + 1 + 1) :=
      PathLen.link hpP ⟨pn, hpn, hmemR⟩
    rw [← he] at h2; have := PathLen.depth_unique hI.tree _ _ _ hqP h2; omega
  have hqp : q ≠ p := by
    intro he; rw [he] at hqP; have := PathLen.depth_unique hI.tree _ _ _ hqP hpP; omega
  have hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR := fun cc z h' => hlr2 cR r hmemR hclt cc z h'
  have hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc) := by
    intro cc z h'
    have h1 := hlr1 cc z h'
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
      · exact h1.1 hxl hc0
  have hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc) := by
    intro cc z h'
    have h1 := hrr1 cc z h'
    rw [hrl] at h1
    constructor
    · intro hin
      have hxl : xn.leaf = false := by simpa using hin
      rcases (h1.2 hxl) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (h0 (by omega))
    · intro hin
      have hxl : xn.leaf = true := by simpa using hin
      exact h1.1 hxl (by omega)
  cases hm2c : mergeM2 c xn ln rn cR v3.next with
  | some yg =>
    refine writerWP_mono (writerWP_mergeTail_liveFullTime2 c base hvc x d' p pn xn leftSome l ln il r rn
      ir cL cR (wNode c.p base v3) v3.top.rootKey v3.next w3 (HoleAtW key g h c v) hm hMP hI.tree hpR
      hpn hL hLL hR hRL hclt hadj hxlr hln hrn (hI.times p pn hpn)
      (fun cc z zn _ hzn => hI.times z zn hzn) hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2 h3p
      (fun z hz => by
        rcases hsrc3 z hz with h' | h'
        · exact hI.ids.1 z h'
        · exact hI.ids.2.1 z h')
      (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hpleaf hll hrl
      hlrange hllow hrrange (fun k z hk hkc cc z' h' => hrr2 k z hk hkc cc z' h')
      q qn k1 hqP hNq hkq hqleaf (lookup_of_prefix _ _ hpre3 _ _ hq3lk) (by rw [hpath3]; exact hq3)
      (by rw [hpath3]; exact hk3') (hI.wf q qn hNq) (hI.times q qn hNq) hqroom hqdead hpnew
      (by rw [hm2c]; rfl) hnB htime hLive hHl) ?_
    rintro res v4 ⟨hres, hLE⟩
    exact ⟨fun h1 => absurd (hres.symm.trans h1) (by decide), fun _ => hLE⟩
  | none =>
    rw [hm2c] at hnB htime
    refine writerWP_mono (writerWP_mergeTail_liveFullTime c base hvc x d' p pn xn leftSome l ln il r rn ir
      cL cR (wNode c.p base v3) v3.top.rootKey v3.next w3 (HoleAtW key g h c v) hm hMP hI.tree hpR hpn
      hL hLL hR hRL hclt hxlr hln hrn (hI.times p pn hpn) (fun cc z zn _ hzn => hI.times z zn hzn)
      hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2 h3p
      (fun z hz => by
        rcases hsrc3 z hz with h' | h'
        · exact hI.ids.1 z h'
        · exact hI.ids.2.1 z h')
      (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hpleaf hll hrl
      (fun cc z h' => hlr2 cR r hmemR hclt cc z h')
      (by
        intro cc z h'
        have h1 := hrr1 cc z h'
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
      q qn k1 hqP hNq hkq (lookup_of_prefix _ _ hpre3 _ _ hq3lk) (by rw [hpath3]; exact hq3)
      (by rw [hpath3]; exact hk3') (hI.wf q qn hNq) (hI.times q qn hNq) hqroom hqdead hpnew hm2c hnB
      htime hLive hHl) ?_
    rintro res v4 ⟨hres, hL4, hfr4, ⟨yn, hy4⟩, hq4, hgy4, hgfr4, htop4⟩
    subst hres
    refine ⟨fun _ => ?_, fun h' => absurd rfl h'⟩
    -- R1: the next round's descent finds the copy
    have hp1 : (v1.path[d' + 2 - 1]?).map (·.2) = some p := by rw [hd1', ← hp13]; exact hpath
    have hq1 : (v1.path[d' + 2 - 2]?).map (·.2) = some q := by rw [hd2', ← hp13]; exact hq3
    have hpk1 : v1.path[d' + 2 - 1]? = some (some k1, p) := by rw [hd1', ← hp13]; exact hk3'
    have hpnv : rdN c v p = some pn := by rw [← hk03.1]; exact rdN_of_lookup c v3 p pn hplk
    have hqnv : rdN c v q = some qn := by rw [← hk03.1]; exact rdN_of_lookup c v3 q qn hq3lk
    obtain ⟨cv, fd, hcv, hfdq, hfdc⟩ := descend_qsearch key g h c v v1 (d' + 2) hS (by omega) p q pn qn
      k1 hpk1 hpnv hpleaf hq1 hqnv hqleaf
    obtain ⟨fd', hfd', hfdy⟩ := searchLte_add_key qn c.i cv k1 (v3.next + 2) fd (hI.wf q qn hNq)
      (hI.times q qn hNq) hfdq hfdc
    have hpc1 : PathCached v1 := writerWP_descendToHeight_path_cached key g h c v (d' + 2) v1 hS
    have hgr : GradedL (rdN c v) (rdG c v) (v1.path.map (·.2)) := by
      have := gradedL_of_ht hvo.heights hb1 hi1 hpf1 hpc1
      rw [hk01.1, hk01.2.1] at this
      exact this
    have hlen1 : v1.path.length = d' + 3 := by
      obtain ⟨_, _, hl, _, _⟩ := descend_exit_shape key g h c v v1 (d' + 2) hS
      omega
    -- a node of the path at index j ≤ d': X j, cached at v3, below the next id, not p, l, r
    have hpathX : ∀ j, j ≤ d' + 2 → (v1.path.map (·.2))[j]? = some (X j) := by
      intro j hj; rw [List.getElem?_map, ← hp13]; exact hX j hj
    have hlow : ∀ j, j ≤ d' → X j ≠ p ∧ X j ≠ l ∧ X j ≠ r ∧ X j < v3.next ∧
        v3.nodes.lookup (X j) = some (Nn j) := by
      intro j hj
      have hPj := hdep j (by omega)
      have hlj := (hS2 j (by omega)).1
      refine ⟨fun he => ?_, fun he => ?_, fun he => ?_, hI.ids.1 _ (by rw [hlj]; rfl), hlj⟩
      · rw [he] at hPj; have := PathLen.depth_unique hI.tree _ _ _ hPj hpP; omega
      · rw [he] at hPj
        have h2 : PathLen (wNode c.p base v3) c.i v3.top.rootKey l (d' + 1 + 1) :=
          PathLen.link hpP ⟨pn, hpn, hmemL⟩
        have := PathLen.depth_unique hI.tree _ _ _ hPj h2; omega
      · rw [he] at hPj
        have h2 : PathLen (wNode c.p base v3) c.i v3.top.rootKey r (d' + 1 + 1) :=
          PathLen.link hpP ⟨pn, hpn, hmemR⟩
        have := PathLen.depth_unique hI.tree _ _ _ hPj h2; omega
    have hmemIdx : ∀ (k : Nat) u, u ∈ (List.map (·.2) v1.path).take k → ∃ j, j < k ∧ j < d' + 3 ∧ u = X j := by
      intro k u hu
      rw [List.mem_iff_getElem] at hu
      obtain ⟨j, hj, hju⟩ := hu
      simp only [List.length_take, List.length_map] at hj
      refine ⟨j, by omega, by omega, ?_⟩
      have := hpathX j (by omega)
      rw [← hju, List.getElem_take] at *
      rw [List.getElem?_eq_getElem (by simp; omega)] at this
      exact Option.some.inj this
    have hdl3 : (v1.path.map (·.2)).dropLast.dropLast.dropLast = (v1.path.map (·.2)).take d' := by
      simp only [List.dropLast_eq_take, List.length_take, List.length_map, hlen1, List.take_take]
      congr 1; omega
    have hdl2 : (v1.path.map (·.2)).dropLast.dropLast = (v1.path.map (·.2)).take (d' + 1) := by
      simp only [List.dropLast_eq_take, List.length_take, List.length_map, hlen1, List.take_take]
      congr 1; omega
    have hw3lk : ∀ j, j ≤ d' → w3.nodes.lookup (X j) = some (Nn j) :=
      fun j hj => lookup_of_prefix _ _ hpre3 _ _ (hlow j hj).2.2.2.2
    have hagN : ∀ u ∈ (v1.path.map (·.2)).dropLast.dropLast.dropLast, rdN c v4 u = rdN c v u := by
      intro u hu
      rw [hdl3] at hu
      obtain ⟨j, hj, _, rfl⟩ := hmemIdx d' u hu
      obtain ⟨hjp, hjl, hjr, hjn, hjlk⟩ := hlow j (by omega)
      have hjq : X j ≠ q := by
        intro he; rw [he] at hjlk
        have := hdep j (by omega); rw [he] at this
        have := PathLen.depth_unique hI.tree _ _ _ this hqP; omega
      rw [← hk03.1, rdN_of_lookup c v3 _ _ hjlk]
      exact rdN_of_lookup c v4 _ _ (by rw [hfr4 _ hjp hjq hjl hjr hjn, hw3lk j (by omega)])
    have hagG : ∀ u ∈ (v1.path.map (·.2)).dropLast.dropLast, rdG c v4 u = rdG c v u := by
      intro u hu
      rw [hdl2] at hu
      obtain ⟨j, hj, _, rfl⟩ := hmemIdx (d' + 1) u hu
      obtain ⟨hjp, hjl, hjr, hjn, hjlk⟩ := hlow j (by omega)
      obtain ⟨n4, hn4⟩ : ∃ n4, v4.nodes.lookup (X j) = some n4 := by
        by_cases hjq : X j = q
        · rw [hjq]; exact ⟨_, hq4⟩
        · exact ⟨_, by rw [hfr4 _ hjp hjq hjl hjr hjn, hw3lk j (by omega)]⟩
      rw [← hk03.2.1, ← hk3.2.1, rdG_of_lookup c v4 _ _ hn4, rdG_of_lookup c w3 _ _ (hw3lk j (by omega)),
        hgfr4 _ hjp hjl hjr hjn]
    have hGy : ∃ g', rdG c v4 (v3.next + 2) = some (g', h + 1) := by
      obtain ⟨g1, h1, g2, h2, hG1, hG2, hh⟩ := gradedL_get (rdN c v) (rdG c v) _ (d' + 1) p x pn hgr
        (by rw [List.getElem?_map, ← hp13]; exact hpath) (by rw [List.getElem?_map, ← hp13]; exact hx)
        hpnv hpleaf
      have hxv : (v1.path[d' + 2]?).map (·.2) = some x := by rw [← hp13]; exact hx
      obtain ⟨x', hx', _, ⟨gx, hgx'⟩, _⟩ := descend_exit_shape key g h c v v1 (d' + 2) hS
      rw [hxv] at hx'
      cases hx'
      rw [hgx'] at hG2; cases hG2
      refine ⟨g1, ?_⟩
      rw [rdG_of_lookup c v4 _ _ hy4, hgy4, ← rdG_of_lookup c w3 p pn h3p, hk3.2.1, hk03.2.1, hG1, hh]
    have hup : HoleAtW key g (h + 1) c v4 (v3.next + 2) := by
      intro d'' T1 hT1
      exact descendToHeight_redirect key g h c v v1 v4 (d' + 2) hS (by omega) p q (v3.next + 2) pn qn
        (qn.add c.i (.key k1 (v3.next + 2))) cv fd' hcv hp1 hpnv hpleaf hq1 hqnv hqleaf
        (by rw [htop4, hr3.2.1, htop3]) hagN hagG hgr (rdN_of_lookup c v4 q _ hq4)
        (by rw [KNode.add_leaf]; exact hqleaf) hfd' hfdy ⟨yn, rdN_of_lookup c v4 _ _ hy4⟩ hGy d'' T1 hT1
    refine liveEdgesH_mono c.p _ c.i _ (fun y => y = v3.next + 2) _ (fun y hy => hy ▸ hup) ?_ hL4
    intro u un cc y yn' hu hun hcc hyn _ hyp
    exact ((hL4.2 u un cc y yn' hu hun hcc hyn).1 hyp).1

/-! ## What is left of `MergeTailFullOK` -/

/-- `MergeTailFullOK` but in its case `MergeFullTimeRoom` (bergdb 030-01, step
3's rest): the merge's tail where its parent p goes `full`, and p was made by
the transaction, or p splits in space, or p is the space root (d = 1) or a
segment root (its parent q a segment leaf), or q has no room for one more klong
or would compact (the cascade). -/
def MergeTailFullRestOK (c : Ctx) (base : View BVal) (B : NodeId) (H : NodeId → Nat → Prop) :
    Prop :=
  ∀ (key : Key) (g h : Nat) (v v1 v3 : W) (d F : Nat) (w0 : W) (k0 : Key) (KO : KindOracle)
    (top0 : Top) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (x p : NodeId)
    (pn xn : KNode),
    descendToHeight key g h c v = .ok (d, v1) → 0 < d →
    ReadsAs c.p base v1 v3 → ObsKept c v1 v3 → v3.path = v1.path →
    LiveHoleW key g h c base v →
    DelInvJ c base w0 k0 F KO B B v3 → PutBook c B top0 v3 → PathOK c v3 d X K Nn →
    Book B c v1 → HtInv H B c v1 → PathFreeTo v1 v1.path.length → HtInv H B c v3 →
    (v3.path[d]?).map (·.2) = some x → (v3.path[d - 1]?).map (·.2) = some p →
    v3.nodes.lookup p = some pn → pn.leaf = false → v3.nodes.lookup x = some xn →
    xn.cnt < c.p.mergeBelow →
    ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode)
      (ir cL cR : Nat) (w3 : W), ReadsAs c.p base v3 w3 →
    w3.nodes.lookup p = some pn → ObsKept c v3 w3 →
    (∀ z, (w3.nodes.lookup z).isSome = true → (v3.nodes.lookup z).isSome = true ∨
      (c.view z).isSome = true) →
    pn.ks[il]? = some (.key cL l) → LastLive pn.ks pn.lastBitmap il cL →
    pn.ks[ir]? = some (.key cR r) → LastLive pn.ks pn.lastBitmap ir cR → cL < cR →
    (∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
    ln.leaf = xn.leaf → rn.leaf = xn.leaf →
    (x = l ∨ x = r) → wNode c.p base v3 l = some ln → wNode c.p base v3 r = some rn →
    v3.nodes <+: w3.nodes → w3.path = v3.path →
    ¬ MergeParentRoom c pn il cL v3.next ir cR (mergeM2 c xn ln rn cR v3.next) →
    ¬ MergeFullTimeRoom c v3 d p pn xn ln rn il cL ir cR →
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun res v4 => (res = 1 → LiveHoleW key g (h + 1) c base v4) ∧
        (res ≠ 1 → LiveEdges c.p (wNode c.p base v4) c.i v4.top.rootKey))

/-- `MergeTailFullOK` from its rest: its case `MergeFullTimeRoom` is proved
(`writerWP_mergeTail_liveFullTimeRound`). -/
theorem mergeTailFullOK_of_rest (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) {B : NodeId} {H : NodeId → Nat → Prop}
    (hvo : ViewHtOK H B c) (hF : MergeTailFullRestOK c base B H) : MergeTailFullOK c base B H := by
  intro key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3 hb1
    hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3
    hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB
  by_cases hN : MergeFullTimeRoom c v3 d p pn xn ln rn il cL ir cR
  · exact writerWP_mergeTail_liveFullTimeRound c base hvc hm hMP hvo key g h v v1 v3 d F w0 k0 KO
      X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hP3 hb1 hi1 hpf1 hx hpath hplk hpleaf hxlk
      leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3 hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn
      hpre3 hpath3 hnB hN
  · exact hF key g h v v1 v3 d F w0 k0 KO top0 X K Nn x p pn xn hS hd hr13 hk13 hp13 hLH hJ3 hpb3 hP3
      hb1 hi1 hpf1 hi3 hx hpath hplk hpleaf hxlk hcnt leftSome l ln il r rn ir cL cR w3 hr3 h3p hk3
      hsrc3 hL hLL hR hRL hclt hadj hll hrl hxlr hln hrn hpre3 hpath3 hnB hN

/-- `afterDelete` with the hole (bergdb 030-01, steps 3 and 4): from the call's
facts to `LiveEdges`, premises `MergeTailFullRestOK`, `MergeParamsOK` and R3
after the merges' loop. -/
theorem writerWP_afterDelete_liveTR (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (hm : c.p.merges = true) (hMP : MergeParamsOK c.p) (KO : KindOracle)
    (B : NodeId) (hv : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hICEk : ICEFromKinds c base KO B) (hsa2 : 2 ≤ c.p.splitAbove) (hcap : 1 ≤ c.p.mergeMax)
    (hpos : 0 < c.i) {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c)
    (hkw : ViewKlongsWf c.p c.view) (top0 : Top) (hB : PutBase c base B)
    (hF : MergeTailFullRestOK c base B H)
    (v : W) (hJ : DelInvJAE c base KO B B v) (hpb : PutBook c B top0 v) (hhi : HtInv H B c v)
    (hLH : LiveHoleW key g 0 c base v)
    (hR3 : WriterWP (mergeUp key g c.p.fuel 0 false) c v
      (fun merged v' => merged = true → R3At key g c v')) :
    WriterWP (afterDelete key g 0) c v
      (fun _ v' => LiveEdges c.p (wNode c.p base v') c.i v'.top.rootKey) :=
  writerWP_afterDelete_liveTF key g c base hvc hm hMP KO B hv hk hICEk hsa2 hcap hpos hvo hkw top0 hB
    (mergeTailFullOK_of_rest c base hvc hm hMP hvo hF) v hJ hpb hhi hLH hR3

end SIS.Tree
