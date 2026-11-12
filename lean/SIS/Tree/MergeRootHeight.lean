import SIS.Tree.MergeHeightBasics

namespace SIS.Tree

open SIS SIS.Check

/-- Reading a node caches the returned node, appends to the cache, and keeps
the access path. In particular it preserves every earlier cached node. -/
theorem writerWP_getNode_cache (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun n v =>
      v.nodes.lookup x = some n ∧ w.nodes.IsPrefix v.nodes ∧ v.path = w.path) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hn, ⟨[], by simp⟩, trivial⟩
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, ⟨_, rfl⟩, trivial⟩
        simp [List.lookup_append, hn]
    · exact writerWP_throw _ _ _ _

/-- The last entry of the path names x. -/
def PathEndsAt (w : W) (x : NodeId) : Prop :=
  ∃ cv, w.path.getLast? = some (cv,x)

/-- A segment root is the space root, or follows a cached segment leaf. -/
def SegmentRootPath (w : W) : Prop :=
  w.path.length = 1 ∨ ∃ cv q n,
    w.path[w.path.length-2]? = some (cv,q) ∧
      w.nodes.lookup q = some n ∧ n.leaf = true

theorem pathEndsAt_pos {w : W} {x : NodeId} (he : PathEndsAt w x) : 0 < w.path.length := by
  rcases he with ⟨cv,he⟩
  cases hp : w.path with
  | nil => simp [hp] at he
  | cons _ _ => simp

theorem segmentRootPath_of_read {w v : W} (hn : w.nodes.IsPrefix v.nodes)
    (hp : v.path = w.path) (hr : SegmentRootPath w) : SegmentRootPath v := by
  rcases hr with hr | ⟨cv,q,n,hq,hnq,hl⟩
  · exact Or.inl (hp ▸ hr)
  · exact Or.inr ⟨cv,q,n,by simpa only [hp] using hq,hn.lookup_eq_some hnq,hl⟩

theorem segmentRootPath_append {w : W} {x : NodeId} {n : KNode}
    (he : PathEndsAt w x) (hn : w.nodes.lookup x = some n) (hl : n.leaf = true)
    (cv : Nat) (y : NodeId) : SegmentRootPath {w with path := w.path ++ [(some cv,y)]} := by
  rcases he with ⟨c0,he⟩
  have hpos : 0 < w.path.length := pathEndsAt_pos ⟨c0,he⟩
  refine Or.inr ⟨c0,x,n,?_,hn,hl⟩
  simp only [List.length_append, List.length_singleton]
  rw [show w.path.length+1-2 = w.path.length-1 by omega]
  rw [List.getElem?_append_left (by omega)]
  exact List.getLast?_eq_getElem? ▸ he

/-- A successful descent ends at a cached segment leaf, preserving earlier
cache entries and the correspondence between its result and the path. -/
theorem writerWP_descendLte_leaf (cv fuel : Nat) (x : NodeId) (c : Ctx) (w : W)
    (he : PathEndsAt w x) :
    WriterWP (descendLte cv fuel x) c w (fun leaf v =>
      PathEndsAt v leaf ∧ (∃ n, v.nodes.lookup leaf = some n ∧ n.leaf = true) ∧
        w.nodes.IsPrefix v.nodes) := by
  induction fuel generalizing x w with
  | zero => exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_getNode_cache x c w) ?_
    intro n v hv
    by_cases hl : n.leaf = true
    · simp only [hl, ↓reduceIte, writerWP_pure]
      exact ⟨by simpa only [PathEndsAt, hv.2.2] using he, ⟨n,hv.1,hl⟩,hv.2.1⟩
    · simp only [hl, Bool.false_eq_true, ↓reduceIte]
      split
      · exact writerWP_throw _ _ _ _
      · rename_i fd hfd
        simp only [pathAdd, writerWP_bind, writerWP_modify]
        refine writerWP_mono (ih fd.y {v with path := v.path ++ [(some fd.c,fd.y)]} ?_) ?_
        · refine ⟨some fd.c, ?_⟩
          rw [List.getLast?_append]
          rfl
        · intro leaf v1 hv1
          exact ⟨hv1.1,hv1.2.1,hv.2.1.trans hv1.2.2⟩

theorem writerWP_foldlM_state {α β : Type} (xs : List α) (f : β → α → M β)
    (a : β) (c : Ctx) (w : W) (inv : β → W → Prop) (hi : inv a w)
    (step : ∀ a b v, inv a v → WriterWP (f a b) c v inv) :
    WriterWP (xs.foldlM f a) c w inv := by
  induction xs generalizing a w with
  | nil => simpa only [List.foldlM_nil, writerWP_pure] using hi
  | cons b xs ih =>
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (step a b w hi) (fun a v hv => ih a v hv)

/-- Rebuilding the path to a segment root ends at that root, immediately
after a segment leaf unless it is the space root. -/
theorem writerWP_descendToSegmentRoot_path (key : Key) (g : Nat) (c : Ctx) (w : W) :
    WriterWP (descendToSegmentRoot key g) c w
      (fun root v => PathEndsAt v root ∧ SegmentRootPath v) := by
  unfold descendToSegmentRoot pathClear findRoot pathAdd
  wpSimplify
  refine writerWP_foldlM_state _ _ _ _ _
    (fun root v => PathEndsAt v root ∧ SegmentRootPath v) ?_ ?_
  · constructor
    · exact ⟨none,rfl⟩
    · exact Or.inl rfl
  · intro node cv v hv
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_descendLte_leaf cv c.p.fuel node c v hv.1) ?_
    intro leaf vl hl
    refine writerWP_mono (writerWP_getNode_cache leaf c vl) ?_
    intro n vn hn
    obtain ⟨ln,hln,hll⟩ := hl.2.1
    have hln' := hn.2.1.lookup_eq_some hln
    have hlnn : ln = n := Option.some.inj (hln'.symm.trans hn.1)
    have hleaf : n.leaf = true := hlnn ▸ hll
    have hend : PathEndsAt vn leaf := by simpa only [PathEndsAt, hn.2.2] using hl.1
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      constructor
      · refine ⟨some fd.c, ?_⟩
        rw [List.getLast?_append]
        rfl
      · exact segmentRootPath_append hend hn.1 hleaf fd.c fd.y

theorem writerWP_getNode_known (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (post : KNode → W → Prop) :
    WriterWP (getNode x) c w post ↔ post n w := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get, hn, writerWP_pure]

theorem writerWP_ghOf_cache (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (ghOf x) c w (fun gh v =>
      (x,gh.1,gh.2) ∈ v.gh ∧ (∃ n, v.nodes.lookup x = some n) ∧
        w.nodes.IsPrefix v.nodes ∧ v.path = w.path) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_getNode_cache x c w) ?_
  intro n v hv
  simp only [writerWP_get]
  split
  · rename_i gh hgh
    simp only [writerWP_pure]
    exact ⟨gh_lookup_mem hgh,⟨n,hv.1⟩,hv.2⟩
  · exact writerWP_throw _ _ _ _

/-- If the requested height is the root's, the descent leaves a root path.
Otherwise a successful descent witnesses a strictly higher cached root. -/
theorem writerWP_descendHeight_root (cv h fuel : Nat) (root : NodeId) (c : Ctx) (w : W)
    (hr : SegmentRootPath w) :
    WriterWP (descendHeight cv h fuel root) c w (fun _ v =>
      SegmentRootPath v ∨ ∃ g height, (root,g,height) ∈ v.gh ∧ h < height) := by
  cases fuel with
  | zero => exact writerWP_throw _ _ _ _
  | succ fuel =>
    unfold descendHeight
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_ghOf_cache root c w) ?_
    intro gh v hv
    rcases gh with ⟨g,hx⟩
    simp only at hv ⊢
    by_cases hh : hx = h
    · simp only [hh, BEq.rfl, ↓reduceIte, writerWP_pure]
      exact Or.inl (segmentRootPath_of_read hv.2.2.1 hv.2.2.2 hr)
    · simp only [show (hx == h) = false from beq_eq_false_iff_ne.mpr hh,
        Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      obtain ⟨n,hn⟩ := hv.2.1
      rw [writerWP_getNode_known root n c v hn]
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hcontinue
        have hnot : ¬ hx < h := by
          intro hlt
          simp [hlt] at hcontinue
        have hlt : h < hx := by omega
        split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          simp only [pathAdd, writerWP_bind, writerWP_modify]
          refine writerWP_mono
            (fieldsGrow_descendHeight cv h fuel fd.y c
              {v with path := v.path ++ [(some fd.c,fd.y)]}) ?_
          intro r v1 hgrow
          exact Or.inr ⟨g,hx,hgrow.1.subset hv.1,hlt⟩

/-- At a segment root the merge loop stops before attempting a merge. -/
def SegmentRootStop (d : Nat) (w : W) : Prop :=
  d = 0 ∨ ∃ cv q n, w.path[d-1]? = some (cv,q) ∧
    w.nodes.lookup q = some n ∧ n.leaf = true

theorem segmentRootStop_of_path (w : W) (hr : SegmentRootPath w) :
    SegmentRootStop (w.path.length-1) w := by
  rcases hr with hr | ⟨cv,q,n,hq,hn,hl⟩
  · exact Or.inl (by omega)
  · exact Or.inr ⟨cv,q,n,by simpa only [Nat.sub_sub] using hq,hn,hl⟩

theorem writerWP_descendToHeight_root (key : Key) (g h : Nat) (c : Ctx) (w : W) :
    WriterWP (descendToHeight key g h) c w (fun d v =>
      SegmentRootStop d v ∨ ∃ y segment height, (y,segment,height) ∈ v.gh ∧ h < height) := by
  unfold descendToHeight
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_descendToSegmentRoot_path key g c w) ?_
  intro root v hv
  split
  · exact writerWP_throw _ _ _ _
  · rename_i cv hcv
    rw [writerWP_bind]
    refine writerWP_mono (writerWP_descendHeight_root cv h c.p.fuel root c v hv.2) ?_
    intro r v1 hroot
    simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
    rcases hroot with hr | ⟨segment,height,hh,hle⟩
    · exact Or.inl (segmentRootStop_of_path v1 hr)
    · exact Or.inr ⟨root,segment,height,hh,hle⟩

/-- Only heights strictly below a segment root can merge. The root itself
may be temporary and one height above the transaction's final bound. -/
theorem writerWP_mergeUp_rootHeightBound (key : Key) (g fuel h : Nat) (merged : Bool)
    (cap : Nat) (c : Ctx) (w : W) :
    WriterWP (mergeUp key g fuel h merged) c w
      (fun _ v => SeenHeightBound cap v → v.merges ≤ w.merges + (cap-h)) := by
  induction fuel generalizing h merged w with
  | zero => exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_of_stats (mergesLe_descendToHeight key g h)
      (fieldsGrow_descendToHeight key g h) c w _ ?_
    intro d wd hd hmd hgd
    have hroot := writerWP_descendToHeight_root key g h c w d wd hd
    by_cases hd0 : d == 0
    · simp only [hd0, ↓reduceIte, writerWP_pure]
      intro hb
      omega
    · simp only [show (d == 0) = false from Bool.eq_false_iff.mpr hd0,
        Bool.false_eq_true, ↓reduceIte]
      simp only [pathNode, writerWP_bind, writerWP_get]
      split
      · rename_i ex hex
        simp only [writerWP_pure]
        split
        · rename_i ep hep
          simp only [writerWP_pure]
          rcases hroot with hstop | ⟨y,gy,hy,hseen,hhigh⟩
          · rcases hstop with hz | ⟨cv,q,pn,hpq,hpn,hleaf⟩
            · simp [hz] at hd0
            · have he : ep = (cv,q) := Option.some.inj (hep.symm.trans hpq)
              subst ep
              rw [writerWP_getNode_known q pn c wd hpn]
              simp only [hleaf, ↓reduceIte, writerWP_pure]
              intro hb
              omega
          · refine writerWP_of_stats (mergesLe_getNode 0 _) (fieldsGrow_getNode _) _ _ _ ?_
            intro pn wp hp hmp hgp
            by_cases hleaf : pn.leaf = true
            · simp only [hleaf, ↓reduceIte, writerWP_pure]
              intro hb
              omega
            · simp only [hleaf, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
              refine writerWP_of_stats (mergesLe_getNode 0 _) (fieldsGrow_getNode _) _ _ _ ?_
              intro xn wx hx hmx hgx
              by_cases hcnt : xn.cnt ≥ c.p.mergeBelow
              · simp only [hcnt, ↓reduceIte, writerWP_pure]
                intro hb
                omega
              · simp only [hcnt, ↓reduceIte, writerWP_bind]
                refine writerWP_of_stats (mergesLe_merge _ _) (fieldsGrow_merge _ _) _ _ _ ?_
                intro r wr hr hmr hgr
                by_cases hr2 : r == 2
                · simp only [hr2, ↓reduceIte, writerWP_pure]
                  intro hb
                  have hcap := hb y gy hy ((hgp.trans (hgx.trans hgr)).subset hseen)
                  omega
                · simp only [show (r == 2) = false from Bool.eq_false_iff.mpr hr2,
                    Bool.false_eq_true, ↓reduceIte]
                  refine writerWP_of_result _ _ _ _ ?_
                  intro b v hv hb
                  have hg' := (fieldsGrow_mergeUp key g fuel (h+1) true c wr b v hv).1
                  have hc' := ih (h+1) true wr b v hv hb
                  have hcap := hb y gy hy ((hgp.trans (hgx.trans (hgr.trans hg'))).subset hseen)
                  omega
        · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _

end SIS.Tree
