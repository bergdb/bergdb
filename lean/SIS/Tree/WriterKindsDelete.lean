/-
The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsSplit.lean:
the descents, which follow klongs of the overlay onto the key access path, and
the delete: the bitmaps, LE-b, the take-back, root collapse and the merges.
-/
import SIS.Tree.WriterKindsSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- x is the last node of the key access path. -/
def KdPathLast (w : W) (x : NodeId) : Prop := ∃ a, w.path[w.path.length - 1]? = some (a, x)

/-- A full node's replacement by a last version of klongs of the right kind. -/
theorem kd_handleFull (K : KindOracle) (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode)
    (compact : Bool) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c)
    (hb : Book B c w) (hi : KdInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh)
    (hpx : ∃ a, w.path[depth]? = some (a, x)) (hlast : kdKs (KindKlong K w g h) last.ks) :
    WriterWP (handleFull depth x last compact) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  obtain ⟨a, hpx⟩ := hpx
  unfold handleFull
  refine kd_handleFullWith K B _ depth x [] last compact c w hv hk hb hi g h hx a hpx hlast
    kdPairs_nil' ?_
  intro e he
  subst he
  intro q more c' w' hv' hk' hb' hi' hpq hmore
  exact kd_appendKlongs K B e q more c' w' hv' hk' hb' hi' hmore hpq

/-! ## The descents -/

/-- A read of a node of the overlay changes nothing. -/
theorem kd_getNode_hit (x : NodeId) (m : KNode) (c : Ctx) (w : W)
    (h : w.nodes.lookup x = some m) : WriterWP (getNode x) c w (fun n v => n = m ∧ v = w) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get, h, writerWP_pure]
  exact ⟨trivial, trivial⟩

/-- The descent by `searchLte` from x, the path's last node or an empty
segment leaf off the path: it stops at a segment leaf, the path's last node
(or x itself, the empty leaf, with the path as it was). -/
theorem kd_descendLte (K : KindOracle) (B : NodeId) (cv fuel : Nat) :
    ∀ (x : NodeId) (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w →
      KdInv K B w → (KdPathLast w x ∨ w.nodes.lookup x = some ⟨true, []⟩) →
      WriterWP (descendLte cv fuel x) c w (fun r v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧
        (KdPathLast v r ∨ (r = x ∧ v.path = w.path ∧ v.nodes.lookup r = some ⟨true, []⟩)) ∧
        ∃ n, v.nodes.lookup r = some n ∧ n.leaf = true) := by
  induction fuel with
  | zero => intro x c w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hv hk hb hi hx
    unfold descendLte
    kdSimp
    rcases hx with ⟨a, ha⟩ | he
    · refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
      rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
      split
      · rename_i hleaf
        rw [writerWP_pure]
        exact ⟨hb1, hi1, hle1, Or.inl ⟨a, by rw [hp1]; exact ha⟩, n, hl1, hleaf⟩
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb1 hl1
          have ha1 : w1.path[w1.path.length - 1]? = some (a, x) := by rw [hp1]; exact ha
          kdSimp
          refine writerWP_mono (kd_pathAdd K B fd.c fd.y c w1 hv hb1 hi1 a x g h ha1 hm
            (kd_cache_node hi1 hl1 hm _ _ (kd_searchLte_mem n c.i cv fd hfd))) ?_
          rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
          refine writerWP_mono (ih fd.y c w2 hv hk hb2 hi2 (Or.inl ⟨some fd.c, ?_⟩)) ?_
          · rw [hp2]
            simp
          · rintro r v ⟨hb3, hi3, hle3, hlast, hleaf3⟩
            refine ⟨hb3, hi3, hle1.trans (hle2.trans hle3), ?_, hleaf3⟩
            rcases hlast with hlast | ⟨rfl, hp3, -⟩
            · exact Or.inl hlast
            · left
              refine ⟨some fd.c, ?_⟩
              rw [hp3, hp2]
              simp
    · refine writerWP_mono (kd_getNode_hit x _ c w he) ?_
      rintro n w1 ⟨rfl, rfl⟩
      simp only [↓reduceIte, writerWP_pure]
      exact ⟨hb, hi, KdLe.refl _, Or.inr ⟨by trivial, by trivial, he⟩, _, he, rfl⟩

/-- A fold of steps that keep an invariant. -/
theorem kd_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (c : Ctx) (Inv : β → W → Prop)
    (hf : ∀ b a w, Inv b w → WriterWP (f b a) c w (fun r v => Inv r v ∧ KdLe w v)) :
    ∀ (init : β) (w : W), Inv init w → WriterWP (xs.foldlM f init) c w (fun r v => Inv r v ∧ KdLe w v) := by
  induction xs with
  | nil =>
    intro init w h0
    simp only [List.foldlM_nil, writerWP_pure]
    exact ⟨h0, KdLe.refl w⟩
  | cons a xs ih =>
    intro init w h0
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a w h0) ?_
    rintro b v ⟨hb, hle⟩
    exact writerWP_mono (ih b v hb) (fun r u h => ⟨h.1, hle.trans h.2⟩)

theorem kd_pathLast_append (l : List (Option Nat × NodeId)) (e : Option Nat × NodeId) :
    (l ++ [e])[(l ++ [e]).length - 1]? = some e := by simp

/-- The descent to the root of the tree of segment `segment` on the key's
path: it ends at the path's last node. -/
theorem kd_descendToSegmentRoot (K : KindOracle) (B : NodeId) (key : Key) (segment : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) :
    WriterWP (descendToSegmentRoot key segment) c w (fun r v => Book B c v ∧ KdInv K B v ∧
      KdLe w v ∧ KdPathLast v r) := by
  unfold descendToSegmentRoot
  kdSimp
  refine writerWP_mono (kd_pathClear K B c w hv hb hi) ?_
  rintro _ w1 ⟨hb1, hi1, hle1, hp1, -⟩
  refine writerWP_mono (kd_findRoot K B c w1 hv hb1 hi1 hp1) ?_
  rintro root w2 ⟨hb2, hi2, hle2, hp2, -⟩
  refine writerWP_mono (kd_foldlM _ _ c (fun node v => Book B c v ∧ KdInv K B v ∧ KdPathLast v node)
    ?_ root w2 ⟨hb2, hi2, none, by rw [hp2]; rfl⟩) ?_
  · intro node cv u ⟨hbu, hiu, hlu⟩
    kdSimp
    refine writerWP_mono (kd_descendLte K B cv c.p.fuel node c u hv hk hbu hiu (Or.inl hlu)) ?_
    rintro leaf u1 ⟨hb3, hi3, hle3, hlast, -⟩
    have hl3 : KdPathLast u1 leaf := by
      rcases hlast with h | ⟨rfl, hp, -⟩
      · exact h
      · obtain ⟨a, ha⟩ := hlu
        exact ⟨a, by rw [hp]; exact ha⟩
    refine writerWP_mono (kd_getNode K B leaf c u1 hv hk hb3 hi3) ?_
    rintro n u2 ⟨hb4, hi4, hle4, hl4, hp4, -⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb4 hl4
      obtain ⟨a, ha⟩ := hl3
      kdSimp
      refine writerWP_mono (kd_pathAdd K B fd.c fd.y c u2 hv hb4 hi4 a leaf g h
        (by rw [hp4]; exact ha) hm
        (kd_cache_node hi4 hl4 hm _ _ (kd_searchEq_mem n c.i cv fd hfd))) ?_
      rintro _ u3 ⟨hb5, hi5, hle5, hp5, -⟩
      exact ⟨⟨hb5, hi5, some fd.c, by rw [hp5]; exact kd_pathLast_append _ _⟩,
        hle3.trans (hle4.trans hle5)⟩
  · rintro r v ⟨⟨hb3, hi3, hl3⟩, hle3⟩
    exact ⟨hb3, hi3, hle1.trans (hle2.trans hle3), hl3⟩

/-- The descent by height from x, the path's last node. -/
theorem kd_descendHeight (K : KindOracle) (B : NodeId) (cv h fuel : Nat) :
    ∀ (x : NodeId) (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w →
      KdInv K B w → KdPathLast w x →
      WriterWP (descendHeight cv h fuel x) c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v) := by
  induction fuel with
  | zero => intro x c w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hv hk hb hi ⟨a, ha⟩
    unfold descendHeight
    kdSimp
    refine writerWP_mono (kd_ghOf K B x c w hv hk hb hi) ?_
    rintro ⟨gx, hx⟩ w1 ⟨hb1, hi1, hle1, hp1, -, hm1, -⟩
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1⟩
    · kdSimp
      refine writerWP_mono (kd_getNode K B x c w1 hv hk hb1 hi1) ?_
      rintro n w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
      have hm2 := KdLe.gh' hm1 hle2
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          kdSimp
          refine writerWP_mono (kd_pathAdd K B fd.c fd.y c w2 hv hb2 hi2 a x gx hx
            (by rw [hp2, hp1]; exact ha) hm2
            (kd_cache_node hi2 hl2 hm2 _ _ (kd_searchLte_mem n c.i cv fd hfd))) ?_
          rintro _ w3 ⟨hb3, hi3, hle3, hp3, -⟩
          refine writerWP_mono (ih fd.y c w3 hv hk hb3 hi3 ⟨some fd.c, ?_⟩) ?_
          · rw [hp3]; exact kd_pathLast_append _ _
          · rintro _ v ⟨hb4, hi4, hle4⟩
            exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4))⟩

theorem kd_descendToHeight (K : KindOracle) (B : NodeId) (key : Key) (g h : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KdInv K B w) :
    WriterWP (descendToHeight key g h) c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v) := by
  unfold descendToHeight
  kdSimp
  refine writerWP_mono (kd_descendToSegmentRoot K B key g c w hv hk hb hi) ?_
  rintro root w1 ⟨hb1, hi1, hle1, hl1⟩
  split
  · exact writerWP_throw _ _ _ _
  · kdSimp
    refine writerWP_mono (kd_descendHeight K B _ h c.p.fuel root c w1 hv hk hb1 hi1 hl1) ?_
    rintro _ w2 ⟨hb2, hi2, hle2⟩
    refine writerWP_mono (kd_pathSize c w2) ?_
    rintro _ w3 ⟨rfl, -⟩
    exact ⟨hb2, hi2, hle1.trans hle2⟩

/-! ## The steps of the delete -/

/-- A step that keeps the books, the walk's state and the path. -/
def KdKeepsP (K : KindOracle) (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KdInv K B w →
    WriterWP f c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path)

theorem kdP_writerWP {K : KindOracle} {B : NodeId} {α : Type} {f : M α} (hf : KdKeepsP K B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c)
    (hb : Book B c w) (hi : KdInv K B w)
    (hp : ∀ r v, Book B c v → KdInv K B v → KdLe w v → v.path = w.path → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hv hk hb hi) (fun r v h => hp r v h.1 h.2.1 h.2.2.1 h.2.2.2)

macro "kdUseP " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' kdP_writerWP $h _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  intro _ _ _ _ _ _))

/-- A key node taken back: no change but the list of nodes taken back. -/
theorem kd_takenBack (K : KindOracle) (B x : NodeId) (c : Ctx) (vr w : W) (n : KNode)
    (hl : vr.nodes.lookup x = some n) (hk : KdLe vr w) (hb : Book B c w) (hi : KdInv K B w) :
    WriterWP (takenBack x) c w (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  refine writerWP_mono (writerWP_and (book_takenBack B x c vr w n hl hk.1 hb)
    (kdFrame_takenBack x c w)) ?_
  rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hvl, hm, hp, hx⟩
  exact ⟨hb', hi.frame v hn hg hvl hm hp hx, ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp⟩

macro "kdTake" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _)
  (refine writerWP_mono (kd_takenBack ?kdK ?kdB _ _ ?kdVr _ ?kdN ?kdLook ?kdKr ?kdBook ?kdInv) ?kdPost)
  case kdLook => assumption
  case kdKr => kdChain
  case kdBook => kdState
  case kdInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

/-- Klongs of the transaction pointed to `dst` instead of `src`, a key node of
dst's segment. -/
theorem kd_retarget (K : KindOracle) (B : NodeId) (p src dst : NodeId) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KdInv K B w)
    (gs hs : Nat) (hsrc : (src, gs, hs) ∈ w.gh) (hdst : IsKeySeg K w dst gs) :
    WriterWP (retarget p src dst) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold retarget
  kdSimp
  refine writerWP_mono (kd_getNode K B p c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  obtain ⟨gp, hp, hm⟩ := kd_tag_of_lookup hb1 hl1
  split
  · refine writerWP_mono (kd_putNode K B p _ c w1 hb1 hi1 n hl1 rfl gp hp hm
      (kdKs_retargetMap _ _ _ (kd_cache_node hi1 hl1 hm) (fun cv hcv => kd_swap hb1 hk hi1
        (KdLe.gh' hsrc hle1) (kd_cache_node hi1 hl1 hm cv src hcv) (hdst.kdMono hle1)))) ?_
    rintro _ v ⟨hb2, hi2, hle2, hp2, -⟩
    exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  · rw [writerWP_pure]
    exact ⟨hb1, hi1, hle1, hp1⟩

theorem kd_unlink (K : KindOracle) (B : NodeId) (x : NodeId) : KdKeepsP K B (unlink x) := by
  intro c w hv hk hb hi
  unfold unlink
  repeat' first | kdSimp | kdCore | wpSplit | split | contradiction

theorem kd_canTakeBack (K : KindOracle) (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KdKeepsP K B (canTakeBack x parent cv) := by
  intro c w hv hk hb hi
  unfold canTakeBack
  repeat' first | kdSimp | kdCore | wpSplit | split | contradiction

theorem kd_climb (K : KindOracle) (B : NodeId) (t : Nat) : KdKeepsP K B (climb t) := by
  induction t with
  | zero =>
    intro c w hv hk hb hi
    unfold climb
    repeat' first | kdSimp | kdCore | wpSplit | split | contradiction
  | succ t ih =>
    intro c w hv hk hb hi
    unfold climb
    repeat' first
      | kdSimp
      | kdCore
      | kdUseP (kd_canTakeBack _ _ _ _ _)
      | kdUseP ih
      | wpSplit
      | split
      | contradiction

/-- The take-back of x, a node of the overlay, by its parent: the parent's
klongs to x name the node that x replaced, of x's segment. -/
theorem kd_takeBack (K : KindOracle) (B : NodeId) (x parent : NodeId) (cv : Nat) (c : Ctx)
    (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) :
    WriterWP (takeBack x parent cv) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  obtain ⟨nx, hnx⟩ := kd_lookup_of_tag hb hx
  unfold takeBack
  kdSimp
  refine writerWP_mono (kd_getNode K B parent c w hv hk hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  refine writerWP_mono (kd_replacedBy x c w1) ?_
  rintro r w1' ⟨hw, hr⟩
  rw [hw]
  split
  · rename_i old j hj
    split
    · exact writerWP_throw _ _ _ _
    · have hx1 := KdLe.gh' hx hle1
      kdSimp
      refine writerWP_mono (kd_retarget K B parent x old c w1 hv hk hb1 hi1 g h hx1
        (hi1.made (x, old) (hr old rfl) g h hx1)) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2⟩
      refine writerWP_mono (kd_takenBack K B x c w w2 nx hnx (hle1.trans hle2) hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3⟩
      refine writerWP_mono (kd_note K B _ c w3 hv hk hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4)),
        hp4.trans (hp3.trans (hp2.trans hp1))⟩
  · exact writerWP_throw _ _ _ _

/-- A full node's replacement, x being the path's node at `depth`, with x's
entry in `gh` given. -/
macro "kdHFx " hx:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (kd_handleFull ?kdK ?kdB _ _ _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv _ _ (KdLe.gh' $hx ?kdKt) ?kdPx ?kdLast) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  case kdKt => kdChain
  case kdPx => exact ⟨_, kd_path_at (by assumption) (by kdPathEq)⟩
  case kdLast => kdKsTac
  rintro _ _ ⟨_, _, _, _⟩))

/-- A full node's replacement, x being the path's node at `depth`. -/
macro "kdHF" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (kd_handleFull ?kdK ?kdB _ _ _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv ?kdG ?kdH ?kdTagX ?kdPx ?kdLast) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  case kdTagX => kdTag
  case kdPx => exact ⟨_, kd_path_at (by assumption) (by kdPathEq)⟩
  case kdLast => kdKsTac
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 1600000 in
/-- The bitmap that deletes cv in x, the path's node at `depth`. -/
theorem kd_appendDeleteKlong (K : KindOracle) (B : NodeId) (x : NodeId) (depth cv : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) :
    WriterWP (appendDeleteKlong x depth cv) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold appendDeleteKlong
  repeat' first
    | kdSimp
    | kdCore
    | kdHF
    | wpSplit
    | split
    | contradiction

/-- LE-b's klongs: the next live klong's pointer, given the empty key, in an
inner node. -/
macro "kdKsLeb" : tactic => `(tactic| first
  | kdKsTac
  | exact kdKs_repoint _ (by kdKsTac) (fun _ _ _ => kd_free (by assumption) _ _ _
      (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain) _ _
        (kd_emptyKeyFold _ (by assumption))))
  | exact kdKs_add_key _ (by kdKsTac) (kd_free (by assumption) _ _ _
      (kd_cache_at (by assumption) (by assumption) (by kdTag) (by kdChain) _ _
        (kd_emptyKeyFold _ (by assumption)))))

macro "kdStoreLeb " hx:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (kd_putNode_of ?kdK ?kdB _ _ _ ?kdVr _ _ ?kdN ?kdBook ?kdInv ?kdLook ?kdKr ?kdLeaf _ _ $hx ?kdKt ?kdKs) ?kdPost)
  case kdBook => kdState
  case kdInv => assumption
  case kdLook => assumption
  case kdKr => kdChain
  case kdLeaf => first | bkLeaf | (split <;> bkLeaf)
  case kdKt => kdChain
  case kdKs => first | kdKsLeb | (split <;> kdKsLeb)
  rintro _ _ ⟨_, _, _, _, _, _⟩))

set_option maxHeartbeats 3200000 in
/-- LE-b in x, an inner node, the path's node at `depth`. -/
theorem kd_emptyKeyNext (K : KindOracle) (B : NodeId) (x : NodeId) (depth : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (g h : Nat)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) :
    WriterWP (emptyKeyNext x depth) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold emptyKeyNext
  repeat' first
    | kdSimp
    | kdStoreLeb hx
    | kdHFx hx
    | kdCore
    | wpSplit
    | split
    | contradiction

/-! ## Root collapse -/

/-- The child that an inner node's klong names is of its segment. -/
theorem kd_child_seg {K : KindOracle} {B : NodeId} {w : W} (hi : KdInv K B w) {x : NodeId}
    {n : KNode} {g h only : Nat} {child : NodeId} (hl : w.nodes.lookup x = some n)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) (hc : n.ptr? only = some child) : IsKeySeg K w child g := by
  obtain ⟨c0, hc0⟩ := kd_ptr_mem hc
  exact (kd_cache_node hi hl hx c0 child (kd_mem_of_get hc0)).1 hh

/-- The root x, inner and the path's node at `depth`, taken back: the klong of
the segment leaf above names x's child, of x's segment. -/
theorem kd_takeBackRoot (K : KindOracle) (B : NodeId) (x : NodeId) (depth only : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (g h : Nat)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) :
    WriterWP (takeBackRoot x depth only) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold takeBackRoot
  kdSimp
  refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hx1 := KdLe.gh' hx hle1
  split
  · exact writerWP_throw _ _ _ _
  · rename_i child hc
    have hcs := kd_child_seg hi1 hl1 hx1 hh hc
    cases depth with
    | zero =>
      kdSimp
      refine writerWP_mono (kd_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kd_newSuperRoot K B child c w2 hv hk hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3, -⟩
      refine writerWP_mono (kd_takenBack K B x c w1 w3 n hl1 (hle2.trans hle3) hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4)),
        hp4.trans (hp3.trans (hp2.trans hp1))⟩
    | succ d =>
      kdSimp
      refine writerWP_mono (kd_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kd_pathNode d c w2) ?_
      rintro leaf w2' ⟨hw, a', hla⟩
      subst hw
      refine writerWP_mono (kd_getNode K B leaf c w2' hv hk hb2 hi2) ?_
      rintro ln w3 ⟨hb3, hi3, hle3, hl3, hp3, -⟩
      refine writerWP_mono (kd_klongAt (d + 1) c w3) ?_
      rintro k w3' ⟨hw, y', hky⟩
      subst hw
      have hpw : w3'.path = w.path := hp3.trans (hp2.trans hp1)
      rw [hpw, hpx] at hky
      simp only [Option.some.injEq, Prod.mk.injEq] at hky
      obtain ⟨rfl, rfl⟩ := hky
      rw [hp2, hp1] at hla
      obtain ⟨gl, hl', hml⟩ := kd_tag_of_lookup hb3 hl3
      have hkl : KindKlong K w3' gl hl' k x :=
        hi3.path d a' leaf k x (by rw [hpw]; exact hla) (by rw [hpw]; exact hpx) gl hl' hml
      have hkc : KindKlong K w3' gl hl' k child :=
        kd_swap hb3 hk hi3 (KdLe.gh' hx1 (hle2.trans hle3)) hkl (hcs.kdMono (hle2.trans hle3))
      split
      · rename_i j hj
        split
        · exact writerWP_throw _ _ _ _
        · kdSimp
          refine writerWP_mono (kd_putNode K B leaf _ c w3' hb3 hi3 ln hl3 (bk_repoint_leaf _ _ _)
            gl hl' hml (kdKs_repoint _ (kd_cache_node hi3 hl3 hml) (kd_repoint_ok hj hkc))) ?_
          rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
          refine writerWP_mono (kd_takenBack K B x c w1 w4 n hl1
            (hle2.trans (hle3.trans hle4)) hb4 hi4) ?_
          rintro _ w5 ⟨hb5, hi5, hle5, hp5⟩
          exact ⟨hb5, hi5, hle1.trans (hle2.trans (hle3.trans (hle4.trans hle5))),
            hp5.trans (hp4.trans hpw)⟩
      · exact writerWP_throw _ _ _ _

/-- The root x, inner and the path's node at `depth`, replaced by its child. -/
theorem kd_replaceRoot (K : KindOracle) (B : NodeId) (x : NodeId) (depth only : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (g h : Nat)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) :
    WriterWP (replaceRoot x depth only) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold replaceRoot
  kdSimp
  refine writerWP_mono (kd_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hx1 := KdLe.gh' hx hle1
  split
  · exact writerWP_throw _ _ _ _
  · rename_i child hc
    have hcs := kd_child_seg hi1 hl1 hx1 hh hc
    cases depth with
    | zero =>
      kdSimp
      refine writerWP_mono (kd_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kd_unlink K B x c w2 hv hk hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3⟩
      refine writerWP_mono (kd_newSuperRoot K B child c w3 hv hk hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4)),
        hp4.trans (hp3.trans (hp2.trans hp1))⟩
    | succ d =>
      kdSimp
      refine writerWP_mono (kd_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kd_pathNode d c w2) ?_
      rintro leaf w2' ⟨hw, a', hla⟩
      subst hw
      refine writerWP_mono (kd_klongAt (d + 1) c w2') ?_
      rintro k w3 ⟨hw, y', hky⟩
      subst hw
      have hpw : w3.path = w.path := hp2.trans hp1
      rw [hpw, hpx] at hky
      simp only [Option.some.injEq, Prod.mk.injEq] at hky
      obtain ⟨rfl, rfl⟩ := hky
      rw [hpw] at hla
      have hlg : leaf ∈ w3.gh.map (·.1) :=
        hi2.pathGh d a' leaf (by rw [hpw]; exact hla)
          (by rw [hpw]; exact (List.getElem?_eq_some_iff.mp hpx).1)
      obtain ⟨⟨leaf', gl, hl'⟩, hml, hle'⟩ := List.mem_map.mp hlg
      simp only at hle'
      subst hle'
      have hkl : KindKlong K w3 gl hl' k x :=
        hi2.path d a' leaf' k x (by rw [hpw]; exact hla) (by rw [hpw]; exact hpx) gl hl' hml
      have hkc : KindKlong K w3 gl hl' k child :=
        kd_swap hb2 hk hi2 (KdLe.gh' hx1 hle2) hkl (hcs.kdMono hle2)
      refine writerWP_mono (kd_unlink K B x c w3 hv hk hb2 hi2) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
      refine writerWP_mono (kd_appendKlongs K B d leaf' [(k, child)] c w4 hv hk hb4 hi4
        ⟨gl, hl', KdLe.gh' hml hle4, kdPairs_cons (hkc.kdMono hle4) kdPairs_nil'⟩
        ⟨a', by rw [hp4, hpw]; exact hla⟩) ?_
      rintro _ w5 ⟨hb5, hi5, hle5, hp5⟩
      exact ⟨hb5, hi5, hle1.trans (hle2.trans (hle4.trans hle5)), hp5.trans (hp4.trans hpw)⟩

/-- Root collapse. -/
theorem kd_collapseRoot (K : KindOracle) (B : NodeId) (key : Key) (segment fuel : Nat) :
    ∀ (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KdInv K B w →
      WriterWP (collapseRoot key segment fuel) c w
        (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v) := by
  induction fuel with
  | zero => intro c w _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro c w hv hk hb hi
    unfold collapseRoot
    kdSimp
    refine writerWP_mono (kd_descendToSegmentRoot K B key segment c w hv hk hb hi) ?_
    rintro root w1 ⟨hb1, hi1, hle1, ⟨a, hla⟩⟩
    refine writerWP_mono (kd_getNode K B root c w1 hv hk hb1 hi1) ?_
    rintro n w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
    obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb2 hl2
    have hla2 : w2.path[w2.path.length - 1]? = some (a, root) := by rw [hp2]; exact hla
    have hfin : ∀ (r : Unit) (v : W), Book B c v → KdInv K B v → KdLe w2 v →
        WriterWP (collapseRoot key segment f) c v (fun _ u => Book B c u ∧ KdInv K B u ∧ KdLe w u) := by
      intro r v hbv hiv hlev
      exact writerWP_mono (ih c v hv hk hbv hiv)
        (fun _ u h => ⟨h.1, h.2.1, hle1.trans (hle2.trans (hlev.trans h.2.2))⟩)
    split
    · rw [writerWP_pure]; exact ⟨hb2, hi2, hle1.trans hle2⟩
    · rename_i hleaf
      have hh : h ≠ 0 := by
        intro h0
        subst h0
        have := kd_leaf hb2 hl2 hm
        simp at this
        exact hleaf this
      kdSimp
      refine writerWP_mono (kd_replacedBy root c w2) ?_
      rintro r w2' ⟨hw, -⟩
      subst hw
      split
      · rw [writerWP_pure]; exact ⟨hb2, hi2, hle1.trans hle2⟩
      · split
        · rw [writerWP_pure]; exact ⟨hb2, hi2, hle1.trans hle2⟩
        · split
          · exact writerWP_throw _ _ _ _
          · kdSimp
            refine writerWP_mono (kd_pathSize c w2') ?_
            rintro sz w3 ⟨hw, hsz⟩
            subst hw
            subst hsz
            split <;> kdSimp
            · refine writerWP_mono (kd_takeBackRoot K B root _ _ c w3 hv hk hb2 hi2 a hla2 g h hm hh) ?_
              rintro _ v ⟨hbv, hiv, hlev, -⟩
              exact hfin () v hbv hiv hlev
            · refine writerWP_mono (kd_replaceRoot K B root _ _ c w3 hv hk hb2 hi2 a hla2 g h hm hh) ?_
              rintro _ v ⟨hbv, hiv, hlev, -⟩
              exact hfin () v hbv hiv hlev

/-! ## The merges -/

/-- An inner node's klong names a node of its segment. -/
theorem kd_inner_kl {K : KindOracle} {w : W} {g h c : Nat} {y : NodeId} (hh : h ≠ 0)
    (hy : IsKeySeg K w y g) : KindKlong K w g h c y :=
  ⟨fun _ => hy, fun h0 => absurd h0 hh⟩

/-- Klongs of an inner node that name nodes of its segment. -/
syntax "kdKsMP " term:max term:max : tactic
macro_rules
  | `(tactic| kdKsMP $hm1 $hm2) => `(tactic| first
    | kdKsTac
    | exact kdKs_repoint _ (by kdKsMP $hm1 $hm2) (fun _ _ _ => kd_inner_kl (by assumption)
        (IsKeySeg.kdMono $hm1 (by kdChain)))
    | exact kdKs_repoint _ (by kdKsMP $hm1 $hm2) (fun _ _ _ => kd_inner_kl (by assumption)
        (IsKeySeg.kdMono ($hm2 _ _ rfl) (by kdChain)))
    | exact kdKs_add_key _ (by kdKsMP $hm1 $hm2) (kd_inner_kl (by assumption)
        (IsKeySeg.kdMono $hm1 (by kdChain)))
    | exact kdKs_add_key _ (by kdKsMP $hm1 $hm2) (kd_inner_kl (by assumption)
        (IsKeySeg.kdMono ($hm2 _ _ rfl) (by kdChain)))
    | exact kdKs_insertSorted _ (by kdKsMP $hm1 $hm2) (kd_inner_kl (by assumption)
        (IsKeySeg.kdMono ($hm2 _ _ rfl) (by kdChain)))
    | exact kdKs_replaceKlong (by assumption) (by kdKsMP $hm1 $hm2) (kd_inner_kl (by assumption)
        (IsKeySeg.kdMono $hm1 (by kdChain)))
    | exact kdKs_replaceKlong (by assumption) (by kdKsMP $hm1 $hm2) (kd_inner_kl (by assumption)
        (IsKeySeg.kdMono ($hm2 _ _ rfl) (by kdChain)))
    | (split <;> kdKsMP $hm1 $hm2))

macro "kdStoreMP " hx:term:max hm1:term:max hm2:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (kd_putNode_of ?kdK ?kdB _ _ _ ?kdVr _ _ ?kdN ?kdBook ?kdInv ?kdLook ?kdKr ?kdLeaf _ _ $hx ?kdKt ?kdKs) ?kdPost)
  case kdBook => kdState
  case kdInv => assumption
  case kdLook => assumption
  case kdKr => kdChain
  case kdLeaf => first | bkLeaf | (split <;> bkLeaf) | (repeat' split) <;> bkLeaf
  case kdKt => kdChain
  case kdKs => kdKsMP $hm1 $hm2
  rintro _ _ ⟨_, _, _, _, _, _⟩))

macro "kdHFMP " hx:term:max hm1:term:max hm2:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (kd_handleFull ?kdK ?kdB _ _ _ _ _ _ ?kdView ?kdKinds ?kdBook ?kdInv _ _ (KdLe.gh' $hx ?kdKt) ?kdPx ?kdLast) ?kdPost)
  case kdView => assumption
  case kdKinds => assumption
  case kdBook => kdState
  case kdInv => assumption
  case kdKt => kdChain
  case kdPx => exact ⟨_, kd_path_at (by assumption) (by kdPathEq)⟩
  case kdLast => kdKsMP $hm1 $hm2
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 6400000 in
/-- The parent p of a merge, inner and the path's node at `depth`, gets klongs
that name m1 and m2, made with the merged nodes' segment, p's. -/
theorem kd_mergeParent (K : KindOracle) (B : NodeId) (p : NodeId) (depth il cL : Nat)
    (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat))
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KdInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, p)) (gp hp : Nat)
    (hx : (p, gp, hp) ∈ w.gh) (hh : hp ≠ 0) (hm1 : IsKeySeg K w m1 gp)
    (hm2 : ∀ y g', m2 = some (y, g') → IsKeySeg K w y gp) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w
      (fun _ v => Book B c v ∧ KdInv K B v ∧ KdLe w v ∧ v.path = w.path) := by
  unfold mergeParent
  repeat' first
    | kdSimp
    | kdStoreMP hx hm1 hm2
    | kdHFMP hx hm1 hm2
    | kdCore
    | wpSplit
    | split
    | contradiction

end SIS.Tree
