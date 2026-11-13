/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name, continued from SIS/Tree/WriterKindsSplit.lean:
the descents, which follow klongs of the overlay onto the key access path, and
the delete: the bitmaps, LE-b, the take-back, root collapse and the merges.
-/
import SIS.Tree.RootWalkSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- x is the last node of the key access path. -/
def KrPathLast (w : W) (x : NodeId) : Prop := ∃ a, w.path[w.path.length - 1]? = some (a, x)

/-- A full node's replacement by a last version of klongs of the right kind. -/
theorem kr_handleFull (K : KindOracle) (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode)
    (compact : Bool) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c)
    (hb : Book B c w) (hi : KrInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh)
    (hpx : ∃ a, w.path[depth]? = some (a, x)) (hlast : krKs (KindKlong K w g h) last.ks) :
    WriterWP (handleFull depth x last compact) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  obtain ⟨a, hpx⟩ := hpx
  unfold handleFull
  refine kr_handleFullWith K B _ depth x [] last compact c w hv hk hb hi g h hx a hpx hlast
    krPairs_nil' ?_
  intro e he
  subst he
  intro q more c' w' hv' hk' hb' hi' hpq hmore
  exact kr_appendKlongs K B e q more c' w' hv' hk' hb' hi' hmore hpq

/-! ## The descents -/

/-- A read of a node of the overlay changes nothing. -/
theorem kr_getNode_hit (x : NodeId) (m : KNode) (c : Ctx) (w : W)
    (h : w.nodes.lookup x = some m) : WriterWP (getNode x) c w (fun n v => n = m ∧ v = w) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get, h, writerWP_pure]
  exact ⟨trivial, trivial⟩

/-- The descent by `searchLte` from x, the path's last node or an empty
segment leaf off the path: it stops at a segment leaf, the path's last node
(or x itself, the empty leaf, with the path as it was). -/
theorem kr_descendLte (K : KindOracle) (B : NodeId) (cv fuel : Nat) :
    ∀ (x : NodeId) (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w →
      KrInv K B w → (KrPathLast w x ∨ w.nodes.lookup x = some ⟨true, []⟩) →
      WriterWP (descendLte cv fuel x) c w (fun r v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧
        (KrPathLast v r ∨ (r = x ∧ v.path = w.path ∧ v.nodes.lookup r = some ⟨true, []⟩)) ∧
        ∃ n, v.nodes.lookup r = some n ∧ n.leaf = true) := by
  induction fuel with
  | zero => intro x c w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hv hk hb hi hx
    unfold descendLte
    krSimp
    rcases hx with ⟨a, ha⟩ | he
    · refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
      rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
      split
      · rename_i hleaf
        rw [writerWP_pure]
        exact ⟨hb1, hi1, hle1, Or.inl ⟨a, by rw [hp1]; exact ha⟩, n, hl1, hleaf⟩
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          obtain ⟨g, h, hm⟩ := kr_tag_of_lookup hb1 hl1
          have ha1 : w1.path[w1.path.length - 1]? = some (a, x) := by rw [hp1]; exact ha
          krSimp
          refine writerWP_mono (kr_pathAdd K B fd.c fd.y c w1 hv hb1 hi1 a x g h ha1 hm
            (kr_cache_node hi1 hl1 hm _ _ (kr_searchLte_mem n c.i cv fd hfd))) ?_
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
    · refine writerWP_mono (kr_getNode_hit x _ c w he) ?_
      rintro n w1 ⟨rfl, rfl⟩
      simp only [↓reduceIte, writerWP_pure]
      exact ⟨hb, hi, KrLe.refl _, Or.inr ⟨by trivial, by trivial, he⟩, _, he, rfl⟩

/-- A fold of steps that keep an invariant. -/
theorem kr_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (c : Ctx) (Inv : β → W → Prop)
    (hf : ∀ b a w, Inv b w → WriterWP (f b a) c w (fun r v => Inv r v ∧ KrLe w v)) :
    ∀ (init : β) (w : W), Inv init w → WriterWP (xs.foldlM f init) c w (fun r v => Inv r v ∧ KrLe w v) := by
  induction xs with
  | nil =>
    intro init w h0
    simp only [List.foldlM_nil, writerWP_pure]
    exact ⟨h0, KrLe.refl w⟩
  | cons a xs ih =>
    intro init w h0
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a w h0) ?_
    rintro b v ⟨hb, hle⟩
    exact writerWP_mono (ih b v hb) (fun r u h => ⟨h.1, hle.trans h.2⟩)

theorem kr_pathLast_append (l : List (Option Nat × NodeId)) (e : Option Nat × NodeId) :
    (l ++ [e])[(l ++ [e]).length - 1]? = some e := by simp

/-- The descent to the root of the tree of segment `segment` on the key's
path: it ends at the path's last node. -/
theorem kr_descendToSegmentRoot (K : KindOracle) (B : NodeId) (key : Key) (segment : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) :
    WriterWP (descendToSegmentRoot key segment) c w (fun r v => Book B c v ∧ KrInv K B v ∧
      KrLe w v ∧ KrPathLast v r) := by
  unfold descendToSegmentRoot
  krSimp
  refine writerWP_mono (kr_pathClear K B c w hv hb hi) ?_
  rintro _ w1 ⟨hb1, hi1, hle1, hp1, -⟩
  refine writerWP_mono (kr_findRoot K B c w1 hv hb1 hi1 hp1) ?_
  rintro root w2 ⟨hb2, hi2, hle2, hp2, -⟩
  refine writerWP_mono (kr_foldlM _ _ c (fun node v => Book B c v ∧ KrInv K B v ∧ KrPathLast v node)
    ?_ root w2 ⟨hb2, hi2, none, by rw [hp2]; rfl⟩) ?_
  · intro node cv u ⟨hbu, hiu, hlu⟩
    krSimp
    refine writerWP_mono (kr_descendLte K B cv c.p.fuel node c u hv hk hbu hiu (Or.inl hlu)) ?_
    rintro leaf u1 ⟨hb3, hi3, hle3, hlast, -⟩
    have hl3 : KrPathLast u1 leaf := by
      rcases hlast with h | ⟨rfl, hp, -⟩
      · exact h
      · obtain ⟨a, ha⟩ := hlu
        exact ⟨a, by rw [hp]; exact ha⟩
    refine writerWP_mono (kr_getNode K B leaf c u1 hv hk hb3 hi3) ?_
    rintro n u2 ⟨hb4, hi4, hle4, hl4, hp4, -⟩
    split
    · exact writerWP_throw _ _ _ _
    · rename_i fd hfd
      obtain ⟨g, h, hm⟩ := kr_tag_of_lookup hb4 hl4
      obtain ⟨a, ha⟩ := hl3
      krSimp
      refine writerWP_mono (kr_pathAdd K B fd.c fd.y c u2 hv hb4 hi4 a leaf g h
        (by rw [hp4]; exact ha) hm
        (kr_cache_node hi4 hl4 hm _ _ (kr_searchEq_mem n c.i cv fd hfd))) ?_
      rintro _ u3 ⟨hb5, hi5, hle5, hp5, -⟩
      exact ⟨⟨hb5, hi5, some fd.c, by rw [hp5]; exact kr_pathLast_append _ _⟩,
        hle3.trans (hle4.trans hle5)⟩
  · rintro r v ⟨⟨hb3, hi3, hl3⟩, hle3⟩
    exact ⟨hb3, hi3, hle1.trans (hle2.trans hle3), hl3⟩

/-- The descent by height from x, the path's last node. -/
theorem kr_descendHeight (K : KindOracle) (B : NodeId) (cv h fuel : Nat) :
    ∀ (x : NodeId) (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w →
      KrInv K B w → KrPathLast w x →
      WriterWP (descendHeight cv h fuel x) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  induction fuel with
  | zero => intro x c w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x c w hv hk hb hi ⟨a, ha⟩
    unfold descendHeight
    krSimp
    refine writerWP_mono (kr_ghOf K B x c w hv hk hb hi) ?_
    rintro ⟨gx, hx⟩ w1 ⟨hb1, hi1, hle1, hp1, -, hm1, -⟩
    split
    · rw [writerWP_pure]; exact ⟨hb1, hi1, hle1⟩
    · krSimp
      refine writerWP_mono (kr_getNode K B x c w1 hv hk hb1 hi1) ?_
      rintro n w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
      have hm2 := KrLe.gh' hm1 hle2
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          krSimp
          refine writerWP_mono (kr_pathAdd K B fd.c fd.y c w2 hv hb2 hi2 a x gx hx
            (by rw [hp2, hp1]; exact ha) hm2
            (kr_cache_node hi2 hl2 hm2 _ _ (kr_searchLte_mem n c.i cv fd hfd))) ?_
          rintro _ w3 ⟨hb3, hi3, hle3, hp3, -⟩
          refine writerWP_mono (ih fd.y c w3 hv hk hb3 hi3 ⟨some fd.c, ?_⟩) ?_
          · rw [hp3]; exact kr_pathLast_append _ _
          · rintro _ v ⟨hb4, hi4, hle4⟩
            exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4))⟩

theorem kr_descendToHeight (K : KindOracle) (B : NodeId) (key : Key) (g h : Nat) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KrInv K B w) :
    WriterWP (descendToHeight key g h) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  unfold descendToHeight
  krSimp
  refine writerWP_mono (kr_descendToSegmentRoot K B key g c w hv hk hb hi) ?_
  rintro root w1 ⟨hb1, hi1, hle1, hl1⟩
  split
  · exact writerWP_throw _ _ _ _
  · krSimp
    refine writerWP_mono (kr_descendHeight K B _ h c.p.fuel root c w1 hv hk hb1 hi1 hl1) ?_
    rintro _ w2 ⟨hb2, hi2, hle2⟩
    refine writerWP_mono (kr_pathSize c w2) ?_
    rintro _ w3 ⟨rfl, -⟩
    exact ⟨hb2, hi2, hle1.trans hle2⟩

/-! ## The steps of the delete -/

/-- A step that keeps the books, the walk's state and the path. -/
def KrKeepsP (K : KindOracle) (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KrInv K B w →
    WriterWP f c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path)

theorem krP_writerWP {K : KindOracle} {B : NodeId} {α : Type} {f : M α} (hf : KrKeepsP K B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c)
    (hb : Book B c w) (hi : KrInv K B w)
    (hp : ∀ r v, Book B c v → KrInv K B v → KrLe w v → v.path = w.path → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hv hk hb hi) (fun r v h => hp r v h.1 h.2.1 h.2.2.1 h.2.2.2)

macro "krUseP " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' krP_writerWP $h _ _ _ ?krView ?krKinds ?krBook ?krInv ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  intro _ _ _ _ _ _))

/-- A key node taken back: no change but the list of nodes taken back. -/
theorem kr_takenBack (K : KindOracle) (B x : NodeId) (c : Ctx) (vr w : W) (n : KNode)
    (hl : vr.nodes.lookup x = some n) (hk : KrLe vr w) (hb : Book B c w) (hi : KrInv K B w) :
    WriterWP (takenBack x) c w (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  refine writerWP_mono (writerWP_and (book_takenBack B x c vr w n hl hk.1 hb)
    (krFrame_takenBack x c w)) ?_
  rintro _ v ⟨⟨hb', hk'⟩, hn, hg, hvl, hm, hp, hx, ht⟩
  exact ⟨hb', hi.frame v hn hg hvl hm hp hx ht, ⟨hk', fun q hq => by rw [hvl]; exact hq⟩, hp⟩

macro "krTake" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _)
  (refine writerWP_mono (kr_takenBack ?krK ?krB _ _ ?krVr _ ?krN ?krLook ?krKr ?krBook ?krInv) ?krPost)
  case krLook => assumption
  case krKr => krChain
  case krBook => krState
  case krInv => assumption
  rintro _ _ ⟨_, _, _, _⟩))

/-- Klongs of the transaction pointed to `dst` instead of `src`, a key node of
dst's segment. -/
theorem kr_retarget (K : KindOracle) (B : NodeId) (p src dst : NodeId) (c : Ctx) (w : W)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w) (hi : KrInv K B w)
    (gs hs : Nat) (hsrc : (src, gs, hs) ∈ w.gh) (hdst : IsKeySeg K w dst gs) :
    WriterWP (retarget p src dst) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold retarget
  krSimp
  refine writerWP_mono (kr_getNode K B p c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  obtain ⟨gp, hp, hm⟩ := kr_tag_of_lookup hb1 hl1
  split
  · refine writerWP_mono (kr_putNode K B p _ c w1 hb1 hi1 n hl1 rfl gp hp hm
      (krKs_retargetMap _ _ _ (kr_cache_node hi1 hl1 hm) (fun cv hcv => kr_swap hb1 hk hi1
        (KrLe.gh' hsrc hle1) (kr_cache_node hi1 hl1 hm cv src hcv) (hdst.krMono hle1)))) ?_
    rintro _ v ⟨hb2, hi2, hle2, hp2, -⟩
    exact ⟨hb2, hi2, hle1.trans hle2, hp2.trans hp1⟩
  · rw [writerWP_pure]
    exact ⟨hb1, hi1, hle1, hp1⟩

theorem kr_unlink (K : KindOracle) (B : NodeId) (x : NodeId) : KrKeepsP K B (unlink x) := by
  intro c w hv hk hb hi
  unfold unlink
  repeat' first | krSimp | krCore | wpSplit | split | contradiction

theorem kr_canTakeBack (K : KindOracle) (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KrKeepsP K B (canTakeBack x parent cv) := by
  intro c w hv hk hb hi
  unfold canTakeBack
  repeat' first | krSimp | krCore | wpSplit | split | contradiction

theorem kr_climb (K : KindOracle) (B : NodeId) (t : Nat) : KrKeepsP K B (climb t) := by
  induction t with
  | zero =>
    intro c w hv hk hb hi
    unfold climb
    repeat' first | krSimp | krCore | wpSplit | split | contradiction
  | succ t ih =>
    intro c w hv hk hb hi
    unfold climb
    repeat' first
      | krSimp
      | krCore
      | krUseP (kr_canTakeBack _ _ _ _ _)
      | krUseP ih
      | wpSplit
      | split
      | contradiction

/-- The take-back of x, a node of the overlay, by its parent: the parent's
klongs to x name the node that x replaced, of x's segment. -/
theorem kr_takeBack (K : KindOracle) (B : NodeId) (x parent : NodeId) (cv : Nat) (c : Ctx)
    (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (g h : Nat) (hx : (x, g, h) ∈ w.gh) :
    WriterWP (takeBack x parent cv) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  obtain ⟨nx, hnx⟩ := kr_lookup_of_tag hb hx
  unfold takeBack
  krSimp
  refine writerWP_mono (kr_getNode K B parent c w hv hk hb hi) ?_
  rintro pn w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  refine writerWP_mono (kr_replacedBy x c w1) ?_
  rintro r w1' ⟨hw, hr⟩
  rw [hw]
  split
  · rename_i old j hj
    split
    · exact writerWP_throw _ _ _ _
    · have hx1 := KrLe.gh' hx hle1
      krSimp
      refine writerWP_mono (kr_retarget K B parent x old c w1 hv hk hb1 hi1 g h hx1
        (hi1.made (x, old) (hr old rfl) g h hx1)) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2⟩
      refine writerWP_mono (kr_takenBack K B x c w w2 nx hnx (hle1.trans hle2) hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3⟩
      refine writerWP_mono (kr_note K B _ c w3 hv hk hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4)),
        hp4.trans (hp3.trans (hp2.trans hp1))⟩
  · exact writerWP_throw _ _ _ _

/-- A full node's replacement, x being the path's node at `depth`, with x's
entry in `gh` given. -/
macro "krHFx " hx:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (kr_handleFull ?krK ?krB _ _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ _ (KrLe.gh' $hx ?krKt) ?krPx ?krLast) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krKt => krChain
  case krPx => exact ⟨_, kr_path_at (by assumption) (by krPathEq)⟩
  case krLast => krKsTac
  rintro _ _ ⟨_, _, _, _⟩))

/-- A full node's replacement, x being the path's node at `depth`. -/
macro "krHF" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (kr_handleFull ?krK ?krB _ _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv ?krG ?krH ?krTagX ?krPx ?krLast) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krTagX => krTag
  case krPx => exact ⟨_, kr_path_at (by assumption) (by krPathEq)⟩
  case krLast => krKsTac
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 1600000 in
/-- The bitmap that deletes cv in x, the path's node at `depth`. -/
theorem kr_appendDeleteKlong (K : KindOracle) (B : NodeId) (x : NodeId) (depth cv : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) :
    WriterWP (appendDeleteKlong x depth cv) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold appendDeleteKlong
  repeat' first
    | krSimp
    | krCore
    | krHF
    | wpSplit
    | split
    | contradiction

/-- LE-b's klongs: the next live klong's pointer, given the empty key, in an
inner node. -/
macro "krKsLeb" : tactic => `(tactic| first
  | krKsTac
  | exact krKs_repoint _ (by krKsTac) (fun _ _ _ => kr_free (by assumption) _ _ _
      (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain) _ _
        (kr_emptyKeyFold _ (by assumption))))
  | exact krKs_add_key _ (by krKsTac) (kr_free (by assumption) _ _ _
      (kr_cache_at (by assumption) (by assumption) (by krTag) (by krChain) _ _
        (kr_emptyKeyFold _ (by assumption)))))

macro "krStoreLeb " hx:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (kr_putNode_of ?krK ?krB _ _ _ ?krVr _ _ ?krN ?krBook ?krInv ?krLook ?krKr ?krLeaf _ _ $hx ?krKt ?krKs) ?krPost)
  case krBook => krState
  case krInv => assumption
  case krLook => assumption
  case krKr => krChain
  case krLeaf => first | bkLeaf | (split <;> bkLeaf)
  case krKt => krChain
  case krKs => first | krKsLeb | (split <;> krKsLeb)
  rintro _ _ ⟨_, _, _, _, _, _⟩))

set_option maxHeartbeats 3200000 in
/-- LE-b in x, an inner node, the path's node at `depth`. -/
theorem kr_emptyKeyNext (K : KindOracle) (B : NodeId) (x : NodeId) (depth : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (g h : Nat)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) :
    WriterWP (emptyKeyNext x depth) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold emptyKeyNext
  repeat' first
    | krSimp
    | krStoreLeb hx
    | krHFx hx
    | krCore
    | wpSplit
    | split
    | contradiction

/-! ## Root collapse -/

/-- The child that an inner node's klong names is of its segment. -/
theorem kr_child_seg {K : KindOracle} {B : NodeId} {w : W} (hi : KrInv K B w) {x : NodeId}
    {n : KNode} {g h only : Nat} {child : NodeId} (hl : w.nodes.lookup x = some n)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) (hc : n.ptr? only = some child) : IsKeySeg K w child g := by
  obtain ⟨c0, hc0⟩ := kr_ptr_mem hc
  exact (kr_cache_node hi hl hx c0 child (kr_mem_of_get hc0)).1 hh

/-- The root x, inner and the path's node at `depth`, taken back: the klong of
the segment leaf above names x's child, of x's segment. -/
theorem kr_takeBackRoot (K : KindOracle) (B : NodeId) (x : NodeId) (depth only : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (g h : Nat)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) :
    WriterWP (takeBackRoot x depth only) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold takeBackRoot
  krSimp
  refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hx1 := KrLe.gh' hx hle1
  split
  · exact writerWP_throw _ _ _ _
  · rename_i child hc
    have hcs := kr_child_seg hi1 hl1 hx1 hh hc
    cases depth with
    | zero =>
      krSimp
      refine writerWP_mono (kr_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kr_newSuperRoot K B child c w2 hv hk hb2 hi2 ⟨g, hcs.krMono hle2⟩) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3, -⟩
      refine writerWP_mono (kr_takenBack K B x c w1 w3 n hl1 (hle2.trans hle3) hb3 hi3) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4)),
        hp4.trans (hp3.trans (hp2.trans hp1))⟩
    | succ d =>
      krSimp
      refine writerWP_mono (kr_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kr_pathNode d c w2) ?_
      rintro leaf w2' ⟨hw, a', hla⟩
      subst hw
      refine writerWP_mono (kr_getNode K B leaf c w2' hv hk hb2 hi2) ?_
      rintro ln w3 ⟨hb3, hi3, hle3, hl3, hp3, -⟩
      refine writerWP_mono (kr_klongAt (d + 1) c w3) ?_
      rintro k w3' ⟨hw, y', hky⟩
      subst hw
      have hpw : w3'.path = w.path := hp3.trans (hp2.trans hp1)
      rw [hpw, hpx] at hky
      simp only [Option.some.injEq, Prod.mk.injEq] at hky
      obtain ⟨rfl, rfl⟩ := hky
      rw [hp2, hp1] at hla
      obtain ⟨gl, hl', hml⟩ := kr_tag_of_lookup hb3 hl3
      have hkl : KindKlong K w3' gl hl' k x :=
        hi3.path d a' leaf k x (by rw [hpw]; exact hla) (by rw [hpw]; exact hpx) gl hl' hml
      have hkc : KindKlong K w3' gl hl' k child :=
        kr_swap hb3 hk hi3 (KrLe.gh' hx1 (hle2.trans hle3)) hkl (hcs.krMono (hle2.trans hle3))
      split
      · rename_i j hj
        split
        · exact writerWP_throw _ _ _ _
        · krSimp
          refine writerWP_mono (kr_putNode K B leaf _ c w3' hb3 hi3 ln hl3 (bk_repoint_leaf _ _ _)
            gl hl' hml (krKs_repoint _ (kr_cache_node hi3 hl3 hml) (kr_repoint_ok hj hkc))) ?_
          rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
          refine writerWP_mono (kr_takenBack K B x c w1 w4 n hl1
            (hle2.trans (hle3.trans hle4)) hb4 hi4) ?_
          rintro _ w5 ⟨hb5, hi5, hle5, hp5⟩
          exact ⟨hb5, hi5, hle1.trans (hle2.trans (hle3.trans (hle4.trans hle5))),
            hp5.trans (hp4.trans hpw)⟩
      · exact writerWP_throw _ _ _ _

/-- The root x, inner and the path's node at `depth`, replaced by its child. -/
theorem kr_replaceRoot (K : KindOracle) (B : NodeId) (x : NodeId) (depth only : Nat)
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (g h : Nat)
    (hx : (x, g, h) ∈ w.gh) (hh : h ≠ 0) :
    WriterWP (replaceRoot x depth only) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold replaceRoot
  krSimp
  refine writerWP_mono (kr_getNode K B x c w hv hk hb hi) ?_
  rintro n w1 ⟨hb1, hi1, hle1, hl1, hp1, -⟩
  have hx1 := KrLe.gh' hx hle1
  split
  · exact writerWP_throw _ _ _ _
  · rename_i child hc
    have hcs := kr_child_seg hi1 hl1 hx1 hh hc
    cases depth with
    | zero =>
      krSimp
      refine writerWP_mono (kr_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kr_unlink K B x c w2 hv hk hb2 hi2) ?_
      rintro _ w3 ⟨hb3, hi3, hle3, hp3⟩
      refine writerWP_mono (kr_newSuperRoot K B child c w3 hv hk hb3 hi3
        ⟨g, hcs.krMono (hle2.trans hle3)⟩) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4, -⟩
      exact ⟨hb4, hi4, hle1.trans (hle2.trans (hle3.trans hle4)),
        hp4.trans (hp3.trans (hp2.trans hp1))⟩
    | succ d =>
      krSimp
      refine writerWP_mono (kr_note K B _ c w1 hv hk hb1 hi1) ?_
      rintro _ w2 ⟨hb2, hi2, hle2, hp2, -⟩
      refine writerWP_mono (kr_pathNode d c w2) ?_
      rintro leaf w2' ⟨hw, a', hla⟩
      subst hw
      refine writerWP_mono (kr_klongAt (d + 1) c w2') ?_
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
        kr_swap hb2 hk hi2 (KrLe.gh' hx1 hle2) hkl (hcs.krMono hle2)
      refine writerWP_mono (kr_unlink K B x c w3 hv hk hb2 hi2) ?_
      rintro _ w4 ⟨hb4, hi4, hle4, hp4⟩
      refine writerWP_mono (kr_appendKlongs K B d leaf' [(k, child)] c w4 hv hk hb4 hi4
        ⟨gl, hl', KrLe.gh' hml hle4, krPairs_cons (hkc.krMono hle4) krPairs_nil'⟩
        ⟨a', by rw [hp4, hpw]; exact hla⟩) ?_
      rintro _ w5 ⟨hb5, hi5, hle5, hp5⟩
      exact ⟨hb5, hi5, hle1.trans (hle2.trans (hle4.trans hle5)), hp5.trans (hp4.trans hpw)⟩

/-- Root collapse. -/
theorem kr_collapseRoot (K : KindOracle) (B : NodeId) (key : Key) (segment fuel : Nat) :
    ∀ (c : Ctx) (w : W), ViewIdsBelow B c.view → ViewKinds K B c → Book B c w → KrInv K B w →
      WriterWP (collapseRoot key segment fuel) c w
        (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v) := by
  induction fuel with
  | zero => intro c w _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro c w hv hk hb hi
    unfold collapseRoot
    krSimp
    refine writerWP_mono (kr_descendToSegmentRoot K B key segment c w hv hk hb hi) ?_
    rintro root w1 ⟨hb1, hi1, hle1, ⟨a, hla⟩⟩
    refine writerWP_mono (kr_getNode K B root c w1 hv hk hb1 hi1) ?_
    rintro n w2 ⟨hb2, hi2, hle2, hl2, hp2, -⟩
    obtain ⟨g, h, hm⟩ := kr_tag_of_lookup hb2 hl2
    have hla2 : w2.path[w2.path.length - 1]? = some (a, root) := by rw [hp2]; exact hla
    have hfin : ∀ (r : Unit) (v : W), Book B c v → KrInv K B v → KrLe w2 v →
        WriterWP (collapseRoot key segment f) c v (fun _ u => Book B c u ∧ KrInv K B u ∧ KrLe w u) := by
      intro r v hbv hiv hlev
      exact writerWP_mono (ih c v hv hk hbv hiv)
        (fun _ u h => ⟨h.1, h.2.1, hle1.trans (hle2.trans (hlev.trans h.2.2))⟩)
    split
    · rw [writerWP_pure]; exact ⟨hb2, hi2, hle1.trans hle2⟩
    · rename_i hleaf
      have hh : h ≠ 0 := by
        intro h0
        subst h0
        have := kr_leaf hb2 hl2 hm
        simp at this
        exact hleaf this
      krSimp
      refine writerWP_mono (kr_replacedBy root c w2) ?_
      rintro r w2' ⟨hw, -⟩
      subst hw
      split
      · rw [writerWP_pure]; exact ⟨hb2, hi2, hle1.trans hle2⟩
      · split
        · rw [writerWP_pure]; exact ⟨hb2, hi2, hle1.trans hle2⟩
        · split
          · exact writerWP_throw _ _ _ _
          · krSimp
            refine writerWP_mono (kr_pathSize c w2') ?_
            rintro sz w3 ⟨hw, hsz⟩
            subst hw
            subst hsz
            split <;> krSimp
            · refine writerWP_mono (kr_takeBackRoot K B root _ _ c w3 hv hk hb2 hi2 a hla2 g h hm hh) ?_
              rintro _ v ⟨hbv, hiv, hlev, -⟩
              exact hfin () v hbv hiv hlev
            · refine writerWP_mono (kr_replaceRoot K B root _ _ c w3 hv hk hb2 hi2 a hla2 g h hm hh) ?_
              rintro _ v ⟨hbv, hiv, hlev, -⟩
              exact hfin () v hbv hiv hlev

/-! ## The merges -/

/-- An inner node's klong names a node of its segment. -/
theorem kr_inner_kl {K : KindOracle} {w : W} {g h c : Nat} {y : NodeId} (hh : h ≠ 0)
    (hy : IsKeySeg K w y g) : KindKlong K w g h c y :=
  ⟨fun _ => hy, fun h0 => absurd h0 hh⟩

/-- Klongs of an inner node that name nodes of its segment. -/
syntax "krKsMP " term:max term:max : tactic
macro_rules
  | `(tactic| krKsMP $hm1 $hm2) => `(tactic| first
    | krKsTac
    | exact krKs_repoint _ (by krKsMP $hm1 $hm2) (fun _ _ _ => kr_inner_kl (by assumption)
        (IsKeySeg.krMono $hm1 (by krChain)))
    | exact krKs_repoint _ (by krKsMP $hm1 $hm2) (fun _ _ _ => kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | exact krKs_add_key _ (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono $hm1 (by krChain)))
    | exact krKs_add_key _ (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | exact krKs_insertSorted _ (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | exact krKs_replaceKlong (by assumption) (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono $hm1 (by krChain)))
    | exact krKs_replaceKlong (by assumption) (by krKsMP $hm1 $hm2) (kr_inner_kl (by assumption)
        (IsKeySeg.krMono ($hm2 _ _ rfl) (by krChain)))
    | (split <;> krKsMP $hm1 $hm2))

macro "krStoreMP " hx:term:max hm1:term:max hm2:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine writerWP_mono (kr_putNode_of ?krK ?krB _ _ _ ?krVr _ _ ?krN ?krBook ?krInv ?krLook ?krKr ?krLeaf _ _ $hx ?krKt ?krKs) ?krPost)
  case krBook => krState
  case krInv => assumption
  case krLook => assumption
  case krKr => krChain
  case krLeaf => first | bkLeaf | (split <;> bkLeaf) | (repeat' split) <;> bkLeaf
  case krKt => krChain
  case krKs => krKsMP $hm1 $hm2
  rintro _ _ ⟨_, _, _, _, _, _⟩))

macro "krHFMP " hx:term:max hm1:term:max hm2:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (refine writerWP_mono (kr_handleFull ?krK ?krB _ _ _ _ _ _ ?krView ?krKinds ?krBook ?krInv _ _ (KrLe.gh' $hx ?krKt) ?krPx ?krLast) ?krPost)
  case krView => assumption
  case krKinds => assumption
  case krBook => krState
  case krInv => assumption
  case krKt => krChain
  case krPx => exact ⟨_, kr_path_at (by assumption) (by krPathEq)⟩
  case krLast => krKsMP $hm1 $hm2
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 6400000 in
/-- The parent p of a merge, inner and the path's node at `depth`, gets klongs
that name m1 and m2, made with the merged nodes' segment, p's. -/
theorem kr_mergeParent (K : KindOracle) (B : NodeId) (p : NodeId) (depth il cL : Nat)
    (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat))
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hb : Book B c w)
    (hi : KrInv K B w) (a : Option Nat) (hpx : w.path[depth]? = some (a, p)) (gp hp : Nat)
    (hx : (p, gp, hp) ∈ w.gh) (hh : hp ≠ 0) (hm1 : IsKeySeg K w m1 gp)
    (hm2 : ∀ y g', m2 = some (y, g') → IsKeySeg K w y gp) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w
      (fun _ v => Book B c v ∧ KrInv K B v ∧ KrLe w v ∧ v.path = w.path) := by
  unfold mergeParent
  repeat' first
    | krSimp
    | krStoreMP hx hm1 hm2
    | krHFMP hx hm1 hm2
    | krCore
    | wpSplit
    | split
    | contradiction

end SIS.Tree
