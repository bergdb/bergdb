/-
The dead klongs' bound kept write by write, with no facts of the tree (bergdb
024-12, section 1, `d4`'s plan of 2026-11-15): `DW`, every key node that the
writer reads holds at most theta dead klongs and well-formed klongs, is kept by
every write that a delete makes but a merge's new nodes (`KeepsDW`). A node is
put only when `deadOver` lets it through, or it is a copy of a node the writer
reads with the same dead klongs or fewer (a repoint, a retarget, the version
before the transaction), or it is made from a last version, which has no dead
klong: a half of a split holds at most the klongs it is given more (at most two
from a cascade), a new root or a time split's copy none.
-/
import SIS.Tree.DeadSteps
import SIS.Tree.MergeFrameDead
import SIS.Tree.WriterTreeMergeOp
import SIS.Tree.SpaceSplitDeadBound
import SIS.Tree.TimeSplitMap
import SIS.Tree.WriterKlongSplits

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every key node that the writer reads holds at most theta dead klongs, and its
klongs are well formed. -/
def DW (c : Ctx) (base : View BVal) (w : W) : Prop :=
  WDeadN c.p (wNode c.p base w) ∧ ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true

/-- A node fit to be read: at most theta dead klongs, klongs well formed. -/
def DOK (p : Params) (m : KNode) : Prop :=
  (p.theta ≠ 0 → m.deadCount ≤ p.theta) ∧ klongsWf m.ks = true

/-- f keeps `DW`, for theta 0 or at least 2. -/
def KeepsDW {α : Type} (base : View BVal) (f : M α) : Prop :=
  ∀ c w, ViewCoherent c base → (2 ≤ c.p.theta ∨ c.p.theta = 0) → DW c base w →
    WriterWP f c w (fun _ v => DW c base v)

theorem dw_node {c : Ctx} {base : View BVal} {w : W} (h : DW c base w) {z : NodeId} {zn : KNode}
    (hz : wNode c.p base w z = some zn) : DOK c.p zn :=
  ⟨fun h0 => h.1 h0 z zn hz, h.2 z zn hz⟩

theorem dw_of_wNode {c : Ctx} {base : View BVal} {w v : W}
    (he : wNode c.p base v = wNode c.p base w) (h : DW c base w) : DW c base v := by
  unfold DW; rw [he]; exact h

theorem dw_same {c : Ctx} {base : View BVal} {w v : W} (hn : v.nodes = w.nodes)
    (ht : v.taken = w.taken) (h : DW c base w) : DW c base v := by
  refine dw_of_wNode ?_ h
  funext z; simp only [wNode, hn, ht]

theorem dw_updN {c : Ctx} {base : View BVal} {w : W} {N : NodeId → Option KNode} (x : NodeId) (m : KNode)
    (hN : N = updN (wNode c.p base w) x m) (h : DW c base w) (hm : DOK c.p m) :
    WDeadN c.p N ∧ ∀ z zn, N z = some zn → klongsWf zn.ks = true := by
  subst hN
  refine ⟨wDeadN_updN c.p _ x m h.1 hm.1, fun z zn hz => ?_⟩
  by_cases hzx : z = x
  · subst hzx; rw [updN_self] at hz; cases hz; exact hm.2
  · rw [updN_ne _ _ _ _ hzx] at hz; exact h.2 z zn hz

/-! ## The primitive steps -/

theorem writerWP_of_dw {α : Type} {base : View BVal} {f : M α} (hf : KeepsDW base f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hvc : ViewCoherent c base)
    (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) (hw : DW c base w)
    (hp : ∀ r v, DW c base v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hvc hth hw) hp

/-- A read: the node read is the one the writer reads, or the id is taken back. -/
theorem dw_getNode (base : View BVal) (x : NodeId) (c : Ctx) (w : W) (hvc : ViewCoherent c base)
    (hw : DW c base w) :
    WriterWP (getNode x) c w (fun n v => DW c base v ∧
      (DOK c.p n ∨ v.taken.contains x = true) ∧ v.nodes.lookup x = some n ∧ v.taken = w.taken) := by
  refine writerWP_mono (writerWP_getNode_all x c w base hvc) ?_
  rintro n v ⟨hr, h2, h3, _, _⟩
  refine ⟨dw_of_wNode hr.1 hw, ?_, h2, hr.2.2.1⟩
  cases ht : v.taken.contains x with
  | true => exact Or.inr rfl
  | false => exact Or.inl (dw_node hw (h3 (by rw [← hr.2.2.1]; exact ht)))

/-- A node put in place: fit, if the id is not taken back. -/
theorem dw_putNode (base : View BVal) (x : NodeId) (m : KNode) (c : Ctx) (w : W)
    (hw : DW c base w) (hm : DOK c.p m ∨ w.taken.contains x = true) :
    WriterWP (putNode x m) c w (fun _ v => DW c base v ∧ v.taken = w.taken) := by
  unfold putNode
  rw [writerWP_modify]
  refine ⟨?_, rfl⟩
  cases hx : w.taken.contains x with
  | false =>
    exact dw_updN x m (wNode_upsert_updN c.p base w _ x m rfl rfl hx) hw
      (hm.resolve_right (by rw [hx]; simp))
  | true =>
    refine dw_of_wNode ?_ hw
    funext z
    simp only [wNode]
    by_cases hz : z = x
    · subst hz; simp only [hx, ↓reduceIte]
    · cases hzt : w.taken.contains z with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, lookup_upsert, hz]

/-- A node made: fit. -/
theorem dw_newKey (base : View BVal) (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hw : DW c base w) (hm : DOK c.p ⟨leaf, ks⟩) :
    WriterWP (newKey g h leaf ks) c w (fun _ v => DW c base v ∧ v.taken = w.taken) := by
  have key : ∀ w' : W, w'.nodes = w.nodes ++ [(w.next, (⟨leaf, ks⟩ : KNode))] → w'.taken = w.taken →
      DW c base w' ∧ w'.taken = w.taken := by
    intro w' h1 h2
    refine ⟨?_, h2⟩
    cases hfree : w.nodes.lookup w.next with
    | none =>
      cases htk : w.taken.contains w.next with
      | false => exact dw_updN _ _ (wNode_append_updN c.p base w w' ⟨leaf, ks⟩ h1 h2 hfree htk) hw hm
      | true =>
        refine dw_of_wNode ?_ hw
        funext z
        simp only [wNode, h1, h2]
        cases hzt : w.taken.contains z with
        | true => rfl
        | false =>
          have hz : z ≠ w.next := fun he => by rw [he, htk] at hzt; cases hzt
          simp only [Bool.false_eq_true, ↓reduceIte, List.lookup_append]
          cases hl : w.nodes.lookup z with
          | some _ => rfl
          | none => simp [List.lookup, show (z == w.next) = false from by simpa using hz]
    | some n0 =>
      refine dw_of_wNode ?_ hw
      funext z
      simp only [wNode, h1, h2]
      cases hzt : w.taken.contains z with
      | true => rfl
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, List.lookup_append]
        cases hl : w.nodes.lookup z with
        | some _ => rfl
        | none =>
          have hz : z ≠ w.next := fun he => by rw [he, hfree] at hl; cases hl
          simp [List.lookup, show (z == w.next) = false from by simpa using hz]
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  split <;>
  · (try simp only [writerWP_modify, writerWP_pure, writerWP_bind])
    first
      | exact key _ rfl rfl
      | (refine ⟨(key _ ?_ ?_).1, trivial⟩ <;> rfl)

/-- An id taken back: the writer reads fewer nodes. -/
theorem dw_takenBack (base : View BVal) (x : NodeId) (c : Ctx) (w : W) (hw : DW c base w) :
    WriterWP (takenBack x) c w (fun _ v => DW c base v) := by
  unfold takenBack
  rw [writerWP_modify]
  have hsub : ∀ z zn, wNode c.p base { w with taken := x :: w.taken } z = some zn →
      wNode c.p base w z = some zn := by
    intro z zn hz
    unfold wNode at hz ⊢
    simp only [List.contains_cons] at hz
    cases hzt : w.taken.contains z with
    | true => rw [hzt] at hz; simp at hz
    | false =>
      rw [hzt] at hz
      simp only [Bool.or_false] at hz
      cases hzx : (z == x) with
      | true => rw [hzx] at hz; simp at hz
      | false => rw [hzx] at hz; simpa using hz
  exact ⟨fun h0 z zn hz => hw.1 h0 z zn (hsub z zn hz), fun z zn hz => hw.2 z zn (hsub z zn hz)⟩

/-! ## Nodes fit to be read -/

/-- A last version at time t: a time klong, then key klongs in strict compare order. -/
def NormKs (t : Time) (ks : List Klong) : Prop :=
  ∃ pairs, ks = newKlongs t pairs ∧ CvSorted pairs

theorem normKs_lastVersionGivenDel (n : KNode) (t : Time) (bits : List Nat) :
    NormKs t (n.lastVersionGivenDel t bits).ks := by
  obtain ⟨pairs, hp, hs⟩ := n.lastVersionGivenDel_order t bits
  exact ⟨pairs, hp, hs⟩

theorem normKs_lastVersion (n : KNode) (t : Time) : NormKs t (n.lastVersion t).ks :=
  normKs_lastVersionGivenDel n t _

theorem dok_or_of {p : Params} {n m : KNode} {T : Prop} (h : DOK p n → DOK p m) :
    DOK p n ∨ T → DOK p m ∨ T := fun h' => h'.imp_left h

theorem dok_nil (p : Params) (leaf : Bool) : DOK p ⟨leaf, []⟩ :=
  ⟨fun _ => Nat.zero_le _, rfl⟩

theorem dok_newKlongs (p : Params) (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hn : (pairs.map Prod.fst).Nodup) : DOK p ⟨leaf, newKlongs t pairs⟩ :=
  ⟨fun _ => by rw [KNode.newKlongs_deadCount leaf t pairs hn]; exact Nat.zero_le _,
    klongsWf_newKlongs t pairs⟩

theorem dok_root (p : Params) (t : Time) (a b : NodeId) (sc : Nat) :
    DOK p ⟨false, [Klong.time t, .key 0 a, .key sc b]⟩ := by
  refine ⟨fun h0 => ?_, klongsWf_newKlongs t [(0, a), (sc, b)]⟩
  have h := KNode.newKlongs_append_deadCount_le false t [(0, a)] [(sc, b)] (by simp)
  have : (⟨false, [Klong.time t, .key 0 a, .key sc b]⟩ : KNode) = ⟨false, newKlongs t ([(0, a)] ++ [(sc, b)])⟩ :=
    rfl
  rw [this]
  simp only [List.length_singleton] at h
  omega

theorem dok_halves (p : Params) (hth : 2 ≤ p.theta ∨ p.theta = 0) (leaf : Bool) (t : Time) (last : KNode)
    (ins : List (Nat × NodeId)) (hlast : NormKs t last.ks) (hins : ins.length ≤ 2) :
    DOK p (halves leaf t last ins).1 ∧ DOK p (halves leaf t last ins).2.1 := by
  obtain ⟨pairs, hks, hs⟩ := hlast
  have he : halves leaf t last ins = halves leaf t ⟨leaf, newKlongs t pairs⟩ ins := by
    rw [← hks]; rfl
  have hwf := halves_flat_wf leaf t last ins ⟨t, pairs, hks⟩
  obtain ⟨h1, h2⟩ := halves_deadCount_le_inserts leaf t pairs ins hs
  rw [← he] at h1 h2
  exact ⟨⟨fun _ => by omega, hwf.1⟩, ⟨fun _ => by omega, hwf.2⟩⟩

theorem dok_repoint {p : Params} {n : KNode} (i : Nat) (y : NodeId) (h : DOK p n) :
    DOK p (n.repoint i y) :=
  ⟨fun h0 => by rw [KNode.deadCount_repoint]; exact h.1 h0, by rw [KNode.repoint_klongsWf]; exact h.2⟩

theorem dok_toPrev {p : Params} {n : KNode} (t : Time) (h : DOK p n) : DOK p (n.toPrev t) :=
  ⟨fun h0 => Nat.le_trans (KNode.deadCount_toPrev_le n t h.2) (h.1 h0), KNode.toPrev_wf n t h.2⟩

theorem dok_ks {p : Params} {l : KNode} (b : Bool) (t : Time)
    (h : ∃ more, l.ks = newKlongs t more ∧ (more.map Prod.fst).Nodup) : DOK p ⟨b, l.ks⟩ := by
  obtain ⟨more, hks, hn⟩ := h
  rw [hks]; exact dok_newKlongs p b t more hn

/-! ## The steps that change no node -/

theorem dw_frame {α : Type} (base : View BVal) (f : M α) (c : Ctx) (w : W)
    (h : WriterWP f c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken)) (hw : DW c base w) :
    WriterWP f c w (fun _ v => DW c base v ∧ v.taken = w.taken) :=
  writerWP_mono h (fun _ v hv => ⟨dw_same hv.1 hv.2 hw, hv.2⟩)

theorem fr_note (s : String) (c : Ctx) (w : W) :
    WriterWP (note s) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold note; rw [writerWP_modify]; exact ⟨rfl, rfl⟩

theorem fr_fresh (c : Ctx) (w : W) :
    WriterWP fresh c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold fresh; wpSimplify; first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp

theorem fr_setMadeFor (x : NodeId) (o : Option NodeId) (c : Ctx) (w : W) :
    WriterWP (setMadeFor x o) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold setMadeFor; split <;> wpSimplify <;> first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp

theorem fr_replacedBy (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (replacedBy x) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold replacedBy; wpSimplify; first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp

theorem fr_pathNode (d : Nat) (c : Ctx) (w : W) :
    WriterWP (pathNode d) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold pathNode; wpSimplify; split
  · wpSimplify; first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp
  · exact writerWP_throw _ _ _ _

theorem fr_klongAt (d : Nat) (c : Ctx) (w : W) :
    WriterWP (klongAt d) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold klongAt; wpSimplify; split
  · wpSimplify; first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp
  · exact writerWP_throw _ _ _ _

theorem fr_parentAt (d : Nat) (c : Ctx) (w : W) :
    WriterWP (parentAt d) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  cases d with
  | zero => unfold parentAt; wpSimplify; first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp
  | succ d =>
    unfold parentAt; rw [writerWP_bind]
    exact writerWP_mono (fr_pathNode d c w) (fun _ v hv => by wpSimplify; exact hv)

theorem fr_newSuperRoot (y : NodeId) (c : Ctx) (w : W) :
    WriterWP (newSuperRoot y) c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold newSuperRoot fresh note; wpSimplify; split <;> (try wpSimplify) <;>
    first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp

theorem fr_spaceSplits (c : Ctx) (w : W) :
    WriterWP (modify (fun w => { w with spaceSplits := w.spaceSplits + 1 }) : M Unit) c w
      (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  rw [writerWP_modify]; exact ⟨rfl, rfl⟩

theorem fr_merges (c : Ctx) (w : W) :
    WriterWP (modify (fun w => { w with merges := w.merges + 1 }) : M Unit) c w
      (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  rw [writerWP_modify]; exact ⟨rfl, rfl⟩

/-- `ghOf` reads x's node and the heights' cache. -/
theorem dw_ghOf (base : View BVal) (x : NodeId) (c : Ctx) (w : W) (hvc : ViewCoherent c base)
    (hw : DW c base w) :
    WriterWP (ghOf x) c w (fun _ v => DW c base v ∧ v.taken = w.taken) := by
  unfold ghOf
  rw [writerWP_bind]
  refine writerWP_mono (dw_getNode base x c w hvc hw) ?_
  rintro _ v ⟨hv, _, _, ht⟩
  wpSimplify
  split
  · wpSimplify; exact ⟨hv, ht⟩
  · exact writerWP_throw _ _ _ _

/-! ## The splits and the cascade -/

/-- A node written by a split fit to be read: a half, a new root, a node with no
klong, a time split's copy, a repoint or the version before the transaction of a
node the writer reads. -/
macro "dwOK" : tactic => `(tactic| first
  | exact Or.inl (dok_halves _ (by assumption) _ _ _ _ (by assumption) (by assumption)).1
  | exact Or.inl (dok_halves _ (by assumption) _ _ _ _ (by assumption) (by assumption)).2
  | exact Or.inl (dok_root _ _ _ _ _)
  | exact Or.inl (dok_nil _ _)
  | exact Or.inl (dok_ks _ _ (by assumption))
  | exact dok_or_of (dok_repoint _ _) (by assumption)
  | exact dok_or_of (dok_toPrev _) (by assumption)
  | exact (dok_halves _ (by assumption) _ _ _ _ (by assumption) (by assumption)).1
  | exact (dok_halves _ (by assumption) _ _ _ _ (by assumption) (by assumption)).2
  | exact dok_root _ _ _ _ _
  | exact dok_nil _ _
  | exact dok_ks _ _ (by assumption))

/-- One step of the walk that keeps `DW`. -/
macro "dwStep" : tactic => `(tactic| first
  | simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure]
  | ((with_unfolding_none guard_target = WriterWP (throw _) _ _ _)
     exact writerWP_throw _ _ _ _)
  | ((with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
     refine writerWP_mono (dw_getNode _ _ _ _ (by assumption) (by assumption)) ?_
     rintro _ _ ⟨_, _, _, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
     refine writerWP_mono (dw_putNode _ _ _ _ _ (by assumption) (by dwOK)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
     refine writerWP_mono (dw_newKey _ _ _ _ _ _ _ (by assumption) (by dwOK)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (note _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_note _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
     refine writerWP_mono (dw_ghOf _ _ _ _ (by assumption) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (setMadeFor _ _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_setMadeFor _ _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_replacedBy _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_pathNode _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (klongAt _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_klongAt _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (parentAt _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_parentAt _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (newSuperRoot _) _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_newSuperRoot _ _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP fresh _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_fresh _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (modify _) _ _ _)
     first
       | (refine writerWP_mono (dw_frame _ _ _ _ (fr_spaceSplits _ _) (by assumption)) ?_
          rintro _ _ ⟨_, _⟩)
       | (refine writerWP_mono (dw_frame _ _ _ _ (fr_merges _ _) (by assumption)) ?_
          rintro _ _ ⟨_, _⟩))
  | ((with_unfolding_none guard_target = WriterWP (ite _ _ _) _ _ _)
     wpSplit)
  | ((with_unfolding_none guard_target = WriterWP (pure _) _ _ _)
     simp only [writerWP_pure])
  | assumption)


end SIS.Tree
