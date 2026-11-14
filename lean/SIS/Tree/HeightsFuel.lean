/-
Step 4 (B) (bergdb 024-22; 024-12's (4)): inside an operation a split's
cascade adds at most one to the heights. The writer caches every key node's
height (`gh`); `SeenHeightBound b w` bounds them all by b. A cascade
(`handleFullWith`, `appendKlongs`, `handleFull`) up the key access path, whose
nodes are all below b, keeps every height at most b: a split's new nodes have
the split node's height, a new root one more (`sb_appendKlongs`).
-/
import SIS.Tree.MergeHeightOrigins
import SIS.Tree.WriterKindsRules
import SIS.Tree.OverlayHeights

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The walk's state from w0: every cached height at most b; the next id and
the path as at w0 or later; the heights of ids below w0's next id are those of
w0, or of nodes of the view (at most H). -/
def SBInv (p : Params) (b : Nat) (w0 v : W) : Prop :=
  SeenHeightBound b v ∧ w0.next ≤ v.next ∧ v.path = w0.path ∧
  ∀ x g h, (x, g, h) ∈ v.gh → x < w0.next → (x, g, h) ∈ w0.gh ∨ h ≤ p.H

theorem SBInv.refl {p : Params} {b : Nat} {w : W} (h : SeenHeightBound b w) : SBInv p b w w :=
  ⟨h, Nat.le_refl _, rfl, fun _ _ _ hm _ => Or.inl hm⟩

/-- The path's nodes are ids below the next one, of heights below b. -/
def PathBelowSB (b : Nat) (w0 : W) : Prop :=
  ∀ (d : Nat) (a : Option Nat) (q : NodeId), w0.path[d]? = some (a, q) →
    q < w0.next ∧ ∀ g h, (q, g, h) ∈ w0.gh → h < b

/-- `SBInv` with the bound asked only of the ids that S picks (bergdb 024-22,
for the fuel after a delete's cascade: S the ids not taken back at w0). The
cascade's lemmas below are proved for every S; `SBInv` is the case S = every
id (`sbInv_iff_S`), and its lemmas follow. -/
def SBInvS (p : Params) (b : Nat) (S : NodeId → Prop) (w0 v : W) : Prop :=
  (∀ x g h, (x, g, h) ∈ v.gh → S x → h ≤ b) ∧ w0.next ≤ v.next ∧ v.path = w0.path ∧
  ∀ x g h, (x, g, h) ∈ v.gh → x < w0.next → (x, g, h) ∈ w0.gh ∨ h ≤ p.H

theorem sbInv_iff_S {p : Params} {b : Nat} {w0 v : W} :
    SBInv p b w0 v ↔ SBInvS p b (fun _ => True) w0 v := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨fun x g h hm _ => h1 x g h hm, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨fun x g h hm => h1 x g h hm trivial, h2, h3, h4⟩

def KeepsSBS (b : Nat) (S : NodeId → Prop) {α : Type} (f : M α) : Prop :=
  ∀ c w0 w, c.p.H < b → SBInvS c.p b S w0 w → WriterWP f c w (fun _ v => SBInvS c.p b S w0 v)

theorem writerWP_of_sbS {α : Type} {b : Nat} {S : NodeId → Prop} {f : M α} (hf : KeepsSBS b S f)
    (c : Ctx) (w0 w : W) (post : α → W → Prop) (hH : c.p.H < b) (hw : SBInvS c.p b S w0 w)
    (hp : ∀ r v, SBInvS c.p b S w0 v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w0 w hH hw) hp

section General

variable {S : NodeId → Prop}

/-- A step that keeps the cached heights and the path, the next id not lower. -/
theorem sbS_of_frame {α : Type} {b : Nat} {f : M α}
    (hf : ∀ c w, WriterWP f c w (fun _ v => v.gh = w.gh ∧ v.path = w.path ∧ w.next ≤ v.next)) :
    KeepsSBS b S f := by
  intro c w0 w _ hw
  refine writerWP_mono (hf c w) ?_
  rintro _ v ⟨hg, hp, hn⟩
  obtain ⟨h1, h2, h3, h4⟩ := hw
  refine ⟨fun x g h hm hs => h1 x g h (by rw [← hg]; exact hm) hs, Nat.le_trans h2 hn, hp.trans h3,
    fun x g h hm hx => h4 x g h (by rw [← hg]; exact hm) hx⟩

macro "sbFrameTac" : tactic => `(tactic| (
  intro c w
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
        writerWP_set, writerWP_modify, note, fresh, putNode, newValue,
        setMadeFor, replacedBy, takenBack, pathSize, pathNode,
        klongAt, parentAt, newSuperRoot, addKeys]
    | exact writerWP_throw _ _ _ _
    | (refine ⟨?_, ?_, ?_⟩ <;> first | rfl | trivial | exact Nat.le_refl _ | omega)
    | wpSplit
    | split
    | contradiction))

theorem sbS_note (b : Nat) (s : String) : KeepsSBS b S (note s) := sbS_of_frame (by sbFrameTac)
theorem sbS_fresh (b : Nat) : KeepsSBS b S fresh := sbS_of_frame (by sbFrameTac)
theorem sbS_putNode (b : Nat) (x : NodeId) (n : KNode) : KeepsSBS b S (putNode x n) :=
  sbS_of_frame (by sbFrameTac)
theorem sbS_setMadeFor (b : Nat) (x : NodeId) (o : Option NodeId) :
    KeepsSBS b S (setMadeFor x o) :=
  sbS_of_frame (by sbFrameTac)
theorem sbS_replacedBy (b : Nat) (x : NodeId) : KeepsSBS b S (replacedBy x) :=
  sbS_of_frame (by sbFrameTac)
theorem sbS_pathNode (b : Nat) (d : Nat) : KeepsSBS b S (pathNode d) :=
  sbS_of_frame (by sbFrameTac)
theorem sbS_klongAt (b : Nat) (d : Nat) : KeepsSBS b S (klongAt d) := sbS_of_frame (by sbFrameTac)
theorem sbS_newSuperRoot (b : Nat) (y : NodeId) : KeepsSBS b S (newSuperRoot y) :=
  sbS_of_frame (by sbFrameTac)

theorem sbS_replaceOrAdd (b : Nat) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsSBS b S (replaceOrAdd last ins) := by
  refine sbS_of_frame ?_
  intro c w
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  generalize last = l0
  induction ins generalizing l0 with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨by trivial, by trivial, Nat.le_refl _⟩
  | cons q ins ih =>
    rw [List.foldlM_cons, writerWP_bind]
    split
    · exact writerWP_throw _ _ _ _
    · rw [writerWP_pure]; exact ih _
    · rw [writerWP_pure]; exact ih _

theorem sbS_getNode (b : Nat) (x : NodeId) : KeepsSBS b S (getNode x) := by
  intro c w0 w hH hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]; exact ⟨h1, h2, h3, h4⟩
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, h2, h3, ?_⟩
        · intro a g d hd hs
          simp only [List.mem_cons, Prod.mk.injEq] at hd
          rcases hd with ⟨rfl, rfl, rfl⟩ | hd
          · exact Nat.le_of_lt (Nat.lt_of_le_of_lt (heightOf_le c.p _) hH)
          · exact h1 a g d hd hs
        · intro a g d hd ha
          simp only [List.mem_cons, Prod.mk.injEq] at hd
          rcases hd with ⟨rfl, rfl, rfl⟩ | hd
          · exact Or.inr (heightOf_le c.p _)
          · exact h4 a g d hd ha
    · exact writerWP_throw _ _ _ _

theorem sbS_ghOf (b : Nat) (x : NodeId) (c : Ctx) (w0 w : W) (hH : c.p.H < b)
    (hw : SBInvS c.p b S w0 w) :
    WriterWP (ghOf x) c w (fun r v => SBInvS c.p b S w0 v ∧ (x, r.1, r.2) ∈ v.gh) := by
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (sbS_getNode b x c w0 w hH hw) ?_
  intro _ v hv
  simp only [writerWP_get]
  split
  · rename_i gh hh
    simp only [writerWP_pure]
    exact ⟨hv, gh_lookup_mem hh⟩
  · exact writerWP_throw _ _ _ _

theorem sbS_newKey (b : Nat) (g h : Nat) (leaf : Bool) (ks : List Klong) (hh : h ≤ b) :
    KeepsSBS b S (newKey g h leaf ks) := by
  intro c w0 w _ hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    refine ⟨?_, by dsimp only; omega, h3, ?_⟩
    · intro a g' d hd hs
      simp only [List.mem_cons, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl, rfl⟩ | hd
      · exact hh
      · exact h1 a g' d hd hs
    · intro a g' d hd ha
      simp only [List.mem_cons, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl, rfl⟩ | hd
      · omega
      · exact h4 a g' d hd ha

/-- A node of the path has its heights below b at every later state. -/
theorem sbS_path_lt {p : Params} {b : Nat} {w0 v : W} (hH : p.H < b) (hv : SBInvS p b S w0 v)
    (hpb : PathBelowSB b w0) {d : Nat} {a : Option Nat} {q : NodeId}
    (hq : w0.path[d]? = some (a, q)) {g h : Nat} (hm : (q, g, h) ∈ v.gh) : h < b := by
  obtain ⟨hlt, hall⟩ := hpb d a q hq
  rcases hv.2.2.2 q g h hm hlt with h0 | h0
  · exact hall g h h0
  · omega

theorem SBInvS.trans {p : Params} {b : Nat} {w0 v u : W} (h1 : SBInvS p b S w0 v)
    (h2 : SBInvS p b S v u) : SBInvS p b S w0 u := by
  obtain ⟨a1, a2, a3, a4⟩ := h1
  obtain ⟨b1, b2, b3, b4⟩ := h2
  refine ⟨b1, Nat.le_trans a2 b2, b3.trans a3, ?_⟩
  intro x g h hm hx
  rcases b4 x g h hm (Nat.lt_of_lt_of_le hx a2) with h0 | h0
  · exact a4 x g h h0 hx
  · exact Or.inr h0

theorem SBInvS.congr {p : Params} {b : Nat} {w0 v v' : W} (h : SBInvS p b S w0 v)
    (hg : v'.gh = v.gh) (hp : v'.path = v.path) (hn : v'.next = v.next) : SBInvS p b S w0 v' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun x g k hm hs => h1 x g k (by rw [← hg]; exact hm) hs, by rw [hn]; exact h2,
    hp.trans h3, fun x g k hm hx => h4 x g k (by rw [← hg]; exact hm) hx⟩

end General

macro "sbsState" : tactic => `(tactic| first
  | assumption
  | exact SBInvS.congr (by assumption) rfl rfl rfl)

macro "sbsUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_sbS $h _ _ _ _ (by assumption) (by sbsState) ?sbPost)
  intro _ _ _))

macro "sbsCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_sbS (S := ?sbSet) (sbS_newKey ?sbB _ _ _ _ ?sbH) _ ?sbW0 _ _ ?sbHH ?sbS ?sbPost)
  case sbS => sbsState
  case sbHH => assumption
  case sbH => first | omega | (dsimp only at *; omega)
  intro _ _ _))

macro "sbsCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | sbsUse (sbS_getNode _ _)
  | sbsUse (sbS_note _ _)
  | sbsUse (sbS_fresh _)
  | sbsUse (sbS_putNode _ _ _)
  | sbsUse (sbS_setMadeFor _ _ _)
  | sbsUse (sbS_replacedBy _ _)
  | sbsUse (sbS_pathNode _ _)
  | sbsUse (sbS_klongAt _ _)
  | sbsUse (sbS_newSuperRoot _ _)
  | sbsUse (sbS_replaceOrAdd _ _ _)
  | sbsCreate
  | sbsState)

section GeneralCascade

variable {S : NodeId → Prop}

set_option maxHeartbeats 2000000 in
/-- A full node's split, and its cascade up the path: every height of the ids
S picks stays at most b when the path's nodes are below b. -/
theorem sbS_handleFullWith (b : Nat) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w0 w : W) (hH : c.p.H < b) (hw : SBInvS c.p b S w0 w) (hpb : PathBelowSB b w0)
    (a : Option Nat) (hpx : w0.path[depth]? = some (a, x))
    (hup : ∀ e, depth = e + 1 → ∀ q more v, SBInvS c.p b S w0 v →
      (∃ a', w0.path[e]? = some (a', q)) →
      WriterWP (up q more) c v (fun _ v' => SBInvS c.p b S w0 v')) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => SBInvS c.p b S w0 v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (sbS_getNode b x c w0 w hH hw) ?_
  intro n w1 hw1
  refine writerWP_mono (sbS_ghOf b x c w0 w1 hH hw1) ?_
  rintro ⟨g, h⟩ w2 ⟨hw2, hm2⟩
  have hhb : h < b := sbS_path_lt hH hw2 hpb hpx hm2
  refine writerWP_mono (kd_parentAt depth c w2) ?_
  rintro parent _ ⟨rfl, hpar0, hpar1⟩
  cases depth with
  | zero =>
    obtain rfl := hpar0 rfl
    clear hpar1 hup
    repeat' first
      | wpSimplify
      | sbsCore
      | wpSplit
      | split
      | contradiction
  | succ e =>
    obtain ⟨a', q, rfl, hpe⟩ := hpar1 e rfl
    have hpe0 : w0.path[e]? = some (a', q) := by rw [← hw2.2.2.1]; exact hpe
    have hup' := hup e rfl
    clear hup
    repeat' first
      | wpSimplify
      | sbsCore
      | (refine writerWP_mono (hup' q _ _ (by sbsState) ⟨a', hpe0⟩) ?_; intro _ _ _)
      | wpSplit
      | split
      | contradiction

theorem sbS_addKeys (b : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsSBS b S (addKeys x ins) := by
  intro c w0 w hH hw
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (sbS_getNode b x c w0 w hH hw) ?_
  intro n v hv
  exact sbS_putNode b x _ c w0 v hH hv

/-- `appendKlongs` up the path. -/
theorem sbS_appendKlongs (b : Nat) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w0 w : W), c.p.H < b →
      SBInvS c.p b S w0 w → PathBelowSB b w0 → (∃ a, w0.path[depth]? = some (a, x)) →
      WriterWP (appendKlongs depth x ins) c w (fun _ v => SBInvS c.p b S w0 v) := by
  induction depth with
  | zero =>
    intro x ins c w0 w hH hw hpb ⟨a, hpx⟩
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (sbS_getNode b x c w0 w hH hw) ?_
    intro n v hv
    have hfin : ∀ cp, WriterWP (handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0")
        0 x ins (n.lastVersion c.i) cp) c v (fun _ u => SBInvS c.p b S w0 u) :=
      fun cp => sbS_handleFullWith b _ 0 x ins _ cp c w0 v hH hv hpb a hpx (fun e he => by cases he)
    split
    · exact hfin false
    · split
      · exact hfin true
      · exact sbS_addKeys b x ins c w0 v hH hv
  | succ d ih =>
    intro x ins c w0 w hH hw hpb ⟨a, hpx⟩
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (sbS_getNode b x c w0 w hH hw) ?_
    intro n v hv
    have hup : ∀ e, d + 1 = e + 1 → ∀ q more u, SBInvS c.p b S w0 u →
        (∃ a', w0.path[e]? = some (a', q)) →
        WriterWP ((fun q more => appendKlongs d q more) q more) c u
          (fun _ u' => SBInvS c.p b S w0 u') := by
      intro e he q more u hu hq
      cases he
      exact ih q more c w0 u hH hu hpb hq
    have hfin : ∀ cp, WriterWP (handleFullWith (fun q more => appendKlongs d q more)
        (d + 1) x ins (n.lastVersion c.i) cp) c v (fun _ u => SBInvS c.p b S w0 u) :=
      fun cp => sbS_handleFullWith b _ (d + 1) x ins _ cp c w0 v hH hv hpb a hpx hup
    split
    · exact hfin false
    · split
      · exact hfin true
      · exact sbS_addKeys b x ins c w0 v hH hv

/-- `handleFull` at the path's node at depth. -/
theorem sbS_handleFull (b : Nat) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w0 w : W) (hH : c.p.H < b) (hw : SBInvS c.p b S w0 w) (hpb : PathBelowSB b w0)
    (a : Option Nat) (hpx : w0.path[depth]? = some (a, x)) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => SBInvS c.p b S w0 v) := by
  unfold handleFull
  refine sbS_handleFullWith b _ depth x [] last compact c w0 w hH hw hpb a hpx ?_
  intro e he q more u hu hq
  subst he
  exact sbS_appendKlongs b e q more c w0 u hH hu hpb hq

/-- A delete's bitmap at the path's node at depth, a cascade when the node is
full: every height of the ids S picks stays at most b when the path's nodes are
below b. -/
theorem sbS_appendDeleteKlong (b : Nat) (x : NodeId) (depth cv : Nat) (c : Ctx) (w0 w : W)
    (hH : c.p.H < b) (hw : SBInvS c.p b S w0 w) (hpb : PathBelowSB b w0) (a : Option Nat)
    (hpx : w0.path[depth]? = some (a, x)) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ v => SBInvS c.p b S w0 v) := by
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | sbsCore
    | (refine writerWP_mono (sbS_handleFull b depth x _ _ c w0 _ hH (by sbsState) hpb a hpx) ?_;
       intro _ _ _)
    | wpSplit
    | split
    | contradiction

end GeneralCascade

/-! ## Every id: `SBInv` -/

theorem SBInv.trans {p : Params} {b : Nat} {w0 v u : W} (h1 : SBInv p b w0 v) (h2 : SBInv p b v u) :
    SBInv p b w0 u :=
  sbInv_iff_S.mpr ((sbInv_iff_S.mp h1).trans (sbInv_iff_S.mp h2))

theorem SBInv.congr {p : Params} {b : Nat} {w0 v v' : W} (h : SBInv p b w0 v) (hg : v'.gh = v.gh)
    (hp : v'.path = v.path) (hn : v'.next = v.next) : SBInv p b w0 v' :=
  sbInv_iff_S.mpr ((sbInv_iff_S.mp h).congr hg hp hn)

/-- `appendKlongs` up the path: every height stays at most b when the path's
nodes are below b. -/
theorem sb_appendKlongs (b : Nat) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w0 w : W), c.p.H < b →
      SBInv c.p b w0 w → PathBelowSB b w0 → (∃ a, w0.path[depth]? = some (a, x)) →
      WriterWP (appendKlongs depth x ins) c w (fun _ v => SBInv c.p b w0 v) :=
  fun x ins c w0 w hH hw hpb hx => writerWP_mono
    (sbS_appendKlongs b depth x ins c w0 w hH (sbInv_iff_S.mp hw) hpb hx)
    (fun _ _ h => sbInv_iff_S.mpr h)

/-- The cascade's bound from a state: every cached height at most m, H at most
m, and the path's nodes cached ids: after it every height is at most m + 1. -/
theorem pathBelowSB_of {B : NodeId} {c : Ctx} {w : W} {m : Nat} (hb : Book B c w)
    (hs : SeenHeightBound m w)
    (hpg : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1)) :
    PathBelowSB (m + 1) w := by
  intro d a q hq
  obtain ⟨⟨q', g, h⟩, hm, he⟩ := List.mem_map.mp (hpg d a q hq)
  simp only at he
  subst he
  exact ⟨hb.bound _ hm, fun g' h' hm' => Nat.lt_succ_of_le (hs _ _ _ hm')⟩

/-- SegFits from the cached heights: every reached node of the writer's tree
has its segment tree of depth at most b when the heights are at most b. -/
theorem segFits_of_seenHeight {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W}
    (hb : Book B c w) (hc : HtCache c H w) (hvh : ViewHeights H B c) (base : View BVal)
    (hbase : BaseHeights c H base) (b : Nat) (r : NodeId) (hs : SeenHeightBound b w)
    (hHb : ∀ y h, H y h → h ≤ b) :
    SegFits (wNode c.p base w) c.i b r :=
  segFits_of_heights hb hc hvh base hbase b r (fun x _ h hx => by
    rcases hx with ⟨g, hm⟩ | hx
    · exact hs x g h hm
    · exact hHb x h hx)

theorem SeenHeightBound.mono {b b' : Nat} {w : W} (h : SeenHeightBound b w) (hb : b ≤ b') :
    SeenHeightBound b' w := fun x g k hm => Nat.le_trans (h x g k hm) hb

/-- (B) for a put's klongs (`appendKlongs` at the path's node at depth): the
same bound. -/
theorem seenHeight_appendKlongs {B : NodeId} {c : Ctx} {w : W} {m : Nat} (hb : Book B c w)
    (hs : SeenHeightBound m w) (hHm : c.p.H ≤ m)
    (hpg : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
      q ∈ w.gh.map (·.1))
    (x : NodeId) (depth : Nat) (ins : List (Nat × NodeId)) (a : Option Nat)
    (hpx : w.path[depth]? = some (a, x)) :
    WriterWP (appendKlongs depth x ins) c w (fun _ v => SeenHeightBound (m + 1) v) :=
  writerWP_mono (sb_appendKlongs (m + 1) depth x ins c w w (by omega)
    (SBInv.refl (hs.mono (Nat.le_succ m))) (pathBelowSB_of hb hs hpg) ⟨a, hpx⟩) (fun _ _ h => h.1)

end SIS.Tree
