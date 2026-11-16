/-
The hole's form for `l4` (bergdb 030-01, step 2): the live counts inside a
delete with the merges. After the leaf's change one node may be under the fill,
the hole; a merge into one node moves it to the parent, one height up; the loop
of the merges ends with no hole or with the hole at the segment's root, which
root collapse closes (030-01, section 2.3; checked on runs by step 0's
live-inside-check).

`LiveEdgesH ... Hl` is `LiveEdges` (LiveEdgesBase.lean) but at the nodes of Hl:
a link to such a node asks only a live klong of it, and the space root, if it is
one, only `RootOK`'s first half. With Hl empty it is `LiveEdges`
(`liveEdgesH_iff`). `HoleAt key g h` is the node of segment g at height h on
the key's path: the node that the merges' loop's descent finds. A merge into
one node of two siblings, one of them the hole, keeps the form with the parent
as the hole (`liveEdgesH_mergeOne`).
-/
import SIS.Tree.LiveStepsX
import SIS.Tree.LiveEdges
import SIS.Tree.WriterTreeMergeFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `LiveEdges` but at the holes Hl: a link to a hole asks only a live klong of
it; the space root asks two live klongs if it is inner only when it is no hole. -/
def LiveEdgesH (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (Hl : NodeId → Prop) : Prop :=
  (∀ rn, N r = some rn → (rn.liveAt t = [] → rn.leaf = true) ∧
    (¬ Hl r → rn.leaf = false → 2 ≤ (rn.liveAt t).length)) ∧
  ∀ u un c y yn, TReach N t r u → N u = some un → (c, y) ∈ un.liveAt t → N y = some yn →
    (¬ Hl y → ChildOK p t un yn) ∧ (Hl y → yn.liveAt t ≠ [])

theorem liveEdgesH_of_liveEdges (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (Hl : NodeId → Prop) (h : LiveEdges p N t r) : LiveEdgesH p N t r Hl :=
  ⟨fun rn hrn => ⟨(h.1 rn hrn).1, fun _ => (h.1 rn hrn).2⟩,
    fun u un c y yn hu hun hc hyn => ⟨fun _ => h.2 u un c y yn hu hun hc hyn,
      fun _ => (h.2 u un c y yn hu hun hc hyn).1⟩⟩

/-- With no hole, the form is `LiveEdges`. -/
theorem liveEdgesH_iff (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId) :
    LiveEdgesH p N t r (fun _ => False) ↔ LiveEdges p N t r := by
  constructor
  · intro h
    exact ⟨fun rn hrn => ⟨(h.1 rn hrn).1, (h.1 rn hrn).2 id⟩,
      fun u un c y yn hu hun hc hyn => (h.2 u un c y yn hu hun hc hyn).1 id⟩
  · exact liveEdgesH_of_liveEdges p N t r _

/-- More holes, a weaker form. -/
theorem liveEdgesH_mono (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (Hl Hl' : NodeId → Prop) (hsub : ∀ y, Hl y → Hl' y)
    (hne : ∀ u un c y yn, TReach N t r u → N u = some un → (c, y) ∈ un.liveAt t → N y = some yn →
      Hl' y → ¬ Hl y → yn.liveAt t ≠ [])
    (h : LiveEdgesH p N t r Hl) : LiveEdgesH p N t r Hl' := by
  refine ⟨fun rn hrn => ⟨(h.1 rn hrn).1, fun hn => (h.1 rn hrn).2 (fun h' => hn (hsub _ h'))⟩,
    fun u un c y yn hu hun hc hyn => ⟨fun hn => (h.2 u un c y yn hu hun hc hyn).1
      (fun h' => hn (hsub _ h')), fun hH => ?_⟩⟩
  by_cases h0 : Hl y
  · exact (h.2 u un c y yn hu hun hc hyn).2 h0
  · exact hne u un c y yn hu hun hc hyn hH h0

/-- A hole that meets `ChildOK` at every link to it and `RootOK` if it is the
space root is no hole. -/
theorem liveEdges_of_liveEdgesH (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (Hl : NodeId → Prop) (h : LiveEdgesH p N t r Hl)
    (hroot : ∀ rn, N r = some rn → Hl r → rn.leaf = false → 2 ≤ (rn.liveAt t).length)
    (hchild : ∀ u un c y yn, TReach N t r u → N u = some un → (c, y) ∈ un.liveAt t →
      N y = some yn → Hl y → ChildOK p t un yn) :
    LiveEdges p N t r := by
  refine ⟨fun rn hrn => ⟨(h.1 rn hrn).1, fun hl => ?_⟩, fun u un c y yn hu hun hc hyn => ?_⟩
  · by_cases hH : Hl r
    · exact hroot rn hrn hH hl
    · exact (h.1 rn hrn).2 hH hl
  · by_cases hH : Hl y
    · exact hchild u un c y yn hu hun hc hyn hH
    · exact (h.2 u un c y yn hu hun hc hyn).1 hH

/-- A merge into one node keeps the hole's form, the parent the hole after:
siblings l and rr under q, one of them the hole (or none is), named by q's
live klongs cL and cR, replaced by the new node m1 of their kind, whose live
klongs name children of theirs and are at least m; q's live klongs after are cL
naming m1 and its others but cL's and cR's; nothing else changes but l and rr,
which are left behind. -/
theorem liveEdgesH_mergeOne (p : Params) (N N' : NodeId → Option KNode) (t : Time)
    (r q l rr m1 : NodeId) (qn ln rn qn' mn : KNode) (cL cR : Nat) (Hl : NodeId → Prop)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hqn : N q = some qn) (hql : qn.leaf = false)
    (hl : (cL, l) ∈ qn.liveAt t) (hrr : (cR, rr) ∈ qn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn) (hm1R : ¬ TReach N t r m1)
    (hN'm1 : N' m1 = some mn)
    (hmn : ∀ c z, (c, z) ∈ mn.liveAt t →
      (∃ c0, (c0, z) ∈ ln.liveAt t) ∨ (∃ c0, (c0, z) ∈ rn.liveAt t))
    (hml : mn.leaf = ln.leaf) (hrl : rn.leaf = ln.leaf)
    (hmne : mn.liveAt t ≠ []) (hmfill : p.mergeBelow ≤ (mn.liveAt t).length)
    (hN'q : N' q = some qn') (hq'l : qn'.leaf = qn.leaf)
    (hq' : ∀ c z, (c, z) ∈ qn'.liveAt t →
      (c = cL ∧ z = m1) ∨ ((c, z) ∈ qn.liveAt t ∧ c ≠ cL ∧ c ≠ cR))
    (hq'ne : qn'.liveAt t ≠ [])
    (hother : ∀ y, y ≠ q → y ≠ l → y ≠ rr → y ≠ m1 → N' y = N y)
    (hHl : ∀ y, Hl y → y = l ∨ y = rr)
    (h : LiveEdgesH p N t r Hl) :
    LiveEdgesH p N' t r (fun y => y = q) := by
  have hlink_l : TLink N t q cL l := ⟨qn, hqn, hl⟩
  have hlink_r : TLink N t q cR rr := ⟨qn, hqn, hrr⟩
  have hlR : TReach N t r l := TReach.link hq hlink_l
  have hrR : TReach N t r rr := TReach.link hq hlink_r
  have hql' : q ≠ l := fun he => hT.no_self_link q cL hq (by rw [← he] at hlink_l; exact hlink_l)
  have hqr' : q ≠ rr := fun he => hT.no_self_link q cR hq (by rw [← he] at hlink_r; exact hlink_r)
  have hR' := mergeV_reach N N' t r q l rr m1 none qn ln rn qn' cL cR hT hq hqn hl hrr hln hrn hN'q
    (fun c z hc => by
      rcases hq' c z hc with ⟨_, hz⟩ | hz
      · exact Or.inl hz
      · exact Or.inr (Or.inr hz))
    (fun m mn' hm hmn' c z hz => by
      rcases hm with hm | hm
      · subst hm; rw [hN'm1] at hmn'; cases hmn'; exact hmn c z hz
      · cases hm)
    (fun y h1 h2 h3 h4 _ => hother y h1 h2 h3 h4) hm1R (fun m hm => by cases hm)
  -- a node that a reached node other than q links is neither l nor rr
  have hnotLR : ∀ u c z, TReach N t r u → TLink N t u c z → u ≠ q → z ≠ l ∧ z ≠ rr := by
    intro u c z hu hlk huq
    refine ⟨fun he => huq ?_, fun he => huq ?_⟩
    · rw [he] at hlk; exact (hT.oneLink u c q cL l hu hq hlk hlink_l).1
    · rw [he] at hlk; exact (hT.oneLink u c q cR rr hu hq hlk hlink_r).1
  have hnotM : ∀ u c z, TReach N t r u → TLink N t u c z → z ≠ m1 := by
    intro u c z hu hlk he
    rw [he] at hlk
    exact hm1R (TReach.link hu hlk)
  have hnotH : ∀ z, z ≠ l → z ≠ rr → ¬ Hl z := by
    intro z h1 h2 hH
    rcases hHl z hH with h' | h'
    · exact h1 h'
    · exact h2 h'
  -- the link of an old node u (not q) to z, z not q, keeps `ChildOK`
  have hold : ∀ u un0 c z zn, TReach N t r u → N u = some un0 → (c, z) ∈ un0.liveAt t →
      N z = some zn → u ≠ q → ChildOK p t un0 zn := by
    intro u un0 c z zn hu hun hc hzn huq
    obtain ⟨h1, h2⟩ := hnotLR u c z hu ⟨un0, hun, hc⟩ huq
    exact (h.2 u un0 c z zn hu hun hc hzn).1 (hnotH z h1 h2)
  refine ⟨fun rn hrn => ?_, fun u un c z zn hu hun hc hzn => ?_⟩
  · by_cases hrq : r = q
    · refine ⟨fun hE => ?_, fun hn => absurd hrq hn⟩
      rw [hrq, hN'q] at hrn; cases hrn; exact absurd hE hq'ne
    · have hrl : r ≠ l := fun he => hT.rootFree q cL hq (by rw [← he] at hlink_l; exact hlink_l)
      have hrr' : r ≠ rr := fun he => hT.rootFree q cR hq (by rw [← he] at hlink_r; exact hlink_r)
      have hrm : r ≠ m1 := fun he => hm1R (by rw [← he]; exact TReach.root)
      rw [hother r hrq hrl hrr' hrm] at hrn
      exact ⟨(h.1 rn hrn).1, fun _ => (h.1 rn hrn).2 (hnotH r hrl hrr')⟩
  · refine ⟨fun hzq => ?_, fun hzq => ?_⟩
    rotate_left
    · rw [hzq, hN'q] at hzn; cases hzn; exact hq'ne
    obtain ⟨huR, hul, hur⟩ := hR' u hu
    by_cases hum : u = m1
    · -- the new node: its children are children of l or rr
      rw [hum, hN'm1] at hun; cases hun
      have hsrc : ∃ P Pn c0, TReach N t r P ∧ N P = some Pn ∧ (c0, z) ∈ Pn.liveAt t ∧
          Pn.leaf = ln.leaf ∧ (P = l ∨ P = rr) := by
        rcases hmn c z hc with ⟨c0, h0⟩ | ⟨c0, h0⟩
        · exact ⟨l, ln, c0, hlR, hln, h0, rfl, Or.inl rfl⟩
        · exact ⟨rr, rn, c0, hrR, hrn, h0, hrl, Or.inr rfl⟩
      obtain ⟨P, Pn, c0, hPR, hPn, hc0, hPl, hP⟩ := hsrc
      have hPq : P ≠ q := by
        rcases hP with h' | h'
        · rw [h']; exact Ne.symm hql'
        · rw [h']; exact Ne.symm hqr'
      obtain ⟨hzl, hzr⟩ := hnotLR P c0 z hPR ⟨Pn, hPn, hc0⟩ hPq
      have hzm := hnotM P c0 z hPR ⟨Pn, hPn, hc0⟩
      rw [hother z hzq hzl hzr hzm] at hzn
      exact childOK_grow p t Pn mn zn zn (hold P Pn c0 z zn hPR hPn hc0 hzn hPq)
        (by rw [hml, hPl]) rfl (Nat.le_refl _)
    · have huR' : TReach N t r u := by
        rcases huR with h' | h' | h'
        · exact h'
        · exact absurd h' hum
        · cases h'
      by_cases huq : u = q
      · rw [huq, hN'q] at hun; cases hun
        rcases hq' c z hc with ⟨_, hz⟩ | ⟨hc0, hcl, hcr⟩
        · subst hz
          rw [hN'm1] at hzn; cases hzn
          exact ⟨hmne, fun h1 => (by rw [hq'l, hql] at h1; cases h1), fun _ _ => hmfill⟩
        · have hzl : z ≠ l := fun he =>
            hcl (hT.oneLink q c q cL l hq hq (by rw [← he]; exact ⟨qn, hqn, hc0⟩) hlink_l).2
          have hzr : z ≠ rr := fun he =>
            hcr (hT.oneLink q c q cR rr hq hq (by rw [← he]; exact ⟨qn, hqn, hc0⟩) hlink_r).2
          have hzm := hnotM q c z hq ⟨qn, hqn, hc0⟩
          rw [hother z hzq hzl hzr hzm] at hzn
          exact childOK_grow p t qn _ zn zn ((h.2 q qn c z zn hq hqn hc0 hzn).1 (hnotH z hzl hzr))
            hq'l rfl (Nat.le_refl _)
      · rw [hother u huq hul hur hum] at hun
        obtain ⟨hzl, hzr⟩ := hnotLR u c z huR' ⟨un, hun, hc⟩ huq
        have hzm := hnotM u c z huR' ⟨un, hun, hc⟩
        rw [hother z hzq hzl hzr hzm] at hzn
        exact hold u un c z zn huR' hun hc hzn huq

/-- The node of segment g at height h on the key's path at v: the node that
the merges' loop's descent finds (`descendToHeight`). -/
def HoleAt (key : Key) (g h : Nat) (c : Ctx) (v : W) (y : NodeId) : Prop :=
  ∃ d v', descendToHeight key g h c v = .ok (d, v') ∧ (v'.path[d]?).map (·.2) = some y

/-- The live counts at a round of the merges' loop at (g, h): `LiveEdges` of the
writer's tree but at the node that the round's descent finds. -/
def LiveHole (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (v : W) : Prop :=
  LiveEdgesH c.p (wNode c.p base v) c.i v.top.rootKey (HoleAt key g h c v)

/-- The descent finds one node. -/
theorem holeAt_unique (key : Key) (g h : Nat) (c : Ctx) (v : W) (y y' : NodeId)
    (hy : HoleAt key g h c v y) (hy' : HoleAt key g h c v y') : y = y' := by
  obtain ⟨d, v1, h1, hp1⟩ := hy
  obtain ⟨d', v1', h1', hp1'⟩ := hy'
  rw [h1] at h1'
  cases h1'
  rw [hp1] at hp1'
  exact Option.some.inj hp1'

end SIS.Tree
