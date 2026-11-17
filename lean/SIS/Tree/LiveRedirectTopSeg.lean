/-
R1 at the merges' descent when the segment leaf above the hole is in the first segment's
tree and that tree changes (bergdb 030-01, R4's open part): a merge below a segment root p,
below its segment leaf q, where every node above q is inner (q is the space root, or the
space root is q's parent), so the key's search before p is one segment's descent from the
space root. Whatever the cascade made of that tree (a new space root by `split.time2` or
`split.space3`, q's node in place), when the new tree's descent at the key's first compare
value ends at a leaf naming p's copy y, the descent one height up finds y. With
`descendToHeight_redirectSeg` and `descendToHeight_redirectSeg2` it covers the descents of
l4f's 69 thin-copy cascades on the runs (030-01's log, 03:25).
-/
import SIS.Tree.LiveRedirectSeg2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A graded descent that takes a step needs two units of fuel. -/
theorem dhP_fuel2 (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time)
    (cv h : Nat) (f : Nat) (x : NodeId) (e : Option Nat × NodeId) (es : List (Option Nat × NodeId))
    (hd : dhP Rd Gh t cv h f x = some (e :: es)) : 2 ≤ f := by
  match f, hd with
  | 0, hd => simp [dhP] at hd
  | 1, hd =>
    exfalso
    unfold dhP at hd
    split at hd
    · split at hd
      · cases hd
      · split at hd
        · cases hd
        · split at hd
          · cases hd
          · simp [dhP] at hd
    · cases hd
  | f + 2, _ => omega

/-- `lteP` from a leaf: the leaf itself. -/
theorem lteP_of_leaf (Rd : NodeId → Option KNode) (t : Time) (cv f : Nat) (x : NodeId) (n : KNode)
    (hf : 0 < f) (hx : Rd x = some n) (hl : n.leaf = true) :
    lteP Rd t cv f x = some (x, []) := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  simp [lteP, hx, hl]

/-- `lteP` from an inner node whose search names a leaf: one step. -/
theorem lteP_of_inner_leaf (Rd : NodeId → Option KNode) (t : Time) (cv f : Nat) (x z : NodeId)
    (n nz : KNode) (fd : Found) (hf : 2 ≤ f) (hx : Rd x = some n) (hl : n.leaf = false)
    (hfd : n.searchLte t cv = some fd) (hfy : fd.y = z) (hz : Rd z = some nz) (hzl : nz.leaf = true) :
    lteP Rd t cv f x = some (z, [(some fd.c, z)]) := by
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
  simp [lteP, hx, hl, hfd, hfy, hz, hzl]

set_option maxHeartbeats 4000000 in
/-- The merges' descent after a time split of a segment root p below its segment
leaf q in the first segment's tree (every node above q inner): the descent at (g, h)
from S found x at depth d below p, p below q; on a state T whose descent from its space
root at p's compare value ends at a leaf q' naming y by that klong, y of height h + 1,
the descent at (g, h + 1) ends at y. No agreement of T with S is asked. -/
theorem descendToHeight_topSeg (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q q' y : NodeId) (pn qn qn' : KNode) (k1 : Nat)
    (hpk : S1.path[d - 1]? = some (some k1, p)) (hpn : rdN c S p = some pn) (hpl : pn.leaf = false)
    (hq : (S1.path[d - 2]?).map (·.2) = some q) (hqn : rdN c S q = some qn) (hql : qn.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hlT : 2 ≤ c.p.fuel → ∃ e, lteP (rdN c T) c.i k1 c.p.fuel T.top.rootKey = some (q', e))
    (hq' : rdN c T q' = some qn')
    (hfd' : ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y)
    (hRy : ∃ yn, rdN c T y = some yn) (hGy : ∃ g', rdG c T y = some (g', h + 1)) :
    WriterWP (descendToHeight key g (h + 1)) c T (fun d' T1 => (T1.path[d']?).map (·.2) = some y) := by
  obtain ⟨root, P0, cv, ext, hdsr, hcv, hdh, hp1, hd1, -⟩ :=
    writerWP_descendToHeight_rd key g h c S d S1 hS
  intro d' T1 hT
  obtain ⟨root', P0', cv', ext', hdsr', hcv', hdh', hp1', hd1', -⟩ :=
    writerWP_descendToHeight_rd key g (h + 1) c T d' T1 hT
  rw [hcv] at hcv'
  cases hcv'
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
  have hp' : (S1.path[d - 1]?).map (·.2) = some p := by rw [hpk]; rfl
  have hinner := dhP_inner (rdN c S) (rdG c S) c.i cv h c.p.fuel root ext hdh
  -- the descent below the segment root is one step: p is the root, q the leaf above
  have hext1 : ext.length = 1 := by
    rcases Nat.lt_or_ge ext.length 1 with h0 | h1
    · exfalso
      have hz : (S1.path.map (·.2))[d - 1]? = some p := by rw [List.getElem?_map]; exact hp'
      rw [hL, List.getElem?_append_left (by omega)] at hz
      have hlastB : B.getLast? = B[B.length - 1]? := List.getLast?_eq_getElem?
      have : d - 1 = B.length - 1 := by omega
      rw [this, ← hlastB] at hz
      obtain ⟨n, hn, hnl⟩ := hBleaf p hz
      rw [hpn] at hn; cases hn; rw [hpl] at hnl; cases hnl
    · rcases Nat.lt_or_ge ext.length 2 with h1' | h2
      · omega
      · exfalso
        have hz : (S1.path.map (·.2))[d - 2]? = some q := by rw [List.getElem?_map]; exact hq
        rw [hL, List.getElem?_append_right (by omega)] at hz
        have hmem : q ∈ (root :: ext.map (·.2)).dropLast := by
          rw [List.mem_iff_getElem?]
          refine ⟨d - 2 - B.length, ?_⟩
          rw [List.getElem?_dropLast]
          have hlt : d - 2 - B.length < (root :: ext.map (·.2)).length - 1 := by simp; omega
          simp only [hlt, ↓reduceIte]
          exact hz
        obtain ⟨n, hn, hnl⟩ := hinner q hmem
        rw [hqn] at hn; cases hn; rw [hql] at hnl; cases hnl
  obtain ⟨e1, he1⟩ : ∃ e1, ext = [e1] := by
    cases ext with
    | nil => simp at hext1
    | cons a l => cases l with
      | nil => exact ⟨a, rfl⟩
      | cons _ _ => simp at hext1
  have hfuel2 : 2 ≤ c.p.fuel := by
    rw [he1] at hdh
    exact dhP_fuel2 _ _ _ _ _ _ _ _ _ hdh
  have hBq : B.getLast? = some q := by
    have hz : (S1.path.map (·.2))[d - 2]? = some q := by rw [List.getElem?_map]; exact hq
    rw [hL, List.getElem?_append_left (by omega)] at hz
    rw [List.getLast?_eq_getElem?]
    have : d - 2 = B.length - 1 := by omega
    rw [← this]; exact hz
  have hBne : B ≠ [] := by intro h0; rw [h0] at hBq; cases hBq
  -- the segment search's last step
  have hkg : key.take g ≠ [] := by
    intro hg
    have := hnil hg
    rw [this] at hB
    simp only [List.map_cons, List.map_nil] at hB
    have hBn : B = [] := by
      cases B with
      | nil => rfl
      | cons a l => simp at hB
    exact hBne hBn
  obtain ⟨pre', k', hpre'⟩ : ∃ pre' k', key.take g = pre' ++ [k'] := by
    rcases List.eq_nil_or_concat (key.take g) with h0 | ⟨pre', k', h'⟩
    · exact absurd h0 hkg
    · exact ⟨pre', k', by rw [h', List.concat_eq_append]⟩
  unfold dsrP at hdsr hdsr'
  rw [hpre', List.foldl_append] at hdsr hdsr'
  simp only [List.foldl_cons, List.foldl_nil] at hdsr hdsr'
  cases hf : pre'.foldl (dsrStep (rdN c S) c.i c.p.fuel) (some (S.top.rootKey, [(none, S.top.rootKey)])) with
  | none => rw [hf] at hdsr; simp [dsrStep] at hdsr
  | some acc =>
    rw [hf] at hdsr
    obtain ⟨r', P'⟩ := acc
    obtain ⟨leaf', ext0, n', fd, hl', hRl', hfd, hacc⟩ := dsrStep_some _ c.i c.p.fuel r' P' k' _ hdsr
    simp only [Prod.mk.injEq] at hacc
    obtain ⟨hrfd, hP0eq⟩ := hacc
    have hshape := dsrFold_shape (rdN c S) c.i c.p.fuel pre' _ [(none, S.top.rootKey)] r' P' hf
      (by simp)
    have hBeq : B = (P' ++ ext0).map (·.2) := by
      have h1 : P0.map (·.2) = (P' ++ ext0).map (·.2) ++ [fd.y] := by rw [hP0eq]; simp
      rw [hB] at h1
      exact (List.append_inj' h1 rfl).1
    have hlenB : B.length = P'.length + ext0.length := by
      have := congrArg List.length hBeq
      simpa using this
    have hfdc : fd.c = k1 := by
      have h1 : S1.path[d - 1]? = some (some fd.c, fd.y) := by
        rw [hp1, List.getElem?_append_left (by rw [hlenP]; omega), hP0eq,
          List.getElem?_append_right (by simp; omega)]
        have : d - 1 - (P' ++ ext0).length = 0 := by simp; omega
        rw [this]; rfl
      rw [hpk] at h1
      exact (Option.some.inj (Prod.mk.inj (Option.some.inj h1)).1).symm
    have hk' : k' = k1 := by rw [← hfdc, KNode.searchEq_c n' c.i k' fd hfd]
    subst hk'
    -- no segment before: the node before the previous segment's root would be a leaf
    have hpre0 : pre' = [] := by
      by_cases hne0 : pre' = []
      · exact hne0
      exfalso
      have hne : pre' ≠ [] := hne0
      obtain ⟨yl, nl, hyl, hnl, hll⟩ := hshape.2 hne
      obtain ⟨sfx', hsfx', hne'⟩ := dsrFold_prefix _ c.i c.p.fuel pre' _ _ r' P' hf
      have hP'2 : 2 ≤ P'.length := by
        rw [hsfx']
        cases sfx' with
        | nil => exact absurd rfl (hne' hne)
        | cons _ _ => simp
      have hidx : (S1.path.map (·.2))[P'.length - 2]? = some yl := by
        rw [hL, List.getElem?_append_left (by omega), hBeq, List.map_append,
          List.getElem?_append_left (by simp; omega)]
        rw [List.getLast?_eq_getElem?, List.getElem?_dropLast] at hyl
        have hl1 : (P'.map (·.2)).dropLast.length - 1 < (P'.map (·.2)).length - 1 := by
          simp; omega
        simp only [hl1, ↓reduceIte] at hyl
        have : (P'.map (·.2)).dropLast.length - 1 = P'.length - 2 := by simp; omega
        rw [this] at hyl
        exact hyl
      rw [List.getElem?_map] at hidx
      obtain ⟨un, hun, hunl⟩ := habove (P'.length - 2) yl (by omega) hidx
      rw [hnl] at hun
      cases hun
      rw [hll] at hunl
      cases hunl
    subst hpre0
    obtain ⟨e, hlT⟩ := hlT hfuel2
    obtain ⟨fd', hfd'1, hfd'y⟩ := hfd'
    simp only [List.foldl_nil] at hdsr'
    simp only [dsrStep, hlT, hq', hfd'1, Option.some.injEq, Prod.mk.injEq] at hdsr'
    obtain ⟨hr', hP0'⟩ := hdsr'
    have hr'' : root' = y := by rw [← hr', hfd'y]
    subst hr''
    -- the descent at y stops at once: y's height is h + 1
    obtain ⟨yn, hyn⟩ := hRy
    obtain ⟨gy, hgy⟩ := hGy
    obtain ⟨f, hf'⟩ : ∃ f, c.p.fuel = f + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf'] at hdh'
    simp only [dhP, hyn, hgy, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hdh'
    subst hdh'
    rw [hd1', hp1', ← hP0']
    simp [hfd'y]

/-- `descendToHeight_topSeg` where T's space root is the leaf q' naming y: the space root
q split in time (`split.time2`, its copy the new space root) or in place. -/
theorem descendToHeight_topSeg_leafRoot (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q y : NodeId) (pn qn qn' : KNode) (k1 : Nat)
    (hpk : S1.path[d - 1]? = some (some k1, p)) (hpn : rdN c S p = some pn) (hpl : pn.leaf = false)
    (hq : (S1.path[d - 2]?).map (·.2) = some q) (hqn : rdN c S q = some qn) (hql : qn.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hq' : rdN c T T.top.rootKey = some qn') (hq'l : qn'.leaf = true)
    (hfd' : ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y)
    (hRy : ∃ yn, rdN c T y = some yn) (hGy : ∃ g', rdG c T y = some (g', h + 1)) :
    WriterWP (descendToHeight key g (h + 1)) c T (fun d' T1 => (T1.path[d']?).map (·.2) = some y) :=
  descendToHeight_topSeg key g h c S S1 T d hS hd p q T.top.rootKey y pn qn qn' k1 hpk hpn hpl hq hqn
    hql habove (fun hf => ⟨[], lteP_of_leaf _ _ _ _ _ qn' (by omega) hq' hq'l⟩) hq' hfd' hRy hGy

/-- `descendToHeight_topSeg` where T's space root is inner and its search names the leaf
q' naming y: the space root split in space (`split.space3`, the halves under a new root), or
a new root above q's parent's copy. -/
theorem descendToHeight_topSeg_innerRoot (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q q' y : NodeId) (pn qn rn qn' : KNode) (k1 : Nat) (fr : Found)
    (hpk : S1.path[d - 1]? = some (some k1, p)) (hpn : rdN c S p = some pn) (hpl : pn.leaf = false)
    (hq : (S1.path[d - 2]?).map (·.2) = some q) (hqn : rdN c S q = some qn) (hql : qn.leaf = true)
    (habove : ∀ i u, i + 2 < d → (S1.path[i]?).map (·.2) = some u →
      ∃ un, rdN c S u = some un ∧ un.leaf = false)
    (hr : rdN c T T.top.rootKey = some rn) (hrl : rn.leaf = false)
    (hfr : rn.searchLte c.i k1 = some fr) (hfry : fr.y = q')
    (hq' : rdN c T q' = some qn') (hq'l : qn'.leaf = true)
    (hfd' : ∃ fd', qn'.searchEq c.i k1 = some fd' ∧ fd'.y = y)
    (hRy : ∃ yn, rdN c T y = some yn) (hGy : ∃ g', rdG c T y = some (g', h + 1)) :
    WriterWP (descendToHeight key g (h + 1)) c T (fun d' T1 => (T1.path[d']?).map (·.2) = some y) :=
  descendToHeight_topSeg key g h c S S1 T d hS hd p q q' y pn qn qn' k1 hpk hpn hpl hq hqn
    hql habove (fun hf => ⟨_, lteP_of_inner_leaf _ _ _ _ _ _ rn qn' fr hf hr hrl hfr hfry hq' hq'l⟩)
    hq' hfd' hRy hGy

end SIS.Tree
