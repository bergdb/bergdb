/-
R1 through two changed levels at the merges' descent (bergdb 030-01, R4's open part):
`descendToHeight_redirectSeg` with the redirect one level higher. A merge below a
segment root p, below its segment leaf q, whose time split's copy y is the hole and
whose cascade split q too (q's copy or half q' a new leaf, named by q's parent q0
instead): the descent one height up finds y. The case of l4f's 69 thin-copy
cascades (`MergeTailFullRest10OK`), by `lteP_redirect` at q0.
-/
import SIS.Tree.LiveMergeFull
import SIS.Tree.LiveRedirect2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- An index two or more before a list's end is in its `dropLast.dropLast`. -/
theorem getElem?_dropLast_dropLast_mem {α : Type} (B : List α) (i : Nat) (z : α)
    (hi : i + 2 < B.length) (hz : B[i]? = some z) : z ∈ B.dropLast.dropLast := by
  rw [List.mem_iff_getElem?]
  refine ⟨i, ?_⟩
  have h1 : i < B.length - 1 := by omega
  have h2 : i < B.length - 1 - 1 := by omega
  simp only [List.getElem?_dropLast, List.length_dropLast, h1, h2, ↓reduceIte]
  exact hz

/-- A member of a list other than its last two values is in its `dropLast.dropLast`. -/
theorem mem_dropLast_dropLast_of_ne {α : Type} (B : List α) (a b z : α) (h2 : 2 ≤ B.length)
    (ha : B[B.length - 2]? = some a) (hb : B[B.length - 1]? = some b)
    (hz : z ∈ B) (hza : z ≠ a) (hzb : z ≠ b) : z ∈ B.dropLast.dropLast := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
  have hlt : i < B.length := by
    rcases Nat.lt_or_ge i B.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; cases hi
  refine getElem?_dropLast_dropLast_mem B i z ?_ hi
  rcases Nat.lt_or_ge (i + 2) B.length with h | h
  · exact h
  · exfalso
    rcases Nat.lt_or_ge i (B.length - 1) with h' | h'
    · have : i = B.length - 2 := by omega
      rw [this, ha] at hi
      exact hza (Option.some.inj hi).symm
    · have : i = B.length - 1 := by omega
      rw [this, hb] at hi
      exact hzb (Option.some.inj hi).symm

set_option maxHeartbeats 4000000 in
/-- The merges' descent after a time split of a segment root p below its segment
leaf q, which splits too (R1 through two changed levels): the descent at (g, h)
from S found x at depth d below p, p below q, a segment leaf, q below q0, inner;
on a state T that reads alike above q0, where q0's search of the key's previous
segment names a new leaf q' (q's copy or half) whose klong of that segment names y,
of height h + 1, the descent at (g, h + 1) ends at y, the segment root. -/
theorem descendToHeight_redirectSeg2 (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 3 ≤ d)
    (p q q0 q' y : NodeId) (pn qn q0n q0n' qn' : KNode) (k1 : Nat)
    (hpk : S1.path[d - 1]? = some (some k1, p)) (hpn : rdN c S p = some pn) (hpl : pn.leaf = false)
    (hq : (S1.path[d - 2]?).map (·.2) = some q) (hqn : rdN c S q = some qn) (hql : qn.leaf = true)
    (hq0 : (S1.path[d - 3]?).map (·.2) = some q0) (hq0n : rdN c S q0 = some q0n)
    (hq0l : q0n.leaf = false)
    (hroot : T.top.rootKey = S.top.rootKey)
    (hagN : ∀ u ∈ (S1.path.map (·.2)).dropLast.dropLast.dropLast.dropLast, rdN c T u = rdN c S u)
    (hq0' : rdN c T q0 = some q0n') (hq0'l : q0n'.leaf = false)
    (hfd0 : ∃ fd0, q0n'.searchLte c.i k1 = some fd0 ∧ fd0.y = q')
    (hq' : rdN c T q' = some qn') (hq'l : qn'.leaf = true)
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
  have hBq : B.getLast? = some q := by
    have hz : (S1.path.map (·.2))[d - 2]? = some q := by rw [List.getElem?_map]; exact hq
    rw [hL, List.getElem?_append_left (by omega)] at hz
    rw [List.getLast?_eq_getElem?]
    have : d - 2 = B.length - 1 := by omega
    rw [← this]; exact hz
  have hBq1 : B[B.length - 1]? = some q := by rw [← List.getLast?_eq_getElem?]; exact hBq
  have hBq0 : B[B.length - 2]? = some q0 := by
    have hz : (S1.path.map (·.2))[d - 3]? = some q0 := by rw [List.getElem?_map]; exact hq0
    rw [hL, List.getElem?_append_left (by omega)] at hz
    have : d - 3 = B.length - 2 := by omega
    rw [← this]; exact hz
  have hB2 : 2 ≤ B.length := by omega
  -- the nodes above q0 read alike
  obtain ⟨e1, he1⟩ : ∃ e1, ext = [e1] := by
    cases ext with
    | nil => simp at hext1
    | cons a l => cases l with
      | nil => exact ⟨a, rfl⟩
      | cons _ _ => simp at hext1
  have hBne : B ≠ [] := by intro h0; rw [h0] at hBq; cases hBq
  have hdl4 : (S1.path.map (·.2)).dropLast.dropLast.dropLast.dropLast = B.dropLast.dropLast := by
    rw [hL, he1]
    simp
  have hagI : ∀ i z, i + 2 < B.length → B[i]? = some z → rdN c T z = rdN c S z := by
    intro i z hi hz
    exact hagN z (by rw [hdl4]; exact getElem?_dropLast_dropLast_mem B i z hi hz)
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
    have hP'0 := hshape.1
    obtain ⟨_, hlast'⟩ := lteP_leaf _ c.i k' c.p.fuel r' leaf' ext0 hl'
    have hA := getLast_map_append P' ext0 r' leaf' hP'0 hlast'
    -- B is the path up to leaf', so leaf' = q
    have hBeq : B = (P' ++ ext0).map (·.2) := by
      have h1 : P0.map (·.2) = (P' ++ ext0).map (·.2) ++ [fd.y] := by rw [hP0eq]; simp
      rw [hB] at h1
      exact (List.append_inj' h1 rfl).1
    have hlenB : B.length = P'.length + ext0.length := by
      have := congrArg List.length hBeq
      simpa using this
    have hlq : leaf' = q := by
      rw [← hBeq] at hA; rw [hA] at hBq; exact Option.some.inj hBq
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
    have hP'pos : 1 ≤ P'.length := by
      cases P' with
      | nil => simp at hP'0
      | cons _ _ => simp
    -- q0 is below r' in the previous segment's tree: q is no segment root
    have hext0 : 1 ≤ ext0.length := by
      rcases Nat.lt_or_ge ext0.length 1 with h0 | h0
      · exfalso
        have he0 : ext0 = [] := List.eq_nil_of_length_eq_zero (by omega)
        by_cases hpre0 : pre' = []
        · rw [hpre0] at hf
          simp only [List.foldl, Option.some.injEq, Prod.mk.injEq] at hf
          rw [← hf.2] at hlenB
          simp at hlenB
          omega
        · obtain ⟨yl, nl, hyl, hnl, hll⟩ := hshape.2 hpre0
          have hBP : B = P'.map (·.2) := by rw [hBeq, he0]; simp
          have h1 : (P'.map (·.2)).dropLast.getLast? = B[B.length - 2]? := by
            rw [List.getLast?_eq_getElem?, List.getElem?_dropLast, hBP]
            have hl1 : (P'.map (·.2)).dropLast.length - 1 < (P'.map (·.2)).length - 1 := by
              simp; omega
            simp only [hl1, ↓reduceIte]
            congr 1
            simp
            omega
          rw [hyl, hBq0] at h1
          cases h1
          rw [hq0n] at hnl
          cases hnl
          rw [hq0l] at hll
          cases hll
      · exact h0
    have hq0in : q0 ∈ r' :: ext0.map (·.2) := by
      have hPd : P'.map (·.2) = (P'.map (·.2)).dropLast ++ [r'] := by
        have hne : P'.map (·.2) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
        have hgl : (P'.map (·.2)).getLast hne = r' := by
          have := hP'0
          rw [List.getLast?_eq_some_getLast hne] at this
          exact Option.some.inj this
        have := List.dropLast_concat_getLast hne
        rw [hgl] at this
        exact this.symm
      have hBd : B = (P'.map (·.2)).dropLast ++ (r' :: ext0.map (·.2)) := by
        rw [hBeq, List.map_append, hPd]; simp
      have hz := hBq0
      rw [hBd, List.getElem?_append_right (by simp; omega)] at hz
      exact List.mem_of_getElem? hz
    have hq0q : q0 ≠ q := by
      intro he
      rw [he, hqn] at hq0n
      cases hq0n
      rw [hql] at hq0l
      cases hq0l
    -- at T: the fold over the earlier segments as at S
    have hfT : pre'.foldl (dsrStep (rdN c T) c.i c.p.fuel) (some (S.top.rootKey, [(none, S.top.rootKey)])) =
        some (r', P') := by
      have hdrop : ∀ z ∈ P'.dropLast.map (·.2), rdN c T z = rdN c S z := by
        intro z hz
        rw [List.map_dropLast] at hz
        obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hz
        have hlt : i < (P'.map (·.2)).dropLast.length := by
          rcases Nat.lt_or_ge i (P'.map (·.2)).dropLast.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hi; cases hi
        simp only [List.length_dropLast, List.length_map] at hlt
        have hlt' : i < (P'.map (·.2)).length - 1 := by simp; omega
        simp only [List.getElem?_dropLast, hlt', ↓reduceIte] at hi
        refine hagI i z (by omega) ?_
        rw [hBeq, List.map_append, List.getElem?_append_left (by simp; omega)]
        exact hi
      refine dsrFold_congr (rdN c S) (rdN c T) c.i c.p.fuel pre' _ _ r' P' hf ?_ hdrop
      · intro hne
        obtain ⟨sfx', hsfx', hne'⟩ := dsrFold_prefix _ c.i c.p.fuel pre' _ _ r' P' hf
        have hsne : sfx' ≠ [] := hne' hne
        apply hdrop
        rw [hsfx']
        cases sfx' with
        | nil => exact absurd rfl hsne
        | cons a l => simp
    have hlT : ∃ ext1, lteP (rdN c T) c.i k' c.p.fuel r' = some (q', ext1) := by
      rw [hlq] at hl'
      obtain ⟨fd0, hfd0a, hfd0y⟩ := hfd0
      refine lteP_redirect (rdN c S) (rdN c T) c.i k' q0 q' q q0n q0n' hq0n hq0' hq0'l
        (fun _ _ _ _ _ => ⟨fd0, hfd0a, hfd0y⟩) ⟨qn', hq', hq'l⟩ c.p.fuel r' ext0 hl' hq0in hq0q ?_
      intro z hz hzq0 hzq
      have hzB : z ∈ B := by
        rw [hBeq, List.map_append]
        rcases List.mem_cons.mp hz with rfl | hz
        · exact List.mem_append_left _ (List.mem_of_getLast? hP'0)
        · exact List.mem_append_right _ hz
      exact hagN z (by
        rw [hdl4]
        exact mem_dropLast_dropLast_of_ne B q0 q z hB2 hBq0 hBq1 hzB hzq0 hzq)
    obtain ⟨ext1, hlT⟩ := hlT
    obtain ⟨fd', hfd'1, hfd'y⟩ := hfd'
    rw [hroot, hfT] at hdsr'
    simp only [dsrStep, hlT, hq', hfd'1, Option.some.injEq, Prod.mk.injEq] at hdsr'
    obtain ⟨hr', hP0'⟩ := hdsr'
    have hr'' : root' = y := by rw [← hr', hfd'y]
    subst hr''
    -- the descent at y stops at once: y's height is h + 1
    obtain ⟨yn, hyn⟩ := hRy
    obtain ⟨gy, hgy⟩ := hGy
    have hfuel : 0 < c.p.fuel := by
      cases hfu : c.p.fuel with
      | zero => rw [hfu] at hdh; simp [dhP] at hdh
      | succ _ => omega
    obtain ⟨f, hf'⟩ : ∃ f, c.p.fuel = f + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf'] at hdh'
    simp only [dhP, hyn, hgy, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hdh'
    subst hdh'
    rw [hd1', hp1', ← hP0']
    simp [hfd'y]

end SIS.Tree
