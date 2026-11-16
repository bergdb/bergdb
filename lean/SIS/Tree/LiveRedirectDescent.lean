/-
The merges' descent after a time split whose parent has room (bergdb 030-01,
R1 for step 3's rest and step 5's full leaf): the parent q's klong of the key's
path names the copy y instead, so the descent one height up stops at y.
-/
import SIS.Tree.LiveSplitRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Along a graded descent, a node's height is h plus the steps below it. -/
theorem dhP_height (Rd : NodeId → Option KNode) (Gh : NodeId → Option (Nat × Nat)) (t : Time)
    (cv h : Nat) :
    ∀ f z ext, dhP Rd Gh t cv h f z = some ext → GradedL Rd Gh (z :: ext.map (·.2)) →
      ∃ g, Gh z = some (g, h + ext.length) := by
  intro f
  induction f with
  | zero => intro z ext h1; simp [dhP] at h1
  | succ f ih =>
    intro z ext h1 hgr
    unfold dhP at h1
    split at h1
    · rename_i n gz hz hRz hGz
      split at h1
      · rename_i hzh
        cases h1
        refine ⟨gz, ?_⟩
        rw [hGz]
        simp at hzh
        simp [hzh]
      · split at h1
        · cases h1
        · rename_i hlh
          split at h1
          · cases h1
          · rename_i fd hfd
            cases hr : dhP Rd Gh t cv h f fd.y with
            | none => rw [hr] at h1; cases h1
            | some r =>
              rw [hr] at h1
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              have hnl : n.leaf = false := by
                cases hl : n.leaf
                · rfl
                · simp [hl] at hlh
              simp only [List.map_cons] at hgr
              obtain ⟨g1, h1', g2, h2', hG1, hG2, hstep⟩ := hgr.1 n hRz hnl
              obtain ⟨g3, hG3⟩ := ih fd.y r hr hgr.2
              rw [hG3] at hG2
              simp only [Option.some.injEq, Prod.mk.injEq] at hG2
              rw [hGz] at hG1
              simp only [Option.some.injEq, Prod.mk.injEq] at hG1
              refine ⟨gz, ?_⟩
              rw [hGz]
              simp only [List.length_cons, Option.some.injEq, Prod.mk.injEq, true_and]
              omega
    · cases h1

theorem dl3_mem {α : Type} (a : α) (L : List α) (hL : 3 ≤ L.length) (u : α)
    (hu : u ∈ L.dropLast.dropLast.dropLast) : u ∈ (a :: L).dropLast.dropLast.dropLast := by
  match L, hL with
  | b :: c :: d :: rest, _ =>
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    exact List.mem_cons_of_mem _ hu

theorem dl2_mem {α : Type} (a : α) (L : List α) (hL : 2 ≤ L.length) (u : α)
    (hu : u ∈ L.dropLast.dropLast) : u ∈ (a :: L).dropLast.dropLast := by
  match L, hL with
  | b :: c :: rest, _ =>
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    exact List.mem_cons_of_mem _ hu

theorem dl2_last {α : Type} (a : α) (L : List α) (hL : 3 ≤ L.length) :
    (a :: L).dropLast.dropLast.getLast? = L.dropLast.dropLast.getLast? := by
  match L, hL with
  | b :: c :: d :: rest, _ =>
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    rw [List.dropLast_cons_of_ne_nil (by simp)]
    rw [List.getLast?_cons]
    have : (b :: c :: d :: rest).dropLast.dropLast ≠ [] := by
      intro h
      have := congrArg List.length h
      simp at this
    cases h : (b :: c :: d :: rest).dropLast.dropLast.getLast? with
    | none => rw [List.getLast?_eq_none_iff] at h; exact absurd h this
    | some v => simp

theorem dropLast_dropLast_cons {α : Type} (a : α) (l : List α) (hl : 2 ≤ l.length) :
    (a :: l).dropLast.dropLast = a :: l.dropLast.dropLast := by
  match l, hl with
  | b :: c :: rest, _ => simp [List.dropLast_cons_cons]

/-- The descent one height up after the third node from its end, q, has its
klong of the key's path pointed to y, a node of height h + 1: reading alike
above q (q's height read alike), it ends at y, one step after q. -/
theorem dhP_redirect (Rd Rd' : NodeId → Option KNode) (Gh Gh' : NodeId → Option (Nat × Nat))
    (t : Time) (cv h : Nat) (q y : NodeId) (qn' : KNode) (fd' : Found)
    (hq' : Rd' q = some qn') (hq'l : qn'.leaf = false) (hfd' : qn'.searchLte t cv = some fd')
    (hy : fd'.y = y) (hRy : ∃ yn, Rd' y = some yn) (hGy : ∃ g, Gh' y = some (g, h + 1)) :
    ∀ f z ext, dhP Rd Gh t cv h f z = some ext → 2 ≤ ext.length →
      GradedL Rd Gh (z :: ext.map (·.2)) →
      (z :: ext.map (·.2)).dropLast.dropLast.getLast? = some q →
      (∀ u ∈ (z :: ext.map (·.2)).dropLast.dropLast.dropLast, Rd' u = Rd u) →
      (∀ u ∈ (z :: ext.map (·.2)).dropLast.dropLast, Gh' u = Gh u) →
      dhP Rd' Gh' t cv (h + 1) f z = some (ext.dropLast.dropLast ++ [(some fd'.c, y)]) := by
  obtain ⟨yn, hRy⟩ := hRy
  obtain ⟨gy, hGy⟩ := hGy
  intro f
  induction f with
  | zero => intro z ext h1; simp [dhP] at h1
  | succ f ih =>
    intro z ext h1 hlen hgr hqz hagN hagG
    have hzH := dhP_height Rd Gh t cv h (f + 1) z ext h1 hgr
    have hGz' : Gh' z = Gh z := hagG z (by
      cases ext with
      | nil => simp at hlen
      | cons e rest =>
        cases rest with
        | nil => simp at hlen
        | cons e2 rest2 => simp [List.dropLast_cons_cons])
    unfold dhP at h1
    split at h1
    · rename_i n gz hz hRz hGz
      split at h1
      · cases h1; simp at hlen
      · split at h1
        · cases h1
        · rename_i hlh
          split at h1
          · cases h1
          · rename_i fd hfd
            cases hr : dhP Rd Gh t cv h f fd.y with
            | none => rw [hr] at h1; cases h1
            | some r =>
              rw [hr] at h1
              simp only [Option.map_some, Option.some.injEq] at h1
              subst h1
              have hnl : n.leaf = false := by
                cases hl : n.leaf
                · rfl
                · simp [hl] at hlh
              obtain ⟨gz', hzH⟩ := hzH
              rw [hGz] at hzH
              simp only [Option.some.injEq, Prod.mk.injEq, List.length_cons] at hzH
              obtain ⟨_, hzH⟩ := hzH
              simp only [List.length_cons] at hlen
              by_cases hr2 : r.length = 1
              · -- z is q: the new descent turns to y
                obtain ⟨e, he⟩ : ∃ e, r = [e] := by
                  match r, hr2 with
                  | [e], _ => exact ⟨e, rfl⟩
                have hzq : z = q := by
                  rw [he] at hqz
                  simp at hqz
                  exact hqz
                subst hzq
                -- f is not 0: the old descent went on from fd.y
                obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := by
                  cases f with
                  | zero => simp [dhP] at hr
                  | succ f' => exact ⟨f', rfl⟩
                unfold dhP
                rw [hq', hGz', hGz]
                have hne : (hz == h + 1) = false := by simp; omega
                have hnlt : ¬ (hz < h + 1) := by omega
                simp only [hne, Bool.false_eq_true, ↓reduceIte, hq'l, Bool.false_or,
                  decide_eq_true_eq, hnlt, hfd', hy]
                unfold dhP
                rw [hRy, hGy]
                simp [he]
              · -- z is above q: the new descent reads z alike
                have hr3 : 2 ≤ r.length := by omega
                have hRz' : Rd' z = Rd z := hagN z (by
                  rw [dropLast_dropLast_cons]
                  · simp only [List.map_cons]
                    match r, hr3 with
                    | a :: b :: rest, _ => simp [List.dropLast_cons_cons]
                  · simp; omega)
                unfold dhP
                rw [hRz', hRz, hGz', hGz]
                have hne : (hz == h + 1) = false := by simp; omega
                have hnlt : ¬ (hz < h + 1) := by omega
                simp only [hne, Bool.false_eq_true, ↓reduceIte, hnl, Bool.false_or,
                  decide_eq_true_eq, hnlt, hfd]
                simp only [List.map_cons] at hgr hqz hagN hagG
                have hL3 : 3 ≤ (fd.y :: r.map (·.2)).length := by simp; omega
                have hih := ih fd.y r hr hr3 hgr.2
                  (by rw [← dl2_last z _ hL3]; exact hqz)
                  (fun u hu => hagN u (dl3_mem z _ hL3 u hu))
                  (fun u hu => hagG u (dl2_mem z _ (by omega) u hu))
                rw [hih]
                simp only [Option.map_some]
                congr 1
                match r, hr3 with
                | a :: b :: rest, _ => simp [List.dropLast_cons_cons]
    · cases h1

set_option maxHeartbeats 2000000 in
/-- The merges' descent after a time split whose parent has room (R1): the
descent at (g, h) from S found x at depth d, its parent p and p's parent q both
inner; on a state T that reads alike above q (q's height too), where q's klong
of the key's segment names y, of height h + 1, the descent at (g, h + 1) ends at
y. -/
theorem descendToHeight_redirect (key : Key) (g h : Nat) (c : Ctx) (S S1 T : W) (d : Nat)
    (hS : descendToHeight key g h c S = .ok (d, S1)) (hd : 2 ≤ d)
    (p q y : NodeId) (pn qn qn' : KNode) (cv : Nat) (fd' : Found) (hcv : key[g]? = some cv)
    (hp : (S1.path[d - 1]?).map (·.2) = some p) (hpn : rdN c S p = some pn) (hpl : pn.leaf = false)
    (hq : (S1.path[d - 2]?).map (·.2) = some q) (hqn : rdN c S q = some qn) (hql : qn.leaf = false)
    (hroot : T.top.rootKey = S.top.rootKey)
    (hagN : ∀ u ∈ (S1.path.map (·.2)).dropLast.dropLast.dropLast, rdN c T u = rdN c S u)
    (hagG : ∀ u ∈ (S1.path.map (·.2)).dropLast.dropLast, rdG c T u = rdG c S u)
    (hgr : GradedL (rdN c S) (rdG c S) (S1.path.map (·.2)))
    (hq' : rdN c T q = some qn') (hq'l : qn'.leaf = false) (hfd' : qn'.searchLte c.i cv = some fd')
    (hy : fd'.y = y) (hRy : ∃ yn, rdN c T y = some yn) (hGy : ∃ g', rdG c T y = some (g', h + 1)) :
    WriterWP (descendToHeight key g (h + 1)) c T (fun d' T1 => (T1.path[d']?).map (·.2) = some y) := by
  obtain ⟨root, P0, cv0, ext, hdsr, hcv0, hdh, hp1, hd1, -⟩ :=
    writerWP_descendToHeight_rd key g h c S d S1 hS
  rw [hcv] at hcv0
  cases hcv0
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
  have hlen2 : (P0 ++ ext).length = B.length + 1 + ext.length := by rw [← hp1]; exact hlenL
  have hdL : d = B.length + ext.length := by rw [hd1]; omega
  -- the node at an index of B: B's last is a segment leaf
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
  have hext : 2 ≤ ext.length := by
    rcases Nat.lt_or_ge ext.length 2 with hlt | hge
    · exfalso
      have hB1 : 1 ≤ B.length := by omega
      have hlastB : B.getLast? = B[B.length - 1]? := List.getLast?_eq_getElem?
      rcases Nat.lt_or_ge ext.length 1 with h0 | h1
      · -- p is B's last: a leaf
        have hz := hidx (d - 1) p (by omega) hp
        have : d - 1 = B.length - 1 := by omega
        rw [this, ← hlastB] at hz
        obtain ⟨n, hn, hnl⟩ := hBleaf p hz
        rw [hpn] at hn; cases hn; rw [hpl] at hnl; cases hnl
      · -- q is B's last: a leaf
        have hz := hidx (d - 2) q (by omega) hq
        have : d - 2 = B.length - 1 := by omega
        rw [this, ← hlastB] at hz
        obtain ⟨n, hn, hnl⟩ := hBleaf q hz
        rw [hqn] at hn; cases hn; rw [hql] at hnl; cases hnl
    · exact hge
  -- the segment root found alike
  have hPB : (P0.map (·.2)).dropLast = B := by rw [hB, List.dropLast_concat]
  have hsplit3 : (S1.path.map (·.2)).dropLast.dropLast.dropLast =
      B ++ (root :: ext.map (·.2)).dropLast.dropLast.dropLast := by
    have h1 : (root :: ext.map (·.2)) ≠ [] := by simp
    have h2 : (root :: ext.map (·.2)).dropLast ≠ [] := by
      apply List.ne_nil_of_length_pos; simp; omega
    have h3 : (root :: ext.map (·.2)).dropLast.dropLast ≠ [] := by
      apply List.ne_nil_of_length_pos; simp; omega
    rw [hL, List.dropLast_append_of_ne_nil h1, List.dropLast_append_of_ne_nil h2,
      List.dropLast_append_of_ne_nil h3]
  have hsplit2 : (S1.path.map (·.2)).dropLast.dropLast =
      B ++ (root :: ext.map (·.2)).dropLast.dropLast := by
    have h1 : (root :: ext.map (·.2)) ≠ [] := by simp
    have h2 : (root :: ext.map (·.2)).dropLast ≠ [] := by
      apply List.ne_nil_of_length_pos; simp; omega
    rw [hL, List.dropLast_append_of_ne_nil h1, List.dropLast_append_of_ne_nil h2]
  have hdsrT := dsrP_congr (rdN c S) (rdN c T) c.i c.p.fuel key g _ root P0 hdsr
    (fun u hu => hagN u (by
      rw [hsplit3]
      apply List.mem_append_left
      rw [← hPB, ← List.map_dropLast]
      exact hu))
  rw [hroot, hdsrT] at hdsr'
  simp only [Option.some.injEq, Prod.mk.injEq] at hdsr'
  obtain ⟨rfl, rfl⟩ := hdsr'
  -- q is the third node from the end of the descent below the segment root
  have hq3 : (root :: ext.map (·.2)).dropLast.dropLast.getLast? = some q := by
    have hlen2 : ((root :: ext.map (·.2)).dropLast.dropLast).length = ext.length - 1 := by simp
    rw [List.getLast?_eq_getElem?, hlen2]
    have hz : (S1.path.map (·.2))[d - 2]? = some q := by rw [List.getElem?_map]; exact hq
    rw [hL, List.getElem?_append_right (by omega)] at hz
    rw [List.getElem?_dropLast, if_pos (by simp; omega), List.getElem?_dropLast, if_pos (by simp; omega)]
    have : d - 2 - B.length = ext.length - 1 - 1 := by omega
    rw [this] at hz
    exact hz
  have hred := dhP_redirect (rdN c S) (rdN c T) (rdG c S) (rdG c T) c.i cv h q y qn' fd' hq' hq'l hfd' hy
    hRy hGy c.p.fuel root ext hdh hext (gradedL_append_right _ _ B _ (hL ▸ hgr)) hq3
    (fun u hu => hagN u (by rw [hsplit3]; exact List.mem_append_right _ hu))
    (fun u hu => hagG u (by rw [hsplit2]; exact List.mem_append_right _ hu))
  rw [hred] at hdh'
  cases hdh'
  rw [hd1', hp1']
  simp

end SIS.Tree
