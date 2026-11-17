/-
The contract package (bergdb 030-07): TREE. The contract's TREE (bergdb
030-08, `TreeOk`: the walk from the space root reaches no node twice) gives
the model's TREE (`SIS.treeAt`: every node reachable but the root is the live
child of exactly one reachable node) for the model's structure of a bridged
history, at the latest time (`BInv.treeAt`).
-/
import Mathlib.Tactic
import SIS.Proof.Init
import Contract.Proof.BridgeStep

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec Reach)
open SIS.Check (BVal bptrs blive bspec)

/-! ## The walk without a node twice -/

/-- In a list put together without repeats, an element is in one part only. -/
theorem nodup_flatMap_inj {α β : Type} {g : α → List β} : ∀ {l : List α},
    (l.flatMap g).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → ∀ {y : β}, y ∈ g a → y ∈ g b → a = b
  | [], _, a, _, ha, _, _, _, _ => by simp at ha
  | e :: r, h, a, b, ha, hb, y, hya, hyb => by
    simp only [List.flatMap_cons] at h
    rw [List.nodup_append] at h
    obtain ⟨_, h2, h3⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · rfl
      · exact absurd rfl (h3 y hya y (List.mem_flatMap.mpr ⟨b, hb', hyb⟩))
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl (h3 y hyb y (List.mem_flatMap.mpr ⟨a, ha', hya⟩))
      · exact nodup_flatMap_inj h2 ha' hb' hya hyb

/-- A node that the walk from x0 reaches is x0 or on a lower level. -/
theorem reachAt_lvl {s : Tree} (hl : LevOK s) : ∀ (f : Nat) (x0 : NodeId) (o0 : Obj),
    s.obj x0 = some o0 → ∀ z, z ∈ reachAt s f x0 →
    ∃ o, s.obj z = some o ∧ (z = x0 ∨ lvl o < lvl o0)
  | 0, x0, o0, h0, z, hz => by
    simp only [reachAt, List.mem_singleton] at hz
    exact ⟨o0, by rw [hz]; exact h0, Or.inl hz⟩
  | f + 1, x0, o0, h0, z, hz => by
    simp only [reachAt, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ⟨o0, h0, Or.inl rfl⟩
    · cases o0 with
      | val v => rw [h0] at hz; simp at hz
      | key n0 =>
        rw [h0] at hz
        simp only [List.mem_flatMap] at hz
        obtain ⟨⟨c0, w⟩, hw, hzw⟩ := hz
        obtain ⟨ow, how, hlt⟩ := hl x0 n0 h0 c0 w (live_mem_key hw)
        obtain ⟨o, ho, hcase⟩ := reachAt_lvl hl f w ow how z hzw
        refine ⟨o, ho, Or.inr ?_⟩
        rcases hcase with rfl | h1
        · rw [how] at ho
          injection ho with ho
          subst ho
          exact hlt
        · exact Nat.lt_trans h1 hlt

/-- A walk that reaches no node twice reaches no node with two parents. -/
theorem reachAt_one_parent {s : Tree} (hl : LevOK s) : ∀ (f : Nat) (x0 : NodeId) (o0 : Obj),
    s.obj x0 = some o0 → lvl o0 < f → (reachAt s f x0).Nodup →
    ∀ x1 x2 n1 n2 c1 c2 y, x1 ∈ reachAt s f x0 → x2 ∈ reachAt s f x0 →
    s.obj x1 = some (.key n1) → s.obj x2 = some (.key n2) →
    (c1, y) ∈ live n1.ks → (c2, y) ∈ live n2.ks → x1 = x2
  | 0, _, _, _, hf, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => by omega
  | f + 1, x0, o0, h0, hf, hnd, x1, x2, n1, n2, c1, c2, y, hx1, hx2, hn1, hn2, hy1, hy2 => by
    cases o0 with
    | val v =>
      simp only [reachAt, h0, List.mem_cons, List.not_mem_nil, or_false] at hx1 hx2
      rw [hx1, hx2]
    | key n0 =>
      simp only [reachAt, h0, List.mem_cons] at hx1 hx2
      simp only [reachAt, h0, List.nodup_cons] at hnd
      obtain ⟨_, hnd⟩ := hnd
      -- A child of x0 by a live klong, and what is below it.
      have below : ∀ e ∈ live n0.ks, ∃ ow, s.obj e.2 = some ow ∧ lvl ow < f := by
        rintro ⟨c0, w⟩ he
        obtain ⟨ow, how, hlt⟩ := hl x0 n0 h0 c0 w (live_mem_key he)
        have hf' : n0.level < f + 1 := hf
        exact ⟨ow, how, by omega⟩
      -- y, a live child of a key node x in the walk below e, is in that walk.
      have inpart : ∀ e ∈ live n0.ks, ∀ x n c, x ∈ reachAt s f e.2 → s.obj x = some (.key n) →
          (c, y) ∈ live n.ks → y ∈ reachAt s f e.2 := by
        intro e he x n c hx hn hc
        obtain ⟨ow, how, hlt⟩ := below e he
        exact reachAt_closed hl f e.2 ow how hlt x n c y hx hn hc
      -- y is not a live child of a node of its own walk.
      have notself : ∀ x n c, x ∈ reachAt s f y → s.obj x = some (.key n) →
          (c, y) ∈ live n.ks → False := by
        intro x n c hx hn hc
        obtain ⟨oy, hoy, hlt⟩ := hl x n hn c y (live_mem_key hc)
        obtain ⟨o, ho, hcase⟩ := reachAt_lvl hl f y oy hoy x hx
        rw [hn] at ho
        injection ho with ho
        subst ho
        rcases hcase with rfl | h1
        · rw [hn] at hoy
          injection hoy with hoy
          subst hoy
          exact Nat.lt_irrefl _ hlt
        · simp only [lvl] at h1 hlt
          omega
      rcases hx1 with rfl | hx1
      · rcases hx2 with rfl | hx2
        · rfl
        · exfalso
          rw [h0] at hn1
          injection hn1 with hn1
          injection hn1 with hn1
          subst hn1
          simp only [List.mem_flatMap] at hx2
          obtain ⟨e2, he2, hx2⟩ := hx2
          have hy2' := inpart e2 he2 x2 n2 c2 hx2 hn2 hy2
          have heq := nodup_flatMap_inj hnd hy1 he2 (mem_reachAt_self s f y) hy2'
          rw [← heq] at hx2
          exact notself x2 n2 c2 hx2 hn2 hy2
      · rcases hx2 with rfl | hx2
        · exfalso
          rw [h0] at hn2
          injection hn2 with hn2
          injection hn2 with hn2
          subst hn2
          simp only [List.mem_flatMap] at hx1
          obtain ⟨e1, he1, hx1⟩ := hx1
          have hy1' := inpart e1 he1 x1 n1 c1 hx1 hn1 hy1
          have heq := nodup_flatMap_inj hnd hy2 he1 (mem_reachAt_self s f y) hy1'
          rw [← heq] at hx1
          exact notself x1 n1 c1 hx1 hn1 hy1
        · simp only [List.mem_flatMap] at hx1 hx2
          obtain ⟨e1, he1, hx1⟩ := hx1
          obtain ⟨e2, he2, hx2⟩ := hx2
          have hy1' := inpart e1 he1 x1 n1 c1 hx1 hn1 hy1
          have hy2' := inpart e2 he2 x2 n2 c2 hx2 hn2 hy2
          have heq := nodup_flatMap_inj hnd he1 he2 hy1' hy2'
          subst heq
          obtain ⟨ow, how, hlt⟩ := below e1 he1
          have hnd1 : (reachAt s f e1.2).Nodup := (List.nodup_flatMap.mp hnd).1 e1 he1
          exact reachAt_one_parent hl f e1.2 ow how hlt hnd1 x1 x2 n1 n2 c1 c2 y hx1 hx2 hn1 hn2
            hy1 hy2

/-! ## The model's TREE -/

section Model

variable {h : BHist} {j : Nat}

/-- The model's TREE for the structure of a bridged history at the latest
time, from the contract's TREE for the tree. -/
theorem BInv.treeAt (hi : BInv h j) (ht : TreeOk (h.tree j)) :
    SIS.treeAt h.spec (h.P j) j := by
  obtain ⟨n0, z, nz, yr, nr, h0, hl0, hz, hlz, hly, hroot, hyr, hnr, hs0, hsz⟩ := hi.link
  have hreach : reach (h.tree j) = reachAt (h.tree j) ((h.tree j).fuel yr) yr := by
    unfold reach; rw [hroot]
  have hfuel : lvl (.key nr) < (h.tree j).fuel yr := by simp [Tree.fuel, hyr, lvl]
  have hnd : (reachAt (h.tree j) ((h.tree j).fuel yr) yr).Nodup := by
    rw [← hreach]; exact ht
  have cases3 : ∀ x, Reach h.spec (h.P j) j x →
      x = SIS.root ∨ x = z ∨ x ∈ reach (h.tree j) :=
    fun x hx => hi.reach3 h0 hl0 hz hly hroot hyr hx
  -- The parents of y in the model: reachable nodes with y a live child.
  have parent_cases : ∀ x N y, Reach h.spec (h.P j) j x → (h.P j).get? x = some N →
      y ∈ h.spec.live (N.hist.upTo j) →
      (x = SIS.root ∧ y = z) ∨ (x = z ∧ y = yr) ∨
      (x ∈ reach (h.tree j) ∧ ∃ n c, (h.tree j).obj x = some (.key n) ∧ (c, y) ∈ live n.ks) := by
    intro x N y hx hN hy
    rcases cases3 x hx with rfl | rfl | hin
    · rw [h0] at hN
      injection hN with hN
      subst hN
      rw [hl0] at hy
      exact Or.inl ⟨rfl, List.mem_singleton.mp hy⟩
    · rw [hz] at hN
      injection hN with hN
      subst hN
      rw [hly] at hy
      exact Or.inr (Or.inl ⟨rfl, List.mem_singleton.mp hy⟩)
    · right; right
      refine ⟨hin, ?_⟩
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hi.reach_obj hin)
      cases o with
      | val v => exact absurd hy (hi.val_live ho hN j y)
      | key n =>
        obtain ⟨hP, hlive⟩ := hi.key_live ho
        rw [hP] at hN
        injection hN with hN
        subst hN
        obtain ⟨c, hc⟩ := (hlive y).mp hy
        exact ⟨n, c, ho, hc⟩
  intro y hy hne
  rw [SIS.reachable_iff] at hy
  -- The list of the parents of y.
  generalize hF : List.filter _ (List.eraseDups (SIS.reachList h.spec (h.P j) j)) = F
  have hFnd : F.Nodup := by
    rw [← hF]; exact SIS.nodup_filter (SIS.nodup_eraseDups _) _
  have hFmem : ∀ x, x ∈ F ↔ Reach h.spec (h.P j) j x ∧ ∃ N, (h.P j).get? x = some N ∧
      y ∈ h.spec.live (N.hist.upTo j) := by
    intro x
    rw [← hF, List.mem_filter, List.mem_eraseDups, ← SIS.reachable_iff]
    simp only [SIS.reachable, List.contains_iff_mem]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      cases hN : (h.P j).get? x with
      | none => rw [hN] at h2; simp at h2
      | some N =>
        rw [hN] at h2
        exact ⟨N, rfl, by simpa using h2⟩
    · rintro ⟨h1, N, hN, h2⟩
      refine ⟨h1, ?_⟩
      rw [hN]
      simpa using h2
  -- There is a parent.
  have hex : ∃ x, x ∈ F := by
    cases hy with
    | root _ _ => exact absurd rfl hne
    | @child x _ N M hrx hN hy' hM hlt => exact ⟨x, (hFmem x).mpr ⟨hrx, N, hN, hy'⟩⟩
  -- There is one parent only.
  have hone : ∀ a ∈ F, ∀ b ∈ F, a = b := by
    intro a ha b hb
    obtain ⟨hra, Na, hNa, hya⟩ := (hFmem a).mp ha
    obtain ⟨hrb, Nb, hNb, hyb⟩ := (hFmem b).mp hb
    have key : ∀ x n c, x ∈ reach (h.tree j) → (h.tree j).obj x = some (.key n) →
        (c, y) ∈ live n.ks → y ≠ z ∧ y ≠ yr := by
      intro x n c hx hn hc
      obtain ⟨oy, hoy, hlt⟩ := hi.lev x n hn c y (live_mem_key hc)
      refine ⟨?_, ?_⟩
      · rintro rfl
        rw [hsz] at hoy; cases hoy
      · rintro rfl
        rw [hreach] at hx
        obtain ⟨o, ho, hcase⟩ := reachAt_lvl hi.lev _ y _ hyr x hx
        rw [hn] at ho
        injection ho with ho
        subst ho
        rw [hyr] at hoy
        injection hoy with hoy
        subst hoy
        rcases hcase with rfl | h1
        · rw [hn] at hyr
          injection hyr with hyr
          injection hyr with hyr
          subst hyr
          exact Nat.lt_irrefl _ hlt
        · simp only [lvl] at h1 hlt
          omega
    have hzyr : z ≠ yr := by
      rintro rfl
      rw [hsz] at hyr; cases hyr
    rcases parent_cases a Na y hra hNa hya with ⟨rfl, hyz⟩ | ⟨rfl, hyyr⟩ | ⟨hina, na, ca, hna, hca⟩
    · rcases parent_cases b Nb y hrb hNb hyb with ⟨rfl, _⟩ | ⟨rfl, hyyr⟩ | ⟨hinb, nb, cb, hnb, hcb⟩
      · rfl
      · exact absurd (hyz.symm.trans hyyr) hzyr
      · exact absurd hyz (key b nb cb hinb hnb hcb).1
    · rcases parent_cases b Nb y hrb hNb hyb with ⟨rfl, hyz⟩ | ⟨rfl, _⟩ | ⟨hinb, nb, cb, hnb, hcb⟩
      · exact absurd (hyz.symm.trans hyyr) hzyr
      · rfl
      · exact absurd hyyr (key b nb cb hinb hnb hcb).2
    · rcases parent_cases b Nb y hrb hNb hyb with ⟨rfl, hyz⟩ | ⟨rfl, hyyr⟩ | ⟨hinb, nb, cb, hnb, hcb⟩
      · exact absurd hyz (key a na ca hina hna hca).1
      · exact absurd hyyr (key a na ca hina hna hca).2
      · rw [hreach] at hina hinb
        exact reachAt_one_parent hi.lev _ yr _ hyr hfuel hnd a b na nb ca cb y hina hinb hna hnb
          hca hcb
  have hle := SIS.length_le_one_of_nodup hFnd hone
  obtain ⟨x, hx⟩ := hex
  have hpos : 0 < F.length := List.length_pos_of_mem hx
  omega

end Model

end Contract
