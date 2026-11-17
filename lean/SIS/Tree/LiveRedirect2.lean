/-
R1 through two changed levels (bergdb 030-01, R4's open part): `lteP_redirect` with the
redirect one level higher. On a descent through q0 and its child q to a leaf a, where at
the new reads q0's search names a new inner node q' (instead of q) whose search names a
leaf y, and the reads agree on the descent's other nodes, the new descent ends at y. For
the copy of a node whose parent splits too (its copy, or a half, between q0 and y): the
full leaf's time split below a parent that splits (l4b's `DelFullTimeHole2M`) and the
stop node's (l4e's `UpCascSplitRest7OK`).
-/
import SIS.Tree.LiveDelFullCopy

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `descendLte` through a node q0 whose search now names an inner node q', whose own
search names a leaf y: it ends at y, the reads agreeing on the path's other nodes but
q0's old child and the end. -/
theorem lteP_redirect2 (Rd Rd' : NodeId → Option KNode) (t : Time) (cv : Nat) (q0 q' y a : NodeId)
    (qn0 qn0' qn' : KNode) (hRq0 : Rd q0 = some qn0) (hRq0' : Rd' q0 = some qn0') (hq0l' : qn0'.leaf = false)
    (hsq0 : ∀ fd, qn0.searchLte t cv = some fd → (∀ f' ext'', lteP Rd t cv f' fd.y = some (a, ext'') →
      fd.y ≠ a ∧ ∃ fd', qn0'.searchLte t cv = some fd' ∧ fd'.y = q'))
    (hRq' : Rd' q' = some qn') (hq'l : qn'.leaf = false)
    (hsq' : ∃ fd', qn'.searchLte t cv = some fd' ∧ fd'.y = y)
    (hy : ∃ ny, Rd' y = some ny ∧ ny.leaf = true) :
    ∀ f x ext, lteP Rd t cv f x = some (a, ext) → q0 ∈ x :: ext.map (·.2) → q0 ≠ a →
      (∀ (z : NodeId) (i : Nat), (x :: ext.map (·.2))[i]? = some z → z ≠ q0 →
        (∀ j, (x :: ext.map (·.2))[j]? = some q0 → i ≤ j) → Rd' z = Rd z) →
      ∃ ext', lteP Rd' t cv f x = some (y, ext') := by
  intro f
  induction f with
  | zero => intro x ext h; simp [lteP] at h
  | succ f ih =>
    intro x ext h hq hqa hag
    obtain ⟨m, hRx, ⟨hml, hax, hex⟩ | ⟨hml, fd, ext'', hfd, hr, rfl⟩⟩ := lteP_succ_some Rd t cv f x a ext h
    · rw [hex] at hq
      simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hq
      exact absurd (hq.trans hax.symm) hqa
    · by_cases hxq : x = q0
      · rw [hxq] at hRx
        rw [hxq]
        rw [hRq0] at hRx
        cases hRx
        obtain ⟨hya, fd', hfd', hfy⟩ := hsq0 fd hfd f ext'' hr
        obtain ⟨fd2, hfd2, hfy2⟩ := hsq'
        obtain ⟨ny, hny, hnyl⟩ := hy
        -- the old descent below q0 took a step more, so the fuel suffices for two
        obtain ⟨f2, rfl⟩ : ∃ f2, f = f2 + 2 := by
          cases f with
          | zero => simp [lteP] at hr
          | succ f1 =>
            cases f1 with
            | zero =>
              exfalso
              obtain ⟨m1, _, ⟨_, ha1, _⟩ | ⟨_, fd1, ext1, _, hr1, _⟩⟩ := lteP_succ_some Rd t cv 0 fd.y a ext'' hr
              · exact hya ha1.symm
              · simp [lteP] at hr1
            | succ f2 => exact ⟨f2, rfl⟩
        refine ⟨[(some fd'.c, q'), (some fd2.c, y)], ?_⟩
        cases f2 with
        | zero => simp [lteP, hRq0', hq0l', hfd', hfy, hRq', hq'l, hfd2, hfy2, hny, hnyl]
        | succ f3 => simp [lteP, hRq0', hq0l', hfd', hfy, hRq', hq'l, hfd2, hfy2, hny, hnyl]
      · have hRx' : Rd' x = some m := by
          rw [hag x 0 (by simp) hxq (fun j _ => Nat.zero_le _)]; exact hRx
        have hq' : q0 ∈ fd.y :: ext''.map (·.2) := by
          simp only [List.map_cons, List.mem_cons] at hq ⊢
          rcases hq with h1 | h1
          · exact absurd h1.symm hxq
          · exact h1
        obtain ⟨ext', he⟩ := ih fd.y ext'' hr hq' hqa (fun z i hz hzq hle => by
          refine hag z (i + 1) (by simpa using hz) hzq (fun j hj => ?_)
          cases j with
          | zero => simp at hj; exact absurd hj hxq
          | succ j => have := hle j (by simpa using hj); omega)
        exact ⟨(some fd.c, fd.y) :: ext', by simp [lteP, hRx', hml, hfd, he]⟩

end SIS.Tree
