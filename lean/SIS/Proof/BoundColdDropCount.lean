/-
Proofs for the count k of `DropStepJ` with TREE (bergdb item 007;
SIS/BoundColdDropJ.lean, SIS/BoundColdDropCountTheorems.lean). Added 2026-11-13.

The pointers that the nodes a change makes unreachable lose to each other go to
nodes made unreachable too, and with TREE at j - 1 each such node has one
parent then. So they are at most the nodes made unreachable (`dropped_le_removed`).
-/
import SIS.Proof.BoundColdDropJTree
import SIS.Proof.BoundColdD

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem nodup_flatMap_of {f : NodeId → List NodeId} : ∀ {l : List NodeId}, l.Nodup →
    (∀ x ∈ l, (f x).Nodup) → (∀ x ∈ l, ∀ y ∈ l, x ≠ y → ∀ a ∈ f x, a ∉ f y) →
    (l.flatMap f).Nodup
  | [], _, _, _ => List.nodup_nil
  | x :: l, hl, hf, hd => by
    rw [List.flatMap_cons]
    rw [List.nodup_cons] at hl
    rw [List.nodup_append]
    refine ⟨hf x List.mem_cons_self,
      nodup_flatMap_of hl.2 (fun y hy => hf y (List.mem_cons_of_mem x hy))
        (fun a ha b hb hab => hd a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hab), ?_⟩
    intro a ha b hb hab
    subst hab
    obtain ⟨y, hy, hay⟩ := List.mem_flatMap.mp hb
    have hxy : x ≠ y := fun h => hl.1 (h ▸ hy)
    exact hd x List.mem_cons_self y (List.mem_cons_of_mem x hy) hxy a ha hay

/-- A live child at t of a node reachable at t is reachable at t, with the
pointers of P to its nodes (`PtrsOK`) and live pointers among the pointers. -/
theorem reachable_live_child {sp : Spec V T} {P : Struct V} {t : Time} (hls : LiveSub sp)
    (hptr : PtrsOK sp P) {z y : NodeId} {n : Node V} (hz : reachable sp P t z = true)
    (hn : P.get? z = some n) (hy : y ∈ sp.live (n.hist.upTo t)) : reachable sp P t y = true := by
  obtain ⟨e, he, hye⟩ := hls _ y hy
  obtain ⟨m, hm, hlt⟩ := hptr z n hn e (mem_upTo.mp he).1 y hye
  exact (reachable_iff _ _ _ _).mpr
    (Reach.child ((reachable_iff _ _ _ _).mp hz) hn hy hm hlt)

/-- With TREE at j - 1, the pointers that the nodes a change makes unreachable
lose to nodes it makes unreachable too are at most the nodes it makes
unreachable. -/
theorem dropped_le_removed (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V)
    (hls : LiveSub sp) (hptr : PtrsOK sp P) (htr : treeAt sp P (j - 1)) :
    ((removedAt sp P c j).map (fun z => (lostTo sp P (P.apply j c) j z).length)).sum ≤
      (removedAt sp P c j).length := by
  rw [← List.length_flatMap]
  have hrem : ∀ z, z ∈ removedAt sp P c j ↔
      reachable sp P (j - 1) z = true ∧ reachable sp (P.apply j c) j z = false := by
    intro z
    unfold removedAt
    rw [List.mem_filter, List.mem_eraseDups]
    unfold reachable
    simp
  -- A lost child of a node made unreachable: its parent at j - 1, reachable
  -- then, and not reachable at j.
  have hlost : ∀ z ∈ removedAt sp P c j, ∀ y ∈ lostTo sp P (P.apply j c) j z,
      ∃ n, P.get? z = some n ∧ y ∈ sp.live (n.hist.upTo (j - 1)) ∧
        reachable sp P (j - 1) y = true ∧ reachable sp (P.apply j c) j y = false := by
    intro z hz y hy
    have hz' := (hrem z).mp hz
    unfold lostTo at hy
    cases hn : P.get? z with
    | none => rw [hn] at hy; simp at hy
    | some n =>
      rw [hn] at hy
      simp only [List.mem_filter, List.mem_eraseDups, Bool.not_eq_true'] at hy
      exact ⟨n, rfl, hy.1, reachable_live_child hls hptr hz'.1 hn hy.1, hy.2⟩
  apply nodup_length_le_sub
  · apply nodup_flatMap_of
    · unfold removedAt
      exact (nodup_eraseDups _).filter _
    · intro z _
      unfold lostTo
      split
      · exact (nodup_eraseDups _).filter _
      · exact List.nodup_nil
    · intro z1 hz1 z2 hz2 hne y hy1 hy2
      obtain ⟨n1, hn1, hl1, hr1, hu1⟩ := hlost z1 hz1 y hy1
      obtain ⟨n2, hn2, hl2, -, -⟩ := hlost z2 hz2 y hy2
      have hyroot : y ≠ root := by
        intro h
        subst h
        obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr1))
        have : reachable sp (P.apply j c) j root = true :=
          (reachable_iff _ _ _ _).mpr (Reach.root _ (get?_apply_of_get? hn))
        rw [hu1] at this; cases this
      have h1 := htr y hr1 hyroot
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
      have hm1 : z1 ∈ [a] := by
        rw [← ha, List.mem_filter, List.mem_eraseDups]
        refine ⟨?_, ?_⟩
        · have := ((hrem z1).mp hz1).1
          unfold reachable at this
          exact List.contains_iff_mem.mp this
        · simp only [hn1]; exact List.contains_iff_mem.mpr hl1
      have hm2 : z2 ∈ [a] := by
        rw [← ha, List.mem_filter, List.mem_eraseDups]
        refine ⟨?_, ?_⟩
        · have := ((hrem z2).mp hz2).1
          unfold reachable at this
          exact List.contains_iff_mem.mp this
        · simp only [hn2]; exact List.contains_iff_mem.mpr hl2
      rw [List.mem_singleton] at hm1 hm2
      exact hne (hm1.trans hm2.symm)
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := List.mem_flatMap.mp hy
    obtain ⟨_, _, _, hr, hu⟩ := hlost z hz y hyz
    exact (hrem y).mpr ⟨hr, hu⟩

end SIS
