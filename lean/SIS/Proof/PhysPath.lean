/-
Proofs about the physical layer, part 9: the writer's paths in the rerun of a
lazy startup (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysRun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The same definitions on structures with the same nodes -/

section Congr

variable {sp : Spec V T} {P P' : Struct V} (hP : SameNodes P P')
include hP

theorem SameNodes.reachList (t : Time) : SIS.reachList sp P t = SIS.reachList sp P' t := by
  unfold SIS.reachList
  rw [hP root]
  split
  · rename_i n _
    exact hP.reachFrom t (n.level + 1) root n (by omega)
  · rfl

theorem SameNodes.reachFrom' (t : Time) (x : NodeId) (n : Node V) :
    SIS.reachFrom sp P t x n = SIS.reachFrom sp P' t x n :=
  hP.reachFrom t (n.level + 1) x n (by omega)

theorem pathOf_congr (c : Changes V) (j : Time) : pathOf sp P c j = pathOf sp P' c j := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  unfold pathOf
  simp only [hP.reachList, hP.reachFrom', hP.reachable, (hP.apply j c).reachable, hP']

theorem newSlot_congr (j : Time) (m : Mem V) (o : Obj V) (y : NodeId) :
    m.newSlot sp P j o y = m.newSlot sp P' j o y := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  unfold Mem.newSlot srcOK
  simp only [hP.reachable, hP']

theorem applyChange_congr (j : Time) (c : Changes V) (m : Mem V) :
    m.applyChange sp P j c = m.applyChange sp P' j c := by
  unfold Mem.applyChange
  simp only [newSlot_congr hP]

end Congr

/-! ### Facts about the paths -/

section Path

variable {sp : Spec V T}

theorem mem_pathOf {P : Struct V} {c : Changes V} {j : Time} {x : NodeId}
    (hx : x ∈ pathOf sp P c j) :
    reachable sp P (j - 1) x = true ∧ ∃ n, P.get? x = some n ∧
      (reachFrom sp P (j - 1) x n).any (fun z => changed c z || c.touch.contains z ||
        (reachable sp P (j - 1) z && !reachable sp (P.apply j c) j z)) = true := by
  unfold pathOf at hx
  rw [List.mem_filter] at hx
  obtain ⟨h1, h2⟩ := hx
  refine ⟨by simp [reachable, List.mem_eraseDups.mp h1], ?_⟩
  split at h2
  · rename_i n hn; exact ⟨n, hn, h2⟩
  · cases h2

theorem pathOf_mem {P : Struct V} {c : Changes V} {j : Time} {x : NodeId} {n : Node V}
    (hr : reachable sp P (j - 1) x = true) (hn : P.get? x = some n)
    (ht : (reachFrom sp P (j - 1) x n).any (fun z => changed c z || c.touch.contains z ||
        (reachable sp P (j - 1) z && !reachable sp (P.apply j c) j z)) = true) :
    x ∈ pathOf sp P c j := by
  unfold pathOf
  rw [List.mem_filter]
  refine ⟨?_, by rw [hn]; exact ht⟩
  rw [List.mem_eraseDups]
  simpa [reachable, List.contains_iff_mem] using hr

/-- The parent at j - 1 of a node on a path, reachable then, is on the path. -/
theorem pathOf_parent {P : Struct V} {c : Changes V} {j : Time} {x p : NodeId} {np nx : Node V}
    (hx : x ∈ pathOf sp P c j) (hp : reachable sp P (j - 1) p = true) (hnp : P.get? p = some np)
    (hxl : x ∈ sp.live (np.hist.upTo (j - 1))) (hnx : P.get? x = some nx) (hlt : nx.level < np.level) :
    p ∈ pathOf sp P c j := by
  obtain ⟨-, n, hn, ht⟩ := mem_pathOf hx
  rw [hnx, Option.some.injEq] at hn
  subst hn
  apply pathOf_mem hp hnp
  obtain ⟨z, hz, hzt⟩ := List.any_eq_true.mp ht
  exact List.any_eq_true.mpr ⟨z, reachFrom_child_sub sp hxl hnx hlt z hz, hzt⟩

end Path

section StepPath

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- A node that the transaction changes, and that it does not create, is on a path. -/
theorem step_changed_path {k : Nat} (_hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId} {nx : Node V}
    (hnx : db.P.get? x = some nx) (hc : changed (parts sp al db tr).c x = true)
    (hreach : reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) x = true) :
    x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) := by
  have hrk : reachable sp db.P k x = true := by
    rcases hstep.noRes x hreach with h | h
    · simpa using h
    · obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp h
      have := hstep.fresh nn hnn
      rw [hid, hnx] at this; cases this
  apply pathOf_mem (by simpa using hrk) hnx
  exact List.any_eq_true.mpr ⟨x, self_mem_reachFrom sp _ _ x nx, by simp [hc]⟩

/-- A node that the transaction touches is on a path (bergdb item 001, WP R3). -/
theorem step_touched_path {k : Nat} (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    {x : NodeId} (ht : x ∈ (parts sp al db tr).c.touch) :
    x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) := by
  have hrk := hstep.touchReach x ht
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hrk))
  apply pathOf_mem hrk hnx
  exact List.any_eq_true.mpr ⟨x, self_mem_reachFrom sp _ _ x nx,
    by simp [ht]⟩

/-- A node that the transaction marks, and that it does not create, is on a path. -/
theorem step_marked_path (hsp : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hm : marked sp (db.P.apply (k + 1) (parts sp al db tr).c) (parts sp al db tr).c (k + 1) x = true)
    (hnew : x ∉ (parts sp al db tr).c.new.map (·.id)) :
    x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) := by
  have hls : LiveSub sp := hsp.liveSub
  unfold marked at hm
  rw [Bool.and_eq_true] at hm
  obtain ⟨hr, hm⟩ := hm
  have hrk : reachable sp db.P k x = true := by
    rcases hstep.noRes x hr with h | h
    · simpa using h
    · exact absurd h hnew
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hrk))
  apply pathOf_mem (by simpa using hrk) hnx
  rw [get?_apply_of_get? hnx] at hm
  simp only at hm
  obtain ⟨z, hz, hzc⟩ := List.any_eq_true.mp hm
  -- Walking down from x at k + 1: a changed node, or a touched node below x at k.
  have key : ∀ (b : Nat) (u : NodeId) (nu : Node V), nu.level < b → db.P.get? u = some nu →
      u ∈ reachFrom sp db.P k x nx →
      ∀ z ∈ reachFrom sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) u
          { nu with hist := nu.hist ++ addsFor (parts sp al db tr).c (k + 1) u },
        changed (parts sp al db tr).c z = true →
        (reachFrom sp db.P k x nx).any (fun z => changed (parts sp al db tr).c z ||
          (parts sp al db tr).c.touch.contains z ||
          (reachable sp db.P k z && !reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) z)) = true := by
    intro b
    induction b with
    | zero => intro u nu h; omega
    | succ b ih =>
      intro u nu hb hnu hu z hz hzc
      by_cases hcu : changed (parts sp al db tr).c u = true
      · exact List.any_eq_true.mpr ⟨u, hu, by simp [hcu]⟩
      · rw [reachFrom_eq] at hz
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz] at hzc; exact absurd hzc hcu
        · obtain ⟨y, hy, hzy⟩ := List.mem_flatMap.mp hz
          have hadds : addsFor (parts sp al db tr).c (k + 1) u = [] := by
            simp only [addsFor, List.map_eq_nil_iff, List.filter_eq_nil_iff, beq_iff_eq]
            intro a ha hau
            apply hcu
            simp only [changed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
            exact Or.inr ⟨a, ha, hau⟩
          simp only [hadds, List.append_nil] at hy
          have hyk : y ∈ sp.live (nu.hist.upTo k) := by
            rw [upTo_of_forall _ _ (fun e he => by have := hinv.times u nu hnu e he; omega)] at hy
            rw [upTo_of_forall _ _ (hinv.times u nu hnu)]
            exact hy
          obtain ⟨e, he, hye⟩ := hls _ _ hyk
          obtain ⟨ny, hny, hlt⟩ := hinv.ptrs u nu hnu e (mem_upTo.mp he).1 y hye
          have hyin : y ∈ reachFrom sp db.P k x nx :=
            mem_reachFrom_of_child sp db.P k (nx.level + 1) x nx (by omega) hnx u nu y ny hu hnu hyk hny hlt
          rw [get?_apply_of_get? hny] at hzy
          simp only [hlt, ↓reduceIte] at hzy
          exact ih y ny (by omega) hny hyin z hzy hzc
  exact key (nx.level + 1) x nx (by omega) hnx (self_mem_reachFrom sp _ _ x nx) z hz hzc

end StepPath

end SIS
