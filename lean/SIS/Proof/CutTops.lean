/-
Proofs about reclaim, part 6 (bergdb item 001, WP R4): with a virtual root, the
root children that startup reads from a stream cut safely, and the root it
rebuilds from them.
-/
import SIS.Proof.CutBase

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Reading the root children from the cut stream gives versions that reading
the whole stream gives, or stubs of them (which the cut made unreadable, so the
read stops there). -/
theorem readTops_cut_sub (sp : Spec V T) (S : Stream V T) {c s : Nat} (hcs : c ≤ s) :
    ∀ (b : Nat) (v : Version V), v.level < b →
      ∀ w' ∈ readTops sp (cutStream c S) s true v,
        w' ∈ readTops sp S s true v ∨ ∃ w ∈ readTops sp S s true v, w' = w.stub := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb w' hw'
    rw [readTops_eq] at hw'
    rcases List.mem_cons.mp hw' with rfl | hw'
    · left; rw [readTops_eq]; exact List.mem_cons_self
    · obtain ⟨y, hy, hw'⟩ := List.mem_flatMap.mp hw'
      have hsub : ∀ w0, w0 ∈ (match follow S s true y (v.ref? y) with
          | none => []
          | some w => if sp.topLevel ≤ w.level ∧ w.level < v.level then readTops sp S s true w else []) →
          w0 ∈ readTops sp S s true v := by
        intro w0 hw0
        rw [readTops_eq]
        exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨y, hy, hw0⟩)
      -- How the pointer is followed on the cut stream.
      unfold follow at hw'
      simp only [ite_true] at hw'
      rw [newest_cut hcs] at hw'
      cases hn : newest S s y with
      | some u =>
        rw [hn] at hw'
        simp only at hw'
        have hfu : follow S s true y (v.ref? y) = some u := follow_newest hn
        split at hw'
        · rename_i hc
          rcases ih u (by omega) w' hw' with h | ⟨w, hw, rfl⟩
          · left; apply hsub; rw [hfu]; simp only [hc, and_self, ite_true]; exact h
          · right; refine ⟨w, hsub w ?_, rfl⟩; rw [hfu]; simp only [hc, and_self, ite_true]; exact hw
        · simp at hw'
      | none =>
        rw [hn] at hw'
        simp only at hw'
        cases hr : v.ref? y with
        | none => rw [hr] at hw'; simp at hw'
        | some r =>
          rw [hr] at hw'
          simp only [Option.bind_some] at hw'
          have hfo : follow S s true y (v.ref? y) = S.versionAt r y := by rw [hr, follow_old hn]
          rcases Nat.lt_or_ge r c with hrc | hrc
          · -- A record before the cut: a stub, with no pointers.
            rw [versionAt_cut_lt hrc] at hw'
            cases hw0 : S.versionAt r y with
            | none => rw [hw0] at hw'; simp at hw'
            | some w0 =>
              rw [hw0] at hw'
              simp only [Option.map_some, stub_level] at hw'
              by_cases hc : sp.topLevel ≤ w0.level ∧ w0.level < v.level
              · simp only [hc, and_self, ite_true] at hw'
                rw [readTops_eq] at hw'
                rcases List.mem_cons.mp hw' with rfl | hw'
                · right
                  refine ⟨w0, hsub w0 ?_, rfl⟩
                  rw [hfo, hw0]
                  simp only [hc, and_self, ite_true]
                  rw [readTops_eq]; exact List.mem_cons_self
                · simp [Version.stub, pointees] at hw'
              · simp only [hc, ite_false] at hw'
                simp at hw'
          · rw [versionAt_cut_ge hrc] at hw'
            cases hw0 : S.versionAt r y with
            | none => rw [hw0] at hw'; simp at hw'
            | some w0 =>
              rw [hw0] at hw'
              simp only at hw'
              split at hw'
              · rename_i hc
                rcases ih w0 (by omega) w' hw' with h | ⟨w, hw, rfl⟩
                · left; apply hsub; rw [hfo, hw0]; simp only [hc, and_self, ite_true]; exact h
                · right; refine ⟨w, hsub w ?_, rfl⟩; rw [hfo, hw0]; simp only [hc, and_self, ite_true]
                  exact hw
              · simp at hw'

section VCut

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The root children that R4 reaches from a root child were created no later. -/
theorem Inv.topClosure_older (hinv : Inv sp db k) (hv : sp.virt = true) :
    ∀ (b : Nat) (z : NodeId) (m : Node V) (cz : Time), m.level < b → TopAt sp db.P z m cz →
      cz ≤ lastSp db.S →
      ∀ y ∈ topClosure sp db.P z m, ∃ my cy, TopAt sp db.P y my cy ∧ cy ≤ cz := by
  have hvi := hinv.vr hv
  intro b
  induction b with
  | zero => intro z m cz h; omega
  | succ b ih =>
    intro z m cz hb hzt hcs y hy
    rw [topClosure_eq sp] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨m, cz, hzt, Nat.le_refl _⟩
    · obtain ⟨y', hy', hy⟩ := List.mem_flatMap.mp hy
      split at hy
      · rename_i my' hmy'
        split at hy
        · rename_i hc
          obtain ⟨u, hu⟩ := hinv.topAt_lv hzt hcs
          have hur := hinv.lv_at hu
          obtain ⟨hun, -⟩ := hinv.version_node hur
          have huh := hvi.topVers z m cz hzt u.recNo u hur
          have hy'u : y' ∈ pointees sp u.hist := by rw [huh]; exact hy'
          have hy'r : y' ≠ root := hinv.pointee_ne_root hur hy'u
          have hyt : isTop sp db.P y' = true := isTop_iff.mpr ⟨hy'r, my', hmy', hc.1⟩
          obtain ⟨m'', c'', hyt'', hlt⟩ := hvi.older z m cz hzt y' hy' hyt
          have hm'' : m'' = my' := by
            have := hyt''.1; rw [hmy'] at this; exact (Option.some.inj this).symm
          subst hm''
          obtain ⟨my, cy, hyt2, hle⟩ := ih y' m'' c'' (by omega) hyt'' (by omega) y hy
          exact ⟨my, cy, hyt2, by omega⟩
        · simp at hy
      · simp at hy

/-- Startup's read of the root children from the cut stream reads every root
child that R4 reaches through root children created at C0 or later, at its
latest version, if their latest versions are at the cut or later. -/
theorem Inv.readTops_all_cut (hinv : Inv sp db k) (hv : sp.virt = true) {c C0 : Nat}
    (hcs : c ≤ lastSp db.S)
    (hC : ∀ y m cy u, TopAt sp db.P y m cy → C0 ≤ cy → cy ≤ lastSp db.S → db.S.lv y = some u →
      c ≤ u.recNo) :
    ∀ (b : Nat) (w : Version V) (m : Node V) (cw : Time), m.level < b →
      TopAt sp db.P w.node m cw → cw ≤ lastSp db.S → db.S.lv w.node = some w →
      ∀ y ∈ topClosure sp db.P w.node m, ∀ my cy, TopAt sp db.P y my cy → C0 ≤ cy →
        ∃ w' ∈ readTops sp (cutStream c db.S) (lastSp db.S) true w, w'.node = y ∧ db.S.lv y = some w' := by
  have hvi := hinv.vr hv
  intro b
  induction b with
  | zero => intro w m cw h; omega
  | succ b ih =>
    intro w m cw hb hzt hcs' hlv y hy my cy hyt hC0
    rw [topClosure_eq sp] at hy
    rcases List.mem_cons.mp hy with hyw | hy
    · subst hyw
      exact ⟨w, by rw [readTops_eq]; exact List.mem_cons_self, rfl, hlv⟩
    · obtain ⟨y', hy', hy⟩ := List.mem_flatMap.mp hy
      split at hy
      · rename_i my' hmy'
        split at hy
        · rename_i hc
          have hwr := hinv.lv_at hlv
          have hwh := hvi.topVers w.node m cw hzt w.recNo w hwr
          have hy'w : y' ∈ pointees sp w.hist := by rw [hwh]; exact hy'
          have hy'r : y' ≠ root := hinv.pointee_ne_root hwr hy'w
          have hyt' : isTop sp db.P y' = true := isTop_iff.mpr ⟨hy'r, my', hmy', hc.1⟩
          obtain ⟨u, hu, hfu, m'', c'', hyt'', hlt⟩ := hinv.top_follow hv hzt hcs' hlv hy'w hyt'
          have hm'' : m'' = my' := by
            have := hyt''.1; rw [hmy'] at this; exact (Option.some.inj this).symm
          subst hm''
          -- y was created no later than y'.
          obtain ⟨my3, cy3, hyt3, hle3⟩ := hinv.topClosure_older hv (m''.level + 1) y' m'' c'' (by omega)
            hyt'' (by omega) y hy
          have hcy : cy3 = cy := TopAt.time_unique hyt3 hyt
          subst hcy
          have hcu : c ≤ u.recNo := hC y' m'' c'' u hyt'' (by omega) (by omega) hu
          -- So the pointer reads the same version on the cut stream.
          have hfu' : follow (cutStream c db.S) (lastSp db.S) true y' (w.ref? y') = some u := by
            rw [follow_cut hcs y' _ (fun hn r hr hsome => by
              rw [hr, follow_old hn] at hfu
              rw [← hinv.recNo_of_versionAt hfu]; exact hcu), hfu]
          obtain ⟨hun, -, my2, hmy2, -, hul, -⟩ := hinv.version_node (hinv.lv_at hu)
          rw [hmy', Option.some.injEq] at hmy2
          subst hmy2
          obtain ⟨-, -, mw, hmw, -, hwl, -⟩ := hinv.version_node hwr
          rw [hzt.1, Option.some.injEq] at hmw
          subst hmw
          obtain ⟨w', hw', hw'y, hlv'⟩ := ih u m'' c'' (by omega) (by rw [hun]; exact hyt'') (by omega)
            (by rw [hun]; exact hu) y (by rw [hun]; exact hy) my cy3 hyt hC0
          refine ⟨w', ?_, hw'y, hlv'⟩
          rw [readTops_eq]
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨y', hy'w, ?_⟩
          rw [hfu']
          have hcond : sp.topLevel ≤ u.level ∧ u.level < w.level := ⟨by omega, by omega⟩
          simp only [hcond, and_self, ite_true]
          exact hw'
        · simp at hy
      · simp at hy

end VCut

end SIS
