/-
The contract package (bergdb 030-23, section 5.2): the proofs for GIS-J's
clauses (Contract/ReclaimGis.lean), in the abstract model's words.

A version of z that is good for a time t' at or after e leads below z to a
good version of every node below z at t', each in a record at or before its
own (`Inv.good_below`). Every node below z at e is below z at t' too, unless
a node on the way got an entry after e; a version good for t' holds that
entry, so it is in a record after e. So a version good for t' is at c ≤ e or
later if a data node below its node at e has all its versions at c or later
(`good_ge_below`).
-/
import SIS.ReclaimTheorems
import SIS.Proof.CutHist

namespace Contract

open SIS

variable {V T : Type} [DecidableEq V]

section

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- In a state with the invariant: a version v of node z at record r, good for
a time t' at or after e, is at c or later if c ≤ e and some node below z at e
has all its versions at c or later. Each step down follows a live child at e;
if z's live children are the same at t', the version's reference for that
child names a good version at or before r (`good_iff`, `Inv.ref_le_recNo`);
if not, z got an entry after e and up to t', which v holds, so r > e. -/
theorem good_ge_below (hinv : Inv sp db k) {c e t' : Nat} (hce : c ≤ e) (het : e ≤ t') :
    ∀ (b : Nat) (z : NodeId) (n : Node V) (r : Nat) (v : Version V), n.level < b →
      db.P.get? z = some n → db.S.versionAt r z = some v → good sp db.S db.P t' v = true →
      ∀ d ∈ reachFrom sp db.P e z n, (∀ r' u, db.S.versionAt r' d = some u → c ≤ r') →
        c ≤ r := by
  intro b
  induction b with
  | zero => intro z n r v h; omega
  | succ b ih =>
    intro z n r v hb hz hv hg d hd hdc
    obtain ⟨hvz, -, nv, hnv, hvh, -, -⟩ := hinv.version_node hv
    rw [hz, Option.some.injEq] at hnv
    subst hnv
    have hg' := (good_iff sp _ _ _ _).mp hg
    obtain ⟨⟨n', hn', hh⟩, hc⟩ := hg'
    rw [hvz, hz, Option.some.injEq] at hn'
    subst hn'
    rw [reachFrom_eq] at hd
    simp only [List.mem_cons, List.mem_flatMap] at hd
    rcases hd with rfl | ⟨y, hy, hd⟩
    · exact hdc r v hv
    · split at hd
      · rename_i m hm
        split at hd
        · rename_i hlt
          by_cases hup : n.hist.upTo e = n.hist.upTo t'
          · -- z's live children are the same at e and t'.
            have hy' : y ∈ sp.live (v.hist.upTo t') := by rw [hh, ← hup]; exact hy
            obtain ⟨r1, w1, h1, h2, -, h4⟩ := hc y hy'
            have hle : r1 ≤ r := hinv.ref_le_recNo hv h1
            have := ih y m r1 w1 (by omega) hm h2 h4 d hd hdc
            omega
          · -- z got an entry after e and up to t', which v holds.
            have hex : ∃ en ∈ n.hist, e < en.time ∧ en.time ≤ t' := by
              apply Classical.byContradiction
              intro hne
              apply hup
              unfold History.upTo
              apply List.filter_congr
              intro en hen
              simp only [decide_eq_decide]
              constructor
              · intro h; omega
              · intro h
                by_cases h' : en.time ≤ e
                · exact h'
                · exact absurd ⟨en, hen, by omega, h⟩ hne
            obtain ⟨en, hen, he1, he2⟩ := hex
            have h1 : en ∈ v.hist.upTo t' := by rw [hh]; exact mem_upTo.mpr ⟨hen, he2⟩
            rw [hvh] at h1
            have := (mem_upTo.mp (mem_upTo.mp h1).1).2
            omega
        · simp at hd
      · simp at hd

end

end Contract
