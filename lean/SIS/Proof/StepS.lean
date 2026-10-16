/-
Proofs, part 10: one transaction keeps the facts about the stream.
-/
import SIS.Proof.StepP

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem eq_of_map_nodup {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hab : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.mp ha with h1 | ha' <;> rcases List.mem_cons.mp hb with h2 | hb'
    · rw [h1, h2]
    · subst h1; exact absurd ⟨b, hb', hab.symm⟩ h.1
    · subst h2; exact absurd ⟨a, ha', hab⟩ h.1
    · exact ih h.2 ha' hb'

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

theorem step_D1_nodup {k : Nat} (hinv : Inv sp db k) :
    ((parts sp al db tr).D1.map (·.1)).Nodup := by
  rw [parts_D1]
  simp only [List.map_append, List.map_map]
  rw [List.nodup_append]
  refine ⟨hinv.dNodup, ?_, ?_⟩
  · have : (((·.1) ∘ fun x => (x, db.S.length)) : NodeId → NodeId) = id := by funext x; rfl
    rw [this, List.map_id]
    exact step_gd3_nodup sp al db tr
  · intro a ha b hb hab
    subst hab
    simp only [List.mem_map, Function.comp] at hb
    obtain ⟨y, hy, rfl⟩ := hb
    have := step_gd3_basic sp al db tr hinv.len y hy
    have h2 : inD db.D y = true := by
      rw [inD_iff]
      simp only [List.mem_map] at ha
      obtain ⟨⟨z, d⟩, hz, rfl⟩ := ha
      exact ⟨d, hz⟩
    rw [this.2.2] at h2
    simp at h2

theorem step_taken_nodup {k : Nat} (hinv : Inv sp db k) : (parts sp al db tr).taken.Nodup := by
  rw [parts_taken]
  apply (byLevel_perm _ _).symm.nodup_iff.mp
  have h := step_D1_nodup sp al db tr hinv
  exact (List.Sublist.map _ List.filter_sublist).nodup h

/-- The nodes taken are old index nodes or nodes that got dirty: all in P, all index nodes. -/
theorem step_taken_index {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).taken) : isIndex (parts sp al db tr).P x = true := by
  obtain ⟨d, hd, -⟩ := (step_taken_mem sp al db tr x).mp hx
  rcases (step_D1_mem sp al db tr hinv.len _).mp hd with h | ⟨-, h⟩
  · have hi := hinv.dIndex _ h
    have hs : (db.P.get? x).isSome := by
      simp only [isIndex] at hi; split at hi <;> simp_all
    rw [step_isIndex_old sp al db tr hinv.len hs]
    exact hi
  · exact (step_gd3_basic sp al db tr hinv.len x h).2.1

theorem isSome_of_isIndex {P : Struct V} {x : NodeId} (h : isIndex P x = true) :
    (P.get? x).isSome := by
  simp only [isIndex] at h; split at h <;> simp_all

theorem step_dataIds_spec {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    (hx : x ∈ dataIds sp al db tr) :
    db.P.get? x = none ∧ ∃ n, (parts sp al db tr).P.get? x = some n ∧ n.isData = true := by
  simp only [dataIds, List.mem_map, List.mem_filter] at hx
  obtain ⟨nn, ⟨hnn, hd⟩, rfl⟩ := hx
  have hfresh := hstep.fresh nn hnn
  refine ⟨hfresh, ?_⟩
  rw [step_P_new sp al db tr hinv.len hfresh]
  cases hm : newNodeOf (parts sp al db tr).c nn.id with
  | none =>
    have := newNodeOf_isSome hnn
    rw [hm] at this; simp at this
  | some m =>
    refine ⟨_, rfl, ?_⟩
    simp only
    obtain ⟨nn', hnn', hid, rfl⟩ := newNodeOf_some hm
    -- Two new nodes with the same id are the same (StepOK.distinct).
    have : nn' = nn := eq_of_map_nodup hstep.distinct hnn' hnn hid
    subst this
    exact hd

theorem step_vs_nodes' {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    (parts sp al db tr).vs.map (·.node) = dataIds sp al db tr ++ (parts sp al db tr).taken := by
  rw [step_vs_nodes]
  congr 1
  · apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨-, n, hn, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    simp [hn]
  · apply List.filter_eq_self.mpr
    intro x hx
    exact isSome_of_isIndex (step_taken_index sp al db tr hinv hx)

theorem step_vs_nodup {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ((parts sp al db tr).vs.map (·.node)).Nodup := by
  rw [step_vs_nodes' sp al db tr hinv hstep, List.nodup_append]
  refine ⟨?_, step_taken_nodup sp al db tr hinv, ?_⟩
  · exact (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  · intro a ha b hb hab
    subst hab
    obtain ⟨-, n, hn, hd⟩ := step_dataIds_spec sp al db tr hinv hstep ha
    have := step_taken_index sp al db tr hinv hb
    simp [isIndex, hn, hd] at this

/-- The versions of the new record are the data versions and the taken ones. -/
theorem step_written_iff {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (x : NodeId) :
    (∃ w ∈ (parts sp al db tr).vs, w.node = x) ↔
      x ∈ dataIds sp al db tr ∨ x ∈ (parts sp al db tr).taken := by
  have h := step_vs_nodes' sp al db tr hinv hstep
  constructor
  · rintro ⟨w, hw, rfl⟩
    have : w.node ∈ (parts sp al db tr).vs.map (·.node) := List.mem_map_of_mem hw
    rw [h] at this
    exact List.mem_append.mp this
  · intro hx
    have : x ∈ (parts sp al db tr).vs.map (·.node) := by rw [h]; exact List.mem_append.mpr hx
    simpa using this

/-! ### The stream facts -/

theorem step_Snew_len {k : Nat} (hinv : Inv sp db k) : (Snew sp al db tr).length = k + 1 + 1 := by
  simp [Snew, hinv.len]

theorem step_Snew_cases {k : Nat} (hinv : Inv sp db k) {r : Nat} {R : Record V T}
    (h : (Snew sp al db tr)[r]? = some R) :
    (r ≤ k ∧ db.S[r]? = some R) ∨ (r = k + 1 ∧ R = (parts sp al db tr).R) := by
  rcases Nat.lt_or_ge r db.S.length with hr | hr
  · left
    rw [Snew_getElem?_old sp al db tr hr] at h
    exact ⟨by rw [hinv.len] at hr; omega, h⟩
  · right
    have hlen := step_Snew_len sp al db tr hinv
    have hr2 : r < (Snew sp al db tr).length := by
      rcases Nat.lt_or_ge r (Snew sp al db tr).length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at h; simp at h
    have hrk : r = k + 1 := by rw [hinv.len] at hr; omega
    subst hrk
    rw [← hinv.len, Snew_getElem?_new] at h
    exact ⟨rfl, (Option.some.inj h).symm⟩

theorem step_recNo {k : Nat} (hinv : Inv sp db k) :
    ∀ (r : Nat) (R : Record V T), (Snew sp al db tr)[r]? = some R → ∀ v ∈ R.vers, v.recNo = r := by
  intro r R hR v hv
  rcases step_Snew_cases sp al db tr hinv hR with ⟨-, h⟩ | ⟨rfl, rfl⟩
  · exact hinv.recNo r R h v hv
  · obtain ⟨n, pre, -, -, h, -⟩ := built_mem (step_vs_built sp al db tr hinv.len) hv
    exact h

theorem step_versNodup {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ (r : Nat) (R : Record V T), (Snew sp al db tr)[r]? = some R → (R.vers.map (·.node)).Nodup := by
  intro r R hR
  rcases step_Snew_cases sp al db tr hinv hR with ⟨-, h⟩ | ⟨rfl, rfl⟩
  · exact hinv.versNodup r R h
  · exact step_vs_nodup sp al db tr hinv hstep

theorem step_lastSp : lastSp (Snew sp al db tr) = (parts sp al db tr).s := by
  simp [Snew, lastSp, parts_R]

theorem step_vh (hok : SpecOK sp) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    ∀ (r : Nat) (R : Record V T), (Snew sp al db tr)[r]? = some R → ∀ v ∈ R.vers,
      ∃ n, (parts sp al db tr).P.get? v.node = some n ∧ v.hist = n.hist.upTo r ∧
        v.level = n.level ∧ v.isData = n.isData := by
  intro r R hR v hv
  rcases step_Snew_cases sp al db tr hinv hR with ⟨hr, h⟩ | ⟨rfl, rfl⟩
  · obtain ⟨n, hn, h1, h2, h3⟩ := hinv.vh r R h v hv
    refine ⟨_, step_P_old sp al db tr hinv.len hn, ?_, h2, h3⟩
    rw [h1]
    simp only
    rw [upTo_append, upTo_eq_nil (addsFor _ _ _) r, List.append_nil]
    intro e he
    rw [mem_addsFor] at he
    omega
  · obtain ⟨n, pre, hn, -, -, h1, h2, h3, -⟩ := built_mem (step_vs_built sp al db tr hinv.len) hv
    refine ⟨n, hn, ?_, h2, h3⟩
    rw [h1, upTo_of_forall]
    exact (step_pfacts sp al db tr hok hinv hstep).times _ n hn

theorem step_ref {k : Nat} (hinv : Inv sp db k) :
    ∀ (r : Nat) (R : Record V T), (Snew sp al db tr)[r]? = some R → ∀ v ∈ R.vers,
      ∃ pre, pre <+: R.vers ∧ ∀ y, v.ref? y =
        if y ∈ pointees sp v.hist then
          ((Stream.building ((Snew sp al db tr).take r) pre).lv y).map (·.recNo) else none := by
  intro r R hR v hv
  rcases step_Snew_cases sp al db tr hinv hR with ⟨hr, h⟩ | ⟨rfl, rfl⟩
  · obtain ⟨pre, hpre, href⟩ := hinv.ref r R h v hv
    refine ⟨pre, hpre, ?_⟩
    have : (Snew sp al db tr).take r = db.S.take r := by
      unfold Snew
      rw [List.take_append_of_le_length (by rw [hinv.len]; omega)]
    rw [this]
    exact href
  · obtain ⟨n, pre, -, hpre, -, -, -, -, href⟩ := built_mem (step_vs_built sp al db tr hinv.len) hv
    refine ⟨pre, hpre, ?_⟩
    have : (Snew sp al db tr).take (k + 1) = db.S := by
      unfold Snew
      rw [← hinv.len, List.take_left]
    rw [this]
    exact href

theorem step_top :
    ∀ R, (Snew sp al db tr).getLast? = some R →
      R.top = topOf sp (parts sp al db tr).P (Snew sp al db tr) (lastSp (Snew sp al db tr)) := by
  intro R hR
  simp only [Snew, List.getLast?_append, List.getLast?_singleton, Option.some_or] at hR
  cases hR
  rw [parts_R, step_lastSp]
  simp only
  exact topOf_congr sp _ (fun x => (lv_of_versionAt_eq (Snew_versionAt sp al db tr) x).symm) _

end Step

end SIS
