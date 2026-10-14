/-
Proofs, part 4: writing versions (writeAll, mkVersion) and the parts of a
transaction.
-/
import SIS.Proof.StreamLemmas

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type}

/-! ### Lookups in lists built by filterMap -/

theorem lookup_filterMap_pair {β : Type} (l : List NodeId) (f : NodeId → Option β) (y : NodeId) :
    List.lookup y (l.filterMap (fun z => (f z).map (fun b => (z, b)))) =
      if y ∈ l then f y else none := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filterMap_cons]
    by_cases hya : y = a
    · subst hya
      cases hf : f y with
      | none =>
        simp only [Option.map_none]
        rw [ih]
        split <;> simp [hf]
      | some b =>
        simp
    · cases hf : f a with
      | none =>
        simp only [Option.map_none]
        rw [ih]
        simp [hya]
      | some b =>
        simp only [Option.map_some]
        rw [List.lookup_cons]
        have : (y == a) = false := by simp [hya]
        simp only [this]
        rw [ih]
        simp [hya]

theorem ref?_mkVersion (sp : Spec V T) (S : Stream V T) (i : Nat) (x : NodeId) (n : Node V)
    (y : NodeId) :
    (mkVersion sp S i x n).ref? y =
      if y ∈ pointees sp n.hist then (S.lv y).map (·.recNo) else none := by
  simp only [Version.ref?, mkVersion]
  have h := lookup_filterMap_pair (pointees sp n.hist) (fun y => (S.lv y).map (·.recNo)) y
  simp only [Option.map_map] at h
  exact h

/-- The versions L of record i, on top of stream S: each one is made by
`mkVersion`, from the stream with the versions before it in the record. -/
def Built (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V) (L : List (Version V)) :
    Prop :=
  ∀ p (hp : p < L.length), ∃ n, P.get? L[p].node = some n ∧
    L[p] = mkVersion sp (S.building (L.take p)) i L[p].node n

theorem built_nil (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V) :
    Built sp S i P [] := by
  intro p hp; simp at hp

theorem built_snoc {sp : Spec V T} {S : Stream V T} {i : Nat} {P : Struct V}
    {L : List (Version V)} (h : Built sp S i P L) {x : NodeId} {n : Node V}
    (hx : P.get? x = some n) : Built sp S i P (L ++ [mkVersion sp (S.building L) i x n]) := by
  intro p hp
  simp only [List.length_append, List.length_singleton] at hp
  rcases Nat.lt_or_ge p L.length with hpl | hpl
  · obtain ⟨m, hm1, hm2⟩ := h p hpl
    refine ⟨m, ?_, ?_⟩
    · rw [List.getElem_append_left hpl]; exact hm1
    · rw [List.getElem_append_left hpl, List.take_append_of_le_length (Nat.le_of_lt hpl)]
      exact hm2
  · have hpe : p = L.length := by omega
    subst hpe
    refine ⟨n, ?_, ?_⟩
    · simp [mkVersion, hx]
    · simp [mkVersion]

theorem writeAll_cons (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V) (x : NodeId)
    (xs : List NodeId) (vs : List (Version V)) :
    writeAll sp S i P (x :: xs) vs =
      writeAll sp S i P xs (match P.get? x with
        | some n => vs ++ [mkVersion sp (S.building vs) i x n]
        | none => vs) := by
  rfl

theorem built_writeAll {sp : Spec V T} {S : Stream V T} {i : Nat} {P : Struct V}
    (xs : List NodeId) : ∀ {vs : List (Version V)}, Built sp S i P vs →
      Built sp S i P (writeAll sp S i P xs vs) := by
  induction xs with
  | nil => intro vs h; exact h
  | cons x xs ih =>
    intro vs h
    rw [writeAll_cons]
    apply ih
    split
    · rename_i n hn; exact built_snoc h hn
    · exact h

theorem writeAll_prefix (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V)
    (xs : List NodeId) : ∀ (vs : List (Version V)), vs <+: writeAll sp S i P xs vs := by
  induction xs with
  | nil => intro vs; exact List.prefix_refl _
  | cons x xs ih =>
    intro vs
    rw [writeAll_cons]
    split
    · exact (List.prefix_append vs _).trans (ih _)
    · exact ih vs

theorem writeAll_nodes (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V)
    (xs : List NodeId) : ∀ (vs : List (Version V)),
      (writeAll sp S i P xs vs).map (·.node) =
        vs.map (·.node) ++ xs.filter (fun x => (P.get? x).isSome) := by
  induction xs with
  | nil => intro vs; simp [writeAll]
  | cons x xs ih =>
    intro vs
    rw [writeAll_cons]
    split
    · rename_i n hn
      rw [ih]
      simp [hn, mkVersion]
    · rename_i hn
      rw [ih]
      simp [hn]

/-- A version in a built record: its fields. -/
theorem built_mem {sp : Spec V T} {S : Stream V T} {i : Nat} {P : Struct V}
    {L : List (Version V)} (h : Built sp S i P L) {v : Version V} (hv : v ∈ L) :
    ∃ n pre, P.get? v.node = some n ∧ pre <+: L ∧ v.recNo = i ∧ v.hist = n.hist ∧
      v.level = n.level ∧ v.isData = n.isData ∧
      ∀ y, v.ref? y = if y ∈ pointees sp v.hist then ((S.building pre).lv y).map (·.recNo)
        else none := by
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨n, hn, heq⟩ := h p hp
  refine ⟨n, L.take p, hn, List.take_prefix p L, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq]; rfl
  · rw [heq]; rfl
  · rw [heq]; rfl
  · rw [heq]; rfl
  · intro y
    rw [heq, ref?_mkVersion]
    rfl

end SIS
