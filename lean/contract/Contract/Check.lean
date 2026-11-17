/-
The contract package (bergdb 030-04, section 7.4 (d)): the contract on a heap
that a program can hold. The trace checker keeps Java's tree in a hash map;
the invariants, the contents and the readers of Statement.lean and Read.lean
run on it as they stand (`Heap.tree`). The frame, clause 3 of the contract,
speaks of every node, so it is computed here over the nodes of the heap
(`frameCheck`), and `frameCheck_sound` proves that the computation gives
`Frame`: with it, `checkTx` gives the contract itself (`checkTx_sound`).
Nothing here needs Mathlib.
-/
import Std.Data.HashMap
import Contract.Statement

namespace Contract

/-- A tree that a program holds: the nodes in a hash map, and the space
roots. -/
structure Heap where
  objs : Std.HashMap NodeId Obj := {}
  roots : List (Time × NodeId) := []

/-- The heap as a tree. -/
def Heap.tree (h : Heap) : Tree := { obj := fun x => h.objs[x]?, roots := h.roots }

/-- The klongs ks' are ks, or ks with a time klong of i and more after it. -/
def extKs (i : Time) : List Klong → List Klong → Bool
  | [], [] => true
  | [], k :: _ => k == Klong.time i
  | _ :: _, [] => false
  | a :: r, b :: r' => a == b && extKs i r r'

/-- `Ext`, computed. -/
def extOk (i : Time) : Obj → Obj → Bool
  | .val h, .val h' => h' == h
  | .key n, .key n' => n'.level == n.level && n'.leaf == n.leaf && extKs i n.ks n'.ks
  | _, _ => false

/-- The space roots rs' are rs and more, the ones added of time i. -/
def rootsExt (i : Time) : List (Time × NodeId) → List (Time × NodeId) → Bool
  | [], new => new.all (fun r => r.1 == i)
  | _ :: _, [] => false
  | a :: r, b :: r' => a == b && rootsExt i r r'

/-- `Frame`, computed over the nodes of the two heaps. -/
def frameCheck (i : Time) (h : Heap) (D : List NodeId) (h' : Heap) : Bool :=
  h.objs.toList.all (fun xo => match h'.objs[xo.1]? with
    | some o' => extOk i xo.2 o' && (D.contains xo.1 || o' == xo.2)
    | none => false) &&
  h'.objs.toList.all (fun xo => match xo.2 with
    | .key _ => h.objs.contains xo.1 || D.contains xo.1
    | .val _ => true) &&
  rootsExt i h.roots h'.roots

/-- The contract for one traced transaction, computed. -/
def checkTx (p : Params) (i : Time) (h : Heap) (ops : List Op) (D : List NodeId)
    (h' : Heap) : Bool :=
  contractOk p i h.tree ops h'.tree && frameCheck i h D h'

theorem extKs_sound (i : Time) : ∀ ks ks' : List Klong, extKs i ks ks' = true →
    ks' = ks ∨ ∃ more, ks' = ks ++ Klong.time i :: more
  | [], [], _ => Or.inl rfl
  | [], k :: r, h => by
    simp [extKs] at h
    exact Or.inr ⟨r, by simp [h]⟩
  | _ :: _, [], h => by simp [extKs] at h
  | a :: r, b :: r', h => by
    simp [extKs] at h
    obtain ⟨hab, hr⟩ := h
    subst hab
    rcases extKs_sound i r r' hr with h1 | ⟨more, h1⟩
    · exact Or.inl (by rw [h1])
    · exact Or.inr ⟨more, by rw [h1]; rfl⟩

theorem extOk_sound (i : Time) (o o' : Obj) (h : extOk i o o' = true) : Ext i o o' := by
  cases o with
  | key n =>
    cases o' with
    | key n' =>
      simp [extOk] at h
      exact ⟨h.1.1, h.1.2, extKs_sound i _ _ h.2⟩
    | val h' => simp [extOk] at h
  | val v =>
    cases o' with
    | key n' => simp [extOk] at h
    | val v' => simpa [extOk, Ext] using h

theorem rootsExt_sound (i : Time) : ∀ rs rs' : List (Time × NodeId), rootsExt i rs rs' = true →
    ∃ new, rs' = rs ++ new ∧ ∀ r ∈ new, r.1 = i
  | [], new, h => ⟨new, rfl, by simpa [rootsExt] using h⟩
  | _ :: _, [], h => by simp [rootsExt] at h
  | a :: r, b :: r', h => by
    simp [rootsExt] at h
    obtain ⟨hab, hr⟩ := h
    obtain ⟨new, h1, h2⟩ := rootsExt_sound i r r' hr
    exact ⟨new, by rw [h1, hab]; rfl, h2⟩

/-- The computed frame gives the frame of the contract. -/
theorem frameCheck_sound (i : Time) (h : Heap) (D : List NodeId) (h' : Heap)
    (hc : frameCheck i h D h' = true) : Frame i h.tree D h'.tree := by
  simp only [frameCheck, Bool.and_eq_true, List.all_eq_true] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  refine ⟨?_, ?_, rootsExt_sound i _ _ h3⟩
  · intro x o hx
    have hm : (x, o) ∈ h.objs.toList := Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx
    have := h1 (x, o) hm
    simp only [Heap.tree]
    cases hx' : h'.objs[x]? with
    | none => simp [hx'] at this
    | some o' =>
      simp only [hx', Bool.and_eq_true, Bool.or_eq_true] at this
      refine ⟨o', rfl, extOk_sound i o o' this.1, ?_⟩
      intro hD
      rcases this.2 with h4 | h4
      · exact absurd (by simpa using h4) hD
      · simpa using h4
  · intro x n hx hno
    have hm : (x, Obj.key n) ∈ h'.objs.toList :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx
    have := h2 (x, Obj.key n) hm
    simp only [Bool.or_eq_true] at this
    rcases this with h4 | h4
    · have : x ∈ h.objs := Std.HashMap.contains_iff_mem.mp h4
      have h5 := Std.HashMap.mem_iff_isSome_getElem?.mp this
      simp only [Heap.tree] at hno
      simp [hno] at h5
    · simpa using h4

/-- What the trace checker computes for a transaction is the contract of
Statement.lean. -/
theorem checkTx_sound (p : Params) (i : Time) (h : Heap) (ops : List Op) (D : List NodeId)
    (h' : Heap) (hc : checkTx p i h ops D h' = true) :
    Contract p i h.tree ops D h'.tree := by
  simp only [checkTx, Bool.and_eq_true] at hc
  exact ⟨hc.1, frameCheck_sound i h D h' hc.2⟩

end Contract
