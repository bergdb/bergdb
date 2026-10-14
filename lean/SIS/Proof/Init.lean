/-
Proofs, part 6: the invariant holds after T(0).
-/
import SIS.Proof.Run
import SIS.Assumptions

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Ordering by level -/

/-- The level of node a in P (0 if a is not in P). -/
def lev (P : Struct V) (a : NodeId) : Nat := ((P.get? a).map (·.level)).getD 0

theorem lev_of_get? {P : Struct V} {a : NodeId} {n : Node V} (h : P.get? a = some n) :
    lev P a = n.level := by
  simp [lev, h]

theorem byLevel_perm (P : Struct V) (xs : List NodeId) : List.Perm (byLevel P xs) xs :=
  List.mergeSort_perm _ _

theorem byLevel_pairwise (P : Struct V) (xs : List NodeId) :
    (byLevel P xs).Pairwise (fun a b => lev P a ≤ lev P b) := by
  have h := List.pairwise_mergeSort (le := fun a b => decide (((P.get? a).map (·.level)).getD 0 ≤
      ((P.get? b).map (·.level)).getD 0))
    (by intro a b c h1 h2; simp only [decide_eq_true_eq] at *; omega)
    (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs
  simpa [lev, byLevel] using h

/-- In a list of versions sorted by level, a version of a node on a lower
level comes first. -/
theorem lower_first {P : Struct V} {L : List (Version V)}
    (hN : (L.map (·.node)).Pairwise (fun a b => lev P a ≤ lev P b)) {p q : Nat}
    (hp : p < L.length) (hq : q < L.length) (hlt : lev P L[q].node < lev P L[p].node) : q < p := by
  rw [List.pairwise_map] at hN
  rcases Nat.lt_trichotomy q p with h | h | h
  · exact h
  · subst h; omega
  · have := List.pairwise_iff_getElem.mp hN p q hp hq h
    omega

/-! ### T(0) -/

section Init

variable (sp : Spec V T)

/-- The versions of R(0). -/
def initVers : List (Version V) :=
  writeAll sp [] 0 sp.init (byLevel sp.init (sp.init.map (·.1))) []

theorem init_eq : init sp =
    { P := sp.init, D := [],
      S := [{ trans := none, sp := 0, vers := initVers sp, gd := [],
              top := ((Stream.building ([] : Stream V T) (initVers sp)).lv root).map (·.recNo) }] } :=
  rfl

theorem init_P : (init sp).P = sp.init := rfl
theorem init_D : (init sp).D = [] := rfl

theorem initVers_built : Built sp [] 0 sp.init (initVers sp) :=
  built_writeAll _ (built_nil sp [] 0 sp.init)

theorem initVers_nodes (_hok : SpecOK sp) :
    (initVers sp).map (·.node) = byLevel sp.init (sp.init.map (·.1)) := by
  unfold initVers
  rw [writeAll_nodes]
  simp only [List.map_nil, List.nil_append]
  apply List.filter_eq_self.mpr
  intro x hx
  have hx' : x ∈ sp.init.map (·.1) := (byLevel_perm _ _).mem_iff.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx'
  exact get?_isSome_of_mem (by simpa using hp)

theorem initVers_nodup (hok : SpecOK sp) : ((initVers sp).map (·.node)).Nodup := by
  rw [initVers_nodes sp hok]
  exact (byLevel_perm _ _).nodup_iff.mpr hok.initDistinct

theorem initVers_mem_node (hok : SpecOK sp) {x : NodeId} (hx : (sp.init.get? x).isSome) :
    ∃ v ∈ initVers sp, v.node = x := by
  have : x ∈ (initVers sp).map (·.node) := by
    rw [initVers_nodes sp hok]
    apply (byLevel_perm _ _).mem_iff.mpr
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
    exact List.mem_map.mpr ⟨(x, n), mem_of_get? hn, rfl⟩
  simpa using this

theorem lv_init (_hok : SpecOK sp) (x : NodeId) :
    Stream.lv (init sp).S x = (initVers sp).find? (fun v => v.node == x) := by
  rw [init_eq]
  simp [Stream.lv]

theorem init_good (hok : SpecOK sp) : ∀ (b : Nat) (p : Nat) (hp : p < (initVers sp).length),
    (initVers sp)[p].level < b → good sp (init sp).S sp.init 0 (initVers sp)[p] = true := by
  have hB := initVers_built sp
  have hnd := initVers_nodup sp hok
  have hN : ((initVers sp).map (·.node)).Pairwise (fun a b => lev sp.init a ≤ lev sp.init b) := by
    rw [initVers_nodes sp hok]; exact byLevel_pairwise _ _
  intro b
  induction b with
  | zero => intro p hp h; omega
  | succ b ih =>
    intro p hp hb
    obtain ⟨n, hn, heq⟩ := hB p hp
    rw [good_iff]
    refine ⟨⟨n, hn, ?_⟩, ?_⟩
    · rw [heq]; rfl
    · intro y hy
      have hvh : (initVers sp)[p].hist = n.hist := by rw [heq]; rfl
      obtain ⟨e, he, hye⟩ := hok.liveSub _ _ hy
      have he' : e ∈ n.hist := by rw [← hvh]; exact (mem_upTo.mp he).1
      obtain ⟨m, hm, hlt⟩ := hok.initLevels _ (mem_of_get? hn) e he' y hye
      obtain ⟨w, hw, hwy⟩ := initVers_mem_node sp hok (by rw [hm]; rfl)
      obtain ⟨q, hq, rfl⟩ := List.getElem_of_mem hw
      have hqp : q < p := by
        apply lower_first hN hp hq
        rw [hwy, lev_of_get? hm, lev_of_get? hn]
        exact hlt
      obtain ⟨m', hm', heq'⟩ := hB q hq
      rw [hwy] at hm'
      rw [hm] at hm'
      cases hm'
      refine ⟨0, (initVers sp)[q], ?_, ?_, ?_, ?_⟩
      · rw [heq, ref?_mkVersion]
        have hyp : y ∈ pointees sp n.hist := by
          simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
          exact ⟨e, he', hye⟩
        rw [ite_eq_left_iff.mpr (fun h => absurd hyp h), lv_building, lv_nil, Option.or_none]
        have hfind : ((initVers sp).take p).find? (fun v => v.node == y) = some (initVers sp)[q] := by
          apply find?_node_of_mem
          · exact (List.take_sublist p _).map _ |>.nodup hnd
          · exact List.mem_take_iff_getElem.mpr ⟨q, Nat.lt_min.mpr ⟨hqp, hq⟩, rfl⟩
          · exact hwy
        rw [hfind]
        simp only [Option.map_some]
        rw [heq']
        rfl
      · show Stream.versionAt (init sp).S 0 y = some (initVers sp)[q]
        rw [init_eq]
        simp only [Stream.versionAt, List.getElem?_cons_zero]
        exact find?_node_of_mem hnd hw hwy
      · rw [heq', heq]
        simp only [mkVersion]
        exact hlt
      · exact ih q hq (by rw [heq'] at *; rw [heq] at hb; simp [mkVersion] at *; omega)

theorem inv_init (hok : SpecOK sp) : Inv sp (init sp) 0 := by
  have hB := initVers_built sp
  have hnd := initVers_nodup sp hok
  -- The latest version of every node of the initial structure is in R(0).
  have hlv : ∀ x, (sp.init.get? x).isSome → ∃ p, ∃ hp : p < (initVers sp).length,
      Stream.lv (init sp).S x = some (initVers sp)[p] ∧ (initVers sp)[p].node = x := by
    intro x hx
    obtain ⟨w, hw, hwx⟩ := initVers_mem_node sp hok hx
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hw
    exact ⟨p, hp, by rw [lv_init sp hok]; exact find?_node_of_mem hnd hw hwx, hwx⟩
  -- Every node is clean.
  have hclean : ∀ x, (sp.init.get? x).isSome → dirty sp (init sp).S sp.init 0 x = false := by
    intro x hx
    obtain ⟨p, hp, h1, -⟩ := hlv x hx
    rw [dirty_false_iff]
    refine ⟨_, h1, fun t ht _ => ?_⟩
    have : t = 0 := by omega
    subst this
    exact init_good sp hok ((initVers sp)[p].level + 1) p hp (by omega)
  constructor
  · rfl
  · intro r R hR v hv
    rw [init_eq] at hR
    cases r with
    | zero =>
      simp at hR; subst hR
      obtain ⟨n, pre, -, -, h, -⟩ := built_mem hB hv
      exact h
    | succ r => simp at hR
  · intro r R hR
    rw [init_eq] at hR
    cases r with
    | zero => simp at hR; subst hR; exact hnd
    | succ r => simp at hR
  · right; exact ⟨rfl, rfl⟩
  · intro r R hR v hv
    rw [init_eq] at hR
    cases r with
    | zero =>
      simp at hR; subst hR
      obtain ⟨n, pre, hn, -, -, h1, h2, h3, -⟩ := built_mem hB hv
      refine ⟨n, hn, ?_, h2, h3⟩
      rw [h1, upTo_of_forall]
      intro e he
      rw [hok.initTime _ (mem_of_get? hn) e he]
      exact Nat.le_refl 0
    | succ r => simp at hR
  · intro r R hR v hv
    rw [init_eq] at hR
    cases r with
    | zero =>
      simp at hR; subst hR
      obtain ⟨n, pre, -, hpre, -, -, -, -, h⟩ := built_mem hB hv
      exact ⟨pre, hpre, by simpa using h⟩
    | succ r => simp at hR
  · intro R hR
    rw [init_eq] at hR ⊢
    simp at hR
    subst hR
    simp [Stream.lv, Stream.building]
  · intro x n hn e he
    rw [hok.initTime _ (mem_of_get? hn) e he]
    exact Nat.le_refl 0
  · exact fun x n hn e he y hy => hok.initLevels _ (mem_of_get? hn) e he y hy
  · exact fun x n hn hd e he => hok.initData _ (mem_of_get? hn) hd e he
  · intro x n hn e he
    rw [hok.initTime _ (mem_of_get? hn) e he]
    exact hok.initReachable _ (mem_of_get? hn)
  · exact hok.initRoot
  · intro x hx
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
    exact ⟨0, Nat.le_refl 0, hok.initReachable _ (mem_of_get? hn)⟩
  · rfl
  · simp [init_eq]
  · simp [init_eq]
  · intro x hx hd
    change isIndex sp.init x = true at hx
    have : (sp.init.get? x).isSome := by
      unfold isIndex at hx
      cases h : sp.init.get? x <;> simp_all
    rw [init_P, hclean x this] at hd
    simp at hd
  · simp [init_eq]
  · simp [init_eq]
  · intro x n hn hd
    rw [init_P] at hn
    obtain ⟨p, hp, h1, h2⟩ := hlv x (by rw [hn]; rfl)
    refine ⟨_, h1, ?_⟩
    obtain ⟨n', hn', heq⟩ := hB p hp
    rw [h2, hn] at hn'
    cases hn'
    rw [heq]; rfl

end Init

end SIS
