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
  writeAll sp [] 0 sp.init (byLevel sp.init ((sp.init.map (·.1)).filter (written sp))) []

theorem init_eq : init sp =
    { P := sp.init, D := [],
      S := [{ trans := none, sp := 0, vers := initVers sp, gd := [],
              top := topOf sp sp.init (Stream.building ([] : Stream V T) (initVers sp)) 0 }] } :=
  rfl

theorem init_P : (init sp).P = sp.init := rfl
theorem init_D : (init sp).D = [] := rfl

theorem initVers_built : Built sp [] 0 sp.init (initVers sp) :=
  built_writeAll _ (built_nil sp [] 0 sp.init)

theorem initVers_nodes (_hok : SpecOK sp) :
    (initVers sp).map (·.node) = byLevel sp.init ((sp.init.map (·.1)).filter (written sp)) := by
  unfold initVers
  rw [writeAll_nodes]
  simp only [List.map_nil, List.nil_append]
  apply List.filter_eq_self.mpr
  intro x hx
  have hx' : x ∈ (sp.init.map (·.1)).filter (written sp) := (byLevel_perm _ _).mem_iff.mp hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hx').1
  exact get?_isSome_of_mem (by simpa using hp)

theorem initVers_nodup (hok : SpecOK sp) : ((initVers sp).map (·.node)).Nodup := by
  rw [initVers_nodes sp hok]
  exact (byLevel_perm _ _).nodup_iff.mpr (List.Pairwise.filter _ hok.initDistinct)

theorem initVers_mem_node (hok : SpecOK sp) {x : NodeId} (hx : (sp.init.get? x).isSome)
    (hw : written sp x = true) : ∃ v ∈ initVers sp, v.node = x := by
  have : x ∈ (initVers sp).map (·.node) := by
    rw [initVers_nodes sp hok]
    apply (byLevel_perm _ _).mem_iff.mpr
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨(x, n), mem_of_get? hn, rfl⟩, hw⟩
  simpa using this

theorem initVers_written (hok : SpecOK sp) {v : Version V} (hv : v ∈ initVers sp) :
    written sp v.node = true := by
  have : v.node ∈ (initVers sp).map (·.node) := List.mem_map_of_mem hv
  rw [initVers_nodes sp hok] at this
  exact (List.mem_filter.mp ((byLevel_perm _ _).mem_iff.mp this)).2

theorem lv_init (_hok : SpecOK sp) (x : NodeId) :
    Stream.lv (init sp).S x = (initVers sp).find? (fun v => v.node == x) := by
  rw [init_eq]
  simp [Stream.lv]

theorem written_of_ne_root {x : NodeId} (h : x ≠ root) : written sp x = true := by
  simp [written, h]

/-- In a state with the invariant, no entry points to the root. -/
theorem Inv.ptr_ne_root {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {x : NodeId} {n : Node V}
    (hx : db.P.get? x = some n) {e : Entry V} (he : e ∈ n.hist) {y : NodeId}
    (hy : y ∈ sp.ptrs e.val) : y ≠ root := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  exact SIS.ptr_ne_root h0 hinv.ptrs (fun x hx => by
    obtain ⟨t, -, hr⟩ := hinv.born x hx
    exact ⟨t, (reachable_iff _ _ _ _).mp hr⟩) hx he hy

/-- A node of D can be written: with a virtual root, the root is never in D. -/
theorem Inv.written_of_D {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : inD db.D x = true) : written sp x = true := by
  unfold written
  cases hv : sp.virt with
  | false => rfl
  | true =>
    have hr := (hinv.vr hv).rootND
    have hne : x ≠ root := by intro he; rw [he, hr] at hx; cases hx
    simp [hne]

/-- In the initial structure, no entry points to the root. -/
theorem init_ptr_ne_root (hok : SpecOK sp) {x : NodeId} {n : Node V} (hx : sp.init.get? x = some n)
    {e : Entry V} (he : e ∈ n.hist) {y : NodeId} (hy : y ∈ sp.ptrs e.val) : y ≠ root := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hok.initRoot
  exact ptr_ne_root h0 (fun x n hn e he y hy => hok.initLevels _ (mem_of_get? hn) e he y hy)
    (fun x hx => by
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨0, (reachable_iff _ _ _ _).mp (hok.initReachable _ (mem_of_get? hn))⟩) hx he hy

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
        (written_of_ne_root sp (init_ptr_ne_root sp hok hn he' hye))
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

theorem topOf_congr (P : Struct V) {S S' : Stream V T} (h : ∀ x, S.lv x = S'.lv x) (s : Nat) :
    topOf sp P S s = topOf sp P S' s := by
  unfold topOf topV
  simp only [h]

theorem get?_of_mem_nodup {P : Struct V} (hnd : (P.map (·.1)).Nodup) {p : NodeId × Node V}
    (hp : p ∈ P) : P.get? p.1 = some p.2 := by
  induction P with
  | nil => simp at hp
  | cons q P ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rw [get?_cons]
    rcases List.mem_cons.mp hp with rfl | hp'
    · simp
    · have hne : p.1 ≠ q.1 := fun h => hnd.1 ⟨p, hp', h⟩
      simp only [hne, ite_false]
      exact ih hnd.2 hp'

theorem length_le_one_of_nodup {l : List Nat} (hnd : l.Nodup) (hall : ∀ a ∈ l, ∀ b ∈ l, a = b) :
    l.length ≤ 1 := by
  match l, hnd, hall with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hnd, hall =>
    exfalso
    simp only [List.nodup_cons, List.mem_cons] at hnd
    exact hnd.1 (Or.inl (hall a (by simp) b (by simp)))

theorem pairwise_of_length_le_one {α : Type} {R : α → α → Prop} {l : List α} (h : l.length ≤ 1) :
    l.Pairwise R := by
  match l, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

/-- With a virtual root, `VInv` holds after T(0). -/
theorem vinv_init (hok : SpecOK sp) (hv : sp.virt = true) : VInv sp (init sp) 0 := by
  have hvi := hok.virtInit hv
  have hnd := initVers_nodup sp hok
  have hB := initVers_built sp
  have hwr : ∀ x, written sp x = true → x ≠ root := by
    intro x hx hxr; subst hxr; simp [written, hv] at hx
  -- The root children of the initial structure.
  have htopAt : ∀ z n, sp.init.get? z = some n → z ≠ root → sp.topLevel ≤ n.level →
      TopAt sp sp.init z n 0 := by
    intro z n hn hzr hl
    obtain ⟨hd, hne, -⟩ := hvi.initTop (z, n) (mem_of_get? hn) hzr hl
    exact ⟨hn, hzr, hl, hd, hne, fun e he => hok.initTime _ (mem_of_get? hn) e he⟩
  have hisTop : ∀ z, isTop sp sp.init z = true →
      z ≠ root ∧ ∃ n, sp.init.get? z = some n ∧ sp.topLevel ≤ n.level := by
    intro z hz
    simp only [isTop, Bool.and_eq_true, bne_iff_ne, ne_eq] at hz
    obtain ⟨hzr, hz⟩ := hz
    cases hn : sp.init.get? z with
    | none => rw [hn] at hz; simp at hz
    | some n => rw [hn] at hz; exact ⟨hzr, n, rfl, by simpa using hz⟩
  have huniq : ∀ z n y m, sp.init.get? z = some n → z ≠ root → sp.topLevel ≤ n.level →
      sp.init.get? y = some m → y ≠ root → sp.topLevel ≤ m.level → y = z := by
    intro z n y m hz hzr hzl hy hyr hyl
    exact (hvi.initTop (z, n) (mem_of_get? hz) hzr hzl).2.2 (y, m) (mem_of_get? hy) hyr hyl
  have htime : ∀ z m c, TopAt sp sp.init z m c → c = 0 := by
    rintro z m c ⟨hz, -, -, -, hne, hall⟩
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    rw [← hall e he]
    exact hok.initTime _ (mem_of_get? hz) e he
  -- No root child points to a root child.
  have hnoptr : ∀ z m, sp.init.get? z = some m → z ≠ root → sp.topLevel ≤ m.level →
      ∀ y ∈ pointees sp m.hist, isTop sp sp.init y = true → False := by
    intro z m hz hzr hzl y hy hyt
    simp only [pointees, List.mem_eraseDups, List.mem_flatMap] at hy
    obtain ⟨e, he, hye⟩ := hy
    obtain ⟨m', hm', hlt⟩ := hok.initLevels _ (mem_of_get? hz) e he y hye
    obtain ⟨hyr, m'', hm'', hyl⟩ := hisTop y hyt
    have := huniq z m y m'' hz hzr hzl hm'' hyr hyl
    subst this
    rw [hz] at hm'
    cases hm'
    simp at hlt
  -- The root's initial history.
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hok.initRoot
  have hrh := hvi.initRootHist n0 h0
  have hLlen : (sp.init.filter (fun p => p.1 != root && decide (sp.topLevel ≤ p.2.level))).length ≤ 1 := by
    have h1 := length_le_one_of_nodup
      (l := (sp.init.filter (fun p => p.1 != root && decide (sp.topLevel ≤ p.2.level))).map (·.1))
      ((List.filter_sublist.map _).nodup hok.initDistinct) (by
        intro a ha b hb
        simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq,
          decide_eq_true_eq] at ha hb
        obtain ⟨p, ⟨hp, hpr, hpl⟩, rfl⟩ := ha
        obtain ⟨q, ⟨hq, hqr, hql⟩, rfl⟩ := hb
        exact (huniq p.1 p.2 q.1 q.2 (get?_of_mem_nodup hok.initDistinct hp) hpr hpl
          (get?_of_mem_nodup hok.initDistinct hq) hqr hql).symm)
    simpa using h1
  constructor
  · exact hvi.rootPtrs
  · simp [init_eq, inD]
  · intro r R hR v hvR
    rw [init_eq] at hR
    cases r with
    | zero =>
      simp at hR; subst hR
      exact hwr _ (initVers_written sp hok hvR)
    | succ r => simp at hR
  · intro n hn
    rw [init_P] at hn
    exact ⟨hvi.rootIndex n hn, by simp [rootLevel, hn]⟩
  · intro z hz
    rw [init_P] at hz ⊢
    obtain ⟨hzr, n, hn, hl⟩ := hisTop z hz
    exact ⟨n, 0, htopAt z n hn hzr hl⟩
  · intro z m c hzt r w hw
    rw [init_P] at hzt
    unfold Stream.versionAt at hw
    rw [init_eq] at hw
    cases r with
    | zero =>
      simp only [List.getElem?_cons_zero] at hw
      obtain ⟨hwm, hwz⟩ := find?_node_spec hw
      obtain ⟨n, pre, hn, -, -, hvh, -⟩ := built_mem hB hwm
      rw [hwz, hzt.1, Option.some.injEq] at hn
      rw [hvh, hn]
    | succ r => simp at hw
  · intro n hn
    rw [init_P, h0] at hn
    cases hn
    rw [hrh]
    exact pairwise_of_length_le_one (by simpa using hLlen)
  · intro n hn e he
    rw [init_P, h0] at hn
    cases hn
    rw [init_P]
    rw [hrh] at he
    simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at he
    obtain ⟨p, ⟨hp, hpr, hpl⟩, rfl⟩ := he
    exact ⟨p.1, p.2, htopAt p.1 p.2 (get?_of_mem_nodup hok.initDistinct hp) hpr hpl, rfl⟩
  · intro z m c hzt n hn
    rw [init_P] at hzt hn
    rw [h0] at hn
    cases hn
    have hc := htime z m c hzt
    subst hc
    obtain ⟨hz, hzr, hzl, -⟩ := hzt
    rw [hrh]
    simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq]
    exact ⟨(z, m), ⟨mem_of_get? hz, hzr, hzl⟩, rfl⟩
  · intro z m c hzt y hy hyt
    rw [init_P] at hzt hyt
    obtain ⟨hz, hzr, hzl, -⟩ := hzt
    exact (hnoptr z m hz hzr hzl y hy hyt).elim
  · intro z m c y m' c' hzt hyt hlt
    rw [init_P] at hzt hyt
    have := htime z m c hzt
    have := htime y m' c' hyt
    omega
  · intro z v hz hlv hD y hy hyt
    rw [init_P] at hz hyt
    rw [lv_init sp hok] at hlv
    obtain ⟨hvm, hvz⟩ := find?_node_spec hlv
    obtain ⟨n, pre, hn, -, -, hvh, -⟩ := built_mem hB hvm
    rw [hvz] at hn
    obtain ⟨hzr, n', hn', hl⟩ := hisTop z hz
    rw [hn] at hn'
    cases hn'
    rw [hvh] at hy
    exact (hnoptr z n hn hzr hl y hy hyt).elim
  · intro z n hz hzt y hy hyt
    rw [init_P] at hz hzt hyt
    obtain ⟨hzr, n', hn', hl⟩ := hisTop z hzt
    rw [hz] at hn'
    cases hn'
    exact (hnoptr z n hz hzr hl y hy hyt).elim

theorem inv_init (hok : SpecOK sp) : Inv sp (init sp) 0 := by
  have hB := initVers_built sp
  have hnd := initVers_nodup sp hok
  -- The latest version of every written node of the initial structure is in R(0).
  have hlv : ∀ x, (sp.init.get? x).isSome → written sp x = true → ∃ p, ∃ hp : p < (initVers sp).length,
      Stream.lv (init sp).S x = some (initVers sp)[p] ∧ (initVers sp)[p].node = x := by
    intro x hx hw
    obtain ⟨w, hw, hwx⟩ := initVers_mem_node sp hok hx hw
    obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hw
    exact ⟨p, hp, by rw [lv_init sp hok]; exact find?_node_of_mem hnd hw hwx, hwx⟩
  -- Every written node is clean.
  have hclean : ∀ x, (sp.init.get? x).isSome → written sp x = true →
      dirty sp (init sp).S sp.init 0 x = false := by
    intro x hx hw
    obtain ⟨p, hp, h1, -⟩ := hlv x hx hw
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
    simp only [lastSp, List.getLast?_singleton, Option.map_some, Option.getD_some]
    exact topOf_congr sp _ (fun x => by simp [Stream.lv, Stream.building]) 0
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
  · intro x hx hw hd
    change isIndex sp.init x = true at hx
    have : (sp.init.get? x).isSome := by
      unfold isIndex at hx
      cases h : sp.init.get? x <;> simp_all
    rw [init_P, hclean x this hw] at hd
    simp at hd
  · simp [init_eq]
  · simp [init_eq]
  · intro x n hn hd
    rw [init_P] at hn
    have hw : written sp x = true := by
      cases hv : sp.virt
      · simp [written, hv]
      · by_cases hx : x = root
        · subst hx
          have := (hok.virtInit hv).rootIndex n hn
          rw [hd] at this; simp at this
        · exact written_of_ne_root sp hx
    obtain ⟨p, hp, h1, h2⟩ := hlv x (by rw [hn]; rfl) hw
    refine ⟨_, h1, ?_⟩
    obtain ⟨n', hn', heq⟩ := hB p hp
    rw [h2, hn] at hn'
    cases hn'
    rw [heq]; rfl
  · exact vinv_init sp hok

end Init

end SIS
