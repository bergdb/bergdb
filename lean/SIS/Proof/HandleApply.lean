/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 6:
the change applied to the canonical objects (`HMem.applyChange`): the new
nodes' objects and live handles, and the shapes of the objects after the adds,
with `HMem.newPtr`, as SIS/Proof/EvictApply.lean shows for Evict.lean.
-/
import SIS.Proof.HandleWalk
import SIS.Proof.EvictInit

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Congruences -/

/-- The canonical objects of m' are m's when the table and the handles are the
same and every object keeps its flag. -/
theorem HMem.canonicalOf_congr {m m' : HMem V} (ht : ∀ y, m'.tableOf y = m.tableOf y)
    (hh : ∀ n, m'.handle? n = m.handle? n)
    (ho : ∀ a, (m'.obj? a).map (·.canonical) = (m.obj? a).map (·.canonical)) (y : NodeId) :
    m'.canonicalOf y = m.canonicalOf y := by
  have hof : m'.objOf = m.objOf := by funext n; unfold HMem.objOf; rw [hh]
  unfold HMem.canonicalOf
  rw [ht, hof]
  cases (m.tableOf y).bind m.objOf with
  | none => rfl
  | some a =>
    simp only
    have h := ho a
    cases h1 : m'.obj? a with
    | none =>
      cases h2 : m.obj? a with
      | none => rfl
      | some o2 => rw [h1, h2] at h; cases h
    | some o1 =>
      cases h2 : m.obj? a with
      | none => rw [h1, h2] at h; cases h
      | some o2 =>
        rw [h1, h2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        simp only [h]

/-- The record rule for pointer p in m' is m's when Rule R's startup position is
the same, p's handle is the same, and the object it holds keeps its flag and
position. -/
theorem HMem.ptrRef_congr {m m' : HMem V} (S0 : Stream V T) (hs : m'.s = m.s) {p : HPtr}
    (hh : p.handle.bind m'.handle? = p.handle.bind m.handle?)
    (ho : ∀ hd b, p.handle.bind m.handle? = some hd → hd.obj = some b →
      (m'.obj? b).map (fun o => (o.canonical, o.pos)) = (m.obj? b).map (fun o => (o.canonical, o.pos)))
    (y : NodeId) : m'.ptrRef S0 y p = m.ptrRef S0 y p := by
  unfold HMem.ptrRef
  rw [hs, hh]
  cases hph : p.handle.bind m.handle? with
  | none => rfl
  | some hd =>
    simp only
    cases hb : hd.obj with
    | none => rfl
    | some b =>
      simp only [Option.bind_some]
      have h := ho hd b hph hb
      cases h1 : m'.obj? b with
      | none =>
        cases h2 : m.obj? b with
        | none => rfl
        | some o2 => rw [h1, h2] at h; cases h
      | some o1 =>
        cases h2 : m.obj? b with
        | none => rw [h1, h2] at h; cases h
        | some o2 =>
          rw [h1, h2] at h
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          simp only [h.1, h.2]

/-- A canonical object is the one object of its node in the table's handle. -/
theorem HTableOK.canonicalOf_node {m : HMem V} (ht : HTableOK m) {z : NodeId} {b : Nat}
    (h : m.canonicalOf z = some b) : ∃ o, m.obj? b = some o ∧ o.node = z ∧ o.canonical = true := by
  obtain ⟨n, o, htz, hob, ho, hc⟩ := (m.canonicalOf_eq_some z b).mp h
  obtain ⟨hd, b', o', hh, -, -, hb', ho', hon'⟩ := ht.entry htz
  have hbb : b' = b := by
    have h0 := hob
    unfold HMem.objOf at h0
    rw [hh] at h0
    simp only [Option.bind_some] at h0
    rw [hb'] at h0
    exact Option.some.inj h0
  subst hbb
  rw [ho', Option.some.injEq] at ho
  subst ho
  exact ⟨o', ho', hon', hc⟩

/-- A canonical object in memory is its node's canonical object. -/
theorem HTableOK.canonicalOf_of {m : HMem V} (ht : HTableOK m) {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) (hc : o.canonical = true) : m.canonicalOf o.node = some a := by
  obtain ⟨n, htb, hob⟩ := ht.held ho
  exact (m.canonicalOf_eq_some o.node a).mpr ⟨n, o, htb, hob, ho, hc⟩

/-- The table's keys after an entry is set do not repeat. -/
theorem HMem.setTable_nodup (m : HMem V) (y : NodeId) (n : Nat) (hnd : (m.table.map (·.1)).Nodup) :
    ((m.setTable y n).table.map (·.1)).Nodup := by
  unfold HMem.setTable
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hnd⟩
  intro hmem
  obtain ⟨q, hq, hqy⟩ := List.mem_map.mp hmem
  have := (List.mem_filter.mp hq).2
  rw [hqy] at this
  simp at this

/-! ## The new nodes -/

/-- The canonical object of a new node. -/
def hnewObj (nn : NewNode) : HObj V :=
  { node := nn.id, level := nn.level, isData := nn.isData, hist := [], canonical := true,
    pos := none, ptrs := [] }

/-- The live handle of a new node, which holds its object at address a. -/
def hnewHandle (nn : NewNode) (a : Nat) : Handle :=
  { node := nn.id, obj := some a, written := none, dead := false }

/-- The memory with a new node's object at the next free address, and the
counters raised. -/
def addNewH0 (m : HMem V) (nn : NewNode) : HMem V :=
  { m with objs := (m.nextObj, hnewObj nn) :: m.objs, nextObj := m.nextObj + 1, nextHandle := m.nextHandle + 1 }

/-- Add the canonical object of a new node, with a new live handle in the table
(`HMem.applyChange`, 02, 4.5: "a node the writer makes gets its handle at
once"). -/
def addNewH (m : HMem V) (nn : NewNode) : HMem V :=
  ((addNewH0 m nn).setHandle m.nextHandle (hnewHandle nn m.nextObj)).setTable nn.id m.nextHandle

theorem addNewH_obj (m : HMem V) (nn : NewNode) (a : Nat) :
    (addNewH m nn).obj? a = if a = m.nextObj then some (hnewObj nn) else m.obj? a := by
  unfold addNewH
  rw [HMem.obj?_setTable, HMem.obj?_setHandle]
  unfold addNewH0 HMem.obj?
  exact lookup_cons_eq _ _ _ _

theorem addNewH_handle (m : HMem V) (nn : NewNode) (n : Nat) :
    (addNewH m nn).handle? n = if n = m.nextHandle then some (hnewHandle nn m.nextObj) else m.handle? n := by
  unfold addNewH
  rw [HMem.handle?_setTable, HMem.handle?_setHandle]
  rfl

theorem addNewH_table (m : HMem V) (nn : NewNode) (y : NodeId) :
    (addNewH m nn).tableOf y = if y = nn.id then some m.nextHandle else m.tableOf y := by
  unfold addNewH
  rw [HMem.tableOf_setTable, HMem.tableOf_setHandle]
  rfl

@[simp] theorem addNewH_nextObj (m : HMem V) (nn : NewNode) : (addNewH m nn).nextObj = m.nextObj + 1 := rfl
@[simp] theorem addNewH_nextHandle (m : HMem V) (nn : NewNode) :
    (addNewH m nn).nextHandle = m.nextHandle + 1 := rfl
@[simp] theorem addNewH_s (m : HMem V) (nn : NewNode) : (addNewH m nn).s = m.s := rfl
@[simp] theorem addNewH_root (m : HMem V) (nn : NewNode) : (addNewH m nn).root = m.root := rfl

theorem addNewH_freshO (m : HMem V) (nn : NewNode) (hfr : ∀ a, m.nextObj ≤ a → m.obj? a = none) :
    ∀ a, (addNewH m nn).nextObj ≤ a → (addNewH m nn).obj? a = none := by
  intro a ha
  rw [addNewH_nextObj] at ha
  rw [addNewH_obj]
  simp only [show a ≠ m.nextObj by omega, ↓reduceIte]
  exact hfr a (by omega)

theorem addNewH_freshH (m : HMem V) (nn : NewNode) (hfr : ∀ n, m.nextHandle ≤ n → m.handle? n = none) :
    ∀ n, (addNewH m nn).nextHandle ≤ n → (addNewH m nn).handle? n = none := by
  intro n hn
  rw [addNewH_nextHandle] at hn
  rw [addNewH_handle]
  simp only [show n ≠ m.nextHandle by omega, ↓reduceIte]
  exact hfr n (by omega)

/-- One new node keeps the table and the handles right, when the node has no
entry in the table yet. -/
theorem addNewH_tbl (m : HMem V) (nn : NewNode) (ht : HTableOK m)
    (hfrO : ∀ a, m.nextObj ≤ a → m.obj? a = none) (hfrH : ∀ n, m.nextHandle ≤ n → m.handle? n = none)
    (hnew : m.tableOf nn.id = none) : HTableOK (addNewH m nn) := by
  have hhlt : ∀ n hd, m.handle? n = some hd → n < m.nextHandle := by
    intro n hd h; exact Nat.lt_of_not_le (fun hle => by rw [hfrH n hle] at h; cases h)
  have holt : ∀ a o, m.obj? a = some o → a < m.nextObj := by
    intro a o h; exact Nat.lt_of_not_le (fun hle => by rw [hfrO a hle] at h; cases h)
  -- No live handle of the new node.
  have hnolive : ∀ n hd, m.handle? n = some hd → hd.dead = false → hd.node ≠ nn.id := by
    intro n hd hh hl he
    have := ht.liveIn hh hl
    rw [he, hnew] at this; cases this
  refine ⟨?_, HMem.setTable_nodup ((addNewH0 m nn).setHandle m.nextHandle (hnewHandle nn m.nextObj)) nn.id
    m.nextHandle ht.nodup, ?_, ?_, ?_, ?_⟩
  · intro y n hy
    rw [addNewH_table] at hy
    split at hy
    · rename_i hyn
      simp only [Option.some.injEq] at hy
      subst hy
      refine ⟨hnewHandle nn m.nextObj, m.nextObj, hnewObj nn, by rw [addNewH_handle]; simp, rfl,
        by rw [hyn]; rfl, rfl, by rw [addNewH_obj]; simp, by rw [hyn]; rfl⟩
    · obtain ⟨hd, a, o, hh, hl, hny, ha, ho, hon⟩ := ht.entry hy
      have hn' : n ≠ m.nextHandle := Nat.ne_of_lt (hhlt n hd hh)
      have ha' : a ≠ m.nextObj := Nat.ne_of_lt (holt a o ho)
      exact ⟨hd, a, o, by rw [addNewH_handle]; simp only [hn', ↓reduceIte]; exact hh, hl, hny, ha,
        by rw [addNewH_obj]; simp only [ha', ↓reduceIte]; exact ho, hon⟩
  · intro n hd hh hl
    rw [addNewH_handle] at hh
    rw [addNewH_table]
    split at hh
    · rename_i hn
      simp only [Option.some.injEq] at hh
      subst hh
      simp [hnewHandle, hn]
    · have h1 := ht.liveIn hh hl
      have hne := hnolive n hd hh hl
      simp only [hne, ↓reduceIte]
      exact h1
  · intro n hd hh hdd
    rw [addNewH_handle] at hh
    split at hh
    · simp only [Option.some.injEq] at hh; subst hh; simp [hnewHandle] at hdd
    · exact ht.deadNone hh hdd
  · intro a o ho
    rw [addNewH_obj] at ho
    split at ho
    · rename_i ha
      simp only [Option.some.injEq] at ho
      subst ho
      refine ⟨m.nextHandle, by rw [addNewH_table]; simp [hnewObj], ?_⟩
      unfold HMem.objOf
      rw [addNewH_handle]
      simp [hnewHandle, ha]
    · obtain ⟨n, htn, hon⟩ := ht.held ho
      have hne : o.node ≠ nn.id := by intro he; rw [he, hnew] at htn; cases htn
      refine ⟨n, by rw [addNewH_table]; simp only [hne, ↓reduceIte]; exact htn, ?_⟩
      have hob : (m.handle? n).bind (·.obj) = some a := hon
      cases hhn : m.handle? n with
      | none => rw [hhn] at hob; cases hob
      | some hd =>
        have hn' : n ≠ m.nextHandle := Nat.ne_of_lt (hhlt n hd hhn)
        unfold HMem.objOf
        rw [addNewH_handle]
        simp only [hn', ↓reduceIte]
        exact hon
  · intro a o y p n ho hp hpn
    rw [addNewH_obj] at ho
    split at ho
    · simp only [Option.some.injEq] at ho; subst ho; simp [hnewObj, HObj.ptr?] at hp
    · obtain ⟨hd, hh, hy⟩ := ht.ptrNode ho hp hpn
      have hn' : n ≠ m.nextHandle := Nat.ne_of_lt (hhlt n hd hh)
      exact ⟨hd, by rw [addNewH_handle]; simp only [hn', ↓reduceIte]; exact hh, hy⟩

section Fold

variable (N : List NewNode)

theorem foldl_addNewH_nextObj : ∀ (m : HMem V), (N.foldl addNewH m).nextObj = m.nextObj + N.length := by
  induction N with
  | nil => intro m; rfl
  | cons nn N ih => intro m; simp only [List.foldl_cons, ih, addNewH_nextObj, List.length_cons]; omega

theorem foldl_addNewH_nextHandle : ∀ (m : HMem V),
    (N.foldl addNewH m).nextHandle = m.nextHandle + N.length := by
  induction N with
  | nil => intro m; rfl
  | cons nn N ih => intro m; simp only [List.foldl_cons, ih, addNewH_nextHandle, List.length_cons]; omega

theorem foldl_addNewH_parts : ∀ (m : HMem V), (N.foldl addNewH m).s = m.s ∧ (N.foldl addNewH m).root = m.root := by
  induction N with
  | nil => intro m; exact ⟨rfl, rfl⟩
  | cons nn N ih => intro m; simp only [List.foldl_cons]; exact ih _

theorem foldl_addNewH_old : ∀ (m : HMem V) (a : Nat), a < m.nextObj → (N.foldl addNewH m).obj? a = m.obj? a := by
  induction N with
  | nil => intro m a _; rfl
  | cons nn N ih =>
    intro m a ha
    simp only [List.foldl_cons]
    rw [ih _ a (by rw [addNewH_nextObj]; omega), addNewH_obj]
    simp only [show a ≠ m.nextObj by omega, ↓reduceIte]

theorem foldl_addNewH_hold : ∀ (m : HMem V) (n : Nat), n < m.nextHandle →
    (N.foldl addNewH m).handle? n = m.handle? n := by
  induction N with
  | nil => intro m n _; rfl
  | cons nn N ih =>
    intro m n hn
    simp only [List.foldl_cons]
    rw [ih _ n (by rw [addNewH_nextHandle]; omega), addNewH_handle]
    simp only [show n ≠ m.nextHandle by omega, ↓reduceIte]

theorem foldl_addNewH_table_old : ∀ (m : HMem V) (y : NodeId), y ∉ N.map (·.id) →
    (N.foldl addNewH m).tableOf y = m.tableOf y := by
  induction N with
  | nil => intro m y _; rfl
  | cons nn N ih =>
    intro m y hy
    simp only [List.map_cons, List.mem_cons, not_or] at hy
    simp only [List.foldl_cons]
    rw [ih _ y hy.2, addNewH_table]
    simp only [hy.1, ↓reduceIte]

theorem foldl_addNewH_freshO : ∀ (m : HMem V), (∀ a, m.nextObj ≤ a → m.obj? a = none) →
    ∀ a, (N.foldl addNewH m).nextObj ≤ a → (N.foldl addNewH m).obj? a = none := by
  induction N with
  | nil => intro m hfr a ha; exact hfr a ha
  | cons nn N ih =>
    intro m hfr a ha
    simp only [List.foldl_cons] at ha ⊢
    exact ih _ (addNewH_freshO m nn hfr) a ha

theorem foldl_addNewH_freshH : ∀ (m : HMem V), (∀ n, m.nextHandle ≤ n → m.handle? n = none) →
    ∀ n, (N.foldl addNewH m).nextHandle ≤ n → (N.foldl addNewH m).handle? n = none := by
  induction N with
  | nil => intro m hfr n hn; exact hfr n hn
  | cons nn N ih =>
    intro m hfr n hn
    simp only [List.foldl_cons] at hn ⊢
    exact ih _ (addNewH_freshH m nn hfr) n hn

theorem foldl_addNewH_nodup : ∀ (m : HMem V), (∀ a, m.nextObj ≤ a → m.obj? a = none) →
    (m.objs.map (·.1)).Nodup → ((N.foldl addNewH m).objs.map (·.1)).Nodup := by
  induction N with
  | nil => intro m _ hnd; exact hnd
  | cons nn N ih =>
    intro m hfr hnd
    simp only [List.foldl_cons]
    apply ih _ (addNewH_freshO m nn hfr)
    show (((m.nextObj, hnewObj nn) :: m.objs).map (·.1)).Nodup
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, hnd⟩
    obtain ⟨q, hq, hqa⟩ := List.mem_map.mp hmem
    have h1 := lookup_ne_none_of_mem hq
    change m.obj? q.1 ≠ none at h1
    rw [hqa, hfr _ (Nat.le_refl _)] at h1
    exact h1 rfl

theorem foldl_addNewH_hnodup : ∀ (m : HMem V), (m.handles.map (·.1)).Nodup →
    ((N.foldl addNewH m).handles.map (·.1)).Nodup := by
  induction N with
  | nil => intro m hnd; exact hnd
  | cons nn N ih =>
    intro m hnd
    simp only [List.foldl_cons]
    apply ih
    exact setHandle_nodup (addNewH0 m nn) m.nextHandle (hnewHandle nn m.nextObj) hnd

theorem foldl_addNewH_tnodup : ∀ (m : HMem V), (m.table.map (·.1)).Nodup →
    ((N.foldl addNewH m).table.map (·.1)).Nodup := by
  induction N with
  | nil => intro m hnd; exact hnd
  | cons nn N ih =>
    intro m hnd
    simp only [List.foldl_cons]
    apply ih
    exact HMem.setTable_nodup ((addNewH0 m nn).setHandle m.nextHandle (hnewHandle nn m.nextObj)) nn.id
      m.nextHandle hnd

theorem foldl_addNewH_tbl (hnd : (N.map (·.id)).Nodup) : ∀ (m : HMem V), HTableOK m →
    (∀ a, m.nextObj ≤ a → m.obj? a = none) → (∀ n, m.nextHandle ≤ n → m.handle? n = none) →
    (∀ nn ∈ N, m.tableOf nn.id = none) → HTableOK (N.foldl addNewH m) := by
  induction N with
  | nil => intro m ht _ _ _; exact ht
  | cons nn0 N ih =>
    intro m ht hfrO hfrH hnew
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    apply ih hnd.2 _ (addNewH_tbl m nn0 ht hfrO hfrH (hnew nn0 List.mem_cons_self))
      (addNewH_freshO m nn0 hfrO) (addNewH_freshH m nn0 hfrH)
    intro nn hnn
    rw [addNewH_table]
    have hne : nn.id ≠ nn0.id := by
      intro he; apply hnd.1; rw [← he]; exact List.mem_map.mpr ⟨nn, hnn, rfl⟩
    simp only [hne, ↓reduceIte]
    exact hnew nn (List.mem_cons_of_mem _ hnn)

/-- After the new nodes: each has its canonical object and its live handle, new. -/
theorem foldl_addNewH_new (hnd : (N.map (·.id)).Nodup) : ∀ (m : HMem V), ∀ nn ∈ N, ∃ a n,
    m.nextObj ≤ a ∧ m.nextHandle ≤ n ∧ (N.foldl addNewH m).tableOf nn.id = some n ∧
      (N.foldl addNewH m).handle? n = some (hnewHandle nn a) ∧
      (N.foldl addNewH m).obj? a = some (hnewObj nn) := by
  induction N with
  | nil => intro m nn h; cases h
  | cons nn0 N ih =>
    intro m nn hnn
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hnn with h | h
    · subst h
      refine ⟨m.nextObj, m.nextHandle, Nat.le_refl _, Nat.le_refl _, ?_, ?_, ?_⟩
      · rw [foldl_addNewH_table_old N _ _ hnd.1, addNewH_table]; simp
      · rw [foldl_addNewH_hold N _ _ (by rw [addNewH_nextHandle]; omega), addNewH_handle]; simp
      · rw [foldl_addNewH_old N _ _ (by rw [addNewH_nextObj]; omega), addNewH_obj]; simp
    · obtain ⟨a, n, hle, hle', ht, hh, ho⟩ := ih hnd.2 (addNewH m nn0) nn h
      rw [addNewH_nextObj] at hle
      rw [addNewH_nextHandle] at hle'
      exact ⟨a, n, by omega, by omega, ht, hh, ho⟩

/-- The objects after the new nodes: the old ones, and the new nodes'. -/
theorem foldl_addNewH_obj (hnd : (N.map (·.id)).Nodup) :
    ∀ (m : HMem V), (∀ a, m.nextObj ≤ a → m.obj? a = none) → ∀ (a : Nat) (o : HObj V),
    (N.foldl addNewH m).obj? a = some o → (a < m.nextObj ∧ m.obj? a = some o) ∨
      (m.nextObj ≤ a ∧ ∃ nn ∈ N, o = hnewObj nn ∧ ∃ n, (N.foldl addNewH m).tableOf nn.id = some n ∧
        (N.foldl addNewH m).handle? n = some (hnewHandle nn a)) := by
  induction N with
  | nil =>
    intro m hfr a o ho
    simp only [List.foldl_nil] at ho
    left
    exact ⟨Nat.lt_of_not_le (fun hle => by rw [hfr a hle] at ho; cases ho), ho⟩
  | cons nn0 N ih =>
    intro m hfr a o ho
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons] at ho ⊢
    rcases ih hnd.2 (addNewH m nn0) (addNewH_freshO m nn0 hfr) a o ho with
      ⟨hlt, ho'⟩ | ⟨hle, nn, hnn, hon, n, ht, hh⟩
    · rw [addNewH_obj] at ho'
      rw [addNewH_nextObj] at hlt
      split at ho'
      · rename_i ha
        cases ho'
        right
        refine ⟨by omega, nn0, List.mem_cons_self, rfl, m.nextHandle, ?_, ?_⟩
        · rw [foldl_addNewH_table_old N _ _ hnd.1, addNewH_table]; simp
        · rw [foldl_addNewH_hold N _ _ (by rw [addNewH_nextHandle]; omega), addNewH_handle, ha]; simp
      · left; exact ⟨by omega, ho'⟩
    · right
      rw [addNewH_nextObj] at hle
      exact ⟨by omega, nn, List.mem_cons_of_mem _ hnn, hon, n, ht, hh⟩

/-- The handles after the new nodes: the old ones, and the new nodes' live
handles. -/
theorem foldl_addNewH_handle (hnd : (N.map (·.id)).Nodup) :
    ∀ (m : HMem V), (∀ a, m.nextObj ≤ a → m.obj? a = none) → (∀ n, m.nextHandle ≤ n → m.handle? n = none) →
    ∀ (n : Nat) (hd : Handle), (N.foldl addNewH m).handle? n = some hd →
      (n < m.nextHandle ∧ m.handle? n = some hd) ∨
      (m.nextHandle ≤ n ∧ ∃ nn ∈ N, ∃ a, m.nextObj ≤ a ∧ hd = hnewHandle nn a ∧
        (N.foldl addNewH m).tableOf nn.id = some n ∧ (N.foldl addNewH m).obj? a = some (hnewObj nn)) := by
  induction N with
  | nil =>
    intro m _ hfr n hd hh
    simp only [List.foldl_nil] at hh
    left
    exact ⟨Nat.lt_of_not_le (fun hle => by rw [hfr n hle] at hh; cases hh), hh⟩
  | cons nn0 N ih =>
    intro m hfrO hfrH n hd hh
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons] at hh ⊢
    rcases ih hnd.2 (addNewH m nn0) (addNewH_freshO m nn0 hfrO) (addNewH_freshH m nn0 hfrH) n hd hh with
      ⟨hlt, hh'⟩ | ⟨hle, nn, hnn, a, hla, hhd, ht, ho⟩
    · rw [addNewH_handle] at hh'
      rw [addNewH_nextHandle] at hlt
      split at hh'
      · rename_i hn
        cases hh'
        right
        refine ⟨by omega, nn0, List.mem_cons_self, m.nextObj, Nat.le_refl _, rfl, ?_, ?_⟩
        · rw [foldl_addNewH_table_old N _ _ hnd.1, addNewH_table, hn]; simp
        · rw [foldl_addNewH_old N _ _ (by rw [addNewH_nextObj]; omega), addNewH_obj]; simp
      · left; exact ⟨by omega, hh'⟩
    · right
      rw [addNewH_nextHandle] at hle
      rw [addNewH_nextObj] at hla
      exact ⟨by omega, nn, List.mem_cons_of_mem _ hnn, a, by omega, hhd, ht, ho⟩

end Fold

/-! ## The pointers of new entries -/

section Ptrs

variable (sp : Spec V T) (P : Struct V) (j : Time)

/-- The copied pointer, if there is a source. -/
def srcPtrH (m : HMem V) (y : NodeId) : Option HPtr :=
  (m.objs.find? (srcOKH sp P j y)).bind (fun p => p.2.ptr? y)

/-- The pointer to y's canonical object: y's live handle, with the object's
position as the reference. -/
def canPtrH (m : HMem V) (y : NodeId) : Option HPtr :=
  (m.canonicalOf y).map (fun b => ({ ref := (m.obj? b).bind (·.pos), handle := m.tableOf y } : HPtr))

/-- The new pointer that does not depend on the object: to y's canonical
object, or copied from a source. -/
def NSH (m : HMem V) (y : NodeId) : Option HPtr :=
  (canPtrH m y).or (srcPtrH sp P j m y)

theorem newPtr_eq (m : HMem V) (o : HObj V) (y : NodeId) :
    m.newPtr sp P j o y = (NSH sp P j m y).or (o.ptr? y) := by
  unfold HMem.newPtr NSH srcPtrH canPtrH
  cases hc : m.canonicalOf y with
  | some b => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    cases hf : m.objs.find? (srcOKH sp P j y) with
    | some p =>
      simp only [Option.bind_some]
      have hp := List.find?_some hf
      unfold srcOKH at hp
      simp only [Bool.and_eq_true] at hp
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hp.1.1.1.2
      rw [hq]; rfl
    | none => rfl

/-- One pointer of a new entry. -/
def upd1H (m1 : HMem V) (o' : HObj V) (y : NodeId) : HObj V :=
  match m1.newPtr sp P j o' y with
  | some p => o'.putPtr y p
  | none => o'

theorem upd1H_core (m1 : HMem V) (o' : HObj V) (y : NodeId) : (upd1H sp P j m1 o' y).core = o'.core := by
  unfold upd1H
  split
  · exact HObj.putPtr_core _ _ _
  · rfl

/-- The pointer that a pointee gets: NSH, or the object's own pointer. -/
def comboH (m1 : HMem V) (o : HObj V) (y : NodeId) : Option HPtr :=
  (NSH sp P j m1 y).or (o.ptr? y)

theorem upd1H_ptr (m1 : HMem V) (o' : HObj V) (y y' : NodeId) :
    (upd1H sp P j m1 o' y).ptr? y' = if y' = y then comboH sp P j m1 o' y else o'.ptr? y' := by
  unfold upd1H comboH
  rw [newPtr_eq]
  cases hc : (NSH sp P j m1 y).or (o'.ptr? y) with
  | none =>
    simp only
    split
    · rename_i hy; subst hy
      simp only [Option.or_eq_none_iff] at hc
      exact hc.2
    · rfl
  | some p =>
    simp only
    rw [HObj.ptr?_putPtr]

theorem comboH_idem (m1 : HMem V) (o : HObj V) (y : NodeId) (o' : HObj V)
    (h : o'.ptr? y = comboH sp P j m1 o y) : comboH sp P j m1 o' y = comboH sp P j m1 o y := by
  unfold comboH at h ⊢
  rw [h]
  cases NSH sp P j m1 y with
  | some _ => rfl
  | none => rfl

theorem foldl_upd1H_ptr (m1 : HMem V) (ys : List NodeId) : ∀ (o : HObj V) (y' : NodeId),
    (ys.foldl (upd1H sp P j m1) o).ptr? y' = if y' ∈ ys then comboH sp P j m1 o y' else o.ptr? y' := by
  induction ys with
  | nil => intro o y'; simp
  | cons y ys ih =>
    intro o y'
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hy : y' ∈ ys
    · simp only [hy, ↓reduceIte, List.mem_cons, or_true]
      by_cases hyy : y' = y
      · subst hyy
        apply comboH_idem
        rw [upd1H_ptr]; simp
      · unfold comboH
        rw [upd1H_ptr]
        simp only [hyy, ↓reduceIte]
    · simp only [hy, ↓reduceIte, List.mem_cons, or_false]
      rw [upd1H_ptr]
      by_cases hyy : y' = y
      · subst hyy; simp
      · simp [hyy]

theorem foldl_upd1H_core (m1 : HMem V) (ys : List NodeId) : ∀ (o : HObj V),
    (ys.foldl (upd1H sp P j m1) o).core = o.core := by
  induction ys with
  | nil => intro o; rfl
  | cons y ys ih => intro o; simp only [List.foldl_cons]; rw [ih, upd1H_core]

theorem comboH_congr (m1 : HMem V) {o o' : HObj V} {y : NodeId} (h : o'.ptr? y = o.ptr? y) :
    comboH sp P j m1 o' y = comboH sp P j m1 o y := by
  unfold comboH; rw [h]

/-- One entry v of the transaction applied to the canonical object o. -/
def updObjH (m1 : HMem V) (o : HObj V) (v : V) : HObj V :=
  (sp.ptrs v).foldl (upd1H sp P j m1) { o with hist := o.hist ++ [⟨j, v⟩] }

theorem updObjH_core (m1 : HMem V) (o : HObj V) (v : V) :
    (updObjH sp P j m1 o v).node = o.node ∧ (updObjH sp P j m1 o v).level = o.level ∧
    (updObjH sp P j m1 o v).isData = o.isData ∧ (updObjH sp P j m1 o v).hist = o.hist ++ [⟨j, v⟩] ∧
    (updObjH sp P j m1 o v).canonical = o.canonical ∧ (updObjH sp P j m1 o v).pos = o.pos := by
  have := foldl_upd1H_core sp P j m1 (sp.ptrs v) { o with hist := o.hist ++ [⟨j, v⟩] }
  unfold updObjH
  simp only [HObj.core, Prod.mk.injEq] at this
  exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem updObjH_ptr (m1 : HMem V) (o : HObj V) (v : V) (y : NodeId) :
    (updObjH sp P j m1 o v).ptr? y = if y ∈ sp.ptrs v then comboH sp P j m1 o y else o.ptr? y := by
  unfold updObjH
  rw [foldl_upd1H_ptr]
  split
  · exact comboH_congr sp P j m1 rfl
  · rfl

/-- The entries of a list of adds, in turn. -/
def updAllH (m1 : HMem V) (L : List (NodeId × V)) (o : HObj V) : HObj V :=
  L.foldl (fun o a => updObjH sp P j m1 o a.2) o

theorem updAllH_core (m1 : HMem V) (L : List (NodeId × V)) : ∀ (o : HObj V),
    (updAllH sp P j m1 L o).node = o.node ∧ (updAllH sp P j m1 L o).level = o.level ∧
    (updAllH sp P j m1 L o).isData = o.isData ∧
    (updAllH sp P j m1 L o).hist = o.hist ++ L.map (fun a => (⟨j, a.2⟩ : Entry V)) ∧
    (updAllH sp P j m1 L o).canonical = o.canonical ∧ (updAllH sp P j m1 L o).pos = o.pos := by
  induction L with
  | nil => intro o; simp [updAllH]
  | cons a L ih =>
    intro o
    unfold updAllH at ih ⊢
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (updObjH sp P j m1 o a.2)
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := updObjH_core sp P j m1 o a.2
    refine ⟨by rw [a1, b1], by rw [a2, b2], by rw [a3, b3], by rw [a4, b4]; simp, by rw [a5, b5],
      by rw [a6, b6]⟩

theorem updAllH_ptr (m1 : HMem V) (L : List (NodeId × V)) : ∀ (o : HObj V) (y : NodeId),
    (updAllH sp P j m1 L o).ptr? y =
      if y ∈ L.flatMap (fun a => sp.ptrs a.2) then comboH sp P j m1 o y else o.ptr? y := by
  induction L with
  | nil => intro o y; simp [updAllH]
  | cons a L ih =>
    intro o y
    unfold updAllH at ih ⊢
    simp only [List.foldl_cons]
    rw [ih, List.flatMap_cons]
    by_cases h1 : y ∈ L.flatMap (fun a => sp.ptrs a.2)
    · simp only [h1, ↓reduceIte, List.mem_append, or_true]
      by_cases h2 : y ∈ sp.ptrs a.2
      · apply comboH_idem
        rw [updObjH_ptr]; simp [h2]
      · apply comboH_congr
        rw [updObjH_ptr]; simp [h2]
    · simp only [h1, ↓reduceIte, List.mem_append, or_false]
      rw [updObjH_ptr]

/-- One add: the entry appended to its node's canonical object. -/
def addsStepH (m1 : HMem V) (m : HMem V) (a : NodeId × V) : HMem V :=
  match m.canonicalOf a.1 with
  | none => m
  | some b =>
    match m.obj? b with
    | none => m
    | some o => m.setObj b (updObjH sp P j m1 o a.2)

theorem applyChangeH_eq (m : HMem V) (c : Changes V) :
    m.applyChange sp P j c =
      c.adds.foldl (addsStepH sp P j (c.new.foldl addNewH m)) (c.new.foldl addNewH m) := rfl

end Ptrs

/-! ## The memory after the adds -/

/-- The objects after the adds: each canonical object of a changed node has its
node's adds, the others are as before; the table, the handles and the counters
are as before. -/
theorem adds_foldH (sp : Spec V T) (P : Struct V) (j : Time) (m1 : HMem V) (L : List (NodeId × V)) :
    ∀ (L0 : List (NodeId × V)) (m : HMem V),
    m.table = m1.table → m.handles = m1.handles → m.nextObj = m1.nextObj → m.nextHandle = m1.nextHandle →
    m.s = m1.s → m.root = m1.root →
    (∀ a, m.obj? a = (m1.obj? a).map
      (updAllH sp P j m1 (L0.filter (fun e => m1.canonicalOf e.1 == some a)))) →
    (L.foldl (addsStepH sp P j m1) m).table = m1.table ∧
    (L.foldl (addsStepH sp P j m1) m).handles = m1.handles ∧
    (L.foldl (addsStepH sp P j m1) m).nextObj = m1.nextObj ∧
    (L.foldl (addsStepH sp P j m1) m).nextHandle = m1.nextHandle ∧
    (L.foldl (addsStepH sp P j m1) m).s = m1.s ∧
    (L.foldl (addsStepH sp P j m1) m).root = m1.root ∧
    (∀ a, (L.foldl (addsStepH sp P j m1) m).obj? a = (m1.obj? a).map
      (updAllH sp P j m1 ((L0 ++ L).filter (fun e => m1.canonicalOf e.1 == some a)))) ∧
    (((m.objs.map (·.1)).Nodup) → ((L.foldl (addsStepH sp P j m1) m).objs.map (·.1)).Nodup) := by
  induction L with
  | nil =>
    intro L0 m ht hh hn hnh hs hr ho
    simp only [List.foldl_nil, List.append_nil]
    exact ⟨ht, hh, hn, hnh, hs, hr, ho, id⟩
  | cons e L ih =>
    intro L0 m ht hh hn hnh hs hr ho
    simp only [List.foldl_cons]
    have hcan : ∀ y, m.canonicalOf y = m1.canonicalOf y := by
      apply HMem.canonicalOf_congr
      · intro y; unfold HMem.tableOf; rw [ht]
      · intro n; unfold HMem.handle?; rw [hh]
      · intro a
        rw [ho a]
        cases m1.obj? a with
        | none => rfl
        | some o1 => simp only [Option.map_some, (updAllH_core sp P j m1 _ o1).2.2.2.2.1]
    have hstep : ∀ a, (addsStepH sp P j m1 m e).obj? a = (m1.obj? a).map
        (updAllH sp P j m1 ((L0 ++ [e]).filter (fun e => m1.canonicalOf e.1 == some a))) := by
      intro a
      unfold addsStepH
      rw [hcan]
      cases hc : m1.canonicalOf e.1 with
      | none =>
        simp only
        rw [ho a, List.filter_append]
        simp [hc]
      | some b =>
        simp only
        rw [ho b]
        cases ho1 : m1.obj? b with
        | none =>
          simp only [Option.map_none]
          rw [ho a, List.filter_append]
          by_cases hab : a = b
          · subst hab; rw [ho1]; rfl
          · have : (some b == some a) = false := by simp [Ne.symm hab]
            simp [hc, this]
        | some o1 =>
          simp only [Option.map_some]
          rw [HMem.obj?_setObj]
          split
          · rename_i hab
            subst hab
            rw [ho1, List.filter_append]
            simp only [Option.map_some, Option.some.injEq]
            unfold updAllH
            simp [hc, List.foldl_append]
          · rename_i hab
            rw [ho a, List.filter_append]
            have : (some b == some a) = false := by simp [Ne.symm hab]
            simp [hc, this]
    have hm' : (addsStepH sp P j m1 m e).table = m1.table ∧ (addsStepH sp P j m1 m e).handles = m1.handles ∧
        (addsStepH sp P j m1 m e).nextObj = m1.nextObj ∧ (addsStepH sp P j m1 m e).nextHandle = m1.nextHandle ∧
        (addsStepH sp P j m1 m e).s = m1.s ∧ (addsStepH sp P j m1 m e).root = m1.root ∧
        (((m.objs.map (·.1)).Nodup) → ((addsStepH sp P j m1 m e).objs.map (·.1)).Nodup) := by
      unfold addsStepH
      split
      · exact ⟨ht, hh, hn, hnh, hs, hr, id⟩
      · split
        · exact ⟨ht, hh, hn, hnh, hs, hr, id⟩
        · exact ⟨ht, hh, hn, hnh, hs, hr, fun h => HMem.setObj_nodup m _ _ h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hm'
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := ih (L0 ++ [e]) _ h1 h2 h3 h4 h5 h6 hstep
    refine ⟨g1, g2, g3, g4, g5, g6, ?_, fun hnd => g8 (h7 hnd)⟩
    intro a
    rw [g7 a, List.append_assoc]
    rfl

/-- The memory m3 after the adds, from m1 after the new nodes. -/
structure ChangeFactsH (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m1 m3 : HMem V) : Prop where
  table : m3.table = m1.table
  handles : m3.handles = m1.handles
  obj : ∀ a, m3.obj? a = (m1.obj? a).map
    (updAllH sp P j m1 (c.adds.filter (fun e => m1.canonicalOf e.1 == some a)))
  nextObj : m3.nextObj = m1.nextObj
  nextHandle : m3.nextHandle = m1.nextHandle
  s : m3.s = m1.s
  root : m3.root = m1.root
  nodup : (m1.objs.map (·.1)).Nodup → (m3.objs.map (·.1)).Nodup

theorem changeFactsH (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V) (m : HMem V) :
    ChangeFactsH sp P j c (c.new.foldl addNewH m) (m.applyChange sp P j c) := by
  have h := adds_foldH sp P j (c.new.foldl addNewH m) c.adds [] (c.new.foldl addNewH m) rfl rfl rfl rfl rfl rfl
    (by intro a; cases (c.new.foldl addNewH m).obj? a <;> rfl)
  rw [← applyChangeH_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, fun a => by rw [h7 a]; rfl, h3, h4, h5, h6, h8⟩

section CF

variable {sp : Spec V T} {P : Struct V} {j : Time} {c : Changes V} {m1 m3 : HMem V}

theorem ChangeFactsH.tableOf (hcf : ChangeFactsH sp P j c m1 m3) (y : NodeId) : m3.tableOf y = m1.tableOf y := by
  unfold HMem.tableOf; rw [hcf.table]

theorem ChangeFactsH.handle? (hcf : ChangeFactsH sp P j c m1 m3) (n : Nat) : m3.handle? n = m1.handle? n := by
  unfold HMem.handle?; rw [hcf.handles]

theorem ChangeFactsH.objOf (hcf : ChangeFactsH sp P j c m1 m3) (n : Nat) : m3.objOf n = m1.objOf n := by
  unfold HMem.objOf; rw [hcf.handle? n]

/-- Every object keeps its node, kind, level, flag and position. -/
theorem ChangeFactsH.keep (hcf : ChangeFactsH sp P j c m1 m3) (a : Nat) :
    (m3.obj? a).map (fun o => (o.node, o.level, o.isData, o.canonical, o.pos)) =
      (m1.obj? a).map (fun o => (o.node, o.level, o.isData, o.canonical, o.pos)) := by
  rw [hcf.obj a]
  cases m1.obj? a with
  | none => rfl
  | some o1 =>
    obtain ⟨a1, a2, a3, -, a5, a6⟩ := updAllH_core sp P j m1
      (c.adds.filter (fun e => m1.canonicalOf e.1 == some a)) o1
    simp only [Option.map_some, a1, a2, a3, a5, a6]

theorem ChangeFactsH.canonicalOf (hcf : ChangeFactsH sp P j c m1 m3) (y : NodeId) :
    m3.canonicalOf y = m1.canonicalOf y := by
  apply HMem.canonicalOf_congr (hcf.tableOf) (hcf.handle?)
  intro a
  rw [hcf.obj a]
  cases m1.obj? a with
  | none => rfl
  | some o1 => simp only [Option.map_some, (updAllH_core sp P j m1 _ o1).2.2.2.2.1]

end CF

/-! ## The memory after the new nodes, from a memory with the invariant -/

/-- The memory m1 after the new nodes' objects and handles: m's objects and
handles, and for each new node a canonical object with a live handle in the
table; m's table and canonical objects for the other nodes. -/
structure HAddFacts (m m1 : HMem V) (c : Changes V) : Prop where
  old : ∀ a, a < m.nextObj → m1.obj? a = m.obj? a
  cls : ∀ a o, m1.obj? a = some o → (a < m.nextObj ∧ m.obj? a = some o) ∨
    (m.nextObj ≤ a ∧ ∃ nn ∈ c.new, o = hnewObj nn ∧ m1.canonicalOf nn.id = some a)
  hold : ∀ n, n < m.nextHandle → m1.handle? n = m.handle? n
  hcls : ∀ n hd, m1.handle? n = some hd → (n < m.nextHandle ∧ m.handle? n = some hd) ∨
    (m.nextHandle ≤ n ∧ ∃ nn ∈ c.new, ∃ a, m.nextObj ≤ a ∧ hd = hnewHandle nn a ∧
      m1.tableOf nn.id = some n ∧ m1.obj? a = some (hnewObj nn))
  canOld : ∀ y, y ∉ c.new.map (·.id) → m1.canonicalOf y = m.canonicalOf y
  tabOld : ∀ y, y ∉ c.new.map (·.id) → m1.tableOf y = m.tableOf y
  canNew : ∀ nn ∈ c.new, ∃ a n, m.nextObj ≤ a ∧ m1.tableOf nn.id = some n ∧ m1.objOf n = some a ∧
    m1.canonicalOf nn.id = some a ∧ m1.obj? a = some (hnewObj nn)
  freshO : ∀ a, m1.nextObj ≤ a → m1.obj? a = none
  freshH : ∀ n, m1.nextHandle ≤ n → m1.handle? n = none
  nodup : (m1.objs.map (·.1)).Nodup
  hnodup : (m1.handles.map (·.1)).Nodup
  tbl : HTableOK m1
  s : m1.s = m.s
  root : m1.root = m.root
  nextObj : m1.nextObj = m.nextObj + c.new.length
  nextHandle : m1.nextHandle = m.nextHandle + c.new.length

section AddFacts

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V} {c : Changes V}

/-- Every object in memory is of a node of P. -/
theorem HEInv.node_of_obj (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) : ∃ n, db.P.get? o.node = some n := by
  cases hco : o.canonical with
  | true => obtain ⟨n, hn, -⟩ := hm.cc a o ho hco; exact ⟨n, hn⟩
  | false =>
    obtain ⟨r, w, -, hw, -⟩ := hm.snap a o ho hco
    obtain ⟨-, -, n, hn, -⟩ := hinv.version_node hw
    exact ⟨n, hn⟩

/-- A new node has no entry in the table. -/
theorem HEInv.tableOf_new (hinv : Inv sp db k) (hm : HEInv sp db S0 k m)
    (hstep : StepOK sp db.P (k + 1) c) : ∀ nn ∈ c.new, m.tableOf nn.id = none := by
  intro nn hnn
  cases ht : m.tableOf nn.id with
  | none => rfl
  | some n =>
    exfalso
    obtain ⟨hd, a, o, -, -, -, -, ho, hon⟩ := hm.tbl.entry ht
    obtain ⟨n', hn'⟩ := hm.node_of_obj hinv ho
    rw [hon, hstep.fresh nn hnn] at hn'
    cases hn'

theorem HEInv.addFactsH (hinv : Inv sp db k) (hm : HEInv sp db S0 k m)
    (hstep : StepOK sp db.P (k + 1) c) : HAddFacts m (c.new.foldl addNewH m) c := by
  have hnd := hstep.distinct
  have htbl := foldl_addNewH_tbl c.new hnd m hm.tbl hm.freshO hm.freshH (hm.tableOf_new hinv hstep)
  have hcanNew : ∀ nn ∈ c.new, ∃ a n, m.nextObj ≤ a ∧ (c.new.foldl addNewH m).tableOf nn.id = some n ∧
      (c.new.foldl addNewH m).objOf n = some a ∧ (c.new.foldl addNewH m).canonicalOf nn.id = some a ∧
      (c.new.foldl addNewH m).obj? a = some (hnewObj nn) := by
    intro nn hnn
    obtain ⟨a, n, hle, -, ht, hh, ho⟩ := foldl_addNewH_new c.new hnd m nn hnn
    have hob : (c.new.foldl addNewH m).objOf n = some a := by
      unfold HMem.objOf; rw [hh]; rfl
    exact ⟨a, n, hle, ht, hob, ((c.new.foldl addNewH m).canonicalOf_eq_some nn.id a).mpr
      ⟨n, hnewObj nn, ht, hob, ho, rfl⟩, ho⟩
  have hhlt : ∀ n hd, m.handle? n = some hd → n < m.nextHandle := by
    intro n hd h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshH n hle] at h; cases h)
  have holt : ∀ a o, m.obj? a = some o → a < m.nextObj := by
    intro a o h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshO a hle] at h; cases h)
  refine
    { old := foldl_addNewH_old c.new m
      cls := ?_
      hold := foldl_addNewH_hold c.new m
      hcls := foldl_addNewH_handle c.new hnd m hm.freshO hm.freshH
      canOld := ?_
      tabOld := foldl_addNewH_table_old c.new m
      canNew := hcanNew
      freshO := foldl_addNewH_freshO c.new m hm.freshO
      freshH := foldl_addNewH_freshH c.new m hm.freshH
      nodup := foldl_addNewH_nodup c.new m hm.freshO hm.objNodup
      hnodup := foldl_addNewH_hnodup c.new m hm.hNodup
      tbl := htbl
      s := (foldl_addNewH_parts c.new m).1
      root := (foldl_addNewH_parts c.new m).2
      nextObj := foldl_addNewH_nextObj c.new m
      nextHandle := foldl_addNewH_nextHandle c.new m }
  · intro a o ho
    rcases foldl_addNewH_obj c.new hnd m hm.freshO a o ho with h | ⟨hle, nn, hnn, hon, n, ht, hh⟩
    · exact Or.inl h
    · right
      refine ⟨hle, nn, hnn, hon, ((c.new.foldl addNewH m).canonicalOf_eq_some nn.id a).mpr
        ⟨n, o, ht, by unfold HMem.objOf; rw [hh]; rfl, ho, by rw [hon]; rfl⟩⟩
  · intro y hy
    unfold HMem.canonicalOf
    rw [foldl_addNewH_table_old c.new m y hy]
    cases ht : m.tableOf y with
    | none => rfl
    | some n =>
      obtain ⟨hd, a, o, hh, -, -, ha, ho, -⟩ := hm.tbl.entry ht
      have hob : (c.new.foldl addNewH m).objOf n = m.objOf n := by
        unfold HMem.objOf; rw [foldl_addNewH_hold c.new m n (hhlt n hd hh)]
      simp only [Option.bind_some]
      rw [hob]
      have hmo : m.objOf n = some a := by unfold HMem.objOf; rw [hh]; exact ha
      rw [hmo]
      simp only
      rw [foldl_addNewH_old c.new m a (holt a o ho)]

/-- With A-COPY's sources, the new pointer of a pointee exists. -/
theorem HEInv.NSH_some (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {path : List NodeId}
    (hpd : ∀ x ∈ path, HPathDone sp db.P k path m x) (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (hpn : ∀ p ∈ path, (db.P.get? p).isSome) (hstep : StepOK sp db.P (k + 1) c) {y : NodeId}
    (hy : y ∈ c.new.map (·.id) ∨ y ∈ path ∨ ∃ z ∈ path, ∃ nz, db.P.get? z = some nz ∧
      y ∈ pointees sp nz.hist ∧ (written sp z = true ∨ y ∈ sp.live (nz.hist.upTo k))) :
    (NSH sp db.P (k + 1) (c.new.foldl addNewH m) y).isSome := by
  have haf := hm.addFactsH hinv hstep
  unfold NSH canPtrH
  cases hc : (c.new.foldl addNewH m).canonicalOf y with
  | some b => rfl
  | none =>
    simp only [Option.map_none, Option.none_or]
    rcases hy with hy | hy | ⟨z, hz, nz, hnz, hyz, hwl⟩
    · exfalso
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
      obtain ⟨a, n, -, -, -, hc', -⟩ := haf.canNew nn hnn
      rw [hid, hc] at hc'; cases hc'
    · exfalso
      obtain ⟨hcy, -⟩ := hpd y hy
      obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (hpn y hy)
      rw [haf.canOld y (not_new_of_get? hstep hny)] at hc
      rw [hc] at hcy; cases hcy
    · -- The canonical object of z, a node of the path, is a source.
      obtain ⟨hcz, -⟩ := hpd z hz
      obtain ⟨bz, hbz⟩ := Option.isSome_iff_exists.mp hcz
      obtain ⟨oz, hoz, hcoz, hnoz⟩ := hm.obj_of_canonicalOf hbz
      obtain ⟨n', hn', hh', -, -⟩ := hm.cc bz oz hoz hcoz
      rw [hnoz, hnz, Option.some.injEq] at hn'
      subst hn'
      have hrz := hpath z hz
      have hsl : (oz.ptr? y).isSome := by
        rcases hwl with hw | hl
        · obtain ⟨p, hp, -⟩ := hm.slots bz oz hoz
            ⟨hcoz, by rw [hnoz]; exact hw, Or.inl (by rw [hnoz]; exact hrz)⟩ y (by rw [hh']; exact hyz)
          rw [hp]; rfl
        · have hyl : y ∈ sp.live oz.hist := by
            rw [hh', ← upTo_of_forall _ _ (hinv.times z nz hnz)]; exact hl
          obtain ⟨p, hp, -⟩ := hm.live bz oz hoz hcoz (by rw [hnoz]; exact hrz) y hyl
          rw [hp]; rfl
      have hlt : bz < m.nextObj := Nat.lt_of_not_le (fun h => by rw [hm.freshO bz h] at hoz; cases hoz)
      have hmem : (bz, oz) ∈ (c.new.foldl addNewH m).objs := by
        apply mem_of_lookup
        show (c.new.foldl addNewH m).obj? bz = some oz
        rw [haf.old bz hlt]; exact hoz
      have hsrc : srcOKH sp db.P (k + 1) y (bz, oz) = true := by
        unfold srcOKH
        simp only [Bool.and_eq_true, Bool.or_eq_true, hcoz, hsl, true_and]
        refine ⟨⟨List.contains_iff_mem.mpr (by rw [hh']; exact hyz), by
          rw [hnoz]; simpa using hrz⟩, ?_⟩
        rcases hwl with hw | hl
        · left; rw [hnoz]; exact hw
        · right; rw [hnoz, hnz]; simpa using hl
      have hfind := List.find?_isSome.mpr ⟨_, hmem, hsrc⟩
      unfold srcPtrH
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hfind
      rw [hp]
      have hpp := List.find?_some hp
      unfold srcOKH at hpp
      simp only [Bool.and_eq_true] at hpp
      simpa using hpp.1.1.1.2

/-- The new pointer of a pointee: to its canonical object, through its live
handle; or, for a pointee with none (so not in D, not new), a copy of a pointer
of m whose record is its latest version. -/
theorem HEInv.NSH_good (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hstep : StepOK sp db.P (k + 1) c)
    {y : NodeId} {p : HPtr} (hns : NSH sp db.P (k + 1) (c.new.foldl addNewH m) y = some p) :
    (∃ b, (c.new.foldl addNewH m).canonicalOf y = some b ∧
      p = { ref := ((c.new.foldl addNewH m).obj? b).bind (·.pos), handle := (c.new.foldl addNewH m).tableOf y }) ∨
    ((c.new.foldl addNewH m).canonicalOf y = none ∧ inD db.D y = false ∧ y ∉ c.new.map (·.id) ∧
      m.ptrRef S0 y p = (db.S.lv y).map (·.recNo) ∧
      ∃ a0 o0, m.obj? a0 = some o0 ∧ o0.ptr? y = some p) := by
  have haf := hm.addFactsH hinv hstep
  unfold NSH canPtrH at hns
  cases hc : (c.new.foldl addNewH m).canonicalOf y with
  | some b =>
    rw [hc] at hns
    simp only [Option.map_some, Option.some_or, Option.some.injEq] at hns
    exact Or.inl ⟨b, rfl, hns.symm⟩
  | none =>
    rw [hc] at hns
    simp only [Option.map_none, Option.none_or] at hns
    right
    have hyn : y ∉ c.new.map (·.id) := by
      intro hy
      obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
      obtain ⟨a, n, -, -, -, hc', -⟩ := haf.canNew nn hnn
      rw [hid, hc] at hc'; cases hc'
    have hcm : m.canonicalOf y = none := by rw [← haf.canOld y hyn]; exact hc
    have hyD : inD db.D y = false := by
      cases hyd : inD db.D y with
      | false => rfl
      | true => have := hm.dCanon y hyd; rw [hcm] at this; cases this
    unfold srcPtrH at hns
    cases hf : (c.new.foldl addNewH m).objs.find? (srcOKH sp db.P (k + 1) y) with
    | none => rw [hf] at hns; cases hns
    | some q =>
      rw [hf] at hns
      simp only [Option.bind_some] at hns
      have hpp := List.find?_some hf
      have hpm := List.mem_of_find?_eq_some hf
      unfold srcOKH at hpp
      simp only [Bool.and_eq_true, Bool.or_eq_true] at hpp
      obtain ⟨⟨⟨⟨hcan, -⟩, hyp⟩, hrp⟩, hwl⟩ := hpp
      have hpo1 : (c.new.foldl addNewH m).obj? q.1 = some q.2 := lookup_of_mem _ haf.nodup q hpm
      -- The source is an object of m: a new node's object has no pointers.
      have hpo : m.obj? q.1 = some q.2 := by
        rcases haf.cls q.1 q.2 hpo1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
        · exact h2
        · exfalso; rw [hon] at hns; simp [hnewObj, HObj.ptr?] at hns
      have hK1 : k + 1 - 1 = k := by omega
      rw [hK1] at hrp hwl
      refine ⟨rfl, hyD, hyn, ?_, q.1, q.2, hpo, hns⟩
      rcases hwl with hw | hl
      · obtain ⟨p', hp', hi⟩ := hm.slots q.1 q.2 hpo ⟨hcan, hw, Or.inl hrp⟩ y
          (List.contains_iff_mem.mp hyp)
        rw [hns, Option.some.injEq] at hp'
        subst hp'
        exact hi.1 hyD
      · obtain ⟨n, hn, hh, -, -⟩ := hm.cc q.1 q.2 hpo hcan
        rw [hn] at hl
        simp only [List.contains_iff_mem] at hl
        have hyl : y ∈ sp.live q.2.hist := by
          rw [hh, ← upTo_of_forall _ _ (hinv.times _ n hn)]; exact hl
        obtain ⟨p', hp', hi⟩ := hm.live q.1 q.2 hpo hcan hrp y hyl
        rw [hns, Option.some.injEq] at hp'
        subst hp'
        exact hi.2 hyD

/-- A node's canonical object after the new nodes: the adds for it are the
node's. -/
theorem adds_filter_nodeH {m1 : HMem V} (ht : HTableOK m1) {x : NodeId} {b : Nat}
    (hx : m1.canonicalOf x = some b) :
    c.adds.filter (fun e => m1.canonicalOf e.1 == some b) = c.adds.filter (fun e => e.1 == x) := by
  apply List.filter_congr
  intro e _
  obtain ⟨o, ho, hon, -⟩ := ht.canonicalOf_node hx
  cases hce : m1.canonicalOf e.1 == some b
  · simp only [Bool.false_eq, beq_eq_false_iff_ne, ne_eq]
    intro hex
    rw [hex] at hce
    simp [hx] at hce
  · simp only [beq_iff_eq] at hce
    obtain ⟨o', ho', hon', -⟩ := ht.canonicalOf_node hce
    rw [ho, Option.some.injEq] at ho'
    subst ho'
    simp [← hon', hon]

end AddFacts

end SIS
