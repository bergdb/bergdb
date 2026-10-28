/-
Proofs about reclaim, part 18 (bergdb item 001, WP R5, T12 with eviction): a
memory with another object for the root (`Mem.withRoot`). After a restart from
a cut stream, the Level 4 memory is the one after the restart from the whole
stream but for the root's object: a virtual root rebuilt from the root children
that the cut stream still has. The physical writer and the cache operations do
the same on both while the two root objects agree from the first available
time on (`RootRel`).
-/
import SIS.Proof.CutLaterRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Another object for the root -/

/-- m with object oc for the root. -/
def Mem.withRoot (m : Mem V) (oc : Obj V) : Mem V :=
  { m with objs := m.objs.map (fun p => if p.1 == m.root then (m.root, oc) else p) }

section Basic

variable {m : Mem V} {oc : Obj V}

@[simp] theorem withRoot_table : (m.withRoot oc).table = m.table := rfl
@[simp] theorem withRoot_s : (m.withRoot oc).s = m.s := rfl
@[simp] theorem withRoot_root : (m.withRoot oc).root = m.root := rfl
@[simp] theorem withRoot_next : (m.withRoot oc).next = m.next := rfl

theorem withRoot_tableOf (y : NodeId) : (m.withRoot oc).tableOf y = m.tableOf y := rfl

theorem withRoot_obj? (h : Nat) :
    (m.withRoot oc).obj? h = if h = m.root then (m.obj? m.root).map (fun _ => oc) else m.obj? h := by
  unfold Mem.withRoot Mem.obj?
  exact lookup_map_set m.objs m.root h oc

theorem withRoot_obj?_ne {h : Nat} (hne : h ≠ m.root) : (m.withRoot oc).obj? h = m.obj? h := by
  rw [withRoot_obj?]; simp [hne]

theorem withRoot_obj?_root {oe : Obj V} (he : m.obj? m.root = some oe) :
    (m.withRoot oc).obj? m.root = some oc := by
  rw [withRoot_obj?]; simp [he]

/-- The filter of `setObj` and the map of `withRoot` commute: both keep the handles. -/
theorem filter_map_root (l : List (Nat × Obj V)) (r h : Nat) (oc : Obj V) :
    (l.map (fun p => if p.1 == r then (r, oc) else p)).filter (fun p => p.1 != h) =
      (l.filter (fun p => p.1 != h)).map (fun p => if p.1 == r then (r, oc) else p) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 = r
  · subst hp; simp
  · simp [hp]

theorem withRoot_setObj_ne {h : Nat} (hne : h ≠ m.root) (o : Obj V) :
    (m.withRoot oc).setObj h o = (m.setObj h o).withRoot oc := by
  unfold Mem.withRoot Mem.setObj
  simp only [List.map_cons, filter_map_root]
  have : (h == m.root) = false := by simp [hne]
  simp [this]

theorem withRoot_setObj_root (o o' : Obj V) :
    (m.withRoot oc).setObj m.root o = (m.setObj m.root o').withRoot o := by
  unfold Mem.withRoot Mem.setObj
  simp only [List.map_cons, filter_map_root, beq_self_eq_true, ↓reduceIte]
  congr 2
  apply List.map_congr_left
  intro p hp
  have hne : p.1 ≠ m.root := by
    have := (List.mem_filter.mp hp).2
    simpa using this
  simp [hne]

theorem withRoot_addObj (hne : m.next ≠ m.root) (o : Obj V) :
    (m.withRoot oc).addObj o = ((m.addObj o).1.withRoot oc, (m.addObj o).2) := by
  unfold Mem.withRoot Mem.addObj
  have : (m.next == m.root) = false := by simp [hne]
  simp only [List.map_cons, this, Bool.false_eq_true, ↓reduceIte]

theorem withRoot_setTable (y : NodeId) (h : Nat) :
    (m.withRoot oc).setTable y h = (m.setTable y h).withRoot oc := rfl

theorem withRoot_canonicalOf {oe : Obj V} (he : m.obj? m.root = some oe) (hc : oc.canonical = oe.canonical)
    (y : NodeId) : (m.withRoot oc).canonicalOf y = m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [withRoot_tableOf]
  cases m.tableOf y with
  | none => rfl
  | some h =>
    simp only
    by_cases hh : h = m.root
    · subst hh
      rw [withRoot_obj?_root he, he]
      simp [hc]
    · rw [withRoot_obj?_ne hh]

end Basic


/-! ## The two root objects -/

/-- The root's object after a restart from a cut stream (oc) and after the
restart from the whole stream (oe), each with the transactions since: the same
but for the history and the slots of the root children that only times before
f need. Without a virtual root, the same object. -/
structure RootRel (sp : Spec V T) (f : Time) (oc oe : Obj V) : Prop where
  nv : sp.virt = false → oc = oe
  node : oc.node = oe.node
  level : oc.level = oe.level
  isData : oc.isData = oe.isData
  canonical : oc.canonical = oe.canonical
  pos : oc.pos = oe.pos
  live : ∀ t, f ≤ t → sp.live (oc.hist.upTo t) = sp.live (oe.hist.upTo t)
  slots : ∀ y, y ∈ pointees sp oc.hist → oc.slot? y = oe.slot? y
  noSlot : sp.virt = true → ∀ y, y ∉ pointees sp oc.hist → oc.slot? y = none
  vals : sp.virt = true → ∀ e ∈ oc.hist, ∃ z, e.val = sp.rootVal z
  /-- oe has slots for pointees of its history only. -/
  keysE : sp.virt = true → ∀ y, (oe.slot? y).isSome = true → y ∈ pointees sp oe.hist

/-- Without a virtual root, an object and itself. -/
theorem RootRel.ofNV {sp : Spec V T} (hv : sp.virt = false) (f : Time) (o : Obj V) : RootRel sp f o o :=
  ⟨fun _ => rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun h => absurd h (by simp [hv]), fun h => absurd h (by simp [hv]), fun h => absurd h (by simp [hv])⟩

/-- Setting the slot for a pointee of oc's history the same in both. -/
theorem RootRel.setSlot {sp : Spec V T} {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) {y : NodeId}
    (hy : y ∈ pointees sp oc.hist ∨ sp.virt = false) (sl : Slot) :
    RootRel sp f (oc.setSlot y sl) (oe.setSlot y sl) where
  nv := fun hv => by rw [hr.nv hv]
  node := hr.node
  level := hr.level
  isData := hr.isData
  canonical := hr.canonical
  pos := hr.pos
  live := hr.live
  slots := by
    intro z hz
    rw [Obj.slot?_setSlot, Obj.slot?_setSlot]
    have hz' : z ∈ pointees sp oc.hist := hz
    split
    · rename_i he; subst he
      rcases hy with hy | hv
      · rw [hr.slots _ hy]
      · rw [hr.nv hv]
    · exact hr.slots z hz'
  noSlot := by
    intro hv z hz
    rw [Obj.slot?_setSlot]
    split
    · rename_i he; subst he
      rw [hr.noSlot hv _ hz]; rfl
    · exact hr.noSlot hv z hz
  vals := hr.vals
  keysE := by
    intro hv z hz
    rw [Obj.slot?_setSlot] at hz
    rw [Obj.setSlot_hist]
    split at hz
    · rename_i he; subst he
      cases h : oe.slot? z with
      | none => rw [h] at hz; cases hz
      | some _ => exact hr.keysE hv z (by rw [h]; rfl)
    · exact hr.keysE hv z hz

/-! ## The loader -/

section Loader

variable {sp : Spec V T} {S0 S : Stream V T} {m : Mem V} {oc oe : Obj V}

/-- The memories of the two runs, the same but for the root's object. -/
structure RootAt (m : Mem V) (oe : Obj V) : Prop where
  root : m.obj? m.root = some oe
  fresh : m.next ≠ m.root

theorem swz_withRoot {hp : Nat} (y : NodeId) (h1 : Nat) (hra : RootAt m oe) :
    (m.withRoot oc).swz hp y h1 =
      (m.swz hp y h1).withRoot (if hp = m.root then oc.setSlot y (Slot.mem h1) else oc) := by
  unfold Mem.swz
  by_cases he : hp = m.root
  · subst he
    rw [withRoot_obj?_root hra.root, hra.root]
    simp only [↓reduceIte]
    exact withRoot_setObj_root _ _
  · rw [withRoot_obj?_ne he]
    simp only [he, ↓reduceIte]
    cases m.obj? hp with
    | none => rfl
    | some op => exact withRoot_setObj_ne he _



/-- The root's object after a swizzle, or after a promotion. -/
theorem swz_obj?_root (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) :
    (m.swz hp y h1).obj? m.root =
      if hp = m.root then (m.obj? m.root).map (·.setSlot y (Slot.mem h1)) else m.obj? m.root := by
  unfold Mem.swz
  by_cases he : hp = m.root
  · rw [he]
    cases ho : m.obj? m.root with
    | none => simp [ho]
    | some op => simp [Mem.obj?_setObj]
  · cases ho : m.obj? hp with
    | none => simp [he]
    | some op => simp [Mem.obj?_setObj, Ne.symm he, he]

theorem swz_root' (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) : (m.swz hp y h1).root = m.root := by
  unfold Mem.swz; split <;> rfl



/-! ## The root apart from the other objects -/

/-- The root's object is of the root's node, at a handle below `next`; no
memory slot for another node, no table entry of another node and no history
names the root. The loader keeps it on any stream that has no version pointing
to the root (`StreamNR`). -/
structure RootSep (sp : Spec V T) (m : Mem V) : Prop where
  rootNode : ∀ o, m.obj? m.root = some o → o.node = root
  fresh : m.root < m.next
  slotsNR : ∀ h o y h', m.obj? h = some o → o.slot? y = some (Slot.mem h') → y ≠ root → h' ≠ m.root
  tableNR : ∀ y h, m.tableOf y = some h → y ≠ root → h ≠ m.root
  ptrsNR : ∀ h o, m.obj? h = some o → ∀ y ∈ pointees sp o.hist, y ≠ root

theorem versionAt_node {S : Stream V T} {r : Nat} {y : NodeId} {w : Version V}
    (h : S.versionAt r y = some w) : w.node = y := by
  unfold Stream.versionAt at h
  split at h
  · have := List.find?_some h
    simpa using this
  · cases h

/-- The views of the two reads: the same but for the root's node. -/
theorem exec_rootSwap (hex : ExecRootOK sp) {tail : List (NodeId × Node V)} {nc ne : Node V}
    (hvc : sp.virt = true → ∀ e ∈ nc.hist, ∃ z, e.val = sp.rootVal z)
    (hve : sp.virt = true → ∀ e ∈ ne.hist, ∃ z, e.val = sp.rootVal z)
    (hl : sp.live nc.hist = sp.live ne.hist) (hnv : sp.virt = false → nc = ne) (tr : T) (i : Time) :
    sp.exec tr i (fun x => ((root, nc) :: tail).lookup x) = sp.exec tr i (fun x => ((root, ne) :: tail).lookup x) := by
  cases hv : sp.virt with
  | false => rw [hnv hv]
  | true =>
    apply hex hv tr i
    · intro n hn e he
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hn
      subst hn; exact hvc hv e he
    · intro n hn e he
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq] at hn
      subst hn; exact hve hv e he
    · intro x hx
      have : (x == root) = false := by simp [hx]
      simp [List.lookup, this]
    · simp [List.lookup, hl]

theorem find?_congr_of_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.find? p = l.find? q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons]
    rw [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-! ## The change -/

section Change

variable {P P' : Struct V} {j : Time}

theorem addNew_withRoot (hne : m.next ≠ m.root) (nn : NewNode) :
    addNew (m.withRoot oc) nn = (addNew m nn).withRoot oc := by
  unfold addNew
  rw [withRoot_addObj hne]
  simp only [withRoot_next]
  rfl

theorem foldl_addNew_withRoot (N : List NewNode) :
    ∀ (m : Mem V), m.root < m.next → N.foldl addNew (m.withRoot oc) = (N.foldl addNew m).withRoot oc := by
  induction N with
  | nil => intro m _; rfl
  | cons nn N ih =>
    intro m hlt
    simp only [List.foldl_cons]
    rw [addNew_withRoot (by omega)]
    exact ih _ (by show m.root < m.next + 1; omega)

theorem foldl_addNew_root (N : List NewNode) : ∀ (m : Mem V), (N.foldl addNew m).root = m.root := by
  induction N with
  | nil => intro m; rfl
  | cons nn N ih => intro m; simp only [List.foldl_cons]; rw [ih]; rfl

/-- A virtual root's new entry, for a new root child z, with the slot to z's
object, the same in both. -/
theorem RootRel.addRoot (hvl : VirtLiveOK sp) (hv : sp.virt = true) {f : Time} (hr : RootRel sp f oc oe)
    (hvalsE : ∀ e ∈ oe.hist, ∃ z, e.val = sp.rootVal z) {e : Entry V} {z : NodeId}
    (hez : e.val = sp.rootVal z) (hptr : sp.ptrs (sp.rootVal z) = [z]) (sl : Slot) :
    RootRel sp f ({ oc with hist := oc.hist ++ [e] }.putSlot z sl) ({ oe with hist := oe.hist ++ [e] }.putSlot z sl) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := Obj.putSlot_fields ({ oc with hist := oc.hist ++ [e] }) z sl
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := Obj.putSlot_fields ({ oe with hist := oe.hist ++ [e] }) z sl
  have hmem : ∀ y, y ∈ pointees sp (oc.hist ++ [e]) → y ∈ pointees sp oc.hist ∨ y = z := by
    intro y hy
    rcases pointees_append_mem hy with h | h
    · exact Or.inl h
    · rw [mem_pointees] at h
      obtain ⟨e', he', hy'⟩ := h
      rw [List.mem_singleton.mp he', hez, hptr] at hy'
      exact Or.inr (List.mem_singleton.mp hy')
  refine ⟨fun h => absurd h (by simp [hv]), by rw [a1, b1]; exact hr.node, by rw [a2, b2]; exact hr.level,
    by rw [a3, b3]; exact hr.isData, by rw [a5, b5]; exact hr.canonical, by rw [a6, b6]; exact hr.pos, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro t ht
    rw [a4, b4]
    simp only
    rw [upTo_append, upTo_append]
    by_cases het : e.time ≤ t
    · have h1 : History.upTo [e] t = [e] := by simp [History.upTo, het]
      rw [h1]
      have hvc : ∀ e' ∈ oc.hist.upTo t ++ [e], ∃ z, e'.val = sp.rootVal z := by
        intro e' he'
        rcases List.mem_append.mp he' with h | h
        · exact hr.vals hv e' (mem_upTo.mp h).1
        · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
      have hve : ∀ e' ∈ oe.hist.upTo t ++ [e], ∃ z, e'.val = sp.rootVal z := by
        intro e' he'
        rcases List.mem_append.mp he' with h | h
        · exact hvalsE e' (mem_upTo.mp h).1
        · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
      rw [hvl hv _ hvc, hvl hv _ hve]
      simp
    · have h1 : History.upTo [e] t = [] := by simp [History.upTo, het]
      rw [h1, List.append_nil, List.append_nil]
      exact hr.live t ht
  · intro y hy
    rw [a4] at hy
    simp only at hy
    rw [Obj.slot?_putSlot, Obj.slot?_putSlot]
    split
    · rfl
    · rename_i hyz
      rcases hmem y hy with h | h
      · exact hr.slots y h
      · exact absurd h hyz
  · intro _ y hy
    rw [a4] at hy
    simp only at hy
    rw [Obj.slot?_putSlot]
    split
    · rename_i hyz
      subst hyz
      exact absurd (by rw [mem_pointees]; exact ⟨e, by simp, by rw [hez, hptr]; simp⟩) hy
    · have : y ∉ pointees sp oc.hist := fun h =>
        hy (by rw [mem_pointees] at h ⊢; obtain ⟨e', he', h'⟩ := h; exact ⟨e', by simp [he'], h'⟩)
      exact hr.noSlot hv y this
  · intro _ e' he'
    rw [a4] at he'
    simp only at he'
    rcases List.mem_append.mp he' with h | h
    · exact hr.vals hv e' h
    · rw [List.mem_singleton.mp h]; exact ⟨z, hez⟩
  · intro _ y hy
    rw [b4]
    simp only
    rw [Obj.slot?_putSlot] at hy
    split at hy
    · rename_i hyz
      subst hyz
      rw [mem_pointees]; exact ⟨e, by simp, by rw [hez, hptr]; simp⟩
    · have := hr.keysE hv y hy
      rw [mem_pointees] at this ⊢
      obtain ⟨e', he', h'⟩ := this
      exact ⟨e', by simp [he'], h'⟩

/-! ## The physical writer -/

end Change

end Loader

/-! ## The writer's paths on structures that agree -/

section Paths

variable {sp : Spec V T} {f k : Time} {P P' : Struct V}

theorem mergeSort_congr {α : Type} {l : List α} {r s : α → α → Bool} (h : ∀ a ∈ l, ∀ b ∈ l, r a b = s a b) :
    l.mergeSort r = l.mergeSort s := by
  have := List.map_mergeSort (f := id) (s := s) (l := l) (r := r) h
  simpa using this

/-- The nodes below a node reachable at a time from f to k, in structures that
agree: the same. -/
theorem CutAgree.reachFrom_same (h : CutAgree sp f k P P') (hls : LiveSub sp) (hp : PtrsOK sp P) {t : Time}
    (h1 : f ≤ t) (h2 : t ≤ k) {x : NodeId} (hx : reachable sp P t x = true) {n n' : Node V}
    (hn : P.get? x = some n) (hn' : P'.get? x = some n') : reachFrom sp P' t x n' = reachFrom sp P t x n := by
  have hnodes : ∀ y, Reach sp P t y → y ≠ root → P'.get? y = P.get? y :=
    fun y hy hyr => h.nodes y t h1 h2 (fun _ => hyr) ((reachable_iff _ _ _ _).mpr hy)
  by_cases hxr : sp.virt = true ∧ x = root
  · obtain ⟨hv, rfl⟩ := hxr
    obtain ⟨hlev, hlive⟩ := h.rootLive hv n n' hn hn'
    rw [SIS.reachFrom_eq, SIS.reachFrom_eq, ← hlive t h1 h2, ← hlev]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    obtain ⟨m, hm, hlt⟩ := hp root n hn e (mem_upTo.mp he).1 y hye
    have hRy : Reach sp P t y := Reach.child (Reach.root n hn) hn hy hm hlt
    have hyr : y ≠ root := by
      intro hyr; subst hyr; rw [hn, Option.some.injEq] at hm; subst hm; omega
    rw [hnodes y hRy hyr, hm]
    simp only [hlt, ↓reduceIte]
    exact reachFrom_agree hls hp h.rootP hnodes (m.level + 1) y m (by omega) hm hRy
  · have hx' : P'.get? x = P.get? x :=
      h.nodes x t h1 h2 (fun hv hx0 => hxr ⟨hv, hx0⟩) hx
    rw [hn', hn, Option.some.injEq] at hx'
    subst hx'
    exact reachFrom_agree hls hp h.rootP hnodes (n'.level + 1) x n' (by omega) hn ((reachable_iff _ _ _ _).mp hx)

theorem CutAgree.reachList_eq (h : CutAgree sp f k P P') (hls : LiveSub sp) (hp : PtrsOK sp P) {t : Time}
    (h1 : f ≤ t) (h2 : t ≤ k) : reachList sp P' t = reachList sp P t := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp h.rootP
  obtain ⟨n0', h0'⟩ := Option.isSome_iff_exists.mp h.rootP'
  unfold reachList
  rw [h0, h0']
  exact h.reachFrom_same hls hp h1 h2 (reachable_root h0 t) h0 h0'

/-- The writer's paths are the same on structures that agree, before and after
the change. -/
theorem CutAgree.pathOf_eq (h : CutAgree sp f k P P') {c : Changes V}
    (h' : CutAgree sp f (k + 1) (P.apply (k + 1) c) (P'.apply (k + 1) c)) (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hp' : PtrsOK sp (P.apply (k + 1) c)) (hfk : f ≤ k) :
    pathOf sp P' c (k + 1) = pathOf sp P c (k + 1) := by
  unfold pathOf
  simp only [Nat.add_sub_cancel]
  rw [h.reachList_eq hls hp hfk (Nat.le_refl _)]
  apply List.filter_congr
  intro x hx
  have hxr : reachable sp P k x = true := by
    simp only [reachable, List.contains_iff_mem]
    exact List.mem_eraseDups.mp hx
  have ht : ∀ z, (changed c z || c.touch.contains z ||
      (reachable sp P' k z && !reachable sp (P'.apply (k + 1) c) (k + 1) z)) =
      (changed c z || c.touch.contains z ||
      (reachable sp P k z && !reachable sp (P.apply (k + 1) c) (k + 1) z)) := by
    intro z
    rw [h.reachable_eq hls hp hfk (Nat.le_refl _) z, h'.reachable_eq hls hp' (by omega) (Nat.le_refl _) z]
  cases hn : P.get? x with
  | none =>
    have : P'.get? x = none := by
      cases h1 : P'.get? x with
      | none => rfl
      | some n' => have := h.ids x (by rw [h1]; rfl); rw [hn] at this; cases this
    rw [this]
  | some n =>
    obtain ⟨n', hn'⟩ : ∃ n', P'.get? x = some n' := by
      cases h1 : P'.get? x with
      | some n' => exact ⟨n', rfl⟩
      | none =>
        exfalso
        have hR := (reachable_iff _ _ _ _).mp hxr
        have := (h.reach hfk (Nat.le_refl _) hR)
        rw [← reachable_iff] at this
        by_cases hv : sp.virt = true ∧ x = root
        · obtain ⟨-, rfl⟩ := hv
          have := h.rootP'; rw [h1] at this; cases this
        · have := h.nodes x k hfk (Nat.le_refl _) (fun hv' hx0 => hv ⟨hv', hx0⟩) hxr
          rw [h1, hn] at this; cases this
    rw [hn']
    simp only
    rw [h.reachFrom_same hls hp hfk (Nat.le_refl _) hxr hn hn']
    congr 1
    funext z
    exact ht z

/-- The levels of the nodes reachable at a time from f to k agree. -/
theorem CutAgree.lev_eq (h : CutAgree sp f k P P') {t : Time} (h1 : f ≤ t) (h2 : t ≤ k) {x : NodeId}
    (hx : reachable sp P t x = true) : lev P' x = lev P x := by
  unfold lev
  by_cases hv : sp.virt = true ∧ x = root
  · obtain ⟨hv, rfl⟩ := hv
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [hn, hn']
    simp only [Option.map_some, Option.getD_some]
    exact ((h.rootLive hv n n' hn hn').1).symm
  · rw [h.nodes x t h1 h2 (fun hv' hx0 => hv ⟨hv', hx0⟩) hx]

/-- The live children at a time from f to k of the nodes reachable then agree. -/
theorem CutAgree.live_eq (h : CutAgree sp f k P P') {t : Time} (h1 : f ≤ t) (h2 : t ≤ k) {x : NodeId}
    (hx : reachable sp P t x = true) :
    (P'.get? x).map (fun n => sp.live (n.hist.upTo t)) = (P.get? x).map (fun n => sp.live (n.hist.upTo t)) := by
  by_cases hv : sp.virt = true ∧ x = root
  · obtain ⟨hv, rfl⟩ := hv
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [hn, hn']
    simp only [Option.map_some, Option.some.injEq]
    exact ((h.rootLive hv n n' hn hn').2 t h1 h2).symm
  · rw [h.nodes x t h1 h2 (fun hv' hx0 => hv ⟨hv', hx0⟩) hx]

end Paths

end SIS
