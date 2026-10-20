/-
Proofs about reclaim, part 19 (bergdb item 001, WP R5, T12 with eviction): two
memories that are the same but for where the root's entry is in the list of
objects (`RootPerm`). The run from the whole stream may change slots of its
root's object that the run from the cut stream does not have, which moves the
root's entry to the front of its list. Every operation keeps the relation:
they look objects up by handle, and the one search over the list, for a
source of a copied slot, finds the root's object only when it is the only
source (`RootOnly`).
-/
import SIS.Proof.CutLaterSim
import SIS.Proof.EvictPin

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The same memories but for where the root's entry is. -/
structure RootPerm (m1 m2 : Mem V) : Prop where
  table : m1.table = m2.table
  s : m1.s = m2.s
  root : m1.root = m2.root
  next : m1.next = m2.next
  rest : m1.objs.filter (fun p => p.1 != m1.root) = m2.objs.filter (fun p => p.1 != m2.root)
  rootObj : m1.obj? m1.root = m2.obj? m2.root
  nd1 : (m1.objs.map (·.1)).Nodup
  nd2 : (m2.objs.map (·.1)).Nodup
  fresh : ∀ h, m1.next ≤ h → m1.obj? h = none
  rootLt : m1.root < m1.next

section Perm

variable {m1 m2 m3 : Mem V}

theorem RootPerm.refl (hnd : (m1.objs.map (·.1)).Nodup) (hfr : ∀ h, m1.next ≤ h → m1.obj? h = none)
    (hlt : m1.root < m1.next) : RootPerm m1 m1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, hnd, hnd, hfr, hlt⟩

theorem RootPerm.obj? (hp : RootPerm m1 m2) (h : Nat) : m1.obj? h = m2.obj? h := by
  by_cases he : h = m1.root
  · subst he; rw [hp.rootObj, hp.root]
  · have he2 : h ≠ m2.root := by rw [← hp.root]; exact he
    unfold Mem.obj?
    rw [← lookup_filter_ne m1.root h m1.objs he, ← lookup_filter_ne m2.root h m2.objs he2, hp.rest]

theorem RootPerm.symm (hp : RootPerm m1 m2) : RootPerm m2 m1 :=
  ⟨hp.table.symm, hp.s.symm, hp.root.symm, hp.next.symm, hp.rest.symm, hp.rootObj.symm, hp.nd2, hp.nd1,
    fun h hh => by rw [← hp.obj? h]; exact hp.fresh h (by rw [hp.next]; exact hh),
    by rw [← hp.root, ← hp.next]; exact hp.rootLt⟩

theorem RootPerm.trans (h12 : RootPerm m1 m2) (h23 : RootPerm m2 m3) : RootPerm m1 m3 :=
  ⟨h12.table.trans h23.table, h12.s.trans h23.s, h12.root.trans h23.root, h12.next.trans h23.next,
    h12.rest.trans h23.rest, h12.rootObj.trans h23.rootObj, h12.nd1, h23.nd2, h12.fresh, h12.rootLt⟩

theorem RootPerm.tableOf (hp : RootPerm m1 m2) (y : NodeId) : m1.tableOf y = m2.tableOf y := by
  unfold Mem.tableOf; rw [hp.table]

theorem RootPerm.canonicalOf (hp : RootPerm m1 m2) (y : NodeId) : m1.canonicalOf y = m2.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [hp.tableOf]
  cases m2.tableOf y with
  | none => rfl
  | some h => simp only [hp.obj? h]

theorem RootPerm.fresh2 (hp : RootPerm m1 m2) : ∀ h, m2.next ≤ h → m2.obj? h = none :=
  hp.symm.fresh

theorem RootPerm.setObj (hp : RootPerm m1 m2) {h : Nat} (hlt : h < m1.next) (o : Obj V) :
    RootPerm (m1.setObj h o) (m2.setObj h o) := by
  refine ⟨hp.table, hp.s, hp.root, hp.next, ?_, ?_, nodup_setObj_keys _ _ _ hp.nd1, nodup_setObj_keys _ _ _ hp.nd2,
    ?_, hp.rootLt⟩
  · simp only [Mem.setObj_root]
    unfold Mem.setObj
    simp only [List.filter_cons]
    have hc : ∀ (l : List (Nat × Obj V)) (r : Nat), List.filter (fun p => p.1 != r) (List.filter (fun p => p.1 != h) l) =
        List.filter (fun p => p.1 != h) (List.filter (fun p => p.1 != r) l) := by
      intro l r; rw [List.filter_filter, List.filter_filter]; congr 1; funext p; exact Bool.and_comm _ _
    rw [hc m1.objs, hc m2.objs, hp.rest, hp.root]
  · simp only [Mem.setObj_root]
    rw [Mem.obj?_setObj, Mem.obj?_setObj, ← hp.root, hp.obj? m1.root]
  · intro h' hh'
    rw [Mem.setObj_next] at hh'
    rw [Mem.obj?_setObj]
    have : h' ≠ h := by omega
    simp only [this, ↓reduceIte]
    exact hp.fresh h' hh'

theorem RootPerm.addObj (hp : RootPerm m1 m2) (o : Obj V) : RootPerm (m1.addObj o).1 (m2.addObj o).1 := by
  have hne : m1.next ≠ m1.root := by have := hp.rootLt; omega
  refine ⟨hp.table, hp.s, hp.root, by simp [hp.next], ?_, ?_,
    nodup_addObj_keys _ _ hp.nd1 hp.fresh, nodup_addObj_keys _ _ hp.nd2 hp.fresh2, ?_, ?_⟩
  · unfold Mem.addObj
    simp only [List.filter_cons]
    have h1 : (m1.next != m1.root) = true := by simp [hne]
    have h2 : (m2.next != m2.root) = true := by rw [← hp.next, ← hp.root]; exact h1
    simp only [h1, h2, ↓reduceIte]
    rw [hp.rest, hp.next]
  · simp only [Mem.addObj_root]
    rw [Mem.obj?_addObj, Mem.obj?_addObj, ← hp.root, ← hp.next]
    simp only [Ne.symm hne, ↓reduceIte]
    exact hp.rootObj.trans (by rw [hp.root])
  · intro h' hh'
    rw [Mem.addObj_next] at hh'
    rw [Mem.obj?_addObj]
    have : h' ≠ m1.next := by omega
    simp only [this, ↓reduceIte]
    exact hp.fresh h' (by omega)
  · simp only [Mem.addObj_root, Mem.addObj_next]; have := hp.rootLt; omega

theorem RootPerm.setTable (hp : RootPerm m1 m2) (y : NodeId) (h : Nat) :
    RootPerm (m1.setTable y h) (m2.setTable y h) :=
  ⟨by simp [Mem.setTable, hp.table], hp.s, hp.root, hp.next, hp.rest, hp.rootObj, hp.nd1, hp.nd2, hp.fresh,
    hp.rootLt⟩

theorem RootPerm.addNew (hp : RootPerm m1 m2) (nn : NewNode) : RootPerm (SIS.addNew m1 nn) (SIS.addNew m2 nn) := by
  unfold SIS.addNew
  rw [← hp.next]
  exact (hp.addObj _).setTable _ _

theorem RootPerm.foldl_addNew (N : List NewNode) : ∀ (m1 m2 : Mem V), RootPerm m1 m2 →
    RootPerm (N.foldl SIS.addNew m1) (N.foldl SIS.addNew m2) := by
  induction N with
  | nil => intro m1 m2 h; exact h
  | cons nn N ih => intro m1 m2 h; exact ih _ _ (h.addNew nn)

/-- `any` over a list with no repeated handles: the entries other than handle r,
and r's. -/
theorem any_root_split {β : Type} (f : Nat × β → Bool) (r : Nat) :
    ∀ (l : List (Nat × β)), (l.map (·.1)).Nodup →
      l.any f = ((l.filter (fun p => p.1 != r)).any f || ((l.lookup r).map (fun o => f (r, o))).getD false) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons p l ih =>
    intro hnd
    obtain ⟨a, x⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.any_cons, List.filter_cons, lookup_cons_eq, ih hnd.2]
    by_cases ha : a = r
    · subst ha
      have hl : List.lookup a l = none := lookup_none_of_not_mem hnd.1
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hl, Option.map_none, Option.getD_none,
        Bool.or_false, Option.map_some, Option.getD_some]
      exact Bool.or_comm _ _
    · have : (a != r) = true := by simp [ha]
      simp only [this, ↓reduceIte, List.any_cons, Ne.symm ha, Bool.or_assoc]

theorem RootPerm.incoming (hp : RootPerm m1 m2) (h : Nat) : m1.incoming h = m2.incoming h := by
  unfold Mem.incoming
  rw [any_root_split _ m1.root m1.objs hp.nd1, any_root_split _ m2.root m2.objs hp.nd2, hp.rest]
  have := hp.rootObj
  unfold Mem.obj? at this
  rw [this, hp.root]

theorem RootPerm.detachable (hp : RootPerm m1 m2) (D : Dirty) (h : Nat) : m1.detachable D h = m2.detachable D h :=
  Mem.detachable_congr hp.root (by rw [hp.obj? h])

theorem RootPerm.eligible (hp : RootPerm m1 m2) (D : Dirty) (h : Nat) : m1.eligible D h = m2.eligible D h := by
  unfold Mem.eligible; rw [hp.detachable D h, hp.incoming h]

theorem RootPerm.release (hp : RootPerm m1 m2) (D : Dirty) (h : Nat) : RootPerm (m1.release D h) (m2.release D h) := by
  unfold Mem.release
  rw [hp.eligible D h]
  split
  · refine ⟨by simp [hp.table], hp.s, hp.root, hp.next, ?_, ?_, ?_, ?_, ?_, hp.rootLt⟩
    · simp only
      have hc : ∀ (l : List (Nat × Obj V)) (r : Nat), List.filter (fun p => p.1 != r) (List.filter (fun p => p.1 != h) l) =
          List.filter (fun p => p.1 != h) (List.filter (fun p => p.1 != r) l) := by
        intro l r; rw [List.filter_filter, List.filter_filter]; congr 1; funext p; exact Bool.and_comm _ _
      rw [hc m1.objs, hc m2.objs, hp.rest]
    · show List.lookup m1.root (m1.objs.filter (fun p => p.1 != h)) = List.lookup m2.root (m2.objs.filter (fun p => p.1 != h))
      by_cases hh : m1.root = h
      · rw [hh, ← hp.root, hh, lookup_filter_self, lookup_filter_self]
      · rw [lookup_filter_ne h _ _ hh, lookup_filter_ne h _ _ (by rw [← hp.root]; exact hh)]
        exact hp.rootObj
    · exact (List.Sublist.map _ List.filter_sublist).nodup hp.nd1
    · exact (List.Sublist.map _ List.filter_sublist).nodup hp.nd2
    · intro h' hh'
      show List.lookup h' (m1.objs.filter (fun p => p.1 != h)) = none
      by_cases he : h' = h
      · rw [he, lookup_filter_self]
      · rw [lookup_filter_ne h h' _ he]; exact hp.fresh h' hh'
  · exact hp

/-- The search for a source over two lists that differ in where the root's
entry is: the same, when the root's object is no source or the only one. -/
theorem find?_root_out {β : Type} (pr : Nat × β → Bool) (r : Nat) :
    ∀ (l : List (Nat × β)), (∀ o, l.lookup r = some o → pr (r, o) = false) → (l.map (·.1)).Nodup →
      l.find? pr = (l.filter (fun p => p.1 != r)).find? pr := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons p l ih =>
    intro hr hnd
    obtain ⟨a, x⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    by_cases ha : a = r
    · subst ha
      have hx : pr (a, x) = false := hr x (by rw [lookup_cons_eq]; simp)
      have hl : List.lookup a l = none := lookup_none_of_not_mem hnd.1
      rw [List.find?_cons_of_neg (by simp [hx]), List.filter_cons_of_neg (by simp)]
      exact ih (fun o ho => by rw [hl] at ho; cases ho) hnd.2
    · rw [List.filter_cons_of_pos (by simp [ha])]
      cases hx : pr (a, x)
      · rw [List.find?_cons_of_neg (by simp [hx]), List.find?_cons_of_neg (by simp [hx])]
        exact ih (fun o ho => hr o (by rw [lookup_cons_eq]; simp [Ne.symm ha, ho])) hnd.2
      · rw [List.find?_cons_of_pos (by simp [hx]), List.find?_cons_of_pos (by simp [hx])]

theorem find?_root_only {β : Type} (pr : Nat × β → Bool) (r : Nat) {o : β} :
    ∀ (l : List (Nat × β)), l.lookup r = some o → pr (r, o) = true → (∀ p ∈ l, p.1 ≠ r → pr p = false) →
      l.find? pr = some (r, o) := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons p l ih =>
    intro hl hpr hno
    obtain ⟨a, x⟩ := p
    rw [lookup_cons_eq] at hl
    by_cases ha : a = r
    · subst ha
      simp only [↓reduceIte, Option.some.injEq] at hl
      subst hl
      rw [List.find?_cons_of_pos (by simp [hpr])]
    · simp only [Ne.symm ha, ↓reduceIte] at hl
      have : pr (a, x) = false := hno (a, x) List.mem_cons_self ha
      rw [List.find?_cons_of_neg (by simp [this])]
      exact ih hl hpr (fun q hq hqr => hno q (List.mem_cons_of_mem _ hq) hqr)

theorem RootPerm.find? (hp : RootPerm m1 m2) (pr : Nat × Obj V → Bool)
    (hU : ∀ oR, m1.obj? m1.root = some oR → pr (m1.root, oR) = true → ∀ p ∈ m1.objs, p.1 ≠ m1.root → pr p = false) :
    m1.objs.find? pr = m2.objs.find? pr := by
  cases hro : m1.obj? m1.root with
  | some oR =>
    cases hpr : pr (m1.root, oR) with
    | true =>
      have hno1 := hU oR hro hpr
      have hro2 : m2.obj? m2.root = some oR := by rw [← hp.rootObj]; exact hro
      have hno2 : ∀ p ∈ m2.objs, p.1 ≠ m2.root → pr p = false := by
        intro p hpm hpr'
        have : p ∈ m2.objs.filter (fun p => p.1 != m2.root) := List.mem_filter.mpr ⟨hpm, by simp [hpr']⟩
        rw [← hp.rest] at this
        obtain ⟨hpm1, hpne⟩ := List.mem_filter.mp this
        exact hno1 p hpm1 (by simpa using hpne)
      rw [find?_root_only pr m1.root m1.objs hro hpr hno1,
        find?_root_only pr m2.root m2.objs hro2 (by rw [← hp.root]; exact hpr) hno2, hp.root]
    | false =>
      rw [find?_root_out pr m1.root m1.objs (fun o ho => by
          have : m1.obj? m1.root = some o := ho
          rw [hro, Option.some.injEq] at this; subst this; exact hpr) hp.nd1,
        find?_root_out pr m2.root m2.objs (fun o ho => by
          have : m2.obj? m2.root = some o := ho
          rw [← hp.rootObj, hro, Option.some.injEq] at this; subst this; rw [← hp.root]; exact hpr) hp.nd2,
        hp.rest]
  | none =>
    rw [find?_root_out pr m1.root m1.objs (fun o ho => by
        have : m1.obj? m1.root = some o := ho
        rw [hro] at this; cases this) hp.nd1,
      find?_root_out pr m2.root m2.objs (fun o ho => by
        have : m2.obj? m2.root = some o := ho
        rw [← hp.rootObj, hro] at this; cases this) hp.nd2,
      hp.rest]

theorem RootPerm.lt_of_obj? (hp : RootPerm m1 m2) {h : Nat} {o : Obj V} (ho : m1.obj? h = some o) : h < m1.next := by
  apply Nat.lt_of_not_le
  intro hle
  rw [hp.fresh h hle] at ho
  cases ho

/-! ### The loader -/

section Loader

variable {sp : Spec V T} {S0 S : Stream V T}

theorem RootPerm.reached4 (hp : RootPerm m1 m2) (h : Nat) (y : NodeId) :
    (m1.reached4 sp S0 S h y).map (·.2) = (m2.reached4 sp S0 S h y).map (·.2) ∧
      ∀ a b, m1.reached4 sp S0 S h y = some a → m2.reached4 sp S0 S h y = some b → RootPerm a.1 b.1 := by
  unfold Mem.reached4
  simp only [hp.obj?, hp.canonicalOf, hp.s]
  cases (m2.obj? h).bind (·.slot? y) with
  | none => exact ⟨rfl, fun _ _ h => by cases h⟩
  | some sl =>
    cases sl with
    | mem h' =>
      simp only
      split
      · refine ⟨rfl, fun a b ha hb => ?_⟩
        cases ha; cases hb; exact hp
      · exact ⟨rfl, fun _ _ h => by cases h⟩
    | stream r =>
      simp only
      cases m2.canonicalOf y with
      | some h0 =>
        refine ⟨rfl, fun a b ha hb => ?_⟩
        cases ha; cases hb; exact hp
      | none =>
        simp only
        cases ruleRRef S0 m2.s y r with
        | none => exact ⟨rfl, fun _ _ h => by cases h⟩
        | some r' =>
          simp only
          cases S.versionAt r' y with
          | none => exact ⟨rfl, fun _ _ h => by cases h⟩
          | some w =>
            refine ⟨by simp [hp.next], fun a b ha hb => ?_⟩
            simp only [Option.some.injEq] at ha hb
            subst ha hb
            exact hp.addObj _

theorem RootPerm.swz (hp : RootPerm m1 m2) (h : Nat) (y : NodeId) (h1 : Nat) :
    RootPerm (m1.swz h y h1) (m2.swz h y h1) := by
  unfold Mem.swz
  rw [← hp.obj? h]
  cases ho : m1.obj? h with
  | none => exact hp
  | some op => exact hp.setObj (hp.lt_of_obj? ho) _

theorem RootPerm.promote (hp : RootPerm m1 m2) (h : Nat) (y : NodeId) (h1 : Nat) :
    RootPerm (m1.promote h y h1).1 (m2.promote h y h1).1 ∧ (m1.promote h y h1).2 = (m2.promote h y h1).2 := by
  unfold Mem.promote
  dsimp only
  rw [← hp.canonicalOf y]
  refine ⟨?_, rfl⟩
  generalize (m1.canonicalOf y).getD h1 = pick
  rw [← hp.obj? pick]
  cases hpo : m1.obj? pick with
  | none =>
    simp only
    exact (hp.swz h y pick : RootPerm (Mem.swz m1 h y pick) (Mem.swz m2 h y pick))
  | some o =>
    simp only
    exact (((hp.setObj (hp.lt_of_obj? hpo) { o with canonical := true }).setTable y pick).swz h y pick :
      RootPerm (Mem.swz ((m1.setObj pick { o with canonical := true }).setTable y pick) h y pick)
        (Mem.swz ((m2.setObj pick { o with canonical := true }).setTable y pick) h y pick))

theorem RootPerm.follow4 (hp : RootPerm m1 m2) (h : Nat) (y : NodeId) (w : Bool) :
    RootPerm (m1.follow4 sp S0 S h y w).1 (m2.follow4 sp S0 S h y w).1 ∧
      (m1.follow4 sp S0 S h y w).2 = (m2.follow4 sp S0 S h y w).2 := by
  rw [follow4_eq, follow4_eq]
  obtain ⟨e1, e2⟩ := hp.reached4 (sp := sp) (S0 := S0) (S := S) h y
  cases ha : m1.reached4 sp S0 S h y with
  | none =>
    rw [ha] at e1
    cases hb : m2.reached4 sp S0 S h y with
    | none => exact ⟨hp, rfl⟩
    | some b => rw [hb] at e1; cases e1
  | some a =>
    rw [ha] at e1
    cases hb : m2.reached4 sp S0 S h y with
    | none => rw [hb] at e1; cases e1
    | some b =>
      rw [hb] at e1
      have hab := e2 a b ha hb
      obtain ⟨ma, ha1⟩ := a
      obtain ⟨mb, hb1⟩ := b
      simp only [Option.map_some, Option.some.injEq] at e1
      subst e1
      simp only at hab ⊢
      cases w with
      | false => exact ⟨hab.swz h y ha1, rfl⟩
      | true =>
        simp only [↓reduceIte]
        obtain ⟨p1, p2⟩ := (hab.swz h y ha1).promote h y ha1
        exact ⟨p1, by rw [p2]⟩

theorem RootPerm.readAt4 : ∀ (fuel : Nat) (m1 m2 : Mem V) (t : Time) (h : Nat), RootPerm m1 m2 →
    RootPerm (m1.readAt4 sp S0 S fuel t h).1 (m2.readAt4 sp S0 S fuel t h).1 ∧
      (m1.readAt4 sp S0 S fuel t h).2 = (m2.readAt4 sp S0 S fuel t h).2 := by
  intro fuel
  induction fuel with
  | zero => intro m1 m2 t h hp; exact ⟨hp, rfl⟩
  | succ fuel ih =>
    intro m1 m2 t h hp
    cases ho : m1.obj? h with
    | none =>
      have ho2 : m2.obj? h = none := by rw [← hp.obj? h]; exact ho
      simp only [Mem.readAt4, ho, ho2]
      exact ⟨hp, trivial⟩
    | some o =>
      have ho2 : m2.obj? h = some o := by rw [← hp.obj? h]; exact ho
      rw [readAt4_succ_eq sp S0 S fuel m1 t h ho, readAt4_succ_eq sp S0 S fuel m2 t h ho2]
      clear ho ho2
      generalize sp.live (o.hist.upTo t) = L
      generalize ([(o.node, o.nodeAt t)] : List (NodeId × Node V)) = l0
      induction L generalizing m1 m2 l0 with
      | nil => exact ⟨hp, rfl⟩
      | cons y L ihL =>
        simp only [List.foldl_cons]
        have hstep : RootPerm (readStep4 sp S0 S fuel t h o (m1, l0) y).1 (readStep4 sp S0 S fuel t h o (m2, l0) y).1 ∧
            (readStep4 sp S0 S fuel t h o (m1, l0) y).2 = (readStep4 sp S0 S fuel t h o (m2, l0) y).2 := by
          unfold readStep4
          dsimp only
          obtain ⟨f1, f2⟩ := hp.follow4 (sp := sp) (S0 := S0) (S := S) h y false
          generalize hF1 : m1.follow4 sp S0 S h y false = F1 at f1 f2
          generalize hF2 : m2.follow4 sp S0 S h y false = F2 at f1 f2
          obtain ⟨a1, r1⟩ := F1
          obtain ⟨a2, r2⟩ := F2
          simp only at f1 f2
          subst f2
          cases r1 with
          | none => exact ⟨f1, rfl⟩
          | some h1 =>
            simp only
            rw [← f1.obj? h1]
            cases a1.obj? h1 with
            | none => exact ⟨f1, rfl⟩
            | some o1 =>
              simp only
              split
              · obtain ⟨g1, g2⟩ := ih a1 a2 t h1 f1
                exact ⟨g1, by rw [g2]⟩
              · exact ⟨f1, rfl⟩
        obtain ⟨s1, s2⟩ := hstep
        generalize readStep4 sp S0 S fuel t h o (m1, l0) y = A at s1 s2
        generalize readStep4 sp S0 S fuel t h o (m2, l0) y = B at s1 s2
        obtain ⟨a, la⟩ := A
        obtain ⟨b, lb⟩ := B
        simp only at s1 s2
        subst s2
        exact ihL a b s1 la

theorem RootPerm.read4 (hp : RootPerm m1 m2) (t : Time) :
    RootPerm (m1.read4 sp S0 S t).1 (m2.read4 sp S0 S t).1 ∧ (m1.read4 sp S0 S t).2 = (m2.read4 sp S0 S t).2 := by
  unfold Mem.read4
  rw [hp.rootObj, hp.root]
  cases m2.obj? m2.root with
  | none => exact ⟨hp, rfl⟩
  | some o =>
    simp only
    have := RootPerm.readAt4 (sp := sp) (S0 := S0) (S := S) (o.level + 1) m1 m2 t m2.root hp
    exact this

theorem RootPerm.reachOnPath4 (hp : RootPerm m1 m2) (P : Struct V) (j : Time) (path : List NodeId) (x : NodeId) :
    RootPerm (m1.reachOnPath4 sp S0 S P j path x) (m2.reachOnPath4 sp S0 S P j path x) := by
  unfold Mem.reachOnPath4
  simp only [hp.canonicalOf]
  split
  · split
    · exact (hp.follow4 _ x true).1
    · exact hp
  · exact hp

theorem RootPerm.reachPath4 (P : Struct V) (j : Time) (path : List NodeId) :
    ∀ (L : List NodeId) (m1 m2 : Mem V), RootPerm m1 m2 →
      RootPerm (L.foldl (Mem.reachOnPath4 sp S0 S P j path) m1) (L.foldl (Mem.reachOnPath4 sp S0 S P j path) m2) := by
  intro L
  induction L with
  | nil => intro m1 m2 h; exact h
  | cons x L ih => intro m1 m2 h; exact ih _ _ (h.reachOnPath4 P j path x)

end Loader

/-! ### The change and the writer -/

section Change

variable {sp : Spec V T} {P : Struct V} {j : Time}

/-- With a virtual root, the root's object is a source of a copied slot only when
no other object is. -/
def RootOnly (sp : Spec V T) (P : Struct V) (j : Time) (m : Mem V) : Prop :=
  ∀ y oR, m.obj? m.root = some oR → srcOK4 sp P j y (m.root, oR) = true →
    ∀ p ∈ m.objs, p.1 ≠ m.root → srcOK4 sp P j y p = false

theorem mem_foldl_addNew_objs (N : List NewNode) : ∀ (m : Mem V) (p : Nat × Obj V),
    p ∈ (N.foldl SIS.addNew m).objs → p ∈ m.objs ∨ p.2.slots = [] := by
  induction N with
  | nil => intro m p hp; exact Or.inl hp
  | cons nn N ih =>
    intro m p hp
    simp only [List.foldl_cons] at hp
    rcases ih _ p hp with h | h
    · unfold SIS.addNew at h
      simp only [Mem.setTable_objs] at h
      unfold Mem.addObj at h
      simp only at h
      rcases List.mem_cons.mp h with h | h
      · right; rw [h]; rfl
      · exact Or.inl h
    · exact Or.inr h

theorem RootOnly.foldl_addNew (hU : RootOnly sp P j m1) (hlt : m1.root < m1.next) (N : List NewNode) :
    RootOnly sp P j (N.foldl SIS.addNew m1) := by
  intro y oR hro hsrc p hp hpr
  have hr : (N.foldl SIS.addNew m1).root = m1.root := foldl_addNew_root N m1
  rw [hr] at hro hsrc hpr
  rw [foldl_addNew_old N m1 m1.root hlt] at hro
  rcases mem_foldl_addNew_objs N m1 p hp with h | h
  · exact hU y oR hro hsrc p h hpr
  · unfold srcOK4
    simp [Obj.slot?, h]

theorem RootPerm.srcSlot4_eq (hp : RootPerm m1 m2) (hU : RootOnly sp P j m1) (y : NodeId) :
    srcSlot4 sp P j m1 y = srcSlot4 sp P j m2 y := by
  unfold SIS.srcSlot4
  rw [hp.find? (srcOK4 sp P j y) (fun oR hro hsrc p hpm hpr => hU y oR hro hsrc p hpm hpr)]

theorem RootPerm.NS4_eq (hp : RootPerm m1 m2) (hU : RootOnly sp P j m1) (y : NodeId) :
    NS4 sp P j m1 y = NS4 sp P j m2 y := by
  unfold SIS.NS4
  rw [hp.canonicalOf, hp.srcSlot4_eq hU]

theorem RootPerm.applyChange4 (hp : RootPerm m1 m2) (hU : RootOnly sp P j m1) (c : Changes V) :
    RootPerm (m1.applyChange4 sp P j c) (m2.applyChange4 sp P j c) := by
  rw [applyChange4_eq, applyChange4_eq]
  have hn := hp.foldl_addNew c.new m1 m2
  have hU1 := hU.foldl_addNew hp.rootLt c.new
  have hns : ∀ y, NS4 sp P j (c.new.foldl SIS.addNew m2) y = NS4 sp P j (c.new.foldl SIS.addNew m1) y :=
    fun y => (hn.NS4_eq hU1 y).symm
  generalize c.new.foldl SIS.addNew m1 = n1 at hn hns ⊢
  generalize c.new.foldl SIS.addNew m2 = n2 at hn hns ⊢
  have key : ∀ (L : List (NodeId × V)) (a b : Mem V), RootPerm a b →
      RootPerm (L.foldl (addsStep4 sp P j n1) a) (L.foldl (addsStep4 sp P j n2) b) := by
    intro L
    induction L with
    | nil => intro a b h; exact h
    | cons x L ih =>
      intro a b h
      simp only [List.foldl_cons]
      apply ih
      unfold addsStep4
      rw [← h.canonicalOf]
      cases a.canonicalOf x.1 with
      | none => exact h
      | some hx =>
        simp only
        rw [← h.obj? hx]
        cases hox : a.obj? hx with
        | none => exact h
        | some o =>
          simp only
          rw [updObj4_congr (P' := P) (m1' := n2) (m1 := n1) hns]
          exact h.setObj (h.lt_of_obj? hox) _
  exact key c.adds n1 n2 hn

theorem RootPerm.refOf (hp : RootPerm m1 m2) (S0 : Stream V T) (D : Dirty) (o : Obj V) (y : NodeId) :
    m1.refOf S0 D o y = m2.refOf S0 D o y := by
  unfold Mem.refOf
  simp only [hp.obj?, hp.canonicalOf, hp.s]

theorem RootPerm.writeNode (hp : RootPerm m1 m2) (S0 : Stream V T) (D : Dirty) (i : Nat) (x : NodeId) :
    RootPerm (m1.writeNode sp S0 D i x).1 (m2.writeNode sp S0 D i x).1 ∧
      (m1.writeNode sp S0 D i x).2 = (m2.writeNode sp S0 D i x).2 := by
  cases hcx : m1.canonicalOf x with
  | none =>
    have hcx2 : m2.canonicalOf x = none := by rw [← hp.canonicalOf]; exact hcx
    unfold Mem.writeNode
    rw [hcx, hcx2]
    exact ⟨hp, rfl⟩
  | some h =>
    have hcx2 : m2.canonicalOf x = some h := by rw [← hp.canonicalOf]; exact hcx
    cases hoh : m1.obj? h with
    | none =>
      have hoh2 : m2.obj? h = none := by rw [← hp.obj?]; exact hoh
      unfold Mem.writeNode
      rw [hcx, hcx2]
      dsimp only
      rw [hoh, hoh2]
      exact ⟨hp, rfl⟩
    | some o =>
      have hoh2 : m2.obj? h = some o := by rw [← hp.obj?]; exact hoh
      rw [writeNode_shape sp S0 D i hcx hoh, writeNode_shape sp S0 D i hcx2 hoh2]
      have hpin : m1.pinSlots D o = m2.pinSlots D o := by
        unfold Mem.pinSlots; simp only [hp.canonicalOf]
      have hver : m1.verOf sp S0 D i x o = m2.verOf sp S0 D i x o := by
        unfold Mem.verOf; simp only [hp.refOf]
      rw [hpin, hver]
      exact ⟨hp.setObj (hp.lt_of_obj? hoh) _, rfl⟩

theorem RootPerm.writeNodes (S0 : Stream V T) (D : Dirty) (i : Nat) :
    ∀ (xs : List NodeId) (m1 m2 : Mem V) (L : List (Version V)), RootPerm m1 m2 →
      RootPerm (xs.foldl (wnStep sp S0 D i) (m1, L)).1 (xs.foldl (wnStep sp S0 D i) (m2, L)).1 ∧
        (xs.foldl (wnStep sp S0 D i) (m1, L)).2 = (xs.foldl (wnStep sp S0 D i) (m2, L)).2 := by
  intro xs
  induction xs with
  | nil => intro m1 m2 L h; exact ⟨h, rfl⟩
  | cons x xs ih =>
    intro m1 m2 L h
    simp only [List.foldl_cons]
    obtain ⟨w1, w2⟩ := h.writeNode (sp := sp) S0 D i x
    have hs : wnStep sp S0 D i (m1, L) x = ((m1.writeNode sp S0 D i x).1,
        match (m1.writeNode sp S0 D i x).2 with | some v => L ++ [v] | none => L) := by
      unfold wnStep; cases (m1.writeNode sp S0 D i x) with | mk a ov => cases ov <;> rfl
    have hs2 : wnStep sp S0 D i (m2, L) x = ((m2.writeNode sp S0 D i x).1,
        match (m2.writeNode sp S0 D i x).2 with | some v => L ++ [v] | none => L) := by
      unfold wnStep; cases (m2.writeNode sp S0 D i x) with | mk a ov => cases ov <;> rfl
    rw [hs, hs2, ← w2]
    exact ih _ _ _ w1

theorem RootPerm.unswizzle (hp : RootPerm m1 m2) (D : Dirty) (h : Nat) (y : NodeId) :
    RootPerm (m1.unswizzle D h y) (m2.unswizzle D h y) := by
  unfold Mem.unswizzle
  rw [← hp.obj? h]
  cases hoh : m1.obj? h with
  | none => exact hp
  | some op =>
    simp only
    cases op.slot? y with
    | none => exact hp
    | some sl =>
      cases sl with
      | stream r => exact hp
      | mem h' =>
        simp only
        rw [← hp.obj? h']
        cases m1.obj? h' with
        | none => exact hp
        | some o =>
          simp only
          rw [← hp.detachable D h']
          split
          · exact hp.setObj (hp.lt_of_obj? hoh) _
          · exact hp

end Change


end Perm

end SIS
