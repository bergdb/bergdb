/-
Proofs for the physical layer with handles (bergdb item 009, phase 2, step 2d),
work in progress. Proved so far, two pieces that the serialization invariant
will use:

* open point 1 of 02, given the invariants: the fast path's test with a
  pointer's own reference gives what the slow path's test gives (`hFastOK_of`);
* eviction is local for records (02, 4.7): evicting a handle changes the record
  rule's reference of no pointer (`HMem.ptrRef_evict`), and the invariants
  give what that needs (`HMem.ptrRef_evict_of`).

The serialization invariant itself (`TC_handles`, its first part) is not
proved yet.
-/
import SIS.HandleTheorems
import SIS.Proof.EvictInv
import SIS.Proof.Recon
import SIS.Proof.PhysRun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Open point 1 of 02, given the invariants: if the table and the handles are
as `HTableOK` says, and every snapshot in a handle is at least as new as its
node's newest version in the startup section (`HRuleROK`) and as its handle's
written position (`HSnapWrittenOK`), then for a pointer whose reference is a
position, the fast path's test with that reference and the slow path's test,
with the larger of the reference after Rule R and the written position, agree
(`HFastOK`). -/
theorem hFastOK_of {S0 : Stream V T} {m : HMem V} (ht : HTableOK m) (hr : HRuleROK S0 m)
    (hw : HSnapWrittenOK m) : HFastOK S0 m := by
  intro a o y p n hd b ob r ha hp hn hh hb hob hpr
  obtain ⟨-, -, -, -, -, hptr⟩ := ht
  obtain ⟨hd', hh', hnode⟩ := hptr a o y p n ha hp hn
  rw [hh] at hh'
  cases hh'
  rw [hpr]
  unfold HObj.usable
  cases hc : ob.canonical with
  | true => simp
  | false =>
    simp only [Bool.false_or]
    have hW : ∀ w, hd.written = some w → ∃ q, ob.pos = some q ∧ w ≤ q :=
      fun w h => hw n hd b ob w hh hb hob hc h
    have hN : ∀ wn, newest S0 m.s y = some wn → ∃ q, ob.pos = some q ∧ wn.recNo ≤ q :=
      fun wn h => hr n hd b ob wn hh hb hob hc (by rw [hnode]; exact h)
    unfold ruleRRef
    cases hnw : newest S0 m.s y with
    | none =>
      cases hwr : hd.written with
      | none => rfl
      | some w =>
        obtain ⟨q, hq, hle⟩ := hW w hwr
        rw [hq]
        simp only [maxRef, decide_eq_decide, Nat.max_le]
        omega
    | some wn =>
      obtain ⟨q, hq, hle⟩ := hN wn hnw
      rw [hq]
      cases hwr : hd.written with
      | none =>
        by_cases hlt : r < wn.recNo
        · simp only [hlt, ite_true, maxRef, decide_eq_decide]
          omega
        · simp only [hlt, ite_false, maxRef]
      | some w =>
        obtain ⟨q', hq', hle'⟩ := hW w hwr
        rw [hq] at hq'
        cases hq'
        by_cases hlt : r < wn.recNo
        · simp only [hlt, ite_true, maxRef, decide_eq_decide, Nat.max_le]
          omega
        · simp only [hlt, ite_false, maxRef, decide_eq_decide, Nat.max_le]
          omega

/-! ## Eviction is local for records -/

/-- Handle n' after handle n is set. -/
theorem HMem.handle?_setHandle (m : HMem V) (n n' : Nat) (hd : Handle) :
    (m.setHandle n hd).handle? n' = if n' = n then some hd else m.handle? n' := by
  unfold HMem.setHandle HMem.handle?
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · rename_i hne
    exact lookup_filter_ne n n' m.handles hne

/-- The written position that `HMem.evict` gives handle n, whose object is at
address a. -/
def HMem.evictWritten (m : HMem V) (hd : Handle) (a : Nat) : Option Nat :=
  match m.obj? a with
  | some o => if o.canonical then o.pos else hd.written
  | none => hd.written

/-- The handles after an eviction of handle n: n is dead, with no object and
the written position of `evictWritten`; the others are as they were. -/
theorem HMem.evict_handle? {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hev : m.evictable D n = true) (hh : m.handle? n = some hd) (ha : hd.obj = some a) (n' : Nat) :
    (m.evict D n).handle? n' =
      if n' = n then some { hd with obj := none, written := m.evictWritten hd a, dead := true }
      else m.handle? n' := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  exact HMem.handle?_setHandle m n n' _

/-- The objects after an eviction of handle n, whose object is at address a:
a has left memory; the others are as they were. -/
theorem HMem.evict_obj? {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hev : m.evictable D n = true) (hh : m.handle? n = some hd) (ha : hd.obj = some a) (b : Nat) :
    (m.evict D n).obj? b = if b = a then none else m.obj? b := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  unfold HMem.obj?
  simp only [HMem.setHandle]
  split
  · rename_i hb
    subst hb
    exact lookup_filter_self m.objs b
  · rename_i hb
    exact lookup_filter_ne a b m.objs hb

/-- An eviction keeps Rule R's startup pos. -/
theorem HMem.evict_s (m : HMem V) (D : Dirty) (n : Nat) : (m.evict D n).s = m.s := by
  unfold HMem.evict
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- A position at least as large as r is the larger of r and it. -/
theorem maxRef_le {r : Option Nat} {q : Nat} (h : ∀ x, r = some x → x ≤ q) :
    maxRef r (some q) = some q := by
  cases r with
  | none => rfl
  | some x =>
    have := h x rfl
    simp only [maxRef, Option.some.injEq]
    omega

/-- Evicting a handle is local for records (02, 4.7): it changes the record
rule's reference of no pointer (`HMem.ptrRef`), whichever handle the pointer
holds, if only handle n holds its object, and a pointer that holds handle n does
not name, after Rule R, a version newer than n's canonical object. -/
theorem HMem.ptrRef_evict {S0 : Stream V T} {m : HMem V} {D : Dirty} {n : Nat} {y : NodeId}
    {p : HPtr}
    (huniq : ∀ n' hd' a, m.handle? n' = some hd' → hd'.obj = some a → m.objOf n = some a → n' = n)
    (hle : p.handle = some n → ∀ a o q r, m.objOf n = some a → m.obj? a = some o →
      o.canonical = true → o.pos = some q → ruleRRef S0 m.s y p.ref = some r → r ≤ q) :
    (m.evict D n).ptrRef S0 y p = m.ptrRef S0 y p := by
  by_cases hev : m.evictable D n = true
  · -- The evicted handle and its object.
    cases hh : m.handle? n with
    | none => simp [HMem.evictable, hh] at hev
    | some hd =>
      cases ha : hd.obj with
      | none => simp [HMem.evictable, hh, ha] at hev
      | some a =>
        cases ho : m.obj? a with
        | none => simp [HMem.evictable, hh, ha, ho] at hev
        | some o =>
          have hpos : o.pos.isSome = true := by
            have h := hev
            simp only [HMem.evictable, hh, ha, ho, Bool.and_eq_true] at h
            exact h.2.2
          have hobj : m.objOf n = some a := by simp [HMem.objOf, hh, ha]
          unfold HMem.ptrRef
          rw [HMem.evict_s]
          cases hp : p.handle with
          | none => rfl
          | some n' =>
            simp only [Option.bind_some]
            rw [HMem.evict_handle? hev hh ha n']
            by_cases hn : n' = n
            · subst hn
              simp only [↓reduceIte, hh, ha, Option.bind_some, ho, Option.bind_none]
              unfold HMem.evictWritten
              rw [ho]
              cases hc : o.canonical with
              | true =>
                simp only [hc, ↓reduceIte]
                cases hq : o.pos with
                | none => rw [hq] at hpos; simp at hpos
                | some q =>
                  exact maxRef_le (fun r hr => hle hp a o q r hobj ho hc hq hr)
              | false => simp only [hc, Bool.false_eq_true, ↓reduceIte]
            · simp only [hn, ↓reduceIte]
              cases hh2 : m.handle? n' with
              | none => rfl
              | some hd2 =>
                dsimp only
                cases hb : hd2.obj with
                | none => rfl
                | some b =>
                  simp only [Option.bind_some]
                  rw [HMem.evict_obj? hev hh ha b]
                  have hba : ¬ b = a := by
                    intro hba
                    subst hba
                    exact hn (huniq n' hd2 b hh2 hb hobj)
                  simp only [hba, ↓reduceIte]
  · unfold HMem.evict
    simp only [hev]
    rfl

/-- Only one handle holds an object: by `HTableOK`, a handle that holds an
object is live, so it is its node's entry in the table, and the object is of
that node. -/
theorem HTableOK.uniq {m : HMem V} (ht : HTableOK m) {n n' : Nat} {hd' : Handle} {a : Nat}
    (hh' : m.handle? n' = some hd') (ha' : hd'.obj = some a) (hobj : m.objOf n = some a) :
    n' = n := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := ht
  -- Handle n holds a, so it is live.
  cases hh : m.handle? n with
  | none => simp [HMem.objOf, hh] at hobj
  | some hd =>
    have ha : hd.obj = some a := by simpa [HMem.objOf, hh] using hobj
    have hlive : ∀ k e, m.handle? k = some e → e.obj = some a → e.dead = false := by
      intro k e hk he
      cases hdk : e.dead with
      | false => rfl
      | true => rw [h4 k e hk hdk] at he; cases he
    have ht' := h3 n' hd' hh' (hlive n' hd' hh' ha')
    have ht := h3 n hd hh (hlive n hd hh ha)
    obtain ⟨e', b', o', he', -, hn', hb', ho', hon'⟩ := h1 hd'.node n' ht'
    obtain ⟨e, b, o, he, -, hn, hb, ho, hon⟩ := h1 hd.node n ht
    rw [hh'] at he'; cases he'
    rw [hh] at he; cases he
    rw [ha'] at hb'; cases hb'
    rw [ha] at hb; cases hb
    rw [ho'] at ho; cases ho
    -- Both handles are their node's entry, and both nodes are the object's.
    have : hd'.node = hd.node := by rw [← hon', hon]
    rw [this, ht] at ht'
    exact (Option.some.inj ht').symm

/-- Eviction is local for records, given the invariants: in a memory with the
table and the handles as `HTableOK` says, canonical objects at their nodes'
latest records (`HCanOK`) and references that name versions (`HWrittenOK`),
evicting a handle changes the record rule's reference of no pointer of any
object (`HMem.ptrRef`). The two stream facts hold in every run: a version is in
the record of its number, and no version of a node is after its latest. -/
theorem HMem.ptrRef_evict_of {S0 : Stream V T} {db : DB V T} {m : HMem V} {D : Dirty} {n : Nat}
    (ht : HTableOK m) (hc : HCanOK db m) (hw : HWrittenOK db m) (hpre : S0 <+: db.S)
    (hidx : ∀ r y w, db.S.versionAt r y = some w → w.recNo = r)
    (hrec : ∀ r y w, db.S.versionAt r y = some w → ∃ v, db.S.lv y = some v ∧ r ≤ v.recNo)
    {a : Nat} {o : HObj V} {y : NodeId} {p : HPtr} (ha : m.obj? a = some o)
    (hp : o.ptr? y = some p) :
    (m.evict D n).ptrRef S0 y p = m.ptrRef S0 y p := by
  apply HMem.ptrRef_evict
  · intro n' hd' b hh' hb hobj
    exact ht.uniq hh' hb hobj
  · intro hpn b ob q r hobj hob hcan hq hr
    -- The handle n is of node y, and so is its object.
    obtain ⟨h1, -, h3, h4, -, h6⟩ := ht
    obtain ⟨hd, hh, hnode⟩ := h6 a o y p n ha hp hpn
    have hb : hd.obj = some b := by simpa [HMem.objOf, hh] using hobj
    have hlive : hd.dead = false := by
      cases hdk : hd.dead with
      | false => rfl
      | true => rw [h4 n hd hh hdk] at hb; cases hb
    obtain ⟨e, b', o', he, -, -, hb', ho', hon⟩ := h1 hd.node n (h3 n hd hh hlive)
    rw [hh] at he; cases he
    rw [hb] at hb'; cases hb'
    rw [hob] at ho'; cases ho'
    -- Its position is y's latest record.
    have hpos := (hc.1 b ob hob hcan).2.2
    rw [hq, hon, hnode] at hpos
    -- Every record that Rule R gives names a version of y.
    have hver : ∃ u, db.S.versionAt r y = some u := by
      unfold ruleRRef at hr
      cases hnw : newest S0 m.s y with
      | none =>
        rw [hnw] at hr
        simp only at hr
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hw.2 a o y p r ha hp hr)
        exact ⟨u, hu⟩
      | some w =>
        rw [hnw] at hr
        obtain ⟨r0, -, hr0⟩ := newest_some hnw
        have hr0' := versionAt_prefix hpre hr0
        have hrec0 := hidx r0 y w hr0'
        cases hpr : p.ref with
        | none =>
          rw [hpr] at hr
          simp only [Option.some.injEq] at hr
          subst hr
          rw [hrec0]; exact ⟨w, hr0'⟩
        | some r1 =>
          rw [hpr] at hr
          simp only at hr
          split at hr
          · simp only [Option.some.injEq] at hr
            subst hr
            rw [hrec0]; exact ⟨w, hr0'⟩
          · simp only [Option.some.injEq] at hr
            subst hr
            obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (hw.2 a o y p r1 ha hp hpr)
            exact ⟨u, hu⟩
    obtain ⟨u, hu⟩ := hver
    obtain ⟨v, hv, hle⟩ := hrec r y u hu
    rw [hv] at hpos
    simp only [Option.map_some, Option.some.injEq] at hpos
    omega

end SIS
