/-
Proofs for stage 2 (bergdb item 001, WP E6), part 2: T-PIN. In every state of a
run with eviction and restarts, an object outside the pinned set has been
written, so it may be detached; unswizzling each slot that names it (one per
object and pointee, `SlotsND`) leaves no memory slot to it, and it can then be
released.
-/
import SIS.Proof.EvictKeys

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Unswizzling every slot to an object, then releasing it -/

/-- The slots of memory m that are memory slots to object h, as (object,
pointee) pairs. -/
def Mem.slotsTo (m : Mem V) (h : Nat) : List (Nat × NodeId) :=
  m.objs.flatMap (fun p => (p.2.slots.filter (fun q => q.2 == Slot.mem h)).map (fun q => (p.1, q.1)))

section Evict

variable {D : Dirty} {h : Nat}

/-- Whether object h may be detached depends only on its node, its canonical
flag, its position and the root's handle. -/
theorem Mem.detachable_congr {m m' : Mem V} (hr : m'.root = m.root)
    (ho : (m'.obj? h).map (fun o => (o.canonical, o.node, o.pos)) =
      (m.obj? h).map (fun o => (o.canonical, o.node, o.pos))) :
    m'.detachable D h = m.detachable D h := by
  unfold Mem.detachable Mem.pinned
  rw [hr]
  cases h1 : m.obj? h with
  | none =>
    rw [h1] at ho
    cases h2 : m'.obj? h with
    | none => rfl
    | some o' => rw [h2] at ho; cases ho
  | some o =>
    rw [h1] at ho
    cases h2 : m'.obj? h with
    | none => rw [h2] at ho; cases ho
    | some o' =>
      rw [h2] at ho
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ho
      obtain ⟨e1, e2, e3⟩ := ho
      simp only [e1, e2, e3]

theorem Mem.detachable_unswizzle {m : Mem V} (a : Nat) (y : NodeId) :
    (m.unswizzle D a y).detachable D h = m.detachable D h := by
  unfold Mem.unswizzle
  split
  · rename_i op hop
    split
    · split
      · split
        · refine Mem.detachable_congr rfl ?_
          rw [Mem.obj?_setObj]
          split
          · rename_i hha
            subst hha
            rw [hop]
            rfl
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-- After unswizzling the slot of object a for y, every memory slot to a
detachable object h was one before, and is not that slot. -/
theorem Mem.unswizzle_slotsTo {m : Mem V} (hs : SlotsND m) (hnd : (m.objs.map (·.1)).Nodup)
    (hd : m.detachable D h = true) (a : Nat) (y : NodeId) :
    ∀ p ∈ (m.unswizzle D a y).objs, ∀ q ∈ p.2.slots, q.2 = Slot.mem h →
      (∃ p0 ∈ m.objs, p0.1 = p.1 ∧ q ∈ p0.2.slots) ∧ ¬ (p.1 = a ∧ q.1 = y) := by
  -- an entry of m that is a memory slot to h is the slot of its object for its pointee
  have hslot : ∀ p ∈ m.objs, ∀ q ∈ p.2.slots, q.2 = Slot.mem h →
      m.obj? p.1 = some p.2 ∧ p.2.slot? q.1 = some (Slot.mem h) := by
    intro p hp q hq hqh
    refine ⟨lookup_of_mem m.objs hnd p hp, ?_⟩
    rw [← hqh]
    exact lookup_of_mem p.2.slots (hs p hp) q hq
  obtain ⟨o, ho⟩ : ∃ o, m.obj? h = some o := by
    unfold Mem.detachable at hd
    cases h1 : m.obj? h with
    | none => rw [h1] at hd; cases hd
    | some o => exact ⟨o, rfl⟩
  -- an unchanged memory: the slot of a for y is not a memory slot to h
  have hsame : (∀ op, m.obj? a = some op → op.slot? y ≠ some (Slot.mem h)) →
      ∀ p ∈ m.objs, ∀ q ∈ p.2.slots, q.2 = Slot.mem h →
        (∃ p0 ∈ m.objs, p0.1 = p.1 ∧ q ∈ p0.2.slots) ∧ ¬ (p.1 = a ∧ q.1 = y) := by
    intro hne p hp q hq hqh
    refine ⟨⟨p, hp, rfl, hq⟩, ?_⟩
    rintro ⟨rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hslot p hp q hq hqh
    exact hne p.2 h1 h2
  unfold Mem.unswizzle
  split
  · rename_i op hop
    split
    · rename_i h' hsl
      split
      · rename_i o' ho'
        split
        · rename_i hd'
          -- the slot is unswizzled
          intro p hp q hq hqh
          unfold Mem.setObj at hp
          simp only [List.mem_cons, List.mem_filter] at hp
          rcases hp with rfl | ⟨hp, hpa⟩
          · simp only [Obj.setSlot, List.mem_map] at hq
            obtain ⟨q0, hq0, hqe⟩ := hq
            split at hqe
            · rw [← hqe] at hqh; cases hqh
            · rename_i hq0y
              subst hqe
              refine ⟨⟨(a, op), mem_of_lookup m.objs a op hop, rfl, hq0⟩, ?_⟩
              rintro ⟨-, hy⟩
              exact hq0y (beq_iff_eq.mpr hy)
          · refine ⟨⟨p, hp, rfl, hq⟩, ?_⟩
            rintro ⟨hpa', -⟩
            simp only [bne_iff_ne, ne_eq] at hpa
            exact hpa hpa'
        · -- h' is not detachable: so h' ≠ h, and the slot is not to h
          apply hsame
          intro op' hop' hsl'
          rw [hop, Option.some.injEq] at hop'
          subst hop'
          rw [hsl, Option.some.injEq, Slot.mem.injEq] at hsl'
          subst hsl'
          rename_i hnd'
          exact hnd' hd
      · apply hsame
        intro op' hop' hsl'
        rw [hop, Option.some.injEq] at hop'
        subst hop'
        rw [hsl, Option.some.injEq, Slot.mem.injEq] at hsl'
        subst hsl'
        rename_i hno
        rw [ho] at hno; cases hno
    · apply hsame
      intro op' hop' hsl'
      rw [hop, Option.some.injEq] at hop'
      subst hop'
      rename_i hns
      exact hns h hsl'
  · rename_i hno
    apply hsame
    intro op' hop' _
    rw [hop'] at hno; cases hno

theorem SlotsND.objsND_unswizzle {m : Mem V} (hnd : (m.objs.map (·.1)).Nodup) (a : Nat) (y : NodeId) :
    ((m.unswizzle D a y).objs.map (·.1)).Nodup := by
  unfold Mem.unswizzle
  split
  · split
    · split
      · split
        · exact nodup_setObj_keys _ _ _ hnd
        · exact hnd
      · exact hnd
    · exact hnd
  · exact hnd

/-- Unswizzling, in turn, every slot in L, where L holds every memory slot to the
detachable object h, leaves no memory slot to h. -/
theorem Mem.unswizzles_incoming (L : List (Nat × NodeId)) :
    ∀ m : Mem V, SlotsND m → (m.objs.map (·.1)).Nodup → m.detachable D h = true →
      (∀ p ∈ m.objs, ∀ q ∈ p.2.slots, q.2 = Slot.mem h → (p.1, q.1) ∈ L) →
      (L.foldl (fun m q => m.unswizzle D q.1 q.2) m).incoming h = false := by
  induction L with
  | nil =>
    intro m _ _ _ hall
    simp only [List.foldl_nil]
    unfold Mem.incoming
    cases hi : m.objs.any (fun p => p.2.slots.any (fun q => q.2 == Slot.mem h)) with
    | false => rfl
    | true =>
      obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp hi
      obtain ⟨q, hq, hqh⟩ := List.any_eq_true.mp hq
      exact absurd (hall p hp q hq (beq_iff_eq.mp hqh)) List.not_mem_nil
  | cons a L ih =>
    intro m hs hnd hd hall
    simp only [List.foldl_cons]
    apply ih _ (hs.unswizzle D a.1 a.2) (SlotsND.objsND_unswizzle hnd a.1 a.2)
      (by rw [Mem.detachable_unswizzle]; exact hd)
    intro p hp q hq hqh
    obtain ⟨⟨p0, hp0, hp1, hq0⟩, hne⟩ := Mem.unswizzle_slotsTo hs hnd hd a.1 a.2 p hp q hq hqh
    have hin := hall p0 hp0 q hq0 hqh
    rw [hp1] at hin
    rcases List.mem_cons.mp hin with he | he
    · exact absurd ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩ hne
    · exact he

/-- Every memory slot of m to h is in `m.slotsTo h`. -/
theorem Mem.mem_slotsTo {m : Mem V} {p : Nat × Obj V} (hp : p ∈ m.objs) {q : NodeId × Slot}
    (hq : q ∈ p.2.slots) (hqh : q.2 = Slot.mem h) : (p.1, q.1) ∈ m.slotsTo h := by
  unfold Mem.slotsTo
  rw [List.mem_flatMap]
  refine ⟨p, hp, ?_⟩
  rw [List.mem_map]
  exact ⟨q, List.mem_filter.mpr ⟨hq, by rw [hqh]; simp⟩, rfl⟩

/-- Evicting a detachable object: each slot of `m.slotsTo h` is a memory slot to
h, and unswizzling them all, then releasing h, removes h. -/
theorem Mem.evict_ok {m : Mem V} (hs : SlotsND m) (hnd : (m.objs.map (·.1)).Nodup)
    (hd : m.detachable D h = true) (sp : Spec V T) (S0 S : Stream V T) :
    (∀ q ∈ m.slotsTo h, (m.obj? q.1).bind (·.slot? q.2) = some (Slot.mem h)) ∧
    (((m.slotsTo h).map (fun q => CacheOp.unswizzle q.1 q.2) ++ [CacheOp.release h]).foldl
      (Mem.cacheOp sp S0 S D) m).obj? h = none := by
  refine ⟨fun q hq => ?_, ?_⟩
  · unfold Mem.slotsTo at hq
    rw [List.mem_flatMap] at hq
    obtain ⟨p, hp, hq⟩ := hq
    rw [List.mem_map] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨hq0, hqh⟩ := List.mem_filter.mp hq0
    simp only
    have h1 : m.obj? p.1 = some p.2 := lookup_of_mem m.objs hnd p hp
    rw [h1, Option.bind_some]
    rw [← (beq_iff_eq.mp hqh)]
    exact lookup_of_mem p.2.slots (hs p hp) q0 hq0
  · rw [List.foldl_append, List.foldl_map]
    simp only [List.foldl_cons, List.foldl_nil, Mem.cacheOp]
    generalize hu : (m.slotsTo h).foldl (fun m q => m.unswizzle D q.1 q.2) m = mu
    have hinc : mu.incoming h = false := by
      rw [← hu]
      exact Mem.unswizzles_incoming _ m hs hnd hd (fun p hp q hq hqh => Mem.mem_slotsTo hp hq hqh)
    have hdu : mu.detachable D h = true := by
      rw [← hu]
      have key : ∀ (L : List (Nat × NodeId)) (m : Mem V),
          (L.foldl (fun m q => m.unswizzle D q.1 q.2) m).detachable D h = m.detachable D h := by
        intro L
        induction L with
        | nil => intro m; rfl
        | cons a L ih => intro m; simp only [List.foldl_cons]; rw [ih, Mem.detachable_unswizzle]
      rw [key]; exact hd
    unfold Mem.release Mem.eligible
    rw [hdu, hinc]
    simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
    exact lookup_filter_self _ _

end Evict

/-! ## Outside the pinned set, every object has been written -/

section Pin

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- With the invariant, an object outside the pinned set has a position: a
canonical one is of a written node not in D, which is clean, so its latest
version exists and is the object's position; a snapshot is the version at its
position. -/
theorem EInv.detachable_of_unpinned (hm : EInv sp db S0 k m) (hinv : Inv sp db k) (hls : LiveSub sp)
    {h : Nat} {o : Obj V} (ho : m.obj? h = some o) (hp : m.pinned db.D h = false) :
    m.detachable db.D h = true := by
  unfold Mem.pinned at hp
  rw [ho] at hp
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hp
  obtain ⟨hr, hcd⟩ := hp
  have hpos : o.pos.isSome = true := by
    cases hc : o.canonical with
    | false =>
      obtain ⟨r, w, hpr, -⟩ := hm.snap h o ho hc
      rw [hpr]; rfl
    | true =>
      rw [hc, Bool.true_and] at hcd
      have hcan := hm.canonicalOf_of ho hc
      have hxr : o.node ≠ SIS.root := by
        intro hx
        obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
        have h1 := hm.canonicalOf_of ho0 hc0
        rw [hn0, ← hx, hcan, Option.some.injEq] at h1
        exact hr h1
      obtain ⟨n, hn, -⟩ := hm.cc h o ho hc
      obtain ⟨t, ht, hrt⟩ := hinv.born o.node (by rw [hn]; rfl)
      obtain ⟨v, hv, -⟩ := hinv.clean_good hls hcd (written_of_ne_root sp hxr) ht hrt
      rw [hm.pos.lv0 hcan ho, hv]; rfl
  have hb : (h == m.root) = false := beq_eq_false_iff_ne.mpr hr
  unfold Mem.detachable Mem.pinned
  rw [ho]
  simp only [hb, hcd, hpos, Bool.false_or, Bool.not_false, Bool.true_and]

end Pin

end SIS
