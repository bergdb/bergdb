/-
Proofs about the physical layer, part 7: the writer's first touch makes a
canonical object that holds the node's whole history (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem makeCanonical_eval (m : Mem V) {hp h : Nat} {y : NodeId} {op o1 : Obj V}
    (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) (hop : m.obj? hp = some op)
    (hne : hp ≠ h) :
    m.makeCanonical hp y h =
      (((m.setObj h { o1 with canonical := true }).setTable y h).setObj hp (op.setSlot y (Slot.mem h)), h) := by
  unfold Mem.makeCanonical
  simp only [ht, beq_self_eq_true, ↓reduceIte, ho1]
  rw [Mem.obj?_setTable, Mem.obj?_setObj]
  simp only [hne, ↓reduceIte, hop]

section Promote

variable {sp : Spec V T} {db : DB V T} {K k : Nat}

/-- The memory after object h, the node table's object for y, is made canonical. -/
def promoteMem (m : Mem V) (h : Nat) (o1 : Obj V) (y : NodeId) : Mem V :=
  (m.setObj h { o1 with canonical := true }).setTable y h

variable {m : Mem V} {y : NodeId} {h : Nat} {o1 : Obj V}

theorem promote_obj (_ho1 : m.obj? h = some o1) (h' : Nat) :
    (promoteMem m h o1 y).obj? h' = if h' = h then some { o1 with canonical := true } else m.obj? h' := by
  unfold promoteMem; rw [Mem.obj?_setTable, Mem.obj?_setObj]

theorem promote_table (ht : m.tableOf y = some h) (z : NodeId) :
    (promoteMem m h o1 y).tableOf z = m.tableOf z := by
  unfold promoteMem
  rw [Mem.tableOf_setTable, Mem.tableOf_setObj]
  split
  · rename_i hz; subst hz; exact ht.symm
  · rfl

theorem promote_canon (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) (z : NodeId) (h' : Nat)
    (hc : m.canonicalOf z = some h') : (promoteMem m h o1 y).canonicalOf z = some h' := by
  obtain ⟨ht', o, ho, hcan⟩ := (m.canonicalOf_eq_some z h').mp hc
  refine ((promoteMem m h o1 y).canonicalOf_eq_some z h').mpr ⟨by rw [promote_table ht]; exact ht', ?_⟩
  rw [promote_obj ho1]
  split
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨o, ho, hcan⟩

theorem promote_obj_self (ho1 : m.obj? h = some o1) :
    (promoteMem m h o1 y).obj? h = some { o1 with canonical := true } := by
  rw [promote_obj ho1]; simp

theorem promote_canon_y (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) :
    (promoteMem m h o1 y).canonicalOf y = some h :=
  ((promoteMem m h o1 y).canonicalOf_eq_some y h).mpr
    ⟨by rw [promote_table ht]; exact ht, { o1 with canonical := true }, promote_obj_self ho1, rfl⟩

theorem promote_ne_none (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) {x : NodeId}
    (hx : m.canonicalOf x ≠ none) : (promoteMem m h o1 y).canonicalOf x ≠ none := by
  cases hc : m.canonicalOf x with
  | none => exact absurd hc hx
  | some h' => rw [promote_canon ht ho1 x h' hc]; simp

theorem promote_le (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) :
    m.Le (promoteMem m h o1 y) := by
  refine ⟨fun h' o ho => ?_, fun z h' hc => promote_canon ht ho1 z h' hc⟩
  rw [promote_obj ho1]
  split
  · rename_i hh; subst hh
    rw [ho1, Option.some.injEq] at ho; subst ho
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun h => by simp at h⟩
  · exact ⟨o, ho, rfl, rfl, rfl, rfl, id, fun _ => rfl⟩

theorem promote_snapOK (ht : m.tableOf y = some h) (_ho1 : m.obj? h = some o1) {K h' : Nat}
    {o : Obj V} {w : Version V} (hs : SnapOK db m K h' o w) :
    SnapOK db (promoteMem m h o1 y) K h' o w := by
  obtain ⟨r, a1, a2, a3, a4, a5⟩ := hs
  refine ⟨r, a1, a2, a3, a4, ?_⟩
  rcases a5 with a5 | ⟨b1, b2, b3, b4⟩
  · exact Or.inl a5
  · exact Or.inr ⟨b1, b2, by rw [promote_table ht]; exact b3, b4⟩

theorem promote_readable (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) (_hy1 : o1.node = y)
    {t : Time} {h' : Nat} {z : NodeId} (hr : Readable sp db m K t h' z) :
    Readable sp db (promoteMem m h o1 y) K t h' z := by
  obtain ⟨o, ho, hz, hc⟩ := hr
  by_cases hh : h' = h
  · subst hh
    rw [ho1, Option.some.injEq] at ho
    subst ho
    exact ⟨{ o1 with canonical := true }, promote_obj_self ho1, hz, Or.inl rfl⟩
  · refine ⟨o, by rw [promote_obj ho1]; simp only [hh, ↓reduceIte]; exact ho, hz, ?_⟩
    rcases hc with hc | ⟨w, hw, hg⟩
    · exact Or.inl hc
    · exact Or.inr ⟨w, promote_snapOK ht ho1 hw, hg⟩

theorem promote_slotGood (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1) (hy1 : o1.node = y)
    {t : Time} {z : NodeId} {sl : Slot} (hg : SlotGood sp db m K t z sl) :
    SlotGood sp db (promoteMem m h o1 y) K t z sl := by
  cases sl with
  | mem h' => exact promote_readable ht ho1 hy1 hg
  | stream r =>
    rcases hg with hg | hg
    · left
      cases hc : m.canonicalOf z with
      | none => exact absurd hc hg
      | some hc' => rw [promote_canon ht ho1 z hc' hc]; simp
    · exact Or.inr hg

theorem promote_slotFresh (ht : m.tableOf y = some h) (ho1 : m.obj? h = some o1)
    {z : NodeId} {sl : Slot} (hf : SlotFresh db m z sl) : SlotFresh db (promoteMem m h o1 y) z sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho, hc⟩ := hf
    by_cases hh : h' = h
    · subst hh
      exact ⟨{ o1 with canonical := true }, promote_obj_self ho1, Or.inl rfl⟩
    · exact ⟨o, by rw [promote_obj ho1]; simp only [hh, ↓reduceIte]; exact ho, hc⟩
  | stream r =>
    rcases hf with hf | hf
    · left
      cases hc : m.canonicalOf z with
      | none => exact absurd hc hf
      | some hc' => rw [promote_canon ht ho1 z hc' hc]; simp
    · exact Or.inr hf

theorem promote_atLeast (ho1 : m.obj? h = some o1) {z : NodeId} {h' : Nat} {r' : Option Nat}
    (ha : AtLeast m z h' r') : AtLeast (promoteMem m h o1 y) z h' r' := by
  obtain ⟨o, ho, hz, hc⟩ := ha
  by_cases hh : h' = h
  · rw [hh] at ho ⊢
    rw [ho1, Option.some.injEq] at ho
    rw [← ho] at hz
    exact ⟨{ o1 with canonical := true }, promote_obj_self ho1, hz, Or.inl rfl⟩
  · exact ⟨o, by rw [promote_obj ho1]; simp only [hh, ↓reduceIte]; exact ho, hz, hc⟩

/-- Making the node table's object for y canonical keeps the invariant, if it
holds y's whole history and its slots are good and fresh. -/
theorem MemInv.promote (hm : MemInv sp db K m) (ht : m.tableOf y = some h)
    (ho1 : m.obj? h = some o1) (hc1 : o1.canonical = false) (hy1 : o1.node = y)
    (hh : ∃ n, db.P.get? y = some n ∧ o1.hist = n.hist.upTo K ∧ o1.level = n.level ∧
      o1.isData = n.isData)
    (hg : ∀ t ≤ K, reachable sp db.P t y = true → ∀ z ∈ sp.live (o1.hist.upTo t),
      ∃ sl, o1.slot? z = some sl ∧ SlotGood sp db m K t z sl)
    (hf : reachable sp db.P K y = true → ∀ z ∈ sp.live o1.hist,
      ∃ sl, o1.slot? z = some sl ∧ SlotFresh db m z sl) :
    MemInv sp db K (promoteMem m h o1 y) := by
  have hyr : y ≠ SIS.root := by
    intro hyy
    obtain ⟨ht0, o0, ho0, hc0, -⟩ := hm.root
    rw [← hyy, ht, Option.some.injEq] at ht0
    subst ht0
    rw [ho1, Option.some.injEq] at ho0; subst ho0
    rw [hc1] at hc0; cases hc0
  obtain ⟨w1, hw1, -⟩ := hm.snap h o1 ho1 hc1
  refine ⟨hm.sEq, hm.sK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun d R x a b c e hc => ?_, fun x w a b c hc => ?_, fun x n e a b c d hc => ?_⟩
  · intro h' hh'
    rw [promote_obj ho1]
    have := lt_next_of_obj? hm.fresh ho1
    unfold promoteMem at hh'
    simp only [Mem.setTable_next, Mem.setObj_next] at hh'
    simp only [show h' ≠ h by omega, ↓reduceIte]
    exact hm.fresh h' hh'
  · unfold promoteMem
    rw [Mem.setTable_objs]
    exact nodup_setObj_keys m h _ hm.nodup
  · obtain ⟨ht0, o0, ho0, hc0, hn0⟩ := hm.root
    have hne : m.root ≠ h := by
      intro he; rw [he, ho1, Option.some.injEq] at ho0; subst ho0; rw [hc1] at hc0; cases hc0
    refine ⟨by rw [promote_table ht]; unfold promoteMem; simp only [Mem.setTable_root, Mem.setObj_root]; exact ht0, o0, ?_, hc0, hn0⟩
    unfold promoteMem; simp only [Mem.setTable_root, Mem.setObj_root]
    rw [← promoteMem, promote_obj ho1]; simp only [hne, ↓reduceIte]; exact ho0
  · intro z h' ht'
    rw [promote_table ht] at ht'
    obtain ⟨o, ho, hz⟩ := hm.tbl z h' ht'
    rw [promote_obj ho1]
    split
    · rename_i hh'; subst hh'; rw [ho1, Option.some.injEq] at ho; subst ho; exact ⟨_, rfl, hz⟩
    · exact ⟨o, ho, hz⟩
  · intro h' o ho
    rw [promote_obj ho1] at ho
    split at ho
    · cases ho; exact hm.born h o1 ho1
    · exact hm.born h' o ho
  · -- canonical objects
    intro h' o ho hc
    rw [promote_obj ho1] at ho
    split at ho
    · rename_i hh'
      cases ho
      rw [hh']
      have e1 : ({ o1 with canonical := true } : Obj V).node = y := hy1
      unfold CanonOK
      rw [e1]
      obtain ⟨r1, hr1, hv1, -⟩ := hw1
      refine ⟨by rw [promote_table ht]; exact ht, hh, ?_, ?_, ?_⟩
      · intro p hp
        simp only at hp
        rw [hr1, Option.some.injEq] at hp; subst hp
        rw [← hy1, hv1]; rfl
      · intro t htK hr z hz
        obtain ⟨sl, hsl, hg'⟩ := hg t htK hr z hz
        exact ⟨sl, hsl, promote_slotGood ht ho1 hy1 hg'⟩
      · intro hr z hz
        obtain ⟨sl, hsl, hf'⟩ := hf hr z hz
        exact ⟨sl, hsl, promote_slotFresh ht ho1 hf'⟩
    · obtain ⟨c1, c2, c3, c4, c5⟩ := hm.canon h' o ho hc
      refine ⟨by rw [promote_table ht]; exact c1, c2, c3, ?_, ?_⟩
      · intro t htK hr z hz
        obtain ⟨sl, hsl, hg'⟩ := c4 t htK hr z hz
        exact ⟨sl, hsl, promote_slotGood ht ho1 hy1 hg'⟩
      · intro hr z hz
        obtain ⟨sl, hsl, hf'⟩ := c5 hr z hz
        exact ⟨sl, hsl, promote_slotFresh ht ho1 hf'⟩
  · -- snapshots
    intro h' o ho hc
    rw [promote_obj ho1] at ho
    split at ho
    · cases ho; simp at hc
    · obtain ⟨w, hw, hss1, hss2⟩ := hm.snap h' o ho hc
      refine ⟨w, promote_snapOK ht ho1 hw, hss1, ?_⟩
      intro z sl hsl
      rcases hss2 z sl hsl with h2 | ⟨h'', h2, h3⟩
      · exact Or.inl h2
      · exact Or.inr ⟨h'', h2, promote_atLeast ho1 h3⟩
  · -- memory slots
    intro h' o z h'' ho hsl
    rw [promote_obj ho1] at ho
    have hms : MemSlotOK m z h'' := by
      split at ho
      · rename_i hh'; cases ho; exact hm.memSlot h o1 z h'' ho1 hsl
      · exact hm.memSlot h' o z h'' ho hsl
    obtain ⟨o', ho', hz', hc'⟩ := hms
    by_cases hh'' : h'' = h
    · rw [hh''] at ho' ⊢
      rw [ho1, Option.some.injEq] at ho'
      rw [← ho'] at hz'
      refine ⟨{ o1 with canonical := true }, promote_obj_self ho1, hz', Or.inl ?_⟩
      rw [promote_table ht, ← hz', hy1]; exact ht
    · refine ⟨o', by rw [promote_obj ho1]; simp only [hh'', ↓reduceIte]; exact ho', hz', ?_⟩
      rcases hc' with hc' | ⟨hcan, h0, o0, p, p0, ht0, ho0, hp, hp0, hlt⟩
      · left; rw [promote_table ht]; exact hc'
      · right
        by_cases hh0 : h0 = h
        · rw [hh0] at ho0 ht0
          rw [ho1, Option.some.injEq] at ho0
          rw [← ho0] at hp0
          exact ⟨hcan, h, { o1 with canonical := true }, p, p0, by rw [promote_table ht]; exact ht0,
            promote_obj_self ho1, hp, hp0, hlt⟩
        · exact ⟨hcan, h0, o0, p, p0, by rw [promote_table ht]; exact ht0,
            by rw [promote_obj ho1]; simp only [hh0, ↓reduceIte]; exact ho0, hp, hp0, hlt⟩
  · exact promote_ne_none ht ho1 (hm.coverGd d R x a b c e) hc
  · exact promote_ne_none ht ho1 (hm.coverSec x w a b c) hc
  · exact promote_ne_none ht ho1 (hm.coverNew x n e a b c d) hc

end Promote

/-! ### The writer's first touch -/

section Writer

variable {sp : Spec V T} {db dbK : DB V T} {K k : Nat} {m : Mem V}

/-- A live child at K of a canonical object's node is a node on a lower level. -/
theorem MemInv.canon_child (hm : MemInv sp db K m) (hctx : PCtx sp db k) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) (hcan : op.canonical = true) {y : NodeId} (hy : y ∈ sp.live op.hist) :
    ∃ n ny, db.P.get? op.node = some n ∧ db.P.get? y = some ny ∧ ny.level < n.level ∧
      op.hist = n.hist.upTo K ∧ y ∈ sp.live (n.hist.upTo K) := by
  obtain ⟨-, ⟨n, hn, hh, -, -⟩, -⟩ := hm.canon hp op hop hcan
  obtain ⟨e, he, hye⟩ := hctx.ls _ _ hy
  rw [hh] at he
  obtain ⟨ny, hny, hlt⟩ := hctx.inv.ptrs op.node n hn e (mem_upTo.mp he).1 y hye
  exact ⟨n, ny, hn, hny, hlt, hh, by rw [← hh]; exact hy⟩

/-- The writer's first touch, from a canonical object of a node reachable at K,
of the slot for a live child y: y's object is canonical after it, and the
invariant is kept. -/
theorem MemInv.follow_writer (hm : MemInv sp db K m) (hctx : PCtx sp db k)
    (hk : KCtx sp db dbK K) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hcan : op.canonical = true) (hr : reachable sp db.P K op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) :
    ∃ m' h1, m.follow sp db.S hp y true = (m', some h1) ∧ MemInv sp db K m' ∧ m.Le m' ∧
      m'.canonicalOf y = some h1 := by
  have hls := hctx.ls
  obtain ⟨-, -, -, c4, c5⟩ := hm.canon hp op hop hcan
  obtain ⟨sl, hsl, hfr⟩ := c5 hr y hy
  obtain ⟨n, ny, hn, hny, hlt, hhist, hyK⟩ := hm.canon_child hctx hop hcan hy
  have hyne : y ≠ op.node := by
    intro he; rw [← he, hny, Option.some.injEq] at hn; subst hn; omega
  have hry : reachable sp db.P K y = true := by
    rw [reachable_iff] at hr ⊢
    exact Reach.child hr hn hyK hny hlt
  obtain ⟨sl', hsl', hg⟩ := c4 K (Nat.le_refl _) hr y (by rw [hhist, upTo_upTo _ (Nat.le_refl _)]; exact hyK)
  rw [hsl, Option.some.injEq] at hsl'
  subst hsl'
  obtain ⟨m2, h1, -, hm2, hle2, hkc2, -, ⟨o1, ho1, hn1, hW⟩, hF⟩ :=
    hm.follow_reader hctx hk.fixedLe hop hsl hyne (Nat.le_refl _) hry hg
  obtain ⟨ht1, hf1⟩ := hF hfr
  cases hc1 : o1.canonical
  · -- The object is made canonical.
    rw [hc1] at hW
    simp only [Bool.false_eq_true, ↓reduceIte] at hW
    obtain ⟨op2, hop2, hc2⟩ := hkc2 hp op hop
    have hne : hp ≠ h1 := by
      intro he
      rw [he, ho1, Option.some.injEq] at hop2
      have e1 : op2.node = op.node := by
        have := congrArg (fun c => c.1) hc2; simpa [Obj.core] using this
      rw [← hop2, hn1] at e1
      exact hyne e1
    rw [makeCanonical_eval m2 ht1 ho1 hop2 hne] at hW
    have hnc : m2.canonicalOf y = none := canonicalOf_none_of_table ht1 ho1 hc1
    -- o1's version is y's latest.
    obtain ⟨w1, hw1, hss1, hss2⟩ := hm2.snap h1 o1 ho1 hc1
    obtain ⟨o1', ho1', hf1'⟩ := hf1
    rw [ho1, Option.some.injEq] at ho1'
    subst ho1'
    have hlv1 : db.S.lv y = some w1 := by
      obtain ⟨r1, hr1, hv1, -, hd1, -⟩ := hw1
      rw [hn1] at hv1
      rcases hf1' with hf1' | hf1' | hf1'
      · rw [hc1] at hf1'; cases hf1'
      · obtain ⟨-, -, n1, hn1', -, -, hd1'⟩ := hctx.inv.version_node hv1
        exact hctx.dataOnce y n1 r1 w1 hn1' (by rw [← hd1', ← hd1, hf1']) hv1
      · cases hlv : db.S.lv y with
        | none => rw [hlv, hr1] at hf1'; cases hf1'
        | some v =>
          rw [hlv, hr1] at hf1'
          simp only [Option.map_some, Option.some.injEq] at hf1'
          subst hf1'
          have := hctx.inv.lv_at hlv
          rw [hv1, Option.some.injEq] at this
          rw [this]
    have hgood : ∀ t ≤ K, reachable sp db.P t y = true → good sp db.S db.P t w1 = true := by
      intro t ht hrt
      obtain ⟨v, hv, hg'⟩ := hm2.cover.mg hk hctx hnc ht hrt
      rw [hlv1, Option.some.injEq] at hv
      rw [hv]; exact hg'
    -- What o1 holds: y's history up to K.
    obtain ⟨r1, hr1, hv1, hl1, hd1, h5⟩ := hw1
    rw [hn1] at hv1
    obtain ⟨-, -, n1, hn1', hwh1, hwl1, hwd1⟩ := hctx.inv.version_node hv1
    rw [hny, Option.some.injEq] at hn1'
    subst hn1'
    have hgK := hgood K (Nat.le_refl _) hry
    have hhist1 : o1.hist = ny.hist.upTo K := by
      rcases h5 with ⟨h6, h7⟩ | ⟨h6, -, -, h9⟩
      · rw [good_iff] at hgK
        obtain ⟨⟨n', hn', hc'⟩, -⟩ := hgK
        rw [(hctx.inv.version_node hv1).1, hny, Option.some.injEq] at hn'
        subst hn'
        rw [h6, ← hc', upTo_of_forall _ _ h7]
      · unfold histAt at h9
        rw [hn1, hny] at h9
        simp only [Option.map_some, Option.getD_some] at h9
        rw [h9, h6]
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro e he
        rw [hwh1] at he
        have he1 := mem_upTo.mp he
        have he2 := mem_upTo.mp he1.1
        have : e ∈ ny.hist.upTo K := mem_upTo.mpr ⟨he2.1, by have := hm2.sK; omega⟩
        rw [h9] at this; cases this
    have hpromote := hm2.promote ht1 ho1 hc1 hn1
      ⟨ny, hny, hhist1, by rw [hl1, hwl1], by rw [hd1, hwd1]⟩
      (by
        intro t ht hrt z hz
        rcases h5 with ⟨h6, -⟩ | ⟨h6, -, -, h9⟩
        · exact hm2.snap_slotGood hctx ⟨hss1, hss2⟩ h6 (hgood t ht hrt) hz
        · exfalso
          have : o1.hist = [] := by rw [hhist1]; unfold histAt at h9; rw [hn1, hny] at h9; simpa using h9
          rw [this, upTo_nil, live_nil hls] at hz
          cases hz)
      (by
        intro hrK z hz
        have hz0 : z ∈ sp.live (ny.hist.upTo K) := by rw [← hhist1]; exact hz
        obtain ⟨e, he, hze⟩ := hls _ _ hz0
        cases hdy : ny.isData
        · by_cases hlate : ∃ r w, K < r ∧ db.S.versionAt r y = some w
          · exfalso
            obtain ⟨r, w, hrK', hw⟩ := hlate
            obtain ⟨hemp, -⟩ := hm2.cover.late_empty hctx hnc hny hdy hrK' hw
            rw [hemp] at he
            cases he
          · have hvK : ∀ r w, K < r → db.S.versionAt r y = some w → False :=
              fun r w h1 h2 => hlate ⟨r, w, h1, h2⟩
            have hz' : z ∈ sp.live w1.hist := by
              rcases h5 with ⟨h6, -⟩ | ⟨-, -, -, h9⟩
              · rw [← h6]; exact hz
              · exfalso
                unfold histAt at h9
                rw [hn1, hny] at h9
                simp only [Option.map_some, Option.getD_some] at h9
                rw [h9] at he
                cases he
            obtain ⟨hcf, hcfs⟩ := hm2.cover.cf hk hctx hnc hry hlv1 hvK hz'
            obtain ⟨sl, hsl1⟩ := Option.isSome_iff_exists.mp (hss1 z (by
              obtain ⟨e', he', hze'⟩ := hls _ _ hz
              exact (mem_pointees sp _ z).mpr ⟨e', he', hze'⟩))
            refine ⟨sl, hsl1, ?_⟩
            rcases hss2 z sl hsl1 with h2 | ⟨h', h2, hal⟩
            · subst h2
              exact Or.inr (Or.inr ⟨hcf, hcfs⟩)
            · subst h2
              obtain ⟨o', ho', hz2, hc'⟩ := hal
              refine ⟨o', ho', ?_⟩
              rcases hc' with hc' | hc' | ⟨p, hp, hle⟩
              · exact Or.inl hc'
              · exact Or.inr (Or.inl hc')
              · right; right
                obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hcfs
                rw [hv] at hcf ⊢
                simp only [Option.map_some] at hcf ⊢
                have hpv := hle v.recNo hcf
                have hposv : (db.S.versionAt p z).isSome := by
                  cases hco : o'.canonical
                  · obtain ⟨w', hw', -⟩ := hm2.snap h' o' ho' hco
                    obtain ⟨r', hr', hv', -⟩ := hw'
                    rw [hp, Option.some.injEq] at hr'; subst hr'
                    rw [hz2] at hv'; simp [hv']
                  · obtain ⟨-, -, c3', -⟩ := hm2.canon h' o' ho' hco
                    have := c3' p hp; rw [hz2] at this; exact this
                obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hposv
                obtain ⟨v', hv', hle'⟩ := hctx.inv.le_lv hu
                rw [hv, Option.some.injEq] at hv'; subst hv'
                rw [hp]; congr 1; omega
        · -- a data node has no pointers
          exfalso
          have := hctx.inv.data y ny hny hdy e (mem_upTo.mp he).1
          rw [this] at hze
          cases hze)
    -- The parent's slot names the canonical object.
    have hop3 : (promoteMem m2 h1 o1 y).obj? hp = some op2 := by
      rw [promote_obj ho1]; simp only [hne, ↓reduceIte]; exact hop2
    have hc2' : op2.canonical = true := by
      have := congrArg (fun c => c.2.2.2.2.1) hc2; simp [Obj.core] at this; rw [this, hcan]
    have hr2 : reachable sp db.P K op2.node = true := by
      have := congrArg (fun c => c.1) hc2; simp [Obj.core] at this; rw [this]; exact hr
    have hy2 : y ∈ sp.live op2.hist := by
      have := congrArg (fun c => c.2.2.2.1) hc2; simp [Obj.core] at this; rw [this]; exact hy
    obtain ⟨-, -, -, -, c5'⟩ := hm2.canon hp op2 hop2 hc2'
    obtain ⟨sl2, hsl2, -⟩ := c5' hr2 y hy2
    obtain ⟨hm4, hs4⟩ := hpromote.swizzle hop3
      ⟨{ o1 with canonical := true }, promote_obj_self ho1, hn1, Or.inl (by rw [promote_table ht1]; exact ht1)⟩
      (fun _ => ⟨fun _ _ _ _ => ⟨{ o1 with canonical := true }, promote_obj_self ho1, hn1, Or.inl rfl⟩,
        fun _ _ => ⟨{ o1 with canonical := true }, promote_obj_self ho1, Or.inl rfl⟩⟩)
      (fun h0 => by rw [hc2'] at h0; cases h0)
      (by rw [hsl2]; rfl)
    refine ⟨(promoteMem m2 h1 o1 y).setObj hp (op2.setSlot y (Slot.mem h1)), h1, hW, hm4,
      (hle2.trans (promote_le ht1 ho1)).trans hs4.le, ?_⟩
    rw [hs4.canonicalOf]
    exact promote_canon_y ht1 ho1
  · -- The object is canonical already.
    rw [hc1] at hW
    simp only [↓reduceIte] at hW
    exact ⟨m2, h1, hW, hm2, hle2,
      (m2.canonicalOf_eq_some y h1).mpr ⟨ht1, o1, ho1, hc1⟩⟩

end Writer

end SIS
