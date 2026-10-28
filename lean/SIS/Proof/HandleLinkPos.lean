/-
Proofs about rule 4 by position (bergdb 005-58): `Rule4_positions`,
`Rule4Pos_handles` and `RunPos_handles` of SIS/HandleTheorems.lean. The memory
that the startup with handles gives rule 4 holds the objects of the lazy
startup's memory, taken to handles; a pointer that holds no handle there is a
stream slot of that memory, which the rerun's invariant describes (`RInv`,
SIS/Proof/PhysStart.lean): it names a version of its pointee, its pointee's
latest version after Rule R, and no version of its pointee lies between it and
the startup section (`RInv.near`). So such a pointer names a version of the
section, its pointee's latest version before the section, or, when the pointee
has no version in the section, the pointee's latest version, its canonical
object's position (`rule4_positions`). Rule 4 by position (`HMem.linkDPos`) then
finds what rule 4 by node id finds (`rule4Pos_handles`): in the second case, for
a key node's pointer, by the `prevPos` of the pointee's first version in the
section, which is a key node version, since a key node points only to key nodes
and data nodes (A4); a top node's pointer that neither map finds goes by node
id; a data node has one version, its canonical object's. Every startup of a run
with handles is from the run's stream (T2-C), so the run with rule 4 by position
is the run with rule 4 by node id (`runPos_handles`).
-/
import SIS.Proof.HandleRestart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The memory before rule 4 -/

/-- The positions change only an object's position. -/
theorem sectionPosObj_fields (S : Stream V T) (s : Nat) (o : Obj V) :
    (if !o.canonical then o else match newest S s o.node with
      | some w => { o with pos := some w.recNo }
      | none => o).node = o.node ∧
    (if !o.canonical then o else match newest S s o.node with
      | some w => { o with pos := some w.recNo }
      | none => o).level = o.level ∧
    (if !o.canonical then o else match newest S s o.node with
      | some w => { o with pos := some w.recNo }
      | none => o).isData = o.isData ∧
    (if !o.canonical then o else match newest S s o.node with
      | some w => { o with pos := some w.recNo }
      | none => o).hist = o.hist ∧
    (if !o.canonical then o else match newest S s o.node with
      | some w => { o with pos := some w.recNo }
      | none => o).slots = o.slots := by
  cases o.canonical
  · simp
  · cases newest S s o.node <;> simp

/-- An object of the memory before rule 4 is an object of the lazy startup's
memory, held by the node table, with its pointers made from its slots. -/
theorem before_obj {m0 : Mem V} {S : Stream V T} {a : Nat} {o : HObj V}
    (ho : ((m0.sectionPos S).toH).obj? a = some o) :
    ∃ o0, m0.obj? a = some o0 ∧ o.node = o0.node ∧ o.level = o0.level ∧ o.isData = o0.isData ∧
      o.hist = o0.hist ∧ o.ptrs = o0.slots.map (m0.sectionPos S).ptrOfH := by
  rw [Mem.toH_obj?] at ho
  split at ho
  · obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [Mem.sectionPos_obj?] at ho1
    obtain ⟨o0, ho0, rfl⟩ := Option.map_eq_some_iff.mp ho1
    obtain ⟨f1, f2, f3, f4, f5⟩ := sectionPosObj_fields S m0.s o0
    exact ⟨o0, ho0, f1, f2, f3, f4, congrArg (List.map (m0.sectionPos S).ptrOfH) f5⟩
  · cases ho

section Before

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A pointer that holds no handle and names record r, of an object of the memory
before rule 4 (startup from the stream after T(k)), is a stream slot with record
r of the lazy startup's object. -/
theorem before_ptr (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) {a : Nat}
    {o : HObj V}
    (ho : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).obj? a = some o)
    {y : NodeId} {p : HPtr} (hmem : (y, p) ∈ o.ptrs) (hh : p.handle = none) {r : Nat}
    (hr : p.ref = some r) :
    ∃ o0, (lazyStartup sp (st sp al ts k).S).obj? a = some o0 ∧
      o0.slot? y = some (Slot.stream (some r)) ∧ o.node = o0.node ∧ o.level = o0.level ∧
      o.hist = o0.hist := by
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  obtain ⟨o0, ho0, hn, hl, -, hh0, hp⟩ := before_obj ho
  refine ⟨o0, ho0, ?_, hn, hl, hh0⟩
  rw [hp] at hmem
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
  have hq1 : q.1 = y := by
    have := congrArg Prod.fst hqe
    rw [Mem.ptrOfH_fst] at this
    exact this
  have hnd := (slotsND_lazyStartup sp (st sp al ts k).S).obj ho0
  have hsl : o0.slot? y = some q.2 := by
    rw [← hq1]; exact lookup_of_mem o0.slots hnd q hq
  obtain ⟨y', sl⟩ := q
  simp only at hq1 hsl
  subst hq1
  cases sl with
  | mem a' =>
    exfalso
    -- A memory slot names the node table's object, all canonical, so its pointer holds it.
    obtain ⟨o', ho', -, hor⟩ := hm.memSlot a o0 y' a' ho0 hsl
    have hta : (lazyStartup sp (st sp al ts k).S).tableOf y' = some a' := by
      rcases hor with h1 | ⟨hc, -⟩
      · exact h1
      · rw [hri.canon a' o' ho'] at hc; cases hc
    have hheld : ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).table.any
        (fun e => e.2 == a') = true := by
      apply List.any_eq_true.mpr
      exact ⟨(y', a'), mem_of_lookup _ y' a' hta, by simp⟩
    unfold Mem.ptrOfH at hqe
    simp only [hheld, ↓reduceIte, Prod.mk.injEq] at hqe
    rw [← hqe.2] at hh
    cases hh
  | stream r0 =>
    unfold Mem.ptrOfH at hqe
    simp only [Prod.mk.injEq] at hqe
    rw [← hqe.2] at hr
    simp only at hr
    rw [hr] at hsl
    exact hsl

/-- A canonical object of the memory before rule 4 is the node table's, at its
node's latest position. -/
theorem before_canon (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) {y : NodeId}
    {b : Nat}
    (hb : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).canonicalOf y = some b) :
    ((((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).obj? b).bind (·.pos) =
      ((st sp al ts k).S.lv y).map (·.recNo) ∧
    (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).tableOf y = some b := by
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hnd0 := tblND_lazyStartup sp (st sp al ts k).S
  generalize hm0 : lazyStartup sp (st sp al ts k).S = m0 at hri hm hnd0 hb ⊢
  have hs0 : m0.s = lastSp (st sp al ts k).S := hm.sEq
  have htbl1 : ∀ z a, (m0.sectionPos (st sp al ts k).S).tableOf z = some a →
      ∃ o, (m0.sectionPos (st sp al ts k).S).obj? a = some o ∧ o.node = z := by
    intro z a ht
    obtain ⟨o, ho, hon⟩ := hm.tbl z a ht
    refine ⟨_, by rw [Mem.sectionPos_obj?, ho]; rfl, ?_⟩
    exact (sectionPosObj_fields (st sp al ts k).S m0.s o).1.trans hon
  rw [Mem.toH_canonicalOf (m := m0.sectionPos (st sp al ts k).S) hnd0 htbl1,
    Mem.sectionPos_canonicalOf] at hb
  obtain ⟨ht, ob, hob, hcb⟩ := (m0.canonicalOf_eq_some y b).mp hb
  obtain ⟨ob', hob', hnb⟩ := hm.tbl y b ht
  rw [hob, Option.some.injEq] at hob'
  subst hob'
  refine ⟨?_, ht⟩
  have hheld : (m0.sectionPos (st sp al ts k).S).heldA b = true := by
    unfold Mem.heldA
    apply List.any_eq_true.mpr
    exact ⟨(y, b), mem_of_lookup _ y b ht, by simp⟩
  rw [Mem.toH_obj?, hheld, Mem.sectionPos_obj?, hob]
  simp only [↓reduceIte, Option.map_some, Option.bind_some, hcb, Bool.not_true, Bool.false_eq_true]
  rw [hs0, hnb]
  cases hn : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y with
  | some u =>
    simp only [Mem.objH]
    rw [newest_lv hn]; rfl
  | none =>
    simp only [Mem.objH]
    rw [hri.pos b ob hob (by rw [hnb]; exact hn), hnb]

end Before

/-! ## The positions (question 1) -/

/-- The first record at or after s with a version of y, below a bound. -/
theorem first_version {S : Stream V T} {s : Nat} {y : NodeId} :
    ∀ n f0 w0, f0 < s + n → s ≤ f0 → S.versionAt f0 y = some w0 →
      ∃ f w, s ≤ f ∧ S.versionAt f y = some w ∧ ∀ f', s ≤ f' → f' < f → S.versionAt f' y = none := by
  intro n
  induction n with
  | zero => intro f0 w0 h1 h2; exfalso; omega
  | succ n ih =>
    intro f0 w0 h1 h2 h0
    by_cases hex : ∃ f', s ≤ f' ∧ f' < f0 ∧ (S.versionAt f' y).isSome
    · obtain ⟨f', h3, h4, h5⟩ := hex
      obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp h5
      exact ih f' w' (by omega) h3 hw'
    · refine ⟨f0, w0, h2, h0, fun f' h3 h4 => ?_⟩
      cases hv : S.versionAt f' y with
      | none => rfl
      | some _ => exact absurd ⟨f', h3, h4, by rw [hv]; rfl⟩ hex

section Pos

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- What a pointer of the memory before rule 4 names, by `RInv`: a pointer that
holds no handle and names record r, to node y, names a version of y; Rule R takes
it to y's latest version; no version of y lies between r and the section; and y
is a pointee of its object's history, which is its node's, on its node's level. -/
theorem before_ptr_facts (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) {a : Nat}
    {o : HObj V}
    (ho : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).obj? a = some o)
    {y : NodeId} {p : HPtr} (hmem : (y, p) ∈ o.ptrs) (hh : p.handle = none) {r : Nat}
    (hr : p.ref = some r) :
    (∃ u, (st sp al ts k).S.versionAt r y = some u) ∧
    ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) y (some r) =
      ((st sp al ts k).S.lv y).map (·.recNo) ∧
    NearSec (st sp al ts k).S (lastSp (st sp al ts k).S) y r ∧
    y ∈ pointees sp o.hist ∧
    ∃ n, (st sp al ts k).P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  obtain ⟨o0, ho0, hsl, hn, hl, hh0⟩ := before_ptr hok hph hj hmk hev hk ho hmem hh hr
  obtain ⟨-, ⟨n, hnn, hnh, hnl, -⟩, -⟩ := hm.canon a o0 ho0 (hri.canon a o0 ho0)
  refine ⟨hri.ver a o0 ho0 y r hsl, hri.fresh a o0 ho0 y (some r) hsl, hri.near a o0 ho0 y r hsl,
    by rw [hh0]; exact hri.keys a o0 ho0 y (by rw [hsl]; rfl), n, by rw [hn]; exact hnn, ?_, ?_⟩
  · rw [hh0, hnh]; exact upTo_of_forall _ _ (hinv.times _ n hnn)
  · rw [hl, hnl]

/-- `Rule4_positions`: a pointer of a pinned object that holds no handle, to a node
with a canonical object, names a version of the section, the version before the
pointee's first version there, or the canonical object's own. -/
theorem rule4_positions (sp : Spec V T) (al : Algo V T) : Rule4_positions sp al := by
  intro ts hok hph hev hj hmk k hk
  dsimp only
  rw [show run sp al (ts.take k) = st sp al ts k from rfl]
  intro a o y p r b ho _ _ hmem hh hr hb
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨hver, hfr, hnear, -, -⟩ := before_ptr_facts hok hph hj hmk hev hk ho hmem hh hr
  by_cases hrs : lastSp (st sp al ts k).S ≤ r
  · left
    obtain ⟨u, hu⟩ := hver
    exact ⟨hrs, by rw [hu]; rfl⟩
  · right
    cases hn : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y with
    | some w =>
      left
      refine ⟨rfl, ?_⟩
      obtain ⟨u, hu⟩ := hver
      obtain ⟨-, hur, -⟩ := hinv.version_node hu
      have hl : Stream.lv ((st sp al ts k).S.take (lastSp (st sp al ts k).S)) y = some u := by
        apply (lv_eq_some_iff _ y u).mpr
        refine ⟨r, ?_, fun r' hr' => ?_⟩
        · rw [versionAt_take]; simp [show r < lastSp (st sp al ts k).S by omega, hu]
        · rw [versionAt_take]
          by_cases h' : r' < lastSp (st sp al ts k).S
          · simp only [h', ↓reduceIte]; exact hnear r' hr' h'
          · simp [h']
      rw [hl, Option.map_some, hur]
    | none =>
      right
      rw [(before_canon hok hph hj hmk hev hk hb).1]
      unfold ruleRRef at hfr
      rw [hn] at hfr
      exact hfr.symm

end Pos

/-! ## Rule 4 by position is rule 4 by node id (question 4) -/

/-- Rule 4 by position gives what rule 4 by node id gives on a memory where each
pointer that it would leave unlinked (of a pinned object on a key level, holding
no handle, naming a record) whose node has a canonical object is in `posToId` or
at the canonical object's position. -/
theorem HMem.linkDPos_eq_linkD (sp : Spec V T) (S : Stream V T) (m : HMem V) (D : Dirty)
    (h : ∀ p ∈ m.objs, (p.2.canonical && (inD D p.2.node || p.1 == m.root)) = true →
      isKeyLevel sp p.2.isData p.2.level = true → ∀ q ∈ p.2.ptrs, q.2.handle = none →
      ∀ r, q.2.ref = some r → ∀ b, m.canonicalOf q.1 = some b →
      inPosToId sp S m.s q.1 r = true ∨ (m.obj? b).bind (·.pos) = some r) :
    m.linkDPos sp S D = m.linkD D := by
  unfold HMem.linkDPos HMem.linkD
  congr 1
  apply List.map_congr_left
  intro p hp
  by_cases hpin : (p.2.canonical && (inD D p.2.node || p.1 == m.root)) = true
  · simp only [hpin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    congr 2
    apply List.map_congr_left
    intro q hq
    obtain ⟨y, pt⟩ := q
    cases hh : pt.handle with
    | some n => simp
    | none =>
      cases hr : pt.ref with
      | none => simp
      | some r =>
        simp only
        by_cases hin : inPosToId sp S m.s y r = true
        · simp only [hin, ↓reduceIte]
        · simp only [hin, Bool.false_eq_true, ↓reduceIte]
          cases hbp : m.byPos y r with
          | some n =>
            simp only
            unfold HMem.byPos at hbp
            cases hc : m.canonicalOf y with
            | none => rw [hc] at hbp; cases hbp
            | some b =>
              rw [hc] at hbp
              simp only at hbp
              split at hbp
              · rw [hbp]
              · cases hbp
          | none =>
            simp only
            cases hkl : isKeyLevel sp p.2.isData p.2.level with
            | false => simp
            | true =>
              simp only [↓reduceIte]
              cases hc : m.canonicalOf y with
              | none => rfl
              | some b =>
                exfalso
                rcases h p hp hpin hkl (y, pt) hq hh r hr b hc with h1 | h1
                · exact hin h1
                · unfold HMem.byPos at hbp
                  rw [hc] at hbp
                  simp only [h1, beq_self_eq_true, ↓reduceIte] at hbp
                  unfold HMem.canonicalOf at hc
                  rw [hbp] at hc
                  simp at hc
  · simp [hpin]


/-- A version of y in R(s), ..., that is an index node version, is in `posToId`. -/
theorem inPosToId_of_section {sp : Spec V T} {S : Stream V T} {s : Nat} {y : NodeId} {r : Nat}
    {w : Version V} (hs : s ≤ r) (hw : S.versionAt r y = some w) (hd : w.isData = false) :
    inPosToId sp S s y r = true := by
  unfold inPosToId
  apply List.any_eq_true.mpr
  have hlt : r < S.length := by
    obtain ⟨R, hR, -, -⟩ := versionAt_spec hw
    exact (List.getElem?_eq_some_iff.mp hR).1
  refine ⟨r, List.mem_range'_1.mpr ⟨hs, by omega⟩, ?_⟩
  rw [hw]
  simp [hd]

/-- The version before a key node version of y in R(s), ..., is in `posToId`. -/
theorem inPosToId_of_prev {sp : Spec V T} {S : Stream V T} {s : Nat} {y : NodeId} {f r : Nat}
    {w : Version V} (hs : s ≤ f) (hw : S.versionAt f y = some w)
    (hk : isKeyLevel sp w.isData w.level = true)
    (hp : (Stream.lv (S.take f) y).map (·.recNo) = some r) :
    inPosToId sp S s y r = true := by
  unfold inPosToId
  apply List.any_eq_true.mpr
  have hlt : f < S.length := by
    obtain ⟨R, hR, -, -⟩ := versionAt_spec hw
    exact (List.getElem?_eq_some_iff.mp hR).1
  refine ⟨f, List.mem_range'_1.mpr ⟨hs, by omega⟩, ?_⟩
  rw [hw]
  have hd : w.isData = false := by
    unfold isKeyLevel at hk
    cases hd : w.isData
    · rfl
    · rw [hd] at hk; simp at hk
  rw [hd] at hk
  simp [hd, hk, hp]

section Eq

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- `Rule4Pos_handles`: on the states that the startup reaches, rule 4 by position
links what rule 4 by node id links. -/
theorem rule4Pos_handles (sp : Spec V T) (al : Algo V T) : Rule4Pos_handles sp al := by
  intro ts hok hph hev hj hmk k hk
  rw [show run sp al (ts.take k) = st sp al ts k from rfl]
  unfold handleStartupPos handleStartup
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hdo := dataOnce_st sp al ts hok hst k hk
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hs0 : (lazyStartup sp (st sp al ts k).S).s = lastSp (st sp al ts k).S := hm.sEq
  have hnd : ((((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs.map
      (·.1)).Nodup := by
    rw [Mem.toH_objs, List.map_map]
    have h1 : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).objs.map (·.1)).Nodup := by
      rw [Mem.sectionPos_keys]; exact hm.nodup
    exact (List.Sublist.map _ List.filter_sublist).nodup h1
  apply HMem.linkDPos_eq_linkD
  intro p hp _ hkl q hq hh r hr b hb
  obtain ⟨y, pt⟩ := q
  simp only at hh hr hb ⊢
  have hobj := lookup_of_mem _ hnd p hp
  obtain ⟨hver, hfr, hnear, hpt, n, hn, hnh, hnl⟩ := before_ptr_facts hok hph hj hmk hev hk hobj hq hh hr
  obtain ⟨hpos, -⟩ := before_canon hok hph hj hmk hev hk hb
  obtain ⟨u, hu⟩ := hver
  obtain ⟨-, hur, ny, hny, -, hnyl, hnyd⟩ := hinv.version_node hu
  -- The pointer's version, if y is a data node, is y's only one, its canonical object's.
  have hdata : u.isData = true → (((((lazyStartup sp (st sp al ts k).S).sectionPos
      (st sp al ts k).S).toH).obj? b).bind (·.pos)) = some r := by
    intro hud
    rw [hpos, hdo y ny r u hny (by rw [← hnyd]; exact hud) hu, Option.map_some, hur]
  have hs1 : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).s =
      lastSp (st sp al ts k).S := hs0
  rw [hs1]
  by_cases hrs : lastSp (st sp al ts k).S ≤ r
  · -- a version of the section
    cases hud : u.isData
    · exact Or.inl (inPosToId_of_section hrs hu hud)
    · exact Or.inr (hdata hud)
  · cases hnw : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y with
    | none =>
      -- no version in the section: the pointer names y's latest version, its canonical object's
      right
      rw [hpos]
      unfold ruleRRef at hfr
      rw [hnw] at hfr
      exact hfr.symm
    | some wn =>
      -- the version before y's first version in the section
      left
      obtain ⟨f0, hf0, hwf0⟩ := newest_some hnw
      obtain ⟨f, w, hsf, hwf, hmin⟩ := first_version (f0 + 1) f0 wn (by omega) hf0 hwf0
      obtain ⟨-, hwr, nw, hnw', -, hnwl, hnwd⟩ := hinv.version_node hwf
      rw [hny, Option.some.injEq] at hnw'
      subst hnw'
      have hfr' : r < f := by omega
      apply inPosToId_of_prev hsf hwf
      · -- w is a key node version: y is below p's node, which is on a key level (A4)
        have hwd : w.isData = false := by
          cases hwd : w.isData
          · rfl
          · exfalso
            have h1 := hdo y ny f w hny (by rw [← hnwd]; exact hwd) hwf
            have h2 := hdo y ny r u hny (by rw [← hnwd]; exact hwd) hu
            rw [h1, Option.some.injEq] at h2
            subst h2
            omega
        unfold isKeyLevel at hkl ⊢
        rw [hwd]
        simp only [Bool.not_false, Bool.true_and]
        cases hv : sp.virt
        · rfl
        · rw [hv] at hkl
          simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hkl
          simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
          have hyp : y ∈ pointees sp n.hist := by rw [← hnh]; exact hpt
          obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hyp
          obtain ⟨my, hmy, hlt⟩ := hinv.ptrs p.2.node n hn e he y hye
          rw [hny, Option.some.injEq] at hmy
          subst hmy
          rw [hnwl]
          omega
      · -- y's latest version before f is the pointer's
        have hl : Stream.lv ((st sp al ts k).S.take f) y = some u := by
          apply (lv_eq_some_iff _ y u).mpr
          refine ⟨r, ?_, fun r' hr' => ?_⟩
          · rw [versionAt_take]; simp [hfr', hu]
          · rw [versionAt_take]
            by_cases h' : r' < f
            · simp only [h', ↓reduceIte]
              by_cases h'' : r' < lastSp (st sp al ts k).S
              · exact hnear r' hr' h''
              · exact hmin r' (by omega) h'
            · simp [h']
        rw [hl, Option.map_some, hur]

end Eq

/-! ## Runs with rule 4 by position -/

/-- `runHandlesPos` is `runHandles` but for its startups: with the same startup
it would be the same run. -/
theorem runHandlesPos_of_startup (sp : Spec V T) (al : Algo V T)
    (h : ∀ S : Stream V T, handleStartupPos sp S = handleStartup sp S)
    (ts : List (T × Bool × List HCacheOp)) : runHandlesPos sp al ts = runHandles sp al ts := by
  simp only [runHandlesPos, runHandles, h]

theorem runHandlesPos_succ (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp))
    {j : Nat} (hj : j < ts.length) :
    runHandlesPos sp al (ts.take (j + 1)) =
      (if ts[j].2.1 then
        (startup sp (handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2
            (runHandlesPos sp al (ts.take j)).1 (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).1.S,
          handleStartupPos sp (handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2
            (runHandlesPos sp al (ts.take j)).1 (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).1.S,
          (handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2 (runHandlesPos sp al (ts.take j)).1
            (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).1.S)
      else
        ((handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2 (runHandlesPos sp al (ts.take j)).1
            (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).1,
          ts[j].2.2.foldl (HMem.cacheOp sp (runHandlesPos sp al (ts.take j)).2.2
            (handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2 (runHandlesPos sp al (ts.take j)).1
              (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).1.S
            (handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2 (runHandlesPos sp al (ts.take j)).1
              (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).1.D)
            (handleTrans sp al (runHandlesPos sp al (ts.take j)).2.2 (runHandlesPos sp al (ts.take j)).1
              (runHandlesPos sp al (ts.take j)).2.1 ts[j].1).2,
          (runHandlesPos sp al (ts.take j)).2.2)) := by
  have h1 : ts.take (j + 1) = ts.take j ++ [ts[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runHandlesPos
  rw [h1, List.foldl_append]
  rfl

/-- `RunPos_handles`: every startup of a run is from the run's stream (T2-C), where
rule 4 by position is rule 4 by node id. -/
theorem runPos_handles (sp : Spec V T) (al : Algo V T) : RunPos_handles sp al := by
  intro ts hok hph hev hj hmk j
  induction j with
  | zero =>
    intro _
    have h0 := rule4Pos_handles sp al (ts.map (·.1)) hok hph hev hj hmk 0 (Nat.zero_le _)
    simp only [List.take_zero] at h0
    simp only [List.take_zero, runHandlesPos, runHandles, List.foldl_nil]
    rw [show (init sp : DB V T) = run sp al [] from rfl, h0]
  | succ j ih =>
    intro hjt
    rw [runHandlesPos_succ sp al ts (by omega), runHandles_succ sp al ts (by omega), ih (by omega)]
    split
    · rename_i hrs
      obtain ⟨hS, -⟩ := t2_handles sp al ts hok hph hev hj hmk (j + 1) hjt
      rw [runHandles_succ sp al ts (by omega)] at hS
      simp only [hrs, ↓reduceIte] at hS
      have hS' : (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
          (runHandles sp al (ts.take j)).2.1 ts[j].1).1.S = (run sp al ((ts.map (·.1)).take (j + 1))).S := by
        rw [← List.map_take]; exact hS
      rw [hS', rule4Pos_handles sp al (ts.map (·.1)) hok hph hev hj hmk (j + 1) (by simp; omega)]
    · rfl

end SIS
