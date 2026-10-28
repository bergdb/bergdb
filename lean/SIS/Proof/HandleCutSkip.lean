/-
Proofs about rule 4 by position after a cut (bergdb 005-62, question 2), part 1:
the pointers that Java skips. Java's rule 4 leaves a stream pointer below the
stream's first position as it is (`HMem.linkDPosFrom`); rule 4 by node id links
it if its node has a canonical object. On the memory of the startup from the
stream S after T(k), with a safe cut at c, no stream slot of the object of a node
of D names a record below c and a node with a canonical object (`cutSkip_lazy`).

The rerun of the startup is followed with an invariant against the cut
(`CutInv`), at each time K of the rerun: every object is the root's or of a node
whose latest version is at c or later (`node`; a node the rerun reaches is
reachable from the first available time on, and `CutOK` puts its latest version
at c or later); a stream slot below c that is live, of a node reachable at K,
names a node without a version in the section (`live`); and a stream slot below
c of the object of a node of D names such a node, or a node that is not
reachable from K on and has no canonical object (`dslot`). A version that the
rerun reads, of a node reachable then, names its live children at versions that
`ReadsPhys` covers (`CutOK`, part 2), or is the latest version of a node of D,
whose references below c name latest versions (part 3). A new pointer copies its
slot from an object of a node that has its pointee as a live child then (`live`),
or, when there is none, its pointee is not reachable from then on or has no
version in the section: a node that is reachable then has a current parent,
which has a canonical object or is clean and names the pointee's latest version,
which `ReadsPhys` covers (`stale_absurd`). Without a version in the section, Rule
R leaves a slot's reference, which is then its node's latest version, below c,
and no object of such a node is canonical (`node`).
-/
import SIS.Proof.HandleCutT12

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- The invariant of the rerun's memory m at time K against a cut at c, for the
startup from the stream of state db (the state after T(k)). -/
structure CutInv (sp : Spec V T) (db : DB V T) (k c K : Nat) (m : Mem V) : Prop where
  /-- Every object is the root's, or of a node whose latest version is at c or later. -/
  node : ∀ h o, m.obj? h = some o → o.node = root ∨ ∀ v, db.S.lv o.node = some v → c ≤ v.recNo
  /-- A live stream slot below c, of an object of a node reachable at K, names a node
  without a version in the section. -/
  live : ∀ h o, m.obj? h = some o → reachable sp db.P K o.node = true → ∀ y ∈ sp.live (o.hist.upTo K),
    ∀ r, o.slot? y = some (Slot.stream (some r)) → r < c → newest db.S (lastSp db.S) y = none
  /-- A stream slot below c of the object of a node of D names a node without a
  version in the section, or a node that is not reachable from K on and has no
  canonical object. -/
  dslot : ∀ h o, m.obj? h = some o → inD db.D o.node = true → ∀ y r,
    o.slot? y = some (Slot.stream (some r)) → r < c →
    newest db.S (lastSp db.S) y = none ∨
      ((∀ t, K ≤ t → t ≤ k → reachable sp db.P t y = false) ∧ m.canonicalOf y = none)

/-- A reference below the section that Rule R leaves names a node without a
version in the section. -/
theorem newest_none_of_fix {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {s : Nat}
    {y : NodeId} {r : Nat} (hfix : ruleRRef db.S s y (some r) = some r) (hrs : r < s) :
    newest db.S s y = none := by
  cases hn : newest db.S s y with
  | none => rfl
  | some w =>
    exfalso
    obtain ⟨r0, hr0, hw0⟩ := newest_some hn
    obtain ⟨-, hrec, -⟩ := hinv.version_node hw0
    unfold ruleRRef at hfix
    rw [hn] at hfix
    simp only at hfix
    split at hfix
    · simp only [Option.some.injEq] at hfix; omega
    · omega

/-! ## The memory before the rerun -/

section Base

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The memory before the rerun meets the invariant: its objects are of the
section's nodes and the root, and its stream slots are Rule R's of a reference,
which Rule R leaves, so below the section they name nodes without a version in it. -/
theorem cutInv_lazyBase (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {k c : Nat}
    (hk : k ≤ ts.length) (hcut : CutOK sp c (st sp al ts k) k) :
    CutInv sp (st sp al ts k) k c (lastSp (st sp al ts k).S) (lazyBase sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hb := hinv.base2 (sp := sp)
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 (st_fa_le sp al ts hk)
  have hfix2 : ∀ h o2, (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).obj? h = some o2 →
      ∀ y r, o2.slot? y = some (Slot.stream r) →
      ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) y r = r := by
    intro h o2 ho2 y r hsl
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    have hcv : ∀ w : Version V, (canonOfVersion sp (st sp al ts k).S (lastSp (st sp al ts k).S) w).slot? y =
        some (Slot.stream r) → ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) y r = r := by
      intro w hs
      have := canonOfVersion_slot_eq hs
      simp only [Slot.stream.injEq] at this
      rw [this, ruleRRef_idem]
    rcases hsrc with ⟨w, -, -, -, hoe, -⟩ | ⟨-, hoe⟩ | ⟨-, u, -, -, -, hoe⟩
    · subst hoe; exact hcv w hsl
    · subst hoe; exact hcv _ hsl
    · subst hoe; exact hcv u hsl
  have hstr : ∀ h o, (lazyBase sp (st sp al ts k).S).obj? h = some o → ∀ y r,
      o.slot? y = some (Slot.stream (some r)) → r < c →
      newest (st sp al ts k).S (lastSp (st sp al ts k).S) y = none := by
    intro h o ho y r hsl hrc
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2] at hsl
    obtain ⟨sl2, hsl2, hq⟩ := Option.map_eq_some_iff.mp hsl
    rcases linkQ_cases (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)) y sl2 with
      he | ⟨h0, o0, -, -, -, he⟩
    · rw [he] at hq
      subst hq
      exact newest_none_of_fix hinv (hfix2 h o2 ho2 y _ hsl2) (by omega)
    · rw [he] at hq; cases hq
  refine ⟨fun h o ho => ?_, fun h o ho _ y _ r hsl hrc => hstr h o ho y r hsl hrc,
    fun h o ho _ y r hsl hrc => Or.inl (hstr h o ho y r hsl hrc)⟩
  unfold lazyBase at ho
  rw [linkCanonical_obj?] at ho
  obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
  rw [(linkObj_fields _ o2).1]
  obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
  rcases hsrc with ⟨w, r, hw, hrs, -, -⟩ | ⟨-, hoe⟩ | ⟨-, u, hu, -, -, hoe⟩
  · right
    intro v hv
    obtain ⟨v', hv', hle⟩ := hinv.le_lv hw
    rw [hv, Option.some.injEq] at hv'
    subst hv'
    omega
  · left; subst hoe; rfl
  · left
    subst hoe
    rw [(canonOfVersion_fields sp _ _ u).1]
    obtain ⟨R, -, -, hun⟩ := versionAt_spec (hinv.lv_at hu)
    exact hun

end Base

/-! ## Facts of the run -/

section Facts

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- No resurrection, over several transactions: a node of the structure after
T(K) that is reachable at a later time was reachable at K. -/
theorem reach_back (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {k K : Nat}
    (hk : k ≤ ts.length) {y : NodeId} (hy : ((st sp al ts K).P.get? y).isSome) :
    ∀ t, K ≤ t → t ≤ k → reachable sp (st sp al ts k).P t y = true →
      reachable sp (st sp al ts k).P K y = true := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  intro t
  induction t with
  | zero => intro h0 _ hr; rw [show K = 0 by omega]; exact hr
  | succ t ih =>
    intro hKt htk hr
    by_cases hK : K = t + 1
    · rw [hK]; exact hr
    · have hKt' : K ≤ t := by omega
      apply ih hKt' (by omega)
      -- one transaction back
      have hk1 := kctx_st sp al ts hok hj (K := t + 1) htk hk
      have hkt := kctx_st sp al ts hok hj (K := t) (by omega) hk
      have hr1 : reachable sp (st sp al ts (t + 1)).P (t + 1) y = true := by
        rw [← hk1.reachable_eq hls (Nat.le_refl _)]; exact hr
      have htl : t < ts.length := by omega
      rw [st_P_succ sp al ts hok hst htl] at hr1
      have hstep := hok.2 t htl
      simp only at hstep
      rcases hstep.noRes y hr1 with h | h
      · rw [hkt.reachable_eq hls (Nat.le_refl _)]
        rw [show t + 1 - 1 = t by omega] at h
        exact h
      · exfalso
        obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp h
        have hfr := hstep.fresh nn hnn
        obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hy
        have hgr := (kctx_st sp al ts hok hj (K := K) hKt' (by omega)).grow nn.id n0 hn0
        obtain ⟨n', hn', -⟩ := hgr
        rw [show (run sp al (ts.take t)).P = (st sp al ts t).P from rfl, hn'] at hfr
        cases hfr

/-- A reference of a version names a record at or before the version's. -/
theorem Inv.ref_le_recNo {db : DB V T} {k : Nat} (hinv : Inv sp db k) {r : Nat} {y : NodeId}
    {v : Version V} (hv : db.S.versionAt r y = some v) {z : NodeId} {r0 : Nat}
    (hz : v.ref? z = some r0) : r0 ≤ r := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR v hvR
  rw [href z] at hz
  split at hz
  · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hz
    unfold Stream.building at hu
    rw [lv_append] at hu
    cases h1 : Stream.lv [{ trans := none, sp := 0, vers := pre, gd := [], top := none : Record V T }] z with
    | some u1 =>
      rw [h1] at hu
      simp only [Option.some_or, Option.some.injEq] at hu
      subst hu
      obtain ⟨i, hi⟩ := lv_versionAt h1
      obtain ⟨R1, hR1, hu1, -⟩ := versionAt_spec hi
      have hi0 : i = 0 := by
        have := (List.getElem?_eq_some_iff.mp hR1).1
        simp at this; omega
      subst hi0
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hR1
      subst hR1
      exact Nat.le_of_eq (hinv.recNo r R hR u1 (hpre.subset hu1))
    | none =>
      rw [h1] at hu
      simp only [Option.none_or] at hu
      obtain ⟨i, hi⟩ := lv_versionAt hu
      have hit : i < r := by
        obtain ⟨R1, hR1, -, -⟩ := versionAt_spec hi
        have := (List.getElem?_eq_some_iff.mp hR1).1
        simp at this; omega
      rw [versionAt_take] at hi
      simp only [hit, ↓reduceIte] at hi
      obtain ⟨-, hrec, -⟩ := hinv.version_node hi
      omega
  · cases hz

/-- A slot below c of the rerun's memory at K, for a node y with a version in the
section, cannot be a copy for a pointer whose pointee is reachable at K with a
current parent q0 without a canonical object: q0 would be clean, without a
version in the section, and its latest version would name y's latest version at
K, which `ReadsPhys` covers; that version is the slot's (no version of y lies
between the slot's and the section, and none of the section is before K). -/
theorem stale_absurd (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {k K c : Nat} (hk : k ≤ ts.length) (hKk : K < k)
    (hsK : lastSp (st sp al ts k).S ≤ K) (hcut : CutOK sp c (st sp al ts k) k) {m : Mem V}
    (hr : RInv sp (st sp al ts k).S m) (hm : MemInv sp (st sp al ts k) K m)
    {y : NodeId} {r : Nat} (hrc : r < c)
    {h : Nat} {o : Obj V} (ho : m.obj? h = some o) (hsl : o.slot? y = some (Slot.stream (some r)))
    {q0 : NodeId} {nq : Node V} (hrq : reachable sp (st sp al ts K).P K q0 = true)
    (hnq : (st sp al ts K).P.get? q0 = some nq) (hyl : y ∈ sp.live (nq.hist.upTo K))
    (hcq : m.canonicalOf q0 = none) : False := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have hfs := st_fa_le sp al ts hk
  have hc1 := hcut.1
  obtain ⟨e, he, hye⟩ := hls _ _ hyl
  have heK := (mem_upTo.mp he)
  obtain ⟨n', hn', -, hnd', hup'⟩ := hkK.grow q0 nq hnq
  have hnqK : nq.hist.upTo K = nq.hist := upTo_of_forall _ _ (hinvK.times q0 nq hnq)
  have hen' : e ∈ n'.hist := by
    have : e ∈ n'.hist.upTo K := by rw [hup', hnqK]; exact heK.1
    exact (mem_upTo.mp this).1
  -- q0 has no version in the section.
  have hnq0 : newest (st sp al ts k).S (lastSp (st sp al ts k).S) q0 = none := by
    cases hn : newest (st sp al ts k).S (lastSp (st sp al ts k).S) q0 with
    | none => rfl
    | some wq =>
      exfalso
      by_cases hes : lastSp (st sp al ts k).S < e.time
      · exact hm.coverNew q0 n' e hn' hen' hes heK.2 hcq
      · obtain ⟨rq, hrq', hwq⟩ := newest_some hn
        obtain ⟨-, hwqr, nw, hnw, hwqh, -, hwqd⟩ := hinvk.version_node hwq
        rw [hn', Option.some.injEq] at hnw
        subst hnw
        have hwd : wq.isData = false := by
          rw [hwqd]
          cases hd : n'.isData
          · rfl
          · exfalso
            have := hinvk.data q0 n' hn' hd e hen'
            rw [this] at hye; cases hye
        apply hm.coverSec q0 wq hn hwd _ hcq
        rw [hwqh, upTo_upTo _ hrq']
        intro hemp
        have : e ∈ n'.hist.upTo (lastSp (st sp al ts k).S) := mem_upTo.mpr ⟨hen', by omega⟩
        rw [hemp] at this; cases this
  -- q0 is not in D at K.
  have hq0D : inD (st sp al ts K).D q0 = false := by
    cases hd : inD (st sp al ts K).D q0 with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hd
      obtain ⟨hsd, R, hR, hxR, hdK⟩ := notD_of_newest_none hok hj (Nat.le_of_lt hKk) hk hsK hnq0 hd'
      exact hm.coverGd d R q0 hsd hdK hR hxR hcq
  -- q0 is written: a virtual root has a canonical object.
  have hq0w : written sp q0 = true := by
    cases hv : sp.virt
    · simp [written, hv]
    · by_cases hq : q0 = root
      · exfalso
        subst hq
        obtain ⟨hrt, o0, ho0, hc0, -⟩ := hm.root
        have := (m.canonicalOf_eq_some root m.root).mpr ⟨hrt, o0, ho0, hc0⟩
        rw [hcq] at this; cases this
      · simp [written, hq]
  -- q0's latest version, clean at K, names y's latest version at K.
  obtain ⟨v, hvK, hvh, -, -⟩ := hinvK.lv_whole hnq hq0w hq0D hrq
  have hnone := (newest_eq_none_iff _ _ q0).mp hnq0
  have hv : (st sp al ts k).S.lv q0 = some v := by
    rw [st_S_take hok hst (Nat.le_of_lt hKk) hk, lv_take (fun r' hr' => hnone r' (by omega))] at hvK
    exact hvK
  have hyp : y ∈ pointees sp v.hist := by
    rw [hvh, ← hnqK]; exact mem_pointees_of_liveH hls hyl
  have href := clean_ref_lvAt hok hj hmk hev (Nat.le_of_lt hKk) hk hsK hnq0 hrq hq0D hq0w hv y hyp
  -- y's version at r, and its latest version at K.
  obtain ⟨u, hu⟩ := hr.ver h o ho y r hsl
  obtain ⟨-, hur, -⟩ := hinvk.version_node hu
  have huK : (st sp al ts K).S.versionAt r y = some u := by
    rw [st_S_take hok hst (Nat.le_of_lt hKk) hk, versionAt_take]
    simp only [show r < K + 1 by omega, ↓reduceIte]; exact hu
  obtain ⟨uK, huK', hle⟩ := hinvK.le_lv huK
  rw [huK', Option.map_some] at href
  have huKa := hinvK.lv_at huK'
  have huKS : (st sp al ts k).S.versionAt uK.recNo y = some uK := by
    rw [st_S_take hok hst (Nat.le_of_lt hKk) hk, versionAt_take] at huKa
    split at huKa
    · exact huKa
    · cases huKa
  -- ReadsPhys covers y's versions from v's reference on.
  have hvw := hinvk.lv_at hv
  have hvs : v.recNo < lastSp (st sp al ts k).S := by
    by_cases h' : lastSp (st sp al ts k).S ≤ v.recNo
    · exact absurd (hnone v.recNo h') (by rw [hvw]; simp)
    · omega
  have hrqk : reachable sp (st sp al ts k).P K q0 = true := by
    rw [hkK.reachable_eq hls (Nat.le_refl K)]; exact hrq
  have hvD : (q0, v.recNo) ∉ (st sp al ts k).D := by
    intro hd
    obtain ⟨hsd, -⟩ := notD_of_newest_none hok hj (Nat.le_refl k) hk (by have := hinvk.spLt; omega) hnq0 hd
    omega
  have hyl' : y ∈ sp.live (v.hist.upTo K) := by rw [hvh, hnqK]; rw [← hnqK]; exact hyl
  have hRP : ReadsPhys sp (st sp al ts k).S (st sp al ts k).P (st sp al ts k).D K uK :=
    ReadsPhys.child v y uK (ReadsPhys.latest q0 v hrqk hv) hyl'
      (Or.inr ⟨by rw [versionAt_node hvw]; exact hvD, uK.recNo, huKS, fun r0 h0 => by
        rw [href, Option.some.injEq] at h0; omega⟩)
  have hcu := hcut.2.1 K uK (by omega) (Nat.le_of_lt hKk) hRP
  -- uK is before the section, so it is the slot's version.
  have huKs : uK.recNo < lastSp (st sp al ts k).S := by
    have := hinvk.ref_le_recNo hvw href
    omega
  have hnear := hr.near h o ho y r hsl
  by_cases hlt : r < uK.recNo
  · have := hnear uK.recNo hlt huKs
    rw [huKS] at this; cases this
  · omega

/-- The history of an object of the rerun's memory at K, canonical, is its node's
in the state after T(K). -/
theorem MemInv.hist_K {db : DB V T} {K : Nat} {m : Mem V} (hm : MemInv sp db K m) {dbK : DB V T}
    (hkK : KCtx sp db dbK K) (hinvK : Inv sp dbK K) {h : Nat} {o : Obj V} (ho : m.obj? h = some o)
    (hc : o.canonical = true) {nK : Node V} (hnK : dbK.P.get? o.node = some nK) : o.hist = nK.hist := by
  obtain ⟨-, ⟨n, hn, hoh, -, -⟩, -⟩ := hm.canon h o ho hc
  obtain ⟨n', hn', -, -, hup⟩ := hkK.grow o.node nK hnK
  rw [hn, Option.some.injEq] at hn'
  subst hn'
  rw [hoh, hup, upTo_of_forall _ _ (hinvK.times _ nK hnK)]

end Facts

/-! ## The writer's walk of the rerun -/

section Walk

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A version that the rerun reads for a node reachable at K: its latest. Its
reference below c to a live child at K names a node without a version in the
section: `ReadsPhys` covers every version of the child from the reference on
(`CutOK`, part 2), unless the node is in D with that version's record, whose
references below c name latest versions (part 3). -/
theorem cut_ref_live (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {k K c : Nat}
    (hk : k ≤ ts.length) (hKk : K ≤ k) (hsK : lastSp (st sp al ts k).S ≤ K)
    (hcut : CutOK sp c (st sp al ts k) k) {x : NodeId} {w : Version V}
    (hrx : reachable sp (st sp al ts k).P K x = true) (hlv : (st sp al ts k).S.lv x = some w)
    {z : NodeId} (hz : z ∈ sp.live (w.hist.upTo K)) {r : Nat} (hzr : w.ref? z = some r) (hrc : r < c) :
    newest (st sp al ts k).S (lastSp (st sp al ts k).S) z = none := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvk := inv_st sp al ts hok hst k hk
  have hw := hinvk.lv_at hlv
  obtain ⟨u, hu⟩ := hinvk.ref_versionAt hw hzr
  obtain ⟨-, hur, -⟩ := hinvk.version_node hu
  have hfs := st_fa_le sp al ts hk
  have hc1 := hcut.1
  cases hnz : newest (st sp al ts k).S (lastSp (st sp al ts k).S) z with
  | none => rfl
  | some wz =>
    exfalso
    obtain ⟨rz, hrz, hwz⟩ := newest_some hnz
    obtain ⟨-, hwzr, -⟩ := hinvk.version_node hwz
    by_cases hxD : (x, w.recNo) ∈ (st sp al ts k).D
    · -- x is in D: its latest version's references below c name latest versions
      have hxD' : inD (st sp al ts k).D x = true := (inD_iff _ _).mpr ⟨w.recNo, hxD⟩
      have h3 := (hcut.2.2.1 x hxD' w hlv).2 z r hzr hrc
      rw [newest_lv hnz, Option.map_some, Option.some.injEq] at h3
      omega
    · have hR : ReadsPhys sp (st sp al ts k).S (st sp al ts k).P (st sp al ts k).D K u :=
        ReadsPhys.child w z u (ReadsPhys.latest x w hrx hlv) hz
          (Or.inr ⟨by rw [versionAt_node hw]; exact hxD, r, hu, fun r0 h0 => by
            rw [hzr, Option.some.injEq] at h0; omega⟩)
      have := hcut.2.1 K u (by omega) hKk hR
      omega

/-- The writer's walk of the rerun keeps the invariant: a node it loads is
reachable at K, so its latest version is at c or later; the loaded object's slots
are its version's references (`cut_ref_live`; for a node of D, `CutOK`, part 3); the
parent's slot becomes a memory slot; no other node gets a canonical object. -/
theorem CutInv.reachOnPath (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    {k K c : Nat} (hk : k ≤ ts.length) (hKk : K < k) (hsK : lastSp (st sp al ts k).S ≤ K)
    (hcut : CutOK sp c (st sp al ts k) k) {m : Mem V} (hci : CutInv sp (st sp al ts k) k c K m)
    (hr : RInv sp (st sp al ts k).S m) (hm : MemInv sp (st sp al ts k) K m) {P : Struct V}
    (hP : SameNodes P (st sp al ts K).P)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp (st sp al ts k).P K p = true) (x : NodeId) :
    CutInv sp (st sp al ts k) k c K (m.reachOnPath sp (st sp al ts k).S P (K + 1) path x) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have hfs := st_fa_le sp al ts hk
  have hc1 := hcut.1
  unfold Mem.reachOnPath
  cases hcx : m.canonicalOf x with
  | some _ => exact hci
  | none =>
    simp only
    have hK1 : K + 1 - 1 = K := by omega
    cases hf : path.find? (fun p => match P.get? p, m.canonicalOf p with
        | some n, some _ => (sp.live (n.hist.upTo (K + 1 - 1))).contains x
        | _, _ => false) with
    | none => exact hci
    | some p =>
      simp only
      have hpp := List.find?_some hf
      have hpm := List.mem_of_find?_eq_some hf
      cases hnp : P.get? p with
      | none => rw [hnp] at hpp; simp at hpp
      | some np =>
        cases hcp : m.canonicalOf p with
        | none => rw [hnp, hcp] at hpp; simp at hpp
        | some hp =>
          simp only
          rw [hnp, hcp] at hpp
          simp only [hK1, List.contains_iff_mem] at hpp
          have hnpK : (st sp al ts K).P.get? p = some np := by rw [← hP]; exact hnp
          have hrpK : reachable sp (st sp al ts K).P K p = true := by
            rw [← hkK.reachable_eq hls (Nat.le_refl K)]; exact hpath p hpm
          obtain ⟨hrx, hxr, -⟩ := hinvK.reach_child hls hnpK hrpK hpp
          have hrxk : reachable sp (st sp al ts k).P K x = true := by
            rw [hkK.reachable_eq hls (Nat.le_refl K)]; exact hrx
          obtain ⟨ht0, op, hop, hco⟩ := (m.canonicalOf_eq_some p hp).mp hcp
          cases hsl : op.slot? x with
          | none =>
            unfold Mem.follow
            simp only [hop, hsl, Option.bind_some]
            exact hci
          | some sl =>
            cases sl with
            | mem h =>
              cases ho : m.obj? h with
              | none =>
                unfold Mem.follow
                simp only [hop, hsl, Option.bind_some, ho]
                exact hci
              | some o =>
                rw [follow_mem_eval_w sp _ m hop hsl ho, hr.canon h o ho]
                exact hci
            | stream r =>
              have htx : m.tableOf x = none := by
                cases htx : m.tableOf x with
                | none => rfl
                | some h0 =>
                  exfalso
                  obtain ⟨o0, ho0, -⟩ := hm.tbl x h0 htx
                  have := (m.canonicalOf_eq_some x h0).mpr ⟨htx, o0, ho0, hr.canon h0 o0 ho0⟩
                  rw [hcx] at this; cases this
              have hrr : ruleRRef (st sp al ts k).S m.s x r = ((st sp al ts k).S.lv x).map (·.recNo) := by
                rw [hm.sEq]; exact hr.fresh hp op hop x r hsl
              cases hlv : (st sp al ts k).S.lv x with
              | none =>
                rw [hlv] at hrr
                unfold Mem.follow
                simp only [hop, hsl, Option.bind_some, htx, hrr, Option.map_none]
                exact hci
              | some w =>
                rw [hlv] at hrr
                simp only [Option.map_some] at hrr
                have hw := hinvk.lv_at hlv
                obtain ⟨hwx, -, -⟩ := hinvk.version_node hw
                let cut := if m.s ≤ w.recNo && isKeyLevel sp w.isData w.level then some m.s else none
                have hpn : hp ≠ m.next := by
                  intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
                have hreg : (m.addObj (Obj.ofVersion sp w cut)).1.register m.next =
                    ((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next, m.next) := by
                  have h1 : (m.addObj (Obj.ofVersion sp w cut)).1.obj? m.next = some (Obj.ofVersion sp w cut) := by
                    rw [Mem.obj?_addObj]; simp
                  have h2 := register_none _ h1 (by
                    rw [(Obj.ofVersion_fields sp w cut).1, hwx, Mem.tableOf_addObj]; exact htx)
                  rw [(Obj.ofVersion_fields sp w cut).1, hwx] at h2
                  exact h2
                have hop1 : ((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).obj? hp = some op := by
                  rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop
                have ho1 : ((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).obj? m.next =
                    some (Obj.ofVersion sp w cut) := by
                  rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp
                rw [follow_load_eval_w sp _ m hop hsl (fun h0 o0 ht _ => by rw [htx] at ht; cases ht) hrr hw
                  hreg hop1 (Ne.symm hpn) ho1]
                rw [(Obj.ofVersion_fields sp w cut).2.2.2.2.1]
                simp only [Bool.false_eq_true, ↓reduceIte]
                have hmc := makeCanonical_eval (((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).setObj hp
                  (op.setSlot x (Slot.mem m.next))) (h := m.next) (y := x) (hp := hp)
                  (o1 := Obj.ofVersion sp w cut) (op := op.setSlot x (Slot.mem m.next))
                  (by rw [Mem.tableOf_setObj, Mem.tableOf_setTable]; simp)
                  (by rw [Mem.obj?_setObj]; simp only [Ne.symm hpn, ↓reduceIte]; exact ho1)
                  (by rw [Mem.obj?_setObj]; simp) hpn
                rw [hmc, Obj.setSlot_twice]
                generalize hM : (((((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).setObj hp
                    (op.setSlot x (Slot.mem m.next))).setObj m.next { Obj.ofVersion sp w cut with canonical := true }).setTable
                      x m.next).setObj hp (op.setSlot x (Slot.mem m.next)) = M
                have hobj : ∀ h', M.obj? h' =
                    if h' = hp then some (op.setSlot x (Slot.mem m.next)) else
                      if h' = m.next then some { Obj.ofVersion sp w cut with canonical := true } else m.obj? h' := by
                  intro h'
                  rw [← hM, Mem.obj?_setObj, Mem.obj?_setTable, Mem.obj?_setObj, Mem.obj?_setObj, Mem.obj?_setTable,
                    Mem.obj?_addObj]
                  by_cases h1 : h' = hp
                  · simp [h1]
                  · by_cases h2 : h' = m.next
                    · simp [h2]
                    · simp [h1, h2]
                have htbl : ∀ z, z ≠ x → M.tableOf z = m.tableOf z := by
                  intro z hzx
                  rw [← hM, Mem.tableOf_setObj, Mem.tableOf_setTable, Mem.tableOf_setObj, Mem.tableOf_setObj,
                    Mem.tableOf_setTable, Mem.tableOf_addObj]
                  simp [hzx]
                -- No node but x changes its canonical object.
                have hcan : ∀ z, z ≠ x → M.canonicalOf z = m.canonicalOf z := by
                  intro z hzx
                  unfold Mem.canonicalOf
                  rw [htbl z hzx]
                  cases ht : m.tableOf z with
                  | none => rfl
                  | some h0 =>
                    simp only
                    obtain ⟨o0, ho0, -⟩ := hm.tbl z h0 ht
                    have h0n : h0 ≠ m.next := by
                      intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at ho0; cases ho0
                    rw [hobj]
                    by_cases h0p : h0 = hp
                    · subst h0p
                      rw [hop, Option.some.injEq] at ho0
                      subst ho0
                      simp only [↓reduceIte, hop]
                      rw [Obj.setSlot_canonical]
                    · simp [h0p, h0n]
                obtain ⟨f1, -, f3, f4, -, -⟩ := Obj.ofVersion_fields sp w cut
                have hslot1 : ∀ z sl, (Obj.ofVersion sp w cut).slot? z = some sl →
                    z ∈ pointees sp (cutHist w cut) ∧ sl = Slot.stream (w.ref? z) := by
                  intro z sl hz
                  rw [Obj.ofVersion_slot?] at hz
                  by_cases hz' : z ∈ pointees sp (cutHist w cut)
                  · simp only [hz', ↓reduceIte, Option.some.injEq] at hz
                    exact ⟨hz', hz.symm⟩
                  · simp only [hz', ↓reduceIte] at hz; cases hz
                -- The loaded object's version is x's latest, at c or later.
                have hcw : c ≤ w.recNo :=
                  hcut.2.1 K w (by omega) (Nat.le_of_lt hKk) (ReadsPhys.latest x w hrxk hlv)
                -- A cut history has no slots: x has no canonical object, so its newest version in the
                -- section has no entries up to s.
                have hcutE : ∀ s', cut = some s' → cutHist w cut = [] := by
                  intro s' hs'
                  have hcs : (m.s ≤ w.recNo && isKeyLevel sp w.isData w.level) = true := by
                    by_cases h : (m.s ≤ w.recNo && isKeyLevel sp w.isData w.level) = true
                    · exact h
                    · exfalso
                      have : cut = none := by
                        show (if m.s ≤ w.recNo && isKeyLevel sp w.isData w.level then some m.s else none) = none
                        simp [h]
                      rw [this] at hs'; cases hs'
                  simp only [Bool.and_eq_true, decide_eq_true_eq] at hcs
                  have hcut' : cut = some m.s := by
                    show (if m.s ≤ w.recNo && isKeyLevel sp w.isData w.level then some m.s else none) = some m.s
                    simp [hcs.1, hcs.2]
                  rw [hcut']
                  show w.hist.upTo m.s = []
                  rw [hm.sEq]
                  have hsw : lastSp (st sp al ts k).S ≤ w.recNo := by rw [← hm.sEq]; exact hcs.1
                  have hnw : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x = some w := by
                    cases hn : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x with
                    | none => exact absurd hn (newest_some_of_versionAt hw hsw)
                    | some w' => rw [newest_lv hn, Option.some.injEq] at hlv; rw [hlv]
                  have hwd : w.isData = false := by
                    have := hcs.2
                    unfold isKeyLevel at this
                    cases hd : w.isData
                    · rfl
                    · rw [hd] at this; simp at this
                  by_cases hem : w.hist.upTo (lastSp (st sp al ts k).S) = []
                  · exact hem
                  · exact absurd hcx (hm.coverSec x w hnw hwd hem)
                refine ⟨fun h' o' ho' => ?_, fun h' o' ho' hro z hz r' hz' hrc => ?_,
                  fun h' o' ho' hoD z r' hz' hrc => ?_⟩
                · -- node
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    exact hci.node hp op hop
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      right
                      intro v hv
                      show c ≤ v.recNo
                      have : (Obj.ofVersion sp w cut).node = x := by rw [f1, hwx]
                      change (Obj.ofVersion sp w cut).node = _ at this
                      rw [show ({ Obj.ofVersion sp w cut with canonical := true } : Obj V).node = x from this,
                        hlv, Option.some.injEq] at hv
                      rw [← hv]; exact hcw
                    · exact hci.node h' o' ho'
                · -- live
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz'
                    split at hz'
                    · cases hz'
                    · exact hci.live hp op hop hro z hz r' hz' hrc
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      obtain ⟨-, hze⟩ := hslot1 z _ hz'
                      simp only [Slot.stream.injEq] at hze
                      have hzl : z ∈ sp.live ((cutHist w cut).upTo K) := hz
                      cases hc : cut with
                      | some s' =>
                        exfalso
                        rw [hcutE s' hc] at hzl
                        obtain ⟨e, he, -⟩ := hls _ _ hzl
                        simp [History.upTo] at he
                      | none =>
                        rw [hc] at hzl
                        exact cut_ref_live hok hj hk (Nat.le_of_lt hKk) hsK hcut hrxk hlv hzl hze.symm hrc
                    · exact hci.live h' o' ho' hro z hz r' hz' hrc
                · -- dslot
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz'
                    split at hz'
                    · cases hz'
                    · rcases hci.dslot hp op hop hoD z r' hz' hrc with h1 | ⟨h1, h2⟩
                      · exact Or.inl h1
                      · right
                        have hzx : z ≠ x := by
                          intro he; subst he
                          rw [h1 K (Nat.le_refl K) (Nat.le_of_lt hKk)] at hrxk; cases hrxk
                        exact ⟨h1, by rw [hcan z hzx]; exact h2⟩
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      left
                      obtain ⟨-, hze⟩ := hslot1 z _ hz'
                      simp only [Slot.stream.injEq] at hze
                      have hxD : inD (st sp al ts k).D x = true := by
                        have : (Obj.ofVersion sp w cut).node = x := by rw [f1, hwx]
                        rw [← this]; exact hoD
                      have h3 := (hcut.2.2.1 x hxD w hlv).2 z r' hze.symm hrc
                      cases hnz : newest (st sp al ts k).S (lastSp (st sp al ts k).S) z with
                      | none => rfl
                      | some wz =>
                        exfalso
                        obtain ⟨rz, hrz, hwz⟩ := newest_some hnz
                        obtain ⟨-, hwzr, -⟩ := hinvk.version_node hwz
                        rw [newest_lv hnz, Option.map_some, Option.some.injEq] at h3
                        omega
                    · rcases hci.dslot h' o' ho' hoD z r' hz' hrc with h1 | ⟨h1, h2⟩
                      · exact Or.inl h1
                      · right
                        have hzx : z ≠ x := by
                          intro he; subst he
                          rw [h1 K (Nat.le_refl K) (Nat.le_of_lt hKk)] at hrxk; cases hrxk
                        exact ⟨h1, by rw [hcan z hzx]; exact h2⟩

end Walk

/-! ## The change of the rerun -/

section Change

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The change of a transaction of the rerun keeps the invariant, from K to K + 1.
A new pointer's slot to a node without a canonical object is copied from an object
of a node that has the node as a live child at K (the invariant at K), or, if there
is none, its node is not reachable from K on, or has no version in the section
(`stale_absurd`): a reachable node has a current parent, which has a canonical
object (a source) or is clean. A live pointer of a node at K + 1 is live at K or
made by the change (`PhysStep`, no live child comes back), and a live new pointer
has a source: the node's current parent at K has a canonical object, or is its
only current parent at K + 1 too (TREE) and so is the node changed. -/
theorem CutInv.applyChange (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k K c : Nat} (hk : k ≤ ts.length) (hKk : K < k)
    (hKt : K < ts.length) (hsK : lastSp (st sp al ts k).S ≤ K) (hcut : CutOK sp c (st sp al ts k) k) {m : Mem V}
    (hci : CutInv sp (st sp al ts k) k c K m) (hr : RInv sp (st sp al ts k).S m)
    (hm : MemInv sp (st sp al ts k) K m) {P : Struct V} (hP : SameNodes P (st sp al ts K).P)
    (hcanP : ∀ x ∈ pathOf sp (st sp al ts K).P (sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K))
      (K + 1), m.canonicalOf x ≠ none)
    (hm3 : MemInv sp (st sp al ts k) (K + 1)
      (m.applyChange sp P (K + 1) (sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K)))) :
    CutInv sp (st sp al ts k) k c (K + 1)
      (m.applyChange sp P (K + 1) (sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K))) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hinvK1 := inv_st sp al ts hok hst (K + 1) (by omega)
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have hkK1 := kctx_st sp al ts hok hj (K := K + 1) (by omega) hk
  have hfs := st_fa_le sp al ts hk
  have hc1 := hcut.1
  have hstep : StepOK sp (st sp al ts K).P (K + 1) (sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K)) :=
    hok.2 K hKt
  have hphs : PhysStep sp (st sp al ts K).P (K + 1) (sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K)) :=
    hph K hKt
  have hP1 := st_P_succ sp al ts hok hst hKt
  have htree : treeAt sp (st sp al ts (K + 1)).P (K + 1) := (hev.1 (K + 1) (by omega)).tree
  generalize hch : sp.exec ts[K] (K + 1) (view sp (st sp al ts K).P K) = ch at hstep hphs hP1 hcanP hm3 ⊢
  -- The memory after the new nodes, and the result.
  have hfr := hm.fresh
  have hnd := hstep.distinct
  have hf := applyFacts sp P (K + 1) ch m
  have hcls := foldl_addNew_obj ch.new hnd m hfr
  have htbl0 : ∀ y h, m.tableOf y = some h → (m.obj? h).isSome := by
    intro y h ht; obtain ⟨o, ho, -⟩ := hm.tbl y h ht; rw [ho]; rfl
  have hnd1 := foldl_addNew_nodup ch.new m hfr hm.nodup
  -- A node of the state after T(K) is not new.
  have hnotnew : ∀ y, ((st sp al ts K).P.get? y).isSome → y ∉ ch.new.map (·.id) := by
    intro y hy hyn
    obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hyn
    have := hstep.fresh nn hnn
    rw [this] at hy; cases hy
  -- A stream slot below c of an object of m names a node of the state after T(K).
  have hyK : ∀ h o y r, m.obj? h = some o → o.slot? y = some (Slot.stream (some r)) → r < c →
      ((st sp al ts K).P.get? y).isSome := by
    intro h o y r ho hsl hrc
    obtain ⟨u, hu⟩ := hr.ver h o ho y r hsl
    have huK : (st sp al ts K).S.versionAt r y = some u := by
      rw [st_S_take hok hst (Nat.le_of_lt hKk) hk, versionAt_take]
      simp only [show r < K + 1 by omega, ↓reduceIte]; exact hu
    obtain ⟨-, -, n, hn, -⟩ := hinvK.version_node huK
    rw [hn]; rfl
  -- The objects of m1: m's, and the new nodes', without slots.
  have hsrc : ∀ q ∈ (ch.new.foldl addNew m).objs, ∀ z sl, q.2.slot? z = some sl → m.obj? q.1 = some q.2 := by
    intro q hq z sl hz
    have hq1 := obj?_of_mem_objs hnd1 hq
    rcases hcls q.1 q.2 hq1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
    · exact h2
    · rw [hon] at hz; simp [newObj, Obj.slot?] at hz
  -- canonical objects of m1
  have hcan1 : ∀ y, y ∉ ch.new.map (·.id) → (ch.new.foldl addNew m).canonicalOf y = m.canonicalOf y :=
    fun y hy => addNew_canonicalOf_old m ch.new hfr htbl0 hy
  -- An object of the result: an object of m1 with the change's entries for its node.
  have hobj : ∀ h o3, (m.applyChange sp P (K + 1) ch).obj? h = some o3 →
      ∃ o1, (ch.new.foldl addNew m).obj? h = some o1 ∧ o3 = updAll sp P (K + 1) (ch.new.foldl addNew m)
        (ch.adds.filter (fun a => (ch.new.foldl addNew m).canonicalOf a.1 == some h)) o1 := by
    intro h o3 ho3
    rw [hf.obj h] at ho3
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
    exact ⟨o1, ho1, rfl⟩
  -- A source: an object of a node reachable at K with y as a live child then.
  have hsrcOK : ∀ (q : Nat × Obj V) (y : NodeId), srcOK sp P (K + 1) y q = true →
      ∀ r, q.2.slot? y = some (Slot.stream (some r)) → r < c → q ∈ (ch.new.foldl addNew m).objs →
      newest (st sp al ts k).S (lastSp (st sp al ts k).S) y = none := by
    intro q y hq r hsl hrc hqm
    have hqo := hsrc q hqm y _ hsl
    unfold srcOK at hq
    simp only [Bool.and_eq_true, Nat.add_sub_cancel] at hq
    obtain ⟨⟨⟨hqc, -⟩, hqr⟩, hql⟩ := hq
    cases hnq : P.get? q.2.node with
    | none => rw [hnq] at hql; cases hql
    | some nq =>
      rw [hnq] at hql
      simp only [List.contains_iff_mem] at hql
      have hnqK : (st sp al ts K).P.get? q.2.node = some nq := by rw [← hP]; exact hnq
      have hqh := hm.hist_K hkK hinvK hqo hqc hnqK
      have hrq : reachable sp (st sp al ts k).P K q.2.node = true := by
        rw [hkK.reachable_eq hls (Nat.le_refl K), ← hP.reachable]; exact hqr
      exact hci.live q.1 q.2 hqo hrq y (by rw [hqh]; exact hql) r hsl hrc
  -- NS1 gives no stream slot below c to a node with a version in the section.
  have hNS1 : ∀ y r, NS1 sp P (K + 1) (ch.new.foldl addNew m) y = some (Slot.stream (some r)) → r < c →
      newest (st sp al ts k).S (lastSp (st sp al ts k).S) y = none := by
    intro y r hns hrc
    unfold NS1 at hns
    cases hcy : (ch.new.foldl addNew m).canonicalOf y with
    | some h0 => rw [hcy] at hns; simp at hns
    | none =>
      rw [hcy] at hns
      simp only [Option.map_none, Option.none_or] at hns
      unfold srcSlot at hns
      cases hfd : (ch.new.foldl addNew m).objs.find? (srcOK sp P (K + 1) y) with
      | none => rw [hfd] at hns; cases hns
      | some q =>
        rw [hfd] at hns
        simp only [Option.bind_some] at hns
        exact hsrcOK q y (List.find?_some hfd) r hns hrc (List.mem_of_find?_eq_some hfd)
  -- Without a source, a node reachable at K with a current parent without a canonical object
  -- after the walk: its parent has a canonical object, so it is a source.
  have hnosrc : ∀ y q0 nq, NS1 sp P (K + 1) (ch.new.foldl addNew m) y = none →
      reachable sp (st sp al ts K).P K q0 = true → (st sp al ts K).P.get? q0 = some nq →
      y ∈ sp.live (nq.hist.upTo K) → m.canonicalOf q0 = none := by
    intro y q0 nq hns hrq hnq hyl
    have hq0n : q0 ∉ ch.new.map (·.id) := hnotnew q0 (by rw [hnq]; rfl)
    cases hcq : m.canonicalOf q0 with
    | none => rfl
    | some h0 =>
      exfalso
      obtain ⟨ht0, o0, ho0, hc0⟩ := (m.canonicalOf_eq_some q0 h0).mp hcq
      obtain ⟨o0', ho0', hn0⟩ := hm.tbl q0 h0 ht0
      rw [ho0, Option.some.injEq] at ho0'
      subst ho0'
      have hnqK : (st sp al ts K).P.get? o0.node = some nq := by rw [hn0]; exact hnq
      have hoh := hm.hist_K hkK hinvK ho0 hc0 hnqK
      have hyp : y ∈ pointees sp o0.hist := by
        rw [hoh, ← upTo_of_forall _ _ (hinvK.times q0 nq hnq)]; exact mem_pointees_of_liveH hls hyl
      have hsl := hr.slotsAll h0 o0 ho0 y hyp
      have ho0m1 : (ch.new.foldl addNew m).obj? h0 = some o0 := by
        rw [foldl_addNew_old ch.new m h0 (lt_next_of_obj? hfr ho0)]; exact ho0
      have hsrc0 : srcOK sp P (K + 1) y (h0, o0) = true := by
        unfold srcOK
        simp only [hc0, hsl, Bool.true_and, Nat.add_sub_cancel, hn0, hP.reachable, hrq, hP q0, hnq]
        simp [hyl]
      unfold NS1 srcSlot at hns
      rw [show (ch.new.foldl addNew m).canonicalOf y = none by
        cases h' : (ch.new.foldl addNew m).canonicalOf y with
        | none => rfl
        | some _ => rw [h'] at hns; simp at hns] at hns
      simp only [Option.map_none, Option.none_or] at hns
      cases hfd : (ch.new.foldl addNew m).objs.find? (srcOK sp P (K + 1) y) with
      | none => exact List.find?_eq_none.mp hfd _ (mem_objs_of_obj? ho0m1) hsrc0
      | some p =>
        rw [hfd] at hns
        have hpr := List.find?_some hfd
        unfold srcOK at hpr
        simp only [Bool.and_eq_true] at hpr
        simp only [Option.bind_some] at hns
        rw [hns] at hpr
        simp at hpr
  -- The node table of m1 names objects of their nodes.
  have htn1 : ∀ z h, (ch.new.foldl addNew m).tableOf z = some h →
      ∃ o, (ch.new.foldl addNew m).obj? h = some o ∧ o.node = z := by
    intro z h ht
    by_cases hzn : z ∈ ch.new.map (·.id)
    · obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hzn
      obtain ⟨h2, -, ht2, ho2⟩ := foldl_addNew_new ch.new hnd m nn hnn
      rw [ht, Option.some.injEq] at ht2
      subst ht2
      exact ⟨newObj nn, ho2, rfl⟩
    · rw [foldl_addNew_table_old ch.new m z hzn] at ht
      obtain ⟨o, ho, hn⟩ := hm.tbl z h ht
      exact ⟨o, by rw [foldl_addNew_old ch.new m h (lt_next_of_obj? hfr ho)]; exact ho, hn⟩
  -- A node with an add of the change, at h: its object's node.
  have hLnode : ∀ h o1 a, (ch.new.foldl addNew m).obj? h = some o1 →
      a ∈ ch.adds.filter (fun a => (ch.new.foldl addNew m).canonicalOf a.1 == some h) →
      a.1 = o1.node ∧ (ch.new.foldl addNew m).canonicalOf o1.node = some h := by
    intro h o1 a ho1 ha
    have hc := (List.mem_filter.mp ha).2
    simp only [beq_iff_eq] at hc
    obtain ⟨ht, o, ho, -⟩ := ((ch.new.foldl addNew m).canonicalOf_eq_some a.1 h).mp hc
    obtain ⟨o', ho', hn'⟩ := htn1 a.1 h ht
    rw [ho1, Option.some.injEq] at ho'
    rw [ho', hn'] at *
    exact ⟨rfl, by rw [← hn']; exact hc⟩
  -- The canonical objects of the result: those of m1.
  have hcan3 : ∀ y, (m.applyChange sp P (K + 1) ch).canonicalOf y = (ch.new.foldl addNew m).canonicalOf y :=
    applyChange_canonicalOf sp P (K + 1) ch m
  -- A stream slot of own or anySlot: a stream slot of an object of m.
  have hown : ∀ h o1 y sl, (ch.new.foldl addNew m).obj? h = some o1 →
      (o1.slot? y).or (anySlot (ch.new.foldl addNew m) y) = some sl →
      ∃ h' o', m.obj? h' = some o' ∧ o'.slot? y = some sl := by
    intro h o1 y sl ho1 hs
    cases hs1 : o1.slot? y with
    | some sl1 =>
      rw [hs1] at hs
      simp only [Option.some_or, Option.some.injEq] at hs
      subst hs
      exact ⟨h, o1, hsrc (h, o1) (mem_objs_of_obj? ho1) y _ hs1, hs1⟩
    | none =>
      rw [hs1] at hs
      simp only [Option.none_or] at hs
      unfold anySlot at hs
      cases hfd : (ch.new.foldl addNew m).objs.find? (fun p => p.2.canonical && (p.2.slot? y).isSome) with
      | none => rw [hfd] at hs; cases hs
      | some q =>
        rw [hfd] at hs
        simp only [Option.bind_some] at hs
        exact ⟨q.1, q.2, hsrc q (List.mem_of_find?_eq_some hfd) y _ hs, hs⟩
  -- An object of m: its node is in the state after T(K).
  have hnodeK : ∀ h o, m.obj? h = some o → ((st sp al ts K).P.get? o.node).isSome := by
    intro h o ho
    obtain ⟨t, ht, hrt⟩ := hm.born h o ho
    rw [hkK.reachable_eq hls ht] at hrt
    exact Reach.isSome ((reachable_iff _ _ _ _).mp hrt)
  refine ⟨fun h o3 ho3 => ?_, fun h o3 ho3 hro y hy r hsl hrc => ?_, fun h o3 ho3 hoD y r hsl hrc => ?_⟩
  · -- node: a new node has no version before its creation
    obtain ⟨o1, ho1, rfl⟩ := hobj h o3 ho3
    rw [(updAll_core sp P (K + 1) _ _ o1).1]
    rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, hnn, hon, -⟩
    · exact hci.node h o1 h2
    · right
      rw [hon]
      intro v hv
      show c ≤ v.recNo
      have hw := hinvk.lv_at hv
      rcases Nat.lt_or_ge v.recNo (K + 1) with hlt | hge
      · exfalso
        have hwK : (st sp al ts K).S.versionAt v.recNo nn.id = some v := by
          rw [st_S_take hok hst (Nat.le_of_lt hKk) hk, versionAt_take]
          simp only [hlt, ↓reduceIte]; exact hw
        obtain ⟨-, -, n, hn, -⟩ := hinvK.version_node hwK
        rw [hstep.fresh nn hnn] at hn; cases hn
      · omega
  · -- live, at K + 1
    obtain ⟨o1, ho1, rfl⟩ := hobj h o3 ho3
    obtain ⟨e1, -, -, -, e5, -⟩ := updAll_core sp P (K + 1) (ch.new.foldl addNew m)
      (ch.adds.filter (fun a => (ch.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    have hc1 : o1.canonical = true := by
      rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
      · exact hr.canon h o1 h2
      · rw [hon]; rfl
    rw [e1] at hro
    -- the node at K + 1, and the live child there
    have hro1 : reachable sp (st sp al ts (K + 1)).P (K + 1) o1.node = true := by
      rw [← hkK1.reachable_eq hls (Nat.le_refl _)]; exact hro
    obtain ⟨n1, hn1⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hro1))
    obtain ⟨-, ⟨n, hn, hoh, -, -⟩, -⟩ := hm3.canon h _ ho3 (by rw [e5]; exact hc1)
    rw [e1] at hn
    obtain ⟨n', hn', -, -, hup⟩ := hkK1.grow o1.node n1 hn1
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    have hy1 : y ∈ sp.live (n1.hist.upTo (K + 1)) := by
      rw [← hup, ← upTo_upTo n.hist (Nat.le_refl (K + 1)), ← hoh]; exact hy
    rw [updAll_slot] at hsl
    split at hsl
    · rename_i hyL
      unfold combo at hsl
      cases hns : NS1 sp P (K + 1) (ch.new.foldl addNew m) y with
      | some sl =>
        rw [hns] at hsl
        simp only [Option.some_or, Option.some.injEq] at hsl
        subst hsl
        exact hNS1 y r hns hrc
      | none =>
        exfalso
        rw [hns] at hsl
        simp only [Option.none_or] at hsl
        obtain ⟨h', o', ho', hsl'⟩ := hown h o1 y _ ho1 hsl
        have hyKs := hyK h' o' y r ho' hsl' hrc
        obtain ⟨hyr1, hyrt, -⟩ := hinvK1.reach_child hls hn1 hro1 hy1
        have hyrK : reachable sp (st sp al ts K).P K y = true := by
          have h1 := hyr1
          rw [hP1] at h1
          rcases hstep.noRes y h1 with h2 | h2
          · rw [show K + 1 - 1 = K by omega] at h2; exact h2
          · exact absurd h2 (hnotnew y hyKs)
        obtain ⟨q0, nq, -, hrq0, hnq0, -, -, hyl0⟩ := reach_parent hyrK hyrt
        have hcq0 := hnosrc y q0 nq hns hrq0 hnq0 hyl0
        have hq0n : q0 ∉ ch.new.map (·.id) := hnotnew q0 (by rw [hnq0]; rfl)
        -- q0 is not on the paths, so unchanged, and still q0's live child at K + 1
        have hq0p : q0 ∉ pathOf sp (st sp al ts K).P ch (K + 1) := fun hp => hcanP q0 hp hcq0
        have hq0c : changed ch q0 = false ∧ reachable sp ((st sp al ts K).P.apply (K + 1) ch) (K + 1) q0 = true := by
          by_cases hcon : changed ch q0 = false ∧
              reachable sp ((st sp al ts K).P.apply (K + 1) ch) (K + 1) q0 = true
          · exact hcon
          exfalso
          apply hq0p
          apply pathOf_mem (n := nq) (by rw [show K + 1 - 1 = K by omega]; exact hrq0) hnq0
          apply List.any_eq_true.mpr
          refine ⟨q0, by rw [show K + 1 - 1 = K by omega]; exact self_mem_reachFrom sp _ K q0 nq, ?_⟩
          cases hcq : changed ch q0
          · cases hrq1 : reachable sp ((st sp al ts K).P.apply (K + 1) ch) (K + 1) q0
            · simp [show K + 1 - 1 = K by omega, hrq0]
            · exact absurd ⟨hcq, hrq1⟩ hcon
          · simp
        have hadds0 : addsFor ch (K + 1) q0 = [] := by
          unfold addsFor
          have : ch.adds.filter (fun a => a.1 == q0) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro a ha hq
            have h1 := hq0c.1
            unfold changed at h1
            simp only [Bool.or_eq_false_iff, List.any_eq_false] at h1
            exact h1.2 a ha (by simpa using hq)
          rw [this]; rfl
        have hnq1 : (st sp al ts (K + 1)).P.get? q0 = some { nq with hist := nq.hist ++ [] } := by
          rw [hP1, get?_apply_of_get? hnq0, hadds0]
        have hyq1 : y ∈ sp.live (({ nq with hist := nq.hist ++ [] } : Node V).hist.upTo (K + 1)) := by
          simp only [List.append_nil]
          rw [upTo_of_forall _ _ (fun e he => Nat.le_succ_of_le (hinvK.times q0 nq hnq0 e he))]
          rw [← upTo_of_forall _ _ (hinvK.times q0 nq hnq0)]; exact hyl0
        have hrq1 : reachable sp (st sp al ts (K + 1)).P (K + 1) q0 = true := by rw [hP1]; exact hq0c.2
        have hxq := treeAt_unique htree hyr1 hyrt hro1 hrq1 hn1 hnq1 hy1 hyq1
        -- but o1's node has a canonical object: it has an add
        obtain ⟨a, haL, -⟩ := List.mem_flatMap.mp hyL
        obtain ⟨-, hca⟩ := hLnode h o1 a ho1 haL
        rw [hxq, hcan1 q0 hq0n, hcq0] at hca
        cases hca
    · rename_i hyL
      -- an old pointer: live at K, or made by the change (then it would be in the adds)
      rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
      · have hxK := hnodeK h o1 h2
        rcases hphs.liveNew o1.node n1 (by rw [← hP1]; exact hn1) y hy1 with ⟨n0, hn0, hy0⟩ | ⟨a, ha, hax, hya⟩
        · rw [show K + 1 - 1 = K by omega] at hy0
          have hoh0 := hm.hist_K hkK hinvK h2 hc1 hn0
          have hrK := reach_back hok hj hk hxK (K + 1) (by omega) (by omega) hro
          apply hci.live h o1 h2 hrK y _ r hsl hrc
          rw [hoh0]; exact hy0
        · exfalso
          apply hyL
          apply List.mem_flatMap.mpr
          refine ⟨a, List.mem_filter.mpr ⟨ha, ?_⟩, hya⟩
          obtain ⟨htb, -⟩ := hm.canon h o1 h2 hc1
          have hcm : m.canonicalOf o1.node = some h := (m.canonicalOf_eq_some _ h).mpr ⟨htb, o1, h2, hc1⟩
          have hon : o1.node ∉ ch.new.map (·.id) := hnotnew o1.node hxK
          rw [hax, hcan1 _ hon, hcm]; simp
      · rw [hon] at hsl; simp [newObj, Obj.slot?] at hsl
  · -- dslot, at K + 1
    obtain ⟨o1, ho1, rfl⟩ := hobj h o3 ho3
    obtain ⟨e1, -, -, -, -, -⟩ := updAll_core sp P (K + 1) (ch.new.foldl addNew m)
      (ch.adds.filter (fun a => (ch.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    rw [e1] at hoD
    rw [updAll_slot] at hsl
    split at hsl
    · unfold combo at hsl
      cases hns : NS1 sp P (K + 1) (ch.new.foldl addNew m) y with
      | some sl =>
        rw [hns] at hsl
        simp only [Option.some_or, Option.some.injEq] at hsl
        subst hsl
        exact Or.inl (hNS1 y r hns hrc)
      | none =>
        rw [hns] at hsl
        simp only [Option.none_or] at hsl
        obtain ⟨h', o', ho', hsl'⟩ := hown h o1 y _ ho1 hsl
        have hyKs := hyK h' o' y r ho' hsl' hrc
        have hcy : (ch.new.foldl addNew m).canonicalOf y = none := by
          unfold NS1 at hns
          cases h1 : (ch.new.foldl addNew m).canonicalOf y with
          | none => rfl
          | some _ => rw [h1] at hns; simp at hns
        cases hny : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y with
        | none => exact Or.inl rfl
        | some wy =>
          right
          refine ⟨fun t ht1 ht2 => ?_, by rw [hcan3]; exact hcy⟩
          cases hrt : reachable sp (st sp al ts k).P t y with
          | false => rfl
          | true =>
            exfalso
            have hrK := reach_back hok hj hk hyKs t (by omega) ht2 hrt
            have hrK' : reachable sp (st sp al ts K).P K y = true := by
              rw [← hkK.reachable_eq hls (Nat.le_refl K)]; exact hrK
            have hyrt : y ≠ root := by
              obtain ⟨-, ⟨n0, hn0, hoh0, -, -⟩, -⟩ := hm.canon h' o' ho' (hr.canon h' o' ho')
              have hyp := hr.keys h' o' ho' y (by rw [hsl']; rfl)
              rw [hoh0] at hyp
              obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hyp
              exact hinvk.ptr_ne_root hn0 (mem_upTo.mp he).1 hye
            obtain ⟨q0, nq, -, hrq0, hnq0, -, -, hyl0⟩ := reach_parent hrK' hyrt
            exact stale_absurd hok hj hmk hev hk hKk hsK hcut hr hm hrc ho' hsl' hrq0 hnq0 hyl0
              (hnosrc y q0 nq hns hrq0 hnq0 hyl0)
    · rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
      · rcases hci.dslot h o1 h2 hoD y r hsl hrc with h3 | ⟨h3, h4⟩
        · exact Or.inl h3
        · right
          refine ⟨fun t ht1 ht2 => h3 t (by omega) ht2, ?_⟩
          rw [hcan3, hcan1 y (hnotnew y (hyK h o1 y r h2 hsl hrc))]
          exact h4
      · rw [hon] at hsl; simp [newObj, Obj.slot?] at hsl

end Change

/-! ## The rerun -/

section Rerun

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The writer's walk of the rerun, node after node. -/
theorem CutInv.reachPath (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {k K c : Nat} (hk : k ≤ ts.length) (hKk : K < k)
    (hsK : lastSp (st sp al ts k).S ≤ K) (hcut : CutOK sp c (st sp al ts k) k) {P : Struct V}
    (hP : SameNodes P (st sp al ts K).P)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp (st sp al ts k).P K p = true) :
    ∀ (L : List NodeId) (m : Mem V), CutInv sp (st sp al ts k) k c K m → RInv sp (st sp al ts k).S m →
      MemInv sp (st sp al ts k) K m →
      CutInv sp (st sp al ts k) k c K (L.foldl (Mem.reachOnPath sp (st sp al ts k).S P (K + 1) path) m) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hctx := pctx_st hok hst hk
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  intro L
  induction L with
  | nil => intro m hci _ _; exact hci
  | cons x L ih =>
    intro m hci hr hm
    simp only [List.foldl_cons]
    exact ih _ (hci.reachOnPath hok hj hk hKk hsK hcut hr hm hP hpath x)
      (hr.reachOnPath hok hj hmk hev hk hKk hsK hm hP hpath x) (hm.reachOnPath_ok hctx hkK hP hpath x).1

/-- One transaction of the rerun keeps the invariant, from K to K + 1. -/
theorem CutInv.rerunStep (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k K c : Nat} (hk : k ≤ ts.length)
    (hsK : lastSp (st sp al ts k).S ≤ K) (hKk : K < k) (hcut : CutOK sp c (st sp al ts k) k)
    {acc : Mem V × Struct V} (hci : CutInv sp (st sp al ts k) k c K acc.1)
    (hr : RInv sp (st sp al ts k).S acc.1) (hm : MemInv sp (st sp al ts k) K acc.1)
    (hP : SameNodes acc.2 (st sp al ts K).P) :
    CutInv sp (st sp al ts k) k c (K + 1) (rerunStep sp (st sp al ts k).S acc (K + 1)).1 := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hKt : K < ts.length := by omega
  have hls : LiveSub sp := hok.1.liveSub
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have htr := st_trans sp al ts hok hst (j := K + 1) (k := k) (by omega) (by omega) hk
  simp only [Nat.add_sub_cancel] at htr
  obtain ⟨R, hR, hRt⟩ : ∃ R, (st sp al ts k).S[K + 1]? = some R ∧ R.trans = some ts[K] := by
    cases h : (st sp al ts k).S[K + 1]? with
    | none => rw [h] at htr; cases htr
    | some R => rw [h] at htr; exact ⟨R, rfl, htr⟩
  rw [rerunStep_eq sp _ acc hR hRt]
  simp only [Nat.add_sub_cancel]
  have hm2 := rerun_apply_ok hok hph hj hk hKk hm hP (tr := ts[K]) (List.getElem?_eq_getElem hKt)
  rw [foldl_canonicalNode_noop sp _ _ R.gd
    (fun x hx => hm2.coverGd (K + 1) R x (by omega) (Nat.le_refl _) hR hx)]
  have hpath : ∀ p ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1),
      reachable sp (st sp al ts k).P K p = true := by
    intro p hp
    have := (mem_pathOf hp).1
    rw [Nat.add_sub_cancel, hP.reachable] at this
    rw [hkK.reachable_eq hls (Nat.le_refl K)]
    exact this
  obtain ⟨hr1, hm1⟩ := RInv.reachPath hok hj hmk hev hk hKk hsK hP hpath
    ((pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1)).mergeSort
      (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))) acc.1 hr hm
  have hci1 := CutInv.reachPath hok hj hmk hev hk hKk hsK hcut hP hpath
    ((pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1)).mergeSort
      (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))) acc.1 hci hr hm
  have hctx := pctx_st hok hst hk
  have hparent : ∀ x ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1), ∃ np nx,
        acc.2.get? p = some np ∧ acc.2.get? x = some nx ∧ nx.level < np.level ∧
        x ∈ sp.live (np.hist.upTo K) := by
    intro x hx hxr
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent (mem_pathOf hx).1 hxr
    refine ⟨p, pathOf_parent hx hrp hnp hxl hnx hlt, np, nx, hnp, hnx, hlt, ?_⟩
    simpa using hxl
  obtain ⟨-, -, hcan1⟩ := MemInv.reachPath_ok hctx hkK hP hpath hparent
    ((pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1)).mergeSort
      (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))) [] acc.1 hm (by simp)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact pairwise_byLevelDesc _ _)
  rw [hP.view K] at hci1 hr1 hm1 hcan1 hm2 hpath ⊢
  exact CutInv.applyChange hok hph hj hmk hev hk hKk hKt hsK hcut hci1 hr1 hm1 hP
    (fun x hx => hcan1 x (by rw [pathOf_congr hP]; exact hx)) hm2

/-- The startup's memory, after the rerun, meets the invariant at k. -/
theorem cutInv_lazyStartup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k c : Nat} (hk : k ≤ ts.length)
    (hcut : CutOK sp c (st sp al ts k) k) :
    CutInv sp (st sp al ts k) k c k (lazyStartup sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hctx := pctx_st hok hst hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have hkS := kctx_st sp al ts hok hj hsk hk
  have hm0 := hctx.base_ok hkS
  have hP0 := base_sameNodes sp al ts hok hst hk
  have hr0 := rinv_lazyBase hok hj hmk hev hk
  have hc0 := cutInv_lazyBase hok hj hk hcut
  rw [lazyStartup_eq]
  generalize hs : lastSp (st sp al ts k).S = s at hm0 hP0 hsk hr0 hc0
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  rw [hidx]
  have key : ∀ n, n ≤ k - s →
      RInv sp (st sp al ts k).S ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).1 ∧
        MemInv sp (st sp al ts k) (s + n)
          ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
            (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).1 ∧
        SameNodes ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
            (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).2
          (st sp al ts (s + n)).P ∧
        CutInv sp (st sp al ts k) k c (s + n)
          ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
            (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).1 := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hr0, hm0, hP0, hc0⟩
    | succ n ih =>
      intro hn
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      obtain ⟨h0, h1, h2, h3⟩ := ih (by omega)
      have hsK : lastSp (st sp al ts k).S ≤ s + n := by rw [hs]; omega
      have := rerunStep_ok hok hph hj hk (K := s + n) hsK (by omega) h1 h2
      have hr' := RInv.rerunStep hok hph hj hmk hev hk (K := s + n) hsK (by omega) h0 h1 h2
      have hc' := CutInv.rerunStep hok hph hj hmk hev hk (K := s + n) hsK (by omega) hcut h3 h0 h1 h2
      rw [show s + 1 + n = s + n + 1 by omega, show s + (n + 1) = s + n + 1 by omega]
      exact ⟨hr', this.1, this.2, hc'⟩
  have := (key (k - s) (Nat.le_refl _)).2.2.2
  rw [show s + (k - s) = k by omega] at this
  exact this

end Rerun

/-! ## The pointers that Java skips -/

section Skip

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- A stream slot of the object of a node of D in the startup's memory that names a
record below a safe cut names a node without a canonical object: a node without a
version in the section, whose latest version is the slot's, below c, so that no
object of it is canonical (`CutInv.node`); or a node not reachable from k on
without a canonical object (`CutInv.dslot`). -/
theorem cutSkip_lazy (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hev : EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {k c : Nat} (hk : k ≤ ts.length)
    (hcut : CutOK sp c (st sp al ts k) k) {h : Nat} {o : Obj V}
    (ho : (lazyStartup sp (st sp al ts k).S).obj? h = some o) (hD : inD (st sp al ts k).D o.node = true)
    {y : NodeId} {r : Nat} (hsl : o.slot? y = some (Slot.stream (some r))) (hrc : r < c) :
    (lazyStartup sp (st sp al ts k).S).canonicalOf y = none := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvk := inv_st sp al ts hok hst k hk
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hci := cutInv_lazyStartup hok hph hj hmk hev hk hcut
  rcases hci.dslot h o ho hD y r hsl hrc with hnew | ⟨-, hcan⟩
  · cases hcy : (lazyStartup sp (st sp al ts k).S).canonicalOf y with
    | none => rfl
    | some b =>
      exfalso
      obtain ⟨ht, ob, hob, -⟩ := ((lazyStartup sp (st sp al ts k).S).canonicalOf_eq_some y b).mp hcy
      obtain ⟨ob', hob', hnb⟩ := hm.tbl y b ht
      rw [hob, Option.some.injEq] at hob'
      subst hob'
      have hfr := hri.fresh h o ho y (some r) hsl
      unfold ruleRRef at hfr
      rw [hnew] at hfr
      rcases hci.node b ob hob with hroot | hlv
      · -- y is a pointee, never the root
        obtain ⟨-, ⟨n0, hn0, hoh0, -, -⟩, -⟩ := hm.canon h o ho (hri.canon h o ho)
        have hyp := hri.keys h o ho y (by rw [hsl]; rfl)
        rw [hoh0] at hyp
        obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hyp
        exact hinvk.ptr_ne_root hn0 (mem_upTo.mp he).1 hye (by rw [← hnb, hroot])
      · cases hl : (st sp al ts k).S.lv y with
        | none => rw [hl] at hfr; cases hfr
        | some u =>
          rw [hl, Option.map_some, Option.some.injEq] at hfr
          have := hlv u (by rw [hnb]; exact hl)
          have hc1 := hcut.1
          omega
  · exact hcan

end Skip

end SIS
