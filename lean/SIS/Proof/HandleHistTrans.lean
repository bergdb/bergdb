/-
Proofs about the physical layer with handles (bergdb item 009, phase 4a), part
2 of T-READ: one transaction of the physical writer with handles keeps the
invariant for reads at earlier times (`HInvH`): the writer's walk (its follows
and promotes), the change, the writes, and the step to the next state.
-/
import SIS.Proof.HandleHist

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The writer's walk -/

/-- The promote keeps what the pointers give: it only marks an object
canonical. -/
theorem HMem.keepPtrs_promote (m : HMem V) (b : Nat) (ob : HObj V) :
    m.KeepPtrs (m.setObj b { ob with canonical := true }) := by
  refine ⟨rfl, fun _ hd h => ⟨hd, h, rfl⟩, fun q h => ?_⟩
  obtain ⟨n', c, oc, hqn, hc, hoc, hcc⟩ := (m.holdsCanonical_iff q).mp h
  refine ((m.setObj b { ob with canonical := true }).holdsCanonical_iff q).mpr ?_
  by_cases hcb : c = b
  · rw [hcb] at hc
    exact ⟨n', b, { ob with canonical := true }, hqn, hc, HMem.obj?_setObj_self _ _ _, rfl⟩
  · exact ⟨n', c, oc, hqn, hc, by rw [HMem.obj?_setObj_ne _ _ hcb]; exact hoc, hcc⟩

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The writer's promote of a readable object keeps the invariant: a snapshot
promoted is of the latest version of a clean node, good for every time at which
the node is reachable, so its pointers are as reads need them. -/
theorem HInvH.promote (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) {b : Nat} {ob : HObj V} (hob : m.obj? b = some ob) {y : NodeId}
    (hrd : HReadable sp db m b y) : HInvH sp db S0 k (m.setObj b { ob with canonical := true }) := by
  have hk := HMem.keepPtrs_promote m b ob
  apply hh.transfer hm.tbl hk
  intro x o' hx hc t ht hr z hz
  rw [HMem.obj?_setObj] at hx
  split at hx
  · rename_i hxb
    rw [Option.some.injEq] at hx
    subst hx
    obtain ⟨ob1, hob1, hoy, hcase⟩ := hrd
    rw [hob, Option.some.injEq] at hob1
    rw [← hob1] at hoy hcase
    cases hco : ob.canonical with
    | true =>
      left
      exact ⟨ob, by rw [hxb]; exact hob, hco, rfl, rfl, by rw [hobj_canonical_true hco]⟩
    | false =>
      right
      rcases hcase with hcase | ⟨hyD, hyw, hpos⟩
      · rw [hco] at hcase; cases hcase
      -- The snapshot of y's latest version, good at t.
      have hry : reachable sp db.P t y = true := by rw [← hoy]; exact hr
      obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hry
      obtain ⟨q, hq, r, w, h1, h2, h3⟩ := hm.snap_goodRef hinv hls hob hco (r := v.recNo)
        (by rw [hpos, hv]; rfl) (by rw [hoy]; exact hinv.lv_at hv) hg hz
      exact ⟨q, hq, Or.inr (Or.inl ⟨r, w, by rw [hk.slowRef S0 z (hm.tbl.ptr_handle hob hq)]; exact h1,
        h2, h3⟩)⟩
  · exact Or.inl ⟨o', hx, hc, rfl, rfl, rfl⟩

/-- The writer's follow of a live pointer of the canonical object of a current
node keeps the invariant. -/
theorem HInvH.follow_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) (hh : HInvH sp db S0 k m) {a : Nat} {op : HObj V}
    (hop : m.obj? a = some op) (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true)
    {y : NodeId} (hy : y ∈ sp.live op.hist) : HInvH sp db S0 k (m.follow sp S0 db.S a y true).1 := by
  -- y: a live child at k, so a current written node below op's.
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc a op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hy
  obtain ⟨e, he, hye⟩ := hls _ _ hy'
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs op.node n hn e (mem_upTo.mp he).1 y hye
  have hyroot : y ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hry : reachable sp db.P k y = true := by
    rw [reachable_iff] at hr ⊢; exact Reach.child hr hn hy' hny hlt
  obtain ⟨p, hp, hli1, hli2⟩ := hm.live a op hop hco hr y hy
  have hg : HPtrGood S0 db m y p := by
    cases hyD : inD db.D y with
    | true => exact Or.inl ⟨hyD, hli1 hyD⟩
    | false => exact Or.inr ⟨hyD, hli2 hyD⟩
  obtain ⟨m1, n1, b1, hf⟩ := hm.followR_some hinv hop hp hg hyw hry
  have hF := hm.followR_ok hinv hop hf
  have hrd := hF.readable op p hop hp hg hyw
  have hh1 := hh.followR hinv hm hop hf
  obtain ⟨ob, hob, -, hpe, -, -⟩ := hF.inv.promote_ok hinv hev hls hF.objOf hF.tableOf hrd hry
  have hfe : m.follow sp S0 db.S a y true = (m1.setObj b1 { ob with canonical := true }, some b1) := by
    unfold HMem.follow; rw [hf]; exact hpe
  rw [hfe]
  exact hh1.promote hinv hls hF.inv hob hrd

/-- The writer reaches one node of a path. -/
theorem HInvH.reachOnPath (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) (hh : HInvH sp db S0 k m) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P k p = true) (x : NodeId) :
    HInvH sp db S0 k (m.reachOnPath sp S0 db.S db.P (k + 1) path x) := by
  unfold HMem.reachOnPath
  have hK1 : k + 1 - 1 = k := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (k + 1 - 1))).contains x
      | _, _ => false) with
  | none => exact hh
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => rw [hnp, hcp] at hpp; simp at hpp
      | some bp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        obtain ⟨nf, hnf, hh', -, -⟩ := hm.cc bp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh', ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        exact hh.follow_writer hinv hls hev hm hop hco (by rw [hnode]; exact hpath p hpm) hxop

/-- The writer reaches the nodes of its paths: the invariant is kept. -/
theorem HInvH.reachPath (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true) :
    ∀ (L : List NodeId) (m : HMem V), HEInv sp db S0 k m → HInvH sp db S0 k m →
      HInvH sp db S0 k (L.foldl (HMem.reachOnPath sp S0 db.S db.P (k + 1) path) m) := by
  intro L
  induction L with
  | nil => intro m _ hh; exact hh
  | cons x L ih =>
    intro m hm hh
    simp only [List.foldl_cons]
    exact ih _ (hm.reachOnPath_ok hinv hls hev hpath x).1 (hh.reachOnPath hinv hls hev hm hpath x)

end Walk

/-! ## The change and the writes -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V} {c : Changes V}

/-- The change keeps the invariant, for the times up to k: the new entries are
at k + 1; a new pointer holds its pointee's live handle with its canonical
object, or is a copy of a pointer whose record is its pointee's latest version;
and the new nodes are not reachable before. -/
theorem HInvH.applyChange (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) (hstep : StepOK sp db.P (k + 1) c) :
    HInvH sp db S0 k (m.applyChange sp db.P (k + 1) c) := by
  have haf := hm.addFactsH hinv hstep
  have hcf := changeFactsH sp db.P (k + 1) c m
  have hhlt : ∀ n hd, m.handle? n = some hd → n < m.nextHandle := by
    intro n hd h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshH n hle] at h; cases h)
  have holt : ∀ a o, m.obj? a = some o → a < m.nextObj := by
    intro a o h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshO a hle] at h; cases h)
  -- What the pointers give is kept: the old handles and objects stay, with their flags.
  have hk : m.KeepPtrs (m.applyChange sp db.P (k + 1) c) := by
    refine ⟨by rw [hcf.s, haf.s], fun n hd h => ⟨hd, ?_, rfl⟩, fun q h => ?_⟩
    · rw [hcf.handle? n, haf.hold n (hhlt n hd h)]; exact h
    · obtain ⟨n', b', ob', hqn, hb', hob', hcb'⟩ := (m.holdsCanonical_iff q).mp h
      have hn'lt : n' < m.nextHandle := by
        unfold HMem.objOf at hb'
        cases hq' : m.handle? n' with
        | none => rw [hq'] at hb'; cases hb'
        | some hd' => exact hhlt n' hd' hq'
      refine ((m.applyChange sp db.P (k + 1) c).holdsCanonical_iff q).mpr ⟨n', b',
        updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
          (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some b')) ob', hqn, ?_, ?_, ?_⟩
      · rw [hcf.objOf]; unfold HMem.objOf; rw [haf.hold n' hn'lt]; exact hb'
      · rw [hcf.obj b', haf.old b' (holt b' ob' hob'), hob']; rfl
      · rw [(updAllH_core _ _ _ _ _ ob').2.2.2.2.1]; exact hcb'
  apply hh.transfer hm.tbl hk
  intro a o3 ho3 hc3 t ht hrt z hz
  rw [hcf.obj a] at ho3
  obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
  obtain ⟨e1, -, -, e4, e5, -⟩ := updAllH_core sp db.P (k + 1) (c.new.foldl addNewH m)
    (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a)) o1
  rcases haf.cls a o1 ho1 with ⟨-, hold⟩ | ⟨-, nn, hnn, hon, -⟩
  · have hc1 : o1.canonical = true := by rw [← e5]; exact hc3
    have hup : (updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
        (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a)) o1).hist.upTo t =
        o1.hist.upTo t := by
      rw [e4, upTo_append, upTo_eq_nil (List.map (fun a => (⟨k + 1, a.2⟩ : Entry V))
        (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a))) t ?_, List.append_nil]
      intro e he
      obtain ⟨a', -, rfl⟩ := List.mem_map.mp he
      show t < k + 1
      omega
    rw [hup] at hz
    have hrt1 : reachable sp db.P t o1.node = true := by rw [← e1]; exact hrt
    rw [updAllH_ptr]
    split
    · -- a pointer of a new entry
      unfold comboH
      cases hns : NSH sp db.P (k + 1) (c.new.foldl addNewH m) z with
      | none =>
        simp only [Option.none_or]
        exact Or.inl ⟨o1, hold, hc1, e1.symm, hup.symm, rfl⟩
      | some q =>
        simp only [Option.some_or]
        right
        refine ⟨q, rfl, ?_⟩
        rcases hm.NSH_good hinv hstep hns with ⟨b, hb, rfl⟩ | ⟨-, hzD, -, href, a0, o0, ho0, hq0⟩
        · -- the pointee's live handle, with its canonical object
          left
          have hcs : ((m.applyChange sp db.P (k + 1) c).canonicalOf z).isSome = true := by
            rw [hcf.canonicalOf, hb]; rfl
          have := HMem.holdsCanonical_tableOf
            ({ ref := ((c.new.foldl addNewH m).obj? b).bind (·.pos),
               handle := (c.new.foldl addNewH m).tableOf z } : HPtr) hcs
          rw [hcf.tableOf] at this
          exact this
        · -- a copy of a pointer whose record is the pointee's latest version
          obtain ⟨hrz, -, hzw⟩ := hm.reach_child hinv hls hold hc1 hrt1 hz
          exact (HPtrHist.clean hinv hls hzD hzw ht hrz href _).keep hk (hm.tbl.ptr_handle ho0 hq0)
    · exact Or.inl ⟨o1, hold, hc1, e1.symm, hup.symm, rfl⟩
  · -- a new node is not reachable at times up to k
    exfalso
    have := hstep.fresh nn hnn
    rw [e1, hon] at hrt
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hrt))
    simp only [hnewObj] at hn
    rw [this] at hn; cases hn

/-- What `resolvePointers` makes of a pointer is as a read at t needs it, if the
pointer was: it holds a canonical object, or it is the pointer with its
reference after Rule R, which has the same slow path's reference. -/
theorem HPtrHist.resolveP {t : Time} {x z : NodeId} {p : HPtr} (h : HPtrHist sp S0 db m t x z p)
    (D : Dirty) : HPtrHist sp S0 db m t x z (m.resolveP S0 D z p) := by
  rcases HMem.resolveP_cases S0 m D z p with ⟨-, h2⟩ | ⟨-, -, hcs, h2⟩ | ⟨-, -, h2⟩
  · rw [h2]; exact h
  · rw [h2]; exact Or.inl (HMem.holdsCanonical_tableOf p hcs)
  · rw [h2]
    rcases h with h1 | ⟨r, w, h1, h2, h3⟩ | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨r, w, by rw [HMem.slowRef_ruleR]; exact h1, h2, h3⟩)
    · exact Or.inr (Or.inr h1)

/-- A memory with the same handles, startup pos and pointers that hold canonical
objects gives the same. -/
theorem HPtrHist.of_same {m' : HMem V} {t : Time} {x z : NodeId} {p : HPtr} (h : HPtrHist sp S0 db m t x z p)
    (hc : ∀ q, m'.holdsCanonical q = m.holdsCanonical q) (hs : m'.s = m.s)
    (hhd : ∀ n, m'.handle? n = m.handle? n) : HPtrHist sp S0 db m' t x z p := by
  rcases h with h1 | ⟨r, w, h1, h2, h3⟩ | h1
  · exact Or.inl (by rw [hc]; exact h1)
  · exact Or.inr (Or.inl ⟨r, w, by rw [HMem.slowRef_congr S0 hs hhd]; exact h1, h2, h3⟩)
  · exact Or.inr (Or.inr h1)

/-- The writes keep the invariant: a pointer changes only by `resolvePointers`,
and the handles stay. -/
theorem HInvH.loops {D0 D1 : Dirty} {xs1 xs2 : List NodeId} {i : Nat} {m3 m6 : HMem V}
    (hh : HInvH sp db S0 k m3) (hfr : LoopsFrameH S0 D0 D1 xs1 xs2 i m3 m6) : HInvH sp db S0 k m6 := by
  have hhd : ∀ n, m6.handle? n = m3.handle? n := by intro n; unfold HMem.handle?; rw [hfr.handles]
  intro a o6 ho6 hc6 t ht hr z hz
  obtain ⟨o3, ho3⟩ : ∃ o3, m3.obj? a = some o3 := by
    cases h3 : m3.obj? a with
    | none => rw [hfr.none a h3] at ho6; cases ho6
    | some o3 => exact ⟨o3, rfl⟩
  obtain ⟨o6', ho6', e1, -, -, e4, e5, hsl, -, -⟩ := hfr.obj a o3 ho3
  rw [ho6, Option.some.injEq] at ho6'
  subst ho6'
  obtain ⟨p, hp, hph⟩ := hh a o3 ho3 (by rw [← e5]; exact hc6) t ht (by rw [← e1]; exact hr) z
    (by rw [← e4]; exact hz)
  have hph6 : ∀ q, HPtrHist sp S0 db m3 t o3.node z q → HPtrHist sp S0 db m6 t o6.node z q := by
    intro q hq
    rw [e1]
    exact hq.of_same hfr.hc hfr.s hhd
  rcases hsl z with h | h | h
  · exact ⟨p, by rw [h]; exact hp, hph6 p hph⟩
  · exact ⟨_, by rw [h, hp]; rfl, hph6 _ (hph.resolveP D0)⟩
  · exact ⟨_, by rw [h, hp]; rfl, hph6 _ (hph.resolveP D1)⟩

end Change

/-! ## The next state -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- After the writes, the invariant of the next state: at the new time k + 1
from the live pointers of the invariant; at earlier times as before, good
versions staying good, and INV-SLOT's second half either written away (the
object's node taken, so its pointer, pinned, holds the pointee's live handle
with its canonical object) or kept (both stay in D with their indexes). -/
theorem HInvH.next (hsp : SpecOK sp) (hinv : Inv sp db k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) {m3 m6 : HMem V}
    (ha : HAInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    (hfr : LoopsFrameH S0 db.D (parts sp al db tr).D1 (dataIds sp al db tr) (parts sp al db tr).taken (k + 1)
      m3 m6)
    (hh6 : HInvH sp db S0 k m6) (hm6' : HEInv sp (step sp al db tr) S0 (k + 1) m6) :
    HInvH sp (step sp al db tr) S0 (k + 1) m6 := by
  have hls : LiveSub sp := hsp.liveSub
  have hgrow : Grow db.P k (step sp al db tr).P := step_grow sp al db tr hinv.len
  have hsext : SExt db.S (step sp al db tr).S := Snew_ext sp al db tr
  intro a o ho hc t ht hr z hz
  by_cases htk : t = k + 1
  · subst htk
    obtain ⟨n, hn, hhist, -, -⟩ := hm6'.cc a o ho hc
    have hz' : z ∈ sp.live o.hist := by
      rw [hhist] at hz ⊢
      rw [upTo_of_forall _ _ (hinv'.times _ n hn)] at hz
      exact hz
    obtain ⟨p, hp, hli1, hli2⟩ := hm6'.live a o ho hc hr z hz'
    refine ⟨p, hp, ?_⟩
    cases hzD : inD (step sp al db tr).D z with
    | true => exact Or.inl (HMem.holdsCanonical_of_holdsLive (hli1 hzD))
    | false =>
      obtain ⟨hrz, -, hzw⟩ := hm6'.reach_child hinv' hls ho hc hr hz
      exact HPtrHist.clean hinv' hls hzD hzw (Nat.le_refl _) hrz (hli2 hzD) o.node
  · have ht' : t ≤ k := by omega
    have hr0 : reachable sp db.P t o.node = true := by
      rw [reachable_iff] at hr ⊢
      exact reach_of_grow_back hls hinv.ptrs hinv.rootIn hgrow ht' hr
    obtain ⟨p, hp, hph⟩ := hh6 a o ho hc t ht' hr0 z hz
    refine ⟨p, hp, ?_⟩
    rcases hph with h1 | ⟨r, w, e1, e2, e3⟩ | ⟨hzD, -, x1, y1, hx1, hy1, hab⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨r, w, e1, hsext.versionAt e2, good_mono' sp hsext hgrow ht' e3⟩)
    · obtain ⟨o3, ho3⟩ : ∃ o3, m3.obj? a = some o3 := by
        cases h3 : m3.obj? a with
        | none => rw [hfr.none a h3] at ho; cases ho
        | some o3 => exact ⟨o3, rfl⟩
      obtain ⟨o6, ho6, e1, -, -, -, e5, -, hpin, -⟩ := hfr.obj a o3 ho3
      rw [ho, Option.some.injEq] at ho6
      subst ho6
      have hxa := mem_of_dOf hx1
      have hzb := mem_of_dOf hy1
      by_cases has : x1 ≤ (parts sp al db tr).s
      · -- o's node is taken: its pointer for z, pinned, holds z's canonical object
        left
        have hxt : o3.node ∈ (parts sp al db tr).taken :=
          (step_taken_mem sp al db tr _).mpr ⟨x1, (step_D1_mem sp al db tr hinv.len _).mpr
            (Or.inl (by rw [← e1]; exact hxa)), has⟩
        have hc3 : o3.canonical = true := by rw [← e5]; exact hc
        have hcan3 : m3.canonicalOf o3.node = some a := ha.tbl.canonicalOf_of ho3 hc3
        have hzD1 : inD (parts sp al db tr).D1 z = true :=
          (inD_iff _ _).mpr ⟨y1, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hzb)⟩
        have hcz := ha.canon z (Or.inl hzD)
        have hp6 := hpin ⟨hxt, hcan3⟩ z
        rw [hp] at hp6
        cases hq3 : o3.ptr? z with
        | none => rw [hq3] at hp6; cases hp6
        | some q =>
          rw [hq3, Option.map_some, Option.some.injEq] at hp6
          rw [hp6, hfr.hc]
          rcases HMem.resolveP_cases S0 m3 (parts sp al db tr).D1 z q with ⟨h1, h2⟩ | ⟨-, -, -, h2⟩ |
              ⟨-, h3, -⟩
          · rw [h2]; exact h1
          · rw [h2]; exact HMem.holdsCanonical_tableOf q hcz
          · exact absurd ⟨hzD1, hcz⟩ h3
      · -- both stay in D, with their indexes
        right; right
        have hxD2 : (o.node, x1) ∈ (parts sp al db tr).D2 :=
          (step_D2_mem sp al db tr _).mpr ⟨(step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hxa), by
            simp only; omega⟩
        have hzD2 : (z, y1) ∈ (parts sp al db tr).D2 :=
          (step_D2_mem sp al db tr _).mpr ⟨(step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hzb), by
            simp only; omega⟩
        have hxD' : (o.node, x1) ∈ (step sp al db tr).D := by
          show _ ∈ (parts sp al db tr).r7.1
          rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hxD2
        have hzD' : (z, y1) ∈ (step sp al db tr).D := by
          show _ ∈ (parts sp al db tr).r7.1
          rw [(step_r7_shape sp al db tr hinv.len).1]; exact List.mem_append_left _ hzD2
        exact ⟨(inD_iff _ _).mpr ⟨y1, hzD'⟩, (inD_iff _ _).mpr ⟨x1, hxD'⟩, x1, y1,
          dOf_of_mem hinv'.dNodup hxD', dOf_of_mem hinv'.dNodup hzD', hab⟩

/-- One transaction of the physical writer with handles keeps the invariant for
reads at earlier times. -/
theorem HInvH.handleTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    {m : HMem V} (hm : HEInv sp db S0 k m) (hh : HInvH sp db S0 k m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) (hev' : EvLogic sp (step sp al db tr) (k + 1)) :
    HInvH sp (step sp al db tr) S0 (k + 1) (handleTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view_ok hinv hls hev
  have hh1 : HInvH sp db S0 k (m.view sp S0 db.S k).1 := hh.read hinv hm k
  have hc : sp.exec tr db.S.length (m.view sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [handleTrans_eq, hc, handleAfter_eq]
  have hm1' : HEInv sp db S0 k (m.view sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  have hh1' : HInvH sp db S0 k (m.view sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hh1
  generalize (m.view sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' hh1' ⊢
  -- The writer's paths.
  have hpr : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hparent : ∀ x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), ∃ np nx, db.P.get? p = some np ∧
        db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k) := by
    intro x hx hxr
    have hrx := (mem_pathOf hx).1
    rw [hK1] at hrx
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent hrx hxr
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp,
      hnx, hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := HEInv.reachPath_ok (S0 := S0) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1 hm1' (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  have hh2 := HInvH.reachPath (S0 := S0) hinv hls hev hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    m1 hm1' hh1'
  -- The change.
  have ha := hm2.applyChange_ok hinv hls hpd hstep hphys hcopy htree
  have hh3 := hh2.applyChange hinv hls hm2 hstep
  have hpre : preWriteH sp S0 db (parts sp al db tr).c m1 =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWriteH; rw [hlen]; rfl
  rw [hpre, hlen]
  generalize (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
      sp db.P (k + 1) (parts sp al db tr).c = m3 at ha hh3 ⊢
  -- The writes.
  obtain ⟨e1, -, -, e4⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  rw [hdata, e1, ← parts_D1Of, ← parts_takenOf]
  have hdnd : (dataIds sp al db tr).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  have hdisj : ∀ x ∈ dataIds sp al db tr, x ∉ (parts sp al db tr).taken := by
    intro x hx hxt
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hxt
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    have := hinv.dIndex (x, d) hxd
    simp [isIndex, hnone] at this
  have hfr := loopsFrameH sp S0 db.D (parts sp al db tr).D1 (k + 1) (dataIds sp al db tr)
    (parts sp al db tr).taken m3 hdnd (step_taken_nodup sp al db tr hinv) ha.tbl hdisj
  have hm6 := ha.final_ok hsp hinv hmk hstep hinv' hev' hfr e4
  exact (hh3.loops hfr).next hsp hinv hinv' ha hfr hm6

end Next

end SIS
