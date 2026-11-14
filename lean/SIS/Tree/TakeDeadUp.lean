/-
The take-back's (C) and the node facts through the upward delete (bergdb
024-12, TP4; `J2N`, TakeDeadCollapse.lean): the building blocks. A node whose
child the transaction made is taken back has its klongs of the transaction to
the child retargeted to the node the child replaced, which is below B
(`RetFormS`); its klongs before t, first time and compare values are kept, and a
klong to the child that is left lies before its last time klong. LE-b's node
(`lebNode`) keeps the klongs before t and the first time, and its key klongs are
the node's or name the new empty key's node.
-/
import SIS.Tree.TakeDeadDelete
import SIS.Tree.TakeInvUp
import SIS.Tree.WriterGetUpLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## A node retargeted from a child taken back -/

/-- S is n, or n with its klongs of the transaction to some node pointed to a
node below B. -/
def RetFormS (t : Time) (B : NodeId) (n : KNode) (S : KNode) : Prop :=
  S = n ∨ (n.lastTime = some t ∧ ∃ src dst, dst < B ∧
    S = { n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst })

/-- S is n with its klongs of the transaction to src pointed to a node below B. -/
def RetFrom (t : Time) (B : NodeId) (n : KNode) (src : NodeId) (S : KNode) : Prop :=
  n.lastTime = some t ∧ ∃ dst, dst < B ∧
    S = { n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst }

theorem firstTime_fold_shape (l : List Klong) :
    (l.map klongShape).findSome? (fun k => match k with
      | .time x => some x
      | _ => none) =
    l.findSome? (fun k => match k with
      | .time x => some x
      | _ => none) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.findSome?_cons]
    cases a <;> simp [klongShape, ih]

theorem KNode.firstTime_of_shapeOf {a b : KNode} (h : a.shapeOf = b.shapeOf) :
    a.firstTime = b.firstTime := by
  have ha : a.shapeOf.firstTime = a.firstTime := by
    unfold KNode.firstTime KNode.shapeOf; exact firstTime_fold_shape a.ks
  have hb : b.shapeOf.firstTime = b.firstTime := by
    unfold KNode.firstTime KNode.shapeOf; exact firstTime_fold_shape b.ks
  rw [← ha, h, hb]

theorem retFormS_shape (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) : S.shapeOf = n.shapeOf := by
  rcases h with rfl | ⟨_, src, dst, _, rfl⟩
  · rfl
  · exact KNode.retarget_shapeOf _ _ _ _

theorem retFormS_leaf (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) : S.leaf = n.leaf := by
  rcases h with rfl | ⟨_, src, dst, _, rfl⟩ <;> rfl

theorem retFormS_firstTime (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) : S.firstTime = n.firstTime :=
  KNode.firstTime_of_shapeOf (retFormS_shape t B n S h)

theorem retFormS_lastTime (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) : S.lastTime = n.lastTime :=
  KNode.lastTime_of_shapeOf (retFormS_shape t B n S h)

theorem retFormS_agree (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) (ti : Nat) (hti : n.lastTimeIndex = some ti) :
    ∀ j, j ≤ ti → S.ks[j]? = n.ks[j]? := by
  rcases h with rfl | ⟨_, src, dst, _, rfl⟩
  · intro _ _; rfl
  · intro j hj
    rw [hti]
    exact retargetKlongs_le n.ks ti src dst j hj

theorem retFormS_prefix (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) (hpos : 0 < t) : prefixAt S.ks (t - 1) = prefixAt n.ks (t - 1) := by
  rcases h with rfl | ⟨hlt, src, dst, hd, rfl⟩
  · rfl
  · obtain ⟨ti, hti, hk⟩ := KNode.lastTime_anchor n t hlt
    exact prefixAt_agree n.ks _ t ti hpos hk
      (retFormS_agree t B n _ (Or.inr ⟨hlt, src, dst, hd, rfl⟩) ti hti)

/-- A key klong of S names a node below B, or is n's. -/
theorem retFormS_key (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) (i c : Nat) (y : NodeId) (hk : S.ks[i]? = some (Klong.key c y)) :
    y < B ∨ n.ks[i]? = some (Klong.key c y) := by
  rcases h with rfl | ⟨_, src, dst, hdst, rfl⟩
  · exact Or.inr hk
  · rcases retargetKlongs_key n.ks _ src dst i c y hk with he | ⟨h1, _⟩
    · left; rw [he]; exact hdst
    · exact Or.inr h1

/-- A key klong of S retargeted from src names a node below B, or is n's, and if
it names src it lies before n's last time klong. -/
theorem retFrom_key (t : Time) (B : NodeId) (n : KNode) (src : NodeId) (S : KNode)
    (h : RetFrom t B n src S) (i c : Nat) (y : NodeId) (hk : S.ks[i]? = some (Klong.key c y)) :
    y < B ∨ (n.ks[i]? = some (Klong.key c y) ∧
      (y = src → ∃ ti, n.lastTimeIndex = some ti ∧ i ≤ ti)) := by
  obtain ⟨hlt, dst, hdst, rfl⟩ := h
  rcases retargetKlongs_key n.ks _ src dst i c y hk with he | ⟨h1, h2⟩
  · left; rw [he]; exact hdst
  · right
    refine ⟨h1, fun hy => ?_⟩
    obtain ⟨ti, hti, _⟩ := KNode.lastTime_anchor n t hlt
    refine ⟨ti, hti, ?_⟩
    rw [hti] at h2
    rcases Nat.lt_or_ge ti i with hlt' | hge
    · exact absurd hy (h2 hlt')
    · exact hge

/-- Retargeting keeps the last live klongs. -/
theorem retFormS_lastLive (t : Time) (B : NodeId) (n : KNode) (S : KNode)
    (h : RetFormS t B n S) (i c : Nat) (hl : LastLive n.ks n.lastBitmap i c) :
    LastLive S.ks S.lastBitmap i c := by
  rw [KNode.lastBitmap_of_shapeOf (retFormS_shape t B n S h)]
  rcases h with rfl | ⟨_, src, dst, _, rfl⟩
  · exact hl
  · obtain ⟨⟨y, hy⟩, hni, hlater⟩ := hl
    refine ⟨?_, hni, fun j y' hij hj => ?_⟩
    · simp only
      rw [retargetKlongs_get, hy]
      simp only [Option.map_some, retargetStep]
      split
      · exact ⟨_, rfl⟩
      · exact ⟨y, rfl⟩
    · simp only at hj
      rw [retargetKlongs_get] at hj
      cases hk : n.ks[j]? with
      | none => rw [hk] at hj; cases hj
      | some k =>
        rw [hk] at hj
        simp only [Option.map_some, Option.some.injEq] at hj
        cases k with
        | key c2 z =>
          simp only [retargetStep] at hj
          have hc2 : c2 = c := by split at hj <;> (simp only [Klong.key.injEq] at hj; exact hj.1)
          rw [hc2] at hk
          exact hlater j z hij hk
        | time u => simp [retargetStep] at hj
        | del b => simp [retargetStep] at hj

/-! ## The take-back with its retarget exactly -/

/-- `retarget` of p's node n at t: n's klongs of the transaction to src point to
dst. -/
theorem writerWP_retarget_exactT (p src dst : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some n) (hlt : n.lastTime = some c.i) :
    WriterWP (retarget p src dst) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧ w'.next = w.next ∧
      (∀ y, y ≠ p → w'.nodes.lookup y = w.nodes.lookup y) ∧
      w'.nodes.lookup p = some { n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst }) := by
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p n c w hlk]
  simp only [hlt, beq_self_eq_true, ↓reduceIte]
  unfold putNode
  refine (writerWP_modify _ c w _).mpr ?_
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_, ?_⟩
  · show (upsert w.nodes p _).lookup y = _
    rw [lookup_upsert]; simp [hy]
  · show (upsert w.nodes p _).lookup p = _
    rw [lookup_upsert]; simp only [↓reduceIte]; rfl

/-- `takeBack` of x with parent p: x is taken, p's node is retargeted from x to
the node x replaced, and p's node is of time t. -/
theorem writerWP_takeBack_exact (x p : NodeId) (cv : Nat) (pn : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup p = some pn) :
    WriterWP (takeBack x p cv) c w (fun _ w' => w'.taken = x :: w.taken ∧ w'.top = w.top ∧
      w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧ w'.next = w.next ∧
      (∀ y, y ≠ p → w'.nodes.lookup y = w.nodes.lookup y) ∧
      pn.lastTime = some c.i ∧ ∃ old, w.madeFor.lookup x = some old ∧
        w'.nodes.lookup p = some { pn with ks := retargetKlongs pn.ks (pn.lastTimeIndex.getD 0) x old }) := by
  unfold takeBack replacedBy
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c w hlk]
  simp only [writerWP_get, writerWP_pure]
  split
  · rename_i old _ hmf _
    split
    · exact writerWP_throw _ _ _ _
    · rename_i hne
      have hlt : pn.lastTime = some c.i := by simpa using hne
      rw [writerWP_bind]
      refine writerWP_mono (writerWP_retarget_exactT p x old pn c w hlk hlt) ?_
      rintro _ w1 ⟨h1t, h1top, h1v, h1p, h1m, h1nx, h1n, h1l⟩
      rw [writerWP_bind]
      refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
      refine (writerWP_note_iff _ c _ _).mpr ?_
      exact ⟨by simp [h1t], h1top, h1v, h1p, h1m, h1nx, h1n, hlt, old, hmf, h1l⟩
  · exact writerWP_throw _ _ _ _

/-! ## LE-b exactly -/

/-- `writerWP_emptyKeyNext_room_frame` with x's node after exactly LE-b's
(`lebNode`), its bitmap set in place only after a bitmap of the transaction, its
empty key pointed in place only after the last time klong of t. -/
theorem writerWP_emptyKeyNext_room_exact (x : NodeId) (depth : Nat) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n)
    (hwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hroom : n.size + 3 ≤ c.p.M)
    (hdead : ∀ b1 b2 e jcv jy, deadOver c.p (lebNode n c.i b1 b2 e jcv jy) = false) :
    WriterWP (emptyKeyNext x depth) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w'.next = w.next ∧ w'.madeFor = w.madeFor ∧
      ∃ n' jcv jy, w'.nodes = upsert w.nodes x n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧ (jcv, jy) ∈ n.liveAt c.i ∧ 0 < jcv ∧
        (∀ c' z, (c', z) ∈ n.live → c' ≠ 0 → jcv ≤ c') ∧
        (∀ c', n'.live.lookup c' = if c' = 0 then some jy else if c' = jcv then none else n.live.lookup c') ∧
        ∃ htd lip e0, n' = lebNode n c.i htd lip e0 jcv jy ∧
          (htd = true → (∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
          (lip = true → n.lastTime = some c.i ∧ ∃ ti, n.lastTimeIndex = some ti ∧ ti < e0)) := by
  unfold emptyKeyNext
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · rename_i e0 j0 jcv jy hE hJ
    have hJ' : n.ks.zipIdx.foldl (lebStep (bitsUnion n.lastBitmap (n.bitsOf 0))) none =
        some (j0, jcv, jy) := hJ
    obtain ⟨hkj, hjd, hjl⟩ := lebOK_fold _ n.ks j0 jcv jy hJ'
    have hmin := leb_min_live n j0 jcv jy hJ'
    have hb0 : j0 ∉ n.bitsOf 0 := fun h => hjd ((mem_bitsUnion_iff _ _ _).mpr (Or.inr h))
    have hj0 : jcv ≠ 0 := by
      intro h; subst h
      exact hb0 ((n.mem_bitsOf_iff 0 j0).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hkj⟩)
    have hLL : LastLive n.ks n.lastBitmap j0 jcv := by
      refine ⟨⟨jy, hkj⟩, fun h => hjd ((mem_bitsUnion_iff _ _ _).mpr (Or.inl h)), ?_⟩
      intro j y' hij hj
      rcases (mem_bitsUnion_iff _ _ _).mp (hjl j y' hij hj) with h | h
      · exact h
      · obtain ⟨y'', hy''⟩ := (n.mem_bitsOf_iff 0 j).mp h
        rw [List.mem_zipIdx_iff_getElem?.mp hy''] at hj
        simp only [Option.some.injEq, Klong.key.injEq] at hj
        exact absurd hj.1.symm hj0
    have hjlive : (jcv, jy) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]
      apply mem_of_lookup_nodup
      rw [KNode.live_lookup]
      exact keyLookup_of_last _ _ _ j0 jy hkj hLL
    have hne : bitsUnion n.lastBitmap (n.bitsOf jcv) ≠ n.lastBitmap := by
      intro he
      have : j0 ∈ bitsUnion n.lastBitmap (n.bitsOf jcv) := (mem_bitsUnion_iff _ _ _).mpr
        (Or.inr ((n.mem_bitsOf_iff jcv j0).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hkj⟩))
      rw [he] at this
      exact hLL.2.1 this
    have he0 : ∃ y0, n.ks[e0]? = some (.key 0 y0) := by
      have hm : e0 ∈ n.bitsOf 0 := List.mem_of_getLast? hE
      obtain ⟨y0, hy0⟩ := (n.mem_bitsOf_iff 0 e0).mp hm
      exact ⟨y0, List.mem_zipIdx_iff_getElem?.mp hy0⟩
    obtain ⟨y0, hy0⟩ := he0
    have helast : ∀ j y', e0 < j → n.ks[j]? = some (.key 0 y') → False := by
      intro j y' hj hjk
      have hm : j ∈ n.bitsOf 0 := (n.mem_bitsOf_iff 0 j).mpr ⟨y', List.mem_zipIdx_iff_getElem?.mpr hjk⟩
      have := bitsOf_le_last n 0 e0 hE j hm
      omega
    have htdh : ∀ b : Bool, (b = ((match n.ks.getLast? with
        | some (.del _) => true
        | _ => false) && n.lastTime == some c.i)) → b = true → ∃ old, n.ks.getLast? = some (.del old) := by
      intro b hb h
      rw [hb] at h
      cases hg : n.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hed => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    have helive : e0 ∉ n.lastBitmap := by simpa using hed
    apply writerWP_ite_true _ (Nat.le_trans (Nat.add_le_add_left (need_le_three _ _ _) _) hroom)
    apply writerWP_ite_false _ (fun hd => absurd (hd.symm.trans (hdead _ _ e0 jcv jy)) (by decide))
    simp only [note, putNode, writerWP_bind, writerWP_modify]
    obtain ⟨hw', ht'⟩ := lebNode_wf_times n c.i _ _ e0 jcv jy hwf hnt (htdh _ rfl) hne
    refine ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, jcv, jy, rfl,
      lebNode_leaf _ _ _ _ _ _ _, hw', ht', hjlive, Nat.pos_of_ne_zero hj0,
      fun c' z hm hc => hmin c' z hm hc, ?_, _, _, e0, rfl, ?_, ?_⟩
    · intro c'
      exact lebNode_live_lookup n c.i _ _ e0 jcv jy y0 hwf (htdh _ rfl) hy0 helive helast hj0 hne c'
    · intro h
      refine ⟨htdh _ rfl h, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.2
    · intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨h1, ?_⟩
      split at h2
      · rename_i ti hti
        exact ⟨ti, hti, by simpa using h2⟩
      · cases h2
  · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

/-! ## LE-b's node -/

theorem key_set_get (ks : List Klong) (j : Nat) (k : Klong) (i c : Nat) (y : NodeId)
    (h : (ks.set j k)[i]? = some (Klong.key c y)) : ks[i]? = some (Klong.key c y) ∨ (i = j ∧ k = Klong.key c y) := by
  by_cases hij : i = j
  · subst hij
    rw [List.getElem?_set_self'] at h
    cases hk : ks[i]? with
    | none => rw [hk] at h; cases h
    | some k0 => rw [hk] at h; simp at h; exact Or.inr ⟨rfl, h⟩
  · rw [List.getElem?_set_ne (Ne.symm hij)] at h; exact Or.inl h

theorem key_add_get (n : KNode) (t : Time) (k : Klong) (i c : Nat) (y : NodeId)
    (h : (n.add t k).ks[i]? = some (Klong.key c y)) : n.ks[i]? = some (Klong.key c y) ∨ k = Klong.key c y := by
  rcases Nat.lt_or_ge i n.ks.length with hi | hi
  · left
    rcases KNode.add_ks n t k with he | he <;> rw [he, List.getElem?_append_left hi] at h <;> exact h
  · right
    rcases KNode.add_ks n t k with he | he <;> rw [he, List.getElem?_append_right hi] at h <;>
      have hm := List.mem_of_getElem? h
    · rcases List.mem_cons.mp hm with hm | hm
      · cases hm
      · exact (List.mem_singleton.mp hm).symm
    · exact (List.mem_singleton.mp hm).symm

/-- A key klong of LE-b's node is the node's, or names jy. -/
theorem lebNode_key (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId)
    (htdh : htd = true → ∃ old, n.ks.getLast? = some (.del old))
    (i c : Nat) (y : NodeId) (h : (lebNode n tt htd lip e jcv jy).ks[i]? = some (Klong.key c y)) :
    n.ks[i]? = some (Klong.key c y) ∨ y = jy := by
  have h1 : ∀ n1 : KNode, (∀ (i c : Nat) (y : NodeId), n1.ks[i]? = some (Klong.key c y) →
      n.ks[i]? = some (Klong.key c y)) →
      ((if lip then n1.repoint e jy else n1.add tt (.key 0 jy)).ks[i]? = some (Klong.key c y)) →
      n.ks[i]? = some (Klong.key c y) ∨ y = jy := by
    intro n1 hn1 h
    cases lip with
    | true =>
      simp only [↓reduceIte] at h
      unfold KNode.repoint at h
      split at h
      · simp only [KNode.setAt] at h
        rcases key_set_get n1.ks e _ i c y h with h | ⟨_, h⟩
        · exact Or.inl (hn1 i c y h)
        · simp only [Klong.key.injEq] at h; exact Or.inr h.2.symm
      · exact Or.inl (hn1 i c y h)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases key_add_get n1 tt _ i c y h with h | h
      · exact Or.inl (hn1 i c y h)
      · simp only [Klong.key.injEq] at h; exact Or.inr h.2.symm
  unfold lebNode at h
  apply h1 _ _ h
  intro i c y hk
  cases htd with
  | true =>
    simp only [↓reduceIte, KNode.setAt] at hk
    rcases key_set_get n.ks _ _ i c y hk with h | ⟨_, h⟩
    · exact h
    · cases h
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hk
    rcases key_add_get n tt _ i c y hk with h | h
    · exact h
    · cases h

/-- LE-b's node agrees with the node up to its time klong of tt at ti when what
it sets in place lies after ti. -/
theorem lebNode_agree_at (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId)
    (ti : Nat) (hk : n.ks[ti]? = some (.time tt)) (htdh : htd = true → ti < n.size - 1)
    (hlip : lip = true → ti < e) :
    ∀ i, i ≤ ti → (lebNode n tt htd lip e jcv jy).ks[i]? = n.ks[i]? := by
  have htil : ti < n.ks.length := (List.getElem?_eq_some_iff.mp hk).1
  have hadd : ∀ (m : KNode) (k : Klong), ti < m.ks.length →
      (∀ i, i ≤ ti → m.ks[i]? = n.ks[i]?) → ∀ i, i ≤ ti → (m.add tt k).ks[i]? = n.ks[i]? := by
    intro m k hl hm i hi
    rcases KNode.add_ks m tt k with h | h <;> rw [h, List.getElem?_append_left (by omega)] <;>
      exact hm i hi
  have hlen : ∀ (m : KNode) (k : Klong), ti < m.ks.length → ti < (m.add tt k).ks.length := by
    intro m k hl
    rcases KNode.add_ks m tt k with h | h <;> rw [h] <;> simp <;> omega
  have h0 : ∀ i, i ≤ ti → n.ks[i]? = n.ks[i]? := fun _ _ => rfl
  have h1 : ti < (if htd then n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))
      else n.add tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))).ks.length ∧
      ∀ i, i ≤ ti → (if htd then n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))
        else n.add tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))).ks[i]? = n.ks[i]? := by
    cases htd with
    | true =>
      have := htdh rfl
      simp only [KNode.size] at this
      simp only [↓reduceIte, KNode.setAt, List.length_set]
      refine ⟨htil, fun i hi => ?_⟩
      rw [List.getElem?_set_ne (by simp only [KNode.size]; omega)]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨hlen n _ htil, hadd n _ htil h0⟩
  obtain ⟨hl1, ha1⟩ := h1
  unfold lebNode
  cases lip with
  | true =>
    simp only [↓reduceIte]
    intro i hi
    unfold KNode.repoint
    split
    · simp only [KNode.setAt]
      rw [List.getElem?_set_ne (by have := hlip rfl; omega)]
      exact ha1 i hi
    · exact ha1 i hi
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hadd _ _ hl1 ha1

/-- LE-b's node keeps the klongs before tt and the first time. -/
theorem lebNode_facts (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId)
    (hpos : 0 < tt) (hpt : ∀ s, Klong.time s ∈ n.ks → s ≤ tt)
    (htdh : htd = true → (∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some tt)
    (hlip : lip = true → n.lastTime = some tt ∧ ∃ ti, n.lastTimeIndex = some ti ∧ ti < e) :
    prefixAt (lebNode n tt htd lip e jcv jy).ks (tt - 1) = prefixAt n.ks (tt - 1) ∧
    ∀ s, n.firstTime = some s → (lebNode n tt htd lip e jcv jy).firstTime = some s := by
  by_cases hof : n.lastTime = some tt
  · obtain ⟨ti, hti, hk⟩ := KNode.lastTime_anchor n tt hof
    have hag := lebNode_agree_at n tt htd lip e jcv jy ti hk ?_ ?_
    · refine ⟨prefixAt_agree n.ks _ tt ti hpos hk hag, fun s hs => ?_⟩
      rw [KNode.firstTime_agree n _ ti tt hk hag]; exact hs
    · intro h
      obtain ⟨⟨old, hl⟩, _⟩ := htdh h
      simp only [KNode.size]
      have htl : ti < n.ks.length := (List.getElem?_eq_some_iff.mp hk).1
      have hne : ti ≠ n.ks.length - 1 := by
        intro he
        rw [List.getLast?_eq_getElem?, ← he, hk] at hl
        cases hl
      omega
    · intro h
      obtain ⟨_, ti', hti', hlt⟩ := hlip h
      rw [hti] at hti'; cases hti'; exact hlt
  · have htd0 : htd = false := by
      cases htd with
      | false => rfl
      | true => exact absurd (htdh rfl).2 hof
    have hlip0 : lip = false := by
      cases lip with
      | false => rfl
      | true => exact absurd (hlip rfl).1 hof
    subst htd0 hlip0
    have hlt : ∀ u, n.lastTime = some u → u < tt := by
      intro u hu
      obtain ⟨m, -, hm⟩ := KNode.lastTime_anchor n u hu
      have := hpt u (List.mem_of_getElem? hm)
      have hne : u ≠ tt := fun he => hof (by rw [hu, he])
      omega
    have hks : ∃ more, (lebNode n tt false false e jcv jy).ks = n.ks ++ more ∧
        more.head? = some (.time tt) := by
      unfold lebNode
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases KNode.add_ks (n.add tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))) tt (.key 0 jy) with h | h
      · rw [h, KNode.add_ks_time n tt _ hlt]
        exact ⟨[.time tt, .del (bitsUnion n.lastBitmap (n.bitsOf jcv)), .time tt, .key 0 jy], by simp, rfl⟩
      · rw [h, KNode.add_ks_time n tt _ hlt]
        exact ⟨[.time tt, .del (bitsUnion n.lastBitmap (n.bitsOf jcv)), .key 0 jy], by simp, rfl⟩
    obtain ⟨more, hm, hh⟩ := hks
    refine ⟨?_, fun s hs => ?_⟩
    · rw [hm]
      exact prefixAt_append_stop n.ks more (tt - 1) tt (by omega) (Or.inr hh)
    · unfold KNode.firstTime at hs ⊢
      rw [hm, List.findSome?_append, hs]
      rfl

/-! ## (C) and the node facts after the upward delete, at node-map level -/

/-- A chain node after the upward delete: taken back if the transaction made it,
else unlinked from its node, perhaps retargeted. -/
def ChainFateN (N' : NodeId → Option KNode) (t : Time) (B : NodeId) (n : KNode) (x : NodeId) : Prop :=
  (n.firstTime = some t → N' x = none) ∧
  (n.firstTime ≠ some t → ∃ S, RetFormS t B n S ∧ N' x = some (unlinkedNode S t))

/-- (C) and the node facts after the upward delete, before root collapse: the
chain below the stop node taken back or unlinked (`ChainFateN`); the stop node
from S, its node retargeted from the chain's top if the transaction made it,
with S's klongs before t and first time, S's key klongs or klongs to nodes
`Extra` names (which it names live, in an inner node), every live child of the
stop node but the chain's kept, and in a leaf the last live klongs but the
chain's kept. -/
theorem j2rest_up (N N' : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (stop depth cs : Nat) (hsD : stop < depth) (hpos : 0 < t)
    (hD : DeadLiveN N t B vals) (hO : OldBelowN N t B) (hS : OldStartN N t B)
    (hM : MadeStartN N t B) (hV : ValsNoNodeN N vals)
    (hN : ∀ i, stop ≤ i → i ≤ depth → N (X i) = some (Nn i))
    (hdist : ∀ i i', stop ≤ i → i ≤ depth → stop ≤ i' → i' ≤ depth → X i = X i' → i = i')
    (hfate : ∀ k, stop < k → k ≤ depth → ChainFateN N' t B (Nn k) (X k))
    (hwfs : klongsWf (Nn stop).ks = true) (hts : ∀ s, Klong.time s ∈ (Nn stop).ks → s ≤ t)
    (hlink : (cs, X (stop + 1)) ∈ (Nn stop).liveAt t)
    (S sn' : KNode) (Extra : NodeId → Prop) (hSf : RetFormS t B (Nn stop) S)
    (hSm : (Nn (stop + 1)).firstTime = some t → RetFrom t B (Nn stop) (X (stop + 1)) S)
    (hsn : N' (X stop) = some sn')
    (hspre : prefixAt sn'.ks (t - 1) = prefixAt S.ks (t - 1))
    (hsft : ∀ s, S.firstTime = some s → sn'.firstTime = some s)
    (hskey : ∀ (i c : Nat) (y : NodeId), sn'.ks[i]? = some (Klong.key c y) →
      S.ks[i]? = some (Klong.key c y) ∨ Extra y)
    (hsextra : ∀ y, Extra y → (∃ c, (c, y) ∈ sn'.liveAt t) ∧ sn'.leaf = false)
    (hskeep : ∀ c y, (c, y) ∈ (Nn stop).liveAt t → c ≠ cs → ∃ c', (c', y) ∈ sn'.liveAt t)
    (hsleaf : sn'.leaf = true → S.leaf = true ∧
      ∀ (i c : Nat), LastLive S.ks S.lastBitmap i c → c ≠ cs → LastLive sn'.ks sn'.lastBitmap i c)
    (hother : ∀ u, u ≠ X stop → (∀ k, stop < k → k ≤ depth → u ≠ X k) → N' u = N u) :
    DeadLiveN N' t B vals ∧ OldBelowN N' t B ∧ OldStartN N' t B ∧ MadeStartN N' t B ∧
      ValsNoNodeN N' vals := by
  have hNs := hN stop (Nat.le_refl _) (by omega)
  have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
    fun k h1 h2 he => by have := hdist _ _ (Nat.le_refl _) (by omega) (by omega) h2 he; omega
  -- the stop node's prefix and first time
  have hspre' : prefixAt sn'.ks (t - 1) = prefixAt (Nn stop).ks (t - 1) := by
    rw [hspre, retFormS_prefix t B (Nn stop) S hSf hpos]
  have hsft' : ∀ s, (Nn stop).firstTime = some s → sn'.firstTime = some s := by
    intro s hs; apply hsft; rw [retFormS_firstTime t B (Nn stop) S hSf]; exact hs
  -- a klong of the stop node's node to the chain's top at or above B is none left
  have hnotop : ∀ (i c : Nat), S.ks[i]? = some (Klong.key c (X (stop + 1))) → B ≤ X (stop + 1) → False := by
    intro i c hk hB
    have hmade := hM _ _ (hN (stop + 1) (by omega) (by omega)) hB
    rcases retFrom_key t B (Nn stop) (X (stop + 1)) S (hSm hmade) i c _ hk with h | ⟨h1, h2⟩
    · omega
    · obtain ⟨ti, hti, hle⟩ := h2 rfl
      obtain ⟨hlt, _⟩ := hSm hmade
      obtain ⟨ti', hti', hk'⟩ := KNode.lastTime_anchor (Nn stop) t hlt
      rw [hti] at hti'; cases hti'
      have hne : i ≠ ti := fun he => by rw [he, hk'] at h1; cases h1
      have hm := key_before_last_time (Nn stop).ks t ti hwfs hk' i (by omega) _ h1
      have := hO _ _ hNs c _ hm
      omega
  -- (C) at the stop node
  have hDs : DeadLiveK sn' t B vals := by
    intro i c' y hi hB hv
    rcases hskey i c' y hi with hS' | hE
    · have hSB : ¬ y < B := by omega
      rcases retFormS_key t B (Nn stop) S hSf i c' y hS' with h | h0
      · exact absurd h hSB
      · obtain ⟨⟨c, hc⟩, hleafN⟩ := hD _ _ hNs i c' y h0 hB hv
        have hccs : c ≠ cs := by
          intro he
          rw [he] at hc
          have := KNode.liveAt_fun _ _ _ _ _ hlink hc
          rw [← this] at hS' hB
          exact hnotop i c' hS' hB
        refine ⟨hskeep c y hc hccs, fun hl => ?_⟩
        obtain ⟨hSl, hLL⟩ := hsleaf hl
        have hNl : (Nn stop).leaf = true := by rw [← retFormS_leaf t B (Nn stop) S hSf]; exact hSl
        have hL0 := hleafN hNl
        have hc'cs : c' ≠ cs := by
          intro he
          rw [he] at hL0 h0 hS'
          have hlv := liveAt_of_lastLive (Nn stop) t hts i cs y h0 hL0
          have := KNode.liveAt_fun _ _ _ _ _ hlink hlv
          rw [← this] at hS' hB
          exact hnotop i cs hS' hB
        exact hLL i c' (retFormS_lastLive t B (Nn stop) S hSf i c' hL0) hc'cs
    · obtain ⟨hlive, hinner⟩ := hsextra y hE
      exact ⟨hlive, fun hl => by rw [hinner] at hl; cases hl⟩
  -- a chain node unlinked: below B, its node's facts
  have hunl : ∀ k, stop < k → k ≤ depth → ∀ un, N' (X k) = some un →
      X k < B ∧ ∃ S0, RetFormS t B (Nn k) S0 ∧ un = unlinkedNode S0 t := by
    intro k h1 h2 un hun
    obtain ⟨hm, hu⟩ := hfate k h1 h2
    by_cases hf : (Nn k).firstTime = some t
    · rw [hm hf] at hun; cases hun
    · obtain ⟨S0, hS0, he⟩ := hu hf
      rw [he] at hun; cases hun
      exact ⟨lt_of_firstTime_ne N t B hM _ _ (hN k (by omega) h2) hf, S0, hS0, rfl⟩
  have hunpre : ∀ k, stop < k → k ≤ depth → ∀ S0, RetFormS t B (Nn k) S0 →
      prefixAt (unlinkedNode S0 t).ks (t - 1) = prefixAt (Nn k).ks (t - 1) := by
    intro k _ _ S0 hS0
    rw [(unlinked_facts S0 t hpos).1, retFormS_prefix t B (Nn k) S0 hS0 hpos]
  have hchain : ∀ u, (∃ k, stop < k ∧ k ≤ depth ∧ u = X k) ∨ u = X stop ∨ N' u = N u := by
    intro u
    by_cases h : ∃ k, stop < k ∧ k ≤ depth ∧ u = X k
    · exact Or.inl h
    · by_cases hs : u = X stop
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr (hother u hs (fun k h1 h2 he => h ⟨k, h1, h2, he⟩)))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u un hu i cv y hi hB hv
    rcases hchain u with ⟨k, h1, h2, rfl⟩ | rfl | he
    · obtain ⟨hkB, S0, hS0, rfl⟩ := hunl k h1 h2 un hu
      unfold unlinkedNode at hi
      split at hi
      · have hm : Klong.key cv y ∈ prefixAt S0.ks (t - 1) := List.mem_of_getElem? hi
        rw [retFormS_prefix t B (Nn k) S0 hS0 hpos] at hm
        have := hO _ _ (hN k (by omega) h2) cv y hm
        omega
      · rename_i hne
        have hlt0 := retFormS_lastTime t B (Nn k) S0 hS0
        have hS0n : S0 = Nn k := by
          rcases hS0 with h | ⟨hlt, _⟩
          · exact h
          · exfalso; apply hne; rw [hlt0, hlt]; simp
        subst hS0n
        have := hD _ _ (hN k (by omega) h2) i cv y hi hB hv
        unfold unlinkedNode
        simp only [hne, Bool.false_eq_true, ↓reduceIte]
        exact this
    · rw [hsn] at hu; cases hu; exact hDs i cv y hi hB hv
    · rw [he] at hu; exact hD u un hu i cv y hi hB hv
  · intro u un hu cv y hk
    rcases hchain u with ⟨k, h1, h2, rfl⟩ | rfl | he
    · obtain ⟨_, S0, hS0, rfl⟩ := hunl k h1 h2 un hu
      rw [hunpre k h1 h2 S0 hS0] at hk
      exact hO _ _ (hN k (by omega) h2) cv y hk
    · rw [hsn] at hu; cases hu
      rw [hspre'] at hk; exact hO _ _ hNs cv y hk
    · rw [he] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    rcases hchain u with ⟨k, h1, h2, rfl⟩ | rfl | he
    · obtain ⟨_, S0, hS0, rfl⟩ := hunl k h1 h2 un hu
      obtain ⟨s, hs, hf⟩ := hS _ _ (hN k (by omega) h2) huB
      refine ⟨s, hs, (unlinked_facts S0 t hpos).2 s hs ?_⟩
      rw [retFormS_firstTime t B (Nn k) S0 hS0]; exact hf
    · rw [hsn] at hu; cases hu
      obtain ⟨s, hs, hf⟩ := hS _ _ hNs huB
      exact ⟨s, hs, hsft' s hf⟩
    · rw [he] at hu; exact hS u un hu huB
  · intro u un hu huB
    rcases hchain u with ⟨k, h1, h2, rfl⟩ | rfl | he
    · have := (hunl k h1 h2 un hu).1; omega
    · rw [hsn] at hu; cases hu
      exact hsft' t (hM _ _ hNs huB)
    · rw [he] at hu; exact hM u un hu huB
  · intro y hy
    rcases hchain y with ⟨k, h1, h2, rfl⟩ | rfl | he
    · have := hV _ hy; rw [hN k (by omega) h2] at this; cases this
    · have := hV _ hy; rw [hNs] at this; cases this
    · rw [he]; exact hV y hy

end SIS.Tree
