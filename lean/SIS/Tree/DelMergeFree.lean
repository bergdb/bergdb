/-
The merge's `checkFree` (bergdb 024-12, section 1): before the merge takes back
a node o that the transaction made, no kept node holds o. The argument looks
ahead to the merge's end: there the take-back's node facts hold (`TakeJ2`, the
reached nodes untaken), so a node kept to the end that held o live would be
reached and would reach o, which is taken back (`noHolder_end`). The nodes that
the rest of the merge changes, its parent p and the other node merged, are seen
at the check itself (`holderFree_of_end`).
-/
import SIS.Tree.DelHoleClimb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The merge's end: the take-back's facts that the look-ahead uses. -/
def MergeEnd (c : Ctx) (base : View BVal) (B : NodeId) (v : W) : Prop :=
  TtReachedN (wNode c.p base v) c.i v.top.rootKey ∧ OldBelowN (wNode c.p base v) c.i B ∧
  TimesN (wNode c.p base v) c.i ∧
  (∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false)

/-- At the merge's end no kept node holds a node of the transaction that is taken back. -/
theorem noHolder_end (c : Ctx) (base : View BVal) (B : NodeId) (hpos : 0 < c.i) (vE : W)
    (hE : MergeEnd c base B vE) (o : NodeId) (hBo : B ≤ o) (hto : vE.taken.contains o = true)
    (q : NodeId) (n : KNode) (hq : vE.nodes.lookup q = some n) (htq : vE.taken.contains q = false)
    (cv : Nat) : (cv, o) ∉ n.live := by
  intro hl
  obtain ⟨hTt, hO, hTi, hU⟩ := hE
  have hw : wNode c.p base vE q = some n := by
    unfold wNode; rw [htq]; simp [hq]
  have hla : (cv, o) ∈ n.liveAt c.i := by
    rw [KNode.liveAt_of_times n c.i (hTi q n hw)]; exact hl
  have hk : Klong.key cv o ∈ n.ks := KNode.liveAt_key_mem n c.i cv o hla
  have htm := time_of_new _ c.i B hpos hO hTi q n hw cv o hk hBo
  have hr : TReach (wNode c.p base vE) c.i vE.top.rootKey o := TReach.link (hTt q n hw htm) ⟨n, hw, hla⟩
  have := hU o hr
  rw [hto] at this
  cases this

/-- `checkFree o` passes at s when the merge's end vE has its facts, o is taken
back there, the root is the same, nothing taken is given back, and every kept
cached node either keeps its node to vE or holds no live klong to o. -/
theorem holderFree_of_end (c : Ctx) (base : View BVal) (B : NodeId) (hvg : ViewGood B c) (s : W)
    (o : NodeId) (hBo : B ≤ o) (vE : W) (hE : MergeEnd c base B vE) (hoE : vE.taken.contains o = true)
    (htop : vE.top = s.top) (hcg : CacheGood B c s) (hnd : (s.nodes.map Prod.fst).Nodup)
    (hX : ∀ q n, s.nodes.lookup q = some n → s.taken.contains q = false →
      (vE.nodes.lookup q = some n ∧ vE.taken.contains q = false) ∨ (∀ cv, (cv, o) ∉ n.live)) :
    holderFree c s o = true := by
  have hpos := hvg.pos
  unfold holderFree
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false,
    beq_iff_eq, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨q, n⟩ hq
    simp only
    by_cases htq : s.taken.contains q = true
    · exact Or.inl htq
    right
    have hlq := lookup_of_mem_nodup _ hnd q n hq
    have hgq : Good B c q n := hcg.2 (q, n) hq
    refine ⟨?_, ?_⟩
    · rintro ⟨cv, z⟩ he hz
      simp only at hz
      subst hz
      rcases hX q n hlq (by simpa using htq) with ⟨h1, h2⟩ | h
      · exact noHolder_end c base B hpos vE hE z hBo hoE q n h1 h2 cv he
      · exact h cv he
    · rintro ⟨cv, z⟩ he hz
      simp only at hz
      subst hz
      obtain ⟨c0, hk⟩ := live_key_mem _ cv z he
      have := ptr_lt_of_prefix B c hvg q n hgq c0 z hk
      omega
  · intro he
    have hr : TReach (wNode c.p base vE) c.i vE.top.rootKey vE.top.rootKey := TReach.root
    have := hE.2.2.2 _ hr
    rw [htop, he, hoE] at this
    cases this
  · cases hvx : c.view o with
    | none => rfl
    | some nd => have := hvg.ids _ nd hvx; omega

/-- A retargeted parent holds no live klong to the node it was retargeted from,
when that node is the transaction's: its klongs to it before the last time klong
are of earlier times, which name old nodes only. -/
theorem retarget_noHold (B : NodeId) (c : Ctx) (hvg : ViewGood B c) (p : NodeId) (pn : KNode)
    (hg : Good B c p pn) (hwf : klongsWf pn.ks = true) (hlt : pn.lastTime = some c.i)
    (o dst : NodeId) (hd : dst ≠ o) (hBo : B ≤ o) (cv : Nat) :
    (cv, o) ∉ ({ pn with ks := retargetKlongs pn.ks (pn.lastTimeIndex.getD 0) o dst } : KNode).live := by
  intro he
  have hpos := hvg.pos
  obtain ⟨c0, hkm⟩ := live_key_mem _ cv o he
  obtain ⟨i, hi, hile⟩ := retargetKlongs_src_mem pn.ks _ o dst hd c0 hkm
  obtain ⟨m, hm1, hm2⟩ := KNode.lastTime_anchor pn c.i hlt
  rw [hm1] at hile
  simp only [Option.getD_some] at hile
  have him : i ≠ m := by intro h; rw [h, hm2] at hi; cases hi
  have hpre := mem_prefixAt_before_time pn.ks c.i hpos hwf hg.times m hm2 i (by omega) _ hi
  have := ptr_lt_of_prefix B c hvg _ pn hg c0 o hpre
  omega

/-! ## The two copies with a postcondition on the result -/

/-- Every successful run of f with a result of Q is one of g. -/
def RWPQ {α : Type} (f g : M α) (c : Ctx) (w : W) (Q : α × W → Prop) : Prop :=
  ∀ x, f c w = .ok x → Q x → g c w = .ok x

theorem rwpq_refl {α : Type} (f : M α) (c : Ctx) (w : W) (Q : α × W → Prop) : RWPQ f f c w Q :=
  fun _ h _ => h

theorem rwpq_bind {α β : Type} {m : M α} {k1 k2 : α → M β} {c : Ctx} {w : W} {Q : β × W → Prop}
    (P : α → W → Prop) (hm : WriterWP m c w P) (hk : ∀ a w', P a w' → RWPQ (k1 a) (k2 a) c w' Q) :
    RWPQ (m >>= k1) (m >>= k2) c w Q := by
  intro x h hQ
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok m k1 c w x).mp h
  exact (m_bind_ok m k2 c w x).mpr ⟨a, w', h1, hk a w' (hm a w' h1) x h2 hQ⟩

theorem rwpq_check {β : Type} {f g : M β} {chk : M Unit} {c : Ctx} {w : W} {Q : β × W → Prop}
    (hc : ∀ x, f c w = .ok x → Q x → chk c w = .ok ((), w)) (h : RWPQ f g c w Q) :
    RWPQ f (chk >>= fun _ => g) c w Q := by
  intro x hx hQ
  exact (m_bind_ok chk _ c w x).mpr ⟨(), w, hc x hx hQ, h x hx hQ⟩

theorem rwp_of_rwpq {α : Type} {f g : M α} {c : Ctx} {w : W} {Q : α × W → Prop}
    (h : RWPQ f g c w Q) (hQ : WriterWP f c w (fun r v => Q (r, v))) : RWP f g c w :=
  fun x hx => h x hx (hQ x.1 x.2 hx)

/-! ## The merge's last loop for the two copies -/

/-- p's node after `retarget p src dst`. -/
def retNode (c : Ctx) (pn : KNode) (src dst : NodeId) : KNode :=
  if pn.lastTime == some c.i then { pn with ks := retargetKlongs pn.ks (pn.lastTimeIndex.getD 0) src dst } else pn

theorem retState_lookup (c : Ctx) (u : W) (p : NodeId) (pn : KNode) (src dst : NodeId)
    (hp : u.nodes.lookup p = some pn) (y : NodeId) :
    (retState c u p pn src dst).nodes.lookup y = if y = p then some (retNode c pn src dst) else u.nodes.lookup y := by
  unfold retState retNode
  split
  · simp only [lookup_upsert]
  · by_cases hy : y = p
    · subst hy; simp [hp]
    · simp [hy]

theorem retState_taken (c : Ctx) (u : W) (p : NodeId) (pn : KNode) (src dst : NodeId) :
    (retState c u p pn src dst).taken = u.taken ∧ (retState c u p pn src dst).top = u.top := by
  unfold retState; split <;> exact ⟨rfl, rfl⟩

theorem retNode_lastTime (c : Ctx) (pn : KNode) (src dst : NodeId) (h : (pn.lastTime == some c.i) = false) :
    retNode c pn src dst = pn := by
  unfold retNode; simp [h]

theorem unlState_lookup (c : Ctx) (u : W) (x : NodeId) (n : KNode) (y : NodeId) (hy : y ≠ x) :
    (unlState c u x n).nodes.lookup y = u.nodes.lookup y := by
  unfold unlState
  split
  · simp only [lookup_upsert, hy, ↓reduceIte]
  · rfl

theorem unlState_lookup_self (c : Ctx) (u : W) (x : NodeId) (n : KNode) (hx : u.nodes.lookup x = some n) :
    (unlState c u x n).nodes.lookup x = some (if n.lastTime == some c.i then n.toPrev (c.i - 1) else n) := by
  unfold unlState
  split
  · rename_i h; simp [lookup_upsert, h]
  · rename_i h; simp [h, hx]

theorem unlState_taken (c : Ctx) (u : W) (x : NodeId) (n : KNode) :
    (unlState c u x n).taken = u.taken ∧ (unlState c u x n).top = u.top := by
  unfold unlState; split <;> exact ⟨rfl, rfl⟩

/-- A node's version before the transaction holds no live klong to a node of the
transaction. -/
theorem toPrev_noHold (B : NodeId) (c : Ctx) (hvg : ViewGood B c) (x : NodeId) (n : KNode)
    (hg : Good B c x n) (o : NodeId) (hBo : B ≤ o) (cv : Nat) : (cv, o) ∉ (n.toPrev (c.i - 1)).live := by
  intro he
  obtain ⟨c0, hk⟩ := live_key_mem _ cv o he
  have := ptr_lt_of_prefix B c hvg x n hg c0 o hk
  omega

/-- The state after `takenBack o` and its note. -/
def tbn (o : NodeId) (u : W) : W :=
  ({ ({ u with taken := o :: u.taken } : W) with trail := "merge.takeback" :: u.trail } : W)

theorem nodup_retState (c : Ctx) (u : W) (p : NodeId) (pn : KNode) (src dst : NodeId)
    (h : (u.nodes.map Prod.fst).Nodup) : ((retState c u p pn src dst).nodes.map Prod.fst).Nodup := by
  unfold retState; split
  · exact upsert_unique _ _ _ h
  · exact h

theorem nodup_unlState (c : Ctx) (u : W) (x : NodeId) (n : KNode)
    (h : (u.nodes.map Prod.fst).Nodup) : ((unlState c u x n).nodes.map Prod.fst).Nodup := by
  unfold unlState; split
  · exact upsert_unique _ _ _ h
  · exact h

theorem writerWP_tbn (o : NodeId) (c : Ctx) (u : W) {β : Type} (k : M β) (P : β → W → Prop)
    (h : WriterWP k c (tbn o u) P) :
    WriterWP (do takenBack o; note "merge.takeback"; k) c u P := by
  simp only [writerWP_bind, writerWP_takenBack_iff, writerWP_note_iff]
  exact h

theorem rwpq_tbn {β : Type} (o : NodeId) (c : Ctx) (u : W) (k1 k2 : M β) (Q : β × W → Prop)
    (h : RWPQ k1 k2 c (tbn o u) Q) :
    RWPQ (do takenBack o; note "merge.takeback"; k1) (do takenBack o; note "merge.takeback"; k2) c u Q := by
  refine rwpq_bind (fun _ v => v = { u with taken := o :: u.taken }) ((writerWP_takenBack_iff o c u _).mpr rfl) ?_
  rintro _ v rfl
  refine rwpq_bind (fun _ v => v = tbn o u) ((writerWP_note_iff _ c _ _).mpr rfl) ?_
  rintro _ v rfl
  exact h

theorem cacheGood_tbn (B : NodeId) (c : Ctx) (o : NodeId) (u : W) (h : CacheGood B c u) :
    CacheGood B c (tbn o u) := h

theorem contains_cons1 {y a : NodeId} {L : List NodeId} (ha : y ≠ a) (h : L.contains y = false) :
    (a :: L).contains y = false := by
  simp only [List.contains_cons, h, Bool.or_false]; simpa using ha

theorem contains_cons2 {y a b : NodeId} {L : List NodeId} (ha : y ≠ a) (hb : y ≠ b) (h : L.contains y = false) :
    (a :: b :: L).contains y = false := contains_cons1 ha (contains_cons1 hb h)

set_option maxHeartbeats 3200000 in
/-- The merge's last loop for the two copies, from its start s0, with the
merge's end as the postcondition: each `checkFree` passes
(`holderFree_of_end`; the parent by `retarget_noHold`, the nodes merged by what
they held at the start). -/
theorem rwpq_mergeLoop (c : Ctx) (base : View BVal) (B : NodeId) (hvg : ViewGood B c)
    (p m1 l r : NodeId) (lM rM : Bool) (ln rn pn0 : KNode) (k : Nat) (s0 : W)
    (hp0 : s0.nodes.lookup p = some pn0) (hl0 : s0.nodes.lookup l = some ln)
    (hr0 : s0.nodes.lookup r = some rn)
    (hlr : l ≠ r) (hlp : l ≠ p) (hrp : r ≠ p) (hm1l : m1 ≠ l) (hm1r : m1 ≠ r)
    (hcg : CacheGood B c s0) (hnd : (s0.nodes.map Prod.fst).Nodup)
    (hwfp : klongsWf pn0.ks = true)
    (hlB : lM = true → B ≤ l) (hrB : rM = true → B ≤ r)
    (hll : lM = true → ∀ cv, (cv, l) ∉ ln.live) (hrl : lM = true → ∀ cv, (cv, l) ∉ rn.live)
    (hrr : rM = true → ∀ cv, (cv, r) ∉ rn.live) (hlr' : rM = true → ∀ cv, (cv, r) ∉ ln.live) :
    RWPQ (forIn [(l, lM), (r, rM)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit))) >>= fun _ => (pure k : M Nat))
      (forIn [(l, lM), (r, rM)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        checkFree q.1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit))) >>= fun _ => (pure k : M Nat)) c s0
      (fun xf => MergeEnd c base B xf.2) := by
  have hgp : Good B c p pn0 := cacheGood_lookup B c s0 hcg p pn0 hp0
  have hgl : Good B c l ln := cacheGood_lookup B c s0 hcg l ln hl0
  cases lM <;> cases rM <;>
    simp only [List.forIn_cons, List.forIn_nil, ite_true, Bool.false_eq_true, ite_false, bind_assoc, pure_bind]
  · exact rwpq_refl _ _ _ _
  · -- l unlinked, r taken back
    have hrB' := hrB rfl
    refine rwpq_bind (fun _ v => v = unlState c s0 l ln ∧ CacheGood B c v)
      (writerWP_and (writerWP_unlink_known l c s0 ln hl0) (good_unlink B l c s0 hvg hcg)) ?_
    rintro _ v1 ⟨rfl, hcg1⟩
    have hp1 : (unlState c s0 l ln).nodes.lookup p = some pn0 := by
      rw [unlState_lookup c s0 l ln p (Ne.symm hlp)]; exact hp0
    have hr1 : (unlState c s0 l ln).nodes.lookup r = some rn := by
      rw [unlState_lookup c s0 l ln r (Ne.symm hlr)]; exact hr0
    refine rwpq_bind (fun _ v => v = retState c (unlState c s0 l ln) p pn0 r m1 ∧ CacheGood B c v)
      (writerWP_and (writerWP_retarget_known p r m1 c _ pn0 hp1)
        (good_retarget B p r m1 c _ hvg hcg1)) ?_
    rintro _ v2 ⟨rfl, hcg2⟩
    refine rwpq_check ?_ (rwpq_refl _ _ _ _)
    intro xf hxf hQ
    have hsE : xf.2 = tbn r (retState c (unlState c s0 l ln) p pn0 r m1) :=
      (writerWP_tbn r c _ (pure k) (fun _ v => v = tbn r (retState c (unlState c s0 l ln) p pn0 r m1))
        (by simp only [writerWP_pure])) xf.1 xf.2 hxf
    have ht2 := retState_taken c (unlState c s0 l ln) p pn0 r m1
    have ht1 := unlState_taken c s0 l ln
    apply checkFree_ok
    refine holderFree_of_end c base B hvg _ r hrB' xf.2 hQ ?_ ?_ hcg2
      (nodup_retState _ _ _ _ _ _ (nodup_unlState _ _ _ _ hnd)) ?_
    · rw [hsE]; simp [tbn]
    · rw [hsE]; rfl
    · intro q n hq htq
      by_cases hqp : q = p
      · subst hqp
        left
        refine ⟨by rw [hsE]; exact hq, ?_⟩
        rw [hsE]
        exact contains_cons1 (Ne.symm hrp) htq
      · by_cases hql : q = l
        · subst hql
          rw [retState_lookup c _ p pn0 r m1 hp1, if_neg hqp, unlState_lookup_self c s0 q ln hl0] at hq
          cases hq
          right
          intro cv
          split
          · exact toPrev_noHold B c hvg q ln hgl r hrB' cv
          · exact hlr' rfl cv
        · by_cases hqr : q = r
          · subst hqr
            rw [retState_lookup c _ p pn0 q m1 hp1, if_neg hqp, hr1] at hq
            cases hq
            right
            exact hrr rfl
          · left
            refine ⟨by rw [hsE]; exact hq, ?_⟩
            rw [hsE]
            exact contains_cons1 hqr htq
  · -- l taken back, r unlinked
    have hlB' := hlB rfl
    refine rwpq_bind (fun _ v => v = retState c s0 p pn0 l m1 ∧ CacheGood B c v)
      (writerWP_and (writerWP_retarget_known p l m1 c s0 pn0 hp0) (good_retarget B p l m1 c s0 hvg hcg)) ?_
    rintro _ v1 ⟨rfl, hcg1⟩
    have hp1 := retState_lookup c s0 p pn0 l m1 hp0
    have ht1 := retState_taken c s0 p pn0 l m1
    have hr2 : (tbn l (retState c s0 p pn0 l m1)).nodes.lookup r = some rn := by
      show (retState c s0 p pn0 l m1).nodes.lookup r = some rn
      rw [hp1, if_neg hrp]; exact hr0
    refine rwpq_check ?_ ?_
    · intro xf hxf hQ
      have hsE : xf.2 = unlState c (tbn l (retState c s0 p pn0 l m1)) r rn :=
        (writerWP_tbn l c _ _ (fun _ v => v = unlState c (tbn l (retState c s0 p pn0 l m1)) r rn)
          (by
            simp only [writerWP_bind]
            refine writerWP_mono (writerWP_unlink_known r c _ rn hr2) ?_
            rintro _ v rfl
            simp only [writerWP_pure])) xf.1 xf.2 hxf
      have hte := unlState_taken c (tbn l (retState c s0 p pn0 l m1)) r rn
      apply checkFree_ok
      refine holderFree_of_end c base B hvg _ l hlB' xf.2 hQ ?_ ?_ hcg1 (nodup_retState _ _ _ _ _ _ hnd) ?_
      · rw [hsE, hte.1]; simp [tbn]
      · rw [hsE, hte.2]; rfl
      · intro q n hq htq
        by_cases hqp : q = p
        · subst hqp
          rw [hp1, if_pos rfl] at hq
          cases hq
          by_cases hlt : (pn0.lastTime == some c.i) = true
          · right
            intro cv
            unfold retNode
            simp only [hlt, ↓reduceIte]
            exact retarget_noHold B c hvg q pn0 hgp hwfp (by simpa using hlt) l m1 hm1l hlB' cv
          · left
            have hlt' : (pn0.lastTime == some c.i) = false := by simpa using hlt
            rw [retNode_lastTime c pn0 l m1 hlt']
            refine ⟨?_, ?_⟩
            · rw [hsE, unlState_lookup _ _ r rn q (Ne.symm hrp)]
              show (retState c s0 q pn0 l m1).nodes.lookup q = some pn0
              rw [hp1, if_pos rfl, retNode_lastTime c pn0 l m1 hlt']
            · rw [hsE, hte.1]
              exact contains_cons1 (Ne.symm hlp) htq
        · by_cases hql : q = l
          · subst hql
            rw [hp1, if_neg hqp, hl0] at hq
            cases hq
            right
            exact hll rfl
          · by_cases hqr : q = r
            · subst hqr
              rw [hp1, if_neg hqp, hr0] at hq
              cases hq
              right
              exact hrl rfl
            · left
              refine ⟨?_, ?_⟩
              · rw [hsE, unlState_lookup _ _ r rn q hqr]; exact hq
              · rw [hsE, hte.1]
                exact contains_cons1 hql htq
    · exact rwpq_tbn l c _ _ _ _ (rwpq_refl _ _ _ _)
  · -- both taken back
    have hlB' := hlB rfl
    have hrB' := hrB rfl
    refine rwpq_bind (fun _ v => v = retState c s0 p pn0 l m1 ∧ CacheGood B c v)
      (writerWP_and (writerWP_retarget_known p l m1 c s0 pn0 hp0) (good_retarget B p l m1 c s0 hvg hcg)) ?_
    rintro _ v1 ⟨rfl, hcg1⟩
    have hp1 := retState_lookup c s0 p pn0 l m1 hp0
    have ht1 := retState_taken c s0 p pn0 l m1
    have hp2 : (tbn l (retState c s0 p pn0 l m1)).nodes.lookup p = some (retNode c pn0 l m1) := by
      show (retState c s0 p pn0 l m1).nodes.lookup p = some _
      rw [hp1, if_pos rfl]
    have hp3 := retState_lookup c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1 hp2
    have ht3 := retState_taken c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1
    refine rwpq_check ?_ ?_
    · intro xf hxf hQ
      have hsE : xf.2 = tbn r (retState c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1) :=
        (writerWP_tbn l c _ _ (fun _ v => v = tbn r (retState c (tbn l (retState c s0 p pn0 l m1)) p
            (retNode c pn0 l m1) r m1))
          (by
            simp only [writerWP_bind]
            refine writerWP_mono (writerWP_retarget_known p r m1 c _ _ hp2) ?_
            rintro _ v rfl
            simp only [writerWP_takenBack_iff, writerWP_note_iff, writerWP_pure]
            try rfl)) xf.1 xf.2 hxf
      apply checkFree_ok
      refine holderFree_of_end c base B hvg _ l hlB' xf.2 hQ ?_ ?_ hcg1 (nodup_retState _ _ _ _ _ _ hnd) ?_
      · rw [hsE]
        show (r :: (retState c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1).taken).contains l = true
        rw [ht3.1]; simp [tbn]
      · rw [hsE]
        show (retState c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1).top = _
        rw [ht3.2]; rfl
      · intro q n hq htq
        by_cases hqp : q = p
        · subst hqp
          rw [hp1, if_pos rfl] at hq
          cases hq
          by_cases hlt : (pn0.lastTime == some c.i) = true
          · right
            intro cv
            unfold retNode
            simp only [hlt, ↓reduceIte]
            exact retarget_noHold B c hvg q pn0 hgp hwfp (by simpa using hlt) l m1 hm1l hlB' cv
          · left
            have hlt' : (pn0.lastTime == some c.i) = false := by simpa using hlt
            refine ⟨?_, ?_⟩
            · rw [hsE]
              show (retState _ _ _ _ _ _).nodes.lookup q = _
              rw [hp3, if_pos rfl, retNode_lastTime c _ r m1 (by rw [retNode_lastTime c pn0 l m1 hlt']; exact hlt')]
            · rw [hsE]
              show (r :: (retState c (tbn l (retState c s0 q pn0 l m1)) q (retNode c pn0 l m1) r m1).taken).contains q = false
              rw [ht3.1]
              exact contains_cons2 (Ne.symm hrp) (Ne.symm hlp) htq
        · by_cases hql : q = l
          · subst hql
            rw [hp1, if_neg hqp, hl0] at hq
            cases hq
            right
            exact hll rfl
          · by_cases hqr : q = r
            · subst hqr
              rw [hp1, if_neg hqp, hr0] at hq
              cases hq
              right
              exact hrl rfl
            · left
              refine ⟨?_, ?_⟩
              · rw [hsE]
                show (retState _ _ _ _ _ _).nodes.lookup q = _
                rw [hp3, if_neg hqp]; exact hq
              · rw [hsE]
                show (r :: (retState c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1).taken).contains q = false
                rw [ht3.1]
                exact contains_cons2 hqr hql htq
    · refine rwpq_tbn l c _ _ _ _ ?_
      refine rwpq_bind (fun _ v => v = retState c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1 ∧
          CacheGood B c v)
        (writerWP_and (writerWP_retarget_known p r m1 c _ _ hp2)
          (good_retarget B p r m1 c _ hvg (cacheGood_tbn B c l _ hcg1))) ?_
      rintro _ v2 ⟨rfl, hcg2⟩
      refine rwpq_check ?_ (rwpq_refl _ _ _ _)
      intro xf hxf hQ
      have hsE : xf.2 = tbn r (retState c (tbn l (retState c s0 p pn0 l m1)) p (retNode c pn0 l m1) r m1) :=
        (writerWP_tbn r c _ (pure k) (fun _ v => v = tbn r (retState c (tbn l (retState c s0 p pn0 l m1)) p
          (retNode c pn0 l m1) r m1)) (by simp only [writerWP_pure])) xf.1 xf.2 hxf
      apply checkFree_ok
      refine holderFree_of_end c base B hvg _ r hrB' xf.2 hQ ?_ ?_ hcg2
        (nodup_retState _ _ _ _ _ _ (nodup_retState _ _ _ _ _ _ hnd)) ?_
      · rw [hsE]; simp [tbn]
      · rw [hsE]; rfl
      · intro q n hq htq
        by_cases hqp : q = p
        · subst hqp
          left
          refine ⟨by rw [hsE]; exact hq, ?_⟩
          rw [hsE]
          exact contains_cons1 (Ne.symm hrp) htq
        · by_cases hql : q = l
          · exfalso
            subst hql
            rw [ht3.1] at htq
            simp [tbn] at htq
          · by_cases hqr : q = r
            · subst hqr
              rw [hp3, if_neg hqp] at hq
              have hq' : (retState c s0 p pn0 l m1).nodes.lookup q = some n := hq
              rw [hp1, if_neg hqp, hr0] at hq'
              cases hq'
              right
              exact hrr rfl
            · left
              refine ⟨by rw [hsE]; exact hq, ?_⟩
              rw [hsE]
              exact contains_cons1 hqr htq

/-! ## The merge's tail up to its last loop -/

/-- What the merge's tail keeps up to its last loop: the two nodes merged as at
its start, the cache's books, the nodes cached at its start s cached. -/
structure TInv (B : NodeId) (c : Ctx) (s : W) (path0 : List (Option Nat × NodeId)) (l r : NodeId)
    (ln rn : KNode) (v : W) : Prop where
  rjl : RJ l ln path0 v
  rjr : RJ r rn path0 v
  good : CacheGood B c v
  uniq : UniqueCache B v
  wf : WriterKlongsWf v
  cached : CachedFrom s c v

section TInvSteps

variable {B : NodeId} {c : Ctx} {s : W} {path0 : List (Option Nat × NodeId)} {l r : NodeId} {ln rn : KNode}

theorem tinv_of_eq {v v' : W} (h : TInv B c s path0 l r ln rn v) (hn : v'.nodes = v.nodes)
    (hx : v'.next = v.next) (hp : v'.path = v.path) (hg : v'.gh = v.gh) (ht : v'.taken = v.taken) :
    TInv B c s path0 l r ln rn v' := by
  obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, hgd, ⟨⟨f1, f2, f3, f4⟩, fu⟩, hwf, hcf⟩ := h
  refine ⟨⟨by rw [hn]; exact a1, by rw [hx]; exact a2, by rw [hp]; exact a3⟩,
    ⟨by rw [hn]; exact b1, by rw [hx]; exact b2, by rw [hp]; exact b3⟩,
    ⟨by rw [hx]; exact hgd.1, by rw [hn]; exact hgd.2⟩,
    ⟨⟨by rw [hx]; exact f1, by rw [hn, hx]; exact f2, by rw [hg, hx]; exact f3, by rw [ht, hx]; exact f4⟩,
      by unfold CacheUnique; rw [hn]; exact fu⟩,
    by unfold WriterKlongsWf; rw [hn]; exact hwf, fun y hy => by rw [hn]; exact hcf y hy⟩

theorem tinv_modify (f : W → W) (v : W) (h : TInv B c s path0 l r ln rn v) (hn : (f v).nodes = v.nodes)
    (hx : (f v).next = v.next) (hp : (f v).path = v.path) (hg : (f v).gh = v.gh) (ht : (f v).taken = v.taken) :
    WriterWP (modify f) c v (fun _ v' => TInv B c s path0 l r ln rn v') :=
  (writerWP_modify f c v _).mpr (tinv_of_eq h hn hx hp hg ht)

theorem tinv_note (str : String) (v : W) (h : TInv B c s path0 l r ln rn v) :
    WriterWP (note str) c v (fun _ v' => TInv B c s path0 l r ln rn v') :=
  tinv_modify _ v h rfl rfl rfl rfl rfl

theorem tinv_replacedBy (y : NodeId) (v : W) (h : TInv B c s path0 l r ln rn v) :
    WriterWP (replacedBy y) c v (fun _ v' => TInv B c s path0 l r ln rn v') := by
  unfold replacedBy; simp only [writerWP_bind, writerWP_get, writerWP_pure]; exact h

theorem tinv_setMadeFor (y : NodeId) (o : Option NodeId) (v : W) (h : TInv B c s path0 l r ln rn v) :
    WriterWP (setMadeFor y o) c v (fun _ v' => TInv B c s path0 l r ln rn v') := by
  unfold setMadeFor
  cases o with
  | none => simp only [writerWP_pure]; exact h
  | some o => exact tinv_modify _ v h rfl rfl rfl rfl rfl

theorem tinv_ghOf (x : NodeId) (n : KNode) (v : W) (hx : v.nodes.lookup x = some n)
    (h : TInv B c s path0 l r ln rn v) :
    WriterWP (ghOf x) c v (fun _ v' => TInv B c s path0 l r ln rn v') :=
  writerWP_ghOf_cached x n c v hx _ (fun _ => h)

theorem tinv_newKey (hvg : ViewGood B c) (g h : Nat) (leaf : Bool) (ks : List Klong) (hks : ks = [] ∨ FlatAt c.i ks)
    (hkw : klongsWf ks = true) (hkv : ViewKlongsWf c.p c.view) (v : W) (hI : TInv B c s path0 l r ln rn v) :
    WriterWP (newKey g h leaf ks) c v (fun y v' => TInv B c s path0 l r ln rn v' ∧ y ≠ l ∧ y ≠ r) := by
  have h1 := (xwp_newKey (m := ln) (c := c) (post := fun y u' => RJ l ln path0 u' ∧ y ≠ l) path0 g h leaf ks hI.rjl
    (fun y u' hJ hy => ⟨hJ, hy⟩)).2
  have h2 := (xwp_newKey (m := rn) (c := c) (post := fun y u' => RJ r rn path0 u' ∧ y ≠ r) path0 g h leaf ks hI.rjr
    (fun y u' hJ hy => ⟨hJ, hy⟩)).2
  have h3 := good_newKey B g h leaf ks c v (fun _ v' => CacheGood B c v') hvg hI.good hks (fun _ _ h => h.1)
  have h4 := writerWP_newKey_uniqueCache B g h leaf ks c v hI.uniq
  have h5 := klongsWf_newKey g h leaf ks hkw c v hkv hI.wf
  have h6 := @state_newKey (cachedFromInvariant s) g h leaf ks c v hI.cached
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and (writerWP_and h1 h2) h3) h4) h5) h6) ?_
  rintro y v' ⟨⟨⟨⟨⟨⟨a1, a2⟩, b1, b2⟩, h3'⟩, h4', _, _⟩, h5'⟩, h6'⟩
  exact ⟨⟨a1, b1, h3', h4', h5', h6'⟩, a2, b2⟩

theorem tinv_mergeParent (hvg : ViewGood B c) (hkv : ViewKlongsWf c.p c.view) (hv : ViewIdsBelow B c.view)
    (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat))
    (v : W) (hI : TInv B c s path0 l r ln rn v) (hp : v.nodes.lookup p = some pn)
    (hR : cR ∈ pn.live.map Prod.fst) (hpl : p ≠ l) (hpr : p ≠ r) (hpath : v.path = path0)
    (hab : ∀ i e, i + 1 ≤ depth → path0[i]? = some e → e.2 ≠ l ∧ e.2 ≠ r) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c v (fun _ v' => TInv B c s path0 l r ln rn v') := by
  have hRJ : WriterWP (mergeParent p depth il cL m1 ir cR m2) c v
      (fun _ v' => RJ l ln path0 v' ∧ RJ r rn path0 v') := by
    refine writerWP_mergeParent_cases p pn depth il cL m1 ir cR m2 c v _ hp ?_ ?_
    · intro str
      obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ := (⟨hI.rjl, hI.rjr⟩ : RJ l ln path0 v ∧ RJ r rn path0 v)
      exact ⟨⟨lookup_upsert_x _ l p _ hpl ln a1, a2, a3⟩, ⟨lookup_upsert_x _ r p _ hpr rn b1, b2, b3⟩⟩
    · intro last compact str _
      have hl' : RJ l ln path0 ({ v with trail := str :: v.trail } : W) := hI.rjl
      have hr' : RJ r rn path0 ({ v with trail := str :: v.trail } : W) := hI.rjr
      cases depth with
      | zero =>
        exact writerWP_and (xwp_handleFull_zero (m := ln) path0 p last compact hl' hpl).2
          (xwp_handleFull_zero (m := rn) path0 p last compact hr' hpr).2
      | succ D =>
        exact writerWP_and
          (xwp_handleFull_succ (m := ln) path0 D p last compact hl' hpl
            (fun i e hi he => (hab i e (by omega) he).1)).2
          (xwp_handleFull_succ (m := rn) path0 D p last compact hr' hpr
            (fun i e hi he => (hab i e (by omega) he).2)).2
  have h3 := good_mergeParent B p depth il cL m1 ir cR m2 c v hvg hI.good
  have h4 := uniqueCache_mergeParent (base := B) p depth il cL m1 ir cR m2 c v hv hI.uniq
  have h5 := writerWP_mergeParent_wf p pn depth il cL m1 ir cR m2 c v hkv hI.wf hp hR
  have h6 := @state_mergeParent (cachedFromInvariant s) p depth il cL m1 ir cR m2 c v hI.cached
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and hRJ h3) h4) h5) h6) ?_
  rintro _ v' ⟨⟨⟨⟨⟨a, b⟩, h3'⟩, h4', _⟩, h5'⟩, h6'⟩
  exact ⟨a, b, h3', h4', h5', h6'⟩

end TInvSteps

section TInvPSteps

variable {B : NodeId} {c : Ctx} {s : W} {path0 : List (Option Nat × NodeId)} {l r : NodeId} {ln rn : KNode}
  {p : NodeId} {pn : KNode}

/-- `TInv` with the parent's node as at the start, up to `mergeParent`. -/
def TInvP (B : NodeId) (c : Ctx) (s : W) (path0 : List (Option Nat × NodeId)) (l r : NodeId) (ln rn : KNode)
    (p : NodeId) (pn : KNode) (v : W) : Prop :=
  TInv B c s path0 l r ln rn v ∧ RJ p pn path0 v

theorem tinvP_note (str : String) (v : W) (h : TInvP B c s path0 l r ln rn p pn v) :
    WriterWP (note str) c v (fun _ v' => TInvP B c s path0 l r ln rn p pn v') :=
  (writerWP_modify _ c v _).mpr ⟨tinv_of_eq h.1 rfl rfl rfl rfl rfl, h.2⟩

theorem tinvP_merges (v : W) (h : TInvP B c s path0 l r ln rn p pn v) :
    WriterWP (modify (fun w => { w with merges := w.merges + 1 })) c v
      (fun _ v' => TInvP B c s path0 l r ln rn p pn v') :=
  (writerWP_modify _ c v _).mpr ⟨tinv_of_eq h.1 rfl rfl rfl rfl rfl, h.2⟩

theorem tinvP_replacedBy (y : NodeId) (v : W) (h : TInvP B c s path0 l r ln rn p pn v) :
    WriterWP (replacedBy y) c v (fun _ v' => TInvP B c s path0 l r ln rn p pn v') := by
  unfold replacedBy; simp only [writerWP_bind, writerWP_get, writerWP_pure]; exact h

theorem tinvP_setMadeFor (y : NodeId) (o : Option NodeId) (v : W) (h : TInvP B c s path0 l r ln rn p pn v) :
    WriterWP (setMadeFor y o) c v (fun _ v' => TInvP B c s path0 l r ln rn p pn v') := by
  unfold setMadeFor
  cases o with
  | none => simp only [writerWP_pure]; exact h
  | some o => exact (writerWP_modify _ c v _).mpr ⟨tinv_of_eq h.1 rfl rfl rfl rfl rfl, h.2⟩

theorem tinvP_ghOf (x : NodeId) (n : KNode) (v : W) (hx : v.nodes.lookup x = some n)
    (h : TInvP B c s path0 l r ln rn p pn v) :
    WriterWP (ghOf x) c v (fun _ v' => TInvP B c s path0 l r ln rn p pn v') :=
  writerWP_ghOf_cached x n c v hx _ (fun _ => h)

theorem tinvP_newKey (hvg : ViewGood B c) (g h : Nat) (leaf : Bool) (ks : List Klong)
    (hks : ks = [] ∨ FlatAt c.i ks) (hkw : klongsWf ks = true) (hkv : ViewKlongsWf c.p c.view) (v : W)
    (hI : TInvP B c s path0 l r ln rn p pn v) :
    WriterWP (newKey g h leaf ks) c v (fun y v' => TInvP B c s path0 l r ln rn p pn v' ∧ y ≠ l ∧ y ≠ r) := by
  have h1 := tinv_newKey hvg g h leaf ks hks hkw hkv v hI.1
  have h2 := (xwp_newKey (m := pn) (c := c) (post := fun _ u' => RJ p pn path0 u') path0 g h leaf ks hI.2
    (fun _ u' hJ _ => hJ)).2
  refine writerWP_mono (writerWP_and h1 h2) ?_
  rintro y v' ⟨⟨a, b, e⟩, d⟩
  exact ⟨⟨a, d⟩, b, e⟩

end TInvPSteps

theorem rwpq_throw_bind {α β : Type} (e : String) (k : α → M β) (g : M β) (c : Ctx) (w : W)
    (Q : β × W → Prop) : RWPQ ((throw e : M α) >>= k) g c w Q :=
  fun x hx _ => rwp_throw_bind e k g c w x hx

theorem rwpq_ite {β : Type} {b : Prop} [Decidable b] {f1 f2 g1 g2 : M β} {c : Ctx} {w : W}
    {Q : β × W → Prop} (h1 : b → RWPQ f1 g1 c w Q) (h2 : ¬ b → RWPQ f2 g2 c w Q) :
    RWPQ (if b then f1 else f2) (if b then g1 else g2) c w Q := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte]; exact h1 hb
  · simp only [hb, ↓reduceIte]; exact h2 hb

set_option maxHeartbeats 3200000 in
theorem rwpq_tailLeaf (c : Ctx) (base : View BVal) (B : NodeId) (hvg : ViewGood B c)
    (hkv : ViewKlongsWf c.p c.view) (hv : ViewIdsBelow B c.view)
    (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat) (m2 : Option (NodeId × Nat))
    (l r : NodeId) (ln rn : KNode) (lM rM : Bool) (k : Nat) (s v : W) (path0 : List (Option Nat × NodeId))
    (hI : TInvP B c s path0 l r ln rn p pn v) (hps : (s.nodes.lookup p).isSome = true)
    (hR : cR ∈ pn.live.map Prod.fst) (hlr : l ≠ r) (hlp : l ≠ p) (hrp : r ≠ p) (hm1l : m1 ≠ l) (hm1r : m1 ≠ r)
    (hab : ∀ i e, i + 1 ≤ depth → path0[i]? = some e → e.2 ≠ l ∧ e.2 ≠ r)
    (hlB : lM = true → B ≤ l) (hrB : rM = true → B ≤ r)
    (hll : lM = true → ∀ cv, (cv, l) ∉ ln.live) (hrl : lM = true → ∀ cv, (cv, l) ∉ rn.live)
    (hrr : rM = true → ∀ cv, (cv, r) ∉ rn.live) (hlr' : rM = true → ∀ cv, (cv, r) ∉ ln.live) :
    RWPQ (do
        mergeParent p depth il cL m1 ir cR m2
        forIn [(l, lM), (r, rM)] PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))
        (pure k : M Nat))
      (do
        mergeParent p depth il cL m1 ir cR m2
        forIn [(l, lM), (r, rM)] PUnit.unit (fun q _ => if q.2 = true then (do
          retarget p q.1 m1
          checkFree q.1
          takenBack q.1
          note "merge.takeback"
          pure (ForInStep.yield PUnit.unit)) else (do
          unlink q.1
          pure (ForInStep.yield PUnit.unit)))
        (pure k : M Nat)) c v (fun xf => MergeEnd c base B xf.2) := by
  refine rwpq_bind (fun _ v' => TInv B c s path0 l r ln rn v')
    (tinv_mergeParent hvg hkv hv p pn depth il cL m1 ir cR m2 v hI.1 hI.2.1 hR (Ne.symm hlp) (Ne.symm hrp)
      hI.2.2.2 hab) ?_
  rintro _ s0 h0
  obtain ⟨pn0, hp0⟩ : ∃ pn0, s0.nodes.lookup p = some pn0 := by
    have := h0.cached p hps
    cases h : s0.nodes.lookup p with
    | none => rw [h] at this; cases this
    | some n => exact ⟨n, rfl⟩
  have hwfp : klongsWf pn0.ks = true := h0.wf (p, pn0) (bk_mem_of_lookup _ _ _ hp0)
  exact rwpq_mergeLoop c base B hvg p m1 l r lM rM ln rn pn0 k s0 hp0 h0.rjl.1 h0.rjr.1 hlr hlp hrp hm1l hm1r
    h0.good h0.uniq.2 hwfp hlB hrB hll hrl hrr hlr'

theorem rwpq_throw {α : Type} (e : String) (g : M α) (c : Ctx) (w : W) (Q : α × W → Prop) :
    RWPQ (throw e : M α) g c w Q :=
  fun x hx _ => ((writerWP_throw e c w (fun _ _ => False)) x.1 x.2 hx).elim

set_option maxHeartbeats 3200000 in
theorem rwpq_mergeTail (c : Ctx) (base : View BVal) (B : NodeId) (hvg : ViewGood B c)
    (hkv : ViewKlongsWf c.p c.view) (hv : ViewIdsBelow B c.view)
    (x : NodeId) (d : Nat) (p : NodeId) (pn xn : KNode) (ls : Bool) (l : NodeId) (ln : KNode) (il : Nat)
    (r : NodeId) (rn : KNode) (ir : Nat) (s : W) (path0 : List (Option Nat × NodeId))
    (hI : TInvP B c s path0 l r ln rn p pn s)
    (hxlr : (x = l ∧ xn = ln) ∨ (x = r ∧ xn = rn))
    (hlr : l ≠ r) (hlp : l ≠ p) (hrp : r ≠ p)
    (hab : ∀ i e, i + 1 ≤ d - 1 → path0[i]? = some e → e.2 ≠ l ∧ e.2 ≠ r)
    (hR : ∀ cR, pn.cv? ir = some cR → cR ∈ pn.live.map Prod.fst)
    (hlB : ln.firstTime = some c.i → B ≤ l) (hrB : rn.firstTime = some c.i → B ≤ r)
    (hll : ln.firstTime = some c.i → ∀ cv, (cv, l) ∉ ln.live)
    (hrl : ln.firstTime = some c.i → ∀ cv, (cv, l) ∉ rn.live)
    (hrr : rn.firstTime = some c.i → ∀ cv, (cv, r) ∉ rn.live)
    (hlr' : rn.firstTime = some c.i → ∀ cv, (cv, r) ∉ ln.live) :
    RWPQ (mergeTail c x d p pn xn ls l ln il r rn ir) (mergeTailChk c x d p pn xn ls l ln il r rn ir) c s
      (fun xf => MergeEnd c base B xf.2) := by
  have hxk : ∀ v, TInvP B c s path0 l r ln rn p pn v → v.nodes.lookup x = some xn := by
    intro v hv
    rcases hxlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hv.1.rjl.1
    · exact hv.1.rjr.1
  unfold mergeTail mergeTailChk
  refine rwpq_bind _ (tinvP_note _ _ hI) (fun _ v1 hv1 => ?_)
  cases hil : pn.cv? il with
  | none => simp only []; first | exact rwpq_throw _ _ _ _ _ | exact rwpq_throw_bind _ _ _ _ _ _
  | some cL =>
  cases hir : pn.cv? ir with
  | none => simp only [pure_bind]; first | exact rwpq_throw _ _ _ _ _ | exact rwpq_throw_bind _ _ _ _ _ _
  | some cR =>
  simp only [pure_bind]
  refine rwpq_ite (fun _ => rwpq_throw_bind _ _ _ _ _ _) (fun _ => ?_)
  refine rwpq_ite (fun _ => rwpq_throw_bind _ _ _ _ _ _) (fun _ => ?_)
  refine rwpq_bind _ (tinvP_merges _ hv1) (fun _ v2 hv2 => ?_)
  refine rwpq_bind _ (tinvP_note _ _ hv2) (fun _ v3 hv3 => ?_)
  refine rwpq_bind _ (tinvP_note _ _ hv3) (fun _ v4 hv4 => ?_)
  refine rwpq_bind _ (tinvP_ghOf x xn v4 (hxk v4 hv4) hv4) (fun gh v5 hv5 => ?_)
  have hps : (s.nodes.lookup p).isSome = true := by rw [hI.2.1]; rfl
  have hR' := hR cR hir
  cases hsec : (mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live).2 with
  | none =>
    by_cases hlm : (ln.firstTime == some c.i) = true <;> by_cases hrm : (rn.firstTime == some c.i) = true <;>
      simp only [hlm, hrm, ↓reduceIte, Bool.false_eq_true]
    all_goals
      repeat' (first
        | (refine rwpq_bind _ (tinvP_note _ _ ‹_›) (fun _ _ _ => ?_))
        | (refine rwpq_bind _ (tinvP_replacedBy _ _ ‹_›) (fun _ _ _ => ?_))
        | (refine rwpq_bind _ (tinvP_setMadeFor _ _ _ ‹_›) (fun _ _ _ => ?_))
        | (refine rwpq_bind _ (tinvP_newKey ‹ViewGood _ _› _ _ _ _ (Or.inr (flatAt_newKlongs _ _))
            (klongsWf_newKlongs _ _) ‹ViewKlongsWf _ _› _ ‹_›) (fun _ _ h => ?_); obtain ⟨_, _, _⟩ := h))
    all_goals
      exact rwpq_tailLeaf c base B hvg hkv hv p pn _ il cL _ ir cR _ l r ln rn _ _ _ s _ path0 ‹_› hps hR'
        hlr hlp hrp (by assumption) (by assumption) hab
        (fun h => hlB (by first | simpa using hlm | simp at h))
        (fun h => hrB (by first | simpa using hrm | simp at h))
        (fun h => hll (by first | simpa using hlm | simp at h))
        (fun h => hrl (by first | simpa using hlm | simp at h))
        (fun h => hrr (by first | simpa using hrm | simp at h))
        (fun h => hlr' (by first | simpa using hrm | simp at h))
  | some ks2g2 =>
  by_cases hlm : (ln.firstTime == some c.i) = true <;> by_cases hrm : (rn.firstTime == some c.i) = true <;>
    simp only [hlm, hrm, ↓reduceIte, Bool.false_eq_true]
  all_goals
    repeat' (first
      | (refine rwpq_bind _ (tinvP_note _ _ ‹_›) (fun _ _ _ => ?_))
      | (refine rwpq_bind _ (tinvP_replacedBy _ _ ‹_›) (fun _ _ _ => ?_))
      | (refine rwpq_bind _ (tinvP_setMadeFor _ _ _ ‹_›) (fun _ _ _ => ?_))
      | (refine rwpq_bind _ (tinvP_newKey ‹ViewGood _ _› _ _ _ _ (Or.inr (flatAt_newKlongs _ _))
          (klongsWf_newKlongs _ _) ‹ViewKlongsWf _ _› _ ‹_›) (fun _ _ h => ?_); obtain ⟨_, _, _⟩ := h))
  all_goals
    exact rwpq_tailLeaf c base B hvg hkv hv p pn _ il cL _ ir cR _ l r ln rn _ _ _ s _ path0 ‹_› hps hR'
      hlr hlp hrp (by assumption) (by assumption) hab
      (fun h => hlB (by first | simpa using hlm | simp at h))
      (fun h => hrB (by first | simpa using hrm | simp at h))
      (fun h => hll (by first | simpa using hlm | simp at h))
      (fun h => hrl (by first | simpa using hlm | simp at h))
      (fun h => hrr (by first | simpa using hrm | simp at h))
      (fun h => hlr' (by first | simpa using hrm | simp at h))

/-- `merge` with its tail as a parameter: `merge` and `mergeChk` are instances. -/
def mergeP (tl : Ctx → NodeId → Nat → NodeId → KNode → KNode → Bool → NodeId → KNode → Nat → NodeId → KNode →
    Nat → M Nat) (x : NodeId) (d : Nat) : M Nat := do
  let c ← read
  let tt := c.i
  let p ← pathNode (d - 1)
  let pn ← getNode p
  let xn ← getNode x
  let inner := !xn.leaf
  let cx ← klongAt d
  let (ix?, ia, ib) := mergeIdx pn cx
  let ix ← match ix? with
    | some ix => pure ix
    | none => throw s!"Bug: merge at {tt}: key node {x} has no live klong {cx} in {p}"
  if pn.ptr? ix != some x then
    throw s!"Bug: merge at {tt}: key node {x} is not the live child of its klong in {p}"
  let left ← match ib with
    | some (ib, _) => do
      let (ls, lsn) ← sibling p pn ib inner
      if ia.isNone || lsn.cnt + xn.cnt ≤ c.p.mergeMax then pure (some (ib, ls, lsn))
      else pure none
    | none => pure none
  let (l, ln, il, r, rn, ir) ← match left with
    | some (ib, ls, lsn) => pure (ls, lsn, ib, x, xn, ix)
    | none =>
      match ia with
      | some (ia, _) => do
        let (rs, rsn) ← sibling p pn ia inner
        pure (x, xn, ix, rs, rsn, ia)
      | none => throw s!"Bug: merge at {tt}: key node {x} has no sibling in {p}"
  tl c x d p pn xn left.isSome l ln il r rn ir

theorem mergeChk_eqP (x : NodeId) (d : Nat) : mergeChk x d = mergeP mergeTailChk x d := rfl
theorem merge_eqP (x : NodeId) (d : Nat) : merge x d = mergeP mergeTail x d := rfl

/-! ## The merge's tail from what the merge reads -/

/-- The merge's tail for the two copies, at the state w3 after the merge's reads
from its start v: the parent p at depth d - 1 of the path, its live klongs to the
two nodes merged, these as v has them. The tail's facts come from the tree and
the take-back's node facts at v (`liveHolder_unique`). -/
theorem rwpq_tailAt (c : Ctx) (base : View BVal) (B : NodeId) (hvg : ViewGood B c)
    (hkv : ViewKlongsWf c.p c.view) (hv : ViewIdsBelow B c.view) (v : W)
    (hI : PutInv c base v) (hJ : TakeJ2 c base B v)
    (x : NodeId) (d : Nat) (hd : 0 < d) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hP : PathOK c v d X K Nn)
    (ls : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId) (rn : KNode) (ir : Nat) (cL cR : Nat)
    (hLL : (Nn (d - 1)).ks[il]? = some (.key cL l)) (hRR : (Nn (d - 1)).ks[ir]? = some (.key cR r))
    (hmL : (cL, l) ∈ (Nn (d - 1)).live) (hmR : (cR, r) ∈ (Nn (d - 1)).live) (hc : cL ≠ cR)
    (hwl : wNode c.p base v l = some ln) (hwr : wNode c.p base v r = some rn)
    (hxlr : (x = l ∧ Nn d = ln) ∨ (x = r ∧ Nn d = rn))
    (w3 : W) (hr3 : ReadsAs c.p base v w3) (hpre3 : v.nodes <+: w3.nodes) (hp3 : w3.path = v.path)
    (hl3 : w3.nodes.lookup l = some ln) (hr3l : w3.nodes.lookup r = some rn)
    (hcg3 : CacheGood B c w3) (hu3 : UniqueCache B w3) (hwk3 : WriterKlongsWf w3) :
    RWPQ (mergeTail c x d (X (d - 1)) (Nn (d - 1)) (Nn d) ls l ln il r rn ir)
      (mergeTailChk c x d (X (d - 1)) (Nn (d - 1)) (Nn d) ls l ln il r rn ir) c w3
      (fun xf => MergeEnd c base B xf.2) := by
  have hpos := hvg.pos
  obtain ⟨hpX, hpK, hlk, hlink, hX0⟩ := hP
  have hPL := pathOK_depth c base v d X K Nn ⟨hpX, hpK, hlk, hlink, hX0⟩
  have hT := hI.tree
  have hTi : TimesN (wNode c.p base v) c.i := fun q qn hq s hs => hI.times q qn hq s hs
  obtain ⟨hTt, _, hOB, _, _, _⟩ := hJ
  have hwp : wNode c.p base v (X (d - 1)) = some (Nn (d - 1)) := by
    obtain ⟨a, b⟩ := hlk (d - 1) (by omega)
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hpt := hI.times _ _ hwp
  have hlA : (cL, l) ∈ (Nn (d - 1)).liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hpt]; exact hmL
  have hrA : (cR, r) ∈ (Nn (d - 1)).liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hpt]; exact hmR
  have hpR : TReach (wNode c.p base v) c.i v.top.rootKey (X (d - 1)) := (hPL (d - 1) (by omega)).reach
  have hTL : TLink (wNode c.p base v) c.i (X (d - 1)) cL l := ⟨_, hwp, hlA⟩
  have hTR : TLink (wNode c.p base v) c.i (X (d - 1)) cR r := ⟨_, hwp, hrA⟩
  have hlR : TReach (wNode c.p base v) c.i v.top.rootKey l := TReach.link hpR hTL
  have hrR : TReach (wNode c.p base v) c.i v.top.rootKey r := TReach.link hpR hTR
  have hlr : l ≠ r := by
    intro he; subst he
    exact hc (hT.oneLink _ _ _ _ _ hpR hpR hTL hTR).2
  have hlp : l ≠ X (d - 1) := by
    intro he; rw [he] at hTL; exact hT.no_self_link _ _ hpR hTL
  have hrp : r ≠ X (d - 1) := by
    intro he; rw [he] at hTR; exact hT.no_self_link _ _ hpR hTR
  have hlPL : PathLen (wNode c.p base v) c.i v.top.rootKey l (d - 1 + 1) := PathLen.link (hPL (d - 1) (by omega)) hTL
  have hrPL : PathLen (wNode c.p base v) c.i v.top.rootKey r (d - 1 + 1) := PathLen.link (hPL (d - 1) (by omega)) hTR
  have hab : ∀ i e, i + 1 ≤ d - 1 → v.path[i]? = some e → e.2 ≠ l ∧ e.2 ≠ r := by
    intro i e hi he
    have h1 := hpX i (by omega)
    rw [he] at h1
    simp only [Option.map_some, Option.some.injEq] at h1
    rw [h1]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := PathLen.depth_unique hT _ _ _ (hPL i (by omega)) (by rw [h]; exact hlPL); omega
    · have := PathLen.depth_unique hT _ _ _ (hPL i (by omega)) (by rw [h]; exact hrPL); omega
  have hgl : Good B c l ln := cacheGood_lookup B c w3 hcg3 l ln hl3
  have hgr : Good B c r rn := cacheGood_lookup B c w3 hcg3 r rn hr3l
  have hlB : ln.firstTime = some c.i → B ≤ l := fun h =>
    Blank.ge B c l hvg (blank_of_firstTime B c l ln hpos hgl (by simp [h]))
  have hrB : rn.firstTime = some c.i → B ≤ r := fun h =>
    Blank.ge B c r hvg (blank_of_firstTime B c r rn hpos hgr (by simp [h]))
  have hold : ∀ o co, TLink (wNode c.p base v) c.i (X (d - 1)) co o → B ≤ o →
      ∀ q qn, wNode c.p base v q = some qn → q ≠ X (d - 1) → ∀ cv, (cv, o) ∉ qn.live := by
    intro o co hTo hBo q qn hq hqp cv hm
    have hmA : (cv, o) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i (hI.times q qn hq)]; exact hm
    exact hqp (liveHolder_unique _ c.i v.top.rootKey B hpos hTt hOB hTi hT o hBo (X (d - 1)) co hpR hTo
      q qn hq cv hmA).1
  have hI3 : TInvP B c w3 w3.path l r ln rn (X (d - 1)) (Nn (d - 1)) w3 := by
    have hp3l : w3.nodes.lookup (X (d - 1)) = some (Nn (d - 1)) :=
      lookup_of_prefix _ _ hpre3 _ _ (hlk (d - 1) (by omega)).1
    refine ⟨⟨⟨hl3, hu3.1.2.1 _ (bk_mem_of_lookup _ _ _ hl3), rfl⟩,
      ⟨hr3l, hu3.1.2.1 _ (bk_mem_of_lookup _ _ _ hr3l), rfl⟩, hcg3, hu3, hwk3, fun _ h => h⟩,
      ⟨hp3l, hu3.1.2.1 _ (bk_mem_of_lookup _ _ _ hp3l), rfl⟩⟩
  refine rwpq_mergeTail c base B hvg hkv hv x d (X (d - 1)) (Nn (d - 1)) (Nn d) ls l ln il r rn ir w3 w3.path hI3
    (by rcases hxlr with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩) hlr hlp hrp
    (fun i e hi he => hab i e hi (by rw [← hp3]; exact he)) ?_ hlB hrB
    (fun h => hold l cL hTL (hlB h) l ln hwl hlp) (fun h => hold l cL hTL (hlB h) r rn hwr hrp)
    (fun h => hold r cR hTR (hrB h) r rn hwr hrp) (fun h => hold r cR hTR (hrB h) l ln hwl hlp)
  intro cR' hcv
  have : cR' = cR := by unfold KNode.cv? at hcv; rw [hRR] at hcv; simp at hcv; exact hcv.symm
  subst this
  exact List.mem_map.mpr ⟨(cR', r), hmR, rfl⟩

theorem writerWP_sibling_all (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (base : View BVal) (hvc : ViewCoherent c base) (B : NodeId) (hvg : ViewGood B c) (hcg : CacheGood B c w)
    (hv : ViewIdsBelow B c.view) (hu : UniqueCache B w) (hkv : ViewKlongsWf c.p c.view)
    (hwk : WriterKlongsWf w) :
    WriterWP (sibling p pn i inner) c w (fun sn v => pn.ptr? i = some sn.1 ∧
      ReadsAs c.p base w v ∧ v.nodes.lookup sn.1 = some sn.2 ∧
      (w.taken.contains sn.1 = false → wNode c.p base w sn.1 = some sn.2) ∧ w.nodes <+: v.nodes ∧
      CacheGood B c v ∧ UniqueCache B v ∧ WriterKlongsWf v ∧ v.path = w.path) := by
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and (writerWP_and
    (writerWP_sibling_leaf p pn i inner c w base hvc) (good_sibling_res B p pn i inner c w hvg hcg))
    (writerWP_sibling_uniqueCache B p pn i inner c w hv hu)) (klongsWf_sibling p pn i inner c w hkv hwk))
    (writerWP_sibling_path p pn i inner c w)) ?_
  rintro sn v ⟨⟨⟨⟨⟨h1, h2, h3, h4, h5, _, _⟩, h6, _⟩, h7, _⟩, h8, _⟩, h9⟩
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

set_option maxHeartbeats 3200000 in
/-- The merge for the two copies, from its start v, with the merge's end as the
postcondition: the merge's reads, then its tail (`rwpq_tailAt`). -/
theorem rwpq_merge (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (B : NodeId) (hvg : ViewGood B c)
    (hkv : ViewKlongsWf c.p c.view) (hv : ViewIdsBelow B c.view) (v : W)
    (hI : PutInv c base v) (hJ : TakeJ2 c base B v)
    (hcg : CacheGood B c v) (hu : UniqueCache B v) (hwk : WriterKlongsWf v)
    (x : NodeId) (d : Nat) (hd : 0 < d) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (hP : PathOK c v d X K Nn) (hXd : X d = x) :
    RWPQ (merge x d) (mergeChk x d) c v (fun xf => MergeEnd c base B xf.2) := by
  have hP' := hP
  obtain ⟨hpX, hpK, hlk, hlink, hX0⟩ := hP'
  have hPL := pathOK_depth c base v d X K Nn hP
  have hwx : wNode c.p base v x = some (Nn d) := by
    obtain ⟨a, b⟩ := hlk d (Nat.le_refl _)
    rw [← hXd]; simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hpR : TReach (wNode c.p base v) c.i v.top.rootKey (X (d - 1)) := (hPL (d - 1) (by omega)).reach
  have hwp : wNode c.p base v (X (d - 1)) = some (Nn (d - 1)) := by
    obtain ⟨a, b⟩ := hlk (d - 1) (by omega)
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hpt := hI.times _ _ hwp
  have hchild : ∀ z cz, (cz, z) ∈ (Nn (d - 1)).live → v.taken.contains z = false := by
    intro z cz hz
    have hzA : (cz, z) ∈ (Nn (d - 1)).liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hpt]; exact hz
    exact hI.untaken z (tReach_reachS _ _ _ _ (TReach.link hpR ⟨_, hwp, hzA⟩))
  show RWPQ (mergeP mergeTail x d) (mergeP mergeTailChk x d) c v _
  unfold mergeP
  refine rwpq_bind (fun a v' => a = c ∧ v' = v) ((writerWP_read c v _).mpr ⟨rfl, rfl⟩) ?_
  rintro c0 v' ⟨hc0, hv'⟩
  subst c0; subst v'
  refine rwpq_bind (fun a v' => a = X (d - 1) ∧ v' = v)
    (writerWP_pathNode_known (d - 1) (X (d - 1)) c v (hpX (d - 1) (by omega)) _ ⟨rfl, rfl⟩) ?_
  rintro p v' ⟨hp', hv'⟩
  subst p; subst v'
  refine rwpq_bind (fun a v' => a = Nn (d - 1) ∧ v' = v)
    ((writerWP_getNode_known _ _ c v (hlk (d - 1) (by omega)).1 _).mpr ⟨rfl, rfl⟩) ?_
  rintro pn v' ⟨hpn', hv'⟩
  subst pn; subst v'
  refine rwpq_bind (fun a v' => a = Nn d ∧ v' = v)
    ((writerWP_getNode_known _ _ c v (by rw [← hXd]; exact (hlk d (Nat.le_refl _)).1) _).mpr ⟨rfl, rfl⟩) ?_
  rintro xn v' ⟨hxn', hv'⟩
  subst xn; subst v'
  refine rwpq_bind (fun a v' => a = K d ∧ v' = v)
    (writerWP_klongAt_known d (K d) x c v (by rw [← hXd]; exact hpK d hd (Nat.le_refl _)) _ ⟨rfl, rfl⟩) ?_
  rintro cx v' ⟨hcx', hv'⟩
  subst cx; subst v'
  dsimp only
  have hML := mergeIdx_last (Nn (d - 1)) (K d)
  rcases hmi : mergeIdx (Nn (d - 1)) (K d) with ⟨ixo, ia, ib⟩
  rw [hmi] at hML
  obtain ⟨hMx, hMa, hMb⟩ := hML
  cases ixo with
  | none => exact rwpq_throw_bind _ _ _ _ _ _
  | some ix =>
    simp only [pure_bind]
    refine rwpq_ite (fun _ => rwpq_throw_bind _ _ _ _ _ _) (fun hptr => ?_)
    have hpx : (Nn (d - 1)).ptr? ix = some x := by simpa using hptr
    obtain ⟨hkx, hmx⟩ := ht_live_of_last (hMx ix rfl) hpx
    have hlkx : v.nodes.lookup x = some (Nn d) := by rw [← hXd]; exact (hlk d (Nat.le_refl _)).1
    cases ib with
    | some ibp =>
      rcases ibp with ⟨ib, cvb⟩
      obtain ⟨hLb, hcb⟩ := hMb ib cvb rfl
      refine rwpq_bind _ (writerWP_sibling_all _ _ ib (!(Nn d).leaf) c v base hvc B hvg hcg hv hu hkv hwk) ?_
      rintro ⟨ls, lsn⟩ v6 ⟨hpls, hr6, hl6, hw6, hpre6, hcg6, hu6, hwk6, hp6⟩
      simp only at hpls hl6 hw6
      obtain ⟨hkls, hmls⟩ := ht_live_of_last hLb hpls
      have hwls : wNode c.p base v ls = some lsn := hw6 (hchild ls cvb hmls)
      refine rwpq_ite (fun _ => ?_) (fun _ => ?_)
      · simp only [pure_bind]
        exact rwpq_tailAt c base B hvg hkv hv v hI hJ x d hd X K Nn hP true ls lsn ib x (Nn d) ix cvb (K d)
          hkls hkx hmls hmx (by omega) hwls hwx (Or.inr ⟨rfl, rfl⟩) v6 hr6 hpre6 hp6 hl6
          (lookup_of_prefix _ _ hpre6 _ _ hlkx) hcg6 hu6 hwk6
      · try simp only [pure_bind]
        cases ia with
        | none => exact rwpq_throw_bind _ _ _ _ _ _
        | some iap =>
          rcases iap with ⟨ia, cva⟩
          obtain ⟨hLa, hca⟩ := hMa ia cva rfl
          refine rwpq_bind _ (writerWP_sibling_all _ _ ia (!(Nn d).leaf) c v6 base hvc B hvg hcg6 hv hu6 hkv hwk6) ?_
          rintro ⟨rs, rsn⟩ v7 ⟨hprs, hr7, hl7, hw7, hpre7, hcg7, hu7, hwk7, hp7⟩
          simp only at hprs hl7 hw7
          obtain ⟨hkrs, hmrs⟩ := ht_live_of_last hLa hprs
          have hwrs6 : wNode c.p base v6 rs = some rsn := hw7 (by rw [hr6.2.2.1]; exact hchild rs cva hmrs)
          have hwrs : wNode c.p base v rs = some rsn := by rw [← hr6.1]; exact hwrs6
          simp only [pure_bind]
          exact rwpq_tailAt c base B hvg hkv hv v hI hJ x d hd X K Nn hP false x (Nn d) ix rs rsn ia (K d) cva
            hkx hkrs hmx hmrs (by omega) hwx hwrs (Or.inl ⟨rfl, rfl⟩) v7 (ReadsAs.trans _ _ _ _ _ hr6 hr7)
            (hpre6.trans hpre7) (by rw [hp7, hp6]) (lookup_of_prefix _ _ (hpre6.trans hpre7) _ _ hlkx) hl7
            hcg7 hu7 hwk7
    | none =>
      simp only [pure_bind]
      cases ia with
      | none => exact rwpq_throw_bind _ _ _ _ _ _
      | some iap =>
        rcases iap with ⟨ia, cva⟩
        obtain ⟨hLa, hca⟩ := hMa ia cva rfl
        refine rwpq_bind _ (writerWP_sibling_all _ _ ia (!(Nn d).leaf) c v base hvc B hvg hcg hv hu hkv hwk) ?_
        rintro ⟨rs, rsn⟩ v7 ⟨hprs, hr7, hl7, hw7, hpre7, hcg7, hu7, hwk7, hp7⟩
        simp only at hprs hl7 hw7
        obtain ⟨hkrs, hmrs⟩ := ht_live_of_last hLa hprs
        have hwrs : wNode c.p base v rs = some rsn := hw7 (hchild rs cva hmrs)
        simp only [pure_bind]
        exact rwpq_tailAt c base B hvg hkv hv v hI hJ x d hd X K Nn hP false x (Nn d) ix rs rsn ia (K d) cva
          hkx hkrs hmx hmrs (by omega) hwx hwrs (Or.inl ⟨rfl, rfl⟩) v7 hr7 hpre7 hp7
          (lookup_of_prefix _ _ hpre7 _ _ hlkx) hl7 hcg7 hu7 hwk7

end SIS.Tree
