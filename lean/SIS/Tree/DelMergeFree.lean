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

end SIS.Tree
