/-
Proofs about reclaim, part 10 (bergdb item 001, WP R5): the nodes of D that
no lookup from f on may reach (M33, M34). Rule A with BergDB's test keeps a
node in D while one of its pointees is in D, lowest level first. So the
ancestors of a node of D at a time it was reachable stay in D with it, and
each of them whose entry in D is later than that time was put back, with a
version in the record of its entry. With a virtual root, the root children
created after a root child of D are in D too. After a restart from a cut
stream, startup reads such a node through its ancestors' versions in the
startup section (Rule R); T12 needs that.
-/
import SIS.Proof.EvLogic
import SIS.Proof.Fresh
import SIS.Proof.CutRecover

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The nodes below a node at a time t are those below it in a structure that
extends P from t on. -/
theorem reachFrom_grow {sp : Spec V T} {P P' : Struct V} {k t : Time} (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hg : Grow P k P') (ht : t ≤ k) :
    ∀ (b : Nat) (x : NodeId) (n n' : Node V), n.level < b → P.get? x = some n →
      P'.get? x = some n' → reachFrom sp P' t x n' = reachFrom sp P t x n := by
  intro b
  induction b with
  | zero => intro x n n' h; omega
  | succ b ih =>
    intro x n n' hb hx hx'
    obtain ⟨n1, h1, hl, -, hh⟩ := hg x n hx
    have h1' : n1 = n' := by rw [hx'] at h1; exact (Option.some.inj h1).symm
    subst h1'
    have hht : n1.hist.upTo t = n.hist.upTo t := upTo_eq_of_le ht hh
    rw [reachFrom_eq, reachFrom_eq, hht, hl]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    obtain ⟨m, hm, hlt⟩ := hp x n hx e (mem_upTo.mp he).1 y hye
    obtain ⟨m', hm', hml, -, -⟩ := hg y m hm
    rw [hm, hm']
    simp only [hml]
    by_cases hc : m.level < n.level
    · simp only [hc, ↓reduceIte]
      exact ih y m m' (by omega) hm hm'
    · simp only [hc, ↓reduceIte]

/-- p is an ancestor of x at time t in P, x itself included: a node that can be
written, reachable at t, with x below it then. -/
def Anc (sp : Spec V T) (P : Struct V) (t : Time) (x p : NodeId) : Prop :=
  written sp p = true ∧ reachable sp P t p = true ∧
    ∃ np, P.get? p = some np ∧ x ∈ reachFrom sp P t p np

theorem anc_grow {sp : Spec V T} {P P' : Struct V} {k t : Time} (hls : LiveSub sp)
    (hp : PtrsOK sp P) (hroot : (P.get? root).isSome) (hg : Grow P k P') (ht : t ≤ k)
    (x p : NodeId) : Anc sp P' t x p ↔ Anc sp P t x p := by
  constructor
  · rintro ⟨hw, hr, np', hnp', hx⟩
    rw [reachable_grow hls hp hroot hg ht] at hr
    obtain ⟨np, hnp⟩ := Option.isSome_iff_exists.mp ((reachable_iff _ _ _ _).mp hr).isSome
    refine ⟨hw, hr, np, hnp, ?_⟩
    rw [← reachFrom_grow hls hp hg ht (np.level + 1) p np np' (Nat.lt_succ_self _) hnp hnp']
    exact hx
  · rintro ⟨hw, hr, np, hnp, hx⟩
    obtain ⟨np', hnp', -⟩ := hg p np hnp
    refine ⟨hw, by rw [reachable_grow hls hp hroot hg ht]; exact hr, np', hnp', ?_⟩
    rw [reachFrom_grow hls hp hg ht (np.level + 1) p np np' (Nat.lt_succ_self _) hnp hnp']
    exact hx

/-- Every node x of D was reachable at a time t at which each of its ancestors
(x included) is now in D, with an entry from time t + 1 at the latest, or with
a version in the record of its entry (it was put back). -/
def DAnchor (sp : Spec V T) (db : DB V T) (k : Nat) : Prop :=
  ∀ x, inD db.D x = true → ∃ t ≤ k, reachable sp db.P t x = true ∧
    ∀ p, Anc sp db.P t x p → ∃ d, (p, d) ∈ db.D ∧ (d ≤ t + 1 ∨ (db.S.versionAt d p).isSome)

section Step

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- Rule A with BergDB's test: a node of D1 with a pointee in the new D is in
the new D. -/
theorem step_persist (hj : al.stillDirty = javaTest sp) (hsp : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {p q : NodeId}
    {np : Node V} (hp : inD (parts sp al db tr).D1 p = true)
    (hnp : (parts sp al db tr).P.get? p = some np) (hq : q ∈ pointees sp np.hist)
    (hqD : inD (parts sp al db tr).r7.1 q = true) : inD (parts sp al db tr).r7.1 p = true := by
  by_cases ht : p ∈ (parts sp al db tr).taken
  · exact step_inD_r7_of_put sp al db tr hinv
      ((step_java_pointee sp al db tr hj hsp hinv hstep ht hnp).mpr ⟨q, hq, hqD⟩)
  · obtain ⟨d, hd⟩ := (inD_iff _ _).mp hp
    exact step_inD_r7_of_D2 sp al db tr hinv (step_D2_of_not_taken sp al db tr hd ht)

/-- With x in the new D, every ancestor of x at a time t that is in D1 is in
the new D: its child towards x is in it, on a lower level. -/
theorem step_anc_persist (hj : al.stillDirty = javaTest sp) (hsp : SpecOK sp) {k : Nat}
    (hinv : Inv sp db k) (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {x : NodeId}
    {t : Time} (hx : inD (parts sp al db tr).r7.1 x = true)
    (hD1 : ∀ p, Anc sp db.P t x p → inD (parts sp al db tr).D1 p = true) :
    ∀ (b : Nat) (p : NodeId) (np : Node V), np.level < b → db.P.get? p = some np →
      Anc sp db.P t x p → inD (parts sp al db tr).r7.1 p = true := by
  have hls : LiveSub sp := hsp.liveSub
  intro b
  induction b with
  | zero => intro p np h; omega
  | succ b ih =>
    intro p np hb hnp hanc
    obtain ⟨hw, hr, np', hnp', hxp⟩ := id hanc
    have h' : np' = np := by rw [hnp] at hnp'; exact (Option.some.inj hnp').symm
    subst h'
    rw [reachFrom_eq] at hxp
    simp only [List.mem_cons, List.mem_flatMap] at hxp
    rcases hxp with hxp | ⟨q, hq, hxq⟩
    · rw [← hxp]; exact hx
    · split at hxq
      · rename_i m hm
        split at hxq
        · rename_i hlt
          obtain ⟨e, he, hqe⟩ := hls _ _ hq
          have hqw : written sp q = true :=
            written_of_ne_root sp (hinv.ptr_ne_root hnp (mem_upTo.mp he).1 hqe)
          have hqr : reachable sp db.P t q = true :=
            (reachable_iff _ _ _ _).mpr (Reach.child ((reachable_iff _ _ _ _).mp hr) hnp hq hm hlt)
          have hqD := ih q m (by omega) hm ⟨hqw, hqr, m, hm, hxq⟩
          exact step_persist sp al db tr hj hsp hinv hstep (hD1 p hanc)
            (step_P_old sp al db tr hinv.len hnp)
            ((mem_pointees sp _ q).mpr ⟨e, List.mem_append_left _ (mem_upTo.mp he).1, hqe⟩) hqD
        · simp at hxq
      · simp at hxq

/-- The entries of the new D are those of D2, or the nodes put back, with
d = k + 1. -/
theorem step_D_entry {k : Nat} (hinv : Inv sp db k) {p : NodeId} {d : Nat}
    (h : (p, d) ∈ (parts sp al db tr).r7.1) :
    (p, d) ∈ (parts sp al db tr).D2 ∨ (d = k + 1 ∧ p ∈ (parts sp al db tr).r7.2) := by
  rw [(step_r7_shape sp al db tr hinv.len).1] at h
  rcases List.mem_append.mp h with h1 | h1
  · exact Or.inl h1
  · obtain ⟨z, hz, hze⟩ := List.mem_map.mp h1
    simp only [Prod.mk.injEq] at hze
    obtain ⟨rfl, rfl⟩ := hze
    exact Or.inr ⟨rfl, hz⟩

/-- An entry of the new D is from time k + 1 at the latest. -/
theorem step_D_entry_le {k : Nat} (hinv : Inv sp db k) {p : NodeId} {d : Nat}
    (h : (p, d) ∈ (parts sp al db tr).r7.1) : d ≤ k + 1 := by
  rcases step_D_entry sp al db tr hinv h with h1 | ⟨h1, -⟩
  · rcases step_D2_cases sp al db tr hinv h1 with ⟨-, h2⟩ | ⟨h2, -⟩ <;> omega
  · omega

/-- A node put back has a version in the new record. -/
theorem step_put_version {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) {p : NodeId}
    (hp : p ∈ (parts sp al db tr).r7.2) :
    ((db.S ++ [(parts sp al db tr).R]).versionAt (k + 1) p).isSome := by
  have ht : p ∈ (parts sp al db tr).taken := (step_r7_shape sp al db tr hinv.len).2.subset hp
  have hm : p ∈ (parts sp al db tr).vs.map (·.node) := by
    rw [step_vs_nodes' sp al db tr hinv hstep]
    exact List.mem_append_right _ ht
  obtain ⟨w, hw, hwp⟩ := List.mem_map.mp hm
  rw [← hinv.len, versionAt_snoc_self, parts_R]
  simp only
  rw [Option.isSome_iff_exists]
  cases hf : (parts sp al db tr).vs.find? (fun v => v.node == p) with
  | some u => exact ⟨u, rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf w hw
    simp [hwp] at this

/-- D stays closed upward. -/
theorem step_dClosed (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hsp : SpecOK sp)
    {k : Nat} (hinv : Inv sp db k) (hcl : DClosed sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    DClosed sp (step sp al db tr) (k + 1) := by
  intro x n y hw hr hx hy hyx
  rw [step_D] at hy ⊢
  exact step_closed sp al db tr hj hmk hsp hinv hcl hstep (n.level + 1) x n (Nat.lt_succ_self _)
    hw hr hx y hy hyx

/-- The anchors stay: a node that stays in D keeps its time, and its ancestors
then stay in D (Rule A), each with its entry, or put back with a version in the
new record; a node that got dirty now has its time now (marked; D is closed
upward) or just before (touched; its ancestors then are touched too). -/
theorem step_dAnchor (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hsp : SpecOK sp)
    {k : Nat} (hinv : Inv sp db k) (hcl : DClosed sp db k) (ha : DAnchor sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    DAnchor sp (step sp al db tr) (k + 1) := by
  have hls : LiveSub sp := hsp.liveSub
  have hgrow := step_grow sp al db tr hinv.len
  have hcl' := step_dClosed sp al db tr hj hmk hsp hinv hcl hstep
  intro x hx
  rw [step_D] at hx
  rw [step_P, step_D, step_S, Snew]
  -- Every entry of the new D: from time k + 1 at the latest.
  have hle : ∀ p, inD (parts sp al db tr).r7.1 p = true →
      ∃ d, (p, d) ∈ (parts sp al db tr).r7.1 ∧ d ≤ k + 1 := by
    intro p hp
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hp
    exact ⟨d, hd, step_D_entry_le sp al db tr hinv hd⟩
  cases hxD : inD db.D x
  · -- x got dirty now.
    rcases step_D1_cases sp al db tr hmk hinv (step_r7_D1 sp al db tr hinv hx) with h | h | h
    · rw [hxD] at h; cases h
    · -- Marked: reachable now; its ancestors now are in the new D.
      have hr : reachable sp (parts sp al db tr).P (k + 1) x = true := by
        unfold marked at h; rw [Bool.and_eq_true] at h; exact h.1
      refine ⟨k + 1, Nat.le_refl _, hr, ?_⟩
      rintro p ⟨hw, hrp, np, hnp, hxp⟩
      obtain ⟨d, hd, hdk⟩ := hle p (hcl' p np x hw hrp hnp hx hxp)
      exact ⟨d, hd, Or.inl (by omega)⟩
    · -- Touched: reachable at k; its ancestors then are touched too.
      have hr0 : reachable sp db.P k x = true := by
        have := hstep.touchReach x h; simpa using this
      have hr : reachable sp (parts sp al db tr).P k x = true := by
        rw [reachable_grow hls hinv.ptrs hinv.rootIn hgrow (Nat.le_refl _)]; exact hr0
      refine ⟨k, by omega, hr, ?_⟩
      intro p hp
      have hp0 : Anc sp db.P k x p := (anc_grow hls hinv.ptrs hinv.rootIn hgrow (Nat.le_refl _) x p).mp hp
      obtain ⟨-, -, np, hnp, -⟩ := id hp0
      have hD1 : ∀ p', Anc sp db.P k x p' → inD (parts sp al db tr).D1 p' = true := by
        rintro p' ⟨hw', hr', np', hnp', hxp'⟩
        exact step_touch_D1 sp al db tr hinv hstep hw' hr' hnp' h hxp'
      obtain ⟨d, hd, hdk⟩ := hle p (step_anc_persist sp al db tr hj hsp hinv hstep hx hD1
        (np.level + 1) p np (Nat.lt_succ_self _) hnp hp0)
      exact ⟨d, hd, Or.inl (by omega)⟩
  · -- x stays in D: the same time.
    obtain ⟨t, htk, hrt, hanc⟩ := ha x hxD
    refine ⟨t, by omega, by rw [reachable_grow hls hinv.ptrs hinv.rootIn hgrow htk]; exact hrt, ?_⟩
    intro p hp
    have hp0 : Anc sp db.P t x p := (anc_grow hls hinv.ptrs hinv.rootIn hgrow htk x p).mp hp
    obtain ⟨d0, hd0, hd0t⟩ := hanc p hp0
    obtain ⟨-, -, np, hnp, -⟩ := id hp0
    have hD1 : ∀ p', Anc sp db.P t x p' → inD (parts sp al db tr).D1 p' = true := by
      intro p' hp'
      obtain ⟨d', hd', -⟩ := hanc p' hp'
      exact (inD_iff _ _).mpr ⟨d', (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd')⟩
    have hpD := step_anc_persist sp al db tr hj hsp hinv hstep hx hD1 (np.level + 1) p np
      (Nat.lt_succ_self _) hnp hp0
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hpD
    rcases step_D_entry sp al db tr hinv hd with h1 | ⟨h1, h2⟩
    · -- Not taken: its entry.
      rcases step_D2_cases sp al db tr hinv h1 with ⟨h3, -⟩ | ⟨-, -, h3⟩
      · have hdd : d = d0 := by
          have := eq_of_map_nodup hinv.dNodup h3 hd0 rfl
          simp only [Prod.mk.injEq] at this
          exact this.2
        subst hdd
        refine ⟨d, hd, ?_⟩
        rcases hd0t with h4 | h4
        · exact Or.inl h4
        · right
          have hdl : d < db.S.length := by
            rw [hinv.inv1] at h3; exact (sectionD_mem h3).2.1
          rw [versionAt_append_left hdl]; exact h4
      · have : inD db.D p = true := (inD_iff _ _).mpr ⟨d0, hd0⟩
        rw [this] at h3; cases h3
    · -- Put back: a version in the new record.
      subst h1
      exact ⟨k + 1, hd, Or.inr (step_put_version sp al db tr hinv hstep h2)⟩

end Step

/-! ### With a virtual root: the root children after a root child of D -/

/-- With a virtual root: every root child created after a root child of D is
in D. -/
def TopsD (sp : Spec V T) (db : DB V T) : Prop :=
  ∀ z mz cz y my cy, TopAt sp db.P z mz cz → TopAt sp db.P y my cy → cz < cy →
    inD db.D z = true → inD db.D y = true

section Tops

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- With a virtual root: the root children that R4 reaches from a root child
were created no later. -/
theorem Inv.topClosure_older' (hinv : Inv sp db k) (hv : sp.virt = true) :
    ∀ (b : Nat) (z : NodeId) (m : Node V) (cz : Time), m.level < b → TopAt sp db.P z m cz →
      ∀ y ∈ topClosure sp db.P z m, ∃ my cy, TopAt sp db.P y my cy ∧ cy ≤ cz := by
  have hvi := hinv.vr hv
  intro b
  induction b with
  | zero => intro z m cz h; omega
  | succ b ih =>
    intro z m cz hb hzt y hy
    rw [topClosure_eq sp] at hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨m, cz, hzt, Nat.le_refl _⟩
    · obtain ⟨y', hy', hy⟩ := List.mem_flatMap.mp hy
      split at hy
      · rename_i my' hmy'
        split at hy
        · rename_i hc
          have hy'r : y' ≠ root := by
            obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y').mp hy'
            exact hinv.ptr_ne_root hzt.1 he hye
          have hyt : isTop sp db.P y' = true := isTop_iff.mpr ⟨hy'r, my', hmy', hc.1⟩
          obtain ⟨m'', c'', hyt'', hlt⟩ := hvi.older z m cz hzt y' hy' hyt
          have hm'' : m'' = my' := by
            have := hyt''.1; rw [hmy'] at this; exact (Option.some.inj this).symm
          subst hm''
          obtain ⟨my, cy, hyt2, hle⟩ := ih y' m'' c'' (by omega) hyt'' y hy
          exact ⟨my, cy, hyt2, by omega⟩
        · simp at hy
      · simp at hy

/-- With a virtual root: a root child reachable at k is the root's live child
then (the root children that root children point to are dead), so no root
child was created after it. -/
theorem Inv.top_reach_last (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp)
    (hls : LiveSub sp) {z : NodeId} {mz : Node V} {cz : Time} (hzt : TopAt sp db.P z mz cz)
    (hr : reachable sp db.P k z = true) {y : NodeId} {my : Node V} {cy : Time}
    (hyt : TopAt sp db.P y my cy) : cy ≤ cz := by
  have hvi := hinv.vr hv
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hcy : cy ≤ k := by
    obtain ⟨e, he, hec⟩ := hyt.exists_entry
    have := hinv.times y my hyt.1 e he
    omega
  cases (reachable_iff _ _ _ _).mp hr with
  | root n hn => exact absurd rfl hzt.2.1
  | @child x _ n m hx hxn hz hzm hlt =>
    by_cases hxr : x = root
    · subst hxr
      rw [h0, Option.some.injEq] at hxn
      subst hxn
      cases hl : (n0.hist.upTo k).getLast? with
      | none =>
        exfalso
        have hrootE : ∀ e ∈ n0.hist.upTo k, ∃ z, e.val = sp.rootVal z := fun e he => by
          obtain ⟨z', m', -, hval⟩ := hvi.rootEntry n0 h0 e (mem_upTo.mp he).1; exact ⟨z', hval⟩
        rw [hvl hv _ hrootE, hl] at hz
        simp at hz
      | some e =>
        obtain ⟨z', m', hzt', -, -, -, hlz, -⟩ := hinv.rootLast hv hvl h0 hl
        rw [hlz, List.mem_singleton] at hz
        subst hz
        have hce : cz = e.time := TopAt.time_unique hzt hzt'
        rw [hce]
        exact getLast_time_max ((hvi.rootSorted n0 h0).filter _) hl
          (mem_upTo.mpr ⟨hvi.topEntry y my cy hyt n0 h0, hcy⟩)
    · exfalso
      have hmz : m = mz := by rw [hzt.1] at hzm; exact (Option.some.inj hzm).symm
      subst hmz
      have hxt : isTop sp db.P x = true :=
        isTop_iff.mpr ⟨hxr, n, hxn, by have := hzt.2.2.1; omega⟩
      have := hvi.deadTops x n hxn hxt z (mem_pointees_of_live hls hz) hzt.isTop
      rw [hr] at this
      cases this

end Tops

section TopsStep

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

/-- A node that got dirty now is in the new D: its entry, k + 1, is after the
startup pos. -/
theorem step_gd3_inD {k : Nat} (hinv : Inv sp db k) {x : NodeId}
    (hx : x ∈ (parts sp al db tr).gd3) : inD (parts sp al db tr).r7.1 x = true := by
  have hD1 : (x, k + 1) ∈ (parts sp al db tr).D1 :=
    (step_D1_mem sp al db tr hinv.len _).mpr (Or.inr ⟨rfl, hx⟩)
  have hs := step_s_le sp al db tr hinv.len
  exact step_inD_r7_of_D2 sp al db tr hinv
    ((inD_iff _ _).mpr ⟨k + 1, (step_D2_mem sp al db tr _).mpr ⟨hD1, by simp only; omega⟩⟩)

/-- With marking, a new root child got dirty now. -/
theorem step_newTop_gd3 (hmk : al.mark = true) {k : Nat} (hinv : Inv sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hv : sp.virt = true) {nn : NewNode}
    (hnn : nn ∈ newTops sp al db tr) : nn.id ∈ (parts sp al db tr).gd3 := by
  have ht := step_topAt_new sp al db tr hinv hstep hv hnn
  have hnew := ((mem_newTops sp al db tr).mp hnn).1
  have hd : nn.isData = false := ht.2.2.2.1
  have hr : reachable sp (parts sp al db tr).P (k + 1) nn.id = true := by
    rw [parts_P' sp al db tr hinv.len]; exact hstep.newReachable nn hnew
  apply step_gd3_of_marked sp al db tr hmk hinv.len ht.1
  · simp only [isIndex, ht.1, hd, Bool.not_false]
  · cases h : inD db.D nn.id
    · rfl
    · exfalso
      obtain ⟨d, hd⟩ := (inD_iff _ _).mp h
      have := isSome_of_isIndex (hinv.dIndex _ hd)
      rw [hstep.fresh nn hnew] at this
      cases this
  · exact written_of_ne_root sp ht.2.1
  · unfold marked
    rw [hr, ht.1]
    simp only [Bool.true_and]
    apply List.any_eq_true.mpr
    refine ⟨nn.id, self_mem_reachFrom sp _ _ _ _, ?_⟩
    simp only [changed, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
    exact Or.inl ⟨nn, hnew, rfl⟩

/-- With a virtual root, the root children after a root child of D stay in D
(Rule A along R4's pointers), and a new root child got dirty now. A root child
that got dirty now is reachable now or just before, so no older root child
is created after it. -/
theorem step_topsD (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hsp : SpecOK sp)
    (hv : sp.virt = true) (hvl : VirtLiveOK sp) {k : Nat} (hinv : Inv sp db k) (htd : TopsD sp db)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) :
    TopsD sp (step sp al db tr) := by
  have hls : LiveSub sp := hsp.liveSub
  have hvi := hinv.vr hv
  have hinv' : Inv sp (step sp al db tr) (k + 1) := by
    have hc : (parts sp al db tr).c = sp.exec tr (k + 1) (view sp db.P k) := by
      rw [parts_c, hinv.len]; rfl
    exact inv_step sp al (algOK_of sp al (Or.inl hj)).still (fun _ => hj) hsp hinv tr (hc ▸ hstep)
  intro z mz cz y my cy hzt hyt hlt hz
  rw [step_D] at hz ⊢
  rcases step_topAt_cases sp al db tr hinv hstep hv hyt with hyt0 | ⟨-, -, nn, hnn, rfl⟩
  · -- y is old, so z is too.
    have hcy : cy ≤ k := by
      obtain ⟨e, he, hec⟩ := hyt0.exists_entry
      have := hinv.times y my hyt0.1 e he
      omega
    have hzt0 : TopAt sp db.P z mz cz := by
      rcases step_topAt_cases sp al db tr hinv hstep hv hzt with h | ⟨hck, -⟩
      · exact h
      · omega
    cases hzD : inD db.D z
    · -- z got dirty now: reachable now or just before, so the newest root child.
      exfalso
      rcases step_D1_cases sp al db tr hmk hinv (step_r7_D1 sp al db tr hinv hz) with h | h | h
      · rw [hzD] at h; cases h
      · have hr : reachable sp (parts sp al db tr).P (k + 1) z = true := by
          unfold marked at h; rw [Bool.and_eq_true] at h; exact h.1
        have := hinv'.top_reach_last hv hvl hls (db := step sp al db tr) hzt hr hyt
        omega
      · have hr : reachable sp db.P k z = true := by
          have := hstep.touchReach z h; simpa using this
        have := hinv.top_reach_last hv hvl hls hzt0 hr hyt0
        omega
    · -- z stays in D: so do the root children after it, by level.
      have key : ∀ (b : Nat) (y : NodeId) (my : Node V) (cy : Time), my.level < b →
          TopAt sp db.P y my cy → cz < cy → inD (parts sp al db tr).r7.1 y = true := by
        intro b
        induction b with
        | zero => intro y my cy h; omega
        | succ b ih =>
          intro y my cy hb hyt1 hlt1
          have hyD : inD db.D y = true := htd z mz cz y my cy hzt0 hyt1 hlt1 hzD
          have hcl := hvi.closed y my cy z mz cz hyt1 hzt0 hlt1
          rw [topClosure_eq sp] at hcl
          rcases List.mem_cons.mp hcl with hzy | hcl
          · exfalso
            subst hzy
            have := TopAt.time_unique hzt0 hyt1
            omega
          · obtain ⟨y', hy', hcl⟩ := List.mem_flatMap.mp hcl
            split at hcl
            · rename_i my' hmy'
              split at hcl
              · rename_i hc
                have hy'r : y' ≠ root := by
                  obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y').mp hy'
                  exact hinv.ptr_ne_root hyt1.1 he hye
                have hyt' : isTop sp db.P y' = true := isTop_iff.mpr ⟨hy'r, my', hmy', hc.1⟩
                obtain ⟨m'', c'', hyt'', -⟩ := hvi.older y my cy hyt1 y' hy' hyt'
                have hm'' : m'' = my' := by
                  have := hyt''.1; rw [hmy'] at this; exact (Option.some.inj this).symm
                subst hm''
                obtain ⟨mz', cz', hzt', hle⟩ :=
                  hinv.topClosure_older' hv (m''.level + 1) y' m'' c'' (Nat.lt_succ_self _) hyt'' z hcl
                have hcz : cz' = cz := TopAt.time_unique hzt' hzt0
                subst hcz
                have hy'D : inD (parts sp al db tr).r7.1 y' = true := by
                  rcases Nat.lt_or_ge cz' c'' with h1 | h1
                  · exact ih y' m'' c'' (by omega) hyt'' h1
                  · have hc' : c'' = cz' := by omega
                    rw [hc'] at hyt''
                    rw [hinv.topAt_unique hv hyt'' hzt0]
                    exact hz
                have hyD1 : inD (parts sp al db tr).D1 y = true := by
                  obtain ⟨d, hd⟩ := (inD_iff _ _).mp hyD
                  exact (inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩
                exact step_persist sp al db tr hj hsp hinv hstep hyD1
                  (step_topAt_old sp al db tr hinv hstep hv hyt1).1 hy' hy'D
              · simp at hcl
            · simp at hcl
      exact key (my.level + 1) y my cy (Nat.lt_succ_self _) hyt0 hlt
  · -- y is new: it got dirty now.
    exact step_gd3_inD sp al db tr hinv (step_newTop_gd3 sp al db tr hmk hinv hstep hv hnn)

end TopsStep

/-! ### Along a run -/

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

theorem stepOK_st (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat} (hj : j < ts.length) :
    StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
  have hinv := inv_st sp al ts hok hst j (by omega)
  have h1 := hok.2 j hj
  rw [parts_c, hinv.len]
  simpa [st] using h1

theorem dClosed_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) : ∀ j ≤ ts.length, DClosed sp (st sp al ts j) j := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero =>
    intro _ x n y _ _ _ hy
    rw [st_zero, init_D] at hy
    simp [inD] at hy
  | succ j ih =>
    intro hjl
    have hinv := inv_st sp al ts hok hst j (by omega)
    rw [st_succ sp al ts (by omega)]
    exact step_dClosed sp al _ _ hj hmk hok.1 hinv (ih (by omega)) (stepOK_st sp al ts hok hst (by omega))

theorem dAnchor_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) : ∀ j ≤ ts.length, DAnchor sp (st sp al ts j) j := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero =>
    intro _ x hx
    rw [st_zero, init_D] at hx
    simp [inD] at hx
  | succ j ih =>
    intro hjl
    have hinv := inv_st sp al ts hok hst j (by omega)
    rw [st_succ sp al ts (by omega)]
    exact step_dAnchor sp al _ _ hj hmk hok.1 hinv (dClosed_st sp al ts hok hj hmk j (by omega))
      (ih (by omega)) (stepOK_st sp al ts hok hst (by omega))

theorem topsD_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hv : sp.virt = true) (hvl : VirtLiveOK sp) :
    ∀ j ≤ ts.length, TopsD sp (st sp al ts j) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero =>
    intro _ z mz cz y my cy _ _ _ hz
    rw [st_zero, init_D] at hz
    simp [inD] at hz
  | succ j ih =>
    intro hjl
    have hinv := inv_st sp al ts hok hst j (by omega)
    rw [st_succ sp al ts (by omega)]
    exact step_topsD sp al _ _ hj hmk hok.1 hv hvl hinv (ih (by omega))
      (stepOK_st sp al ts hok hst (by omega))

end Run

end SIS
