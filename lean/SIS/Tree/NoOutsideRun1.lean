/-
The run machinery for the runs of `N.Within` (bergdb 025-03; NoOutsideBase.lean):
the get and the scan, the writer's tree, PutInv and the ranges over runs,
each lemma as in its own file (named in its docstring) with `Within` the runs with no
key node outside the level bounds.
-/
import SIS.Tree.NoOutsideBase

set_option autoImplicit false

namespace SIS.Tree.N

open SIS SIS.Check

/-- As `SIS.Tree.treeRun_get_snoc_past`, for the runs of `N.Within`. -/
theorem treeRun_get_snoc_past (p : Params) (hinv : InvPreserved p)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (t : Time) (ht : t ≤ ts.length)
    (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (treeRun p (ts ++ [tx]))) t key = get p (viewOf (treeRun p ts)) t key := by
  have hwpre := within_snoc_prefix p ts tx hw
  have hi := (hinv ts hwpre t ht).1
  have hi' := (hinv (ts ++ [tx]) hw t (by simp only [List.length_append, List.length_singleton]; omega)).1
  have hh := treeRun_highKindsOK p (ts ++ [tx])
  rw [treeRun_snoc] at hi' hh ⊢
  exact get_apply_past_of_invariants p (treeRun p ts) (ts.length + 1) t _ (by omega)
    (treeRun_highKindsOK p ts) hh (treeRun_dataEntriesOK p ts) hi hi' key hkey

/-- As `SIS.Tree.treeRun_get_eq_prefix`, for the runs of `N.Within`. -/
theorem treeRun_get_eq_prefix (p : Params) (hinv : InvPreserved p)
    (ts : List Tx) (hw : Within p ts) (t : Time) (ht : t ≤ ts.length)
    (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (treeRun p ts)) t key = get p (viewOf (treeRun p (ts.take t))) t key := by
  have hf : ∀ revts : List Tx, Within p revts.reverse → ∀ u ≤ revts.reverse.length,
      get p (viewOf (treeRun p revts.reverse)) u key =
        get p (viewOf (treeRun p (revts.reverse.take u))) u key := by
    intro revts
    induction revts with
    | nil => intro h u hu; simp only [List.reverse_nil, List.take_nil]
    | cons tx revts ih =>
      intro h u hu
      simp only [List.reverse_cons] at h hu ⊢
      by_cases hle : u ≤ revts.reverse.length
      · rw [treeRun_get_snoc_past p hinv revts.reverse tx h u hle key hkey,
          List.take_append_of_le_length hle]
        exact ih (within_snoc_prefix p revts.reverse tx h) u hle
      · have he : u = (revts.reverse ++ [tx]).length := by
          simp only [List.length_append, List.length_singleton] at hu ⊢
          omega
        rw [he, List.take_length]
  simpa only [List.reverse_reverse] using hf ts.reverse (by simpa using hw) t (by simpa using ht)

/-- As `SIS.Tree.getOK_of_latest`, for the runs of `N.Within`. -/
theorem getOK_of_latest (p : Params) (hinv : InvPreserved p) (hlatest : LatestGetOK p) : GetOK p := by
  intro ts hw t ht key hkey
  rw [treeRun_get_eq_prefix p hinv ts hw t ht key hkey]
  have hlen : (ts.take t).length = t := by simp only [List.length_take, Nat.min_eq_left ht]
  have he := hlatest (ts.take t) (within_take p ts hw t) key hkey
  rw [hlen, refGet_take_eq ts t t (Nat.le_refl _) key] at he
  exact he

/-- As `SIS.Tree.latestGetOK_of_txGet`, for the runs of `N.Within`. -/
theorem latestGetOK_of_txGet (p : Params) (htx : TxGetOK p) : LatestGetOK p := by
  suffices h : ∀ n, ∀ ts : List Tx, ts.length = n → Within p ts → ∀ key, keyWf key = true →
      get p (viewOf (treeRun p ts)) ts.length key = refGet ts ts.length key by
    intro ts hw key hkey
    exact h ts.length ts rfl hw key hkey
  intro n
  induction n with
  | zero =>
    intro ts hl _ key _
    have hnil : ts = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simpa only [treeRun, List.zipIdx_nil, List.foldl_nil, refGet, List.take_nil,
      List.flatMap_nil, List.length_nil] using get_init p 0 key
  | succ n ih =>
    intro ts hl hw key hkey
    rcases List.eq_nil_or_concat ts with hnil | ⟨ts', tx, hts⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hts
      subst hts
      have hl' : ts'.length = n := by simp at hl; omega
      have hw' := within_snoc_prefix p ts' tx hw
      have hs : tx.sorted = true := (hw.w.1 tx (by simp)).1
      have hlen : (ts' ++ [tx]).length = ts'.length + 1 := by simp
      rw [hlen, htx ts' tx hw key hkey, ih ts' hl' hw' key hkey, refGet_snoc_latest ts' tx hs]

/-- As `SIS.Tree.getOK_of_txGet`, for the runs of `N.Within`. -/
theorem getOK_of_txGet (p : Params) (hinv : InvPreserved p) (htx : TxGetOK p) : GetOK p :=
  getOK_of_latest p hinv (latestGetOK_of_txGet p htx)

/-- As `SIS.Tree.scanOK_of_latest_invariant`, for the runs of `N.Within`. -/
theorem scanOK_of_latest_invariant (p : Params) (hinv : LatestInvOK p)
    (hlatest : LatestScanOK p) : ScanOK p := by
  intro ts hw t ht req limit hreq
  have hlen : (ts.take t).length = t := by simp only [List.length_take, Nat.min_eq_left ht]
  have hwithin := within_take p ts hw t
  have hi := hinv (ts.take t) hwithin
  rw [hlen] at hi
  rw [treeRun_scan_eq_prefix_of_invariant p ts t ht hi req limit]
  have he := hlatest (ts.take t) hwithin req limit hreq
  rw [hlen, refScan_take_eq ts t req limit] at he
  exact he

/-- As `SIS.Tree.scanOK_of_latest`, for the runs of `N.Within`. -/
theorem scanOK_of_latest (p : Params) (hinv : InvPreserved p)
    (hlatest : LatestScanOK p) : ScanOK p :=
  scanOK_of_latest_invariant p (fun ts hw => (hinv ts hw ts.length (Nat.le_refl _)).1) hlatest

/-- As `SIS.Tree.rootContents_eq_refKvs`, for the runs of `N.Within`. -/
theorem rootContents_eq_refKvs (p : Params) (ts : List Tx) (hw : Within p ts)
    (hi : InvOK p (treeRun p ts) ts.length) (hget : LatestGetOK p) :
    rootContents p (treeRun p ts) ts.length = refKvs ts ts.length := by
  have henc := structEncoded_viewOf _ (treeRun_encoded_of_within p ts hw)
  apply eq_of_sorted_mem _ _
    (rootContents_sorted p _ _ (treeRun_highKindsOK p ts) (treeRun_dataEntriesOK p ts) henc hi)
    (refKvs_sorted ts ts.length)
  intro ⟨k, h⟩
  by_cases hk : keyWf k = true
  · rw [← get_mem_rootContents p _ _ (treeRun_highKindsOK p ts) hi k hk h, hget ts hw k hk,
      mem_refKvs]
  · constructor
    · intro hm
      exfalso
      apply hk
      unfold rootContents at hm
      cases hr : rootAt (viewOf (treeRun p ts)) ts.length with
      | none => simp [hr] at hm
      | some r =>
        rw [hr] at hm
        exact treeRun_treeContents_keyWf p ts hw ts.length p.fuel r (k, h) hm
    · intro hm
      exact absurd (refKvs_keyWf p ts hw ts.length k h hm) hk

/-- As `SIS.Tree.latestScanOK_of_latestGet`, for the runs of `N.Within`. -/
theorem latestScanOK_of_latestGet (p : Params) (hinv : LatestInvOK p)
    (hget : LatestGetOK p) : LatestScanOK p := by
  intro ts hw req limit hreq
  have hi := hinv ts hw
  rw [scan_eq_contents p _ ts.length (treeRun_highKindsOK p ts) (treeRun_dataEntriesOK p ts)
    (structEncoded_viewOf _ (treeRun_encoded_of_within p ts hw)) hi req hreq limit,
    rootContents_eq_refKvs p ts hw hi hget]
  simp only [refScan, orient]

/-- As `SIS.Tree.scanOK_of_latestGet`, for the runs of `N.Within`. -/
theorem scanOK_of_latestGet (p : Params) (hinv : InvPreserved p) (hget : LatestGetOK p) :
    ScanOK p :=
  scanOK_of_latest p hinv
    (latestScanOK_of_latestGet p (fun ts hw => (hinv ts hw ts.length (Nat.le_refl _)).1) hget)

/-- As `SIS.Tree.scanOK_of_txGet`, for the runs of `N.Within`. -/
theorem scanOK_of_txGet (p : Params) (hinv : InvPreserved p) (htx : TxGetOK p) : ScanOK p :=
  scanOK_of_latestGet p hinv (latestGetOK_of_txGet p htx)

/-- As `SIS.Tree.txGet_fold`, for the runs of `N.Within`. -/
theorem txGet_fold (p : Params) (ho : OpGetOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done, tx.ops = done ++ todo → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      ∀ key, keyWf key = true →
        runGet p ts w' key =
          todo.foldl (fun v op => if op.key == key then op.value else v) (runGet p ts w key) := by
  intro todo
  induction todo with
  | nil =>
    intro done _ r w _ r' w' hrun key _
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    rfl
  | cons op rest ih =>
    intro done hsplit r w hdone r' w' hrun key hkey
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hstep := ho ts tx hw z top hz htop done op rest hsplit r w hdone a w1 h1 key hkey
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    rw [ih (done ++ [op]) (by rw [hsplit]; simp) _ w1 hdone' r1 w' h2 key hkey, List.foldl_cons,
      hstep]

/-- As `SIS.Tree.txGetOK_of_writer`, for the runs of `N.Within`. -/
theorem txGetOK_of_writer (p : Params) (hi : InitGetOK p) (ho : OpGetOK p)
    (hc : CommitGetOK p) : TxGetOK p := by
  intro ts tx hw key hkey
  obtain ⟨noops, w, hrun⟩ := within_last_ok p ts tx hw
  obtain ⟨z, top, hz, htop, hops⟩ := runOps_ok p _ _ _ _ noops w hrun
  have hs : tx.sorted = true := (hw.w.1 tx (by simp)).1
  rw [hc ts tx hw noops w hrun key hkey]
  have hfold := txGet_fold p ho ts tx hw z top hz htop tx.ops [] (by simp) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure])
    noops w hops key hkey
  rw [hfold, hi ts tx hw z top hz htop key hkey, fold_value_find key tx.ops (Tx.keys_nodup tx hs)]
  rfl

/-- As `SIS.Tree.txGetOK_of_op_commit`, for the runs of `N.Within`. -/
theorem txGetOK_of_op_commit (p : Params) (ho : OpGetOK p) (hc : CommitGetOK p) :
    TxGetOK p :=
  txGetOK_of_writer p (initGetOK p) ho hc

/-- As `SIS.Tree.getOK_of_op_commit`, for the runs of `N.Within`. -/
theorem getOK_of_op_commit (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hc : CommitGetOK p) : GetOK p :=
  getOK_of_txGet p hinv (txGetOK_of_op_commit p ho hc)

/-- As `SIS.Tree.scanOK_of_op_commit`, for the runs of `N.Within`. -/
theorem scanOK_of_op_commit (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hc : CommitGetOK p) : ScanOK p :=
  scanOK_of_txGet p hinv (txGetOK_of_op_commit p ho hc)

/-- As `SIS.Tree.commitGetOK_of_lift`, for the runs of `N.Within`. -/
theorem commitGetOK_of_lift (p : Params) (hl : CommitLiftOK p) : CommitGetOK p := by
  intro ts tx hw noops w hrun key _
  obtain ⟨hK, htaken, htopt⟩ := hl ts tx hw noops w hrun
  have hbase : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.w.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have halloc : AllocatedIds tx.base w := execW_allocatedIds p tx _ _ noops w hrun
  have hdata : MadeData w := execW_madeData p tx _ _ noops w hrun
  obtain ⟨z, top0, hz, htop, hinv⟩ := commitInv_of_runOps p ts tx noops w hrun
  obtain ⟨_, hnf, hnt, hvm, hvn, _⟩ := hinv
  have hroot0 := rootAt_of_writerTop p ts z top0 hz htop
  rw [treeRun_snoc_changes p ts tx noops w hrun] at hK ⊢
  generalize hP : treeRun p ts = P at hK hbase hroot0 ⊢
  generalize hi : ts.length + 1 = i at hK ⊢
  have hroot := treeRun_root p ts
  rw [hP] at hroot
  obtain ⟨ndr, hndr, hlr, hdr⟩ := hroot
  have hbase0 : 0 < tx.base := hbase _ (get?_mem P root ndr hndr)
  -- Key adds only for the writer's own nodes, which the lift reads.
  have noKey : ∀ x, knodeOf p (viewOf (P.apply i (changesOf i w))) x = none →
      w.taken.contains x = false → ∀ q ∈ w.nodes, q.1 ≠ x := by
    intro x hx ht q hq hqx
    rw [hK x] at hx
    simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte] at hx
    cases hl : w.nodes.lookup x with
    | none =>
      have := List.lookup_eq_none_iff.mp hl q hq
      simp [hqx] at this
    | some n => rw [hl] at hx; cases hx
  have madeGe : ∀ m ∈ w.made, tx.base ≤ m.id := fun m hm => (halloc.2.2 m hm).1
  -- The values.
  have hV : valueOf (viewOf (P.apply i (changesOf i w))) = wValue (viewOf P) w := by
    funext y
    by_cases hty : w.taken.contains y = true
    · have hPy := get?_none_of_ge P tx.base y hbase (htaken y (by simpa using hty))
      have hNy := newNodeOf_changesOf_none i w y (fun m _ hid => by rw [← hid] at hty ⊢; exact hty)
      have hty2 : y ∈ w.taken := by simpa using hty
      simp [valueOf, viewOf, get?_apply, hPy, hNy, wValue, hty2]
    · have hty' : w.taken.contains y = false := by simpa using hty
      cases hv : w.vals.lookup y with
      | some h =>
        obtain ⟨l1, l2, hvl, _⟩ := List.lookup_eq_some_iff.mp hv
        have hmem : (y, h) ∈ w.vals := by rw [hvl]; simp
        have hmade := hvm (y, h) hmem
        have hge : tx.base ≤ y := madeGe _ hmade
        have hPy := get?_none_of_ge P tx.base y hbase hge
        have hNy := newNodeOf_changesOf_made tx.base i w halloc _ hmade hty'
        have hk : knodeOf p (viewOf (P.apply i (changesOf i w))) y = none := by
          simp [knodeOf, viewOf, get?_apply, hPy, hNy]
        have hadds : ∀ e ∈ addsFor (changesOf i w) i y, e.val = .data h := by
          intro e he
          obtain ⟨_, hm⟩ := mem_addsFor.mp he
          rcases mem_changesOf_adds i w y e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', hv'⟩ |
              ⟨hnt', hr⟩
          · exact absurd hqy (noKey y hk hty' q hq)
          · have := nodup_map_inj (·.1) w.vals hvn _ _ hh' hmem rfl
            cases this
            exact hv'
          · rcases hr with ⟨hyr, _⟩ | ⟨hyt, _⟩
            · rw [hyr] at hge; simp only [root] at hge; omega
            · obtain ⟨m, hm, hmid, hmd, _⟩ := hnt hnt'
              have := nodup_map_inj (·.id) w.made halloc.2.1 m _ hm hmade (by simp [hmid, hyt])
              rw [this] at hmd
              cases hmd
        have hex : (⟨i, .data h⟩ : Entry BVal) ∈ addsFor (changesOf i w) i y :=
          mem_addsFor.mpr ⟨rfl, val_mem_changesOf_adds i w y h hmem⟩
        simp only [valueOf, viewOf, get?_apply, hPy, hNy, Option.none_or, Option.map_some,
          ↓reduceIte, List.nil_append, wValue, hty', hv, Bool.false_eq_true]
        apply findSome_of_all
        · exact ⟨_, hex, rfl⟩
        · intro e he
          right
          rw [hadds e he]
      | none =>
        cases hPy : P.get? y with
        | some nd =>
          simp only [valueOf, viewOf, get?_apply_of_get? hPy, wValue, hty', hv, hPy,
            Bool.false_eq_true, ↓reduceIte]
          cases hd : nd.isData with
          | false => rfl
          | true =>
            obtain ⟨e, he, h0, hed⟩ := treeRun_dataEntriesOK p ts y nd (by rw [hP]; exact hPy) hd
            simp only [↓reduceIte, List.findSome?_append]
            have hs : (nd.hist.findSome? (fun e => match e.val with
                | .data h => some h
                | _ => none)).isSome = true := by
              apply List.findSome?_isSome_iff.mpr
              exact ⟨e, he, by simp [hed]⟩
            cases hf : nd.hist.findSome? (fun e => match e.val with
                | .data h => some h
                | _ => none) with
            | none => rw [hf] at hs; cases hs
            | some h1 => rfl
        | none =>
          cases hNy : newNodeOf (changesOf i w) y with
          | none => simp [valueOf, viewOf, get?_apply, hPy, hNy, wValue, hty', hv]
          | some nd =>
            obtain ⟨m, hm, hid, _, hnd⟩ := newNodeOf_changesOf_some i w y nd hNy
            cases hmd : m.isData with
            | false =>
              simp [valueOf, viewOf, get?_apply, hPy, hNy, hnd, hmd, wValue, hty', hv]
            | true =>
              obtain ⟨h, hh⟩ := hdata m hm hmd
              rw [hid] at hh
              have := List.lookup_eq_none_iff.mp hv _ hh
              simp at this
  -- The super root.
  have hR : rootAt (viewOf (P.apply i (changesOf i w))) i = some w.top.rootKey := by
    have hrt : w.taken.contains root = false := by
      cases h : w.taken.contains root with
      | false => rfl
      | true =>
        have := htaken root (by simpa using h)
        simp only [root] at this
        omega
    have hkr : knodeOf p (viewOf (P.apply i (changesOf i w))) root = none := by
      have := rootLevel_gt p
      simp [knodeOf, viewOf, get?_apply_of_get? hndr, hlr, hdr, this]
    have noKeyRoot := noKey root hkr hrt
    have hradds : ∀ e ∈ addsFor (changesOf i w) i root,
        w.newTop = true ∧ e = ⟨i, .top w.top.id⟩ := by
      intro e he
      obtain ⟨het, hm⟩ := mem_addsFor.mp he
      rcases mem_changesOf_adds i w root e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
          ⟨hnt', hr⟩
      · exact absurd hqy (noKeyRoot q hq)
      · have := madeGe _ (hvm _ hh')
        simp only [root] at this
        omega
      · rcases hr with ⟨_, hval⟩ | ⟨hyt, _⟩
        · refine ⟨hnt', ?_⟩
          cases e
          simp only at het hval
          rw [het, hval]
        · obtain ⟨m, hm, hmid, _, _⟩ := hnt hnt'
          have := madeGe m hm
          rw [hmid, ← hyt] at this
          simp only [root] at this
          omega
    cases hnew : w.newTop with
    | true =>
      obtain ⟨m, hm, hmid, hmd, hml⟩ := hnt hnew
      have htt := htopt hnew
      have hge : tx.base ≤ w.top.id := hmid ▸ madeGe m hm
      have hPt := get?_none_of_ge P tx.base _ hbase hge
      have hNt := newNodeOf_changesOf_made tx.base i w halloc m hm (by rw [hmid]; exact htt)
      rw [hmid] at hNt
      have hkt : knodeOf p (viewOf (P.apply i (changesOf i w))) w.top.id = none := by
        have hml' : p.keyMax < m.level := hml
        simp [knodeOf, viewOf, get?_apply, hPt, hNt, hml']
      have noKeyTop := noKey _ hkt htt
      have hmems := top_mem_changesOf_adds i w hnew
      unfold rootAt topAt rootKeyOf viewOf
      rw [get?_apply_of_get? hndr]
      simp only
      rw [upTo_append]
      have hA : (addsFor (changesOf i w) i root).upTo i = addsFor (changesOf i w) i root :=
        List.filter_eq_self.mpr (fun e he => by
          rw [(mem_addsFor.mp he).1]; simp)
      rw [hA, getLast_append_const (ndr.hist.upTo i) (addsFor (changesOf i w) i root)
        ⟨i, .top w.top.id⟩
        (List.ne_nil_of_mem (a := (⟨i, .top w.top.id⟩ : Entry BVal)) (mem_addsFor.mpr ⟨rfl, hmems.1⟩))
        (fun e he => (hradds e he).2)]
      simp only [Option.bind_some]
      rw [get?_apply, hPt, hNt]
      simp only [Option.none_or, Option.map_some, Option.bind_some, List.nil_append]
      apply findSome_of_all
      · exact ⟨⟨i, .rootKey w.top.rootKey⟩, mem_addsFor.mpr ⟨rfl, hmems.2⟩, rfl⟩
      · intro e he
        obtain ⟨_, hm'⟩ := mem_addsFor.mp he
        rcases mem_changesOf_adds i w w.top.id e.val hm' with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
            ⟨_, hr⟩
        · exact absurd hqy (noKeyTop q hq)
        · have := nodup_map_inj (·.id) w.made halloc.2.1 m _ hm (hvm _ hh') (by simp [hmid])
          rw [this] at hmd
          cases hmd
        · rcases hr with ⟨hyr, _⟩ | ⟨_, hv | ⟨j, z', hv⟩⟩
          · simp only [root] at hyr; omega
          · right; rw [hv]
          · left; rw [hv]
    | false =>
      have htw := hnf hnew
      have hA : addsFor (changesOf i w) i root = [] :=
        List.eq_nil_iff_forall_not_mem.mpr (fun e he => by
          have := (hradds e he).1
          rw [hnew] at this
          cases this)
      have hshift := topAt_succ_of_timesLE P ts.length (by rw [← hP]; exact treeRun_timesLE p ts)
      rw [htw]
      unfold rootAt at hroot0 ⊢
      have htopEq : topAt (viewOf (P.apply i (changesOf i w))) i = topAt (viewOf P) ts.length := by
        rw [← hshift, hi]
        unfold topAt viewOf
        rw [get?_apply_of_get? hndr, hA, List.append_nil, hndr]
      rw [htopEq]
      cases hzt : topAt (viewOf P) ts.length with
      | none => rw [hzt] at hroot0; cases hroot0
      | some z' =>
        rw [hzt] at hroot0
        simp only [Option.bind_some] at hroot0 ⊢
        exact rootKeyOf_apply_some P i (changesOf i w) z' _ hroot0
  -- The get.
  unfold get runGet wGet
  rw [hR, hP]
  simp only [Option.bind_some]
  rw [getFrom_eq_getFromR, hV, show knodeOf p (viewOf (P.apply i (changesOf i w))) =
    wNode p (viewOf P) w from funext hK, hi]

/-- As `SIS.Tree.getOK_of_op_lift`, for the runs of `N.Within`. -/
theorem getOK_of_op_lift (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hl : CommitLiftOK p) : GetOK p :=
  getOK_of_op_commit p hinv ho (commitGetOK_of_lift p hl)

/-- As `SIS.Tree.scanOK_of_op_lift`, for the runs of `N.Within`. -/
theorem scanOK_of_op_lift (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hl : CommitLiftOK p) : ScanOK p :=
  scanOK_of_op_commit p hinv ho (commitGetOK_of_lift p hl)

/-- As `SIS.Tree.commitLiftOK_of_overlay`, for the runs of `N.Within`. -/
theorem commitLiftOK_of_overlay (p : Params) (ho : OverlayLiftOK p) : CommitLiftOK p := by
  intro ts tx hw noops w hrun
  obtain ⟨hov, htaken, htopt⟩ := ho ts tx hw noops w hrun
  refine ⟨?_, htaken, htopt⟩
  have hbase : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.w.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have halloc : AllocatedIds tx.base w := execW_allocatedIds p tx _ _ noops w hrun
  have hmn := madeNodes_of_runOps p ts tx noops w hrun
  obtain ⟨z, top0, _, _, hinv⟩ := commitInv_of_runOps p ts tx noops w hrun
  obtain ⟨_, _, hnt, hvm, _, _⟩ := hinv
  have hroot := treeRun_root p ts
  intro x
  have hov' := hov x
  rw [treeRun_snoc_changes p ts tx noops w hrun] at hov' ⊢
  generalize hP : treeRun p ts = P at hov' hbase hroot ⊢
  generalize hi : ts.length + 1 = i at hov' ⊢
  obtain ⟨ndr, hndr, hlr, hdr⟩ := hroot
  have madeGe : ∀ m ∈ w.made, tx.base ≤ m.id := fun m hm => (halloc.2.2 m hm).1
  by_cases hty : w.taken.contains x = true
  · have hge := htaken x (by simpa using hty)
    have hPx := get?_none_of_ge P tx.base x hbase hge
    have hNx := newNodeOf_changesOf_none i w x (fun m _ hid => by rw [← hid] at hty ⊢; exact hty)
    have hty2 : x ∈ w.taken := by simpa using hty
    simp [knodeOf, viewOf, get?_apply, hPx, hNx, wNode, hty2]
  · have hty' : w.taken.contains x = false := by simpa using hty
    have hty3 : x ∉ w.taken := by simpa using hty
    cases hl : w.nodes.lookup x with
    | some n =>
      rw [hov' n hl hty']
      simp [wNode, hty3, hl]
    | none =>
      have hwn : wNode p (viewOf P) w x = knodeOf p (viewOf P) x := by
        simp [wNode, hty3, hl]
      rw [hwn]
      have hnokey : ∀ q ∈ w.nodes, q.1 ≠ x := by
        intro q hq hqx
        have := List.lookup_eq_none_iff.mp hl q hq
        simp [hqx] at this
      cases hPx : P.get? x with
      | some nd =>
        have hlt : x < tx.base := hbase _ (get?_mem P x nd hPx)
        by_cases hxr : x = root
        · subst hxr
          rw [hndr] at hPx
          cases hPx
          have := rootLevel_gt p
          simp [knodeOf, viewOf, get?_apply_of_get? hndr, hndr, hlr, hdr, this]
        · have hA : addsFor (changesOf i w) i x = [] :=
            List.eq_nil_iff_forall_not_mem.mpr (fun e he => by
              obtain ⟨_, hm⟩ := mem_addsFor.mp he
              rcases mem_changesOf_adds i w x e.val hm with ⟨q, hq, _, hqy⟩ | ⟨h', hh', _⟩ |
                  ⟨hnt', hr⟩
              · exact hnokey q hq hqy
              · have := madeGe _ (hvm _ hh')
                simp only at this
                omega
              · rcases hr with ⟨hxr', _⟩ | ⟨hxt, _⟩
                · exact hxr hxr'
                · obtain ⟨m, hm, hmid, _, _⟩ := hnt hnt'
                  have := madeGe m hm
                  rw [hmid, ← hxt] at this
                  omega)
          simp [knodeOf, viewOf, get?_apply_of_get? hPx, hPx, hA]
      | none =>
        have hk0 : knodeOf p (viewOf P) x = none := by simp [knodeOf, viewOf, hPx]
        rw [hk0]
        cases hNx : newNodeOf (changesOf i w) x with
        | none => simp [knodeOf, viewOf, get?_apply, hPx, hNx]
        | some nd =>
          obtain ⟨m, hm, hid, _, hnd⟩ := newNodeOf_changesOf_some i w x nd hNx
          subst hnd
          cases hmd : m.isData with
          | true => simp [knodeOf, viewOf, get?_apply, hPx, hNx, hmd]
          | false =>
            rcases hmn m hm hmd with hs | hlv
            · rw [hid, hl] at hs
              cases hs
            · have hlv' : p.keyMax < m.level := hlv
              simp [knodeOf, viewOf, get?_apply, hPx, hNx, hmd, hlv']

/-- As `SIS.Tree.getOK_of_op_overlay`, for the runs of `N.Within`. -/
theorem getOK_of_op_overlay (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hl : OverlayLiftOK p) : GetOK p :=
  getOK_of_op_lift p hinv ho (commitLiftOK_of_overlay p hl)

/-- As `SIS.Tree.scanOK_of_op_overlay`, for the runs of `N.Within`. -/
theorem scanOK_of_op_overlay (p : Params) (hinv : InvPreserved p) (ho : OpGetOK p)
    (hl : OverlayLiftOK p) : ScanOK p :=
  scanOK_of_op_lift p hinv ho (commitLiftOK_of_overlay p hl)

/-- As `SIS.Tree.invPreserved_of_latest`, for the runs of `N.Within`. -/
theorem invPreserved_of_latest (p : Params)
    (hA : ∀ ts, Within p ts → KeyNodesOK p (treeRun p ts))
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hL : LatestInvOK p) : InvPreserved p := by
  intro ts hw t ht
  refine ⟨?_, hP ts hw⟩
  apply invOK_treeRun_of_take p ts t ht
  · intro k _ _
    exact hA _ (within_take p ts hw k)
  · have hlen : (ts.take t).length = t := by
      simp only [List.length_take, Nat.min_eq_left ht]
    have h := hL (ts.take t) (within_take p ts hw t)
    rwa [hlen] at h

/-- As `SIS.Tree.overlayLiftOKUnder_mono`, for the runs of `N.Within`. -/
theorem overlayLiftOKUnder_mono (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ P t, R P t → R' P t) (hl : OverlayLiftOKUnder p R') : OverlayLiftOKUnder p R :=
  fun ts tx hw hr => hl ts tx hw (h _ _ hr)

/-- As `SIS.Tree.opGetOK_of_under`, for the runs of `N.Within`. -/
theorem opGetOK_of_under (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (ho : OpGetOKUnder p R) :
    OpGetOK p :=
  fun ts tx hw => ho ts tx hw (hR ts (within_snoc_prefix p ts tx hw))

/-- As `SIS.Tree.overlayLiftOK_of_under`, for the runs of `N.Within`. -/
theorem overlayLiftOK_of_under (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (hl : OverlayLiftOKUnder p R) :
    OverlayLiftOK p :=
  fun ts tx hw => hl ts tx hw (hR ts (within_snoc_prefix p ts tx hw))

/-- As `SIS.Tree.getOK_of_under`, for the runs of `N.Within`. -/
theorem getOK_of_under (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (ho : OpGetOKUnder p R)
    (hl : OverlayLiftOKUnder p R) : GetOK p :=
  getOK_of_op_overlay p hinv (opGetOK_of_under p R hR ho)
    (overlayLiftOK_of_under p R hR hl)

/-- As `SIS.Tree.scanOK_of_under`, for the runs of `N.Within`. -/
theorem scanOK_of_under (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length) (ho : OpGetOKUnder p R)
    (hl : OverlayLiftOKUnder p R) : ScanOK p :=
  scanOK_of_op_overlay p hinv (opGetOK_of_under p R hR ho)
    (overlayLiftOK_of_under p R hR hl)

/-- As `SIS.Tree.writerTreeOK_fold`, for the runs of `N.Within`. -/
theorem writerTreeOK_fold (p : Params) (ho : OpTreeOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ todo done extra, tx.ops = done ++ todo ++ extra → ∀ r w,
      (done.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
      ∀ r' w', (todo.mapM putKv) (ctxOf p ts) w = .ok (r', w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' := by
  intro todo
  induction todo with
  | nil =>
    intro done _ _ r w _ hT r' w' hrun
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hrun
    rw [← hrun.2]
    exact hT
  | cons op rest ih =>
    intro done extra hsplit r w hdone hT r' w' hrun
    obtain ⟨a, w1, r1, h1, h2⟩ := mapM_cons_run op rest _ w w' r' hrun
    have hT1 := ho ts tx hw z top hz htop done op (rest ++ extra) (by rw [hsplit]; simp) r w hdone
      hT a w1 h1
    have hdone' := mapM_snoc_run done op _ _ w w1 r a hdone h1
    exact ih (done ++ [op]) extra (by rw [hsplit]; simp) _ w1 hdone' hT1 r1 w' h2

/-- As `SIS.Tree.writerTreeOK_reached`, for the runs of `N.Within`. -/
theorem writerTreeOK_reached (p : Params) (ho : OpTreeOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hT : TreeAt p (treeRun p ts) ts.length) (pre : List Tree.Op) (post : List Tree.Op)
    (hsplit : tx.ops = pre ++ post) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w :=
  writerTreeOK_fold p ho ts tx hw z top hz htop pre [] post (by simp [hsplit]) [] (wInit tx top)
    (by simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure])
    (writerTreeOK_init p ts tx z top hz htop hT) r w hpre

/-- As `SIS.Tree.invPreserved_of_parts`, for the runs of `N.Within`. -/
theorem invPreserved_of_parts (p : Params) (hL : LatestInvOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hS : ∀ ts, Within p ts → SizeOK p (treeRun p ts))
    (hN : ∀ ts, Within p ts → KeyNonempty p (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts)) : InvPreserved p := by
  apply invPreserved_of_latest p ?_ hP hL
  intro ts hw x nd hx hd hl
  have hH := treeRun_keyHistOK p ts hw
    (fun k _ => hP _ (within_take p ts hw k)) (fun k _ => hN _ (within_take p ts hw k))
  obtain ⟨hwf, hrt⟩ := hH x nd hx hd hl
  have hk := keyNodeAt_of p _ x nd hx hd hl
  refine ⟨hS ts hw x _ hk, hwf, hrt, ?_, hD ts hw x _ hk⟩
  intro c y hm
  obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist c y hm
  exact hP ts hw _ (mem_of_get? hx) e he y (by rw [hv]; simp [bptrs])

/-- As `SIS.Tree.runLinksOK_of_pointers`, for the runs of `N.Within`. -/
theorem runLinksOK_of_pointers (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    RunLinksOK p (treeRun p ts) ts.length := by
  have hk : ∀ n, n ≤ ts.length → RunLinksOK p (treeRun p (ts.take n)) n := by
    intro n
    induction n with
    | zero => intro _; exact runLinksOK_init p
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hr : RunLinksOK p (treeRun p (ts.take n)) (ts.take n).length := ih (by omega)
      obtain ⟨h1, h2⟩ := keyNonempty_step p hM (ts.take n) ts[n] hwn hr
      rw [htake]
      exact ⟨hP _ hwn, h1, h2⟩
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- As `SIS.Tree.treeRun_sizeOK_of_pointers`, for the runs of `N.Within`. -/
theorem treeRun_sizeOK_of_pointers (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    SizeOK p (treeRun p ts) := by
  have hM := mergeParamsOK_M p hp
  have hk : ∀ n, n ≤ ts.length → SizeOK p (treeRun p (ts.take n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact sizeOK_init p (by omega)
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      obtain ⟨hP', hH, hN⟩ := runLinksOK_of_pointers p (by omega) hP (ts.take n)
        (within_take p ts hw n)
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.w.2 n hlt).1
      have htimes : StructTimesLE (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) :=
        treeRun_timesLE p (ts.take n)
      have hl := viewLinksOK_of p _ _ ts[n].base hfresh htimes hP' hN
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      rw [htake, treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
      exact sizeOK_step p _ ((ts.take n).length + 1) ts[n] bs w hp (by omega) hfresh htimes
        (treeRun_root_level p _) hH hl (ih (by omega)) hrun
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- As `SIS.Tree.invPreserved_of_latest_pointers`, for the runs of `N.Within`. -/
theorem invPreserved_of_latest_pointers (p : Params) (hp : MergeParamsOK p) (hL : LatestInvOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts)) : InvPreserved p := by
  have hM := mergeParamsOK_M p hp
  exact invPreserved_of_parts p hL hP
    (fun ts hw => treeRun_sizeOK_of_pointers p hp hP ts hw)
    (fun ts hw => (runLinksOK_of_pointers p (by omega) hP ts hw).2.2) hD

/-- As `SIS.Tree.putInv_reached`, for the runs of `N.Within`. -/
theorem putInv_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) (ho : OpTreeOK p) (hP : OpPutInvOK p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hT : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact putInv_init p ts tx hw (hR _ _ hr) hT hI z top hz htop
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          have hI1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 := ho ts tx hw z top hz htop pre' op post hsplit' r1 w1 h1
            (writerTreeOK_reached p ho ts tx hw z top hz htop hT pre' (op :: post) hsplit' r1 w1 h1)
            a w2 h2
          have := hP ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 a w2 h2 hT2
          rw [← h.2]
          exact this

/-- As `SIS.Tree.opGetOKUnder_of_putInv`, for the runs of `N.Within`. -/
theorem opGetOKUnder_of_putInv (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hg : OpGetPutInvOK p R) : OpGetOKUnder p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre
  exact hg ts tx hw hr z top hz htop pre op post hsplit r w hpre
    (putInv_reached p R hRL ho hP ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop pre
      (op :: post) hsplit r w hpre)

/-- As `SIS.Tree.getOK_of_putInv`, for the runs of `N.Within`. -/
theorem getOK_of_putInv (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hg : OpGetPutInvOK p R)
    (hl : OverlayLiftOKUnder p R) : GetOK p :=
  getOK_of_under p hinv R hR (opGetOKUnder_of_putInv p R hRL hRT hRI ho hP hg) hl

/-- As `SIS.Tree.scanOK_of_putInv`, for the runs of `N.Within`. -/
theorem scanOK_of_putInv (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hg : OpGetPutInvOK p R)
    (hl : OverlayLiftOKUnder p R) : ScanOK p :=
  scanOK_of_under p hinv R hR (opGetOKUnder_of_putInv p R hRL hRT hRI ho hP hg) hl

/-- As `SIS.Tree.rangeOrder_reached`, for the runs of `N.Within`. -/
theorem rangeOrder_reached (p : Params) (R : Struct BVal → Time → Prop) (hO : OpRangeOK p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top)
    (hPI : ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hTr : ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact rangeOrder_init p ts tx hI z top hz htop
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      have h0 := h
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          have hR1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hP1 := hPI pre' (op :: post) hsplit' r1 w1 h1
          have hT2 := hTr (pre' ++ [op]) post (by rw [hsplit]) r w h0
          rw [← h.2] at hT2 ⊢
          exact hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hP1 hR1 a w2 h2 hT2

/-- As `SIS.Tree.treeRun_kindsAllOK`, for the runs of `N.Within`. -/
theorem treeRun_kindsAllOK (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    KindsAllOK p (treeRun p ts) := by
  have hk : ∀ n, n ≤ ts.length → KindsAllOK p (treeRun p (ts.take n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact kindsAllOK_init p
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hPn := hP (ts.take n) (within_take p ts hw n)
      obtain ⟨hP', hH, hN⟩ := runLinksOK_of_pointers p (by omega) hP (ts.take n)
        (within_take p ts hw n)
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.w.2 n hlt).1
      have htimes : StructTimesLE (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) :=
        treeRun_timesLE p (ts.take n)
      have htimes' : StructTimesLE (treeRun p (ts.take n)) (ts.take n).length :=
        treeRun_timesLE p (ts.take n)
      have hl := viewLinksOK_of p _ _ ts[n].base hfresh htimes hP' hN
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      have he : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1)) =
            .ok (bs, w) := hrun
      have he' : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := hrun
      have hvg := viewGood_of p (treeRun p (ts.take n)) ((ts.take n).length + 1) ts[n].base
        (by omega) hfresh htimes hl
      have hbook := execW_book p ts[n] ((ts.take n).length + 1) _ bs w
        (viewIdsBelow_view p (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) ts[n].base
          hfresh) he
      have htaken := execW_takenAbove p ts[n] ((ts.take n).length + 1) _ bs w hvg he
      have hKW := execW_kinds (kindOracleOf p (treeRun p (ts.take n))) p ts[n]
        ((ts.take n).length + 1) _ bs w hM (hw.w.1 ts[n] (List.getElem_mem hlt)).2
        (appendFrameOK ts[n].base)
        (viewIdsBelow_view p (treeRun p (ts.take n)) (ts.take n).length ts[n].base hfresh)
        (viewKinds_of p (treeRun p (ts.take n)) (ts.take n).length ts[n].base hfresh htimes' hPn
          (ih (by omega))) he'
      rw [htake, treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
      exact kindsAllOK_step p _ ((ts.take n).length + 1) ts[n] bs w (by omega) hfresh htimes
        (treeRun_root_level p _) hH hl hPn he hbook htaken (ih (by omega)) hKW
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- As `SIS.Tree.opGetPutInvOK_of_cases`, for the runs of `N.Within`. -/
theorem opGetPutInvOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hO : OpRangeOK p R) (hfit : TxSegFitsOK p R)
    (c1 : OpGetCaseOK p R PutLeafRoomCase) (c2 : OpGetCaseOK p R PutLeafFullCase)
    (c3 : OpGetCaseOK p R PutNewSegCase) (c4 : OpGetCaseOK p R DelMergeCase)
    (c5 : OpGetCaseOK p R DelNoLeafCase) (c6 : OpGetCaseOK p R DelNoopCase)
    (c7 : OpGetCaseOK p R DelEmptyCase) (c8 : OpGetCaseOK p R DelRoomCase)
    (c9 : OpGetCaseOK p R DelFullCase) :
    OpGetPutInvOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hPI
  have hPIall := putInv_reached p R hRL ho hP ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop
  have hRO := rangeOrder_reached p R hO ts tx hw hr (hRI _ _ hr) z top hz htop hPIall
    (fun pre' post' hs r' w' h => writerTreeOK_reached p ho ts tx hw z top hz htop (hRT _ _ hr) pre' post'
      hs r' w' h) pre (op :: post) hsplit r w hpre
  have hcase : ∀ P : Ctx → View BVal → W → Op → Prop, OpGetCaseOK p R P →
      P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => ∀ key, keyWf key = true →
        runGet p ts w' key = if op.key == key then op.value else runGet p ts w key) := by
    intro P hc hPc a w' hrun
    exact hc ts tx hw hr z top hz htop pre op post hsplit r w hpre hPI hRO hPc a w' hrun
      (hfit ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hsplit]; simp) (r ++ [a]) w'
        (mapM_snoc_run pre op _ _ w w' r a hpre hrun))
  rcases opCase_cover (ctxOf p ts) (viewOf (treeRun p ts)) w op with
    h | h | h | h | h | h | h | h | h
  · exact hcase _ c1 h
  · exact hcase _ c2 h
  · exact hcase _ c3 h
  · exact hcase _ c4 h
  · exact hcase _ c5 h
  · exact hcase _ c6 h
  · exact hcase _ c7 h
  · exact hcase _ c8 h
  · exact hcase _ c9 h

/-- As `SIS.Tree.getOK_scanOK_of_open`, for the runs of `N.Within`. -/
theorem getOK_scanOK_of_open (p : Params) (hinv : InvPreserved p) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (ho : OpTreeOK p) (hP : OpPutInvOK p R) (hO : OpRangeOK p R) (hfit : TxSegFitsOK p R)
    (hl : OverlayLiftOKUnder p R)
    (c1 : OpGetCaseOK p R PutLeafRoomCase) (c2 : OpGetCaseOK p R PutLeafFullCase)
    (c3 : OpGetCaseOK p R PutNewSegCase) (c4 : OpGetCaseOK p R DelMergeCase)
    (c5 : OpGetCaseOK p R DelNoLeafCase) (c6 : OpGetCaseOK p R DelNoopCase)
    (c7 : OpGetCaseOK p R DelEmptyCase) (c8 : OpGetCaseOK p R DelRoomCase)
    (c9 : OpGetCaseOK p R DelFullCase) :
    GetOK p ∧ ScanOK p := by
  have hg := opGetPutInvOK_of_cases p R hRL hRT hRI ho hP hO hfit c1 c2 c3 c4 c5 c6 c7 c8 c9
  exact ⟨getOK_of_putInv p hinv R hR hRL hRT hRI ho hP hg hl,
    scanOK_of_putInv p hinv R hR hRL hRT hRI ho hP hg hl⟩

/-- As `SIS.Tree.getOK_scanOK_of_open_runOK`, for the runs of `N.Within`. -/
theorem getOK_scanOK_of_open_runOK (p : Params) (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpTreeOK p) (hP : OpPutInvOK p (RunOK p)) (hO : OpRangeOK p (RunOK p))
    (hfit : TxSegFitsOK p (RunOK p))
    (c1 : OpGetCaseOK p (RunOK p) PutLeafRoomCase) (c2 : OpGetCaseOK p (RunOK p) PutLeafFullCase)
    (c3 : OpGetCaseOK p (RunOK p) PutNewSegCase) (c4 : OpGetCaseOK p (RunOK p) DelMergeCase)
    (c5 : OpGetCaseOK p (RunOK p) DelNoLeafCase) (c6 : OpGetCaseOK p (RunOK p) DelNoopCase)
    (c7 : OpGetCaseOK p (RunOK p) DelEmptyCase) (c8 : OpGetCaseOK p (RunOK p) DelRoomCase)
    (c9 : OpGetCaseOK p (RunOK p) DelFullCase) :
    GetOK p ∧ ScanOK p :=
  getOK_scanOK_of_open p hinv (RunOK p)
    (fun ts hw => ⟨hlinks ts hw, htree ts hw, (hinv ts hw ts.length (Nat.le_refl _)).1⟩)
    (fun _ _ h => h.1) (fun _ _ h => h.2.1) (fun _ _ h => h.2.2) ho hP hO hfit
    (overlayLiftOKUnder_mono p (RunOK p) _ (fun _ _ h => h.1) (overlayLiftOKUnder_links p))
    c1 c2 c3 c4 c5 c6 c7 c8 c9

/-- As `SIS.Tree.getOK_scanOK_of_open_cases`, for the runs of `N.Within`. -/
theorem getOK_scanOK_of_open_cases (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpTreeOK p) (hP : OpPutInvOK p (RunOK p)) (hO : OpRangeOK p (RunOK p))
    (hfit : TxSegFitsOK p (RunOK p))
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) (c7 : OpGetCaseOK p (RunOK p) DelEmptyCase)
    (c9 : OpGetCaseOK p (RunOK p) DelFullCase) :
    GetOK p ∧ ScanOK p :=
  getOK_scanOK_of_open_runOK p hinv hlinks htree ho hP hO hfit
    (opGetCaseOK_putLeafRoom p _) (opGetCaseOK_putLeafFull p _ (fun _ _ h => h.1) hsa)
    (opGetCaseOK_putNewSeg p _ (fun _ _ h => h.1) hM hsa) c4 (opGetCaseOK_delNoLeaf p _)
    (opGetCaseOK_delNoop p _) c7 (opGetCaseOK_delRoom p _) c9

/-- As `SIS.Tree.getOK_scanOK_of_open_merges`, for the runs of `N.Within`. -/
theorem getOK_scanOK_of_open_merges (p : Params) (hp : MergeParamsOK p) (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpTreeOK p) (hP : OpPutInvOK p (RunOK p)) (hO : OpRangeOK p (RunOK p))
    (hfit : TxSegFitsOK p (RunOK p)) (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hm : p.merges = true := by
    unfold MergeParamsOK at hp; unfold Params.merges; simp only [decide_eq_true_eq]; omega
  unfold MergeParamsOK at hp
  exact getOK_scanOK_of_open_cases p (by omega) (by omega) hinv hlinks htree ho hP hO hfit c4
    (opGetCaseOK_delEmpty_merges p _ hm) (opGetCaseOK_delFull_merges p _ hm)

/-- As `SIS.Tree.opCaseOK_of_cases`, for the runs of `N.Within`. -/
theorem opCaseOK_of_cases (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop)
    (c1 : OpCaseOK p R Q PutLeafRoomCase) (c2 : OpCaseOK p R Q PutLeafFullCase)
    (c3 : OpCaseOK p R Q PutNewSegCase) (c4 : OpCaseOK p R Q DelMergeCase)
    (c5 : OpCaseOK p R Q DelNoLeafCase) (c6 : OpCaseOK p R Q DelNoopCase)
    (c7 : OpCaseOK p R Q DelEmptyCase) (c8 : OpCaseOK p R Q DelRoomCase)
    (c9 : OpCaseOK p R Q DelFullCase) :
    OpCaseOK p R Q AnyOp := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO _
  have hcase : ∀ P : Ctx → View BVal → W → Op → Prop, OpCaseOK p R Q P →
      P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => Q ts op w w') :=
    fun P hc hPc => hc ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO hPc
  rcases opCase_cover (ctxOf p ts) (viewOf (treeRun p ts)) w op with
    h | h | h | h | h | h | h | h | h
  · exact hcase _ c1 h
  · exact hcase _ c2 h
  · exact hcase _ c3 h
  · exact hcase _ c4 h
  · exact hcase _ c5 h
  · exact hcase _ c6 h
  · exact hcase _ c7 h
  · exact hcase _ c8 h
  · exact hcase _ c9 h

/-- As `SIS.Tree.opCaseOK_of_cases_merges`, for the runs of `N.Within`. -/
theorem opCaseOK_of_cases_merges (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop) (hm : p.merges = true)
    (c1 : OpCaseOK p R Q PutLeafRoomCase) (c2 : OpCaseOK p R Q PutLeafFullCase)
    (c3 : OpCaseOK p R Q PutNewSegCase) (c4 : OpCaseOK p R Q DelMergeCase) :
    OpCaseOK p R Q AnyOp :=
  opCaseOK_of_cases p R Q c1 c2 c3 c4 (opCaseOK_void p R Q _ hm delNoLeafCase_merges)
    (opCaseOK_void p R Q _ hm delNoopCase_merges) (opCaseOK_void p R Q _ hm delEmptyCase_merges)
    (opCaseOK_void p R Q _ hm delRoomCase_merges) (opCaseOK_void p R Q _ hm delFullCase_merges)

/-- As `SIS.Tree.joint_reached`, for the runs of `N.Within`. -/
theorem joint_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact ⟨putInv_init p ts tx hw (hRL _ _ hr) hTA hI z top hz htop,
      rangeOrder_init p ts tx hI z top hz htop⟩
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          obtain ⟨hI1, hR1⟩ := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
            hT ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2 h2
          have hI2 := hP ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
            h2 hT2
          have hR2 := hO ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2
            h2 hT2
          rw [← h.2]
          exact ⟨hI2, hR2⟩

/-- As `SIS.Tree.opRangeOK_of_any`, for the runs of `N.Within`. -/
theorem opRangeOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpRangeOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO
  exact hO ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-- As `SIS.Tree.opPutInvOK_of_any`, for the runs of `N.Within`. -/
theorem opPutInvOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpPutInvOK p R := by
  intro ts tx hw hr z top hz htop pre op post hsplit r w hpre hI
  have hRO := (joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top hz htop
    pre (op :: post) hsplit r w hpre).2
  exact hP ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-- As `SIS.Tree.opTreeOK_of_any`, for the runs of `N.Within`. -/
theorem opTreeOK_of_any (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ ts, Within p ts → R (treeRun p ts) ts.length)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) : OpTreeOK p := by
  intro ts tx hw z top hz htop pre op post hsplit r w hpre _
  have hr := hR ts (within_snoc_prefix p ts tx hw)
  obtain ⟨hI, hRO⟩ := joint_reached p R hRL hT hP hO ts tx hw hr (hRT _ _ hr) (hRI _ _ hr) z top
    hz htop pre (op :: post) hsplit r w hpre
  exact hT ts tx hw hr z top hz htop pre op post hsplit r w hpre hI hRO trivial

/-- As `SIS.Tree.getOK_scanOK_of_cases_merges`, for the runs of `N.Within`. -/
theorem getOK_scanOK_of_cases_merges (p : Params) (hp : MergeParamsOK p) (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t1 : OpCaseOK p (RunOK p) (QTree p) PutLeafRoomCase)
    (t2 : OpCaseOK p (RunOK p) (QTree p) PutLeafFullCase)
    (t3 : OpCaseOK p (RunOK p) (QTree p) PutNewSegCase)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i1 : OpCaseOK p (RunOK p) (QPutInv p) PutLeafRoomCase)
    (i2 : OpCaseOK p (RunOK p) (QPutInv p) PutLeafFullCase)
    (i3 : OpCaseOK p (RunOK p) (QPutInv p) PutNewSegCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r1 : OpCaseOK p (RunOK p) (QRange p) PutLeafRoomCase)
    (r2 : OpCaseOK p (RunOK p) (QRange p) PutLeafFullCase)
    (r3 : OpCaseOK p (RunOK p) (QRange p) PutNewSegCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hm : p.merges = true := by
    unfold MergeParamsOK at hp; unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hR : ∀ ts, Within p ts → RunOK p (treeRun p ts) ts.length :=
    fun ts hw => ⟨hlinks ts hw, htree ts hw, (hinv ts hw ts.length (Nat.le_refl _)).1⟩
  have hT := opCaseOK_of_cases_merges p _ _ hm t1 t2 t3 t4
  have hP := opCaseOK_of_cases_merges p _ _ hm i1 i2 i3 i4
  have hO := opCaseOK_of_cases_merges p _ _ hm r1 r2 r3 r4
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT : ∀ P t, RunOK p P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI : ∀ P t, RunOK p P t → InvOK p P t := fun _ _ h => h.2.2
  exact getOK_scanOK_of_open_merges p hp hinv hlinks htree
    (opTreeOK_of_any p _ hR hRL hRT hRI hT hP hO) (opPutInvOK_of_any p _ hRL hRT hRI hT hP hO)
    (opRangeOK_of_any p _ hO) hfit c4

/-- As `SIS.Tree.live_reached`, for the runs of `N.Within`. -/
theorem live_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) (hLv : OpCaseOK p R (QLive p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact liveCounts_init p ts tx hI z top hz htop
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          obtain ⟨hI1, hR1⟩ := joint_reached p R hRL hT hP hO ts tx hw hr hTA hI z top hz htop
            pre' (op :: post) hsplit' r1 w1 h1
          have hL1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
            hT ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2 h2
          have hL2 := hLv ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a
            w2 h2 hT2 hL1
          rw [← h.2]
          exact hL2

/-- As `SIS.Tree.opCaseOK_putNewSeg_of_parts`, for the runs of `N.Within`. -/
theorem opCaseOK_putNewSeg_of_parts (p : Params) (R : Struct BVal → Time → Prop)
    (Q : List Tx → Op → W → W → Prop)
    (a : OpCaseOK p R Q PutNewSeg1RoomCase) (b : OpCaseOK p R Q PutNewSegsRoomCase)
    (cF : OpCaseOK p R Q PutNewSegFullCase) :
    OpCaseOK p R Q PutNewSegCase := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hP
  obtain ⟨key, h, hop, hno⟩ := id hP
  have hkey : keyWf key = true := by
    have := within_op_keyWf p ts tx hw ops _ post hops
    rw [hop] at this; exact this
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  by_cases hseg : NewSegFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey
  · obtain ⟨pre, c0, tail, rk0, L, n, hk, htail, hrk0, hL, hn, hnl, hnone⟩ := hseg
    have hat : NewSegAt (ctxOf p ts) (viewOf (treeRun p ts)) w pre c0 tail rk0 L n :=
      ⟨htail, hrk0, hL, hn, hnl, hnone⟩
    by_cases hroom : n.size + 1 < p.M
    · cases tail with
      | nil => exact absurd rfl htail
      | cons cl rest =>
        cases rest with
        | nil =>
          exact a ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO
            ⟨pre, c0, cl, h, rk0, L, n, by rw [hop, hk], hat, hroom⟩
        | cons d rest' =>
          exact b ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO
            ⟨pre, c0, cl :: d :: rest', h, rk0, L, n, by rw [hop, hk], by simp, hat, hroom⟩
    · exact cF ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO
        ⟨pre, c0, tail, h, rk0, L, n, by rw [hop, hk], hat, hroom⟩
  · subst hop
    unfold putKv pathClear findRoot pathAdd
    wpSimplify
    generalize hw2 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
    have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
      subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine writerWP_mono (writerWP_putSegs_put_fail (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key h
      key w.top.rootKey w2 hne ?_ ?_ ?_) (fun _ _ hf => hf.elim)
    · intro q hq
      rw [hr02.2.2.1]
      rw [hr02.1] at hq
      exact hI.pathUntaken key q hq
    · rw [hr02.1]; exact hno'
    · rw [hr02.1]; exact hseg

/-- As `SIS.Tree.getOK_scanOK_of_cases_merges_open`, for the runs of `N.Within`. -/
theorem getOK_scanOK_of_cases_merges_open (p : Params) (hp : MergeParamsOK p)
    (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM : 2 ≤ p.M := by omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  exact getOK_scanOK_of_cases_merges p hp hinv hlinks htree hfit
    (treeCase_putLeafRoom p _) (treeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ hM) (treeCase_putNewSegsRoom p _ hM)
      (treeCase_putNewSegFull p _ hRL hM hsa)) t4
    (putInvCase_putLeafRoom p _ hRL) (putInvCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL hM)
      (putInvCase_putNewSegsRoom p _ hRL hM) (putInvCase_putNewSegFull p _ hRL hM hsa)) i4
    (rangeCase_putLeafRoom p _) (rangeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ hM)
      (rangeCase_putNewSegsRoom p _ hM) (rangeCase_putNewSegFull p _ hRL hM hsa)) r4
    c4

/-- As `SIS.Tree.latestGetOK_of_getOK`, for the runs of `N.Within`. -/
theorem latestGetOK_of_getOK (p : Params) (h : GetOK p) : LatestGetOK p :=
  fun ts hw key hkey => h ts hw ts.length (Nat.le_refl _) key hkey

/-- As `SIS.Tree.latestScanOK_of_scanOK`, for the runs of `N.Within`. -/
theorem latestScanOK_of_scanOK (p : Params) (h : ScanOK p) : LatestScanOK p :=
  fun ts hw req limit hreq => h ts hw ts.length (Nat.le_refl _) req limit hreq

end SIS.Tree.N
