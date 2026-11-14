/-
The tree model (bergdb 024-12, TP4, TP5 and TP7): what is left of the
structure's invariants that are no walk of the tree, after the walks of this
directory through the writer. One statement about the writer remains, the
take-back discipline (`TakeBackOKUnder`): at a transaction's end no overlay
node that is kept has a klong that names a node taken back, and the space
root is not taken back (fault 12 of 023-08 broke this). From it, for every
run within reach (`runLinksOK_of_takeBack`):

* TP4 (`PointersOK`): `pointersOK_step` with `execW_ptrsOK`, `execW_book`;
* a history for every key node (`KeyNonempty`): `execW_nonempty`;
* klongs well formed and giving the history (`KeyHistOK`): `keyHistOK_step`;

and with them the lift of the writer's overlay (`overlayLiftOK_of_takeBack`),
TP5 under valid parameters (`treeRun_sizeOK`), and TP7 from its latest time,
the take-back discipline and the bound on dead klongs
(`invPreserved_of_takeBack`).

The last two of the three, and TP5, need of the writer only what is proved;
TP4 after the earlier transactions is enough (`runLinksOK_of_pointers`,
`treeRun_sizeOK_of_pointers`). So TP7, which has TP4 in it, gives the lift
of the writer's overlay (`overlayLiftOK_of_invPreserved`), and TP10 and TP11
follow from TP7 and the writer's refinement of the map alone
(`getOK_of_inv_op`, `scanOK_of_inv_op`). TP7 itself, under valid parameters,
is its latest time, TP4 and the bound on dead klongs
(`invPreserved_of_latest_pointers`), the last one void without option 2.
-/
import SIS.Tree.OverlayLift
import SIS.Tree.PointersStep
import SIS.Tree.SizeStep
import SIS.Tree.WriterPtrsRun
import SIS.Tree.WriterNonemptyRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The invariants of P that the writer's lift needs: TP4, klongs that give
the histories, a history for every key node. -/
def RunLinksOK (p : Params) (P : Struct BVal) (_t : Time) : Prop :=
  PointersOK P ∧ KeyHistOK p P ∧ KeyNonempty p P

/-- What a transaction's last state must meet for TP4: no overlay node kept
has a klong naming a node taken back; the space root is not taken back. -/
def TakeBackEnd (w : W) : Prop :=
  (∀ q ∈ w.nodes, w.taken.contains q.1 = false →
    ∀ cv y, Klong.key cv y ∈ q.2.ks → w.taken.contains y = false) ∧
  w.taken.contains w.top.rootKey = false

/-- The take-back discipline, for transactions after a run whose structure
meets R. -/
def TakeBackOKUnder (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ noops w,
    runOps p tx.base tx.ops (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      .ok (noops, w) → TakeBackEnd w

theorem takeBackOKUnder_mono (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ P t, R P t → R' P t) (hT : TakeBackOKUnder p R') : TakeBackOKUnder p R :=
  fun ts tx hw hr => hT ts tx hw (h _ _ hr)

/-- The first top node of a transaction names nodes of P. -/
theorem topOf_old (p : Params) (P : Struct BVal) (t : Time) (htimes : StructTimesLE P t)
    (hP : PointersOK P) (z : NodeId) (top : Top)
    (h : topOf p (rootless (view (treeSpec p) P t)) z = .ok top) :
    (P.get? top.id).isSome = true ∧ (P.get? top.rootKey).isSome = true ∧
      ∀ q ∈ top.skips, (P.get? q.2).isSome = true := by
  unfold topOf at h
  cases hz : rootless (view (treeSpec p) P t) z with
  | none => rw [hz] at h; cases h
  | some nd =>
    rw [hz] at h
    simp only at h
    have hg := view_eq_get? p P t htimes z nd (rootless_some_eq _ z nd hz)
    have hm := mem_of_get? hg
    split at h
    · rename_i t0 y hf
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨by simp [hg], ?_, ?_⟩
      · obtain ⟨e, he, hv⟩ := List.exists_of_findSome?_eq_some hf
        cases hev : e.val with
        | rootKey y' =>
          rw [hev] at hv
          simp only [Option.some.injEq, Prod.mk.injEq] at hv
          exact hP _ hm e he y (by rw [hev, hv.2]; simp [bptrs])
        | key a b => rw [hev] at hv; cases hv
        | del a => rw [hev] at hv; cases hv
        | skip a b => rw [hev] at hv; cases hv
        | top a => rw [hev] at hv; cases hv
        | data a => rw [hev] at hv; cases hv
      · intro q hq
        obtain ⟨e, he, hv⟩ := List.mem_filterMap.mp hq
        cases hev : e.val with
        | skip j s =>
          rw [hev] at hv
          simp only [Option.some.injEq] at hv
          subst hv
          exact hP _ hm e he s (by rw [hev]; simp [bptrs])
        | key a b => rw [hev] at hv; cases hv
        | del a => rw [hev] at hv; cases hv
        | rootKey a => rw [hev] at hv; cases hv
        | top a => rw [hev] at hv; cases hv
        | data a => rw [hev] at hv; cases hv
    · cases h

/-- One transaction keeps TP4, the klongs that give the histories and a
history for every key node, if its last state meets the take-back
discipline. -/
theorem runLinksOK_step (p : Params) (hM : 2 ≤ p.M) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hR : RunLinksOK p (treeRun p ts) ts.length)
    (hT : ∀ noops w, runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w) → TakeBackEnd w) :
    RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hP, hH, hN⟩ := hR
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  obtain ⟨hT1, hT2⟩ := hT bs w hrun
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl : ViewLinksOK tx.base p (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) :=
    viewLinksOK_of p _ _ tx.base hfresh htimes hP hN
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (bs, w) := hrun
  have hvg := viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have hbook := execW_book p tx (ts.length + 1) _ bs w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have hne := execW_nonempty p tx (ts.length + 1) _ bs w hM hvg he
  have hvOld : ViewPtrsOld (fun y => ((treeRun p ts).get? y).isSome = true)
      (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) := by
    constructor
    · intro x nd hx
      simp [view_eq_get? p _ _ htimes x nd hx]
    · intro x nd hx cv y hk
      have hg := view_eq_get? p _ _ htimes x nd hx
      obtain ⟨e, hem, hv⟩ := klongsOf_key_mem nd.hist cv y hk
      exact hP _ (mem_of_get? hg) e hem y (by rw [hv]; simp [bptrs])
  have hptrs := execW_ptrsOK (fun y => ((treeRun p ts).get? y).isSome = true) p tx
    (ts.length + 1) _ bs w hvOld
    (fun z top _ ht => topOf_old p (treeRun p ts) _ htimes hP z top ht) he
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  refine ⟨?_, ?_, ?_⟩
  · exact pointersOK_step p (treeRun p ts) (ts.length + 1) tx bs w hfresh hP he hptrs hbook
      hT1 hT2
  · rw [← apply_exec_eq p (treeRun p ts) tx (ts.length + 1) _ bs w he]
    exact keyHistOK_step p (treeRun p ts) (ts.length + 1) tx bs w (by omega) hfresh htimes
      (treeRun_root_level p ts) hH hl he
  · intro x nd' hx hd hlv
    rcases apply_keyNode p (treeRun p ts) (ts.length + 1) tx bs w (by omega) hfresh htimes
      (treeRun_root_level p ts) hH hl he x nd' hx hd hlv with ⟨n, hlook, _, _, hk, _⟩ | ⟨hp0, _⟩
    · intro hnil
      rw [hnil] at hk
      exact hne (x, n) (mem_ids_of_lookup w.nodes x n hlook) hk.symm
    · exact hN x nd' hp0 hd hlv

theorem runLinksOK_init (p : Params) : RunLinksOK p (initStruct p) 0 := by
  refine ⟨pointersOK_init p, keyHistOK_init p, ?_⟩
  intro x nd hx hd hl
  rcases mem_init p (x, nd) (mem_of_get? hx) with h | h | h <;> cases h <;> simp

/-- TP4, klongs that give the histories and a history for every key node,
after every run within reach, from the take-back discipline. -/
theorem runLinksOK_of_takeBack (p : Params) (hM : 2 ≤ p.M)
    (hT : TakeBackOKUnder p (RunLinksOK p)) (ts : List Tx) (hw : Within p ts) :
    RunLinksOK p (treeRun p ts) ts.length := by
  have hk : ∀ n, n ≤ ts.length → RunLinksOK p (treeRun p (ts.take n)) n := by
    intro n
    induction n with
    | zero => intro _; exact runLinksOK_init p
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hlen : (ts.take n).length = n := by
        simp only [List.length_take]; omega
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hr : RunLinksOK p (treeRun p (ts.take n)) (ts.take n).length := ih (by omega)
      have hs := runLinksOK_step p hM (ts.take n) ts[n] hwn hr
        (fun noops w hrun => hT (ts.take n) ts[n] hwn hr noops w hrun)
      rw [htake]
      exact hs
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- TP4 from the take-back discipline. -/
theorem pointersOK_of_takeBack (p : Params) (hM : 2 ≤ p.M)
    (hT : TakeBackOKUnder p (RunLinksOK p)) (ts : List Tx) (hw : Within p ts) :
    PointersOK (treeRun p ts) := (runLinksOK_of_takeBack p hM hT ts hw).1

/-- The lift of the writer's overlay from the take-back discipline. -/
theorem overlayLiftOK_of_takeBack (p : Params) (hM : 2 ≤ p.M)
    (hT : TakeBackOKUnder p (RunLinksOK p)) : OverlayLiftOK p :=
  overlayLiftOK_of_under p _ (fun ts hw => runLinksOK_of_takeBack p hM hT ts hw)
    (overlayLiftOKUnder_links p)

theorem mergeParamsOK_M (p : Params) (hp : MergeParamsOK p) : 6 ≤ p.M := by
  unfold MergeParamsOK at hp
  omega

theorem sizeOK_init (p : Params) (hM : 1 ≤ p.M) : SizeOK p (initStruct p) := by
  intro x n hx
  unfold keyNodeAt at hx
  cases hg : (initStruct p).get? x with
  | none => rw [hg] at hx; cases hx
  | some nd =>
    rw [hg] at hx
    rcases mem_init p (x, nd) (mem_of_get? hg) with h | h | h <;> cases h
    · have := rootLevel_gt p
      simp [Nat.not_le.mpr this] at hx
    · have hk := initial_key_level_le p
      simp only [Bool.not_false, Bool.true_and, hk, decide_true, ↓reduceIte,
        Option.some.injEq] at hx
      have h1 : (klongsOf [(⟨0, marker⟩ : Entry BVal)]).length = 1 := by decide
      rw [← hx]
      show (klongsOf [(⟨0, marker⟩ : Entry BVal)]).length ≤ p.M
      omega
    · simp [Params.topLevel] at hx
      exact absurd (of_decide_eq_true hx.1) (by omega)

/-! ## From TP4 alone

A history for every key node and klongs that give the histories need no
statement about the writer beyond TP4 after the earlier transactions: so
TP7, which has TP4 in it, gives the lift of the writer's overlay. -/

/-- One transaction keeps a history for every key node, from TP4 before it. -/
theorem keyNonempty_step (p : Params) (hM : 2 ≤ p.M) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hR : RunLinksOK p (treeRun p ts) ts.length) :
    KeyHistOK p (treeRun p (ts ++ [tx])) ∧ KeyNonempty p (treeRun p (ts ++ [tx])) := by
  obtain ⟨hP, hH, hN⟩ := hR
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have h := (hw.2 ts.length (by simp)).1
    have hj : (ts ++ [tx])[ts.length]'(by simp) = tx := by simp
    have ht : (ts ++ [tx]).take ts.length = ts := by simp
    rw [hj, ht] at h
    exact h
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl : ViewLinksOK tx.base p (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) :=
    viewLinksOK_of p _ _ tx.base hfresh htimes hP hN
  have he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) =
      .ok (bs, w) := hrun
  have hvg := viewGood_of p (treeRun p ts) (ts.length + 1) tx.base (by omega) hfresh htimes hl
  have hne := execW_nonempty p tx (ts.length + 1) _ bs w hM hvg he
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  refine ⟨?_, ?_⟩
  · rw [← apply_exec_eq p (treeRun p ts) tx (ts.length + 1) _ bs w he]
    exact keyHistOK_step p (treeRun p ts) (ts.length + 1) tx bs w (by omega) hfresh htimes
      (treeRun_root_level p ts) hH hl he
  · intro x nd' hx hd hlv
    rcases apply_keyNode p (treeRun p ts) (ts.length + 1) tx bs w (by omega) hfresh htimes
      (treeRun_root_level p ts) hH hl he x nd' hx hd hlv with ⟨n, hlook, _, _, hk, _⟩ | ⟨hp0, _⟩
    · intro hnil
      rw [hnil] at hk
      exact hne (x, n) (mem_ids_of_lookup w.nodes x n hlook) hk.symm
    · exact hN x nd' hp0 hd hlv

/-- TP4 after every run within reach gives the klongs that give the
histories and a history for every key node, after every run within reach. -/
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

/-- The lift of the writer's overlay from TP4. -/
theorem overlayLiftOK_of_pointers (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) : OverlayLiftOK p :=
  overlayLiftOK_of_under p _ (fun ts hw => runLinksOK_of_pointers p hM hP ts hw)
    (overlayLiftOKUnder_links p)

/-- The lift of the writer's overlay from TP7. -/
theorem overlayLiftOK_of_invPreserved (p : Params) (hM : 2 ≤ p.M) (hinv : InvPreserved p) :
    OverlayLiftOK p :=
  overlayLiftOK_of_pointers p hM (fun ts hw => (hinv ts hw ts.length (Nat.le_refl _)).2)

/-- TP10 from TP7 and the writer's refinement of the map. -/
theorem getOK_of_inv_op (p : Params) (hM : 2 ≤ p.M) (hinv : InvPreserved p) (ho : OpGetOK p) :
    GetOK p :=
  getOK_of_op_overlay p hinv ho (overlayLiftOK_of_invPreserved p hM hinv)

/-- TP11 from TP7 and the writer's refinement of the map. -/
theorem scanOK_of_inv_op (p : Params) (hM : 2 ≤ p.M) (hinv : InvPreserved p) (ho : OpGetOK p) :
    ScanOK p :=
  scanOK_of_op_overlay p hinv ho (overlayLiftOK_of_invPreserved p hM hinv)

/-- TP5 for every run within reach, under valid parameters, from TP4. -/
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
      have hfresh := (hw.2 n hlt).1
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

/-- TP7 under valid parameters from the invariants at each run's last time,
TP4 and the bound on dead klongs: TP5, the klongs' well-formedness and the
histories follow. -/
theorem invPreserved_of_latest_pointers (p : Params) (hp : MergeParamsOK p) (hL : LatestInvOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts)) : InvPreserved p := by
  have hM := mergeParamsOK_M p hp
  exact invPreserved_of_parts p hL hP
    (fun ts hw => treeRun_sizeOK_of_pointers p hp hP ts hw)
    (fun ts hw => (runLinksOK_of_pointers p (by omega) hP ts hw).2.2) hD

/-- Without option 2 (theta 0) the bound on dead klongs asks nothing. -/
theorem deadAllOK_of_theta_zero (p : Params) (h0 : p.theta = 0) (P : Struct BVal) :
    DeadAllOK p P := fun _ _ _ hne => (hne h0).elim

/-- TP7 under valid parameters without option 2: from the invariants at each
run's last time and TP4. -/
theorem invPreserved_of_latest_pointers_theta0 (p : Params) (hp : MergeParamsOK p)
    (h0 : p.theta = 0) (hL : LatestInvOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) : InvPreserved p :=
  invPreserved_of_latest_pointers p hp hL hP (fun _ _ => deadAllOK_of_theta_zero p h0 _)

/-! ## From the take-back discipline -/

/-- TP5 for every run within reach, under valid parameters, from the
take-back discipline. -/
theorem treeRun_sizeOK (p : Params) (hp : MergeParamsOK p)
    (hT : TakeBackOKUnder p (RunLinksOK p)) (ts : List Tx) (hw : Within p ts) :
    SizeOK p (treeRun p ts) :=
  treeRun_sizeOK_of_pointers p hp
    (fun ts hw => pointersOK_of_takeBack p (by have := mergeParamsOK_M p hp; omega) hT ts hw) ts hw

/-- TP7 under valid parameters, from the invariants at each run's last time,
the take-back discipline and the bound on dead klongs. -/
theorem invPreserved_of_takeBack (p : Params) (hp : MergeParamsOK p) (hL : LatestInvOK p)
    (hT : TakeBackOKUnder p (RunLinksOK p))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts)) : InvPreserved p :=
  invPreserved_of_latest_pointers p hp hL
    (fun ts hw => pointersOK_of_takeBack p (by have := mergeParamsOK_M p hp; omega) hT ts hw) hD

end SIS.Tree
