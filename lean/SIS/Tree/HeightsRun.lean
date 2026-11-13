/-
The heights of P's key nodes after every run (bergdb 024-22, step 4; 024-12,
TP7's open (b)): the walk of the heights through a transaction's operations
(`ht_reached`, `execW_htCache`) and the step of a run (`heightAllOK_step`), by
induction over the run's transactions (`treeRun_heightAllOK`), as
`treeRun_kindsAllOK`. TP7's `HeightLiveOK` follows (`treeRun_heightLiveOK`), and with it latest's
assembly of TP7 takes `OpHtDelOK` in place of the live heights
(`invPreserved_of_open_htDel`).

The delete is a named premise, `OpHtDelOK`: a delete, from a state that the
transaction's earlier operations reach, keeps the walk's state. The put is
proved (`ht_putKv_put`).
-/
import SIS.Tree.HeightsStep
import SIS.Tree.KindsRun
import SIS.Tree.PutInvInit
import SIS.Tree.InvAssembly

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The delete side of the walk of the heights (named premise): a delete, at a
state that the transaction's earlier operations reach and that meets the walk's
state, keeps it. -/
def OpHtDelOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    WriterWP (putKv (.del key)) (ctxOf p ts) w
      (fun _ v => HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) v)

/-- A node of the walk from the root at time t is a key node. -/
theorem ht_mem_nodesAt_knode (p : Params) (view : View BVal) (t : Time) :
    ∀ (f : Nat) (r x : NodeId), x ∈ nodesAt p view t f r → ∃ n, knodeOf p view x = some n
  | 0, r, x, h => by simp [nodesAt] at h
  | f + 1, r, x, h => by
    unfold nodesAt at h
    split at h
    · simp at h
    · rename_i n hn
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨n, hn⟩
      · obtain ⟨⟨c, y⟩, _, hy⟩ := List.mem_flatMap.mp h
        have hy' : x ∈ nodesAt p view t f y := by
          by_cases hc : (n.leaf && segLen c != 7) = true
          · simp [hc] at hy
          · simpa [hc] using hy
        exact ht_mem_nodesAt_knode p view t f y x hy'

/-- The key nodes reached from the root are key nodes of P. -/
theorem ht_keyNodesAt_key (p : Params) (P : Struct BVal) (t : Time) :
    ∀ x ∈ keyNodesAt p P t, ∀ nd, P.get? x = some nd → nd.isData = false ∧ nd.level ≤ p.keyMax := by
  intro x hx nd hnd
  unfold keyNodesAt at hx
  split at hx
  · obtain ⟨n, hn⟩ := ht_mem_nodesAt_knode p (viewOf P) t p.fuel _ x hx
    obtain ⟨nd', hnd', hd, hlv, _⟩ := ht_knodeOf_some hn
    have hnd'' : P.get? x = some nd' := hnd'
    rw [hnd] at hnd''
    obtain rfl := Option.some.inj hnd''
    exact ⟨hd, hlv⟩
  · simp at hx

/-- The walk's premises on the view of a transaction of a run. -/
theorem viewHtOK_of_run (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (hK : KindsAllOK p (treeRun p ts))
    (hA : HeightAllOK p (treeRun p ts) ts.length) :
    ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) := by
  have hP := hR.1
  have hfresh := within_snoc_fresh p ts tx hw
  have htimes : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  have hB := putBase_of_run p ts tx hw hR
  refine ⟨hB.good.ids, viewHeights_of p (treeRun p ts) ts.length tx.base hfresh htimes hP hK hA,
    hB.good.ptrs, ?_⟩
  intro x nd hx t ht
  have hlt := hB.good.times x nd hx
  exact klongsOf_times nd.hist (ctxOf p ts).i (fun e he => Nat.le_of_lt (hlt e he)) _ ht t rfl

/-- The walk's state at the transaction's first state. -/
theorem htInv_start (H : NodeId → Nat → Prop) (B : NodeId) (c : Ctx) (top : Top) :
    HtInv H B c { next := B, top := top } := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n g h hn; cases hn
  · intro d a q cv y h1; simp at h1
  · intro d a q h1; simp at h1
  · rfl
  · intro x hx; simp at hx
  · intro d a q h1; simp at h1

/-- The walk's state at every state that a prefix of a transaction's operations
reaches. -/
theorem ht_reached (p : Params) (hM : 2 ≤ p.M) (hdel : OpHtDelOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hR : RunLinksOK p (treeRun p ts) ts.length)
    (hvo : ViewHtOK (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts))
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact htInv_start _ _ _ top
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
          have hbk := putBook_reached p ts tx hw hR z top htop pre' r1 w1 h1
          have hB := putBase_of_run p ts tx hw hR
          rw [← h.2]
          cases op with
          | put key hv0 =>
            exact (ht_putKv_put tx.base (appendFrameOK tx.base) key hv0 (ctxOf p ts) w1 hvo
              (by simp [ctxOf]) hbk.book hI1 hM hB.wf hbk.klongs a w2 h2).2.1
          | del key =>
            exact hdel ts tx hw z top hz htop pre' key post hsplit' r1 w1 h1 hI1 a w2 h2

/-- A successful transaction of the writer: the overlay's nodes not taken back
have their live children one height below them (`HtCache`). -/
theorem execW_htCache (p : Params) (hM : 2 ≤ p.M) (hdel : OpHtDelOK p) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hR : RunLinksOK p (treeRun p ts) ts.length)
    (hK : KindsAllOK p (treeRun p ts)) (hA : HeightAllOK p (treeRun p ts) ts.length)
    (bs : List Bool) (w : W)
    (he : execW p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w)) :
    HtCache (ctxOf p ts) (htOracleOf p (treeRun p ts)) w := by
  have hvo := viewHtOK_of_run p ts tx hw hR hK hA
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless (view (treeSpec p) (treeRun p ts) ts.length)) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      exact (ht_reached p hM hdel ts tx hw hR hvo z top hz ht tx.ops [] (by simp) bs w hr).cache

/-- Every inner key node has its live children one height below it, after
every run within reach, given the delete side of the walk. -/
theorem treeRun_heightAllOK (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hdel : OpHtDelOK p)
    (ts : List Tx) (hw : Within p ts) :
    HeightAllOK p (treeRun p ts) ts.length := by
  have hk : ∀ n, n ≤ ts.length → HeightAllOK p (treeRun p (ts.take n)) n := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      rw [h0]
      exact heightAllOK_init p 0
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      have hlen : (ts.take n).length = n := by simp; omega
      have hPn := hP (ts.take n) (within_take p ts hw n)
      have hR := runLinksOK_of_pointers p hM hP (ts.take n) (within_take p ts hw n)
      obtain ⟨hP', hH, hN⟩ := hR
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.2 n hlt).1
      have htimes : StructTimesLE (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) :=
        treeRun_timesLE p (ts.take n)
      have hl := viewLinksOK_of p _ _ ts[n].base hfresh htimes hP' hN
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      have he : execW p ts[n] ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1)) =
            .ok (bs, w) := hrun
      have hbook := execW_book p ts[n] ((ts.take n).length + 1) _ bs w
        (viewIdsBelow_view p (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) ts[n].base
          hfresh) he
      have hK := treeRun_kindsAllOK p hM hP (ts.take n) (within_take p ts hw n)
      have hA : HeightAllOK p (treeRun p (ts.take n)) (ts.take n).length := by
        rw [hlen]; exact ih (by omega)
      have hHt := execW_htCache p hM hdel (ts.take n) ts[n] hwn ⟨hP', hH, hN⟩ hK hA bs w he0
      have hA' : HeightAllOK p (treeRun p (ts.take n)) ((ts.take n).length + 1 - 1) := by
        simpa using hA
      have hstep := heightAllOK_step p _ ((ts.take n).length + 1) ts[n] bs w (by omega) hfresh
        htimes (treeRun_root_level p _) hH hl hPn he hbook hA' hHt
      rw [htake, treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
      have h1 : (ts.take n).length + 1 = n + 1 := by omega
      rw [← h1]
      exact hstep
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-- TP7's (b): the key nodes reached from the root at a run's last time have
their live children one height below them, given the delete side of the walk. -/
theorem treeRun_heightLiveOK (p : Params) (hM : 2 ≤ p.M)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (hdel : OpHtDelOK p)
    (ts : List Tx) (hw : Within p ts) :
    HeightLiveOK p (treeRun p ts) ts.length :=
  heightLiveOK_of_all p _ _ (treeRun_heightAllOK p hM hP hdel ts hw)
    (ht_keyNodesAt_key p _ _)

/-- latest's `invPreserved_of_open` with the live heights from the walk: the
delete side of the walk (`OpHtDelOK`) in place of `HeightLiveOK`. -/
theorem invPreserved_of_open_htDel (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hdel : OpHtDelOK p)
    (hNE : ∀ ts, Within p ts → NonEmptyOK p (treeRun p ts) ts.length)
    (hRT : ∀ ts, Within p ts → RootsOK p (treeRun p ts) ts.length)
    (hF : ∀ ts, Within p ts → FillOK p (treeRun p ts) ts.length)
    (hO : ∀ ts, Within p ts → RangeAtOK p (treeRun p ts) ts.length) : InvPreserved p :=
  invPreserved_of_open p hp hP hD
    (treeRun_heightLiveOK p (by have := mergeParamsOK_M p hp; omega) hP hdel) hNE hRT hF hO

end SIS.Tree
