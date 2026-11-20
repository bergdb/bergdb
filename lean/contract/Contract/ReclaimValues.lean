/-
bergdb 030-35: reclaim preserves the users' values. A history distinguishes
user transactions from maintenance. A maintenance transaction is either a
modelled reclaim step, or writes only reclaim's reserved namespace (table,
row and filler stores). The reference keeps the original transaction times
and applies only user operations outside that namespace.

The proof removes maintenance from the reference, rather than using the
values maintenance wrote as the reference. It composes this preservation
result with reclaim's existing cut-safety theorem.
-/
import Contract.ReclaimSteps

namespace Contract

open SIS.Check (BVal)

/-- Every maintenance transaction is a step meeting the strengthened model,
or writes only reclaim's reserved keys. The Boolean marks maintenance at
zero-based transaction indexes; it does not assert any equality of maps. -/
def MaintenanceOK (h : BHist) (maintenance : Nat → Bool) : Prop :=
  ∀ j (hj : j < h.txs.length), maintenance j = true →
    (∀ op ∈ h.txs[j].ops, reclaimKey op.key = true) ∨
    ∃ c E L rule, StepTx h c j (stepScan h E L ⟨j, rule⟩) h.txs[j].ops

/-- The independent reference's transactions. Maintenance contributes no
operations; the other transactions contribute only keys outside reclaim's
namespace. Empty transactions keep the original lookup times. -/
def userTransactions (h : BHist) (maintenance : Nat → Bool) : List (List Op) :=
  List.ofFn (fun j : Fin h.txs.length =>
    if maintenance j then [] else h.txs[j].ops.filter (fun op => userKey op.key))

theorem userTransactions_length (h : BHist) (maintenance : Nat → Bool) :
    (userTransactions h maintenance).length = h.txs.length := by
  simp [userTransactions]

theorem userTransactions_get (h : BHist) (maintenance : Nat → Bool) (j : Nat)
    (hj : j < h.txs.length) :
    (userTransactions h maintenance)[j]'(by simpa [userTransactions_length] using hj) =
      if maintenance j then [] else h.txs[j].ops.filter (fun op => userKey op.key) := by
  simp [userTransactions]

open PeProof.Keys

/-- Every non-row put is an old key met, carrying its pre-step value. -/
theorem StepTx.put_value {h : BHist} {c j : Nat} {out : ScanOut} {ops : List Op}
    (ht : StepTx h c j out ops) {k : Key} {v : Nat} (hp : Op.put k v ∈ ops)
    (hk : k ≠ reclaimRow) :
    (∃ kv ∈ out.met, kv.1 = k ∧ oldNode h c kv.2 = true) ∧
      refGet (contents ((h.tree j).at j)) k = some v := by
  exact (ht.2.2.2 (.put k v) hp).resolve_left hk

/-- Deletes, including extra deletes, are forbidden in a step. -/
theorem StepTx.no_delete {h : BHist} {c j : Nat} {out : ScanOut} {ops : List Op}
    (ht : StepTx h c j out ops) (k : Key) : Op.del k ∉ ops := by
  intro hd
  exact ht.2.2.2 (.del k) hd

/-- Putting an existing pair back into a map in key order changes nothing. -/
theorem mapPut_existing {k : Key} {v : Nat} : ∀ {m : List (Key × Nat)},
    m.Pairwise KvLt → (k, v) ∈ m → mapPut k v m = m
  | [], _, hm => by simp at hm
  | (k', v') :: rest, hs, hm => by
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact mapPut_cons_self
    · have hlt : k' < k := (List.pairwise_cons.mp hs).1 _ hm
      rw [mapPut_cons_gt hlt, mapPut_existing (List.pairwise_cons.mp hs).2 hm]

/-- A list of puts of pairs already present changes no map entries. -/
theorem applyOps_existing (m : List (Key × Nat)) (hs : m.Pairwise KvLt) :
    ∀ (ops : List Op),
      (∀ op ∈ ops, ∃ k v, op = .put k v ∧ (k, v) ∈ m) → applyOps ops m = m
  | [], _ => rfl
  | op :: rest, h => by
    obtain ⟨k, v, rfl, hm⟩ := h op (by simp)
    rw [applyOps_cons']
    change applyOps rest (mapPut k v m) = m
    rw [mapPut_existing hs hm]
    exact applyOps_existing m hs rest (fun op hop => h op (List.mem_cons_of_mem _ hop))

/-- **One step preserves user contents.** Every non-row operation is a put
of the value in the state immediately before the step; the row is reserved. -/
theorem StepTx.preserves_users {h : BHist} {c j : Nat} {out : ScanOut} {ops : List Op}
    (ht : StepTx h c j out ops)
    (hs : (contents ((h.tree j).at j)).Pairwise KvLt) :
    (applyOps ops (contents ((h.tree j).at j))).filter (fun kv => userKey kv.1) =
      (contents ((h.tree j).at j)).filter (fun kv => userKey kv.1) := by
  rw [applyOps_filter userKey ops _ hs]
  apply applyOps_existing _ (hs.filter _)
  intro op hop
  obtain ⟨hop, hu⟩ := List.mem_filter.mp hop
  have ht' := ht.2.2.2 op hop
  cases op with
  | del k => exact ht'.elim
  | put k v =>
    refine ⟨k, v, rfl, List.mem_filter.mpr ⟨?_, hu⟩⟩
    rcases ht' with rfl | hcopy
    · simp [userKey, reclaimRow_reserved, Op.key] at hu
    · exact mem_of_lookup' hcopy.2

/-- Namespace-only stores also preserve user contents, including deletes. -/
theorem reserved_preserves_users (ops : List Op) (m : List (Key × Nat))
    (hs : m.Pairwise KvLt) (hr : ∀ op ∈ ops, reclaimKey op.key = true) :
    (applyOps ops m).filter (fun kv => userKey kv.1) = m.filter (fun kv => userKey kv.1) := by
  rw [applyOps_filter userKey ops m hs]
  have hf : ops.filter (fun op => userKey op.key) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro op hop
    simp [userKey, hr op hop]
  rw [hf]
  rfl

/-- The contract gives the full plain reference at the state of every time. -/
theorem MeetsFull.contents_ref {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {t : Nat} (ht : t ≤ h.txs.length) :
    contents ((h.tree t).at t) = refMap ((h.txs.map (·.ops)).take t) := by
  have hc := ((hm.meetsTop hM t ht).meets.at_time t (by simp; omega)).2
  simpa [← List.map_take, List.take_take] using hc

/-- **Maintenance preserves the users' reference at every history time.**
This includes times inside an iteration, before any cut, and intervening
user puts and deletes. No equality of references is assumed. -/
theorem user_contents_at {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {maintenance : Nat → Bool}
    (hmaint : MaintenanceOK h maintenance) : ∀ t, t ≤ h.txs.length →
      (contents ((h.tree t).at t)).filter (fun kv => userKey kv.1) =
        refMap ((userTransactions h maintenance).take t)
  | 0, _ => by
    change (contents (h.s0.at 0)).filter _ = _
    rw [(hm.start.start hM).2]
    rfl
  | j + 1, hj => by
    have hj' : j < h.txs.length := by omega
    have hc := (hm.step j hj').1.1
    simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hc
    have hs : (contents ((h.tree j).at j)).Pairwise KvLt := by
      simpa only [List.pairwise_map] using contents_sorted (hm.inv_at hM j (by omega))
    have hju : j < (userTransactions h maintenance).length := by
      simpa [userTransactions_length] using hj'
    have htake : (userTransactions h maintenance).take (j + 1) =
        (userTransactions h maintenance).take j ++ [(userTransactions h maintenance)[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hju]
      rfl
    rw [htake, refMap_snoc, userTransactions_get h maintenance j hj', hc.2]
    cases hmark : maintenance j with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rw [applyOps_filter userKey _ _ hs, user_contents_at hm hM hmaint j (by omega)]
    | true =>
      simp only [ite_true]
      change _ = refMap ((userTransactions h maintenance).take j)
      rw [← user_contents_at hm hM hmaint j (by omega)]
      rcases hmaint j hj' hmark with hr | ⟨c, E, L, rule, hstep⟩
      · exact reserved_preserves_users _ _ hs hr
      · exact hstep.preserves_users hs

/-- The old all-operations reference, restricted to user keys, equals the
independent reference that excludes maintenance operations altogether. -/
theorem user_refMap {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {maintenance : Nat → Bool}
    (hmaint : MaintenanceOK h maintenance) {t : Nat} (ht : t ≤ h.txs.length) :
    (refMap ((h.txs.map (·.ops)).take t)).filter (fun kv => userKey kv.1) =
      refMap ((userTransactions h maintenance).take t) := by
  rw [← hm.contents_ref hM ht]
  exact user_contents_at hm hM hmaint t ht

/-- A get of a user key is unchanged by removing reserved keys. -/
theorem refGet_filter_user (m : List (Key × Nat)) (k : Key) (hk : userKey k = true) :
    refGet (m.filter (fun kv => userKey kv.1)) k = refGet m k := by
  induction m with
  | nil => rfl
  | cons kv rest ih =>
    obtain ⟨k', v⟩ := kv
    cases hu : userKey k' with
    | true =>
      simp only [List.filter_cons, hu, ite_true, refGet, List.lookup_cons]
      cases k == k' with
      | false => exact ih
      | true => rfl
    | false =>
      have hne : k ≠ k' := by
        rintro rfl
        rw [hu] at hk
        cases hk
      simp only [List.filter_cons, hu, Bool.false_eq_true, ite_false, refGet,
        List.lookup_cons, beq_eq_false_iff_ne.mpr hne]
      exact ih

/-- Filtering a complete scan to user keys, then taking its limit, is a
scan of the user map, for every range and either direction. -/
theorem refScan_filter_user (m : List (Key × Nat)) (req : ScanReq) {n : Nat}
    (hn : m.length ≤ n) (limit : Nat) :
    ((refScan m req n).filter (fun kv => userKey kv.1)).take limit =
      refScan (m.filter (fun kv => userKey kv.1)) req limit := by
  have hc : (m.filter (fun kv => inRange req kv.1)).filter (fun kv => userKey kv.1) =
      (m.filter (fun kv => userKey kv.1)).filter (fun kv => inRange req kv.1) := by
    simp only [List.filter_filter]
    apply List.filter_congr
    intro kv _
    exact Bool.and_comm _ _
  have hlen := (List.length_filter_le (fun kv => inRange req kv.1) m).trans hn
  unfold refScan
  cases req.forward with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have ht : (m.filter (fun kv => inRange req kv.1)).reverse.take n =
        (m.filter (fun kv => inRange req kv.1)).reverse :=
      List.take_of_length_le (by simpa using hlen)
    rw [ht, List.filter_reverse, hc]
  | true =>
    simp only [ite_true]
    rw [List.take_of_length_le hlen, hc]

/-- A user-range scan agrees directly, including its requested limit. -/
theorem refScan_user_range (m : List (Key × Nat)) (req : ScanReq)
    (hu : ∀ k, inRange req k = true → userKey k = true) (limit : Nat) :
    refScan m req limit = refScan (m.filter (fun kv => userKey kv.1)) req limit := by
  have hf : m.filter (fun kv => inRange req kv.1) =
      (m.filter (fun kv => userKey kv.1)).filter (fun kv => inRange req kv.1) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro kv _
    cases hi : inRange req kv.1 with
    | false => simp
    | true => simp [hu kv.1 hi]
  unfold refScan
  rw [hf]

/-- At any raw Core scan limit, the user results are a prefix of the
users-only reference, with the same values and no user key skipped. Rows
may consume some of the raw limit. -/
theorem refScan_user_prefix (m : List (Key × Nat)) (req : ScanReq) (limit : Nat) :
    ∃ n, n ≤ limit ∧ (refScan m req limit).filter (fun kv => userKey kv.1) =
      refScan (m.filter (fun kv => userKey kv.1)) req n := by
  refine ⟨((refScan m req limit).filter (fun kv => userKey kv.1)).length, ?_, ?_⟩
  · exact (List.length_filter_le _ _).trans (List.length_take_le _ _)
  · have hc : (m.filter (fun kv => inRange req kv.1)).filter (fun kv => userKey kv.1) =
        (m.filter (fun kv => userKey kv.1)).filter (fun kv => inRange req kv.1) := by
      simp only [List.filter_filter]
      apply List.filter_congr
      intro kv _
      exact Bool.and_comm _ _
    unfold refScan
    cases req.forward with
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hp := List.prefix_iff_eq_take.mp
        ((List.take_prefix limit (m.filter (fun kv => inRange req kv.1)).reverse).filter
          (fun kv => userKey kv.1))
      simpa only [List.filter_reverse, hc] using hp
    | true =>
      simp only [ite_true]
      have hp := List.prefix_iff_eq_take.mp
        ((List.take_prefix limit (m.filter (fun kv => inRange req kv.1))).filter
          (fun kv => userKey kv.1))
      simpa only [hc] using hp

/-- Java's reads agree with the users-only reference. Gets protect every
key outside reclaim's namespace. At every raw scan limit the user results
are a prefix of the user reference. Every scan range, exhausted and
projected to user keys before taking the limit, gives exactly the user scan. A scan
whose range excludes reserved keys agrees directly at every limit, without
projection. Raw Core scans across reserved rows can return those rows. -/
def JUserReadsRight (s : Tree) (tp : Top) (t : Time) (mid : Bool)
    (users : List (List Op)) : Prop :=
  (∀ key, userKey key = true →
    jget s tp t mid key = refGet (refMap (users.take t)) key) ∧
  (∀ req, req.wf = true → ∀ limit, ∃ n, n ≤ limit ∧
    (jscan s tp t mid req limit).filter (fun kv => userKey kv.1) =
      refScan (refMap (users.take t)) req n) ∧
  (∀ req, req.wf = true → ∃ n, ∀ limit,
    ((jscan s tp t mid req n).filter (fun kv => userKey kv.1)).take limit =
      refScan (refMap (users.take t)) req limit) ∧
  (∀ req, req.wf = true → (∀ key, inRange req key = true → userKey key = true) →
    ∀ limit, jscan s tp t mid req limit = refScan (refMap (users.take t)) req limit)

theorem JReadsRight.users {s : Tree} {tp : Top} {t : Nat} {mid : Bool}
    {txs users : List (List Op)} (hr : JReadsRight s tp t mid txs)
    (hu : (refMap (txs.take t)).filter (fun kv => userKey kv.1) = refMap (users.take t)) :
    JUserReadsRight s tp t mid users := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro key hk
    rw [hr.1 key, ← hu, refGet_filter_user _ _ hk]
  · intro req hreq limit
    rw [hr.2 req hreq limit, ← hu]
    exact refScan_user_prefix _ _ _
  · intro req hreq
    refine ⟨(refMap (txs.take t)).length, fun limit => ?_⟩
    rw [hr.2 req hreq _, ← hu]
    exact refScan_filter_user _ _ (le_refl _) _
  · intro req hreq huser limit
    rw [hr.2 req hreq limit, ← hu]
    exact refScan_user_range _ _ huser _

/-- Cuts whose iterations follow the strengthened step model, with every
step designated maintenance. The remaining cut premises are unchanged. -/
def CutsMeetMaintenanceSteps (h : BHist) (al : SIS.Algo BVal Nat)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (maintenance : Nat → Bool) : Prop :=
  ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
    (∀ i (hi : i < j) c', cs[i].2.1 = some c' → c' ≤ c) ∧
    ∃ it : Iteration, it.c = c ∧ StepsOK h it ∧
      (∀ st ∈ it.steps, maintenance st.j = true) ∧
      it.last ≤ SIS.lastFa (SIS.run h.spec al (h.ts.take (j + 1))).S ∧
      RC4 h.spec al h.ts it.last (j + 1)

theorem CutsMeetMaintenanceSteps.cutsMeetSteps {h : BHist} {al : SIS.Algo BVal Nat}
    {cs : List (Nat × Option Nat × List SIS.HCacheOp)} {maintenance : Nat → Bool}
    (hc : CutsMeetMaintenanceSteps h al cs maintenance) : CutsMeetSteps h al cs := by
  intro j hj c hcut
  obtain ⟨hord, it, hci, hit, -, hfa, hwait⟩ := hc j hj c hcut
  exact ⟨hord, it, hci, hit, hfa, hwait⟩

/-- **Reclaim preserves users' reads after cuts** (bergdb 030-35), for any
history meeting the writer's contract, K-LEVEL and VAL-NEW. -/
theorem reclaim_user_reads_steps {p : Params} {h : BHist} {top : Nat → Top}
    {kind : Nat → Bool} {maintenance : Nat → Bool}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h) (hv : ValNew h)
    (hmaint : MaintenanceOK h maintenance)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts) (hit : CutsMeetMaintenanceSteps h al cs maintenance)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JUserReadsRight s tp t mid (userTransactions h maintenance) := by
  intro V hs htp
  have hr := reclaim_java_reads_steps hm hM hkd hv al hj hmk hpol cs hcs
    hit.cutsMeetSteps hreads hft htn mid s tp hs htp
  exact hr.users (user_refMap hm hM hmaint htn)

end Contract

namespace Contract.PE

variable {cf : Cfg}

/-- **PE's reclaim preserves the users' values** (bergdb 030-35): after
reclaim's cuts, with handles, evictions and restarts, every retained-time
user get and scan agrees with the reference of users' operations alone.
All maintenance transactions are excluded, including step rewrites. The
premises describe local step operations and namespace-only stores, never
the equality of the full and users-only references. -/
theorem pe_reclaim_user_reads_steps (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62)
    {txs : List (List Op)} {h : BHist} {top : Nat → Top} {maintenance : Nat → Bool}
    (hlen : txs.length < 2 ^ 48 - 1) (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup)
    (hh : peHist cf txs = some (h, top)) (hM : 1 ≤ cf.params.M)
    (hmaint : MaintenanceOK h maintenance)
    (al : SIS.Algo SIS.Check.BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec)
    (hmk : al.mark = true) (hpol : SIS.PolicyCutOK al)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetMaintenanceSteps h al cs maintenance)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf (peKind cf) V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JUserReadsRight s tp t mid (userTransactions h maintenance) := by
  have hf := pe_full hcf hcap hlen hk hh
  exact reclaim_user_reads_steps hf.1 hM hf.2 (pe_valNew hcf hcap hlen hk hh)
    hmaint al hj hmk hpol cs hcs hit hreads hft htn mid s tp

end Contract.PE
