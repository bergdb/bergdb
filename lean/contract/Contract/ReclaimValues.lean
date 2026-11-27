/-
bergdb 030-35: reclaim preserves the users' values. Since bergdb 031-06 (one
record an action) a step of reclaim rides in the record of a commit or of a part
of maintain(), beside the action's operations, and its copies carry the copy mark
(byte 6 of their value nodes; 027-03): the history marks maintenance per
operation, `maintenance j op` for the copies of record j (until 031-06 per
transaction: a step, or a store of reclaim's reserved namespace). Every copy is
a put of an old KV that a step's scan met, with the value the key had
immediately before the record (`StepOpOK`), and a record has one operation a
key; reclaim's row, table and settings are at its reserved keys. The reference
keeps the original transaction times and applies, of each record, only the
operations outside reclaim's namespace that are not copies: the action's.

The proof removes the copies from each record, rather than using the values
maintenance wrote as the reference: putting back a pair that the map holds, at
a key that no other operation of the record writes, changes nothing
(`applyOps_drop_copies`), so a record's effect on the user keys is that of its
operations without the copies, its action's (`record_preserves_users`). It
composes this preservation result with reclaim's cut-safety theorem. That the
operations without the mark are the action as submitted is tested, not proved:
the trace checker's C-STEP, STEP-action (lean/Check/Steps.lean,
`actionFailures`; 027-02, section 4).
-/
import Contract.ReclaimSteps

namespace Contract

open SIS.Check (BVal)

/-- A copy (bergdb 031-06; from 030-35 to 031-06 every operation of a step's
transaction but its row): a put of an old KV that the step's scan met, with the
value the key had immediately before the record. A copy is never a delete. -/
def StepOpOK (h : BHist) (c j : Nat) (out : ScanOut) : Op → Prop
  | .put k v => (∃ kv ∈ out.met, kv.1 = k ∧ oldNode h c kv.2 = true) ∧
      refGet (contents ((h.tree j).at j)) k = some v
  | .del _ => False

instance (h : BHist) (c j : Nat) (out : ScanOut) (op : Op) :
    Decidable (StepOpOK h c j out op) := by
  cases op <;> unfold StepOpOK <;> infer_instance

/-- The copy marks of a history are its steps' copies (bergdb 031-06): `maintenance
j op` marks the operation op of record j (zero-based) as a copy, as the copy mark
of its value node does in Java. Every record has one operation a key, and every
marked operation is a copy of a step's scan at that record (`StepOpOK`). The
marks assert no equality of maps. -/
def MaintenanceOK (h : BHist) (maintenance : Nat → Op → Bool) : Prop :=
  ∀ j (hj : j < h.txs.length), (h.txs[j].ops.map Op.key).Nodup ∧
    ∀ op ∈ h.txs[j].ops, maintenance j op = true →
      ∃ c E L rule, StepOpOK h c j (stepScan h E L ⟨j, rule⟩) op

/-- The independent reference's transactions: of each record, the operations
outside reclaim's namespace that are not copies, the action's. A record without
such operations (a part of maintain(), a setter of reclaim's) keeps its lookup
time with no operation. -/
def userTransactions (h : BHist) (maintenance : Nat → Op → Bool) : List (List Op) :=
  List.ofFn (fun j : Fin h.txs.length =>
    h.txs[j].ops.filter (fun op => userKey op.key && !maintenance j op))

theorem userTransactions_length (h : BHist) (maintenance : Nat → Op → Bool) :
    (userTransactions h maintenance).length = h.txs.length := by
  simp [userTransactions]

theorem userTransactions_get (h : BHist) (maintenance : Nat → Op → Bool) (j : Nat)
    (hj : j < h.txs.length) :
    (userTransactions h maintenance)[j]'(by simpa [userTransactions_length] using hj) =
      h.txs[j].ops.filter (fun op => userKey op.key && !maintenance j op) := by
  simp [userTransactions]

open PeProof.Keys

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

/-- A pair stays when a put at another key is applied. -/
theorem mem_mapPut_of_ne {k : Key} {v : Nat} {e : Key × Nat} (hne : e.1 ≠ k) :
    ∀ {m : List (Key × Nat)}, e ∈ m → e ∈ mapPut k v m
  | [], h => by simp at h
  | (k', v') :: r, h => by
    unfold mapPut
    split_ifs with h1 h2
    · exact List.mem_cons_of_mem _ h
    · exact List.mem_cons_of_mem _ ((List.mem_cons.mp h).resolve_left
        (fun he => hne (by rw [he]; exact h2.symm)))
    · rcases List.mem_cons.mp h with he | he
      · rw [he]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_mapPut_of_ne hne he)

/-- A pair stays when an operation at another key is applied. -/
theorem mem_step_of_ne {m : List (Key × Nat)} {op : Op} {e : Key × Nat}
    (hne : e.1 ≠ op.key) (h : e ∈ m) : e ∈ step m op := by
  cases op with
  | put k v => exact mem_mapPut_of_ne hne h
  | del k =>
    simp only [step, mapDel]
    exact List.mem_filter.mpr ⟨h, by simpa [Op.key] using hne⟩

/-- **Copies change nothing** (bergdb 031-06). On a map in key order, operations
with one operation a key, of which the marked ones put pairs that the map holds,
give the map that the unmarked ones give: a marked put leaves the map as it is,
and no later operation is at its key. -/
theorem applyOps_drop_copies (mk : Op → Bool) : ∀ (ops : List Op) (m : List (Key × Nat)),
    m.Pairwise KvLt → (ops.map Op.key).Nodup →
    (∀ op ∈ ops, mk op = true → ∃ k v, op = .put k v ∧ (k, v) ∈ m) →
    applyOps ops m = applyOps (ops.filter (fun op => !mk op)) m
  | [], _, _, _, _ => rfl
  | op :: ops, m, hs, hnd, hc => by
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hmk : mk op = true
    · obtain ⟨k, v, rfl, hkv⟩ := hc _ List.mem_cons_self hmk
      rw [applyOps_cons', List.filter_cons_of_neg (by simp [hmk])]
      change applyOps ops (mapPut k v m) = _
      rw [mapPut_existing hs hkv]
      exact applyOps_drop_copies mk ops m hs hnd.2
        (fun op' hop' hm' => hc op' (List.mem_cons_of_mem _ hop') hm')
    · rw [applyOps_cons', List.filter_cons_of_pos (by simpa using hmk), applyOps_cons']
      apply applyOps_drop_copies mk ops (step m op) (step_sorted op hs) hnd.2
      intro op' hop' hm'
      obtain ⟨k, v, rfl, hkv⟩ := hc op' (List.mem_cons_of_mem _ hop') hm'
      refine ⟨k, v, rfl, mem_step_of_ne ?_ hkv⟩
      intro he
      apply hnd.1
      have : (Op.put k v).key ∈ ops.map Op.key := List.mem_map_of_mem hop'
      simpa [Op.key, he] using this

/-- **A record's effect on the user keys is its action's** (bergdb 031-06): with
one operation a key, and its copies puts of the values that their keys hold before
it, the user keys after the record are as after its operations at user keys
without the copies, the action's. -/
theorem record_preserves_users (mk : Op → Bool) {ops : List Op} {m : List (Key × Nat)}
    (hs : m.Pairwise KvLt) (hnd : (ops.map Op.key).Nodup)
    (hc : ∀ op ∈ ops, mk op = true → ∃ k v, op = .put k v ∧ refGet m k = some v) :
    (applyOps ops m).filter (fun kv => userKey kv.1) =
      applyOps (ops.filter (fun op => userKey op.key && !mk op))
        (m.filter (fun kv => userKey kv.1)) := by
  rw [applyOps_filter userKey ops m hs]
  have hf : ops.filter (fun op => userKey op.key && !mk op) =
      (ops.filter (fun op => userKey op.key)).filter (fun op => !mk op) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro op _
    exact Bool.and_comm _ _
  rw [hf]
  apply applyOps_drop_copies mk _ _ (hs.filter _)
    (List.Nodup.sublist (List.Sublist.map Op.key (List.filter_sublist ..)) hnd)
  intro op hop hmk
  obtain ⟨hop, hu⟩ := List.mem_filter.mp hop
  obtain ⟨k, v, rfl, hg⟩ := hc op hop hmk
  exact ⟨k, v, rfl, List.mem_filter.mpr ⟨mem_of_lookup' hg, by simpa [Op.key] using hu⟩⟩

/-- The contract gives the full plain reference at the state of every time. -/
theorem MeetsFull.contents_ref {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {t : Nat} (ht : t ≤ h.txs.length) :
    contents ((h.tree t).at t) = refMap ((h.txs.map (·.ops)).take t) := by
  have hc := ((hm.meetsTop hM t ht).meets.at_time t (by simp; omega)).2
  simpa [← List.map_take, List.take_take] using hc

/-- **Maintenance preserves the users' reference at every history time.**
This includes times inside an iteration, before any cut, and intervening
user puts and deletes, in the records that carry the steps (bergdb 031-06) and
in others. No equality of references is assumed. -/
theorem user_contents_at {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {maintenance : Nat → Op → Bool}
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
    rw [htake, refMap_snoc, userTransactions_get h maintenance j hj', hc.2,
      ← user_contents_at hm hM hmaint j (by omega)]
    obtain ⟨hnd, hcp⟩ := hmaint j hj'
    refine record_preserves_users (maintenance j) hs hnd (fun op hop hmk => ?_)
    obtain ⟨c, E, L, rule, hst⟩ := hcp op hop hmk
    cases op with
    | del k => exact hst.elim
    | put k v => exact ⟨k, v, rfl, hst.2⟩

/-- The old all-operations reference, restricted to user keys, equals the
independent reference that excludes maintenance operations altogether. -/
theorem user_refMap {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {maintenance : Nat → Op → Bool}
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

/-- **Reclaim preserves users' reads after cuts** (bergdb 030-35), for any
history meeting the writer's contract, K-LEVEL and VAL-NEW, with cuts whose
iterations' steps follow the model and copy marks that are its steps' copies
(bergdb 031-06: until then the steps were marked as maintenance transactions,
`CutsMeetMaintenanceSteps`). -/
theorem reclaim_user_reads_steps {p : Params} {h : BHist} {top : Nat → Top}
    {kind : Nat → Bool} {maintenance : Nat → Op → Bool}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h) (hv : ValNew h)
    (hmaint : MaintenanceOK h maintenance)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts) (hit : CutsMeetSteps h al cs)
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
    hit hreads hft htn mid s tp hs htp
  exact hr.users (user_refMap hm hM hmaint htn)

end Contract

namespace Contract.PE

variable {cf : Cfg}

/-- **PE's reclaim preserves the users' values** (bergdb 030-35): after
reclaim's cuts, with handles, evictions and restarts, every retained-time
user get and scan agrees with the reference of users' operations alone.
Every copy is excluded (since bergdb 031-06 by its mark, an operation of a
record that may hold an action too), and every store of reclaim's reserved
keys. The premises describe the copies locally, never the equality of the
full and users-only references. -/
theorem pe_reclaim_user_reads_steps (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62)
    {txs : List (List Op)} {h : BHist} {top : Nat → Top} {maintenance : Nat → Op → Bool}
    (hlen : txs.length < 2 ^ 48 - 1) (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup)
    (hh : peHist cf txs = some (h, top)) (hM : 1 ≤ cf.params.M)
    (hmaint : MaintenanceOK h maintenance)
    (al : SIS.Algo SIS.Check.BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec)
    (hmk : al.mark = true) (hpol : SIS.PolicyCutOK al)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetSteps h al cs)
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
