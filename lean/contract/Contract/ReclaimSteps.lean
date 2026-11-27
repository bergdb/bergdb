/-
The contract package (bergdb 030-25): reclaim's iteration, step by step. A
model of the iteration's steps (bergdb 027-13, section 1.4) on the contract's
histories, and the proof that a history whose steps follow it meets
`IterationOK` (030-24), so that what stays tested of the iteration is that
Java's steps are the model's steps.

The model. An iteration has its cut c (a value node made by a transaction
before c is stored before pCut), its start t0 (tStart: E, the end key, is the
greatest key live after transaction t0, Java's `lastKeyAt`), and its steps, in
order. Step st is the transaction st.j + 1; it holds the write lock, so its scan
reads the latest state, the tree after transaction st.j. The scan walks the
live keys after lastKey (every key for the first step) up to E, in key order,
each with its value node; at each KV it may stop before it (the value limit:
the KV is the next step's first) or after it (the split, the size), as a stop
rule says. The model quantifies over the stop rules: Java's byte and node
counts decide where a step stops, not which keys are rewritten. lastKey becomes
the last key met. The step's record writes each KV met whose value node is old
(made before c) and puts the row, one operation a key. Since bergdb 031-06 (one
record an action) a step rides in the record of a commit or of a part of
maintain(), decided from the stream before the record: its scan reads the state
after the record before, and the record holds the action's operations beside the
step's copies, its row and maybe its table. An old KV met is written by its copy,
or by the action's put or delete at its key (Java leaves out a copy at a key that
the action writes), or by reclaim's row or table there. What a copy is (a put of
an old KV met with the value immediately before the record) is stated with the
copy mark in Contract/ReclaimValues.lean (`StepOpOK`); the cut's safety needs only
that the record writes the key. The last step's scan passed E or the last key
without a stop (Java's `eod`). Between the steps run any transactions: the
user's, the parts' records, the table stored again. Restarts need nothing more: a
step's record holds its row, with lastKey, E and pCut, and a start resumes from
the row, so the steps of a run with restarts are such steps in the history of its
commits; a last step whose end was lost in a crash is an ordinary step, and the
next one ends the iteration (bergdb 030-25, section 2).

The theorem (`iterationOK_of_stepsOK`): with VAL-NEW, such a history meets
`IterationOK` from every s with t0 < s up to the first step, to the last step
e. A key that names an old value node at s - 1 named it at t0 (a later put
makes a new node; a node is made once, `MeetsFull.made_once`), so it is at
most E; each step's scan met it if it was not written before, unless the step
stopped before it, and then lastKey is below it and a later step's scan
begins below it; the last step met every key of its range. The top theorems
(`reclaim_java_reads_steps`, `PE.pe_reclaim_reads_steps`) take the steps in
place of `IterationOK` and a live key at the iteration's end (the last step
puts its row).
-/
import Contract.ReclaimTree

namespace Contract

open SIS.Check (BVal)

/-! ## 1. The model of the steps -/

/-- Key k is after the last key L of the steps before; every key is when there
is none (the iteration's first step). -/
def afterKey : Option Key → Key → Bool
  | none, _ => true
  | some l, k => keyLt l k

/-- Key k is at most the end key E; no key is when E is none (no key was live
at tStart). -/
def upToKey : Option Key → Key → Bool
  | none, _ => false
  | some e, k => !keyLt e k

/-- E, the end key of an iteration that starts on the tree s: the greatest key
live (Java's `Reclaim.lastKeyAt`); none if no key is. -/
def endKey (s : Tree) : Option Key := ((contents s).map Prod.fst).getLast?

/-- What a step's scan walks: the live keys of the tree s, each with the id of
its value node, after L and up to E, in key order. -/
def scanRange (s : Tree) (L E : Option Key) : List (Key × NodeId) :=
  (idContents s).filter (fun kv => afterKey L kv.1 && upToKey E kv.1)

/-- A stop rule: for the KVs met so far and the next KV, whether to stop before
it (Java: the value limit), and if not, whether to stop after it (Java: the
split, the size). -/
abbrev StopRule := List (Key × NodeId) → Key × NodeId → Bool × Bool

/-- What a scan did: the KVs it met, in order, and whether it passed E or the
last key without a stop (Java's `StopCondition.eod`). -/
structure ScanOut where
  met : List (Key × NodeId)
  eod : Bool

/-- The scan's walk with a stop rule, from the KVs met so far. -/
def scanWalk (rule : StopRule) (met : List (Key × NodeId)) : List (Key × NodeId) → ScanOut
  | [] => ⟨met, true⟩
  | kv :: rest =>
    if (rule met kv).1 then ⟨met, false⟩
    else if (rule met kv).2 then ⟨met ++ [kv], false⟩
    else scanWalk rule (met ++ [kv]) rest

/-- lastKey after a step that met the KVs `met`: the last of them; L if none. -/
def nextKey (L : Option Key) (met : List (Key × NodeId)) : Option Key :=
  match met.getLast? with
  | some kv => some kv.1
  | none => L

/-- A value node made by a transaction before c (Java: stored before pCut). -/
def oldNode (h : BHist) (c : Nat) (y : NodeId) : Bool :=
  (List.range c).any (fun i => madeAt h i y)

/-- A step: its transaction, the (j + 1)-th of the history, whose scan reads
the tree after transaction j, and the stop rule its scan followed. -/
structure IterStep where
  j : Nat
  rule : StopRule

/-- Step st's scan, at the latest state, after L and up to E. -/
def stepScan (h : BHist) (E L : Option Key) (st : IterStep) : ScanOut :=
  scanWalk st.rule [] (scanRange ((h.tree st.j).at st.j) L E)

/-- The segment interval of reclaim's reserved prefix, `/#i/dreclaim/`.
The bounds are its byte-key encoding as compare values; the upper bound
increments its last byte. This includes the prefix itself. -/
def reclaimKey (k : Key) : Bool :=
  !keyLt k [0x495ac0599d19f8, 0x195b98dadbc04030] &&
    keyLt k [0x495ac0599d19f8, 0x195b98dadbc08030]

/-- Reclaim's current row (`-current.txt` under `/#i/dreclaim/`), as compare values. -/
def reclaimRow : Key :=
  [0x495ac0599d19f8, 0x195b98dadbc04bf8, 0x195ddd1d19dc1db8, 0xc1d9e9d80000020]

theorem reclaimRow_reserved : reclaimKey reclaimRow = true := by decide

/-- The user keys for reclaim's preservation theorem: every key outside
reclaim's reserved prefix. Other internal namespaces are protected too. -/
def userKey (k : Key) : Bool := !reclaimKey k

/-- A step's record, whose scan `out` met the KVs of the state before it (bergdb
030-35; bergdb 031-06): it writes every old KV met (a copy, or an operation of the action at its key, a put
or a delete, or reclaim's row or table there), it puts its current row, and it has
one operation a key. Until bergdb 031-06 the step was a transaction of its own,
which put every old KV met again and its row and nothing else, and deleted no key
(the conjunct `StepOpOK` of every operation, now of the copies only, in
Contract/ReclaimValues.lean; with it the step's index j, which the scan's state
was, left StepTx). -/
def StepTx (h : BHist) (c : Nat) (out : ScanOut) (ops : List Op) : Prop :=
  (∀ kv ∈ out.met, oldNode h c kv.2 = true → kv.1 ∈ ops.map Op.key) ∧
  reclaimRow ∈ putKeys ops ∧ (ops.map Op.key).Nodup

/-- The steps from lastKey L on, the first after transaction `prev`: each is a
transaction of the history after the one before, each scans from the lastKey
that the one before left, and the last one's scan passed E or the last key. -/
def StepsFrom (h : BHist) (c : Nat) (E : Option Key) : Nat → Option Key → List IterStep → Prop
  | _, _, [] => True
  | prev, L, st :: rest =>
    prev ≤ st.j ∧
    (∃ hj : st.j < h.txs.length, StepTx h c (stepScan h E L st) h.txs[st.j].ops) ∧
    (rest = [] → (stepScan h E L st).eod = true) ∧
    StepsFrom h c E (st.j + 1) (nextKey L (stepScan h E L st).met) rest

/-- An iteration: its cut c, its start t0 (tStart), and its steps in order. -/
structure Iteration where
  c : Nat
  t0 : Nat
  steps : List IterStep

/-- The iteration's first step, as a transaction number (0 if none). -/
def Iteration.first (it : Iteration) : Nat :=
  match it.steps.head? with
  | some st => st.j + 1
  | none => 0

/-- The iteration's last step, as a transaction number (0 if none): tEnd. -/
def Iteration.last (it : Iteration) : Nat :=
  match it.steps.getLast? with
  | some st => st.j + 1
  | none => 0

/-- **The steps of an iteration follow the model** (bergdb 030-25; 027-13,
section 1.4): it has steps; its cut is at most t0 + 1 (pCut is at most pStart,
the stream's length after transaction t0); its steps, from lastKey none on,
the first after transaction t0, follow `StepsFrom` with E the greatest key live
after t0. -/
def StepsOK (h : BHist) (it : Iteration) : Prop :=
  it.steps ≠ [] ∧ it.c ≤ it.t0 + 1 ∧
  StepsFrom h it.c (endKey ((h.tree it.t0).at it.t0)) it.t0 none it.steps

/-! ## 2. Lemmas -/

/-- Key k is written by a transaction from a to before b (transaction j + 1
for j from a to b - 1). -/
def WrittenIn (h : BHist) (k : Key) (a b : Nat) : Prop :=
  ∃ j, ∃ hj : j < h.txs.length, a ≤ j ∧ j < b ∧ k ∈ h.txs[j].ops.map Op.key

theorem WrittenIn.mono {h : BHist} {k : Key} {a b b' : Nat} (hw : WrittenIn h k a b)
    (hb : b ≤ b') : WrittenIn h k a b' :=
  let ⟨j, hj, h1, h2, h3⟩ := hw
  ⟨j, hj, h1, by omega, h3⟩

/-- The keys a transaction puts are those of its puts. -/
theorem mem_putKeys {k : Key} {ops : List Op} : k ∈ putKeys ops ↔ ∃ v, Op.put k v ∈ ops := by
  simp only [putKeys, List.mem_filterMap]
  constructor
  · rintro ⟨op, hop, hk⟩
    cases op with
    | put k' v =>
      simp only [Option.some.injEq] at hk
      subst hk
      exact ⟨v, hop⟩
    | del k' => simp at hk
  · rintro ⟨v, hv⟩
    exact ⟨_, hv, rfl⟩

/-- The scan meets a prefix of what it walks. -/
theorem scanWalk_met (rule : StopRule) : ∀ (l met : List (Key × NodeId)),
    ∃ m, (scanWalk rule met l).met = met ++ m ∧ m <+: l
  | [], met => ⟨[], by simp [scanWalk], List.nil_prefix⟩
  | kv :: rest, met => by
    unfold scanWalk
    split_ifs with h1 h2
    · exact ⟨[], by simp, List.nil_prefix⟩
    · exact ⟨[kv], rfl, ⟨rest, rfl⟩⟩
    · obtain ⟨m, hm, hp⟩ := scanWalk_met rule rest (met ++ [kv])
      exact ⟨kv :: m, by rw [hm]; simp, List.cons_prefix_cons.mpr ⟨rfl, hp⟩⟩

/-- A scan that passed the end met every KV it walks. -/
theorem scanWalk_eod (rule : StopRule) : ∀ (l met : List (Key × NodeId)),
    (scanWalk rule met l).eod = true → (scanWalk rule met l).met = met ++ l
  | [], met, _ => by simp [scanWalk]
  | kv :: rest, met, he => by
    unfold scanWalk at he ⊢
    split_ifs at he ⊢ with h1 h2
    rw [scanWalk_eod rule rest _ he]; simp

/-- A sound tree's contents are in key order. -/
theorem contents_sorted {p : Params} {s : Tree} (h : invOk p s = true) :
    ((contents s).map Prod.fst).Pairwise (· < ·) := by
  unfold invOk at h
  unfold contents
  cases hr : s.root with
  | none => simp
  | some r =>
    simp only [hr] at h
    cases ho : s.obj r with
    | none => simp [ho] at h
    | some o =>
      simp only [ho] at h
      cases o with
      | val _ => simp at h
      | key n =>
        simp only [Bool.and_eq_true] at h
        have hg := walk_good _ _ _ _ h.2
        have hs := hg.sorted
        unfold L at hs
        exact List.pairwise_map.mpr hs

/-- What a scan walks is in key order. -/
theorem scanRange_sorted {p : Params} {s : Tree} (h : invOk p s = true) (L E : Option Key) :
    ((scanRange s L E).map Prod.fst).Pairwise (· < ·) := by
  have h1 := contents_sorted h
  rw [← idContents_keys, List.pairwise_map] at h1
  rw [List.pairwise_map]
  exact List.Pairwise.sublist (List.filter_sublist) h1

/-- In a list in key order, a KV at or before the last KV of a prefix is in the
prefix. -/
theorem mem_of_prefix_le {m l : List (Key × NodeId)} (hp : m <+: l)
    (hs : (l.map Prod.fst).Pairwise (· < ·)) {x z : Key × NodeId} (hx : x ∈ l)
    (hz : m.getLast? = some z) (hle : x.1 ≤ z.1) : x ∈ m := by
  obtain ⟨t, rfl⟩ := hp
  rcases List.mem_append.mp hx with h | h
  · exact h
  · exfalso
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hz
    rw [List.map_append, List.pairwise_append] at hs
    have := hs.2.2 z.1 (List.mem_map_of_mem (by simp)) x.1 (List.mem_map_of_mem h)
    exact absurd hle (not_le.mpr this)

/-- In a list in key order, every key is at most the last. -/
theorem le_getLast_of_mem {l : List Key} (hs : l.Pairwise (· < ·)) {x : Key} (hx : x ∈ l) :
    ∃ e, l.getLast? = some e ∧ x ≤ e := by
  have hne : l ≠ [] := List.ne_nil_of_mem hx
  obtain ⟨ys, e, rfl⟩ : ∃ ys e, l = ys ++ [e] :=
    ⟨_, _, (List.dropLast_append_getLast hne).symm⟩
  refine ⟨e, by simp, ?_⟩
  rcases List.mem_append.mp hx with h | h
  · exact le_of_lt ((List.pairwise_append.mp hs).2.2 x h e (List.mem_singleton_self _))
  · rw [List.mem_singleton.mp h]

/-- A key live in a sound tree is at most its end key. -/
theorem upTo_endKey {p : Params} {s : Tree} (hs : invOk p s = true) {k : Key} {y : NodeId}
    (hk : (idContents s).lookup k = some y) : upToKey (endKey s) k = true := by
  have hmem : k ∈ (contents s).map Prod.fst := by
    rw [← idContents_keys]
    exact List.mem_map.mpr ⟨(k, y), mem_of_lookup' hk, rfl⟩
  obtain ⟨e, he, hle⟩ := le_getLast_of_mem (contents_sorted hs) hmem
  unfold endKey
  rw [he]
  simp [upToKey, (keyLt_false_iff e k).mpr hle]

/-- A change's new node is in the model's structure after the change. -/
theorem isSome_apply_of_new {P : SIS.Struct BVal} {i : Nat} {c : SIS.Changes BVal}
    {y : NodeId} (hy : c.new.any (·.id == y) = true) : ((P.apply i c).get? y).isSome = true := by
  rw [SIS.get?_apply, Option.isSome_map]
  cases hP : P.get? y with
  | some _ => rfl
  | none =>
    simp only [Option.none_or]
    unfold SIS.newNodeOf
    simp only [SIS.Struct.get?, List.lookup_isSome_iff, List.mem_map]
    obtain ⟨nn, hnn, hid⟩ := List.any_eq_true.mp hy
    exact ⟨_, ⟨nn, hnn, rfl⟩, by simp [beq_iff_eq.mp hid]⟩

/-- A node that transaction i makes is in the model's structure after i. -/
theorem BHist.P_made {h : BHist} {i : Nat} {y : NodeId} (hi : i ≤ h.txs.length)
    (hy : madeAt h i y = true) : ((h.P i).get? y).isSome = true := by
  cases i with
  | zero =>
    change ((SIS.Struct.apply [] 0 h.c0).get? y).isSome = true
    apply isSome_apply_of_new
    simpa [madeAt, BHist.chs] using hy
  | succ j =>
    rw [h.P_succ (by omega)]
    apply isSome_apply_of_new
    have : (h.chs.getD (j + 1) { new := [], adds := [] }) = h.txs[j].c := by
      simp [BHist.chs, show j < h.txs.length by omega]
    simpa [madeAt, this] using hy

section Steps

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- **A node is made once**: no two transactions make the same node. A node
that a transaction makes is no node of the tree before it, so none of the
model's structure before it (the bridge's `fresh`), which holds every node made
before. -/
theorem MeetsFull.made_once (hm : MeetsFull p h top) {i i' : Nat} {y : NodeId} (hii : i < i')
    (hi' : i' ≤ h.txs.length) (h1 : madeAt h i y = true) (h2 : madeAt h i' y = true) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, i' = j + 1 := ⟨i' - 1, by omega⟩
  have hj : j < h.txs.length := by omega
  have hy : y ∈ h.txs[j].c.new.map (·.id) := by
    have : (h.chs.getD (j + 1) { new := [], adds := [] }) = h.txs[j].c := by
      simp [BHist.chs, hj]
    simp only [madeAt, this, List.any_eq_true, beq_iff_eq] at h2
    obtain ⟨nn, hnn, hid⟩ := h2
    exact List.mem_map.mpr ⟨nn, hnn, hid⟩
  obtain ⟨nn, hnn, hid⟩ := List.mem_map.mp hy
  have hn := (bridgeOk_parts (hm.step j hj).2.1).1
  simp only [newsOk, Bool.and_eq_true, List.all_eq_true] at hn
  have hnone : (h.tree j).obj nn.id = none := by
    have := (hn.2 nn hnn).1
    simpa using this
  have hfresh := (hm.meetsBridge.step j hj).2.2.2.1.fresh nn hnn hnone
  rw [hid] at hfresh
  obtain ⟨n, hn1⟩ := Option.isSome_iff_exists.mp (BHist.P_made (by omega) h1)
  obtain ⟨n', hn', -⟩ := h.P_isData hn1 j (by omega) (by omega)
  rw [hfresh] at hn'
  cases hn'

/-- **An old value was live at the iteration's start**: with VAL-NEW, a key that
names, after transaction a, a value node made before c ≤ t0 + 1, named it after
t0 ≤ a: a write of it after t0 would have made a new node, or deleted it. -/
theorem old_live_before (hm : MeetsFull p h top) (hv : ValNew h) {c t0 a : Nat}
    (hc : c ≤ t0 + 1) (hta : t0 ≤ a) (ha : a ≤ h.txs.length) {k : Key} {y : NodeId}
    (hy : (idContents ((h.tree a).at a)).lookup k = some y)
    (hold : ∃ i, i < c ∧ madeAt h i y = true) :
    (idContents ((h.tree t0).at t0)).lookup k = some y := by
  by_cases hex : ∃ j, t0 ≤ j ∧ j < a ∧ ∃ hj : j < h.txs.length, k ∈ h.txs[j].ops.map Op.key
  · exfalso
    obtain ⟨j, h1, h2, ⟨hj, hw⟩, h4⟩ := last_of a hex
    have hkeep := hv.keep k (a := j + 1) a (by omega) ha
      (fun j' hj' a1 a2 hw' => h4 j' (by omega) a2 ⟨hj', hw'⟩)
    by_cases hput : k ∈ putKeys h.txs[j].ops
    · obtain ⟨y', hy', hmade'⟩ := (hv j hj k).1 hput
      rw [hkeep, hy'] at hy
      injection hy with hy
      subst hy
      obtain ⟨i, hi, hmade⟩ := hold
      exact hm.made_once (i := i) (i' := j + 1) (by omega) (by omega) hmade hmade'
    · have hc' := (hm.step j hj).1.1
      simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hc'
      have hgone := applyOps_del_gone h.txs[j].ops (contents ((h.tree j).at j)) hput hw
      rw [← hc'.2, ← idContents_keys] at hgone
      rw [hkeep, lookup_none hgone] at hy
      cases hy
  · rw [← hv.keep k (a := t0) a hta ha (fun j hj a1 a2 hw => hex ⟨j, a1, a2, hj, hw⟩)]
    exact hy

/-- **One step**: a key that names an old value node after transaction a, at
most E, and written from a on, if it is at or before L, by the steps before:
after the step, it is written from a on if it is at or before the new lastKey,
and if the step was the last. -/
theorem step_covers (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hv : ValNew h) {c : Nat}
    {E L : Option Key} {st : IterStep} (hj : st.j < h.txs.length)
    (hT : StepTx h c (stepScan h E L st) h.txs[st.j].ops)
    {k : Key} {y : NodeId} {a prev : Nat} (ha : a ≤ st.j) (hprev : prev ≤ st.j + 1)
    (hy : (idContents ((h.tree a).at a)).lookup k = some y) (hold : oldNode h c y = true)
    (hE : upToKey E k = true)
    (hcov : ∀ l, L = some l → keyLt l k = false → WrittenIn h k a prev) :
    (∀ l, nextKey L (stepScan h E L st).met = some l → keyLt l k = false →
      WrittenIn h k a (st.j + 1)) ∧
    ((stepScan h E L st).eod = true → WrittenIn h k a (st.j + 1)) := by
  by_cases hw : WrittenIn h k a st.j
  · have := hw.mono (by omega : st.j ≤ st.j + 1)
    exact ⟨fun _ _ _ => this, fun _ => this⟩
  -- Not written from a on: k names y at the step's state.
  have hkeep := hv.keep k (a := a) st.j ha (by omega)
    (fun j hj' a1 a2 hw' => hw ⟨j, hj', a1, a2, hw'⟩)
  rw [hy] at hkeep
  have hmem : (k, y) ∈ idContents ((h.tree st.j).at st.j) := mem_of_lookup' hkeep
  cases hL : afterKey L k with
  | false =>
    -- At or before L: written by the steps before.
    cases L with
    | none => simp [afterKey] at hL
    | some l =>
      have := (hcov l rfl hL).mono hprev
      exact ⟨fun _ _ _ => this, fun _ => this⟩
  | true =>
    have hin : (k, y) ∈ scanRange ((h.tree st.j).at st.j) L E := by
      unfold scanRange
      exact List.mem_filter.mpr ⟨hmem, by simp [hL, hE]⟩
    -- The record writes it (bergdb 031-06: a copy, or the action's put or delete).
    have hput : (k, y) ∈ (stepScan h E L st).met → WrittenIn h k a (st.j + 1) :=
      fun hm' => ⟨st.j, hj, ha, by omega, hT.1 (k, y) hm' hold⟩
    refine ⟨fun l hl hle => ?_, fun he => ?_⟩
    · obtain ⟨m, hm1, hm2⟩ := scanWalk_met st.rule (scanRange ((h.tree st.j).at st.j) L E) []
      rw [List.nil_append] at hm1
      unfold nextKey at hl
      cases hz : (stepScan h E L st).met.getLast? with
      | none =>
        rw [hz] at hl
        subst hl
        simp [afterKey, hle] at hL
      | some z =>
        rw [hz] at hl
        injection hl with hl
        subst hl
        apply hput
        have hsort := scanRange_sorted (hm.inv_at hM st.j (by omega)) L E
        unfold stepScan at hz ⊢
        rw [hm1] at hz ⊢
        exact mem_of_prefix_le hm2 hsort hin hz ((keyLt_false_iff z.1 k).mp hle)
    · apply hput
      have := scanWalk_eod st.rule _ [] he
      unfold stepScan
      rw [this, List.nil_append]
      exact hin

/-- **The steps**: by induction, such a key is written from a on by the last
step. -/
theorem stepsFrom_covers (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hv : ValNew h) {c : Nat}
    {E : Option Key} {k : Key} {y : NodeId} {a : Nat}
    (hy : (idContents ((h.tree a).at a)).lookup k = some y) (hold : oldNode h c y = true)
    (hE : upToKey E k = true) :
    ∀ (steps : List IterStep) (prev : Nat) (L : Option Key), StepsFrom h c E prev L steps →
      (∀ st, steps.head? = some st → a ≤ st.j) →
      (∀ l, L = some l → keyLt l k = false → WrittenIn h k a prev) →
      ∀ st, steps.getLast? = some st → WrittenIn h k a (st.j + 1)
  | [], _, _, _, _, _, st, hl => by simp at hl
  | st0 :: rest, prev, L, hS, ha, hcov, st, hl => by
    obtain ⟨hp, ⟨hj, hT⟩, heod, hrest⟩ := hS
    have ha0 : a ≤ st0.j := ha st0 rfl
    obtain ⟨hA, hB⟩ := step_covers hm hM hv hj hT ha0 (by omega) hy hold hE hcov
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact hB (heod rfl)
    | cons st1 rest' =>
      have hl' : (st1 :: rest').getLast? = some st := by
        rw [← hl, List.getLast?_cons_cons]
      have h1 : st0.j + 1 ≤ st1.j := hrest.1
      refine stepsFrom_covers hm hM hv hy hold hE (st1 :: rest') (st0.j + 1) _ hrest ?_ hA st hl'
      intro st' hst'
      simp only [List.head?_cons, Option.some.injEq] at hst'
      subst hst'
      omega

/-- Each step is a transaction of the history, after `prev`. -/
theorem stepsFrom_bounds {c : Nat} {E : Option Key} : ∀ (steps : List IterStep) (prev : Nat)
    (L : Option Key), StepsFrom h c E prev L steps →
      ∀ st, steps.getLast? = some st → prev ≤ st.j ∧ st.j < h.txs.length
  | [], _, _, _, st, hl => by simp at hl
  | st0 :: rest, prev, L, hS, st, hl => by
    obtain ⟨hp, ⟨hj, -⟩, -, hrest⟩ := hS
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact ⟨hp, hj⟩
    | cons st1 rest' =>
      have hl' : (st1 :: rest').getLast? = some st := by
        rw [← hl, List.getLast?_cons_cons]
      have := stepsFrom_bounds (st1 :: rest') _ _ hrest st hl'
      exact ⟨by omega, this.2⟩

/-- The last step's transaction meets `StepTx` for some lastKey. -/
theorem stepsFrom_lastTx {c : Nat} {E : Option Key} : ∀ (steps : List IterStep) (prev : Nat)
    (L : Option Key), StepsFrom h c E prev L steps →
      ∀ st, steps.getLast? = some st →
        ∃ L', ∃ hj : st.j < h.txs.length, StepTx h c (stepScan h E L' st) h.txs[st.j].ops
  | [], _, _, _, st, hl => by simp at hl
  | st0 :: rest, prev, L, hS, st, hl => by
    obtain ⟨-, ⟨hj, hT⟩, -, hrest⟩ := hS
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact ⟨L, hj, hT⟩
    | cons st1 rest' =>
      have hl' : (st1 :: rest').getLast? = some st := by
        rw [← hl, List.getLast?_cons_cons]
      exact stepsFrom_lastTx (st1 :: rest') _ _ hrest st hl'

/-- The facts of an iteration's first and last steps that `IterationOK` needs. -/
theorem StepsOK.ends {it : Iteration} (hst : StepsOK h it) :
    ∃ st0 stl, it.first = st0.j + 1 ∧ it.last = stl.j + 1 ∧
      it.steps.head? = some st0 ∧ it.steps.getLast? = some stl ∧
      it.t0 ≤ st0.j ∧ st0.j ≤ stl.j ∧ stl.j < h.txs.length := by
  obtain ⟨hne, -, hS⟩ := hst
  obtain ⟨st0, rest, hsteps⟩ : ∃ st0 rest, it.steps = st0 :: rest := by
    cases hs : it.steps with
    | nil => exact absurd hs hne
    | cons st0 rest => exact ⟨st0, rest, rfl⟩
  obtain ⟨stl, hl⟩ : ∃ stl, (st0 :: rest).getLast? = some stl :=
    ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil st0 rest)⟩
  rw [hsteps] at hS
  have hb := stepsFrom_bounds _ _ _ hS stl hl
  have hp0 : it.t0 ≤ st0.j := hS.1
  have h0l : st0.j ≤ stl.j := by
    cases rest with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hl
      exact le_refl _
    | cons st1 rest' =>
      have hl' : (st1 :: rest').getLast? = some stl := by
        rw [← hl, List.getLast?_cons_cons]
      have := (stepsFrom_bounds (st1 :: rest') _ _ hS.2.2.2 stl hl').1
      omega
  refine ⟨st0, stl, by simp [Iteration.first, hsteps], by simp [Iteration.last, hsteps, hl],
    by rw [hsteps]; rfl, by rw [hsteps]; exact hl, hp0, h0l, hb.2⟩

/-- **The steps give the iteration** (bergdb 030-25): with VAL-NEW, a history
whose iteration's steps follow the model meets `IterationOK` from every s after
the iteration's start t0 up to its first step, to its last step: every key live
before s whose value node was made before the cut is written by a transaction
from s to the last step. -/
theorem iterationOK_of_stepsOK (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hv : ValNew h)
    {it : Iteration} (hst : StepsOK h it) {s : Nat} (hs1 : it.t0 + 1 ≤ s) (hs2 : s ≤ it.first) :
    IterationOK h it.c s it.last := by
  obtain ⟨st0, stl, hfirst, hlast, hhead, hl, hp0, h0l, hjl⟩ := hst.ends
  obtain ⟨-, hc, hS⟩ := hst
  rw [hfirst] at hs2
  rw [hlast]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  intro k y hy hold'
  have hold : oldNode h it.c y = true := by
    obtain ⟨i, hi, hmade⟩ := hold'
    exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, hmade⟩
  have h0 := old_live_before hm hv hc (by omega : it.t0 ≤ s - 1) (by omega) hy hold'
  have hE := upTo_endKey (hm.inv_at hM it.t0 (by omega)) h0
  obtain ⟨j, hj, h1, h2, h3⟩ := stepsFrom_covers hm hM hv hy hold hE it.steps it.t0 none hS
    (by
      intro st hst
      rw [hhead, Option.some.injEq] at hst
      subst hst
      omega)
    (by intro l hl'; cases hl') stl hl
  exact ⟨j, hj, by omega, by omega, h3⟩

/-- `IterationOK` from the first step to the last. -/
theorem iterationOK_steps (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hv : ValNew h)
    {it : Iteration} (hst : StepsOK h it) : IterationOK h it.c it.first it.last := by
  obtain ⟨st0, -, hfirst, -, -, -, hp0, -, -⟩ := hst.ends
  exact iterationOK_of_stepsOK hm hM hv hst (by omega) (le_refl _)

/-- **A key is live at the iteration's end**: the last step puts its row, one
operation a key. -/
theorem stepsOK_live (hm : MeetsFull p h top) {it : Iteration} (hst : StepsOK h it) :
    contents ((h.tree it.last).at it.last) ≠ [] := by
  obtain ⟨-, stl, -, hlast, -, hl, -, -, -⟩ := hst.ends
  obtain ⟨-, -, hS⟩ := hst
  obtain ⟨L', hj, -, hrow, hnd⟩ := stepsFrom_lastTx _ _ _ hS stl hl
  obtain ⟨v, hput⟩ := mem_putKeys.mp hrow
  have hc := (hm.step stl.j hj).1.1
  simp only [contractOk, Bool.and_eq_true, beq_iff_eq, Nat.add_sub_cancel] at hc
  rw [hlast, hc.2]
  have := applyOps_put h.txs[stl.j].ops (contents ((h.tree stl.j).at stl.j)) hnd hput
  exact List.ne_nil_of_mem this

end Steps

/-! ## 3. The cuts of a run, with the steps -/

/-- The cut marks of a run meet reclaim's contract with the iteration's steps:
as `CutsMeetIter`, with an iteration whose steps follow the model (`StepsOK`)
in place of `IterationOK` and of a key live at the iteration's end: at each
mark of a cut c, c is at or after every earlier mark's cut, and some iteration
with the cut c has steps that follow the model, its last step is at most the
first available time, and RC4 holds (Java's two waits). -/
def CutsMeetSteps (h : BHist) (al : SIS.Algo BVal Nat)
    (cs : List (Nat × Option Nat × List SIS.HCacheOp)) : Prop :=
  ∀ j (hjl : j < cs.length) c, cs[j].2.1 = some c →
    (∀ i (hi : i < j) c', cs[i].2.1 = some c' → c' ≤ c) ∧
    ∃ it : Iteration, it.c = c ∧ StepsOK h it ∧
      it.last ≤ SIS.lastFa (SIS.run h.spec al (h.ts.take (j + 1))).S ∧
      RC4 h.spec al h.ts it.last (j + 1)

/-- With VAL-NEW, cuts whose iterations' steps follow the model meet
`CutsMeetIter`. -/
theorem cutsMeetIter_of_steps {p : Params} {h : BHist} {top : Nat → Top}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hv : ValNew h) (al : SIS.Algo BVal Nat)
    {cs : List (Nat × Option Nat × List SIS.HCacheOp)} (hit : CutsMeetSteps h al cs) :
    CutsMeetIter h al cs := by
  intro j hjl c hc
  obtain ⟨hord, it, rfl, hst, hfa, hrc4⟩ := hit j hjl c hc
  exact ⟨hord, it.first, it.last, iterationOK_steps hm hM hv hst, stepsOK_live hm hst, hfa, hrc4⟩

/-- **Reclaim chooses only safe cuts, given VAL-NEW and the steps** (bergdb
030-25): `reclaim_java_reads` with cuts whose iterations' steps follow the
model in place of `IterationOK`. -/
theorem reclaim_java_reads_steps {p : Params} {h : BHist} {top : Nat → Top}
    {kind : Nat → Bool}
    (hm : MeetsFull p h top) (hM : 1 ≤ p.M) (hkd : KindsOK kind h) (hv : ValNew h)
    (al : SIS.Algo BVal Nat) (hj : al.stillDirty = SIS.javaTest h.spec) (hmk : al.mark = true)
    (hpol : SIS.PolicyCutOK al) (cs : List (Nat × Option Nat × List SIS.HCacheOp))
    (hcs : cs.map (·.1) = h.ts)
    (hit : CutsMeetSteps h al cs)
    (hreads : ∀ j (hjl : j < cs.length), cs[j].2.1 = none → ∀ t,
      SIS.HCacheOp.read t ∈ cs[j].2.2 →
      SIS.lastFa (SIS.run h.spec al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1)
    {t : Nat} (hft : SIS.lastFa (SIS.run h.spec al h.ts).S ≤ t) (htn : t ≤ h.txs.length)
    (mid : Bool) (s : Tree) (tp : Top) :
    let V := SIS.view h.spec (SIS.runHandlesCut h.spec al cs).1.P t
    HoldsView V (kindOf kind V) t s →
      TopFrom (SIS.lastFa (SIS.run h.spec al h.ts).S) (top h.txs.length) tp →
      JReadsRight s tp t mid (h.txs.map (·.ops)) :=
  reclaim_java_reads hm hM hkd hv al hj hmk hpol cs hcs (cutsMeetIter_of_steps hm hM hv al hit)
    hreads hft htn mid s tp

end Contract

namespace Contract.PE

variable {cf : Cfg}

/-- **Reclaim chooses only safe cuts, for PE, given the steps** (bergdb 030-25):
for every history PE writes, with Java's still-dirty test and the marking,
policies that read no cut stream, and cuts whose iterations' steps follow the
model of reclaim's steps (`StepsOK`: each step's scan, at its own time, from
the last key the step before met up to the end key, meets a prefix of the live
keys, and its record writes those whose value node was made before the cut,
by a copy or an operation of the action at the key (bergdb 031-06), and puts
its row; the last step's scan passed the end), with the last step at most the
first available time and Java's two waits, Java's get and scan after the run
with handles, evictions and restarts from the cut streams are right at every
time from the first available time on. -/
theorem pe_reclaim_reads_steps (hcf : cf.Ok) (hcap : cf.topBase ≤ 2 ^ 62) {txs : List (List Op)}
    {h : BHist} {top : Nat → Top} (hlen : txs.length < 2 ^ 48 - 1)
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top))
    (hM : 1 ≤ cf.params.M)
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
      JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  have hm := (pe_full hcf hcap hlen hk hh).1
  exact pe_reclaim_reads hcf hcap hlen hk hh hM al hj hmk hpol cs hcs
    (cutsMeetIter_of_steps hm hM (pe_valNew hcf hcap hlen hk hh) al hit) hreads hft htn mid s tp

end Contract.PE
