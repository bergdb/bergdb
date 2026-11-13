import SIS.Tree.HistoricalGet
import SIS.Tree.HistoricalPrefix
import SIS.Tree.InvInit
import SIS.Tree.RunPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! TP10 at the latest time (bergdb 024-12, TP10): `LatestGetOK` from one
transaction's step, `TxGetOK`. A get after a transaction within reach gives,
for a key of one of its operations, that operation's value, and for any other
key what a get gave at the time before. The rest is proved here: the run's
first state, the reference's fold, and that the structure before a
transaction reads at the transaction's time as at the time before. -/

/-! ## Reading after the last entry -/

theorem parseKlongEntry_times (acc : KlongParseState) (e : Entry BVal) (t : Time)
    (he : e.time ≤ t) (ha : ∀ k ∈ acc.1, ∀ s, k = .time s → s ≤ t) :
    ∀ k ∈ (parseKlongEntry acc e).1, ∀ s, k = .time s → s ≤ t := by
  have hks : ∀ k ∈ (if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]),
      ∀ s, k = .time s → s ≤ t := by
    split
    · exact ha
    · intro k hk s hs
      rcases List.mem_append.mp hk with hk | hk
      · exact ha k hk s hs
      · simp only [List.mem_singleton] at hk
        subst hk
        cases hs
        exact he
  intro k hk s hs
  unfold parseKlongEntry at hk
  generalize (if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]) = ks at hks hk
  cases hv : e.val with
  | key c y =>
    simp only [hv, List.mem_append, List.mem_singleton] at hk
    rcases hk with hk | hk
    · exact hks k hk s hs
    · subst hk; cases hs
  | del cs =>
    cases cs with
    | nil => simp only [hv] at hk; exact hks k hk s hs
    | cons c cs =>
      simp only [hv, List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | hk
      · exact hks k hk s hs
      · subst hk; cases hs
  | rootKey y => simp only [hv] at hk; exact hks k hk s hs
  | skip j z => simp only [hv] at hk; exact hks k hk s hs
  | top z => simp only [hv] at hk; exact hks k hk s hs
  | data h => simp only [hv] at hk; exact hks k hk s hs

/-- The time klongs of a history's klongs are times of its entries. -/
theorem klongsOf_times (es : History BVal) (t : Time) (he : ∀ e ∈ es, e.time ≤ t) :
    ∀ k ∈ klongsOf es, ∀ s, k = .time s → s ≤ t := by
  have hf : ∀ (qs : History BVal) (acc : KlongParseState), (∀ e ∈ qs, e.time ≤ t) →
      (∀ k ∈ acc.1, ∀ s, k = .time s → s ≤ t) →
      ∀ k ∈ (qs.foldl parseKlongEntry acc).1, ∀ s, k = .time s → s ≤ t := by
    intro qs
    induction qs with
    | nil => intro acc _ ha; exact ha
    | cons e qs ih =>
      intro acc hq ha
      rw [List.foldl_cons]
      exact ih _ (fun q h => hq q (List.mem_cons_of_mem e h))
        (parseKlongEntry_times acc e t (hq e List.mem_cons_self) ha)
  rw [klongsOf_eq_parse]
  exact hf es ([], none, []) he (by simp)

theorem prefixAt_of_times (ks : List Klong) (t : Time)
    (h : ∀ k ∈ ks, ∀ s, k = .time s → s ≤ t) : prefixAt ks t = ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    unfold prefixAt at ih ⊢
    rw [List.takeWhile_cons, ih (fun k' hk' => h k' (List.mem_cons_of_mem k hk'))]
    cases k with
    | time s => simp [h (.time s) List.mem_cons_self s rfl]
    | key c y => simp
    | del b => simp

theorem get?_mem (P : Struct BVal) (x : NodeId) (nd : Node BVal) (h : P.get? x = some nd) :
    (x, nd) ∈ P := by
  unfold Struct.get? at h
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  simp

theorem knodeOf_prefix_succ (p : Params) (P : Struct BVal) (t : Time)
    (hP : StructTimesLE P t) (x : NodeId) (n : KNode) (hn : knodeOf p (viewOf P) x = some n) :
    prefixAt n.ks (t + 1) = prefixAt n.ks t := by
  unfold knodeOf at hn
  cases hx : viewOf P x with
  | none => simp [hx] at hn
  | some nd =>
    simp only [hx] at hn
    split at hn
    · cases hn
    · cases hn
      have hmem := get?_mem P x nd hx
      have ht := klongsOf_times nd.hist t (hP _ hmem)
      simp only
      rw [prefixAt_of_times _ t ht,
        prefixAt_of_times _ (t + 1) (fun k hk s hs => Nat.le_succ_of_le (ht k hk s hs))]

theorem KNode.searchEq_prefix (n : KNode) (t u : Time) (h : prefixAt n.ks u = prefixAt n.ks t)
    (c : Nat) : n.searchEq u c = n.searchEq t c := by
  unfold KNode.searchEq
  rw [h]

theorem KNode.searchBy_prefix (n : KNode) (t u : Time) (h : prefixAt n.ks u = prefixAt n.ks t)
    (b : Nat → Option Nat → Bool) : n.searchBy u b = n.searchBy t b := by
  unfold KNode.searchBy
  rw [h]

theorem getEq_succ_of_timesLE (p : Params) (P : Struct BVal) (t : Time)
    (hP : StructTimesLE P t) (c : Nat) (f : Nat) (x : NodeId) :
    getEq p (viewOf P) (t + 1) c f x = getEq p (viewOf P) t c f x := by
  induction f generalizing x with
  | zero => rfl
  | succ f ih =>
    simp only [getEq]
    cases hn : knodeOf p (viewOf P) x with
    | none => rfl
    | some n =>
      have hpre := knodeOf_prefix_succ p P t hP x n hn
      simp only
      rw [KNode.searchEq_prefix n t (t + 1) hpre]
      unfold KNode.searchLte
      rw [KNode.searchBy_prefix n t (t + 1) hpre]
      split
      · rfl
      · split
        · rfl
        · exact ih _

theorem getFrom_succ_of_timesLE (p : Params) (P : Struct BVal) (t : Time)
    (hP : StructTimesLE P t) (key : Key) (x : NodeId) :
    getFrom p (viewOf P) (t + 1) key x = getFrom p (viewOf P) t key x := by
  induction key generalizing x with
  | nil => rfl
  | cons c rest ih =>
    cases rest with
    | nil => simp only [getFrom, getEq_succ_of_timesLE p P t hP]
    | cons d rest =>
      simp only [getFrom, getEq_succ_of_timesLE p P t hP]
      split
      · split
        · exact ih _
        · rfl
      · rfl

theorem topAt_succ_of_timesLE (P : Struct BVal) (t : Time) (hP : StructTimesLE P t) :
    topAt (viewOf P) (t + 1) = topAt (viewOf P) t := by
  unfold topAt
  cases hr : viewOf P root with
  | none => rfl
  | some r =>
    have hmem := get?_mem P root r hr
    have hall := hP _ hmem
    have h1 : r.hist.upTo (t + 1) = r.hist :=
      List.filter_eq_self.mpr (fun e he => by have := hall e he; simp; omega)
    have h2 : r.hist.upTo t = r.hist :=
      List.filter_eq_self.mpr (fun e he => by have := hall e he; simp; omega)
    simp only [h1, h2]

/-- A structure whose entries all have times at most t reads at t + 1 as at t. -/
theorem get_succ_of_timesLE (p : Params) (P : Struct BVal) (t : Time)
    (hP : StructTimesLE P t) (key : Key) :
    get p (viewOf P) (t + 1) key = get p (viewOf P) t key := by
  unfold get rootAt
  rw [topAt_succ_of_timesLE P t hP]
  cases (topAt (viewOf P) t).bind (rootKeyOf (viewOf P)) with
  | none => rfl
  | some r => exact getFrom_succ_of_timesLE p P t hP key r

/-! ## The reference's step -/

/-- The value an operation gives its key: a put's, none after a delete. -/
def Op.value : Op → Option Nat
  | .put _ h => some h
  | .del _ => none

/-- The value of a key after a transaction, by the reference: that of the
transaction's operation on the key, if it has one, else the value before. -/
def txValue (tx : Tx) (key : Key) (before : Option Nat) : Option Nat :=
  match tx.ops.find? (fun op => op.key == key) with
  | some op => op.value
  | none => before

/-- The step of TP10 for one transaction: after a transaction within reach, a
get at its time gives, for a key of one of its operations, that operation's
value (a put's, none after a delete), and for any other key what a get gave at
the time before. With it, `LatestGetOK` holds, and with TP7 then TP10 and TP11
(`getOK_of_txGet`, `scanOK_of_txGet`). This is the writer's refinement of the
map, one transaction at a time; it is not proved. -/
def TxGetOK (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → ∀ key, keyWf key = true →
    get p (viewOf (treeRun p (ts ++ [tx]))) (ts.length + 1) key =
      txValue tx key (get p (viewOf (treeRun p ts)) ts.length key)

theorem refGet_eq_fold (ts : List Tx) (t : Time) (key : Key) :
    refGet ts t key =
      ((ts.take t).flatMap (·.ops)).foldl (fun v op => if op.key == key then op.value else v) none := by
  unfold refGet
  congr

theorem fold_value_none (key : Key) (ops : List Op) (v : Option Nat)
    (h : ∀ op ∈ ops, op.key ≠ key) :
    ops.foldl (fun v op => if op.key == key then op.value else v) v = v := by
  induction ops generalizing v with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldl_cons]
    have hk : (op.key == key) = false := by simpa using h op List.mem_cons_self
    simp only [hk, Bool.false_eq_true, ↓reduceIte]
    exact ih v (fun o ho => h o (List.mem_cons_of_mem op ho))

theorem fold_value_find (key : Key) (ops : List Op) (hnd : (ops.map (·.key)).Nodup)
    (v : Option Nat) :
    ops.foldl (fun v op => if op.key == key then op.value else v) v =
      match ops.find? (fun op => op.key == key) with
      | some op => op.value
      | none => v := by
  induction ops generalizing v with
  | nil => rfl
  | cons op ops ih =>
    rw [List.foldl_cons, List.find?_cons]
    have hnd' := List.nodup_cons.mp (by simpa only [List.map_cons] using hnd)
    by_cases hk : op.key = key
    · have hk' : (op.key == key) = true := by simpa using hk
      simp only [hk', ↓reduceIte]
      apply fold_value_none
      intro o ho he
      apply hnd'.1
      rw [hk, ← he]
      exact List.mem_map_of_mem ho
    · have hk' : (op.key == key) = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      exact ih hnd'.2 v

theorem refGet_snoc_latest (ts : List Tx) (tx : Tx) (hs : tx.sorted = true) (key : Key) :
    refGet (ts ++ [tx]) (ts.length + 1) key = txValue tx key (refGet ts ts.length key) := by
  have hl : (ts ++ [tx]).take (ts.length + 1) = ts ++ [tx] := by
    apply List.take_of_length_le
    simp
  rw [refGet_eq_fold, refGet_eq_fold, hl, List.take_length, List.flatMap_append,
    List.foldl_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [fold_value_find key tx.ops (Tx.keys_nodup tx hs)]
  rfl

/-! ## TP10 at the latest time -/

/-- `LatestGetOK` from one transaction's step: the run's first state has no
key, and a structure before a transaction reads at its time as at the time
before. TP7 is not used. -/
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
      have hs : tx.sorted = true := (hw.1 tx (by simp)).1
      have hlen : (ts' ++ [tx]).length = ts'.length + 1 := by simp
      rw [hlen, htx ts' tx hw key hkey, ih ts' hl' hw' key hkey, refGet_snoc_latest ts' tx hs]

/-- TP10 from TP7 and one transaction's step. -/
theorem getOK_of_txGet (p : Params) (hinv : InvPreserved p) (htx : TxGetOK p) : GetOK p :=
  getOK_of_latest p hinv (latestGetOK_of_txGet p htx)

end SIS.Tree
