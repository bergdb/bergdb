/-
The tree model (bergdb 024-12, TP2): the leftmost rule at every time, from
TP4. Three invariants of the structure, kept by every transaction without a
walk through the writer: an inner key node has the empty key live at every
time it has klongs (`HistLeftOK`); a key node that an entry names has an
entry at or before that entry's time (`CreationOK`); the root key entry of a
top node is no later than the root's entry that names the top node
(`TopTimeOK`). With them every key node reachable at t has klongs at t, so
its smallest live klong at t is the empty key's (`leftmostOK_all`).
-/
import SIS.Tree.LeftRun
import SIS.Tree.HistoricalRead
import SIS.Tree.KlongHistoryTime
import SIS.Tree.WalkComplete
import SIS.Tree.ExportLedger
import SIS.Tree.AllocationIds
import SIS.Proof.CutAgree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## 1. The invariants -/

/-- Every inner key node has the empty key live at every time it has klongs. -/
def HistLeftOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    p.heightOf nd.level ≠ 0 → ∀ t, prefixAt (klongsOf nd.hist) t ≠ [] →
      Live0 ⟨false, prefixAt (klongsOf nd.hist) t⟩

/-- A key node that an entry names has an entry no later than that entry. -/
def CreationOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → ∀ e ∈ nd.hist, ∀ y ∈ bptrs e.val, ∀ ny, P.get? y = some ny →
    ny.isData = false → ny.level ≤ p.keyMax → ∃ e' ∈ ny.hist, e'.time ≤ e.time

/-- The root key entries of a top node are no later than an entry that names
the top node. -/
def TopTimeOK (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → ∀ e ∈ nd.hist, ∀ z, e.val = .top z → ∀ nz, P.get? z = some nz →
    ∀ e2 ∈ nz.hist, ∀ y, e2.val = .rootKey y → e2.time ≤ e.time

/-! ## 2. Histories in time order -/

/-- The klongs at t of a history in time order are those of its entries up
to t. -/
theorem leftHist_prefix_eq (h : History BVal) (hs : h.Pairwise (fun e f => e.time ≤ f.time))
    (t : Time) :
    prefixAt (klongsOf h) t = klongsOf (h.takeWhile (fun e => decide (e.time ≤ t))) := by
  have hsplit := List.takeWhile_append_dropWhile (p := fun e : Entry BVal => decide (e.time ≤ t))
    (l := h)
  have hd : ∀ e ∈ h.dropWhile (fun e => decide (e.time ≤ t)), t < e.time := by
    have hsd : (h.dropWhile (fun e => decide (e.time ≤ t))).Pairwise
        (fun e f => e.time ≤ f.time) := by
      rw [← hsplit] at hs
      exact (List.pairwise_append.mp hs).2.1
    generalize hdw : h.dropWhile (fun e => decide (e.time ≤ t)) = dw at hsd
    cases dw with
    | nil => intro e he; cases he
    | cons a r =>
      have ha : (fun e : Entry BVal => decide (e.time ≤ t)) a = false := by
        have := List.head_dropWhile_not (fun e : Entry BVal => decide (e.time ≤ t)) (l := h)
          (by rw [hdw]; simp)
        simp only [hdw, List.head_cons] at this
        simpa using this
      simp only [decide_eq_false_iff_not, Nat.not_le] at ha
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ha
      · have := (List.pairwise_cons.mp hsd).1 e he
        omega
  conv => lhs; rw [← hsplit]
  rw [klongsOf_prefixAt_append_future _ _ t hd]
  apply prefixAt_eq_self
  intro u hu
  obtain ⟨e, he, het⟩ := klongsOf_time_mem _ u hu
  have := mem_takeWhile_pred _ _ e he
  simp only [decide_eq_true_eq] at this
  omega

/-- The history of a key node of a structure with `KeyHistOK` is in time
order. -/
theorem leftHist_sorted (p : Params) (P : Struct BVal) (hH : KeyHistOK p P) (x : NodeId)
    (nd : Node BVal) (hx : P.get? x = some nd) (hd : nd.isData = false)
    (hlv : nd.level ≤ p.keyMax) : nd.hist.Pairwise (fun e f => e.time ≤ f.time) := by
  obtain ⟨hwf, hent⟩ := hH x nd hx hd hlv
  have := (entriesOf_time_order _ hwf).1
  rwa [hent] at this

/-- A key klong at t of a history in time order is a key entry at or before
t. -/
theorem leftHist_key_time (h : History BVal) (hs : h.Pairwise (fun e f => e.time ≤ f.time))
    (t : Time) (c : Nat) (y : NodeId) (hk : Klong.key c y ∈ prefixAt (klongsOf h) t) :
    ∃ e ∈ h, e.val = .key c y ∧ e.time ≤ t := by
  rw [leftHist_prefix_eq h hs t] at hk
  obtain ⟨e, he, hv⟩ := klongsOf_key_mem _ c y hk
  have := mem_takeWhile_pred _ _ e he
  simp only [decide_eq_true_eq] at this
  exact ⟨e, (List.takeWhile_sublist _).subset he, hv, this⟩

/-- A history in time order with an entry at or before t has klongs at t. -/
theorem leftHist_prefix_ne (h : History BVal) (hs : h.Pairwise (fun e f => e.time ≤ f.time))
    (t : Time) (he : ∃ e ∈ h, e.time ≤ t) : prefixAt (klongsOf h) t ≠ [] := by
  rw [leftHist_prefix_eq h hs t]
  apply klongsOf_ne_nil
  intro hnil
  obtain ⟨e, he, het⟩ := he
  have hsplit := List.takeWhile_append_dropWhile (p := fun e : Entry BVal => decide (e.time ≤ t))
    (l := h)
  rw [hnil, List.nil_append] at hsplit
  rw [← hsplit] at he
  cases hdw : h.dropWhile (fun e => decide (e.time ≤ t)) with
  | nil => rw [hdw] at he; cases he
  | cons a r =>
    have ha := List.head_dropWhile_not (fun e : Entry BVal => decide (e.time ≤ t)) (l := h)
      (by rw [hdw]; simp)
    simp only [hdw, List.head_cons, decide_eq_false_iff_not, Nat.not_le] at ha
    rw [hdw] at he hsplit
    have hs' : (a :: r).Pairwise (fun e f => e.time ≤ f.time) := by rw [hsplit]; exact hs
    rcases List.mem_cons.mp he with rfl | he
    · omega
    · have := (List.pairwise_cons.mp hs').1 e he
      omega

/-- No klongs of an empty history. -/
theorem leftHist_klongsOf_nil : klongsOf ([] : History BVal) = [] := rfl

/-! ## 3. A node after a transaction -/

/-- A node after the changes at time i: a node of P with entries added, or a
new one whose entries are all added. -/
theorem leftHist_apply_cases (P : Struct BVal) (i : Time) (c : Changes BVal) (x : NodeId)
    (nd' : Node BVal) (hx : (P.apply i c).get? x = some nd') :
    (∃ nd, P.get? x = some nd ∧ nd' = { nd with hist := nd.hist ++ addsFor c i x }) ∨
      (P.get? x = none ∧ nd'.hist = addsFor c i x) := by
  obtain ⟨n0, hn0, hnd⟩ := get?_apply_some hx
  cases hp : P.get? x with
  | some nd =>
    rw [hp] at hn0
    have h0 : nd = n0 := by simpa using hn0
    subst h0
    exact Or.inl ⟨nd, rfl, hnd⟩
  | none =>
    rw [hp] at hn0
    have hn0' : newNodeOf c x = some n0 := by simpa using hn0
    refine Or.inr ⟨rfl, ?_⟩
    rw [hnd]
    simp [newNodeOf_hist hn0']

/-- An entry of a node after the changes at time i: an entry of the node in P,
or one of time i that the changes add. -/
theorem leftHist_entry_cases (P : Struct BVal) (i : Time) (c : Changes BVal) (x : NodeId)
    (nd' : Node BVal) (hx : (P.apply i c).get? x = some nd') (e : Entry BVal) (he : e ∈ nd'.hist) :
    (∃ nd, P.get? x = some nd ∧ e ∈ nd.hist) ∨ (e.time = i ∧ (x, e.val) ∈ c.adds) := by
  rcases leftHist_apply_cases P i c x nd' hx with ⟨nd, hp, rfl⟩ | ⟨_, hh⟩
  · rcases List.mem_append.mp he with he | he
    · exact Or.inl ⟨nd, hp, he⟩
    · exact Or.inr (mem_addsFor.mp he)
  · rw [hh] at he
    exact Or.inr (mem_addsFor.mp he)

/-- A node of P keeps its level, its kind and its entries after the changes. -/
theorem leftHist_old_node (P : Struct BVal) (i : Time) (c : Changes BVal) (y : NodeId)
    (ny ny' : Node BVal) (hy : P.get? y = some ny) (hy' : (P.apply i c).get? y = some ny') :
    ny'.level = ny.level ∧ ny'.isData = ny.isData ∧ ∀ e ∈ ny.hist, e ∈ ny'.hist := by
  rw [get?_apply_of_get? hy] at hy'
  cases hy'
  exact ⟨rfl, rfl, fun e he => List.mem_append_left _ he⟩

/-! ## 4. The leftmost rule at every time -/

/-- At a time with no later entry, `LeftAllOK` gives the empty key live in
the klongs at that time. -/
theorem leftHist_of_leftAll (p : Params) (P : Struct BVal) (i : Time) (hA : LeftAllOK p P)
    (hT : StructTimesLE P i) (x : NodeId) (nd : Node BVal) (hx : P.get? x = some nd)
    (hd : nd.isData = false) (hlv : nd.level ≤ p.keyMax) (hh : p.heightOf nd.level ≠ 0)
    (t : Time) (ht : i ≤ t) : Live0 ⟨false, prefixAt (klongsOf nd.hist) t⟩ := by
  have hpre : prefixAt (klongsOf nd.hist) t = klongsOf nd.hist := by
    apply prefixAt_eq_self
    intro u hu
    obtain ⟨e, he, het⟩ := klongsOf_time_mem _ u hu
    have := hT _ (mem_of_get? hx) e he
    omega
  rw [hpre]
  have hleaf : (p.heightOf nd.level == 0) = false := by simpa using hh
  have hn := (hA x nd hx hd hlv) hleaf
  rw [hleaf] at hn
  exact hn.2

/-- The structure at the start. -/
theorem leftHist_init (p : Params) : HistLeftOK p (initStruct p) := by
  intro x nd hx hd hlv hh t _
  have hT : StructTimesLE (initStruct p) 0 := by
    have := treeRun_timesLE p []
    simpa [treeRun] using this
  exact leftHist_of_leftAll p _ 0 (leftAllOK_init p) hT x nd hx hd hlv hh t (Nat.zero_le _)

/-- A transaction at time i keeps `HistLeftOK`: before i a node's klongs are
those of P (a new node has none), from i on they are all its klongs, which
`LeftAllOK` of the structure after covers. -/
theorem leftHist_step (p : Params) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (hL : HistLeftOK p P) (hA : LeftAllOK p (P.apply i c)) (hT : StructTimesLE (P.apply i c) i) :
    HistLeftOK p (P.apply i c) := by
  intro x nd' hx hd hlv hh t hne
  by_cases ht : i ≤ t
  · exact leftHist_of_leftAll p _ i hA hT x nd' hx hd hlv hh t ht
  · have ht' : t < i := by omega
    rcases leftHist_apply_cases P i c x nd' hx with ⟨nd, hp, rfl⟩ | ⟨_, hh'⟩
    · simp only at hne hd hlv hh ⊢
      rw [klongsOf_prefixAt_append_future _ _ t (addsFor_future c i t x ht')] at hne ⊢
      exact hL x nd hp hd hlv hh t hne
    · exfalso
      apply hne
      rw [hh', ← List.nil_append (addsFor c i x),
        klongsOf_prefixAt_append_future _ _ t (addsFor_future c i t x ht'), leftHist_klongsOf_nil]
      rfl

/-! ## 5. Key nodes as old as the entries that name them -/

/-- The structure at the start: every key node has an entry, all of time 0. -/
theorem leftHist_creation_of_times (p : Params) (P : Struct BVal) (hN : KeyNonempty p P)
    (hT : StructTimesLE P 0) : CreationOK p P := by
  intro x nd hx e he y hy ny hny hd hlv
  have hne := hN y ny hny hd hlv
  obtain ⟨e', hm⟩ := List.exists_mem_of_ne_nil ny.hist hne
  refine ⟨e', hm, ?_⟩
  have := hT _ (mem_of_get? hny) e' hm
  omega

/-- A transaction at time i keeps `CreationOK`: an old entry names a node of
P (TP4), which keeps its entries; a new entry has time i, and the key node it
names has an entry, of time at most i. -/
theorem leftHist_creation_step (p : Params) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (hC : CreationOK p P) (hP : PointersOK P) (hN : KeyNonempty p (P.apply i c))
    (hT : StructTimesLE (P.apply i c) i) : CreationOK p (P.apply i c) := by
  intro x nd' hx e he y hy ny' hny' hd hlv
  rcases leftHist_entry_cases P i c x nd' hx e he with ⟨nd, hp, heo⟩ | ⟨hei, _⟩
  · have hs := hP _ (mem_of_get? hp) e heo y hy
    obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨hl, hk, hsub⟩ := leftHist_old_node P i c y ny ny' hny hny'
    obtain ⟨e', hm, het⟩ := hC x nd hp e heo y hy ny hny (by rw [← hk]; exact hd)
      (by rw [← hl]; exact hlv)
    exact ⟨e', hsub e' hm, het⟩
  · have hne := hN y ny' hny' hd hlv
    obtain ⟨e', hm⟩ := List.exists_mem_of_ne_nil ny'.hist hne
    refine ⟨e', hm, ?_⟩
    have := hT _ (mem_of_get? hny') e' hm
    omega

/-! ## 6. Top nodes no later than the root's entries -/

/-- The structure at the start: all entries of time 0. -/
theorem leftHist_topTime_of_times (P : Struct BVal) (hT : StructTimesLE P 0) : TopTimeOK P := by
  intro x nd hx e he z hz nz hnz e2 he2 y hy
  have := hT _ (mem_of_get? hnz) e2 he2
  omega

/-- A transaction at time i that adds root key entries only to new nodes keeps
`TopTimeOK`: an entry of time i is no earlier than any entry; an old entry
names an old top node, whose root key entries are old. -/
theorem leftHist_topTime_step (P : Struct BVal) (i : Time) (c : Changes BVal)
    (hTT : TopTimeOK P) (hP : PointersOK P) (hT : StructTimesLE (P.apply i c) i)
    (hnew : ∀ z y, (z, BVal.rootKey y) ∈ c.adds → P.get? z = none) :
    TopTimeOK (P.apply i c) := by
  intro x nd' hx e he z hz nz' hnz' e2 he2 y hy
  rcases leftHist_entry_cases P i c x nd' hx e he with ⟨nd, hp, heo⟩ | ⟨hei, _⟩
  · have hs := hP _ (mem_of_get? hp) e heo z (by rw [hz]; simp [bptrs])
    obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp hs
    rcases leftHist_entry_cases P i c z nz' hnz' e2 he2 with ⟨nz0, hp0, he20⟩ | ⟨_, hadd⟩
    · rw [hnz] at hp0
      cases hp0
      exact hTT x nd hp e heo z hz nz hnz e2 he20 y hy
    · rw [hy] at hadd
      have := hnew z y hadd
      rw [hnz] at this
      cases this
  · have := hT _ (mem_of_get? hnz') e2 he2
    omega

/-- A transaction adds a root key entry only to its own new top node, which
is not a node of P. -/
theorem leftHist_rootKey_new (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool)
    (w : W) (he : execW p tx i v = .ok (bs, w)) (P : Struct BVal)
    (hfresh : ∀ q ∈ P, q.1 < tx.base) :
    ∀ z y, (z, BVal.rootKey y) ∈ (changesOf i w).adds → P.get? z = none := by
  intro z y hm
  rw [changesOf_adds, List.mem_mergeSort] at hm
  have hz : z = w.top.id ∧ w.newTop = true := by
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_append.mp hm with hm | hm
      · exfalso
        unfold keyAdditions at hm
        obtain ⟨q, _, hq⟩ := List.mem_flatMap.mp hm
        obtain ⟨e, he, hqe⟩ := List.mem_map.mp hq
        have hv : e.val = .rootKey y := (Prod.mk.inj hqe).2
        have hk := entriesOf_values q.2.ks e (List.mem_filter.mp he).1
        rw [hv] at hk
        exact hk
      · exfalso
        unfold valueAdditions at hm
        obtain ⟨q, _, hq⟩ := List.mem_map.mp hm
        cases (Prod.mk.inj hq).2
    · unfold topAdditions at hm
      cases hnt : w.newTop with
      | false => rw [hnt] at hm; simp at hm
      | true =>
        rw [hnt] at hm
        simp only [↓reduceIte, List.mem_cons, Prod.mk.injEq, reduceCtorEq, and_false,
          false_or, BVal.rootKey.injEq, List.mem_map] at hm
        rcases hm with ⟨h1, _⟩ | ⟨_, hf⟩
        · exact ⟨h1, rfl⟩
        · exact hf.elim
  obtain ⟨hz, hnt⟩ := hz
  obtain ⟨lvl, _, hmade⟩ := (execW_ledger p tx i v bs w he).2.2 hnt
  have hge := ((execW_allocatedIds p tx i v bs w he).2.2 _ hmade).1
  apply get?_none_of_ge P tx.base z hfresh
  rw [hz]
  exact hge

/-! ## 7. After every run within reach -/

/-- The three invariants after every run within reach, under valid
parameters, from TP4. -/
theorem leftHist_run (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    HistLeftOK p (treeRun p ts) ∧ CreationOK p (treeRun p ts) ∧ TopTimeOK (treeRun p ts) := by
  have hM := mergeParamsOK_M p hp
  have hk : ∀ n, n ≤ ts.length →
      HistLeftOK p (treeRun p (ts.take n)) ∧ CreationOK p (treeRun p (ts.take n)) ∧
        TopTimeOK (treeRun p (ts.take n)) := by
    intro n
    induction n with
    | zero =>
      intro _
      have h0 : treeRun p (ts.take 0) = initStruct p := by simp [treeRun]
      have hT : StructTimesLE (initStruct p) 0 := by
        have := treeRun_timesLE p []
        simpa [treeRun] using this
      rw [h0]
      exact ⟨leftHist_init p,
        leftHist_creation_of_times p _ (runLinksOK_init p).2.2 hT,
        leftHist_topTime_of_times _ hT⟩
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      obtain ⟨ihL, ihC, ihT⟩ := ih (by omega)
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.2 n hlt).1
      have hrun : runOps p ts[n].base ts[n].ops ((ts.take n).length + 1)
          (view (treeSpec p) (treeRun p (ts.take n)) (ts.take n).length) = .ok (bs, w) := he0
      have hA := treeRun_leftAllOK p hp hP _ hwn
      have hN := (runLinksOK_of_pointers p (by omega) hP _ hwn).2.2
      have hT := treeRun_timesLE p (ts.take n ++ [ts[n]])
      have hlen : (ts.take n ++ [ts[n]]).length = (ts.take n).length + 1 := by
        simp only [List.length_append, List.length_singleton]
      rw [hlen] at hT
      have hP0 := hP _ (within_take p ts hw n)
      rw [treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun] at hA hN hT
      rw [htake, treeRun_snoc_changes p (ts.take n) ts[n] bs w hrun]
      exact ⟨leftHist_step p _ _ _ ihL hA hT,
        leftHist_creation_step p _ _ _ ihC hP0 hN hT,
        leftHist_topTime_step _ _ _ ihT hP0 hT
          (leftHist_rootKey_new p ts[n] _ _ bs w he0 _ hfresh)⟩
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-! ## 8. Every node reachable at t has klongs at t -/

/-- Key node y has an entry at or before t. -/
def leftHist_Born (p : Params) (P : Struct BVal) (t : Time) (y : NodeId) : Prop :=
  ∀ ny, P.get? y = some ny → ny.isData = false → ny.level ≤ p.keyMax → ∃ e ∈ ny.hist, e.time ≤ t

/-- The time klongs at t are at most t. -/
theorem leftHist_prefix_times (ks : List Klong) (t u : Time) (hu : Klong.time u ∈ prefixAt ks t) :
    u ≤ t := by
  unfold prefixAt at hu
  have := mem_takeWhile_pred _ _ _ hu
  simpa using this

/-- The live klongs at t of a node are those of its klongs at t. -/
theorem leftHist_liveAt_prefix (n : KNode) (t : Time) :
    n.liveAt t = (⟨n.leaf, prefixAt n.ks t⟩ : KNode).liveAt t :=
  KNode.liveAt_eq_of_prefix _ _ t (prefixAt_idem n.ks t).symm

/-- A child of a key node through a klong live at t is born by t. -/
theorem leftHist_born_child (p : Params) (P : Struct BVal) (t : Time) (hH : KeyHistOK p P)
    (hC : CreationOK p P) (x : NodeId) (nd : Node BVal) (hx : P.get? x = some nd)
    (hd : nd.isData = false) (hlv : nd.level ≤ p.keyMax) (leaf : Bool) (c : Nat) (y : NodeId)
    (hm : (c, y) ∈ (⟨leaf, klongsOf nd.hist⟩ : KNode).liveAt t) : leftHist_Born p P t y := by
  rw [leftHist_liveAt_prefix] at hm
  have hk := KNode.liveAt_key_mem _ t c y hm
  obtain ⟨e, he, hv, het⟩ := leftHist_key_time _ (leftHist_sorted p P hH x nd hx hd hlv) t c y hk
  intro ny hny hdy hly
  obtain ⟨e', hm', het'⟩ := hC x nd hx e he y (by rw [hv]; simp [bptrs]) ny hny hdy hly
  exact ⟨e', hm', by omega⟩

/-- Every node that the walk at t reaches from a node born by t is born by
t. -/
theorem leftHist_born_nodesAt (p : Params) (P : Struct BVal) (t : Time) (hH : KeyHistOK p P)
    (hC : CreationOK p P) (f : Nat) :
    ∀ x0 x, leftHist_Born p P t x0 → x ∈ nodesAt p (viewOf P) t f x0 → leftHist_Born p P t x := by
  induction f with
  | zero => intro x0 x _ hx; simp [nodesAt] at hx
  | succ f ih =>
    intro x0 x hb hx
    unfold nodesAt at hx
    cases hk : knodeOf p (viewOf P) x0 with
    | none => rw [hk] at hx; cases hx
    | some n =>
      rw [hk] at hx
      simp only [List.mem_cons, List.mem_flatMap] at hx
      rcases hx with rfl | ⟨⟨c, y⟩, hm, hxy⟩
      · exact hb
      · unfold knodeOf viewOf at hk
        cases hx0 : P.get? x0 with
        | none => rw [hx0] at hk; cases hk
        | some nd =>
          rw [hx0] at hk
          by_cases hc : (nd.isData || decide (p.keyMax < nd.level)) = true
          · simp only [hc, ↓reduceIte] at hk; cases hk
          · simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hk
            simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Bool.not_eq_true] at hc
            subst hk
            have hby := leftHist_born_child p P t hH hC x0 nd hx0 hc.1 (by omega) _ c y hm
            split at hxy
            · cases hxy
            · exact ih y x hby hxy

/-- The space root at t is born by t. -/
theorem leftHist_born_root (p : Params) (P : Struct BVal) (t : Time) (hC : CreationOK p P)
    (hTT : TopTimeOK P) (r : NodeId) (h : rootAt (viewOf P) t = some r) :
    leftHist_Born p P t r := by
  unfold rootAt at h
  cases htop : topAt (viewOf P) t with
  | none => rw [htop] at h; cases h
  | some z =>
    rw [htop] at h
    simp only [Option.bind_some] at h
    unfold topAt viewOf at htop
    cases hr : P.get? root with
    | none => rw [hr] at htop; cases htop
    | some rn =>
      rw [hr] at htop
      simp only at htop
      cases hl : (rn.hist.upTo t).getLast? with
      | none => rw [hl] at htop; cases htop
      | some e =>
        rw [hl] at htop
        obtain ⟨te, v⟩ := e
        have hmem := List.mem_of_getLast? hl
        unfold History.upTo at hmem
        obtain ⟨he, hte⟩ := List.mem_filter.mp hmem
        simp only [decide_eq_true_eq] at hte
        cases v with
        | top z0 =>
          simp only [Option.some.injEq] at htop
          subst htop
          unfold rootKeyOf viewOf at h
          cases hz : P.get? z0 with
          | none => rw [hz] at h; cases h
          | some nz =>
            rw [hz] at h
            simp only [Option.bind_some] at h
            obtain ⟨e2, he2, hf⟩ := List.exists_of_findSome?_eq_some h
            have hv : e2.val = .rootKey r := by
              revert hf
              cases e2.val <;> simp
            have h2 := hTT root rn hr _ he z0 rfl nz hz e2 he2 r hv
            intro ny hny hdy hly
            obtain ⟨e', hm', het'⟩ := hC z0 nz hz e2 he2 r (by rw [hv]; simp [bptrs]) ny hny
              hdy hly
            exact ⟨e', hm', by simp only at h2 hte; omega⟩
        | _ => simp at htop

/-! ## 9. TP2 at every time -/

/-- TP2 at every time, from the three invariants and klongs that give the
histories. -/
theorem leftHist_leftmostOK (p : Params) (P : Struct BVal) (t : Time) (hH : KeyHistOK p P)
    (hL : HistLeftOK p P) (hC : CreationOK p P) (hTT : TopTimeOK P) : LeftmostOK p P t := by
  intro x hx n hn hleaf
  unfold keyNodesAt at hx
  cases hr : rootAt (viewOf P) t with
  | none => rw [hr] at hx; cases hx
  | some r =>
    rw [hr] at hx
    have hb := leftHist_born_nodesAt p P t hH hC p.fuel r x
      (leftHist_born_root p P t hC hTT r hr) hx
    unfold keyNodeAt at hn
    cases hxp : P.get? x with
    | none => rw [hxp] at hn; cases hn
    | some nd =>
      rw [hxp] at hn
      by_cases hc : (!nd.isData && decide (nd.level ≤ p.keyMax)) = true
      · simp only [hc, ↓reduceIte, Option.some.injEq] at hn
        subst hn
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
        obtain ⟨hd, hlv⟩ := hc
        have hh : p.heightOf nd.level ≠ 0 := by
          intro h0
          simp [h0] at hleaf
        have hne := leftHist_prefix_ne _ (leftHist_sorted p P hH x nd hxp hd hlv) t
          (hb nd hxp hd hlv)
        have hlive := hL x nd hxp hd hlv hh t hne
        rw [leftHist_liveAt_prefix]
        simp only at hleaf ⊢
        rw [hleaf]
        exact Live0.liveAt_head _ t hlive (leftHist_prefix_times _ t)
      · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hn

/-- TP2 at every time of a run within reach, under valid parameters, from
TP4. -/
theorem leftmostOK_all (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts)) (ts : List Tx) (hw : Within p ts)
    (t : Time) (_ht : t ≤ ts.length) : LeftmostOK p (treeRun p ts) t := by
  obtain ⟨hL, hC, hTT⟩ := leftHist_run p hp hP ts hw
  exact leftHist_leftmostOK p _ t
    (runLinksOK_of_pointers p (by have := mergeParamsOK_M p hp; omega) hP ts hw).2.1 hL hC hTT

end SIS.Tree
