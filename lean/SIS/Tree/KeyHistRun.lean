/-
The tree model (bergdb 024-12, TP7): the klongs of every key node after a
run. With the bridge of SIS/Tree/ApplyBridge.lean, a transaction keeps the
klongs of every key node well formed and giving its history
(`keyHistOK_step`), so a run within reach does (`treeRun_keyHistOK`), if after
each of its earlier transactions the pointers of P name nodes of P (TP4) and
every key node has a history.

TP7 then follows from statements that have no klong well-formedness left in
them (`invPreserved_of_parts`): the invariants at each run's last time, TP4,
TP5, a history for every key node, and the bound on dead klongs.
-/
import SIS.Tree.ApplyBridge
import SIS.Tree.InvLatest
import SIS.Tree.RunPotential

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Key klongs and entries -/

theorem parseKlongEntry_key_mem (acc : KlongParseState) (e : Entry BVal) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ (parseKlongEntry acc e).1) :
    Klong.key c y ∈ acc.1 ∨ e.val = .key c y := by
  have hks : Klong.key c y ∈ (if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]) →
      Klong.key c y ∈ acc.1 := by
    intro hm
    split at hm
    · exact hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact hm
      · simp at hm
  unfold parseKlongEntry at h
  dsimp only at h
  split at h
  · rename_i c' y' hv
    rcases List.mem_append.mp h with h | h
    · exact Or.inl (hks h)
    · simp only [List.mem_singleton, Klong.key.injEq] at h
      rw [hv, h.1, h.2]
      exact Or.inr rfl
  · exact Or.inl (hks h)
  · rcases List.mem_append.mp h with h | h
    · exact Or.inl (hks h)
    · simp at h
  · exact Or.inl (hks h)

/-- A key klong of a history's klongs is a key entry of the history. -/
theorem klongsOf_key_mem (es : History BVal) (c : Nat) (y : NodeId)
    (h : Klong.key c y ∈ klongsOf es) : ∃ e ∈ es, e.val = .key c y := by
  have hf : ∀ (qs : History BVal) (acc : KlongParseState),
      Klong.key c y ∈ (qs.foldl parseKlongEntry acc).1 →
        Klong.key c y ∈ acc.1 ∨ ∃ e ∈ qs, e.val = .key c y := by
    intro qs
    induction qs with
    | nil => intro acc h; exact Or.inl h
    | cons e qs ih =>
      intro acc h
      rcases ih _ h with h | ⟨e', he', ht⟩
      · rcases parseKlongEntry_key_mem acc e c y h with h | h
        · exact Or.inl h
        · exact Or.inr ⟨e, List.mem_cons_self, h⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', ht⟩
  rw [klongsOf_eq_parse] at h
  rcases hf es _ h with h | h
  · cases h
  · exact h

/-- A history has klongs. -/
theorem klongsOf_ne_nil (es : History BVal) (h : es ≠ []) : klongsOf es ≠ [] := by
  cases es with
  | nil => exact (h rfl).elim
  | cons e es =>
    rw [klongsOf_eq_parse]
    unfold parseKlongEntries
    simp only [List.foldl_cons]
    obtain ⟨t, r, h1⟩ := parseKlongEntry_head ([], none, []) e (Or.inl ⟨rfl, rfl⟩)
    have hf : ∀ (qs : History BVal) (acc : KlongParseState), (∃ t r, acc.1 = .time t :: r) →
        ∃ t r, (qs.foldl parseKlongEntry acc).1 = .time t :: r := by
      intro qs
      induction qs with
      | nil => intro acc h; exact h
      | cons e qs ih => intro acc h; exact ih _ (parseKlongEntry_head acc e (Or.inr h))
    obtain ⟨t', r', h2⟩ := hf es _ ⟨t, r, h1⟩
    rw [h2]
    intro hc
    cases hc

/-! ## The premises from invariants of P -/

/-- Every key node of P has a history. -/
def KeyNonempty (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax → nd.hist ≠ []

/-- The links of the writer's view, from TP4 and a history for every key
node. -/
theorem viewLinksOK_of (p : Params) (P : Struct BVal) (t : Time) (B : NodeId)
    (hfresh : ∀ q ∈ P, q.1 < B) (htimes : StructTimesLE P t) (hP : PointersOK P)
    (hN : KeyNonempty p P) : ViewLinksOK B p (view (treeSpec p) P t) := by
  constructor
  · intro x nd hx cv y hk
    have hg := view_eq_get? p P t htimes x nd hx
    obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist cv y hk
    have hy := hP _ (mem_of_get? hg) e he y (by rw [hv]; simp [bptrs])
    cases hgy : P.get? y with
    | none => simp [hgy] at hy
    | some ny => exact hfresh _ (mem_of_get? hgy)
  · intro x nd hx hd hl
    exact klongsOf_ne_nil nd.hist (hN x nd (view_eq_get? p P t htimes x nd hx) hd hl)

theorem apply_exec_eq (p : Params) (P : Struct BVal) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs, w)) :
    P.apply i (exec p tx i v) = P.apply i (changesOf i w) := by
  unfold execW at he
  unfold exec exec?
  rw [he]
  rfl

/-- A transaction keeps the klongs of every key node well formed and giving
its history. -/
theorem keyHistOK_step (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)
    (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w)) :
    KeyHistOK p (P.apply i (exec p tx i (view (treeSpec p) P (i - 1)))) := by
  rw [apply_exec_eq p P tx i _ bs w he]
  intro x nd' hx hd hlv
  rcases apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x nd' hx hd hlv with
    ⟨n, _, _, hh, hk, hwf⟩ | ⟨hp, _⟩
  · rw [hk]
    exact ⟨hwf, hh.symm⟩
  · exact hH x nd' hp hd hlv

/-! ## Runs -/

theorem treeRun_root_level (p : Params) (ts : List Tx) :
    ∃ r, (treeRun p ts).get? root = some r ∧ p.keyMax < r.level := by
  have hf : ∀ (qs : List (Tx × Nat)) (P : Struct BVal),
      (∃ r, P.get? root = some r ∧ p.keyMax < r.level) →
        ∃ r, (qs.foldl (fun P (q : Tx × Nat) =>
          P.apply (q.2 + 1) (exec p q.1 (q.2 + 1) (view (treeSpec p) P q.2))) P).get? root = some r ∧
            p.keyMax < r.level := by
    intro qs
    induction qs with
    | nil => intro P hP; exact hP
    | cons q qs ih =>
      intro P hP
      apply ih
      obtain ⟨r, hr, hl⟩ := hP
      exact ⟨_, get?_apply_of_get? hr, hl⟩
  apply hf ts.zipIdx (initStruct p)
  refine ⟨_, init_get_root p, ?_⟩
  simp only [Params.rootLevel]
  omega

theorem keyHistOK_init (p : Params) : KeyHistOK p (initStruct p) := by
  intro x nd hx hd hl
  rcases mem_init p (x, nd) (mem_of_get? hx) with h | h | h
  · cases h
    simp only [Params.rootLevel] at hl
    omega
  · cases h
    have h1 : klongsWf (klongsOf [(⟨0, marker⟩ : Entry BVal)]) = true := by decide
    have h2 : entriesOf (klongsOf [(⟨0, marker⟩ : Entry BVal)]) = [⟨0, marker⟩] := by decide
    exact ⟨h1, h2⟩
  · cases h
    simp only [Params.topLevel] at hl
    omega

/-- After a run within reach, the klongs of every key node are well formed
and give its history, if after each earlier transaction of the run the
pointers of P name nodes of P (TP4) and every key node has a history. -/
theorem treeRun_keyHistOK (p : Params) (ts : List Tx) (hw : Within p ts)
    (hP : ∀ k < ts.length, PointersOK (treeRun p (ts.take k)))
    (hN : ∀ k < ts.length, KeyNonempty p (treeRun p (ts.take k))) :
    KeyHistOK p (treeRun p ts) := by
  have hk : ∀ n, n ≤ ts.length → KeyHistOK p (treeRun p (ts.take n)) := by
    intro n
    induction n with
    | zero => intro _; exact keyHistOK_init p
    | succ n ih =>
      intro hn
      have hlt : n < ts.length := by omega
      have htake : ts.take (n + 1) = ts.take n ++ [ts[n]] := List.take_succ_eq_append_getElem hlt
      have hlen : (ts.take n).length = n := by
        simp only [List.length_take]; omega
      have hwn : Within p (ts.take n ++ [ts[n]]) := by
        rw [← htake]; exact within_take p ts hw (n + 1)
      obtain ⟨bs, w, he⟩ := execW_success_of_within_snoc p (ts.take n) ts[n] hwn
      have hfresh := (hw.2 n hlt).1
      have htimes := treeRun_timesLE p (ts.take n)
      rw [hlen] at he htimes
      rw [htake, treeRun_snoc, hlen]
      exact keyHistOK_step p _ (n + 1) ts[n] bs w (by omega) hfresh htimes (treeRun_root_level p _)
        (ih (by omega))
        (viewLinksOK_of p _ n ts[n].base hfresh htimes (hP n hlt) (hN n hlt)) he
  have h := hk ts.length (Nat.le_refl _)
  rwa [List.take_length] at h

/-! ## TP7 from its parts -/

/-- A key node holds at most theta dead klongs, for every key node of P. -/
def DeadAllOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x n, keyNodeAt p P x = some n → p.theta ≠ 0 → n.deadCount ≤ p.theta

theorem keyNodeAt_of (p : Params) (P : Struct BVal) (x : NodeId) (nd : Node BVal)
    (hx : P.get? x = some nd) (hd : nd.isData = false) (hl : nd.level ≤ p.keyMax) :
    keyNodeAt p P x = some (nodeK p nd) := by
  simp [keyNodeAt, hx, hd, hl, nodeK]

/-- TP7 from statements without klong well-formedness: the invariants at
each run's last time (`LatestInvOK`), pointers to nodes of P (TP4), at most M
klongs in a key node (TP5), a history for every key node (`KeyNonempty`),
and at most theta dead klongs in every key node (`DeadAllOK`), each after
every run within reach. -/
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

end SIS.Tree
