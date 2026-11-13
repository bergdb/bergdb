import SIS.Tree.WriterEncodingOps
import SIS.Tree.TreeReadModel
import SIS.Proof.Basic
import SIS.Tree.InvInit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

def ChangesEncoded (c : Changes BVal) : Prop := ∀ q ∈ c.adds, ValueEncoded q.2

def StructEncoded (P : Struct BVal) : Prop := ∀ q ∈ P, HistoryEncoded q.2.hist

theorem changesOf_encoded (i : Time) (w : W) (hw : WriterEncoded w) :
    ChangesEncoded (changesOf i w) := by
  intro q hq
  unfold changesOf at hq
  have hm := (List.mergeSort_perm _ _).mem_iff.mp hq
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hk | hv
    · obtain ⟨node, hnode, hentry⟩ := List.mem_flatMap.mp hk
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hentry
      cases heq
      exact entriesOf_encoded node.2.ks (hw.1 node (List.mem_filter.mp hnode).1)
        e (List.mem_filter.mp he).1
    · obtain ⟨pair, _, heq⟩ := List.mem_map.mp hv
      cases heq
      trivial
  · split at hm
    · rcases List.mem_cons.mp hm with heq | hm
      · subst q; trivial
      · rcases List.mem_cons.mp hm with heq | hm
        · subst q; trivial
        · obtain ⟨pair, _, heq⟩ := List.mem_map.mp hm
          cases heq
          trivial
    · cases hm

theorem structEncoded_addEntry (P : Struct BVal) (i : Time) (x : NodeId) (val : BVal)
    (hP : StructEncoded P) (hv : ValueEncoded val) : StructEncoded (P.addEntry i x val) := by
  intro q hq
  unfold Struct.addEntry at hq
  obtain ⟨old, hold, he⟩ := List.mem_map.mp hq
  split at he
  · cases he
    apply (historyEncoded_append _ _).mpr
    exact ⟨hP old hold, by simpa [HistoryEncoded] using hv⟩
  · cases he
    exact hP _ hold

theorem structEncoded_apply (P : Struct BVal) (i : Time) (c : Changes BVal)
    (hP : StructEncoded P) (hc : ChangesEncoded c) : StructEncoded (P.apply i c) := by
  have hf : ∀ (qs : List (NodeId × BVal)) (Q : Struct BVal),
      (∀ q ∈ qs, ValueEncoded q.2) → StructEncoded Q →
        StructEncoded (qs.foldl (fun Q q => Q.addEntry i q.1 q.2) Q) := by
    intro qs
    induction qs with
    | nil => intro Q _ hQ; exact hQ
    | cons q qs ih =>
      intro Q hq hQ
      exact ih _ (fun a ha => hq a (List.mem_cons_of_mem q ha))
        (structEncoded_addEntry Q i q.1 q.2 hQ (hq q List.mem_cons_self))
  apply hf c.adds _ hc
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hP q hq
  · obtain ⟨node, _, he⟩ := List.mem_map.mp hq
    cases he
    exact historyEncoded_nil

theorem structEncoded_viewOf (P : Struct BVal) (hP : StructEncoded P) :
    ViewEncoded (viewOf P) := by
  intro x n hn
  exact hP _ (mem_of_get? hn)

theorem historyEncoded_upTo (es : History BVal) (t : Time) (he : HistoryEncoded es) :
    HistoryEncoded (es.upTo t) := by
  intro e hm
  exact he e (List.mem_filter.mp hm).1

theorem structEncoded_view (p : Params) (P : Struct BVal) (t : Time) (hP : StructEncoded P) :
    ViewEncoded (view (treeSpec p) P t) := by
  intro x n hn
  unfold view at hn
  split at hn
  · cases hx : P.get? x with
    | none => simp [hx] at hn
    | some old =>
      have he : {old with hist := old.hist.upTo t} = n := by simpa [hx] using hn
      subst n
      exact historyEncoded_upTo old.hist t (hP _ (mem_of_get? hx))
  · cases hn

theorem exec_changes_encoded (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (hv : ViewEncoded v) (htx : tx.wf = true) : ChangesEncoded (exec p tx i v) := by
  unfold exec exec?
  cases he : runOps p tx.base tx.ops i v with
  | error e => simp [ChangesEncoded, Except.map]
  | ok result =>
    rcases result with ⟨bs, w⟩
    simp only [Except.map]
    exact changesOf_encoded i w (execW_encoded p tx i v bs w hv htx he)

theorem structEncoded_init (p : Params) : StructEncoded (initStruct p) := by
  intro q hq
  rcases mem_init p q hq with rfl | rfl | rfl <;>
    simp [HistoryEncoded, ValueEncoded, marker]

/-- Every stored key compare value in a run satisfies the corrected scalar
encoding restriction. No successful-execution, sorting or freshness premise
is required beyond the well-formed keys of the transactions themselves. -/
theorem treeRun_encoded (p : Params) (ts : List Tx) (hts : ∀ tx ∈ ts, tx.wf = true) :
    StructEncoded (treeRun p ts) := by
  have hf : ∀ (qs : List (Tx × Nat)) (P : Struct BVal),
      (∀ q ∈ qs, q.1.wf = true) → StructEncoded P →
        StructEncoded (qs.foldl (fun P (q : Tx × Nat) =>
          P.apply (q.2 + 1) (exec p q.1 (q.2 + 1) (view (treeSpec p) P q.2))) P) := by
    intro qs
    induction qs with
    | nil => intro P _ hP; exact hP
    | cons q qs ih =>
      intro P hq hP
      exact ih _ (fun a ha => hq a (List.mem_cons_of_mem q ha))
        (structEncoded_apply P (q.2 + 1) _ hP
          (exec_changes_encoded p q.1 (q.2 + 1) _ (structEncoded_view p P q.2 hP)
            (hq q List.mem_cons_self)))
  exact hf ts.zipIdx (initStruct p)
    (fun q hq => hts q.1 (List.fst_mem_of_mem_zipIdx hq)) (structEncoded_init p)

theorem treeRun_encoded_of_within (p : Params) (ts : List Tx) (hw : Within p ts) :
    StructEncoded (treeRun p ts) := treeRun_encoded p ts (fun tx ht => (hw.1 tx ht).2)

theorem knodeOf_encoded (p : Params) (v : View BVal) (x : NodeId) (n : KNode)
    (hv : ViewEncoded v) (hn : knodeOf p v x = some n) : KlongsEncoded n.ks := by
  unfold knodeOf at hn
  cases hx : v x with
  | none => simp [hx] at hn
  | some nd =>
    simp only [hx] at hn
    split at hn
    · cases hn
    · have he := Option.some.inj hn
      subst n
      exact klongsOf_encoded nd.hist (hv x nd hx)

/-- The corrected well-formedness claim needs encoded input histories;
the old length-shape theorem holds on arbitrary views. -/
theorem treeContents_keyWf_of_encoded (p : Params) (v : View BVal) (t f x : Nat)
    (hv : ViewEncoded v) : ∀ q ∈ treeContents p v t f x, keyWf q.1 = true := by
  induction f generalizing x with
  | zero => simp [treeContents]
  | succ f ih =>
    intro kv hkv
    simp only [treeContents] at hkv
    cases hn : knodeOf p v x with
    | none => simp [hn] at hkv
    | some n =>
      have hencoded := (knodeOf_encoded p v x n hv hn).liveAt n t
      simp only [hn] at hkv
      obtain ⟨q, hq, hkv⟩ := List.mem_flatMap.mp hkv
      have hc := hencoded q hq
      cases hleaf : n.leaf with
      | false =>
        simp only [hleaf, Bool.false_eq_true, ↓reduceIte] at hkv
        exact ih q.2 kv hkv
      | true =>
        simp only [hleaf, ↓reduceIte] at hkv
        by_cases hlen : segLen q.1 = 7
        · simp only [hlen, beq_self_eq_true, ↓reduceIte] at hkv
          obtain ⟨child, hchild, rfl⟩ := List.mem_map.mp hkv
          have hw := ih q.2 child hchild
          cases hk : child.1 with
          | nil => simp [hk, keyWf] at hw
          | cons c rest =>
            apply (keyWf_cons_cons q.1 c rest).mpr
            exact ⟨hc.1, hc.2, hlen, by simpa only [hk] using hw⟩
        · simp only [show (segLen q.1 == 7) = false by simp [hlen], Bool.false_eq_true, ↓reduceIte] at hkv
          cases hh : valueOf v q.2 with
          | none => simp [hh] at hkv
          | some value =>
            have he : kv = ([q.1], value) := by simpa [hh] using hkv
            subst kv
            exact (keyWf_singleton q.1).mpr ⟨hc.1, hc.2, hlen⟩

theorem treeRun_treeContents_keyWf (p : Params) (ts : List Tx) (hw : Within p ts)
    (t f x : Nat) :
    ∀ q ∈ treeContents p (viewOf (treeRun p ts)) t f x, keyWf q.1 = true :=
  treeContents_keyWf_of_encoded p _ t f x
    (structEncoded_viewOf _ (treeRun_encoded_of_within p ts hw))

end SIS.Tree
