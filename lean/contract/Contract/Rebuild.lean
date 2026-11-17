/-
The contract package (bergdb 030-08, work list item 4): the step from a
trace's lines to Java's tree, reduced to one named premise.

The checker builds a tree from each transaction's lines (`applyTx`,
Trace.lean) and a top (`applyTop`, TraceTop.lean), and checks the contract on
them. What the theorems then say is about the trees the checker built. They
say it about Java's own trees if the lines are Java's change: `LinesOf s s'
tx`, the premise, says that the lines of a transaction describe the change
from Java's tree s before it to Java's tree s' after it:

* every node of s' that is not as it was in s has a line: a value its V
  entry (`ADD y i V h`), a key node its KN line (030-09 tests this: a NEW
  line for every node made, a KN line for every key node made or given a
  klong, from Java's klong diff, and an ERROR line, which fails, for a
  change that lines cannot express);
* every V entry is a value of s', every KN line a key node of s' with its
  klongs and its kind; its level is that of its NEW line, or, for a node
  that was there, the level it had (levels are the exporter's, computed after
  the run, 027-02; Java has none: a level is only a witness that every walk
  ends, which the invariants check);
* the space roots of s' are those of s, then the root pointer of each top
  node made, at time i.

Proved: from such lines `applyTx` rebuilds s' exactly (`applyTx_rebuilds`);
so, by induction over a trace (`java_meetsTop`), if the lines of every
transaction are Java's change and Java's top is the one the lines give, and
the checker passes the trace, then Java's own trees and tops meet `MeetsTop`,
and the theorems of TheoremsTop.lean hold for Java's trees.

The premises left, each tested, not proved: `LinesOf` for every transaction
(the exporter, TraceExport, writes Java's change: 030-09's completeness
checks; the old checkers tie the ADD lines to the stream, tracecheck, and
the KN lines to the model's writer, treecheck); Java's top the lines' top
(SKIPT lines for the cached times, LIVE lines for the search); and that
`runOk` is what ContractCheck.lean's loop computes (by reading: the loop
computes `checkTopTx` of the same heaps, and compares it with its parts).
-/
import Contract.HistoryTop
import Contract.TraceTop

namespace Contract

/-- The level that `applyTx` gives the key node of a KN line: its NEW line's,
or the level it had in s. -/
def levelOf (s : Tree) (tx : TxLines) (x : NodeId) : Nat :=
  match tx.news.lookup x with
  | some l => l
  | none =>
    match s.obj x with
    | some (.key n) => n.level
    | _ => 0

/-- The premise: the lines tx of a transaction are the change from Java's
tree s before it to Java's tree s' after it. -/
structure LinesOf (s s' : Tree) (tx : TxLines) : Prop where
  covered : ∀ x, s'.obj x ≠ s.obj x →
    (∃ v, (x, v) ∈ tx.vals) ∨ (∃ leaf ks, (x, leaf, ks) ∈ tx.kns)
  vals : ∀ y v, (y, v) ∈ tx.vals → s'.obj y = some (.val v)
  kns : ∀ x leaf ks, (x, leaf, ks) ∈ tx.kns →
    s'.obj x = some (.key { level := levelOf s tx x, leaf := leaf, ks := ks })
  roots : s'.roots =
    s.roots ++ tx.tops.filterMap (fun z => (tx.rootPtrs.lookup z).map (fun y => (tx.i, y)))

/-! ## applyTx rebuilds the tree -/

theorem fold_insert_none {β : Type} (g : NodeId × β → Obj) (x : NodeId) :
    ∀ (l : List (NodeId × β)) (m : Std.HashMap NodeId Obj), (∀ q ∈ l, q.1 ≠ x) →
      (l.foldl (fun m q => m.insert q.1 (g q)) m)[x]? = m[x]?
  | [], _, _ => rfl
  | a :: r, m, h => by
    rw [List.foldl_cons, fold_insert_none g x r _ (fun q hq => h q (List.mem_cons_of_mem a hq)),
      Std.HashMap.getElem?_insert]
    have : (a.1 == x) = false := by simpa using h a List.mem_cons_self
    simp [this]

theorem fold_insert_some {β : Type} (g : NodeId × β → Obj) (x : NodeId) :
    ∀ (l : List (NodeId × β)) (m : Std.HashMap NodeId Obj), (∃ q ∈ l, q.1 = x) →
      ∃ q ∈ l, q.1 = x ∧ (l.foldl (fun m q => m.insert q.1 (g q)) m)[x]? = some (g q)
  | [], _, h => by simp at h
  | a :: r, m, h => by
    rw [List.foldl_cons]
    by_cases hr : ∃ q ∈ r, q.1 = x
    · obtain ⟨q, hq, h1, h2⟩ := fold_insert_some g x r _ hr
      exact ⟨q, List.mem_cons_of_mem a hq, h1, h2⟩
    · have hr' : ∀ q ∈ r, q.1 ≠ x := fun q hq h1 => hr ⟨q, hq, h1⟩
      rw [fold_insert_none g x r _ hr', Std.HashMap.getElem?_insert]
      obtain ⟨q, hq, h1⟩ := h
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨q, List.mem_cons_self, h1, by simp [h1]⟩
      · exact absurd ⟨q, hq, h1⟩ hr

theorem fold_roots (tx : TxLines) : ∀ (zs : List NodeId) (rs : List (Time × NodeId)),
    zs.foldl (fun rs z => match tx.rootPtrs.lookup z with
      | some y => rs ++ [(tx.i, y)]
      | none => rs) rs =
    rs ++ zs.filterMap (fun z => (tx.rootPtrs.lookup z).map (fun y => (tx.i, y)))
  | [], rs => by simp
  | z :: zs, rs => by
    rw [List.foldl_cons, fold_roots tx zs]
    cases h : tx.rootPtrs.lookup z <;> simp [h]

/-- From lines that are Java's change, the checker rebuilds Java's tree. -/
theorem applyTx_rebuilds (h : Heap) (s' : Tree) (tx : TxLines) (hl : LinesOf h.tree s' tx) :
    (applyTx h tx).tree = s' := by
  obtain ⟨obj', roots'⟩ := s'
  simp only [Heap.tree, applyTx, Tree.mk.injEq]
  refine ⟨?_, ?_⟩
  · funext x
    let gk : NodeId × Bool × List Klong → Obj := fun q =>
      .key { level := levelOf h.tree tx q.1, leaf := q.2.1, ks := q.2.2 }
    let gv : NodeId × Nat → Obj := fun q => .val q.2
    show (tx.kns.foldl (fun m q => m.insert q.1 (gk q))
      (tx.vals.foldl (fun m q => m.insert q.1 (gv q)) h.objs))[x]? = obj' x
    by_cases hk : ∃ q ∈ tx.kns, q.1 = x
    · obtain ⟨q, hq, hqx, h1⟩ := fold_insert_some gk x tx.kns _ hk
      rw [h1]
      subst hqx
      exact (hl.kns q.1 q.2.1 q.2.2 hq).symm
    · rw [fold_insert_none gk x tx.kns _ (fun q hq h1 => hk ⟨q, hq, h1⟩)]
      by_cases hv : ∃ q ∈ tx.vals, q.1 = x
      · obtain ⟨q, hq, hqx, h1⟩ := fold_insert_some gv x tx.vals _ hv
        rw [h1]
        subst hqx
        exact (hl.vals q.1 q.2 hq).symm
      · rw [fold_insert_none gv x tx.vals _ (fun q hq h1 => hv ⟨q, hq, h1⟩)]
        apply Classical.byContradiction
        intro hne
        rcases hl.covered x (Ne.symm hne) with ⟨v, hv'⟩ | ⟨leaf, ks, hk'⟩
        · exact hv ⟨(x, v), hv', rfl⟩
        · exact hk ⟨(x, leaf, ks), hk', rfl⟩
  · exact (fold_roots tx tx.tops h.roots).trans hl.roots.symm

/-! ## The premise can be met

The tree that `applyTx` builds meets `LinesOf` with the lines it was built
from, whenever the lines name each node once (030-09's completeness check
refuses a second KN line). So the premise is not vacuous: it says that the
lines are of Java's tree, nothing more. -/

theorem eq_of_mem_ids {β : Type} :
    ∀ {l : List (NodeId × β)}, (l.map (·.1)).Nodup → ∀ {q q' : NodeId × β}, q ∈ l → q' ∈ l →
      q.1 = q'.1 → q = q'
  | [], _, _, _, hq, _, _ => by simp at hq
  | a :: r, hn, q, q', hq, hq', h => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    rcases List.mem_cons.mp hq with h1 | h1 <;> rcases List.mem_cons.mp hq' with h2 | h2
    · exact h1.trans h2.symm
    · subst h1; exact absurd ⟨q', h2, h.symm⟩ hn.1
    · subst h2; exact absurd ⟨q, h1, h⟩ hn.1
    · exact eq_of_mem_ids hn.2 h1 h2 h

theorem applyTx_linesOf (h : Heap) (tx : TxLines) (hk : (tx.kns.map (·.1)).Nodup)
    (hv : (tx.vals.map (·.1)).Nodup) (hvk : ∀ q ∈ tx.vals, ∀ k ∈ tx.kns, q.1 ≠ k.1) :
    LinesOf h.tree (applyTx h tx).tree tx := by
  let gk : NodeId × Bool × List Klong → Obj := fun q =>
    .key { level := levelOf h.tree tx q.1, leaf := q.2.1, ks := q.2.2 }
  let gv : NodeId × Nat → Obj := fun q => .val q.2
  have hobj : ∀ x, (applyTx h tx).tree.obj x = (tx.kns.foldl (fun m q => m.insert q.1 (gk q))
      (tx.vals.foldl (fun m q => m.insert q.1 (gv q)) h.objs))[x]? := fun x => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hne
    rw [hobj] at hne
    apply Classical.byContradiction
    intro hno
    have h1 : ∀ q ∈ tx.kns, q.1 ≠ x := fun q hq h1 => hno (Or.inr ⟨q.2.1, q.2.2, h1 ▸ hq⟩)
    have h2 : ∀ q ∈ tx.vals, q.1 ≠ x := fun q hq h2 => hno (Or.inl ⟨q.2, h2 ▸ hq⟩)
    rw [fold_insert_none gk x tx.kns _ h1, fold_insert_none gv x tx.vals _ h2] at hne
    exact hne rfl
  · intro y v hyv
    rw [hobj, fold_insert_none gk y tx.kns _ (fun k hk' h1 => hvk (y, v) hyv k hk' h1.symm)]
    obtain ⟨q, hq, hqy, h1⟩ := fold_insert_some gv y tx.vals h.objs ⟨(y, v), hyv, rfl⟩
    rw [h1, eq_of_mem_ids hv hq hyv hqy]
  · intro x leaf ks hx
    rw [hobj]
    obtain ⟨q, hq, hqx, h1⟩ := fold_insert_some gk x tx.kns _ ⟨(x, leaf, ks), hx, rfl⟩
    rw [h1, eq_of_mem_ids hk hq hx hqx]
  · exact fold_roots tx tx.tops h.roots

/-! ## Java's trees meet the contract -/

/-- The checker's verdict on a trace from heap h and top tp at time i: each
transaction its operations, its D and its lines, applied and checked. -/
def runOk (p : Params) : Time → Heap → Top → List (List Op × List NodeId × TxLines) → Bool
  | _, _, _, [] => true
  | i, h, tp, (ops, D, tx) :: rest =>
    checkTopTx p i h tp ops D (applyTx h tx) (applyTop tp tx) &&
      runOk p (i + 1) (applyTx h tx) (applyTop tp tx) rest

/-- The premise for a trace: Java's trees and tops js, one after each
transaction, from Java's tree s and top tp before the first; the lines of
each transaction are Java's change of the tree, and Java's top after it is
the one its lines give. -/
def JavaLines : Tree → Top → List (List Op × List NodeId × TxLines) → List (Tree × Top) → Prop
  | _, _, [], [] => True
  | s, tp, (_, _, tx) :: rest, (s', tp') :: js =>
    LinesOf s s' tx ∧ tp' = applyTop tp tx ∧ JavaLines s' tp' rest js
  | _, _, _, _ => False

/-- Java's tree and top after the last transaction. -/
def lastJava : Tree × Top → List (Tree × Top) → Tree × Top
  | st, [] => st
  | _, st :: js => lastJava st js

/-- If the checker passes a trace whose lines are Java's change, from a
heap with Java's tree, then Java's trees and tops meet the contract with
TREE and the top: the theorems of TheoremsTop.lean hold for Java's trees. -/
theorem java_meetsTop (p : Params) :
    ∀ (steps : List (List Op × List NodeId × TxLines)) (js : List (Tree × Top))
      (txs : List (List Op)) (h : Heap) (s : Tree) (tp : Top),
      h.tree = s → MeetsTop p txs s tp → JavaLines s tp steps js →
      runOk p (txs.length + 1) h tp steps = true →
      MeetsTop p (txs ++ steps.map (·.1)) (lastJava (s, tp) js).1 (lastJava (s, tp) js).2
  | [], [], txs, _, s, tp, _, hm, _, _ => by simpa [lastJava] using hm
  | [], _ :: _, _, _, _, _, _, _, hj, _ => by simp [JavaLines] at hj
  | _ :: _, [], _, _, _, _, _, _, hj, _ => by simp [JavaLines] at hj
  | (ops, D, tx) :: rest, (s', tp') :: js, txs, h, s, tp, hs, hm, hj, hc => by
    simp only [JavaLines] at hj
    obtain ⟨hl, htp, hj⟩ := hj
    simp only [runOk, Bool.and_eq_true] at hc
    obtain ⟨h1, h2, h3, h4⟩ := checkTopTx_sound p _ h tp ops D _ _ hc.1
    have hs' : (applyTx h tx).tree = s' := applyTx_rebuilds h s' tx (hs ▸ hl)
    rw [hs, hs'] at h1
    rw [hs'] at h2 h4
    rw [← htp] at h3 h4
    have hm' : MeetsTop p (txs ++ [ops]) s' tp' := MeetsTop.step txs s tp ops D s' tp' hm h1 h2 h3 h4
    rw [← htp] at hc
    have := java_meetsTop p rest js (txs ++ [ops]) (applyTx h tx) s' tp' hs' hm' hj
      (by simpa [Nat.add_assoc] using hc.2)
    simpa [lastJava, List.append_assoc] using this

/-- The start: if the lines of TX 0 are Java's start tree, from no nodes,
Java's start top the one they give, and the checker passes the start, then
Java's start tree and top meet the start of `MeetsTop`. -/
theorem java_start (p : Params) (s : Tree) (tp : Top) (tx : TxLines)
    (hl : LinesOf ({} : Heap).tree s tx) (htp : tp = applyTop [] tx)
    (hc : startTopOk p (applyTx {} tx) (applyTop [] tx) = true) : MeetsTop p [] s tp := by
  have := startTopOk_meetsTop p _ _ hc
  rwa [applyTx_rebuilds {} s tx hl, ← htp] at this

end Contract
