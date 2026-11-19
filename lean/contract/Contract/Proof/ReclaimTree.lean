/-
The contract package (bergdb 030-24): proofs for RC2 and RC3 on BergDB's key
tree (Contract/ReclaimTree.lean), in the contract's words.

A sound key node with a live klong has a value below it (`Good.val_below`):
a live klong of an inner node, or of a long segment, names a sound key node
with a live klong, on a lower level; a short segment's names a value. And
every node that the walk reaches from a sound node is the node itself, a
value, or a sound key node with a live klong (`Good.reach_cases`).
-/
import Contract.Proof.Good
import Contract.Proof.BridgeReach
import Contract.Proof.BridgeWords
import Contract.BridgeFull

namespace Contract

variable {s : Tree}

/-- A sound key node with a live klong has a value below it, which the walk
with enough fuel reaches. -/
theorem Good.val_below : ∀ (f : Nat) {x : NodeId} {lo : Nat} {hi : Option Nat} {n : KNode},
    Good s x lo hi → s.obj x = some (.key n) → live n.ks ≠ [] → n.level < f →
    ∃ v w, s.obj v = some (.val w) ∧ v ∈ reachAt s f x
  | 0, _, _, _, _, _, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | f + 1, x, lo, hi, n, hg, hobj, hne, hf => by
    obtain ⟨⟨c, y⟩, hm⟩ : ∃ cy, cy ∈ live n.ks := List.exists_mem_of_ne_nil _ hne
    have hreach : ∀ z, z ∈ reachAt s f y → z ∈ reachAt s (f + 1) x := by
      intro z hz
      simp only [reachAt, hobj, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨(c, y), hm, hz⟩
    by_cases hk : n.leaf = true → isLong c = true
    · obtain ⟨m, lo', hi', hm1, hm2, hm3, hgy⟩ := hg.child hobj hm hk
      obtain ⟨v, w, hv, hvr⟩ := Good.val_below f hgy hm1 hm3 (by omega)
      exact ⟨v, w, hv, hreach v hvr⟩
    · have hl : n.leaf = true := by
        by_contra hl
        exact hk (fun h => absurd h hl)
      have hs : isLong c = false := by
        cases hc : isLong c with
        | false => rfl
        | true => exact absurd (fun _ => hc) hk
      cases hg with
      | mk _ _ _ n' hobj' _ _ _ hval _ _ _ =>
        rw [hobj] at hobj'
        obtain rfl : n = n' := by injection hobj' with h1; injection h1
        obtain ⟨w, hw⟩ := hval hl c y hm hs
        exact ⟨y, w, hw, hreach y (mem_reachAt_self s f y)⟩

/-- What the walk reaches from a sound node: the node, a value, or a sound key
node with a live klong. -/
theorem Good.reach_cases : ∀ (f : Nat) {r : NodeId} {lo : Nat} {hi : Option Nat},
    Good s r lo hi → ∀ x, x ∈ reachAt s f r →
    x = r ∨ (∃ w, s.obj x = some (.val w)) ∨
      ∃ m lo' hi', s.obj x = some (.key m) ∧ live m.ks ≠ [] ∧ Good s x lo' hi'
  | 0, r, _, _, _, x, hx => by
    simp only [reachAt, List.mem_singleton] at hx
    exact Or.inl hx
  | f + 1, r, lo, hi, hg, x, hx => by
    simp only [reachAt, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · right
      cases hro : s.obj r with
      | none => rw [hro] at hx; simp at hx
      | some o =>
        cases o with
        | val w => rw [hro] at hx; simp at hx
        | key n =>
          rw [hro] at hx
          simp only [List.mem_flatMap] at hx
          obtain ⟨⟨c, y⟩, hm, hxy⟩ := hx
          by_cases hk : n.leaf = true → isLong c = true
          · obtain ⟨m, lo', hi', hm1, _, hm3, hgy⟩ := hg.child hro hm hk
            rcases Good.reach_cases f hgy x hxy with rfl | h2 | h2
            · exact Or.inr ⟨m, lo', hi', hm1, hm3, hgy⟩
            · exact Or.inl h2
            · exact Or.inr h2
          · have hl : n.leaf = true := by
              by_contra hl
              exact hk (fun h => absurd h hl)
            have hs : isLong c = false := by
              cases hc : isLong c with
              | false => rfl
              | true => exact absurd (fun _ => hc) hk
            cases hg with
            | mk _ _ _ n' hobj' _ _ _ hval _ _ _ =>
              rw [hro] at hobj'
              obtain rfl : n = n' := by injection hobj' with h1; injection h1
              obtain ⟨w, hw⟩ := hval hl c y hm hs
              have : x = y := by
                cases f with
                | zero => simpa [reachAt] using hxy
                | succ f =>
                  simp only [reachAt, hw, List.mem_cons] at hxy
                  rcases hxy with h | h
                  · exact h
                  · simp at h
              subst this
              exact Or.inl ⟨w, hw⟩

section Hist

variable {p : Params} {h : BHist} {top : Nat → Top}

/-- The invariants after every transaction of a history in the contract's
words, at the transaction's time. -/
theorem MeetsFull.inv_at (hm : MeetsFull p h top) (hM : 1 ≤ p.M) :
    ∀ j, j ≤ h.txs.length → invOk p ((h.tree j).at j) = true
  | 0, _ => (hm.start.start hM).1
  | j + 1, hj => by
    have hc := (hm.step j hj).1.1
    simp only [contractOk, Bool.and_eq_true] at hc
    exact hc.1

/-- The space root after transaction j is a sound key node, and, if the tree
holds a key, it has a live klong. -/
theorem MeetsFull.root_good (hm : MeetsFull p h top) (hM : 1 ≤ p.M) {j : Nat}
    (hj : j ≤ h.txs.length) {r : NodeId} (hr : (h.tree j).root = some r) :
    ∃ n, (h.tree j).obj r = some (.key n) ∧ Good (h.tree j) r 0 none ∧
      (contents (h.tree j) ≠ [] → live n.ks ≠ []) := by
  have hi := hm.meetsBridge.binv j hj
  have hinv := hm.inv_at hM j hj
  rw [hi.timely.at_eq] at hinv
  unfold invOk at hinv
  simp only [hr] at hinv
  cases ho : (h.tree j).obj r with
  | none => simp [ho] at hinv
  | some o =>
    simp only [ho] at hinv
    cases o with
    | val w => simp at hinv
    | key n =>
      simp only [Bool.and_eq_true] at hinv
      refine ⟨n, rfl, walk_good _ _ _ _ hinv.2, ?_⟩
      intro hne hl
      apply hne
      unfold contents
      rw [hr]
      simp [Tree.fuel, ho, listAt, hl]

end Hist

end Contract
