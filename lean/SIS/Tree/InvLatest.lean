/-
The tree model (bergdb 024-12, TP7): TP7 reduced to its latest time.

`InvPreserved` asks for the invariants at every time t up to the run's
length. A walk at an earlier time t reads two things of each node it reaches:
its live klongs at t, which later transactions never change (entries are
only appended), and the node as it is now (`CurrentOK`: size, well-formed
klongs, klongs that give the history, pointers, dead klongs). So the walk at
t stays fault-free through every later transaction that leaves the key
nodes sound as they are (`walk_apply_past`, `invOK_apply_past`), and TP7
follows from three statements about the structure after a run, none about an
earlier time (`invPreserved_of_latest`):

* `LatestInvOK`: the invariants at the run's last time;
* `KeyNodesOK`: every key node of P, reachable or not, sound as it is;
* `PointersOK` (TP4).
-/
import SIS.Tree.WalkNil
import SIS.Tree.ReadExtension

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every key node of P, reachable or not, is sound as it is now: at most M
klongs, well formed, giving its history; its klongs name nodes of P; at most
theta dead klongs. -/
def KeyNodesOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    CurrentOK p (viewOf P) nd

/-- A walk at time t without faults stays so when a later transaction's
changes are applied, if the key nodes are sound as they are after it. -/
theorem walk_apply_past (p : Params) (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (hK : HighKindsOK p P) (hA : KeyNodesOK p (P.apply i c))
    (f x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) :
    walk p (viewOf (P.apply i c)) t f x lo hi isRoot space = [] := by
  induction f generalizing x lo hi isRoot space with
  | zero => simp [walk] at hw
  | succ f ih =>
    cases hx : P.get? x with
    | none => simp [walk, viewOf, hx] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp [walk, viewOf, hx, hd] at hw
      | false =>
        have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hK hx hd hw
        obtain ⟨_, hT, hC⟩ :=
          (walk_succ_eq_nil_iff p (viewOf P) t f x lo hi isRoot space nd hx hd).mp hw
        have hx' : (P.apply i c).get? x = some { nd with hist := nd.hist ++ addsFor c i x } :=
          get?_apply_of_get? hx
        have hpre : prefixAt (nodeK p { nd with hist := nd.hist ++ addsFor c i x }).ks t =
            prefixAt (nodeK p nd).ks t :=
          klongsOf_prefixAt_append_future nd.hist _ t (addsFor_future c i t x ht)
        have hlive : (nodeK p { nd with hist := nd.hist ++ addsFor c i x }).liveAt t =
            (nodeK p nd).liveAt t := KNode.liveAt_eq_of_prefix _ _ t hpre
        apply (walk_succ_eq_nil_iff p (viewOf (P.apply i c)) t f x lo hi isRoot space _
          hx' hd).mpr
        refine ⟨hA x _ hx' hd hl, ?_, ?_⟩
        · rw [hlive]
          exact hT
        · rw [hlive]
          intro qb hqb
          have hq := hC qb hqb
          obtain ⟨⟨cv, y⟩, b⟩ := qb
          have hmem := childBounds_fst _ _ _ _ hqb
          have hp := walk_current_pointer p (viewOf P) t f x lo hi isRoot space nd hx hd hw
            cv y ((nodeK p nd).liveAt_key_mem t cv y hmem)
          cases hy : P.get? y with
          | none => simp [viewOf, hy] at hp
          | some ny =>
            have hy' : (P.apply i c).get? y =
                some { ny with hist := ny.hist ++ addsFor c i y } := get?_apply_of_get? hy
            have hleaf : (nodeK p { nd with hist := nd.hist ++ addsFor c i x }).leaf =
                (nodeK p nd).leaf := rfl
            simp only [walkChildFaults, viewOf, hy, hy', hleaf] at hq ⊢
            cases hnl : (nodeK p nd).leaf with
            | true =>
              simp only [hnl, ↓reduceIte] at hq ⊢
              by_cases hlen : segLen cv = 7
              · simp only [hlen, beq_self_eq_true, ↓reduceIte] at hq ⊢
                cases hnd : ny.isData with
                | true => simp [hnd] at hq
                | false =>
                  simp only [hnd, Bool.false_eq_true, ↓reduceIte] at hq ⊢
                  split at hq
                  · cases hq
                  · rename_i hseg
                    simp only [hseg]
                    exact ih y _ _ _ _ hq
              · simp only [show (segLen cv == 7) = false by simp [hlen], Bool.false_eq_true,
                  ↓reduceIte] at hq ⊢
                exact hq
            | false =>
              simp only [hnl, Bool.false_eq_true, ↓reduceIte] at hq ⊢
              cases hnd : ny.isData with
              | true => simp [hnd] at hq
              | false =>
                simp only [hnd, Bool.false_eq_true, ↓reduceIte] at hq ⊢
                split at hq
                · cases hq
                · rename_i hseg
                  simp only [hseg]
                  exact ih y _ _ _ _ hq

/-- The invariants at time t hold after a later transaction's changes, if
they held before and the key nodes are sound as they are after it. -/
theorem invOK_apply_past (p : Params) (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (hK : HighKindsOK p P) (hA : KeyNodesOK p (P.apply i c))
    (hi : InvOK p P t) : InvOK p (P.apply i c) t := by
  unfold InvOK faultsAt at hi ⊢
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hi
  | some r =>
    simp only [hr] at hi
    rw [rootAt_apply_some_past P i t c ht r hr]
    exact walk_apply_past p P i t c ht hK hA p.fuel r 0 none true true hi

/-- The invariants at time t after the first t transactions hold after the
whole run, if after every longer prefix the key nodes are sound as they are. -/
theorem invOK_treeRun_of_take (p : Params) (ts : List Tx) (t : Time) (ht : t ≤ ts.length)
    (hA : ∀ k, t < k → k ≤ ts.length → KeyNodesOK p (treeRun p (ts.take k)))
    (h0 : InvOK p (treeRun p (ts.take t)) t) : InvOK p (treeRun p ts) t := by
  have hk : ∀ d, t + d ≤ ts.length → InvOK p (treeRun p (ts.take (t + d))) t := by
    intro d
    induction d with
    | zero => intro _; exact h0
    | succ d ih =>
      intro hd
      have hlt : t + d < ts.length := by omega
      have htake : ts.take (t + (d + 1)) = ts.take (t + d) ++ [ts[t + d]] := by
        rw [← Nat.add_assoc]
        exact List.take_succ_eq_append_getElem hlt
      have hA' := hA (t + (d + 1)) (by omega) hd
      have hlen : (ts.take (t + d)).length = t + d := by
        simp only [List.length_take]; omega
      rw [htake, treeRun_snoc, hlen] at hA' ⊢
      exact invOK_apply_past p _ (t + d + 1) t _ (by omega) (treeRun_highKindsOK p _) hA'
        (ih (by omega))
  have h := hk (ts.length - t) (by omega)
  rwa [show t + (ts.length - t) = ts.length by omega, List.take_length] at h

/-- TP7 from its latest time: the invariants at every time of every run within
reach follow from the invariants at each run's last time (`LatestInvOK`), every
key node sound as it is (`KeyNodesOK`), and pointers to nodes of P (TP4). No
premise speaks of an earlier time. -/
theorem invPreserved_of_latest (p : Params)
    (hA : ∀ ts, Within p ts → KeyNodesOK p (treeRun p ts))
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hL : LatestInvOK p) : InvPreserved p := by
  intro ts hw t ht
  refine ⟨?_, hP ts hw⟩
  apply invOK_treeRun_of_take p ts t ht
  · intro k _ _
    exact hA _ (within_take p ts hw k)
  · have hlen : (ts.take t).length = t := by
      simp only [List.length_take, Nat.min_eq_left ht]
    have h := hL (ts.take t) (within_take p ts hw t)
    rwa [hlen] at h

end SIS.Tree
