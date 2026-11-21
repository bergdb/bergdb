/-
bergdb 030-37: fill of one segment as a property of the abstract lists
held by emit. The payload premise supplies the fill of next-segment
trees, making the remaining history obligation explicit.
-/
import Contract.Proof.DnbFillPlan

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

def OwnFill (cf : Cfg) (isRoot : Bool) (h n : Nat) : Prop :=
  (isRoot = true → h ≠ 0 → 2 ≤ n) ∧ (isRoot = false → cf.m ≤ n)

def NodeFill (cf : Cfg) : (h : Nat) → Bool → Node h → Prop
  | 0, root, A => OwnFill cf root 0 A.length
  | h + 1, root, A => OwnFill cf root (h + 1) A.length ∧
      ∀ p ∈ kids A, NodeFill cf h false p.2

theorem NodeFill.own {h : Nat} {root : Bool} {A : Node h} (hf : NodeFill cf h root A) :
    OwnFill cf root h A.length := by
  cases h with
  | zero => exact hf
  | succ h => exact hf.1

theorem NodeFill.renameHead {h c : Nat} {root : Bool} {A : Node h}
    (hf : NodeFill cf h root A) : NodeFill cf h root (renameHead c A) := by
  cases h with
  | zero => simpa only [NodeFill, renameHead_length] using hf
  | succ h =>
    refine ⟨by simpa only [renameHead_length] using hf.1, ?_⟩
    intro p hp
    obtain ⟨p', hp', h2⟩ := renameHead_mem hp
    rw [← h2]
    exact hf.2 p' hp'

theorem nodeFill_view (hm2 : 2 ≤ cf.m) : ∀ (h : Nat) {g y : Nat} {root : Bool},
    Shaped cf s g h y → Filled cf s root y → NodeFill cf h root (view h s y)
  | 0, g, y, root, hs, hf => by
    obtain ⟨n, ho, _, _, _, _, _⟩ := shaped_getKey hs
    have hfn := filled_key hf ho
    simp only [view, ho, NodeFill]
    exact ⟨fun _ hz => by omega, fun hr => hfn.2.1 hm2 hr⟩
  | h + 1, g, y, root, hs, hf => by
    obtain ⟨n, ho, _, _, hl, _, _⟩ := shaped_getKey hs
    have hleaf : n.leaf = false := by simpa using hl
    have hkids := (shaped_inner hs ho).2
    have hfn := filled_key hf ho
    simp only [view, ho, NodeFill, ofKids, kids]
    refine ⟨?_, ?_⟩
    · change OwnFill cf root (h + 1) ((live n.ks).map (fun cy => (cy.1, view h s cy.2))).length
      rw [List.length_map]
      exact ⟨fun hr _ => hfn.1 hleaf hr, fun hr => hfn.2.1 hm2 hr⟩
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact nodeFill_view hm2 h (hkids q.1 q.2 hq) (hfn.2.2.2 q.1 q.2 hq hleaf)

/-- Emit's held abstract tree and the fill of its long payloads imply
the physical recursive fill predicate. No write-count premise is used. -/
theorem filled_of_holds : ∀ (h : Nat) {T : Tree} {g x : Nat} {root : Bool} {A : Node h},
    Holds cf T g h x A → NodeFill cf h root A →
    (∀ p ∈ content h A, isLong p.1 = true → Filled cf T true p.2) → Filled cf T root x
  | 0, T, g, x, root, A, hx, hf, hp => by
    cases hx with
    | @leaf _ n _ ho hl _ _ _ hlive =>
      refine Filled.key ho ?_ ?_ ?_ ?_
      · intro hn _; rw [hl] at hn; cases hn
      · intro _ hr; rw [hlive]; exact hf.2 hr
      · intro c y hmem _ hlong
        rw [hlive] at hmem
        exact hp (c, y) hmem hlong
      · intro _ _ _ hn; rw [hl] at hn; cases hn
  | h + 1, T, g, x, root, A, hx, hf, hp => by
    cases hx with
    | @inner _ _ n _ ho hl _ _ _ _ hcv hkids =>
      have hE := holdsE_of hcv hkids
      have hlen : (live n.ks).length = A.length := by
        calc (live n.ks).length = ((live n.ks).map (·.1)).length := (List.length_map _).symm
             _ = ((kids A).map (·.1)).length := congrArg List.length hcv
             _ = (kids A).length := List.length_map _
             _ = A.length := rfl
      refine Filled.key ho ?_ ?_ ?_ ?_
      · intro _ hr
        have := hf.1.1 hr (by omega)
        omega
      · intro _ hr
        have := hf.1.2 hr
        omega
      · intro _ _ _ hn; rw [hl] at hn; cases hn
      · intro c y hmem _
        obtain ⟨a, ha, hea⟩ := forall₂_exists hE (c, y) hmem
        exact filled_of_holds h hea.2 (hf.2 a ha)
          (fun p hp' => hp p (mem_content_succ ha hp'))

theorem nodeFill_cut_piece {h : Nat} {A Q : Node h} (hsub : Q.Sublist A)
    (hf : NodeFill cf h false A) (hmin : cf.m ≤ Q.length) : NodeFill cf h false Q := by
  cases h with
  | zero => simpa only [NodeFill, OwnFill, Bool.false_eq_true, false_implies, implies_true,
      and_true, true_implies, true_and] using hmin
  | succ h =>
    refine ⟨by simpa [OwnFill] using hmin, ?_⟩
    intro p hp
    exact hf.2 p (hsub.subset hp)

end Contract.PE
