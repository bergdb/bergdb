import SIS.Tree.WalkEdges
import SIS.Tree.RunEncoding

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The facts needed for scan fuel: finite key-node depth, compare values
strictly between the sentinels, and nonempty key children. Missing children
or values terminate the reader immediately and need no fuel assumption. -/
def ScanTree (p : Params) (v : View BVal) (t : Time) : Nat → NodeId → Prop
  | 0, _ => False
  | f + 1, x => ∃ n, knodeOf p v x = some n ∧
      (∀ q ∈ n.liveAt t, cvLo < (q.1 : Int) ∧ (q.1 : Int) < cvHi) ∧
      ∀ q ∈ n.liveAt t, ∀ nd, v q.2 = some nd → nd.isData = false →
        ScanTree p v t f q.2 ∧
          ∃ child, knodeOf p v q.2 = some child ∧ child.liveAt t ≠ []

/-- Each frame has enough remaining depth after accounting for its ancestors.
No relationship between their cursor compare values is needed for fuel. -/
def ScanChain (p : Params) (v : View BVal) (t : Time) (bound : Nat) :
    List (NodeId × Int) → Prop
  | [] => True
  | (x, _) :: rest => ∃ depth, ScanTree p v t depth x ∧
      depth + rest.length ≤ bound ∧ ScanChain p v t bound rest

theorem scanTree_pos (p : Params) (v : View BVal) (t depth x : Nat)
    (h : ScanTree p v t depth x) : 0 < depth := by
  cases depth with
  | zero => exact h.elim
  | succ f => omega

theorem scanChain_length (p : Params) (v : View BVal) (t bound : Nat)
    (links : List (NodeId × Int)) (h : ScanChain p v t bound links) :
    links.length ≤ bound := by
  cases links with
  | nil => simp
  | cons q rest =>
    obtain ⟨depth, hd, hb, _⟩ := h
    have hp := scanTree_pos p v t depth q.1 hd
    simp only [List.length_cons]
    omega

/-- The full invariant walk supplies finite depth and nonempty descendants.
Compare-value encoding is independent of TP7 and is proved for actual runs. -/
theorem scanTree_of_walk (p : Params) (P : Struct BVal) (t f : Nat)
    (hkinds : HighKindsOK p P) (henc : ViewEncoded (viewOf P))
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) :
    ScanTree p (viewOf P) t f x := by
  induction f generalizing x lo hi isRoot space with
  | zero => simp only [walk, List.cons_ne_nil] at hw
  | succ f ih =>
    cases hx : P.get? x with
    | none => simp [walk, viewOf, hx] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp [walk, viewOf, hx, hd] at hw
      | false =>
        have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hkinds hx hd hw
        let n : KNode := ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩
        have hn : knodeOf p (viewOf P) x = some n := by
          simp [knodeOf, viewOf, hx, hd, Nat.not_lt_of_ge hl, n]
        refine ⟨n, hn, ?_, ?_⟩
        · intro q hq
          have he := ((knodeOf_encoded p _ x n henc hn).liveAt n t) q hq
          dsimp only [CompareValueOK] at he
          dsimp only [cvLo, cvHi]
          omega
        · intro q hq ny hy hny
          obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi q hq
          have hc := List.flatMap_eq_nil_iff.mp
            (walk_child_faults_nil p (viewOf P) t f x lo hi isRoot space nd hx hd hw) (q,b) hb
          change walkChildFaults p (viewOf P) t f x n (p.segOf nd.level)
            (p.heightOf nd.level) lo space (q,b) = [] at hc
          have hchild : ∃ lo' hi' root' space',
              walk p (viewOf P) t f q.2 lo' hi' root' space' = [] ∧
              (space' && root') = false := by
            cases hleaf : n.leaf with
            | true =>
              by_cases hlen : segLen q.1 = 7
              · simp only [walkChildFaults, hleaf, hlen, beq_self_eq_true,
                  ↓reduceIte, hy, hny, Bool.false_eq_true] at hc
                split at hc
                · cases hc
                · exact ⟨0, none, true, false, hc, rfl⟩
              · simp [walkChildFaults, hleaf, hlen, hy, hny] at hc
            | false =>
              simp only [walkChildFaults, hleaf, Bool.false_eq_true, ↓reduceIte,
                hy, hny] at hc
              split at hc
              · cases hc
              · exact ⟨_, _, false, space, hc, by simp⟩
          obtain ⟨lo', hi', root', space', hw', hnotspace⟩ := hchild
          have hs := ih q.2 lo' hi' root' space' hw'
          refine ⟨hs, ?_⟩
          cases f with
          | zero => exact hs.elim
          | succ f =>
            have hl' := highKindsOK_walk_level p P t f q.2 lo' hi' root' space' ny
              hkinds hy hny hw'
            let child : KNode := ⟨p.heightOf ny.level == 0, klongsOf ny.hist⟩
            refine ⟨child, ?_, ?_⟩
            · simp [knodeOf, hy, hny, Nat.not_lt_of_ge hl', child]
            · exact walk_current_nonempty p _ t f q.2 lo' hi' root' space' ny hy hny hw' hnotspace

end SIS.Tree
