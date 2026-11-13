import SIS.Tree.ScanSetup
import SIS.Tree.ReadExtension

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A set of reader-visible key nodes closed under live edges. Every edge
names either an available value or another key node in the set. -/
def ReadClosed (p : Params) (v : View BVal) (t : Time) (S : NodeId → Prop) : Prop :=
  ∀ x, S x → ∃ n, knodeOf p v x = some n ∧
    ∀ q ∈ n.liveAt t, (∃ h, valueOf v q.2 = some h) ∨ S q.2

/-- Nodes admitting a fault-free invariant walk, at any depth and range. -/
def WalkNode (p : Params) (P : Struct BVal) (t : Time) (x : NodeId) : Prop :=
  ∃ f lo hi isRoot space, walk p (viewOf P) t f x lo hi isRoot space = []

theorem readClosed_walkNode (p : Params) (P : Struct BVal) (t : Time)
    (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P) :
    ReadClosed p (viewOf P) t (WalkNode p P t) := by
  intro x ⟨f, lo, hi, isRoot, space, hw⟩
  cases f with
  | zero => simp [walk] at hw
  | succ f =>
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
        refine ⟨n, hn, ?_⟩
        intro q hq
        obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi q hq
        have he := walk_edge_info p P t f x lo hi isRoot space nd hdata hx hd hw q b hb
        change ((n.leaf && segLen q.1 != 7) = true → _) ∧
          ((n.leaf && segLen q.1 != 7) = false → _) at he
        cases ht : n.leaf && segLen q.1 != 7 with
        | true => exact Or.inl (he.1 ht)
        | false => exact Or.inr ⟨f, _, _, _, _, he.2 ht⟩

/-- All chain frames belong to a closed set of old reader-visible nodes. -/
def ReadChain (S : NodeId → Prop) (links : List (NodeId × Int)) : Prop :=
  ∀ q ∈ links, S q.1

@[simp] theorem readChain_nil (S : NodeId → Prop) : ReadChain S [] := by
  simp [ReadChain]

@[simp] theorem readChain_cons (S : NodeId → Prop) (x : NodeId) (lc : Int)
    (rest : List (NodeId × Int)) :
    ReadChain S ((x,lc) :: rest) ↔ S x ∧ ReadChain S rest := by
  simp [ReadChain]

theorem knodeOf_view (p : Params) (v : View BVal) (x : NodeId) (n : KNode)
    (hn : knodeOf p v x = some n) :
    ∃ nd, v x = some nd ∧ nd.isData = false := by
  unfold knodeOf at hn
  cases hx : v x with
  | none => simp [hx] at hn
  | some nd =>
    simp only [hx] at hn
    split at hn
    · cases hn
    · rename_i h
      exact ⟨nd, rfl, by simpa using (Bool.or_eq_false_iff.mp (Bool.eq_false_iff.mpr h)).1⟩

theorem valueOf_view (v : View BVal) (x h : Nat) (hv : valueOf v x = some h) :
    ∃ nd, v x = some nd ∧ nd.isData = true := by
  unfold valueOf at hv
  cases hx : v x with
  | none => simp [hx] at hv
  | some nd =>
    cases hd : nd.isData with
    | false => simp [hx, hd] at hv
    | true => exact ⟨nd, rfl, hd⟩

theorem scanChoice_of_prefix (a b : KNode) (t : Time) (req : ScanReq)
    (first eqMatch : Bool) (lc : Int) (he : prefixAt a.ks t = prefixAt b.ks t) :
    scanChoice a t req first eqMatch lc = scanChoice b t req first eqMatch lc := by
  unfold scanChoice
  split <;> split <;> exact a.searchBy_eq_of_prefix b t _ he

theorem scanPop_of_readExtension (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (S : NodeId → Prop)
    (hclosed : ReadClosed p (viewOf P) t S) (ch : Chain) (rest : List (NodeId × Int))
    (hc : ReadChain S rest) : scanPop p (viewOf Q) ch rest = scanPop p (viewOf P) ch rest := by
  cases rest with
  | nil => rfl
  | cons q rest =>
    obtain ⟨n, hn, _⟩ := hclosed q.1 ((readChain_cons S q.1 q.2 rest).mp hc).1
    obtain ⟨next, hn', hleaf, _⟩ := hext.key q.1 n hn
    simp only [scanPop, hn, hn', Option.map_some, hleaf]

/-- One next-step call reads the same old snapshot after an extension,
and leaves every frame inside the same closed set. Fuel is arbitrary. -/
theorem nextGo_of_readClosed (p : Params) (P Q : Struct BVal) (t : Time)
    (hext : ReadExtension p t P Q) (S : NodeId → Prop)
    (hclosed : ReadClosed p (viewOf P) t S) (req : ScanReq) (fuel : Nat) (ch : Chain)
    (hc : ReadChain S ch.links) :
    nextGo p (viewOf Q) t req fuel ch = nextGo p (viewOf P) t req fuel ch ∧
      ReadChain S (nextGo p (viewOf P) t req fuel ch).2.links := by
  induction fuel generalizing ch with
  | zero => exact ⟨rfl, readChain_nil S⟩
  | succ fuel ih =>
    cases hl : ch.links with
    | nil => simp [nextGo, hl]
    | cons q rest =>
      rcases q with ⟨x, lc⟩
      rw [hl, readChain_cons] at hc
      obtain ⟨n, hn, hchildren⟩ := hclosed x hc.1
      obtain ⟨next, hn', hleaf, hpre⟩ := hext.key x n hn
      rw [nextGo_step p (viewOf Q) t req fuel ch x lc rest hl next hn',
        nextGo_step p (viewOf P) t req fuel ch x lc rest hl n hn]
      rw [scanChoice_of_prefix next n t req ch.first ch.eqMatch lc hpre]
      cases hf : scanChoice n t req ch.first ch.eqMatch lc with
      | none =>
        rw [scanPop_of_readExtension p P Q t hext S hclosed ch rest hc.2]
        exact ih (scanPop p (viewOf P) ch rest) hc.2
      | some fd =>
        have hmem := scanChoice_mem n t req ch.first ch.eqMatch lc fd hf
        simp only
        by_cases hpast : scanPast req ch fd = true
        · simp [hpast, Chain.done]
        · simp only [hpast]
          rcases hchildren (fd.c, fd.y) hmem with ⟨value, hv⟩ | hchild
          · have hv' := hext.value fd.y value hv
            obtain ⟨nd, hy, hd⟩ := valueOf_view _ fd.y value hv
            obtain ⟨nd', hy', hd'⟩ := valueOf_view _ fd.y value hv'
            simp only [hy, hy', hd, hd', ↓reduceIte, hv, hv']
            exact ⟨trivial, (readChain_cons S x (fd.c : Int) rest).mpr hc⟩
          · obtain ⟨child, hcn, _⟩ := hclosed fd.y hchild
            obtain ⟨child', hcn', _, _⟩ := hext.key fd.y child hcn
            obtain ⟨nd, hy, hd⟩ := knodeOf_view p _ fd.y child hcn
            obtain ⟨nd', hy', hd'⟩ := knodeOf_view p _ fd.y child' hcn'
            simp only [hy, hy', hd, hd', Bool.false_eq_true, ↓reduceIte]
            have hpush : scanPush req ch next x rest fd = scanPush req ch n x rest fd := by
              simp only [scanPush, hleaf]
            rw [hpush]
            apply ih
            exact (readChain_cons S fd.y _ _).mpr
              ⟨hchild, (readChain_cons S x _ _).mpr hc⟩

end SIS.Tree
