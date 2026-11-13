/-
TP7's invariants at a run's last time from their parts (bergdb 024-12, TP6 and
TP7's `LatestInvOK`). The walk of the tree at t finds no fault
(`invOK_of_parts`) when:

* the space root is a key node (`RootKeyOK`, `RootRun.lean`);
* every key node is sound as it is (`KeyNodesOK`);
* the kinds and the live heights hold (`KindsAllOK`, `HeightLiveOK`);
* the reachable nodes meet the conditions on their live klongs: `NonEmptyOK`,
  `LeftmostOK`, `RootsOK` and `FillOK`;
* the order holds (`RangeAtOK`: putinv's `RangeOrder` from the space root).

The walk's fuel needs no premise. Along the walk's edges a node's level falls
(`walkVisit_key`), and the space root's level is at most `keyMax`, which is
below the fuel.

The nodes the walk reaches are `WalkVisit`'s, with the bounds and the flags the
walk gives them. They are in `nodesRootsAt` with their flag (`walkVisit_mem`).
The statements over `keyNodesAt` and `nodesRootsAt` therefore reach every node
the walk checks.
-/
import SIS.Tree.WalkNil
import SIS.Tree.InvConsequences
import SIS.Tree.KindsRun
import SIS.Tree.HeightsStep
import SIS.Tree.PutInvRange
import SIS.Tree.MergeProps
import SIS.Tree.RootRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The parts -/

/-- TP6's `RootsOK` (what RC leaves): at time t every reachable inner node
that is the root of its segment tree has two live klongs at least. -/
def RootsOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ q ∈ nodesRootsAt p P t, q.2 = true → ∀ n, keyNodeAt p P q.1 = some n → n.leaf = false →
    2 ≤ (n.liveAt t).length

/-- TP6's `RangeOK` (the order) at t: from the space root, every reachable key
node has its live compare values in the range its path gives it (putinv's
`RangeOrder`, on the key nodes of P). -/
def RangeAtOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ r, rootAt (viewOf P) t = some r → RangeOrder (keyNodeAt p P) t r

/-! ## The walk's visits -/

/-- The nodes the walk of the tree at t from r reaches, each with its depth
(the edges from r), the bounds and the flags the walk gives it. A child is
reached where the walk's kind checks pass: an inner node's key node of its
segment one height below it, a segment leaf's key node of the next segment
through a klong of a long segment. -/
inductive WalkVisit (p : Params) (v : View BVal) (t : Time) (r : NodeId) :
    Nat → NodeId → Nat → Option Nat → Bool → Bool → Prop
  | root : WalkVisit p v t r 0 r 0 none true true
  | inner (d : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat) (isRoot space : Bool)
      (nd : Node BVal) (c : Nat) (y : NodeId) (b : Option Nat) (ny : Node BVal) :
      WalkVisit p v t r d x lo hi isRoot space → v x = some nd → nd.isData = false →
      (nodeK p nd).leaf = false → ((c, y), b) ∈ childBounds ((nodeK p nd).liveAt t) hi →
      v y = some ny → ny.isData = false → p.segOf ny.level = p.segOf nd.level →
      p.heightOf ny.level + 1 = p.heightOf nd.level →
      WalkVisit p v t r (d + 1) y (if c == 0 then lo else c) b false space
  | seg (d : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat) (isRoot space : Bool)
      (nd : Node BVal) (c : Nat) (y : NodeId) (b : Option Nat) (ny : Node BVal) :
      WalkVisit p v t r d x lo hi isRoot space → v x = some nd → nd.isData = false →
      (nodeK p nd).leaf = true → ((c, y), b) ∈ childBounds ((nodeK p nd).liveAt t) hi →
      segLen c = 7 → v y = some ny → ny.isData = false →
      p.segOf ny.level = p.segOf nd.level + 1 →
      WalkVisit p v t r (d + 1) y 0 none true false

/-- What the walk checks at a node it reaches, and the kinds of the node's
children. -/
def VisitOK (p : Params) (v : View BVal) (t : Time) (d : Nat) (x : NodeId) (lo : Nat)
    (hi : Option Nat) (isRoot space : Bool) : Prop :=
  d < p.fuel ∧ ∃ nd, v x = some nd ∧ nd.isData = false ∧ CurrentOK p v nd ∧
    TimeOK p (nodeK p nd).leaf ((nodeK p nd).liveAt t) lo hi isRoot space ∧
    ∀ c y b, ((c, y), b) ∈ childBounds ((nodeK p nd).liveAt t) hi → ∀ ny, v y = some ny →
      ((nodeK p nd).leaf = false → ny.isData = false ∧ p.segOf ny.level = p.segOf nd.level ∧
        p.heightOf ny.level + 1 = p.heightOf nd.level) ∧
      ((nodeK p nd).leaf = true →
        (segLen c = 7 → ny.isData = false ∧ p.segOf ny.level = p.segOf nd.level + 1) ∧
        (segLen c ≠ 7 → ny.isData = true))

/-- The walk finds no fault at a node it reaches with the fuel left, when every
node it reaches passes its checks. -/
theorem walk_nil_of_visits (p : Params) (v : View BVal) (t : Time) (r : NodeId)
    (hok : ∀ d x lo hi b s, WalkVisit p v t r d x lo hi b s → VisitOK p v t d x lo hi b s) :
    ∀ f d x lo hi b s, WalkVisit p v t r d x lo hi b s → d + f = p.fuel →
      walk p v t f x lo hi b s = [] := by
  intro f
  induction f with
  | zero =>
    intro d x lo hi b s hv hf
    have := (hok d x lo hi b s hv).1
    omega
  | succ f ih =>
    intro d x lo hi b s hv hf
    obtain ⟨_, nd, hnd, hdat, hcur, htime, hkind⟩ := hok d x lo hi b s hv
    rw [walk_succ_eq_nil_iff p v t f x lo hi b s nd hnd hdat]
    refine ⟨hcur, htime, ?_⟩
    rintro ⟨⟨c, y⟩, b'⟩ hcb
    unfold walkChildFaults
    dsimp only
    cases hy : v y with
    | none =>
      split
      · split
        · split <;> simp_all
        · split <;> simp_all
      · split <;> simp_all
    | some ny =>
      obtain ⟨hin, hlf⟩ := hkind c y b' hcb ny hy
      cases hl : (nodeK p nd).leaf with
      | false =>
        obtain ⟨hd, hg, hh⟩ := hin hl
        have hv' := WalkVisit.inner d x lo hi b s nd c y b' ny hv hnd hdat hl hcb hy hd hg hh
        simp only [Bool.false_eq_true, ↓reduceIte, hd, hg, hh, bne_self_eq_false, Bool.or_self]
        exact ih (d + 1) y _ b' false s hv' (by omega)
      | true =>
        obtain ⟨hlong, hshort⟩ := hlf hl
        by_cases hs7 : segLen c = 7
        · obtain ⟨hd, hg⟩ := hlong hs7
          have hv' := WalkVisit.seg d x lo hi b s nd c y b' ny hv hnd hdat hl hcb hs7 hy hd hg
          simp only [↓reduceIte, hs7, beq_self_eq_true, hd, hg, bne_self_eq_false,
            Bool.false_eq_true]
          exact ih (d + 1) y 0 none true false hv' (by omega)
        · have hd := hshort hs7
          have hb : (segLen c == 7) = false := by simpa using hs7
          simp only [↓reduceIte, hb, hd, Bool.false_eq_true]

/-! ## The levels fall along the walk's edges -/

theorem keyMax_lt_fuel (p : Params) : p.keyMax < p.fuel := by
  unfold Params.keyMax Params.fuel
  have e : p.G * (p.H + 2) = p.G * (p.H + 1) + p.G := Nat.mul_succ p.G (p.H + 1)
  rw [Nat.add_mul, Nat.one_mul, e]
  omega

theorem level_div_le (p : Params) (a : Nat) (ha : a ≤ p.keyMax) : (a - 1) / (p.H + 1) ≤ p.G := by
  have h : (a - 1) / (p.H + 1) < p.G + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega), Nat.add_mul, Nat.one_mul]
    unfold Params.keyMax at ha
    omega
  omega

/-- An inner node's child of its segment one height below it is one level
below it. -/
theorem level_inner (p : Params) (a b : Nat) (ha : a ≤ p.keyMax) (hb : b ≤ p.keyMax)
    (hg : p.segOf b = p.segOf a) (hh : p.heightOf b + 1 = p.heightOf a) : b - 1 + 1 = a - 1 := by
  have hqa := level_div_le p a ha
  have hqb := level_div_le p b hb
  unfold Params.segOf at hg
  unfold Params.heightOf at hh
  have hq : (b - 1) / (p.H + 1) = (a - 1) / (p.H + 1) := by omega
  have hda := Nat.div_add_mod (a - 1) (p.H + 1)
  have hdb := Nat.div_add_mod (b - 1) (p.H + 1)
  rw [hq] at hdb
  omega

/-- A segment leaf's child of the next segment is below it. -/
theorem level_seg (p : Params) (a b : Nat) (ha : a ≤ p.keyMax) (hb : b ≤ p.keyMax)
    (h0 : p.heightOf a = 0) (hg : p.segOf b = p.segOf a + 1) : b - 1 + 1 ≤ a - 1 := by
  have hqa := level_div_le p a ha
  have hqb := level_div_le p b hb
  unfold Params.segOf at hg
  unfold Params.heightOf at h0
  have hq : (a - 1) / (p.H + 1) = (b - 1) / (p.H + 1) + 1 := by omega
  have hda := Nat.div_add_mod (a - 1) (p.H + 1)
  have hdb := Nat.div_add_mod (b - 1) (p.H + 1)
  have hm := Nat.mod_lt (b - 1) (show 0 < p.H + 1 by omega)
  rw [hq, Nat.mul_add, Nat.mul_one, h0] at hda
  omega

/-! ## The nodes the walk reaches -/

theorem walkVisit_zero (p : Params) (v : View BVal) (t : Time) (r x : NodeId) (lo : Nat)
    (hi : Option Nat) (b s : Bool) (hv : WalkVisit p v t r 0 x lo hi b s) :
    x = r ∧ b = true ∧ s = true := by
  cases hv
  exact ⟨rfl, rfl, rfl⟩

/-- Every node the walk reaches is a key node of P, its level falls by one at
least with every edge from the space root. -/
theorem walkVisit_key (p : Params) (P : Struct BVal) (t : Time) (r : NodeId) (ndr : Node BVal)
    (hgr : P.get? r = some ndr) (hdr : ndr.isData = false) (hlr : ndr.level ≤ p.keyMax)
    (hK : KindsAllOK p P) :
    ∀ d x lo hi b s, WalkVisit p (viewOf P) t r d x lo hi b s →
      ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax ∧
        nd.level - 1 + d ≤ ndr.level - 1 := by
  intro d x lo hi b s hv
  induction hv with
  | root => exact ⟨ndr, hgr, hdr, hlr, by omega⟩
  | inner d x lo hi isRoot space nd c y b ny _ hnd hdat hl hcb hy hd hg hh ih =>
    obtain ⟨nd', hx', _, hlv, hle⟩ := ih
    have hnd' : nd' = nd := by
      have : viewOf P x = some nd' := hx'
      rw [hnd] at this; exact (Option.some.inj this).symm
    subst hnd'
    have hmem : Klong.key c y ∈ klongsOf nd'.hist :=
      KNode.liveAt_key_mem (nodeK p nd') t c y (childBounds_fst _ _ _ _ hcb)
    have hh0 : p.heightOf nd'.level ≠ 0 := by simpa [nodeK] using hl
    obtain ⟨_, hylv, _⟩ := (hK x nd' hx' hdat hlv c y hmem ny hy).1 hh0
    refine ⟨ny, hy, hd, hylv, ?_⟩
    have := level_inner p nd'.level ny.level hlv hylv hg hh
    omega
  | seg d x lo hi isRoot space nd c y b ny _ hnd hdat hl hcb hs7 hy hd hg ih =>
    obtain ⟨nd', hx', _, hlv, hle⟩ := ih
    have hnd' : nd' = nd := by
      have : viewOf P x = some nd' := hx'
      rw [hnd] at this; exact (Option.some.inj this).symm
    subst hnd'
    have hmem : Klong.key c y ∈ klongsOf nd'.hist :=
      KNode.liveAt_key_mem (nodeK p nd') t c y (childBounds_fst _ _ _ _ hcb)
    have hh0 : p.heightOf nd'.level = 0 := by simpa [nodeK] using hl
    obtain ⟨_, hylv, _⟩ := ((hK x nd' hx' hdat hlv c y hmem ny hy).2 hh0).1 hs7
    refine ⟨ny, hy, hd, hylv, ?_⟩
    have := level_seg p nd'.level ny.level hlv hylv hh0 hg
    omega

theorem knodeOf_of_key (p : Params) (P : Struct BVal) (x : NodeId) (nd : Node BVal)
    (hx : P.get? x = some nd) (hd : nd.isData = false) (hl : nd.level ≤ p.keyMax) :
    knodeOf p (viewOf P) x = some (nodeK p nd) := by
  rw [← keyNodeAt_eq_knodeOf]; exact keyNodeAt_of p P x nd hx hd hl

/-- The nodes below a node the walk reaches, with their flags, are among the
space root's. -/
theorem walkVisit_mem (p : Params) (P : Struct BVal) (t : Time) (r : NodeId)
    (hkey : ∀ d x lo hi b s, WalkVisit p (viewOf P) t r d x lo hi b s →
      ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax ∧ d < p.fuel) :
    ∀ d x lo hi b s, WalkVisit p (viewOf P) t r d x lo hi b s →
      ∀ q ∈ nodesRoots p (viewOf P) t (p.fuel - d) x b, q ∈ nodesRoots p (viewOf P) t p.fuel r true := by
  intro d x lo hi b s hv
  induction hv with
  | root => intro q hq; exact hq
  | inner d x lo hi isRoot space nd c y b ny hv0 hnd hdat hl hcb hy hd hg hh ih =>
    have hv1 := WalkVisit.inner d x lo hi isRoot space nd c y b ny hv0 hnd hdat hl hcb hy hd hg hh
    obtain ⟨_, _, _, _, hf1⟩ := hkey _ _ _ _ _ _ hv1
    obtain ⟨nd', hx', hd', hlv', _⟩ := hkey _ _ _ _ _ _ hv0
    have hnd' : nd' = nd := by
      have : viewOf P x = some nd' := hx'
      rw [hnd] at this; exact (Option.some.inj this).symm
    subst hnd'
    intro q hq
    apply ih
    have he : p.fuel - d = (p.fuel - (d + 1)) + 1 := by omega
    rw [he, nodesRoots, knodeOf_of_key p P x nd' hx' hd' hlv']
    simp only [List.mem_cons]
    right
    refine List.mem_flatMap.mpr ⟨(c, y), childBounds_fst _ _ _ _ hcb, ?_⟩
    simp only [hl, Bool.false_eq_true, ↓reduceIte]
    exact hq
  | seg d x lo hi isRoot space nd c y b ny hv0 hnd hdat hl hcb hs7 hy hd hg ih =>
    have hv1 := WalkVisit.seg d x lo hi isRoot space nd c y b ny hv0 hnd hdat hl hcb hs7 hy hd hg
    obtain ⟨_, _, _, _, hf1⟩ := hkey _ _ _ _ _ _ hv1
    obtain ⟨nd', hx', hd', hlv', _⟩ := hkey _ _ _ _ _ _ hv0
    have hnd' : nd' = nd := by
      have : viewOf P x = some nd' := hx'
      rw [hnd] at this; exact (Option.some.inj this).symm
    subst hnd'
    intro q hq
    apply ih
    have he : p.fuel - d = (p.fuel - (d + 1)) + 1 := by omega
    rw [he, nodesRoots, knodeOf_of_key p P x nd' hx' hd' hlv']
    simp only [List.mem_cons]
    right
    refine List.mem_flatMap.mpr ⟨(c, y), childBounds_fst _ _ _ _ hcb, ?_⟩
    simp only [hl, hs7, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    exact hq

/-- The walk's visits are reached with their bounds in `RangeOrder`'s sense. -/
theorem walkVisit_reachR (p : Params) (P : Struct BVal) (t : Time) (r : NodeId)
    (hkey : ∀ d x lo hi b s, WalkVisit p (viewOf P) t r d x lo hi b s →
      ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax) :
    ∀ d x lo hi b s, WalkVisit p (viewOf P) t r d x lo hi b s → ReachR (keyNodeAt p P) t r x lo hi := by
  intro d x lo hi b s hv
  induction hv with
  | root => exact ReachR.root
  | inner d x lo hi isRoot space nd c y b ny hv0 hnd hdat hl hcb hy hd hg hh ih =>
    obtain ⟨nd', hx', hd', hlv'⟩ := hkey _ _ _ _ _ _ hv0
    have hnd' : nd' = nd := by
      have : viewOf P x = some nd' := hx'
      rw [hnd] at this; exact (Option.some.inj this).symm
    subst hnd'
    exact ReachR.inner x (nodeK p nd') lo hi c y b ih (keyNodeAt_of p P x nd' hx' hd' hlv') hl hcb
  | seg d x lo hi isRoot space nd c y b ny hv0 hnd hdat hl hcb hs7 hy hd hg ih =>
    obtain ⟨nd', hx', hd', hlv'⟩ := hkey _ _ _ _ _ _ hv0
    have hnd' : nd' = nd := by
      have : viewOf P x = some nd' := hx'
      rw [hnd] at this; exact (Option.some.inj this).symm
    subst hnd'
    exact ReachR.seg x (nodeK p nd') lo hi c y ih (keyNodeAt_of p P x nd' hx' hd' hlv') hl
      (childBounds_fst _ _ _ _ hcb)

theorem cvInRange_of_nodeRange (n : KNode) (t lo : Nat) (hi : Option Nat) (h : NodeRange n t lo hi) :
    ∀ q ∈ n.liveAt t, cvInRange n.leaf lo hi q.1 = true := by
  intro q hq
  obtain ⟨h1, h2⟩ := h q hq
  unfold cvInRange
  cases hl : n.leaf <;> cases hi <;> simp_all [UpperBound]

/-! ## The assembly -/

set_option maxHeartbeats 800000 in
/-- TP6 at time t from its parts: the space root a key node, every key node
sound as it is, the kinds and the live heights, and the reachable nodes'
conditions on their live klongs (`NonEmptyOK`, `LeftmostOK`, `RootsOK`,
`FillOK`) and the order (`RangeAtOK`). -/
theorem invOK_of_parts (p : Params) (P : Struct BVal) (t : Time)
    (hR : RootKeyOK p P t) (hKN : KeyNodesOK p P) (hK : KindsAllOK p P)
    (hH : HeightLiveOK p P t) (hNE : NonEmptyOK p P t) (hLM : LeftmostOK p P t)
    (hRT : RootsOK p P t) (hF : FillOK p P t) (hO : RangeAtOK p P t) : InvOK p P t := by
  obtain ⟨r, ndr, hr, hgr, hdr, hlr⟩ := hR
  have hkey := walkVisit_key p P t r ndr hgr hdr hlr hK
  have hfmax := keyMax_lt_fuel p
  have hkey' : ∀ d x lo hi b s, WalkVisit p (viewOf P) t r d x lo hi b s →
      ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax ∧ d < p.fuel := by
    intro d x lo hi b s hv
    obtain ⟨nd, h1, h2, h3, h4⟩ := hkey d x lo hi b s hv
    exact ⟨nd, h1, h2, h3, by omega⟩
  have hmem := walkVisit_mem p P t r hkey'
  have hreach := walkVisit_reachR p P t r
    (fun d x lo hi b s hv => by
      obtain ⟨nd, h1, h2, h3, _⟩ := hkey d x lo hi b s hv
      exact ⟨nd, h1, h2, h3⟩)
  have hroots : nodesRootsAt p P t = nodesRoots p (viewOf P) t p.fuel r true := by
    unfold nodesRootsAt; rw [hr]
  have hnodes : keyNodesAt p P t = (nodesRoots p (viewOf P) t p.fuel r true).map Prod.fst := by
    unfold keyNodesAt; rw [hr, nodesRoots_map_fst]
  unfold InvOK faultsAt
  rw [hr]
  refine walk_nil_of_visits p (viewOf P) t r ?_ p.fuel 0 r 0 none true true WalkVisit.root (by omega)
  intro d x lo hi b s hv
  obtain ⟨nd, hx, hd, hlv, hle⟩ := hkey d x lo hi b s hv
  have hkn : keyNodeAt p P x = some (nodeK p nd) := keyNodeAt_of p P x nd hx hd hlv
  have hmR : (x, b) ∈ nodesRootsAt p P t := by
    rw [hroots]
    apply hmem d x lo hi b s hv
    have he : p.fuel - d = (p.fuel - d - 1) + 1 := by omega
    rw [he, nodesRoots, knodeOf_of_key p P x nd hx hd hlv]
    exact List.mem_cons_self ..
  have hmK : x ∈ keyNodesAt p P t := by
    rw [hnodes, ← hroots]
    exact List.mem_map.mpr ⟨(x, b), hmR, rfl⟩
  refine ⟨by omega, nd, hx, hd, hKN x nd hx hd hlv, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- a live klong, but in a space root that is a segment leaf
    by_cases hE : (nodeK p nd).liveAt t = []
    · have hxr : x = r := Classical.byContradiction (fun hne =>
        hNE x hmK (nodeK p nd) hkn (by rw [hr]; intro h; exact hne (Option.some.inj h).symm) hE)
      subst hxr
      have hd0 : d = 0 := by
        rw [hgr] at hx; cases hx; omega
      subst hd0
      obtain ⟨_, hb, hs⟩ := walkVisit_zero p _ t x x lo hi b s hv
      subst hb hs
      cases hl : (nodeK p nd).leaf with
      | true => simp
      | false =>
        have h2 := hRT (x, true) hmR rfl (nodeK p nd) hkn hl
        rw [hE] at h2; simp at h2
    · have : ((nodeK p nd).liveAt t).isEmpty = false := by
        cases h' : (nodeK p nd).liveAt t with
        | nil => exact absurd h' hE
        | cons _ _ => rfl
      simp [this]
  · -- the empty key first in an inner node
    cases hl : (nodeK p nd).leaf with
    | true => simp
    | false =>
      have h := hLM x hmK (nodeK p nd) hkn hl
      simp [h]
  · -- two live klongs in an inner root
    cases hl : (nodeK p nd).leaf with
    | true => simp
    | false =>
      cases b with
      | false => simp
      | true =>
        have h := hRT (x, true) hmR rfl (nodeK p nd) hkn hl
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]
        omega
  · -- the fill
    cases hm : p.merges with
    | false => simp
    | true =>
      cases b with
      | true => simp
      | false =>
        have h := hF hm (x, false) hmR rfl (nodeK p nd) hkn
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]
        omega
  · -- the order
    exact cvInRange_of_nodeRange _ t lo hi (hO r hr x lo hi (nodeK p nd) (hreach d x lo hi b s hv) hkn)
  · -- the kinds of the children
    intro c y b' hcb ny hy
    have hmem' : Klong.key c y ∈ klongsOf nd.hist :=
      KNode.liveAt_key_mem (nodeK p nd) t c y (childBounds_fst _ _ _ _ hcb)
    have hKc := hK x nd hx hd hlv c y hmem' ny hy
    refine ⟨fun hl => ?_, fun hl => ?_⟩
    · have hh0 : p.heightOf nd.level ≠ 0 := by simpa [nodeK] using hl
      obtain ⟨h1, _, h3⟩ := hKc.1 hh0
      exact ⟨h1, h3, hH x hmK nd hx hh0 c y (childBounds_fst _ _ _ _ hcb) ny hy⟩
    · have hh0 : p.heightOf nd.level = 0 := by simpa [nodeK] using hl
      obtain ⟨hlong, hshort⟩ := hKc.2 hh0
      exact ⟨fun h7 => ⟨(hlong h7).1, (hlong h7).2.2⟩, hshort⟩

/-! ## At every run -/

/-- Every key node of P after a run within reach is sound as it is, from TP4
and the bound on dead klongs (as `invPreserved_of_parts` has it). -/
theorem keyNodesOK_of_pointers (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts)) (ts : List Tx) (hw : Within p ts) :
    KeyNodesOK p (treeRun p ts) := by
  have hM := mergeParamsOK_M p hp
  intro x nd hx hd hl
  have hHk := treeRun_keyHistOK p ts hw
    (fun k _ => hP _ (within_take p ts hw k))
    (fun k _ => (runLinksOK_of_pointers p (by omega) hP _ (within_take p ts hw k)).2.2)
  obtain ⟨hwf, hrt⟩ := hHk x nd hx hd hl
  have hk := keyNodeAt_of p _ x nd hx hd hl
  refine ⟨treeRun_sizeOK_of_pointers p hp hP ts hw x _ hk, hwf, hrt, ?_, hD ts hw x _ hk⟩
  intro c y hm
  obtain ⟨e, he, hv⟩ := klongsOf_key_mem nd.hist c y hm
  exact hP ts hw _ (mem_of_get? hx) e he y (by rw [hv]; simp [bptrs])

/-- `LatestInvOK` under valid parameters from TP4, the bound on dead klongs,
and at every run's last time: the live heights (`HeightLiveOK`, cost's),
`NonEmptyOK`, `RootsOK`, `FillOK` and the order (`RangeAtOK`, putinv's
`RangeOrder` on P). The space root, the kinds and `LeftmostOK` come from TP4
(`treeRun_rootKeyOK`, `treeRun_kindsAllOK`, `leftmostOK_latest`). -/
theorem latestInvOK_of_parts (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hH : ∀ ts, Within p ts → HeightLiveOK p (treeRun p ts) ts.length)
    (hNE : ∀ ts, Within p ts → NonEmptyOK p (treeRun p ts) ts.length)
    (hRT : ∀ ts, Within p ts → RootsOK p (treeRun p ts) ts.length)
    (hF : ∀ ts, Within p ts → FillOK p (treeRun p ts) ts.length)
    (hO : ∀ ts, Within p ts → RangeAtOK p (treeRun p ts) ts.length) : LatestInvOK p := by
  intro ts hw
  have hM := mergeParamsOK_M p hp
  exact invOK_of_parts p _ _ (treeRun_rootKeyOK p (by omega) hP ts hw _ (Nat.le_refl _))
    (keyNodesOK_of_pointers p hp hP hD ts hw)
    (treeRun_kindsAllOK p (by omega) hP ts hw) (hH ts hw) (hNE ts hw)
    (leftmostOK_latest p hp hP ts hw) (hRT ts hw) (hF ts hw) (hO ts hw)

/-- TP7 under valid parameters from its open parts: TP4, the bound on dead
klongs (void for theta 0), and at every run's last time `HeightLiveOK`,
`NonEmptyOK`, `RootsOK`, `FillOK` and `RangeAtOK`. -/
theorem invPreserved_of_open (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hH : ∀ ts, Within p ts → HeightLiveOK p (treeRun p ts) ts.length)
    (hNE : ∀ ts, Within p ts → NonEmptyOK p (treeRun p ts) ts.length)
    (hRT : ∀ ts, Within p ts → RootsOK p (treeRun p ts) ts.length)
    (hF : ∀ ts, Within p ts → FillOK p (treeRun p ts) ts.length)
    (hO : ∀ ts, Within p ts → RangeAtOK p (treeRun p ts) ts.length) : InvPreserved p :=
  invPreserved_of_latest_pointers p hp (latestInvOK_of_parts p hp hP hD hH hNE hRT hF hO) hP hD

/-! ## The parts are not void

A run within reach with the merges on (node size 8 with record format 7's
thresholds: m = 2, h = c = 4): thirty puts, then twenty-two deletes that merge
the tree down from 14 key nodes to 3. At its last time the walk finds no fault,
and the Bool forms of `NonEmptyOK`, `RootsOK`, `FillOK` and `RootKeyOK` hold,
with two nodes that are not segment roots for the fill to check. -/

/-- `Within p ts` as a Bool. -/
def invAsmWithin (p : Params) (ts : List Tx) : Bool :=
  ts.all (fun tx => tx.sorted && tx.wf) &&
  (List.range ts.length).all (fun j =>
    match ts[j]? with
    | none => false
    | some tx =>
      (treeRun p (ts.take j)).all (fun q => decide (q.1 < tx.base)) &&
      isOk (exec? p tx (j + 1) (view (treeSpec p) (treeRun p (ts.take j)) j)))

/-- `NonEmptyOK`, `RootsOK`, `FillOK` and `RootKeyOK` as Bools. -/
def invAsmParts (p : Params) (P : Struct BVal) (t : Time) : Bool :=
  let ne := (keyNodesAt p P t).all (fun x => rootAt (viewOf P) t == some x ||
    match keyNodeAt p P x with
    | some n => !(n.liveAt t).isEmpty
    | none => true)
  let roots := (nodesRootsAt p P t).all (fun q => !q.2 ||
    match keyNodeAt p P q.1 with
    | some n => n.leaf || decide (2 ≤ (n.liveAt t).length)
    | none => true)
  let fill := !p.merges || (nodesRootsAt p P t).all (fun q => q.2 ||
    match keyNodeAt p P q.1 with
    | some n => decide (p.mergeBelow ≤ (n.liveAt t).length)
    | none => true)
  let rootKey := match rootAt (viewOf P) t with
    | some r => match P.get? r with
      | some nd => !nd.isData && decide (nd.level ≤ p.keyMax)
      | none => false
    | none => false
  ne && roots && fill && rootKey

def invAsmP : Params := ({M := 8, G := 1, H := 2} : Params).withMerges
def invAsmTs : List Tx :=
  [{base := 1000, ops := (List.range 30).map (fun j => .put [64*j+8] (j+1))},
   {base := 2000, ops := (List.range 22).map (fun j => .del [64*j+8])}]

/-- `MergeParamsOK invAsmP`'s inequalities, the run within reach, the parts
and no fault at its last time, a merged tree with two nodes under the root. -/
def invAsmCheck : Bool :=
  let p := invAsmP
  let P := treeRun p invAsmTs
  let t := invAsmTs.length
  decide (2 ≤ p.mergeBelow ∧ p.mergeBelow ≤ (p.mergeMax + 1) / 2 ∧
    p.mergeBelow ≤ p.splitAbove / 2 ∧ p.mergeMax + 2 ≤ p.M ∧ p.splitAbove + 2 ≤ p.M ∧
    (p.mergeBelow + p.M - 1) / 2 + 1 ≤ p.M) &&
  invAsmWithin p invAsmTs && invAsmParts p P t && (faultsAt p (viewOf P) t).isEmpty &&
  decide (14 ≤ (keyNodesAt p (treeRun p (invAsmTs.take 1)) 1).length) &&
  decide (((nodesRootsAt p P t).filter (fun q => !q.2)).length = 2)

#guard invAsmCheck

end SIS.Tree
