import SIS.Tree.GetCascadeGen
import SIS.Tree.GetSegLeaf
import SIS.Tree.WriterTreeDepth

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Splits in place at any depth (bergdb 024-12, TP10): the step of the
induction over the writer's `appendKlongs` for a node that the transaction made
and that space splits in place below an inner parent. The node keeps the first
half, a new node the second, and the parent gets a klong to the second. -/

/-- `getEqR_split_inner` with F possibly L (the split in place): the links
reached avoid F only where they avoid L. -/
theorem getEqR_split_inner' (Nm N2 : NodeId → Option KNode) (t : Time) (r0 L q F S : NodeId)
    (qn qn2 m f s : KNode) (sc : Nat)
    (hNq : Nm q = some qn) (hql : qn.leaf = false) (hN2q : N2 q = some qn2)
    (hq2l : qn2.leaf = false)
    (hqsearch : ∀ c : Nat, (qn2.searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = L then (if c < sc then F else S) else fd.y))
    (hNmL : Nm L = some m) (hml : m.leaf = false) (hrL : ReachS Nm t r0 L)
    (hN2F : N2 F = some f) (hfl : f.leaf = false) (hN2S : N2 S = some s) (hsl : s.leaf = false)
    (hsF : ∀ c : Nat, c < sc → (f.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y))
    (hsS : ∀ c : Nat, sc ≤ c → (s.searchLte t c).map (·.y) = (m.searchLte t c).map (·.y))
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      (z ≠ L → z ≠ F) ∧ z ≠ S) (hLq : L ≠ q) (c : Nat) :
    ∀ (fu : Nat), (∀ (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fu x = getEqR Nm t c fu x) ∧
      getEqR N2 t c fu (if c < sc then F else S) = getEqR Nm t c fu L := by
  intro fu
  induction fu with
  | zero => exact ⟨fun _ _ _ _ _ => rfl, rfl⟩
  | succ fu ih =>
    obtain ⟨ihP, ihQ⟩ := ih
    refine ⟨?_, ?_⟩
    · intro x hx hxL hxF hxS
      by_cases hxq : x = q
      · subst hxq
        simp only [getEqR, hNq, hN2q, hql, hq2l, Bool.false_eq_true, ↓reduceIte]
        have hs := hqsearch c
        cases h1 : qn.searchLte t c with
        | none =>
          rw [h1] at hs
          cases h2 : qn2.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at hs; cases hs
        | some fd =>
          rw [h1] at hs
          cases h2 : qn2.searchLte t c with
          | none => rw [h2] at hs; cases hs
          | some fd2 =>
            rw [h2] at hs
            simp only [Option.map_some, Option.some.injEq] at hs
            simp only
            have hmem := KNode.searchLte_mem qn t c fd h1
            have hrfd : ReachS Nm t r0 fd.y := ReachS.step x qn fd.c fd.y hx hNq hmem
            by_cases hL : fd.y = L
            · rw [hL] at hs
              simp only [↓reduceIte] at hs
              rw [hs, hL]
              exact ihQ
            · simp only [hL, ↓reduceIte] at hs
              rw [hs]
              have hfs := hnotFS x qn fd.c fd.y hx hNq hmem
              exact ihP fd.y hrfd hL (hfs.1 hL) hfs.2
      · have he := hsame x hxL hxq hxF hxS
        simp only [getEqR, he]
        cases hn : Nm x with
        | none => rfl
        | some xn =>
          simp only
          split
          · rfl
          · cases h1 : xn.searchLte t c with
            | none => rfl
            | some fd =>
              simp only
              have hmem := KNode.searchLte_mem xn t c fd h1
              have hrfd : ReachS Nm t r0 fd.y := ReachS.step x xn fd.c fd.y hx hn hmem
              have hfs := hnotFS x xn fd.c fd.y hx hn hmem
              have hL' := hnotL x xn fd.c fd.y hx hxq hn hmem
              exact ihP fd.y hrfd hL' (hfs.1 hL') hfs.2
    · -- the halves search as L does, then the same child
      have hchild : ∀ fd : Found, m.searchLte t c = some fd →
          getEqR N2 t c fu fd.y = getEqR Nm t c fu fd.y := by
        intro fd hfd
        have hmem := KNode.searchLte_mem m t c fd hfd
        have hfs := hnotFS L m fd.c fd.y hrL hNmL hmem
        have hL' := hnotL L m fd.c fd.y hrL hLq hNmL hmem
        exact ihP fd.y (ReachS.step L m fd.c fd.y hrL hNmL hmem) hL' (hfs.1 hL') hfs.2
      by_cases hc : c < sc
      · simp only [hc, ↓reduceIte, getEqR, hN2F, hfl, hNmL, hml, Bool.false_eq_true]
        have he := hsF c hc
        cases h1 : m.searchLte t c with
        | none =>
          rw [h1] at he
          cases h2 : f.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at he; cases he
        | some fd =>
          rw [h1] at he
          cases h2 : f.searchLte t c with
          | none => rw [h2] at he; cases he
          | some fd2 =>
            rw [h2] at he
            simp only [Option.map_some, Option.some.injEq] at he
            simp only
            rw [he]
            exact hchild fd h1
      · simp only [hc, ↓reduceIte, getEqR, hN2S, hsl, hNmL, hml, Bool.false_eq_true]
        have he := hsS c (by omega)
        cases h1 : m.searchLte t c with
        | none =>
          rw [h1] at he
          cases h2 : s.searchLte t c with
          | none => rfl
          | some _ => rw [h2] at he; cases he
        | some fd =>
          rw [h1] at he
          cases h2 : s.searchLte t c with
          | none => rw [h2] at he; cases he
          | some fd2 =>
            rw [h2] at he
            simp only [Option.map_some, Option.some.injEq] at he
            simp only
            rw [he]
            exact hchild fd h1

/-- The parent's search after a split in place: its klong K to x routes below
sc to x and from sc to S. -/
theorem splitParentInPlace_search_tree (V : NodeId → Option KNode) (t : Time) (r q x S : NodeId)
    (qn : KNode) (K sc : Nat) (hT : TreeOK V t r) (hVq : V q = some qn) (hrq : ReachS V t r q)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hKx : (K, x) ∈ qn.liveAt t) (hKsc : K ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ qn.live → c' ≤ K ∨ sc < c') :
    ∀ c : Nat, ((qn.add t (.key sc S)).searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = x then (if c < sc then x else S) else fd.y) := by
  intro c
  have hk1 : (K, x) ∈ qn.live := by rw [← KNode.liveAt_of_times qn t hqt]; exact hKx
  have hrqT := reachS_tReach V t r q hrq
  have hA := KNode.splitParentInPlace_searchLte qn t K sc x S hqwf hqt hk1 hKsc hgap c
  rw [hA]
  cases hs : qn.searchLte t c with
  | none => rfl
  | some fd =>
    simp only [Option.map_some, Option.some.injEq]
    have hmemfd := KNode.searchLte_mem qn t c fd hs
    have hyx : fd.y = x ↔ fd.c = K := by
      constructor
      · intro hy
        rw [hy] at hmemfd
        exact (hT.oneLink q fd.c q K x hrqT hrqT ⟨qn, hVq, hmemfd⟩ ⟨qn, hVq, hKx⟩).2
      · intro hc
        rw [KNode.liveAt_of_times qn t hqt, hc] at hmemfd
        exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup qn) hmemfd).symm.trans
          (lookup_some_of_mem (KNode.live_keys_nodup qn) hk1))
    by_cases hc : fd.c = K
    · simp only [hc, ↓reduceIte, hyx.mpr hc, Int.ofNat_lt]
    · have hy : ¬ fd.y = x := fun h => hc (hyx.mp h)
      simp only [hc, ↓reduceIte, hy]

/-- The reading through a space split in place at one level: in the virtual map
V the node x holds `xv`; in A x holds the first half f, the second half s is at
S, and x's parent q gets a klong sc to S. The halves search as `xv` below sc and
from sc on. If V is a tree from r, the readings agree. -/
theorem getFromR_spaceInPlaceLevel (V A : NodeId → Option KNode) (Val : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (r q x S : NodeId) (qn xv f s : KNode) (K sc : Nat)
    (hT : TreeOK V t r) (hwfV : ∀ z zn, ReachS V t r z → V z = some zn → klongsWf zn.ks = true)
    (hVq : V q = some qn) (hrq : ReachS V t r q) (hql : qn.leaf = false)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hKx : (K, x) ∈ qn.liveAt t) (hqx : q ≠ x) (hKsc : K ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ qn.live → c' ≤ K ∨ sc < c')
    (hVx : V x = some xv) (hVS : V S = none)
    (hnoS : ∀ u c z, ReachS V t r u → TLink V t u c z → z ≠ S)
    (hAx : A x = some f) (hAS : A S = some s) (hfl : f.leaf = xv.leaf) (hsl : s.leaf = xv.leaf)
    (hleafF : xv.leaf = true → ∀ c, c < sc → (f.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hleafS : xv.leaf = true → ∀ c, sc ≤ c → (s.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hinF : xv.leaf = false → ∀ c : Nat, c < sc →
      (f.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hinS : xv.leaf = false → ∀ c : Nat, sc ≤ c →
      (s.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hAq : A q = some (qn.add t (.key sc S)))
    (hA : ∀ z, z ≠ x → z ≠ q → z ≠ S → A z = V z)
    (hrx : r ≠ x) (hrS : r ≠ S) :
    ∀ key, getFromR A Val t fuel key r = getFromR V Val t fuel key r := by
  have hSx : S ≠ x := fun h => by rw [h, hVx] at hVS; cases hVS
  have hrqT := reachS_tReach V t r q hrq
  have hrx' : ReachS V t r x := ReachS.step q qn K x hrq hVq hKx
  have hnotL : ∀ z zn c y, ReachS V t r z → z ≠ q → V z = some zn → (c, y) ∈ zn.liveAt t →
      y ≠ x := by
    intro z zn c y hz hzq hzn hy hyx
    subst hyx
    exact hzq (hT.oneLink z c q K y (reachS_tReach V t r z hz) hrqT ⟨zn, hzn, hy⟩ ⟨qn, hVq, hKx⟩).1
  have hnotFS : ∀ z zn c y, ReachS V t r z → V z = some zn → (c, y) ∈ zn.liveAt t →
      (y ≠ x → y ≠ x) ∧ y ≠ S := fun z zn c y hz hzn hy => ⟨fun h => h, hnoS z c y hz ⟨zn, hzn, hy⟩⟩
  have hq2l : (qn.add t (.key sc S)).leaf = false := by
    rw [KNode.add_leaf]; exact hql
  have hqsearch := splitParentInPlace_search_tree V t r q x S qn K sc hT hVq hrq hqwf hqt hKx hKsc hgap
  have hsame : ∀ z, z ≠ x → z ≠ q → z ≠ x → z ≠ S → A z = V z :=
    fun z h1 h2 _ h4 => hA z h1 h2 h4
  have hget : ∀ c (z : NodeId), ReachS V t r z → z ≠ x → z ≠ x → z ≠ S →
      getEqR A t c fuel z = getEqR V t c fuel z := by
    intro c z hz hzx _ hzS
    cases hxl : xv.leaf with
    | true =>
      exact getEqR_split V A t r x q x S qn _ xv f s sc hVq hql hAq hq2l hqsearch hVx hxl hAx
        (by rw [hfl, hxl]) hAS (by rw [hsl, hxl]) (hleafF hxl) (hleafS hxl) hsame hnotL
        hnotFS c fuel z hz hzx hzx hzS
    | false =>
      exact (getEqR_split_inner' V A t r x q x S qn _ xv f s sc hVq hql hAq hq2l hqsearch hVx hxl
        hrx' hAx (by rw [hfl, hxl]) hAS (by rw [hsl, hxl]) (hinF hxl) (hinS hxl) hsame hnotL
        hnotFS (fun h => hqx h.symm) c fuel).1 z hz hzx hzx hzS
  intro key
  exact getFromR_split V A Val t fuel r x q x S hwfV hget hsame (by rw [hAq, hVq]; rfl) hnotL
    (fun xn c z hxn _ hxl => by rw [hVq] at hxn; cases hxn; rw [hql] at hxl; cases hxl)
    hnotFS key r ReachS.root hrx hrx hrS

/-! ## A node's tree read from another node with the same searches -/

/-- The visits of a descent all carry its compare value. -/
theorem eqVisits_snd (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x : NodeId) (q : NodeId × Nat), q ∈ eqVisits N t cv f x → q.2 = cv := by
  intro f
  induction f with
  | zero => intro x q h; simp [eqVisits] at h
  | succ f ih =>
    intro x q h
    simp only [eqVisits, List.mem_cons] at h
    rcases h with h | h
    · rw [h]
    · cases hn : N x with
      | none => rw [hn] at h; cases h
      | some n =>
        rw [hn] at h
        simp only at h
        split at h
        · cases h
        · cases hs : n.searchLte t cv with
          | none => rw [hs] at h; cases h
          | some fd => rw [hs] at h; exact ih fd.y q h

/-- The reading from Y in A is the reading from x in V when Y's node searches
as x's and A agrees with V on the nodes below x, which do not name x. -/
theorem getFromR_rename_root (V A : NodeId → Option KNode) (Val : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (x Y : NodeId) (xv l : KNode)
    (hVx : V x = some xv) (hAY : A Y = some l) (hll : l.leaf = xv.leaf)
    (hEq : xv.leaf = true → ∀ c, (l.searchEq t c).map (·.y) = (xv.searchEq t c).map (·.y))
    (hLte : xv.leaf = false → ∀ c : Nat, (l.searchLte t c).map (·.y) = (xv.searchLte t c).map (·.y))
    (hwf : ∀ z zn, ReachS V t x z → V z = some zn → klongsWf zn.ks = true)
    (hagree : ∀ z, ReachS V t x z → z ≠ x → A z = V z)
    (hnox : ∀ z zn c, ReachS V t x z → V z = some zn → (c, x) ∉ zn.liveAt t) :
    ∀ key, getFromR A Val t fuel key Y = getFromR V Val t fuel key x := by
  -- the nodes below a node other than x are not x
  have hbelow : ∀ y z, ReachS V t x y → y ≠ x → ReachS V t y z → ReachS V t x z ∧ z ≠ x := by
    intro y z hy hyx hz
    refine ⟨reachS_trans V t x y hy z hz, ?_⟩
    cases hz with
    | root => exact hyx
    | step u un c _ hu hun hmem =>
      intro he
      exact hnox u un c (reachS_trans V t x y hy u hu) hun (he ▸ hmem)
  have hvis : ∀ y c f, ReachS V t x y → y ≠ x → ∀ q ∈ eqVisits V t c f y,
      q.1 ≠ x ∧ ReachS V t x q.1 := by
    intro y c f hy hyx q hq
    obtain ⟨a, b⟩ := q
    have hq2 := eqVisits_snd V t c f y (a, b) hq
    simp only at hq2
    subst hq2
    have hr := eqVisits_reach V t y b f y a b ReachS.root hq
    have := hbelow y a hy hyx hr
    exact ⟨this.2, this.1⟩
  have hchild : ∀ y, ReachS V t x y → y ≠ x → ∀ c f, getEqR A t c f y = getEqR V t c f y := by
    intro y hy hyx c f
    exact ((getEqR_frame V A t c f y (fun q hq =>
      Or.inl (hagree q.1 (hvis y c f hy hyx q hq).2 (hvis y c f hy hyx q hq).1).symm)).1).symm
  have hstep : ∀ c f, getEqR A t c (f + 1) Y = getEqR V t c (f + 1) x := by
    intro c f
    simp only [getEqR, hAY, hVx, hll]
    cases hxl : xv.leaf with
    | true => simp only [↓reduceIte]; exact hEq hxl c
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have he := hLte hxl c
      cases h1 : xv.searchLte t c with
      | none =>
        rw [h1] at he
        cases h2 : l.searchLte t c with
        | none => rfl
        | some _ => rw [h2] at he; cases he
      | some fd =>
        rw [h1] at he
        cases h2 : l.searchLte t c with
        | none => rw [h2] at he; cases he
        | some fd2 =>
          rw [h2] at he
          simp only [Option.map_some, Option.some.injEq] at he
          simp only
          rw [he]
          have hmem := KNode.searchLte_mem xv t c fd h1
          have hry : ReachS V t x fd.y := ReachS.step x xv fd.c fd.y ReachS.root hVx hmem
          have hyx : fd.y ≠ x := fun h => hnox x xv fd.c ReachS.root hVx (h ▸ hmem)
          exact hchild fd.y hry hyx c f
  have hget : ∀ c, getEqR A t c fuel Y = getEqR V t c fuel x := by
    intro c
    cases fuel with
    | zero => rfl
    | succ f => exact hstep c f
  -- what a descent from x finds is below x and not x
  have hfound : ∀ c y, getEqR V t c fuel x = some y → ReachS V t x y ∧ y ≠ x := by
    intro c y h
    obtain ⟨z, zn, hz, hzn, hzl, hs⟩ := getEqR_some_visit V t c fuel x y h
    have hrz := eqVisits_reach V t x c fuel x z c ReachS.root hz
    cases hfd : zn.searchEq t c with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      have hmem := KNode.searchEq_mem zn t c fd (hwf z zn hrz hzn) hfd
      exact ⟨ReachS.step z zn c fd.y hrz hzn hmem,
        fun h => hnox z zn c hrz hzn (h ▸ hmem)⟩
  intro key
  cases key with
  | nil => rfl
  | cons c rest =>
    cases rest with
    | nil => simp only [getFromR]; rw [hget c]
    | cons d more =>
      simp only [getFromR]
      rw [hget c]
      cases hg : getEqR V t c fuel x with
      | none => rfl
      | some y =>
        simp only
        obtain ⟨hry, hyx⟩ := hfound c y hg
        rw [hagree y hry hyx]
        split
        · symm
          have hf1 : 1 ≤ fuel := by
            cases fuel with
            | zero => simp [getEqR] at hg
            | succ f => omega
          apply getFromR_frame V A Val Val t fuel hf1 (d :: more) y
          · intro q hq
            have hwfy : ∀ z zn, ReachS V t y z → V z = some zn → klongsWf zn.ks = true :=
              fun z zn hz hzn => hwf z zn (reachS_trans V t x y hry z hz) hzn
            have hr := fromVisits_reach V t fuel y hwfy (d :: more) y q.1 q.2 ReachS.root hq
            obtain ⟨h1, h2⟩ := hbelow y q.1 hry hyx hr
            exact Or.inl (hagree q.1 h1 h2).symm
          · intro _ _ _ _ _ _ _ _; rfl
        · rfl

/-- A path of links from x to every node x reaches. -/
theorem reachS_pathFromLen (N : NodeId → Option KNode) (t : Time) (x : NodeId) :
    ∀ z, ReachS N t x z → ∃ k, PathFromLen N t x z k := by
  intro z hz
  induction hz with
  | root => exact ⟨0, PathFromLen.refl _⟩
  | step u un c _ _ hun hmem ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, PathFromLen.link hk ⟨un, hun, hmem⟩⟩

/-- In a tree, a node's parent is not below the node. -/
theorem notReach_parent (N : NodeId → Option KNode) (t : Time) (r q x : NodeId) (c : Nat)
    (hT : TreeOK N t r) (hq : TReach N t r q) (hl : TLink N t q c x) :
    ∀ z, ReachS N t x z → z ≠ q := by
  intro z hz hzq
  subst hzq
  obtain ⟨a, ha⟩ := hq.pathLen
  obtain ⟨k, hk⟩ := reachS_pathFromLen N t x z hz
  have h1 : PathLen N t r x (a + 1) := PathLen.link ha hl
  have h2 := h1.append hk
  have := PathLen.depth_unique hT a z (a + 1 + k) ha h2
  omega

/-- The reading through a time split below a segment leaf: in the virtual map V
the segment root x holds `xv`; in A its last version l, with x's live klongs, is
at Y, and x's parent q, a segment leaf, names Y by its klong K. If V is a tree
from r, the readings agree. -/
theorem getFromR_segTimeLevel (V A : NodeId → Option KNode) (Val : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r q x Y : NodeId) (qn xv l : KNode) (K : Nat)
    (hT : TreeOK V t r) (hwfV : ∀ z zn, ReachS V t r z → V z = some zn → klongsWf zn.ks = true)
    (hVq : V q = some qn) (hrq : ReachS V t r q) (hql : qn.leaf = true)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hKx : (K, x) ∈ qn.liveAt t) (hqx : q ≠ x)
    (hVx : V x = some xv) (hxwf : klongsWf xv.ks = true) (hxt : ∀ s, Klong.time s ∈ xv.ks → s ≤ t)
    (hVY : V Y = none) (hnoY : ∀ u c, ReachS V t r u → ¬ TLink V t u c Y)
    (hAY : A Y = some l) (hll : l.leaf = xv.leaf) (hlwf : klongsWf l.ks = true)
    (hlt : ∀ s, Klong.time s ∈ l.ks → s ≤ t) (hllook : ∀ c, l.live.lookup c = xv.live.lookup c)
    (hAq : A q = some (qn.add t (.key K Y)))
    (hA : ∀ z, z ≠ x → z ≠ q → z ≠ Y → A z = V z)
    (hVal : Val x = Val Y) (hrY : r ≠ Y) (hrx : r ≠ x) :
    ∀ key, getFromR A Val t fuel key r = getFromR V Val t fuel key r := by
  have hYx : Y ≠ x := fun h => by rw [h, hVx] at hVY; cases hVY
  have hYq : Y ≠ q := fun h => by rw [h, hVq] at hVY; cases hVY
  have hk1 : (K, x) ∈ qn.live := by rw [← KNode.liveAt_of_times qn t hqt]; exact hKx
  have hrqT := reachS_tReach V t r q hrq
  have hrx' : ReachS V t r x := ReachS.step q qn K x hrq hVq hKx
  have hnotq : ∀ z, ReachS V t x z → z ≠ q := notReach_parent V t r q x K hT hrqT ⟨qn, hVq, hKx⟩
  have honly : ∀ z zn c, ReachS V t r z → V z = some zn → (c, x) ∈ zn.liveAt t → z = q ∧ c = K :=
    fun z zn c hz hzn hc => hT.oneLink z c q K x (reachS_tReach V t r z hz) hrqT ⟨zn, hzn, hc⟩
      ⟨qn, hVq, hKx⟩
  -- the tree from Y in A reads as the tree from x in V
  have hsub : ∀ key, key ≠ [] → getFromR A Val t fuel key Y = getFromR V Val t fuel key x := by
    intro key _
    refine getFromR_rename_root V A Val t fuel x Y xv l hVx hAY hll ?_ ?_ ?_ ?_ ?_ key
    · intro _ c
      rw [KNode.searchEq_live l t hlwf hlt, KNode.searchEq_live xv t hxwf hxt, hllook]
    · intro _ c
      exact KNode.searchLte_congr l xv t hlt hxt hllook c
    · intro z zn hz hzn
      exact hwfV z zn (reachS_trans V t r x hrx' z hz) hzn
    · intro z hz hzx
      apply hA z hzx (hnotq z hz)
      intro hzY
      cases hz with
      | root => exact hzx rfl
      | step u un c _ hu hun hmem =>
        exact hnoY u c (reachS_trans V t r x hrx' u hu) ⟨un, hun, hzY ▸ hmem⟩
    · intro z zn c hz hzn hc
      exact hnotq z hz (honly z zn c (reachS_trans V t r x hrx' z hz) hzn hc).1
  have hqs : ∀ c, ((qn.add t (.key K Y)).searchEq t c).map (·.y) =
      ((qn.searchEq t c).map (·.y)).map (fun z => if z = x then Y else z) := by
    intro c
    rw [KNode.add_key_searchEq qn t K Y hqwf hqt c, KNode.searchEq_live qn t hqwf hqt c]
    by_cases hc : K = c
    · subst hc
      rw [lookup_some_of_mem (KNode.live_keys_nodup qn) hk1]
      simp
    · have hb : (K == c) = false := by simpa using hc
      rw [hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hlk : qn.live.lookup c with
      | none => rfl
      | some z =>
        have hzx : z ≠ x := by
          intro hzx
          rw [hzx] at hlk
          have hm := lookup_some_mem hlk
          rw [← KNode.liveAt_of_times qn t hqt] at hm
          exact hc (honly q qn c hrq hVq hm).2.symm
        simp [hzx]
  have hg := getFromR_graft V A Val t fuel r q x Y (fun z => z = x ∨ z = Y) qn (qn.add t (.key K Y))
    hVq hAq hql (by rw [KNode.add_leaf]; exact hql) hqs (Or.inl rfl) hwfV
    (fun z _ hD hzq => hA z (fun h => hD (Or.inl h)) hzq (fun h => hD (Or.inr h)))
    (by
      intro z zn c y hz _ hzq hzn hy hD
      rcases hD with hD | hD
      · subst hD; exact hzq (honly z zn c hz hzn hy).1
      · subst hD; exact hnoY z c hz ⟨zn, hzn, hy⟩)
    (by
      intro c y hy hD
      rcases hD with hD | hD
      · exact hD
      · subst hD; exact absurd ⟨qn, hVq, hy⟩ (hnoY q c hrq))
    hsub (by rw [hAY, hVx]; rfl) hVal.symm
  intro key
  exact hg key r ReachS.root (fun h => by rcases h with h | h; exact hrx h; exact hrY h)

end SIS.Tree
