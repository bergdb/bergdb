import SIS.Tree.GetLeafRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Every put of a key whose prefix is there, into a leaf below inner nodes with
room for two klongs (bergdb 024-12, TP10; `OpGetOK`'s rules together): with
room, or by a time split or a space split, in place for a leaf the transaction
made, the reading changes by the put alone (`writerWP_put_leafBelow`). -/

/-- A descent's visits hold one leaf at most. -/
theorem eqVisits_leaf_unique (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x L1 L2 : NodeId) (n1 n2 : KNode),
      (L1, cv) ∈ eqVisits N t cv f x → (L2, cv) ∈ eqVisits N t cv f x →
      N L1 = some n1 → n1.leaf = true → N L2 = some n2 → n2.leaf = true → L1 = L2 := by
  intro f
  induction f with
  | zero => intro x L1 L2 n1 n2 h1; simp [eqVisits] at h1
  | succ f ih =>
    intro x L1 L2 n1 n2 h1 h2 hn1 hl1 hn2 hl2
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq, and_true] at h1 h2
    cases hx : N x with
    | none =>
      rw [hx] at h1 h2
      simp only [List.not_mem_nil, or_false] at h1 h2
      rw [h1, h2]
    | some n =>
      rw [hx] at h1 h2
      simp only at h1 h2
      by_cases hl : n.leaf = true
      · simp only [hl, ↓reduceIte, List.not_mem_nil, or_false] at h1 h2
        rw [h1, h2]
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h1 h2
        have hx1 : L1 ≠ x := by
          intro he; subst he; rw [hn1] at hx; cases hx; exact hl hl1
        have hx2 : L2 ≠ x := by
          intro he; subst he; rw [hn2] at hx; cases hx; exact hl hl2
        rcases h1 with h1 | h1
        · exact absurd h1 hx1
        rcases h2 with h2 | h2
        · exact absurd h2 hx2
        cases hs : n.searchLte t cv with
        | none => rw [hs] at h1; cases h1
        | some fd =>
          rw [hs] at h1 h2
          exact ih fd.y L1 L2 n1 n2 h1 h2 hn1 hl1 hn2 hl2

theorem writerWP_put_leafBelow (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 2 + 1 ≤ c.p.M ∧
      (∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false) ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hrange : ∀ q qn L n k1, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
      n.leaf = true → (k1, L) ∈ qn.live →
      ∀ c' z, (c', z) ∈ n.live → k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (huniq : ∀ key' x n, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n → n.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hnext : w.taken.contains w.next = false ∧ w.vals.lookup w.next = none := by
    refine ⟨?_, ?_⟩
    · cases h' : w.taken.contains w.next with
      | false => rfl
      | true => have := hidt _ h'; omega
    · apply List.lookup_eq_none_iff.mpr
      intro q' hq'
      have := hidvals q' hq'
      simp only [bne_iff_ne, ne_eq]
      omega
  have hfresh : ∀ key' x c' n' y,
      (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → (n'.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next := by
    intro key' x c' n' y hx hn' _ hs
    have hrx := fromVisits_reach _ _ _ _ hwf key' _ x c' ReachS.root hx
    cases hfd : n'.searchEq c.i c' with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      have := hlinks x n' c' fd.y hrx hn' (KNode.searchEq_mem n' c.i c' fd (hwf x n' hrx hn') hfd)
      omega
  have hids' : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next := ⟨hidn, hidv, hidt, hidvals, hidr⟩
  have hlive : ∀ n : KNode, c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro n hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  by_cases hex : ∃ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk ∧
      wNode c.p base w L = some n ∧ n.leaf = true
  · obtain ⟨L, n, hL, hn, hnl⟩ := hex
    have hone : ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
        wNode c.p base w L' = some n' → n'.leaf = true → L' = L ∧ n' = n := by
      intro L' n' hL' hn' hnl'
      have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
      subst he
      rw [hn] at hn'
      exact ⟨rfl, (Option.some.inj hn').symm⟩
    obtain ⟨hnwf, htimes, hLval, hLroot⟩ := hleaf L n hL hn hnl
    -- the leaf's case decides the rule
    have hat : ∀ (P : KNode → Prop), P n → ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv
        c.p.fuel rk → wNode c.p base w L' = some n' → n'.leaf = true → P n' := by
      intro P hP L' n' hL' hn' hnl'
      obtain ⟨_, he⟩ := hone L' n' hL' hn' hnl'
      subst he; exact hP
    by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
    · exact writerWP_put_room_seg c base hvc pre cv h rk w hfuel hkey hrk ht
        (fun L' n' hL' hn' hnl' => hat (fun m => klongsWf m.ks = true ∧
          (∀ s, Klong.time s ∈ m.ks → s ≤ c.i) ∧ m.size + 1 < c.p.M ∧
          deadOver c.p (m.add c.i (.key cv w.next)) = false)
          ⟨hnwf, htimes, hroom.1, hroom.2⟩ L' n' hL' hn' hnl')
        hnext huniq hfresh
    · by_cases hnew : n.firstTime = some c.i
      · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
        · exact writerWP_put_spaceSplitInPlace_ord c base hvc pre cv h rk w hfuel hkey hrk ht hids'
            (hbase _ (Nat.le_refl _)).1 hinner
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hsp.1, hnew, hsp.2, hlive _ hsp.2, hLroot⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, _, a4⟩ := hparent q qn hq hqn hql
              exact ⟨a1, by omega, a4⟩)
            hrange huniq hwf htreeK
            (fun x xn cc z hx hn hz => by
              have := hlinks x xn cc z hx hn hz
              exact ⟨by omega, by omega⟩)
        · exact writerWP_put_timeInPlace_seg c base hvc pre cv h rk w hfuel hkey hrk ht
            (fun L' n' hL' hn' hnl' => hat (fun m => klongsWf m.ks = true ∧
              (∀ s, Klong.time s ∈ m.ks → s ≤ c.i) ∧
              ¬ (m.size + 1 < c.p.M ∧ deadOver c.p (m.add c.i (.key cv w.next)) = false) ∧
              m.firstTime = some c.i ∧ (c.p.M ≤ m.size + 1 → (m.lastVersion c.i).size ≤ c.p.splitAbove))
              ⟨hnwf, htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩
              L' n' hL' hn' hnl')
            hnext huniq hfresh
      · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
        · exact writerWP_put_spaceSplit_ord c base hvc pre cv h rk w hfuel hkey hrk ht hids'
            (hbase _ (Nat.le_refl _)).1 hinner
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hsp.1, hnew, hsp.2, hlive _ hsp.2, hLroot⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, a3, _⟩ := hparent q qn hq hqn hql
              exact ⟨a1, a2, a3⟩)
            hrange huniq hwf htreeK
            (fun x xn cc z hx hn hz => by
              have := hlinks x xn cc z hx hn hz
              exact ⟨by omega, by omega, by omega⟩)
        · exact writerWP_put_timeSplit_key c base hvc pre cv h rk w hfuel hkey hrk ht hids'
            ⟨(hbase _ (Nat.le_refl _)).1, (hbase (w.next + 2) (by omega)).2,
              (hbase (w.next + 2) (by omega)).1⟩ hinner
            (fun L' n' hL' hn' hnl' => by
              obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
              subst he1 he2
              exact ⟨htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩),
                hLval, hLroot⟩)
            (fun q qn hq hqn hql => by
              obtain ⟨a1, a2, _, a4⟩ := hparent q qn hq hqn hql
              exact ⟨a1, by omega, a4⟩)
            huniq hwf htreeK
            (fun x xn cc z hx hn hz => by
              have := hlinks x xn cc z hx hn hz
              exact ⟨by omega, by omega⟩)
  · exact writerWP_put_room_seg c base hvc pre cv h rk w hfuel hkey hrk ht
      (fun L' n' hL' hn' hnl' => absurd ⟨L', n', hL', hn', hnl'⟩ hex) hnext huniq hfresh

end SIS.Tree
