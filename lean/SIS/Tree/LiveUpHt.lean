/-
The heights at the upward delete's call of `afterDelete` (bergdb 030-01, R2's
heights), the true form of `UpHtWalk` (false as stated, LiveUpHtFalse.lean): not
an invariant of every step, but the heights of the walk's start w3 carried by the
upward loop's frame to the state w' where the stop node calls `afterDelete`
(`htInv_upFrame`). Between w3 and w' only the chain's nodes and the stop node
change: a chain node the transaction made is taken back, another one is unlinked
(its node before the transaction, `ChainFateW`), and the stop node gets a bitmap
that deletes the chain's klong. A node taken back is held by no node but its tree
parent (`liveHolder_unique`, from the take-back's node facts at w3, `TakeJ2`), and
that parent is the next chain node or the stop node, whose klong to it is gone; a
version before the transaction names only nodes below B (`OldBelowN`), which are
never taken back. So every node not taken back at w' keeps its live children not
taken back, and their heights.
-/
import SIS.Tree.LiveUpHtFalse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem upf_mem_of_lookup {β : Type} (l : List (Nat × β)) (a : Nat) (b : β) (h : l.lookup a = some b) :
    (a, b) ∈ l := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]; simp

/-- The live klongs of a node depend on its klongs only. -/
theorem upf_live_ks (n m : KNode) (h : n.ks = m.ks) : n.live = m.live := by
  cases n; cases m
  simp only at h
  subst h
  rfl

/-- A chain node unlinked: its klongs are those of its version before t. -/
theorem upf_unlinked_ks (t : Time) (B : NodeId) (n S : KNode) (hS : RetFormS t B n S) (hpos : 0 < t)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    (unlinkedNode S t).ks = prefixAt n.ks (t - 1) := by
  unfold unlinkedNode
  split
  · exact retFormS_prefix t B n S hS hpos
  · rename_i hl
    have hl' : n.lastTime ≠ some t := by
      intro he
      have hS' : S.lastTime = some t := by rw [retFormS_lastTime t B n S hS]; exact he
      simp [hS'] at hl
    have hSn : S = n := by
      rcases hS with h | ⟨h, _⟩
      · exact h
      · exact absurd h hl'
    subst hSn
    refine (prefixAt_of_times S.ks (t - 1) ?_).symm
    intro k hk s hs
    subst hs
    have hle := ht s hk
    have hne : s ≠ t := fun he => hl' (by rw [← he]; exact KNode.lastTime_of_mem_max S s hw hk (by
      intro s' hs'; rw [he]; exact ht s' hs'))
    omega

set_option maxHeartbeats 1600000 in
/-- The heights at the stop node's call: from `HtInv` at the walk's start w3, the
upward loop's frame to w' (the chain's fates, the stop node's bitmap, nothing else
changed), the books at w' and the take-back's node facts at w3, `HtInv` at w'. -/
theorem htInv_upFrame {H : NodeId → Nat → Prop} (B : NodeId) (c : Ctx) (base : View BVal)
    (w3 w' : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat)
    (hpos : 0 < c.i)
    (hb3 : Book B c w3) (hi3 : HtInv H B c w3) (hwf3 : WriterKlongsWf w3) (hb' : Book B c w')
    (hgh : ∀ e ∈ w3.gh, e ∈ w'.gh) (hpath : w'.path = w3.path)
    (hJ2 : TakeJ2 c base B w3) (hT : TreeOK (wNode c.p base w3) c.i w3.top.rootKey)
    (hTi : TimesN (wNode c.p base w3) c.i)
    (hsD : stop < depth) (hX0 : X 0 = w3.top.rootKey)
    (hlk : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w3.taken.contains (X i) = false)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (ht : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w3.taken.contains y)
    (htop : w'.top = w3.top)
    (hnodes : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
      w'.nodes.lookup y = w3.nodes.lookup y)
    (sn' : KNode) (hsn' : w'.nodes.lookup (X stop) = some sn')
    (hst' : ∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i)
    (hlive' : ∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1))
    (hfJ : ∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k))
    (hS : ∃ S, RetFormS c.i B (Nn stop) S ∧ BitmapOf S sn' c.i (K (stop + 1))) :
    HtInv H B c w' := by
  obtain ⟨hTt, _, hO, hSt, _, _⟩ := hJ2
  have hwN : ∀ y n, w3.nodes.lookup y = some n → w3.taken.contains y = false →
      wNode c.p base w3 y = some n := fun y n hl hu => by
    simp only [wNode, hu, Bool.false_eq_true, ↓reduceIte, hl]
  have hN : ∀ i, i ≤ depth → wNode c.p base w3 (X i) = some (Nn i) := fun i hi =>
    hwN _ _ (hlk i hi) (htk i hi)
  -- a chain node the transaction made is at or above B
  have hfirstB : ∀ k, k ≤ depth → (Nn k).firstTime = some c.i → B ≤ X k := by
    intro k hk hf
    refine Classical.byContradiction fun hlt => ?_
    obtain ⟨s, hs, hf'⟩ := hSt (X k) (Nn k) (hN k hk) (by omega)
    rw [hf] at hf'
    cases hf'
    omega
  -- what w' takes back: w3's, and the chain's nodes that the transaction made
  have htaken' : ∀ y, w'.taken.contains y = true → w3.taken.contains y = true ∨
      ∃ k, stop < k ∧ k ≤ depth ∧ y = X k ∧ (Nn k).firstTime = some c.i := by
    intro y hy
    by_cases hc : ∃ k, stop < k ∧ k ≤ depth ∧ y = X k
    · obtain ⟨k, h1, h2, rfl⟩ := hc
      right
      refine ⟨k, h1, h2, rfl, Classical.byContradiction fun hf => ?_⟩
      rw [((hfJ k h1 h2).2 hf).1] at hy
      cases hy
    · left
      rw [← ht y (fun k h1 h2 he => hc ⟨k, h1, h2, he⟩)]
      exact hy
  have hAbove' : ∀ y, w'.taken.contains y = true → B ≤ y := by
    intro y hy
    rcases htaken' y hy with h | ⟨k, _, h2, rfl, hf⟩
    · exact hi3.takenAbove y h
    · exact hfirstB k h2 hf
  have hfreeB : ∀ y, y < B → w'.taken.contains y = false := by
    intro y hy
    cases h : w'.taken.contains y with
    | false => rfl
    | true => have := hAbove' y h; omega
  -- the heights of w3 hold at w'
  have hHt : ∀ y h, HasHt H w3 y h → HasHt H w' y h := fun y h hy => hy.mono hgh
  -- an entry of w'.gh is w3's
  have hgh' : ∀ y g h, (y, g, h) ∈ w'.gh → (y, g, h) ∈ w3.gh := by
    intro y g h hm
    have hy' : y ∈ w'.nodes.map (·.1) := by rw [hb'.ids]; exact List.mem_reverse.mpr (kd_mem_ids hm)
    obtain ⟨⟨y0, n0⟩, hmem, hy0⟩ := List.mem_map.mp hy'
    simp only at hy0
    subst hy0
    have hl' := ht_lookup_of_mem hb' hmem
    obtain ⟨m3, hm3⟩ : ∃ m3, w3.nodes.lookup y0 = some m3 := by
      by_cases hc : ∃ k, stop < k ∧ k ≤ depth ∧ y0 = X k
      · obtain ⟨k, _, h2, rfl⟩ := hc
        exact ⟨_, hlk k h2⟩
      · by_cases hs : y0 = X stop
        · subst hs
          exact ⟨_, hlk stop (by omega)⟩
        · rw [← hnodes y0 hs (fun k h1 h2 he => hc ⟨k, h1, h2, he⟩), hl']
          exact ⟨_, rfl⟩
    obtain ⟨g3, h3, hm3g⟩ := kd_tag_of_lookup hb3 hm3
    obtain ⟨rfl, rfl⟩ := kd_tag_eq hb' hm (hgh _ hm3g)
    exact hm3g
  have hN3 : ∀ y n g h, w3.nodes.lookup y = some n → (y, g, h) ∈ w3.gh → w3.taken.contains y = false →
      NodeHt c H w3 h n := fun y n g h hl hg hu =>
    hi3.cache y n g h (upf_mem_of_lookup _ _ _ hl) hg hu
  -- the one holder of a chain node the transaction made: its tree parent
  have hhold : ∀ k, stop < k → k ≤ depth → (Nn k).firstTime = some c.i →
      ∀ y n cv, wNode c.p base w3 y = some n → (cv, X k) ∈ n.liveAt c.i → y = X (k - 1) ∧ cv = K k := by
    intro k h1 h2 hf y n cv hy hl
    exact liveHolder_unique (wNode c.p base w3) c.i w3.top.rootKey B hpos hTt hO hTi hT (X k)
      (hfirstB k h2 hf) (X (k - 1)) (K k) (hreach (k - 1) (by omega))
      ⟨Nn (k - 1), hN (k - 1) (by omega), hlinkK k (by omega) h2⟩ y n hy cv hl
  -- a version before the transaction names nodes below B only
  have hprevB : ∀ y n, wNode c.p base w3 y = some n → ∀ cv z,
      (cv, z) ∈ (n.toPrev (c.i - 1)).live → z < B := by
    intro y n hy cv z hz
    obtain ⟨c0, hc0⟩ := live_key_mem _ cv z hz
    exact hO y n hy c0 z hc0
  refine ⟨?_, ?_, ?_, ?_, hAbove', ?_⟩
  · intro y n g h hn hg hu
    have hl' := ht_lookup_of_mem hb' hn
    have hg3 := hgh' y g h hg
    by_cases hc : ∃ k, stop < k ∧ k ≤ depth ∧ y = X k
    · -- a chain node unlinked: its version before the transaction
      obtain ⟨k, h1, h2, rfl⟩ := hc
      have hf : (Nn k).firstTime ≠ some c.i := fun hf => by
        rw [(hfJ k h1 h2).1 hf] at hu
        cases hu
      obtain ⟨_, S, hRS, hlS⟩ := (hfJ k h1 h2).2 hf
      rw [hlS] at hl'
      cases hl'
      have hNk := hN3 (X k) (Nn k) g h (hlk k h2) hg3 (htk k h2)
      have hwk : klongsWf (Nn k).ks = true := hwf3 _ (upf_mem_of_lookup _ _ _ (hlk k h2))
      have hks := upf_unlinked_ks c.i B (Nn k) S hRS hpos hwk hNk.times
      have hlv : (unlinkedNode S c.i).live = ((Nn k).toPrev (c.i - 1)).live := upf_live_ks _ _ hks
      have hlp : ((unlinkedNode S c.i).toPrev (c.i - 1)).live = ((Nn k).toPrev (c.i - 1)).live :=
        upf_live_ks _ _ (by
          show prefixAt (unlinkedNode S c.i).ks (c.i - 1) = prefixAt (Nn k).ks (c.i - 1)
          rw [hks, prefixAt_idem])
      refine ⟨fun cv z hz => ?_, fun cv z hz => ?_, fun s hs => ?_⟩
      · rw [hlv] at hz
        exact ⟨hfreeB z (hprevB _ _ (hN k h2) cv z hz), fun hh => hHt _ _ ((hNk.prev cv z hz).2 hh)⟩
      · rw [hlp] at hz
        exact ⟨hfreeB z (hprevB _ _ (hN k h2) cv z hz), fun hh => hHt _ _ ((hNk.prev cv z hz).2 hh)⟩
      · rw [hks] at hs
        exact hNk.times s ((List.takeWhile_sublist _).subset hs)
    by_cases hs : y = X stop
    · -- the stop node: its bitmap deletes the chain's klong
      subst hs
      rw [hsn'] at hl'
      cases hl'
      have hNs := hN3 (X stop) (Nn stop) g h (hlk stop (by omega)) hg3 (htk stop (by omega))
      obtain ⟨S, hRS, hBS⟩ := hS
      have hpk : (sn'.toPrev (c.i - 1)).ks = ((Nn stop).toPrev (c.i - 1)).ks :=
        (bitmapOf_prefix S sn' c.i _ hBS hpos).trans (retFormS_prefix c.i B (Nn stop) S hRS hpos)
      refine ⟨fun cv z hz => ?_, fun cv z hz => ?_, hst'⟩
      · rw [← KNode.liveAt_of_times sn' c.i hst'] at hz
        obtain ⟨hz0, hne⟩ := (hlive' cv z).mp hz
        have hz1 : (cv, z) ∈ (Nn stop).live := by rw [← KNode.liveAt_of_times _ c.i hNs.times]; exact hz0
        obtain ⟨hu3, hh3⟩ := hNs.live cv z hz1
        refine ⟨?_, fun hh => hHt _ _ (hh3 hh)⟩
        cases hzt : w'.taken.contains z with
        | false => rfl
        | true =>
          exfalso
          rcases htaken' z hzt with h3 | ⟨k, h1, h2, rfl, hf⟩
          · rw [hu3] at h3; cases h3
          · obtain ⟨he, hcv⟩ := hhold k h1 h2 hf (X stop) (Nn stop) cv (hN stop (by omega)) hz0
            have hk1 := hdist stop (k - 1) (by omega) (by omega) he
            have hk : k = stop + 1 := by omega
            subst hk
            exact hne hcv
      · rw [upf_live_ks _ _ hpk] at hz
        exact ⟨hfreeB z (hprevB _ _ (hN stop (by omega)) cv z hz), fun hh => hHt _ _ ((hNs.prev cv z hz).2 hh)⟩
    · -- a node off the chain: as at w3
      have hnc : ∀ k, stop < k → k ≤ depth → y ≠ X k := fun k h1 h2 he => hc ⟨k, h1, h2, he⟩
      have hl3 : w3.nodes.lookup y = some n := by rw [← hnodes y hs hnc]; exact hl'
      have hu3 : w3.taken.contains y = false := by rw [← ht y hnc]; exact hu
      have hNy := hN3 y n g h hl3 hg3 hu3
      refine ⟨fun cv z hz => ?_, fun cv z hz => ?_, hNy.times⟩
      · obtain ⟨hu3z, hh3⟩ := hNy.live cv z hz
        refine ⟨?_, fun hh => hHt _ _ (hh3 hh)⟩
        cases hzt : w'.taken.contains z with
        | false => rfl
        | true =>
          exfalso
          rcases htaken' z hzt with h3 | ⟨k, h1, h2, rfl, hf⟩
          · rw [hu3z] at h3; cases h3
          · have hz' : (cv, X k) ∈ n.liveAt c.i := by rw [KNode.liveAt_of_times _ c.i hNy.times]; exact hz
            obtain ⟨he, _⟩ := hhold k h1 h2 hf y n cv (hwN y n hl3 hu3) hz'
            by_cases hk : k - 1 = stop
            · rw [hk] at he; exact hs he
            · exact hnc (k - 1) (by omega) (by omega) he
      · exact ⟨hfreeB z (hprevB _ _ (hwN y n hl3 hu3) cv z hz), fun hh => hHt _ _ ((hNy.prev cv z hz).2 hh)⟩
  · intro d a q cv y h1 h2 g h hg hu hh
    rw [hpath] at h1 h2
    have hu3 : w3.taken.contains q = false := by
      by_cases hc : ∃ k, stop < k ∧ k ≤ depth ∧ q = X k
      · obtain ⟨k, _, h2', rfl⟩ := hc
        exact htk k h2'
      · rw [← ht q (fun k h1 h2 he => hc ⟨k, h1, h2, he⟩)]
        exact hu
    exact hHt _ _ (hi3.path d a q cv y h1 h2 g h (hgh' q g h hg) hu3 hh)
  · intro d a q h1 h2
    rw [hpath] at h1 h2
    obtain ⟨e, he, hq⟩ := List.mem_map.mp (hi3.pathGh d a q h1 h2)
    exact List.mem_map.mpr ⟨e, hgh e he, hq⟩
  · have hnr : ∀ k, stop < k → k ≤ depth → w3.top.rootKey ≠ X k := fun k h1 h2 he => by
      rw [← hX0] at he
      have := hdist 0 k (Nat.zero_le _) h2 he
      omega
    rw [htop, ht _ hnr]
    exact hi3.rootFree
  · intro d a q h1
    rw [hpath] at h1
    exact hi3.pathSome d a q h1

end SIS.Tree
