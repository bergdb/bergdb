/-
The writer's tree kept by a cascade of time splits (bergdb 024-22, `OpTreeOK`;
prover latest's `TimeSplit2After`, GetChain.lean): the leaf L and its parent q
are both split in time, the grandparent g names q's last version
(`treeOK_timeSplit2`, `writerWP_appendKlongs_timeSplit2_tree`).
-/
import SIS.Tree.WriterTreeCollapseSeg
import SIS.Tree.GetChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- No two nodes of a tree name each other. -/
theorem TreeOK.no_two_cycle {N : NodeId → Option KNode} {t : Time} {r : NodeId} (hT : TreeOK N t r)
    (a b : NodeId) (ca cb : Nat) (hab : TLink N t a ca b) (hba : TLink N t b cb a)
    (ha : TReach N t r a) : False := by
  have hb : TReach N t r b := TReach.link ha hab
  -- neither is the root
  have har : a ≠ r := fun h => hT.rootFree b cb hb (by rw [← h]; exact hba)
  have hbr : b ≠ r := fun h => hT.rootFree a ca ha (by rw [← h]; exact hab)
  have key : ∀ x, TReach N t r x → x ≠ a ∧ x ≠ b := by
    intro x hx
    induction hx with
    | root => exact ⟨Ne.symm har, Ne.symm hbr⟩
    | @link y c x hy hl ih =>
      refine ⟨fun hxa => ?_, fun hxb => ?_⟩
      · rw [hxa] at hl
        exact ih.2 (hT.oneLink y c b cb a hy hb hl hba).1
      · rw [hxb] at hl
        exact ih.1 (hT.oneLink y c a ca b hy ha hl hab).1
  exact (key a ha).1 rfl

/-- A live klong of a node whose live lookup is another's with compare value k
pointed to y: it is (k, y), or the other's with another compare value. -/
theorem liveAt_of_lookup_update (m n : KNode) (t : Time) (k : Nat) (y : NodeId)
    (hm : ∀ s, Klong.time s ∈ m.ks → s ≤ t) (hn : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hl : ∀ q', m.live.lookup q' = if k == q' then some y else n.live.lookup q')
    (c : Nat) (z : NodeId) (h : (c, z) ∈ m.liveAt t) :
    (c = k ∧ z = y) ∨ ((c, z) ∈ n.liveAt t ∧ c ≠ k) := by
  rw [KNode.liveAt_of_times m t hm] at h
  have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
  rw [hl c] at hlk
  by_cases hck : k = c
  · subst hck; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
  · have hb : (k == c) = false := by simpa using hck
    rw [hb] at hlk
    simp only [Bool.false_eq_true, ↓reduceIte] at hlk
    refine Or.inr ⟨?_, Ne.symm hck⟩
    rw [KNode.liveAt_of_times n t hn]
    exact mem_of_lookup_nodup _ c z hlk

/-- The tree after a time split of the leaf L under q and of q under g: new
nodes y1 (L's last version with the put's (cv, v)) and y2 (q's last version with
k1 naming y1); g's klong kq names y2; L and q are left behind. -/
theorem treeOK_timeSplit2 (N N' : NodeId → Option KNode) (t : Time) (r g q L y1 y2 v : NodeId)
    (gn qn n l lq : KNode) (kq k1 cv : Nat)
    (hT : TreeOK N t r) (hg : TReach N t r g) (hgn : N g = some gn)
    (hgk : (kq, q) ∈ gn.liveAt t) (hgwf : klongsWf gn.ks = true)
    (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ t)
    (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hl_times : ∀ s, Klong.time s ∈ l.ks → s ≤ t)
    (hl_look : ∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q')
    (hlq_times : ∀ s, Klong.time s ∈ lq.ks → s ≤ t)
    (hlq_look : ∀ q', lq.live.lookup q' = if k1 == q' then some y1 else qn.live.lookup q')
    (hN'g : N' g = some (gn.add t (.key kq y2)))
    (hN'1 : N' y1 = some ⟨n.leaf, l.ks⟩) (hN'2 : N' y2 = some ⟨qn.leaf, lq.ks⟩)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ g → z ≠ y1 → z ≠ y2 → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (hvN : N v = none)
    (h12 : y1 ≠ y2) (hv1 : v ≠ y1) (hv2 : v ≠ y2)
    (hfresh : ∀ z, (z = y1 ∨ z = y2 ∨ z = v) → ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  have hne : ∀ z m, N z = some m → ∀ y, N y = none → z ≠ y := fun z m hz y hy he => by
    rw [he, hy] at hz; cases hz
  have hgq_link : TLink N t g kq q := ⟨gn, hgn, hgk⟩
  have hq : TReach N t r q := TReach.link hg hgq_link
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hgq : g ≠ q := fun h => hT.no_self_link g kq hg (by rw [← h] at hgq_link; exact hgq_link)
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hgL : g ≠ L := fun h => hT.no_two_cycle g q kq k1 hgq_link (by rw [h]; exact hqL_link) hg
  have hqpar : ∀ u c', TReach N t r u → TLink N t u c' q → u = g ∧ c' = kq :=
    fun u c' hu hl => hT.oneLink u c' g kq q hu hg hl hgq_link
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hL1 := hne L n hLn y1 hf1
  have hL2 := hne L n hLn y2 hf2
  have hLv := hne L n hLn v hvN
  have hq1 := hne q qn hqn y1 hf1
  have hq2 := hne q qn hqn y2 hf2
  have hqv := hne q qn hqn v hvN
  have hg1 := hne g gn hgn y1 hf1
  have hg2 := hne g gn hgn y2 hf2
  have hgv := hne g gn hgn v hvN
  have hvN' : N' v = none := by rw [hother v (Ne.symm hLv) (Ne.symm hqv) (Ne.symm hgv) hv1 hv2]; exact hvN
  have hnotR : ∀ z, (z = y1 ∨ z = y2 ∨ z = v) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h | h <;> rw [h]
    · exact not_reach_fresh N t r y1 hT hf1 (hfresh y1 (Or.inl rfl))
    · exact not_reach_fresh N t r y2 hT hf2 (hfresh y2 (Or.inr (Or.inl rfl)))
    · exact not_reach_fresh N t r v hT hvN (hfresh v (Or.inr (Or.inr rfl)))
  -- the new links
  have h1l : ∀ c' z, TLink N' t y1 c' z → (c' = cv ∧ z = v) ∨ ((c', z) ∈ n.liveAt t ∧ c' ≠ cv) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'1] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact liveAt_of_lookup_update _ n t cv v hl_times hnt
      hl_look c' z hc
  have h2l : ∀ c' z, TLink N' t y2 c' z → (c' = k1 ∧ z = y1) ∨ ((c', z) ∈ qn.liveAt t ∧ c' ≠ k1) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'2] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact liveAt_of_lookup_update _ qn t k1 y1 hlq_times hqt
      hlq_look c' z hc
  have hgl : ∀ c' z, TLink N' t g c' z → (c' = kq ∧ z = y2) ∨ (c' ≠ kq ∧ (c', z) ∈ gn.liveAt t) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'g] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact KNode.add_key_liveAt_mem gn t kq y2 hgwf hgt c' z hc
  have hvl : ∀ c' z, ¬ TLink N' t v c' z := by
    intro c' z hl
    obtain ⟨m, hm, _⟩ := hl
    rw [hvN'] at hm; cases hm
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ g → u ≠ y1 → u ≠ y2 → ∀ c' z,
      TLink N' t u c' z → TLink N t u c' z := by
    intro u h1 h2 h3 h4 h5 c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hother u h1 h2 h3 h4 h5] at hm
    exact ⟨m, hm, hc⟩
  have hReachOr : ∀ u, (TReach N t r u ∨ (u = y1 ∨ u = y2 ∨ u = v)) → u ≠ y1 → u ≠ y2 → u ≠ v →
      TReach N t r u := by
    intro u hu h1 h2 h3
    rcases hu with h | h
    · exact h
    · rcases h with h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
  -- an old target of an old reached node u is not L unless u = q, not q unless u = g
  have hnotGone : ∀ u c' z, TReach N t r u → TLink N t u c' z → (u ≠ q ∨ c' ≠ k1) →
      (u ≠ g ∨ c' ≠ kq) → ¬ (z = L ∨ z = q) := by
    intro u c' z hu hl h1 h2 hz
    rcases hz with hz | hz
    · rw [hz] at hl
      obtain ⟨a, b⟩ := hLpar u c' hu hl
      rcases h1 with h1 | h1
      · exact h1 a
      · exact h1 b
    · rw [hz] at hl
      obtain ⟨a, b⟩ := hqpar u c' hu hl
      rcases h2 with h2 | h2
      · exact h2 a
      · exact h2 b
  apply treeOK_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2 ∨ z = v) (fun z => z = L ∨ z = q)
    (fun u c' => if u = L then (y1, c') else if u = q then (y2, c') else (u, c')) hT hnotR
  · refine Or.inl ⟨rfl, ?_⟩
    rintro (h | h)
    · exact hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
    · exact hT.rootFree g kq hg (by rw [h]; exact hgq_link)
  · intro u c' z hu hug hl
    have huL : u ≠ L := fun h => hug (Or.inl h)
    have huq : u ≠ q := fun h => hug (Or.inr h)
    by_cases hu1 : u = y1
    · rw [hu1] at hl
      rcases h1l c' z hl with ⟨_, h⟩ | ⟨hmem, hc⟩
      · exact Or.inl (Or.inr (Or.inr h))
      · have hl0 : TLink N t L c' z := ⟨n, hLn, hmem⟩
        exact Or.inr ⟨hnotGone L c' z hL hl0 (Or.inl (Ne.symm hqL)) (Or.inl (Ne.symm hgL)),
          L, c', hL, hl0, by simp [hu1]⟩
    · by_cases hu2 : u = y2
      · rw [hu2] at hl
        rcases h2l c' z hl with ⟨_, h⟩ | ⟨hmem, hc⟩
        · exact Or.inl (Or.inl h)
        · have hl0 : TLink N t q c' z := ⟨qn, hqn, hmem⟩
          exact Or.inr ⟨hnotGone q c' z hq hl0 (Or.inr hc) (Or.inl (Ne.symm hgq)),
            q, c', hq, hl0, by simp [hu2, hqL]⟩
      · by_cases huv : u = v
        · rw [huv] at hl; exact absurd hl (hvl c' z)
        · have huR := hReachOr u hu hu1 hu2 huv
          by_cases hug' : u = g
          · rw [hug'] at hl
            rcases hgl c' z hl with ⟨_, h⟩ | ⟨hc, hmem⟩
            · exact Or.inl (Or.inr (Or.inl h))
            · have hl0 : TLink N t g c' z := ⟨gn, hgn, hmem⟩
              exact Or.inr ⟨hnotGone g c' z hg hl0 (Or.inl hgq) (Or.inr hc), g, c', hg, hl0,
                by simp [hgL, hgq, hug']⟩
          · have hl0 := hOld u huL huq hug' hu1 hu2 c' z hl
            exact Or.inr ⟨hnotGone u c' z huR hl0 (Or.inl huq) (Or.inl hug'), u, c', huR, hl0,
              by simp [huL, huq]⟩
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hone : ∀ y d, (TReach N t r y ∨ (y = y1 ∨ y = y2 ∨ y = v)) → ¬ (y = L ∨ y = q) →
        TLink N' t y d z →
        (y = y2 ∧ d = k1 ∧ z = y1) ∨ (y = g ∧ d = kq ∧ z = y2) ∨ (y = y1 ∧ d = cv ∧ z = v) := by
      intro y d hy hyg hl
      have hfr := hfresh z hz
      have hyL : y ≠ L := fun h => hyg (Or.inl h)
      have hyq : y ≠ q := fun h => hyg (Or.inr h)
      by_cases hy1 : y = y1
      · rw [hy1] at hl
        rcases h1l d z hl with ⟨hd, h⟩ | ⟨hmem, _⟩
        · exact Or.inr (Or.inr ⟨hy1, hd, h⟩)
        · exact absurd ⟨n, hLn, hmem⟩ (hfr L d hL)
      · by_cases hy2 : y = y2
        · rw [hy2] at hl
          rcases h2l d z hl with ⟨hd, h⟩ | ⟨hmem, _⟩
          · exact Or.inl ⟨hy2, hd, h⟩
          · exact absurd ⟨qn, hqn, hmem⟩ (hfr q d hq)
        · by_cases hyv : y = v
          · rw [hyv] at hl; exact absurd hl (hvl d z)
          · have hyR := hReachOr y hy hy1 hy2 hyv
            by_cases hyg' : y = g
            · rw [hyg'] at hl
              rcases hgl d z hl with ⟨hd, h⟩ | ⟨_, hmem⟩
              · exact Or.inr (Or.inl ⟨hyg', hd, h⟩)
              · exact absurd ⟨gn, hgn, hmem⟩ (hfr g d hg)
            · exact absurd (hOld y hyL hyq hyg' hy1 hy2 d z hl) (hfr y d hyR)
    rcases hone u c' hu hug hl1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
      rcases hone u' c'' hu' hug' hl2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact absurd (c1.symm.trans c2) h12
    · exact absurd (c2.symm.trans c1) hv1
    · exact absurd (c2.symm.trans c1) h12
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact absurd (c2.symm.trans c1) hv2
    · exact absurd (c1.symm.trans c2) hv1
    · exact absurd (c1.symm.trans c2) hv2
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro z hz hzg
    rcases hz with h | h | h <;> rcases hzg with h' | h' <;> rw [h] at h'
    · exact hL1 h'.symm
    · exact hq1 h'.symm
    · exact hL2 h'.symm
    · exact hq2 h'.symm
    · exact hLv h'.symm
    · exact hqv h'.symm
  · by_cases hrg : r = g
    · rw [hrg, hN'g]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      have hrq : r ≠ q := fun h => hT.rootFree g kq hg (by rw [h]; exact hgq_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      have hr1 := hne r rm hrm y1 hf1
      have hr2 := hne r rm hrm y2 hf2
      rw [hother r hrL hrq hrg hr1 hr2]; exact ⟨rm, hrm⟩

/-- The writer's two-level time split keeps the writer's tree
(`writerWP_appendKlongs_timeSplit2` with `treeOK_timeSplit2`). -/
theorem writerWP_appendKlongs_timeSplit2_tree (base : View BVal) (d'' : Nat) (L q g : NodeId)
    (n qn gn : KNode) (kq k1 cv v : Nat) (c : Ctx) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hgR : TReach (wNode c.p base w) c.i w.top.rootKey g)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hgt' : w.taken.contains g = false)
    (hgk : (kq, q) ∈ gn.liveAt c.i) (hqk : (k1, L) ∈ qn.liveAt c.i)
    (hgwf : klongsWf gn.ks = true) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ c.i)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hqfull : ¬ (qn.size + 1 < c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M ≤ qn.size + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hf1 : wNode c.p base w w.next = none) (hf2 : wNode c.p base w (w.next + 2) = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (hvN : wNode c.p base w v = none) (hv1 : v ≠ w.next) (hv2 : v ≠ w.next + 2)
    (hLn : L < w.next)
    (hfresh : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = v) →
      ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u → ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  have hwg : wNode c.p base w g = some gn := by simp only [wNode, hgt', Bool.false_eq_true, ↓reduceIte, hlg]
  have hgqL : TLink (wNode c.p base w) c.i g kq q := ⟨gn, hwg, hgk⟩
  have hq : TReach (wNode c.p base w) c.i w.top.rootKey q := TReach.link hgR hgqL
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqk; exact ⟨qn, hwq, hqk⟩)
  have hgq : g ≠ q := fun h => hT.no_self_link g kq hgR (by rw [← h] at hgqL; exact hgqL)
  have hgL : g ≠ L := fun h => hT.no_two_cycle g q kq k1 hgqL (by rw [h]; exact ⟨qn, hwq, hqk⟩) hgR
  have hny : w.nodes.lookup w.next = none := by
    unfold wNode at hf1; simp only [ht1, Bool.false_eq_true, ↓reduceIte] at hf1
    split at hf1
    · cases hf1
    · assumption
  have hny2 : w.nodes.lookup (w.next + 2) = none := by
    unfold wNode at hf2; simp only [ht2, Bool.false_eq_true, ↓reduceIte] at hf2
    split at hf2
    · cases hf2
    · assumption
  refine writerWP_mono (writerWP_appendKlongs_timeSplit2 d'' L q g n qn gn kq k1 cv v c w hlk hlq hlg
    hqL hgq hgL hql hgl hfirst hqfirst hfull hsplit hqfull hqsplit hpg hpq hpk hroomg hdeadg hny hny2
    hLn) ?_
  intro _ w' ⟨l, lq, _, _, hl_times, hl_look, _, _, hlq_times, hlq_look, h'taken, h'top, _, h'nodes⟩
  rw [h'top]
  have hN' : ∀ x, wNode c.p base w' x = if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some (gn.add c.i (.key kq (w.next + 2)))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else if x = w.next + 2 then some ⟨qn.leaf, lq.ks⟩
      else wNode c.p base w x := by
    intro x
    unfold wNode
    rw [h'taken, h'nodes x]
    by_cases hxL : x = L
    · subst hxL; simp only [hLt, Bool.false_eq_true, ↓reduceIte]
    · by_cases hxq : x = q
      · subst hxq; simp only [hqt', hxL, Bool.false_eq_true, ↓reduceIte]
      · by_cases hxg : x = g
        · subst hxg; simp only [hgt', hxL, hxq, Bool.false_eq_true, ↓reduceIte]
        · by_cases hx1 : x = w.next
          · subst hx1; simp only [ht1, hxL, hxq, hxg, Bool.false_eq_true, ↓reduceIte]
          · by_cases hx2 : x = w.next + 2
            · subst hx2; simp only [ht2, hxL, hxq, hxg, hx1, Bool.false_eq_true, ↓reduceIte]
            · simp only [hxL, hxq, hxg, hx1, hx2, ↓reduceIte]
  have h12 : w.next ≠ w.next + 2 := by omega
  have hq1 : q ≠ w.next := fun h => by rw [h, hf1] at hwq; cases hwq
  have hq2 : q ≠ w.next + 2 := fun h => by rw [h, hf2] at hwq; cases hwq
  have hg1 : g ≠ w.next := fun h => by rw [h, hf1] at hwg; cases hwg
  have hg2 : g ≠ w.next + 2 := fun h => by rw [h, hf2] at hwg; cases hwg
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  apply treeOK_timeSplit2 (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey g q L w.next
    (w.next + 2) v gn qn n l lq kq k1 cv hT hgR hwg hgk hgwf hgt hwq hqk hqt hwL hnt hl_times
    (fun q' => by rw [hl_look q']) hlq_times (fun q' => by rw [hlq_look q'])
  · rw [hN' g]; simp [hgL, hgq]
  · rw [hN' w.next]; simp [Ne.symm hL1, Ne.symm hq1, Ne.symm hg1]
  · rw [hN' (w.next + 2)]; simp [Ne.symm hL2, Ne.symm hq2, Ne.symm hg2]
  · intro z hzL hzq hzg hz1 hz2
    rw [hN' z]; simp [hzL, hzq, hzg, hz1, hz2]
  · exact hf1
  · exact hf2
  · exact hvN
  · exact h12
  · exact hv1
  · exact hv2
  · exact hfresh

/-- A live klong of a node whose live lookup is another's with k1 pointed to y1
and then k2 to y2. -/
theorem liveAt_of_lookup_update2 (m n : KNode) (t : Time) (k1 k2 : Nat) (y1 y2 : NodeId)
    (hm : ∀ s, Klong.time s ∈ m.ks → s ≤ t) (hn : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hl : ∀ q', m.live.lookup q' = [(k1, y1), (k2, y2)].foldl (pairLookupStep q') (n.live.lookup q'))
    (c : Nat) (z : NodeId) (h : (c, z) ∈ m.liveAt t) :
    (c = k2 ∧ z = y2) ∨ (c = k1 ∧ z = y1 ∧ c ≠ k2) ∨ ((c, z) ∈ n.liveAt t ∧ c ≠ k1 ∧ c ≠ k2) := by
  rw [KNode.liveAt_of_times m t hm] at h
  have hlk := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) c z h
  rw [hl c] at hlk
  simp only [List.foldl_cons, List.foldl_nil, pairLookupStep] at hlk
  by_cases h2 : k2 = c
  · subst h2; simp at hlk; exact Or.inl ⟨rfl, hlk.symm⟩
  · have hb2 : (k2 == c) = false := by simpa using h2
    rw [hb2] at hlk
    simp only [Bool.false_eq_true, ↓reduceIte] at hlk
    by_cases h1 : k1 = c
    · subst h1; simp at hlk; exact Or.inr (Or.inl ⟨rfl, hlk.symm, Ne.symm h2⟩)
    · have hb1 : (k1 == c) = false := by simpa using h1
      rw [hb1] at hlk
      simp only [Bool.false_eq_true, ↓reduceIte] at hlk
      refine Or.inr (Or.inr ⟨?_, Ne.symm h1, Ne.symm h2⟩)
      rw [KNode.liveAt_of_times n t hn]
      exact mem_of_lookup_nodup _ c z hlk

/-- The tree after a space split of the leaf L under q and a time split of q
under g: halves y1 and y2 of L's last version with the put's (cv, v), y3 q's
last version naming them, g's klong kq names y3; L and q are left behind. -/
theorem treeOK_spaceSplitTime (N N' : NodeId → Option KNode) (t : Time) (r g q L y1 y2 y3 v : NodeId)
    (gn qn n lq : KNode) (kq k1 cv : Nat) (r0 : Nat × NodeId)
    (hT : TreeOK N t r) (hg : TReach N t r g) (hgn : N g = some gn)
    (hgk : (kq, q) ∈ gn.liveAt t) (hgwf : klongsWf gn.ks = true)
    (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ t)
    (hqn : N q = some qn) (hqk : (k1, L) ∈ qn.liveAt t) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hLn : N L = some n) (hnleaf : n.leaf = true)
    (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hlq_times : ∀ s, Klong.time s ∈ lq.ks → s ≤ t)
    (hlq_look : ∀ q', lq.live.lookup q' = [(k1, y1),
      ((halves true t (n.lastVersion t) [(cv, v)]).2.2, y2)].foldl (pairLookupStep q') (qn.live.lookup q'))
    (hN'g : N' g = some (gn.add t (.key kq y3)))
    (hN'1 : N' y1 = some (halves true t (n.lastVersion t) [(cv, v)]).1)
    (hN'2 : N' y2 = some (halves true t (n.lastVersion t) [(cv, v)]).2.1)
    (hN'3 : N' y3 = some ⟨qn.leaf, lq.ks⟩)
    (hother : ∀ z, z ≠ L → z ≠ q → z ≠ g → z ≠ y1 → z ≠ y2 → z ≠ y3 → N' z = N z)
    (hf1 : N y1 = none) (hf2 : N y2 = none) (hf3 : N y3 = none) (hvN : N v = none)
    (h12 : y1 ≠ y2) (h13 : y1 ≠ y3) (h23 : y2 ≠ y3) (hv1 : v ≠ y1) (hv2 : v ≠ y2) (hv3 : v ≠ y3)
    (hfresh : ∀ z, (z = y1 ∨ z = y2 ∨ z = y3 ∨ z = v) →
      ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  obtain ⟨hsc, hfirst, hsecond⟩ := halves_leaf_live n t hnleaf cv v r0 hr0
  generalize hout : halves true t (n.lastVersion t) [(cv, v)] = out at *
  rw [hsc] at hlq_look
  have hnlive : n.liveAt t = n.live := KNode.liveAt_of_times n t hnt
  have hne : ∀ z m, N z = some m → ∀ y, N y = none → z ≠ y := fun z m hz y hy he => by
    rw [he, hy] at hz; cases hz
  have hgq_link : TLink N t g kq q := ⟨gn, hgn, hgk⟩
  have hq : TReach N t r q := TReach.link hg hgq_link
  have hqL_link : TLink N t q k1 L := ⟨qn, hqn, hqk⟩
  have hL : TReach N t r L := TReach.link hq hqL_link
  have hgq : g ≠ q := fun h => hT.no_self_link g kq hg (by rw [← h] at hgq_link; exact hgq_link)
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqL_link; exact hqL_link)
  have hgL : g ≠ L := fun h => hT.no_two_cycle g q kq k1 hgq_link (by rw [h]; exact hqL_link) hg
  have hqpar : ∀ u c', TReach N t r u → TLink N t u c' q → u = g ∧ c' = kq :=
    fun u c' hu hl => hT.oneLink u c' g kq q hu hg hl hgq_link
  have hLpar : ∀ u c', TReach N t r u → TLink N t u c' L → u = q ∧ c' = k1 :=
    fun u c' hu hl => hT.oneLink u c' q k1 L hu hq hl hqL_link
  have hLlink : ∀ c' z, (c', z) ∈ n.live → TLink N t L c' z := fun c' z h =>
    ⟨n, hLn, by rw [hnlive]; exact h⟩
  have hvN' : N' v = none := by
    rw [hother v (Ne.symm (hne L n hLn v hvN)) (Ne.symm (hne q qn hqn v hvN))
      (Ne.symm (hne g gn hgn v hvN)) hv1 hv2 hv3]; exact hvN
  have hnotR : ∀ z, (z = y1 ∨ z = y2 ∨ z = y3 ∨ z = v) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h | h | h <;> rw [h]
    · exact not_reach_fresh N t r y1 hT hf1 (hfresh y1 (Or.inl rfl))
    · exact not_reach_fresh N t r y2 hT hf2 (hfresh y2 (Or.inr (Or.inl rfl)))
    · exact not_reach_fresh N t r y3 hT hf3 (hfresh y3 (Or.inr (Or.inr (Or.inl rfl))))
    · exact not_reach_fresh N t r v hT hvN (hfresh v (Or.inr (Or.inr (Or.inr rfl))))
  have h1l : ∀ c' z, TLink N' t y1 c' z → ((c', z) = (cv, v) ∧ cv < r0.1) ∨
      ((c', z) ∈ n.live ∧ c' < r0.1) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'1] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hfirst c' z hc
  have h2l : ∀ c' z, TLink N' t y2 c' z → ((c', z) = (cv, v) ∧ r0.1 ≤ cv) ∨
      ((c', z) ∈ n.live ∧ r0.1 ≤ c') := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'2] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hsecond c' z hc
  have h3l : ∀ c' z, TLink N' t y3 c' z → (c' = r0.1 ∧ z = y2) ∨ (c' = k1 ∧ z = y1 ∧ c' ≠ r0.1) ∨
      ((c', z) ∈ qn.liveAt t ∧ c' ≠ k1 ∧ c' ≠ r0.1) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'3] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact liveAt_of_lookup_update2 _ qn t k1 r0.1 y1 y2 hlq_times hqt hlq_look c' z hc
  have hgl : ∀ c' z, TLink N' t g c' z → (c' = kq ∧ z = y3) ∨ (c' ≠ kq ∧ (c', z) ∈ gn.liveAt t) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'g] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact KNode.add_key_liveAt_mem gn t kq y3 hgwf hgt c' z hc
  have hvl : ∀ c' z, ¬ TLink N' t v c' z := by
    intro c' z hl
    obtain ⟨m, hm, _⟩ := hl
    rw [hvN'] at hm; cases hm
  have hOld : ∀ u, u ≠ L → u ≠ q → u ≠ g → u ≠ y1 → u ≠ y2 → u ≠ y3 → ∀ c' z,
      TLink N' t u c' z → TLink N t u c' z := by
    intro u h1 h2 h3 h4 h5 h6 c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hother u h1 h2 h3 h4 h5 h6] at hm
    exact ⟨m, hm, hc⟩
  have hReachOr : ∀ u, (TReach N t r u ∨ (u = y1 ∨ u = y2 ∨ u = y3 ∨ u = v)) → u ≠ y1 → u ≠ y2 →
      u ≠ y3 → u ≠ v → TReach N t r u := by
    intro u hu h1 h2 h3 h4
    rcases hu with h | h
    · exact h
    · rcases h with h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact absurd h h4
  have hnotGone : ∀ u c' z, TReach N t r u → TLink N t u c' z → (u ≠ q ∨ c' ≠ k1) →
      (u ≠ g ∨ c' ≠ kq) → ¬ (z = L ∨ z = q) := by
    intro u c' z hu hl h1 h2 hz
    rcases hz with hz | hz
    · rw [hz] at hl
      obtain ⟨a, b⟩ := hLpar u c' hu hl
      rcases h1 with h1 | h1
      · exact h1 a
      · exact h1 b
    · rw [hz] at hl
      obtain ⟨a, b⟩ := hqpar u c' hu hl
      rcases h2 with h2 | h2
      · exact h2 a
      · exact h2 b
  apply treeOK_transfer_gone N N' t r r (fun z => z = y1 ∨ z = y2 ∨ z = y3 ∨ z = v)
    (fun z => z = L ∨ z = q)
    (fun u c' => if u = L then (if c' < r0.1 then (y1, c') else (y2, c'))
      else if u = q then (y3, c') else (u, c')) hT hnotR
  · refine Or.inl ⟨rfl, ?_⟩
    rintro (h | h)
    · exact hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
    · exact hT.rootFree g kq hg (by rw [h]; exact hgq_link)
  · intro u c' z hu hug hl
    have huL : u ≠ L := fun h => hug (Or.inl h)
    have huq : u ≠ q := fun h => hug (Or.inr h)
    by_cases hu1 : u = y1
    · rw [hu1] at hl
      rcases h1l c' z hl with ⟨h, _⟩ | ⟨hmem, hlt⟩
      · simp only [Prod.mk.injEq] at h
        exact Or.inl (Or.inr (Or.inr (Or.inr h.2)))
      · have hl0 := hLlink c' z hmem
        exact Or.inr ⟨hnotGone L c' z hL hl0 (Or.inl (Ne.symm hqL)) (Or.inl (Ne.symm hgL)),
          L, c', hL, hl0, by simp [hu1, hlt]⟩
    · by_cases hu2 : u = y2
      · rw [hu2] at hl
        rcases h2l c' z hl with ⟨h, _⟩ | ⟨hmem, hge⟩
        · simp only [Prod.mk.injEq] at h
          exact Or.inl (Or.inr (Or.inr (Or.inr h.2)))
        · have hl0 := hLlink c' z hmem
          have hnlt : ¬ c' < r0.1 := by omega
          exact Or.inr ⟨hnotGone L c' z hL hl0 (Or.inl (Ne.symm hqL)) (Or.inl (Ne.symm hgL)),
            L, c', hL, hl0, by simp [hu2, hnlt]⟩
      · by_cases hu3 : u = y3
        · rw [hu3] at hl
          rcases h3l c' z hl with ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨hmem, hc1, _⟩
          · exact Or.inl (Or.inr (Or.inl h))
          · exact Or.inl (Or.inl h)
          · have hl0 : TLink N t q c' z := ⟨qn, hqn, hmem⟩
            exact Or.inr ⟨hnotGone q c' z hq hl0 (Or.inr hc1) (Or.inl (Ne.symm hgq)),
              q, c', hq, hl0, by simp [hu3, hqL]⟩
        · by_cases huv : u = v
          · rw [huv] at hl; exact absurd hl (hvl c' z)
          · have huR := hReachOr u hu hu1 hu2 hu3 huv
            by_cases hug' : u = g
            · rw [hug'] at hl
              rcases hgl c' z hl with ⟨_, h⟩ | ⟨hc, hmem⟩
              · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
              · have hl0 : TLink N t g c' z := ⟨gn, hgn, hmem⟩
                exact Or.inr ⟨hnotGone g c' z hg hl0 (Or.inl hgq) (Or.inr hc), g, c', hg, hl0,
                  by simp [hgL, hgq, hug']⟩
            · have hl0 := hOld u huL huq hug' hu1 hu2 hu3 c' z hl
              exact Or.inr ⟨hnotGone u c' z huR hl0 (Or.inl huq) (Or.inl hug'), u, c', huR, hl0,
                by simp [huL, huq]⟩
  · intro u c' u' c'' z hu hug hu' hug' hz hl1 hl2
    have hone : ∀ y d, (TReach N t r y ∨ (y = y1 ∨ y = y2 ∨ y = y3 ∨ y = v)) →
        ¬ (y = L ∨ y = q) → TLink N' t y d z →
        (y = y3 ∧ d = k1 ∧ z = y1) ∨ (y = y3 ∧ d = r0.1 ∧ z = y2) ∨ (y = g ∧ d = kq ∧ z = y3) ∨
        (z = v ∧ d = cv ∧ ((y = y1 ∧ cv < r0.1) ∨ (y = y2 ∧ r0.1 ≤ cv))) := by
      intro y d hy hyg hl
      have hfr := hfresh z hz
      have hyL : y ≠ L := fun h => hyg (Or.inl h)
      have hyq : y ≠ q := fun h => hyg (Or.inr h)
      by_cases hy1 : y = y1
      · rw [hy1] at hl
        rcases h1l d z hl with ⟨h, hlt⟩ | ⟨hmem, _⟩
        · simp only [Prod.mk.injEq] at h
          exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1, Or.inl ⟨hy1, hlt⟩⟩))
        · exact absurd (hLlink d z hmem) (hfr L d hL)
      · by_cases hy2 : y = y2
        · rw [hy2] at hl
          rcases h2l d z hl with ⟨h, hge⟩ | ⟨hmem, _⟩
          · simp only [Prod.mk.injEq] at h
            exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1, Or.inr ⟨hy2, hge⟩⟩))
          · exact absurd (hLlink d z hmem) (hfr L d hL)
        · by_cases hy3 : y = y3
          · rw [hy3] at hl
            rcases h3l d z hl with ⟨hd, h⟩ | ⟨hd, h, _⟩ | ⟨hmem, _, _⟩
            · exact Or.inr (Or.inl ⟨hy3, hd, h⟩)
            · exact Or.inl ⟨hy3, hd, h⟩
            · exact absurd ⟨qn, hqn, hmem⟩ (hfr q d hq)
          · by_cases hyv : y = v
            · rw [hyv] at hl; exact absurd hl (hvl d z)
            · have hyR := hReachOr y hy hy1 hy2 hy3 hyv
              by_cases hyg' : y = g
              · rw [hyg'] at hl
                rcases hgl d z hl with ⟨hd, h⟩ | ⟨_, hmem⟩
                · exact Or.inr (Or.inr (Or.inl ⟨hyg', hd, h⟩))
                · exact absurd ⟨gn, hgn, hmem⟩ (hfr g d hg)
              · exact absurd (hOld y hyL hyq hyg' hy1 hy2 hy3 d z hl) (hfr y d hyR)
    rcases hone u c' hu hug hl1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
      rcases hone u' c'' hu' hug' hl2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
    all_goals first
      | exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
      | exact absurd (c1.symm.trans c2) h12
      | exact absurd (c2.symm.trans c1) h12
      | exact absurd (c1.symm.trans c2) h13
      | exact absurd (c2.symm.trans c1) h13
      | exact absurd (c1.symm.trans c2) h23
      | exact absurd (c2.symm.trans c1) h23
      | exact absurd (a1.symm.trans c2) hv1
      | exact absurd (a1.symm.trans c2) hv2
      | exact absurd (a1.symm.trans c2) hv3
      | exact absurd (a2.symm.trans c1) hv1
      | exact absurd (a2.symm.trans c1) hv2
      | exact absurd (a2.symm.trans c1) hv3
      | (refine ⟨?_, b1.trans b2.symm⟩
         rcases c1 with ⟨h1, hlt⟩ | ⟨h1, hge⟩ <;> rcases c2 with ⟨h2, hlt'⟩ | ⟨h2, hge'⟩
         · exact h1.trans h2.symm
         · omega
         · omega
         · exact h1.trans h2.symm)
  · intro z hz hzg
    rcases hz with h | h | h | h <;> rcases hzg with h' | h' <;> rw [h] at h'
    · exact hne L n hLn y1 hf1 h'.symm
    · exact hne q qn hqn y1 hf1 h'.symm
    · exact hne L n hLn y2 hf2 h'.symm
    · exact hne q qn hqn y2 hf2 h'.symm
    · exact hne L n hLn y3 hf3 h'.symm
    · exact hne q qn hqn y3 hf3 h'.symm
    · exact hne L n hLn v hvN h'.symm
    · exact hne q qn hqn v hvN h'.symm
  · by_cases hrg : r = g
    · rw [hrg, hN'g]; exact ⟨_, rfl⟩
    · have hrL : r ≠ L := fun h => hT.rootFree q k1 hq (by rw [h]; exact hqL_link)
      have hrq : r ≠ q := fun h => hT.rootFree g kq hg (by rw [h]; exact hgq_link)
      obtain ⟨rm, hrm⟩ := hT.rootKey
      rw [hother r hrL hrq hrg (hne r rm hrm y1 hf1) (hne r rm hrm y2 hf2) (hne r rm hrm y3 hf3)]
      exact ⟨rm, hrm⟩

/-- The writer's space split of a leaf with the time split of its full parent
keeps the writer's tree (`writerWP_appendKlongs_spaceSplitTime` with
`treeOK_spaceSplitTime`). -/
theorem writerWP_appendKlongs_spaceSplitTime_tree (base : View BVal) (d'' : Nat) (L q g : NodeId)
    (n qn gn : KNode) (kq k1 cv v : Nat) (c : Ctx) (w : W) (r0 : Nat × NodeId)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hgR : TReach (wNode c.p base w) c.i w.top.rootKey g)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hlg : w.nodes.lookup g = some gn)
    (hLt : w.taken.contains L = false) (hqt' : w.taken.contains q = false)
    (hgt' : w.taken.contains g = false)
    (hgk : (kq, q) ∈ gn.liveAt c.i) (hqk : (k1, L) ∈ qn.liveAt c.i)
    (hgwf : klongsWf gn.ks = true) (hgt : ∀ s, Klong.time s ∈ gn.ks → s ≤ c.i)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hnleaf : n.leaf = true) (hr0 : (n.live.drop (n.live.length / 2)).head? = some r0)
    (hql : qn.leaf = false) (hgl : gn.leaf = false)
    (hfirst : n.firstTime ≠ some c.i) (hqfirst : qn.firstTime ≠ some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hqfull : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2))) = false))
    (hqsplit : c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpg : (w.path[d'']?).map (·.2) = some g) (hpq : w.path[d'' + 1]? = some (some kq, q))
    (hpk : w.path[d'' + 1 + 1]? = some (some k1, L))
    (hroomg : gn.size + 1 + 1 ≤ c.p.M) (hdeadg : ∀ y, deadOver c.p (gn.add c.i (.key kq y)) = false)
    (hf1 : wNode c.p base w w.next = none) (hf2 : wNode c.p base w (w.next + 2) = none)
    (hf3 : wNode c.p base w (w.next + 2 + 2) = none)
    (ht1 : w.taken.contains w.next = false) (ht2 : w.taken.contains (w.next + 2) = false)
    (ht3 : w.taken.contains (w.next + 2 + 2) = false)
    (hvN : wNode c.p base w v = none) (hv1 : v ≠ w.next) (hv2 : v ≠ w.next + 2)
    (hv3 : v ≠ w.next + 2 + 2)
    (hfresh : ∀ z, (z = w.next ∨ z = w.next + 2 ∨ z = w.next + 2 + 2 ∨ z = v) →
      ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u → ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (appendKlongs (d'' + 1 + 1) L [(cv, v)]) c w
      (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  have hwL : wNode c.p base w L = some n := by simp only [wNode, hLt, Bool.false_eq_true, ↓reduceIte, hlk]
  have hwq : wNode c.p base w q = some qn := by simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hlq]
  have hwg : wNode c.p base w g = some gn := by simp only [wNode, hgt', Bool.false_eq_true, ↓reduceIte, hlg]
  have hgqL : TLink (wNode c.p base w) c.i g kq q := ⟨gn, hwg, hgk⟩
  have hq : TReach (wNode c.p base w) c.i w.top.rootKey q := TReach.link hgR hgqL
  have hqL : q ≠ L := fun h => hT.no_self_link q k1 hq (by rw [← h] at hqk; exact ⟨qn, hwq, hqk⟩)
  have hgq : g ≠ q := fun h => hT.no_self_link g kq hgR (by rw [← h] at hgqL; exact hgqL)
  have hgL : g ≠ L := fun h => hT.no_two_cycle g q kq k1 hgqL (by rw [h]; exact ⟨qn, hwq, hqk⟩) hgR
  have hnone : ∀ z, w.taken.contains z = false → wNode c.p base w z = none → w.nodes.lookup z = none := by
    intro z htz hfz
    unfold wNode at hfz; simp only [htz, Bool.false_eq_true, ↓reduceIte] at hfz
    split at hfz
    · cases hfz
    · assumption
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitTime d'' L q g n qn gn kq k1 cv v c w hlk hlq
    hlg hqL hgq hgL hql hgl hfirst hqfirst hfull hsplit hqfull hqsplit hpg hpq hpk hroomg hdeadg
    (hnone _ ht1 hf1) (hnone _ ht2 hf2) (hnone _ ht3 hf3)) ?_
  intro _ w' ⟨lq, _, _, hlq_times, hlq_look, h'taken, h'top, _, h'nodes⟩
  rw [h'top]
  rw [hnleaf] at hlq_look h'nodes
  have h12 : w.next ≠ w.next + 2 := by omega
  have h13 : w.next ≠ w.next + 2 + 2 := by omega
  have h23 : w.next + 2 ≠ w.next + 2 + 2 := by omega
  have hne : ∀ z m, wNode c.p base w z = some m → ∀ y, wNode c.p base w y = none → z ≠ y :=
    fun z m hz y hy he => by rw [he, hy] at hz; cases hz
  have hN' : ∀ x, wNode c.p base w' x = if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.toPrev (c.i - 1))
      else if x = g then some (gn.add c.i (.key kq (w.next + 2 + 2)))
      else if x = w.next then some (halves true c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = w.next + 2 then some (halves true c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else if x = w.next + 2 + 2 then some ⟨qn.leaf, lq.ks⟩
      else wNode c.p base w x := by
    intro x
    unfold wNode
    rw [h'taken, h'nodes x]
    by_cases hxL : x = L
    · subst hxL; simp only [hLt, Bool.false_eq_true, ↓reduceIte]
    · by_cases hxq : x = q
      · subst hxq; simp only [hqt', hxL, Bool.false_eq_true, ↓reduceIte]
      · by_cases hxg : x = g
        · subst hxg; simp only [hgt', hxL, hxq, Bool.false_eq_true, ↓reduceIte]
        · by_cases hx1 : x = w.next
          · subst hx1; simp only [ht1, hxL, hxq, hxg, Bool.false_eq_true, ↓reduceIte]
          · by_cases hx2 : x = w.next + 2
            · subst hx2; simp only [ht2, hxL, hxq, hxg, hx1, Bool.false_eq_true, ↓reduceIte]
            · by_cases hx3 : x = w.next + 2 + 2
              · subst hx3; simp only [ht3, hxL, hxq, hxg, hx1, hx2, Bool.false_eq_true, ↓reduceIte]
              · simp only [hxL, hxq, hxg, hx1, hx2, hx3, ↓reduceIte]
  have hL1 := hne L n hwL _ hf1
  have hL2 := hne L n hwL _ hf2
  have hL3 := hne L n hwL _ hf3
  have hq1 := hne q qn hwq _ hf1
  have hq2 := hne q qn hwq _ hf2
  have hq3 := hne q qn hwq _ hf3
  have hg1 := hne g gn hwg _ hf1
  have hg2 := hne g gn hwg _ hf2
  have hg3 := hne g gn hwg _ hf3
  apply treeOK_spaceSplitTime (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey g q L w.next
    (w.next + 2) (w.next + 2 + 2) v gn qn n lq kq k1 cv r0 hT hgR hwg hgk hgwf hgt hwq hqk hqt hwL hnleaf
    hr0 hnt hlq_times hlq_look
  · rw [hN' g]; simp [hgL, hgq]
  · rw [hN' w.next]; simp [Ne.symm hL1, Ne.symm hq1, Ne.symm hg1]
  · rw [hN' (w.next + 2)]; simp [Ne.symm hL2, Ne.symm hq2, Ne.symm hg2]
  · rw [hN' (w.next + 2 + 2)]; simp [Ne.symm hL3, Ne.symm hq3, Ne.symm hg3, Ne.symm h13]
  · intro z hzL hzq hzg hz1 hz2 hz3
    rw [hN' z]; simp [hzL, hzq, hzg, hz1, hz2, hz3]
  · exact hf1
  · exact hf2
  · exact hf3
  · exact hvN
  · exact h12
  · exact h13
  · exact h23
  · exact hv1
  · exact hv2
  · exact hv3
  · exact hfresh

end SIS.Tree
