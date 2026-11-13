import SIS.Tree.GetTree
import SIS.Tree.SpaceSplitMap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a full leaf below an inner parent with room, by a space split
(bergdb 024-12, TP10; `OpGetOK`'s rules): the leaf's last version and the
put's klong go to two new leaves, the parent's klong to the leaf names the
first and a new klong at the second half's first compare value names the
second. Reading a key through the parent gives what reading the leaf with the
put gave (`halves_leaf_lookup`), if the leaf's compare values lie between the
parent's klong to it and the parent's next one (the search tree's order). -/

/-! ## The parent's search after the split -/

theorem KNode.searchLte_of_max (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (c : Int) (ec : Nat) (ey : NodeId) (hm : (ec, ey) ∈ m.live) (hle : (ec : Int) ≤ c)
    (hmax : ∀ q ∈ m.live, (q.1 : Int) ≤ c → q.1 ≤ ec) :
    (m.searchLte t c).map (·.y) = some ey := by
  have hs := m.searchLte_spec t c
  unfold NodeSearchSpec at hs
  rw [KNode.liveAt_of_times m t ht] at hs
  cases h : m.searchLte t c with
  | none =>
    have := hs.2.mp h (ec, ey) hm
    simp only [decide_eq_false_iff_not] at this
    exact absurd hle this
  | some f =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs.1 f h
    simp only [decide_eq_true_eq] at hfa
    have h1 := hfmax (ec, ey) hm (by simpa using hle)
    have h2 := hmax (f.c, f.y) hfm hfa
    simp only [decide_eq_true_eq] at h1
    have hc : f.c = ec := by omega
    have hnd := KNode.live_keys_nodup m
    have hm' : (f.c, ey) ∈ m.live := by rw [hc]; exact hm
    have := (lookup_some_of_mem hnd hfm).symm.trans (lookup_some_of_mem hnd hm')
    simp only [Option.map_some, Option.some.injEq]
    exact Option.some.inj this

theorem KNode.searchLte_none_of (m : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ m.ks → s ≤ t)
    (c : Int) (hall : ∀ q ∈ m.live, c < (q.1 : Int)) : m.searchLte t c = none := by
  have hs := m.searchLte_spec t c
  unfold NodeSearchSpec at hs
  rw [KNode.liveAt_of_times m t ht] at hs
  apply hs.2.mpr
  intro q hq
  have := hall q hq
  simp only [decide_eq_false_iff_not]
  omega

/-- The parent after a space split of its child L: its klong k1 to L names the
first half F, and a klong at sc names the second half S. A search that found
k1 finds F below sc and S from sc on; any other search finds what it found. -/
theorem KNode.splitParent_searchLte (n : KNode) (t : Time) (k1 sc : Nat) (L F S : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hk1 : (k1, L) ∈ n.live) (hle : k1 ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ n.live → c' ≤ k1 ∨ sc < c') (c : Int) :
    (((n.add t (.key k1 F)).add t (.key sc S)).searchLte t c).map (·.y) =
      (n.searchLte t c).map (fun fd => if fd.c = k1 then (if c < sc then F else S) else fd.y) := by
  have hw1 := KNode.add_key_wf n t k1 F hw
  have ht1 := KNode.add_times n t (.key k1 F) (fun s h => by cases h) ht
  have ht2 := KNode.add_times _ t (.key sc S) (fun s h => by cases h) ht1
  have hlk : ∀ c', ((n.add t (.key k1 F)).add t (.key sc S)).live.lookup c' =
      if sc == c' then some S else if k1 == c' then some F else n.live.lookup c' := by
    intro c'
    rw [KNode.add_key_live_lookup_of_wf _ t sc c' S hw1, KNode.add_key_live_lookup_of_wf n t k1 c' F hw]
  have hnd := KNode.live_keys_nodup n
  have hnd2 := KNode.live_keys_nodup ((n.add t (.key k1 F)).add t (.key sc S))
  have hmem2 : ∀ c' z, (c', z) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live ↔
      (if sc = c' then z = S else if k1 = c' then z = F else (c', z) ∈ n.live) := by
    intro c' z
    rw [mem_iff_lookup _ hnd2, hlk]
    by_cases h1 : sc = c'
    · subst h1; simp [eq_comm]
    · have h1' : (sc == c') = false := by simpa using h1
      simp only [h1', Bool.false_eq_true, ↓reduceIte, h1]
      by_cases h2 : k1 = c'
      · subst h2; simp [eq_comm]
      · have h2' : (k1 == c') = false := by simpa using h2
        simp only [h2', Bool.false_eq_true, ↓reduceIte, h2]
        rw [mem_iff_lookup _ hnd]
  -- every compare value of the new node: sc, k1 or one of n's
  have hcv2 : ∀ q ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live,
      q.1 = sc ∨ q.1 = k1 ∨ q ∈ n.live := by
    intro q hq
    have := (hmem2 q.1 q.2).mp hq
    by_cases h1 : sc = q.1
    · exact Or.inl h1.symm
    · simp only [h1, ↓reduceIte] at this
      by_cases h2 : k1 = q.1
      · exact Or.inr (Or.inl h2.symm)
      · simp only [h2, ↓reduceIte] at this
        exact Or.inr (Or.inr this)
  have hs1 := n.searchLte_spec t c
  unfold NodeSearchSpec at hs1
  rw [KNode.liveAt_of_times n t ht] at hs1
  have hk1live : ((k1, F) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live) ∨ sc = k1 := by
    by_cases h : sc = k1
    · exact Or.inr h
    · left; rw [hmem2]; simp [h]
  have hsclive : (sc, S) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live := by
    rw [hmem2]; simp
  cases h1 : n.searchLte t c with
  | none =>
    have hall := hs1.2.mp h1
    have hk1c : c < (k1 : Int) := by
      have := hall (k1, L) hk1
      simp only [decide_eq_false_iff_not] at this
      omega
    rw [KNode.searchLte_none_of _ t ht2 c (fun q hq => by
      rcases hcv2 q hq with h | h | h
      · rw [h]; omega
      · rw [h]; exact hk1c
      · have := hall q h
        simp only [decide_eq_false_iff_not] at this
        omega)]
    rfl
  | some fd =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs1.1 fd h1
    simp only [decide_eq_true_eq] at hfa
    simp only [Option.map_some]
    by_cases hfk : fd.c = k1
    · simp only [hfk, ↓reduceIte]
      by_cases hcs : c < (sc : Int)
      · simp only [hcs, ↓reduceIte]
        have hsk : sc ≠ k1 := by
          intro he; rw [hfk] at hfa; omega
        rcases hk1live with hk | hk
        · apply KNode.searchLte_of_max _ t ht2 c k1 F hk (by rw [← hfk]; exact hfa)
          intro q hq hqc
          rcases hcv2 q hq with h | h | h
          · rw [h] at hqc; omega
          · omega
          · have := hfmax q h (by simpa using hqc)
            simp only [decide_eq_true_eq] at this
            omega
        · exact absurd hk hsk
      · simp only [hcs, ↓reduceIte]
        apply KNode.searchLte_of_max _ t ht2 c sc S hsclive (by omega)
        intro q hq hqc
        rcases hcv2 q hq with h | h | h
        · omega
        · omega
        · have := hfmax q h (by simpa using hqc)
          simp only [decide_eq_true_eq] at this
          omega
    · simp only [hfk, ↓reduceIte]
      have hfsc : fd.c ≠ sc := by
        intro he
        rcases hgap fd.c fd.y hfm with h | h
        · omega
        · omega
      have hmem : (fd.c, fd.y) ∈ ((n.add t (.key k1 F)).add t (.key sc S)).live := by
        rw [hmem2]
        simp only [show ¬ sc = fd.c from fun h => hfsc h.symm, show ¬ k1 = fd.c from fun h => hfk h.symm,
          ↓reduceIte]
        exact hfm
      apply KNode.searchLte_of_max _ t ht2 c fd.c fd.y hmem hfa
      intro q hq hqc
      rcases hcv2 q hq with h | h | h
      · -- sc ≤ c: then k1 ≤ c, k1 ≤ fd.c, so sc < fd.c
        have hk := hfmax (k1, L) hk1 (by simp; omega)
        simp only [decide_eq_true_eq] at hk
        rcases hgap fd.c fd.y hfm with h' | h'
        · omega
        · omega
      · rw [h] at hqc ⊢
        have hk := hfmax (k1, L) hk1 (by simpa using hqc)
        simpa using hk
      · have := hfmax q h (by simpa using hqc)
        simpa using this

/-! ## The writer's space split below an inner parent with room -/

theorem writerWP_appendKlongs_room2 (d : Nat) (q : NodeId) (qn : KNode) (k1 y1 k2 y2 : Nat)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup q = some qn) (hroom : qn.size + 2 + 1 ≤ c.p.M)
    (hdead : deadOver c.p ((qn.add c.i (.key k1 y1)).add c.i (.key k2 y2)) = false) :
    WriterWP (appendKlongs d q [(k1, y1), (k2, y2)]) c w (fun _ w' =>
      w' = { w with nodes := upsert w.nodes q ((qn.add c.i (.key k1 y1)).add c.i (.key k2 y2)) }) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  have h1 : ¬ (qn.size + [(k1, y1), (k2, y2)].length + 1 > c.p.M) := by simp; omega
  simp only [h1, ↓reduceIte, List.foldl_cons, List.foldl_nil, hdead,
    Bool.false_eq_true]
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  simp only [putNode, List.foldl_cons, List.foldl_nil, writerWP_modify]

theorem writerWP_klongAt (d k1 : Nat) (L : NodeId) (c : Ctx) (w : W)
    (h : w.path[d]? = some (some k1, L)) (post : Nat → W → Prop) :
    WriterWP (klongAt d) c w post ↔ post k1 w := by
  unfold klongAt
  simp only [writerWP_bind, writerWP_get, h, writerWP_pure]

/-- The state after a space split of a leaf L below an inner parent q with
room: the halves of L's last version with the put's klong at the next two ids,
q's klong k1 names the first, a klong at the second's first compare value names
the second, L keeps only its klongs before the transaction. -/
def SpaceSplitAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) : Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some ((qn.add c.i (.key k1 w.next)).add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2)))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else w.nodes.lookup x

theorem writerWP_handleFullWith_spaceSplit (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitAfter c w w' L q n qn k1 cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = true := by
      simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, Bool.false_eq_true,
      ↓reduceIte]
    have hq1 : q ≠ w.next + 2 := by omega
    have hq2 : q ≠ w.next := by omega
    have hL1 : L ≠ w.next + 2 := by omega
    have hL2 : L ≠ w.next := by omega
    simp only [newKey, fresh, setMadeFor, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      refine (writerWP_klongAt (d' + 1) k1 L c _ ?_ _).mpr ?_
      · exact hpk
      refine writerWP_mono (writerWP_appendKlongs_room2 d' q qn k1 w.next _ (w.next + 2) c _
        ?_ hroomq (hdeadq _ _ _ _)) ?_
      · simp only [lookup_upsert, List.lookup_append, hq1, hq2, ↓reduceIte, hlq]
        rfl
      intro _ w2 hw2
      subst hw2
      rw [writerWP_getNode_known L n c _ (by
        simp only [lookup_upsert, List.lookup_append, hqL.symm, hL1, hL2, ↓reduceIte, hlk]; rfl)]
      refine ⟨rfl, rfl, rfl, ?_⟩
      intro x
      simp only [lookup_upsert, List.lookup_append]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte]
          by_cases hx2 : x = w.next + 2
          · simp [hx2]
          · simp only [hx2, ↓reduceIte]
            by_cases hx1 : x = w.next
            · simp [hx1]
            · simp only [hx1, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show ((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                  ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hx1, lookup_cons_ne _ _ _ _ hx2]; rfl

theorem writerWP_appendKlongs_spaceSplit (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 2 + 1 ≤ c.p.M)
    (hdeadq : ∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSplitAfter c w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplit d' L q n qn k1 cv v c w hlk hlq hqL hql hfirst hsplit
    hpq hpk hroomq hdeadq hLn hqn

/-! ## The reading after the split -/

/-- The descents of reader N2, in which q's klong to the leaf L names F below
compare value sc and S from it, and F and S read as L for those compare values,
are those of reader Nm, on the nodes that Nm reaches but L, F and S. -/
theorem getEqR_split (Nm N2 : NodeId → Option KNode) (t : Time) (r0 L q F S : NodeId)
    (qn qn2 m f s : KNode) (sc : Nat)
    (hNq : Nm q = some qn) (hql : qn.leaf = false) (hN2q : N2 q = some qn2)
    (hq2l : qn2.leaf = false)
    (hqsearch : ∀ c : Nat, (qn2.searchLte t c).map (·.y) =
      (qn.searchLte t c).map (fun fd => if fd.y = L then (if c < sc then F else S) else fd.y))
    (hNmL : Nm L = some m) (hml : m.leaf = true)
    (hN2F : N2 F = some f) (hfl : f.leaf = true) (hN2S : N2 S = some s) (hsl : s.leaf = true)
    (hleafF : ∀ c, c < sc → (f.searchEq t c).map (·.y) = (m.searchEq t c).map (·.y))
    (hleafS : ∀ c, sc ≤ c → (s.searchEq t c).map (·.y) = (m.searchEq t c).map (·.y))
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      z ≠ F ∧ z ≠ S) (c : Nat) :
    ∀ (fu : Nat) (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fu x = getEqR Nm t c fu x := by
  -- reading a leaf the split made, or L, for a compare value routed to it
  have hleafRead : ∀ fu, getEqR N2 t c fu (if c < sc then F else S) = getEqR Nm t c fu L := by
    intro fu
    cases fu with
    | zero => rfl
    | succ fu =>
      by_cases hcs : c < sc
      · simp only [hcs, ↓reduceIte, getEqR, hN2F, hfl, hNmL, hml]
        exact hleafF c hcs
      · simp only [hcs, ↓reduceIte, getEqR, hN2S, hsl, hNmL, hml]
        exact hleafS c (by omega)
  intro fu
  induction fu with
  | zero => intro x _ _ _ _; rfl
  | succ fu ih =>
    intro x hx hxL hxF hxS
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
            exact hleafRead fu
          · simp only [hL, ↓reduceIte] at hs
            rw [hs]
            have hfs := hnotFS x qn fd.c fd.y hx hNq hmem
            exact ih fd.y hrfd hL hfs.1 hfs.2
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
            exact ih fd.y hrfd (hnotL x xn fd.c fd.y hx hxq hn hmem) hfs.1 hfs.2

/-- What a descent finds is named by a live klong of a leaf that it reaches. -/
theorem getEqR_leaf_link (N : NodeId → Option KNode) (t : Time) (r0 : NodeId) (cv : Nat)
    (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true) :
    ∀ (f : Nat) (x y : NodeId), ReachS N t r0 x → getEqR N t cv f x = some y →
      ∃ x' xn c, ReachS N t r0 x' ∧ N x' = some xn ∧ xn.leaf = true ∧ (c, y) ∈ xn.liveAt t := by
  intro f
  induction f with
  | zero => intro x y _ h; simp [getEqR] at h
  | succ f ih =>
    intro x y hx h
    simp only [getEqR] at h
    cases hn : N x with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only at h
      split at h
      · rename_i hl
        cases hf : n.searchEq t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact ⟨x, n, cv, hx, hn, hl, KNode.searchEq_mem n t cv fd (hwf x n hx hn) hf⟩
      · cases hf : n.searchLte t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          exact ih fd.y y (ReachS.step x n fd.c fd.y hx hn (KNode.searchLte_mem n t cv fd hf)) h

/-- `getEqR_split` for the reading of keys. -/
theorem getFromR_split (Nm N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r0 L q F S : NodeId)
    (hwf : ∀ x xn, ReachS Nm t r0 x → Nm x = some xn → klongsWf xn.ks = true)
    (hget : ∀ c (x : NodeId), ReachS Nm t r0 x → x ≠ L → x ≠ F → x ≠ S →
      getEqR N2 t c fuel x = getEqR Nm t c fuel x)
    (hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x)
    (hq : (N2 q).isSome = (Nm q).isSome)
    (hnotL : ∀ x xn c z, ReachS Nm t r0 x → x ≠ q → Nm x = some xn → (c, z) ∈ xn.liveAt t → z ≠ L)
    (hqL : ∀ xn c z, Nm q = some xn → (c, z) ∈ xn.liveAt t → xn.leaf = true → z ≠ L)
    (hnotFS : ∀ x xn c z, ReachS Nm t r0 x → Nm x = some xn → (c, z) ∈ xn.liveAt t →
      z ≠ F ∧ z ≠ S) :
    ∀ (key : List Nat) (r : NodeId), ReachS Nm t r0 r → r ≠ L → r ≠ F → r ≠ S →
      getFromR N2 V t fuel key r = getFromR Nm V t fuel key r := by
  intro key
  induction key with
  | nil => intro r _ _ _ _; rfl
  | cons cv rest ih =>
    intro r hr hrL hrF hrS
    have he := hget cv r hr hrL hrF hrS
    cases rest with
    | nil => simp only [getFromR]; rw [he]
    | cons d rest' =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR Nm t cv fuel r with
      | none => rfl
      | some z =>
        simp only
        have hz : ReachS Nm t r0 z := getEqR_reach Nm t r0 cv hwf fuel r z hr hg
        -- z is a leaf's target: neither L, F nor S
        obtain ⟨x, xn, cz, hx, hxn, hxl, hzm⟩ : ∃ x xn cz, ReachS Nm t r0 x ∧ Nm x = some xn ∧
            xn.leaf = true ∧ (cz, z) ∈ xn.liveAt t :=
          getEqR_leaf_link Nm t r0 cv hwf fuel r z hr hg
        have hzL : z ≠ L := by
          by_cases hxq : x = q
          · subst hxq; exact hqL xn cz z hxn hzm hxl
          · exact hnotL x xn cz z hx hxq hxn hzm
        have hfs := hnotFS x xn cz z hx hxn hzm
        have hsome : (N2 z).isSome = (Nm z).isSome := by
          by_cases hzq : z = q
          · rw [hzq]; exact hq
          · rw [hsame z hzL hzq hfs.1 hfs.2]
        rw [hsome]
        split
        · exact ih z hz hzL hfs.1 hfs.2
        · rfl

theorem newKlongs_times (t : Time) (l : List (Nat × NodeId)) :
    ∀ s, Klong.time s ∈ newKlongs t l → s ≤ t := by
  intro s hs
  simp only [newKlongs, List.mem_cons, List.mem_map] at hs
  rcases hs with hs | ⟨q, _, hq⟩
  · cases hs; exact Nat.le_refl _
  · cases hq

theorem KNode.lastVersion_eq_newKlongs (n : KNode) (t : Time) :
    n.lastVersion t = ⟨n.leaf, newKlongs t n.live⟩ := by
  have hk := KNode.lastVersion_keys n t
  have hl : (n.lastVersion t).leaf = n.leaf := rfl
  cases hv : n.lastVersion t with
  | mk leaf ks =>
    rw [hv] at hk hl
    simp only at hk hl
    subst hl hk
    simp only [newKlongs]

/-- After a space split of the leaf L of a key's last segment (its last version
with the put's klong to the new value v, in halves at the new nodes F and S;
q's klong k1, the one klong that named L, names F, and a klong at the second
half's first compare value names S), every key reads what it read but the key,
which reads the put's value. L's compare values lie between q's klong k1 and
q's next klong. -/
theorem getFromR_spaceSplit (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q F S v : NodeId) (n qn : KNode)
    (k1 : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i) (hlive : n.live ≠ [])
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hN2q : N2 q = some ((qn.add i (.key k1 F)).add i
      (.key (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2 S)))
    (hN2F : N2 F = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1)
    (hN2S : N2 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a)
    (hqL : q ≠ L) (hvL : v ≠ L) (hvF : v ≠ F) (hvS : v ≠ S) (hNv : N v = none)
    (hrootL : root ≠ L) (hrootF : root ≠ F) (hrootS : root ≠ S) (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ F ∧ z ≠ S) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
  -- the leaf with the put, as a reader would see it unsplit
  let m := n.add i (.key cv v)
  have hml : m.leaf = true := by simp only [m, KNode.add_leaf]; exact hnl
  have hmwf : klongsWf m.ks = true := KNode.add_key_wf n i cv v hnwf
  have hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i := KNode.add_times n i (.key cv v) (fun s h => by cases h) hnt
  have hmlook : ∀ c, m.live.lookup c = if cv == c then some v else n.live.lookup c :=
    fun c => KNode.add_key_live_lookup_of_wf n i cv c v hnwf
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNmq : Nm q = some qn := by simp [Nm, hqL, hNq]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hmem : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i ∨ z = v := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hmlook] at this
    by_cases hc : cv = c
    · subst hc
      rw [beq_self_eq_true] at this
      simp only [↓reduceIte, Option.some.injEq] at this
      exact Or.inr this.symm
    · have hc' : (cv == c) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      left; rw [hL1]; exact lookup_some_mem this
  have hreach := reach_change N i root L v n m hNL hmem hNv hvL
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq (by
    rw [KNode.liveAt_of_times qn i hqt]; exact hk1)
  have hwfm : ∀ x xn, ReachS Nm i root x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNv] at hn; cases hn
  have hnotL : ∀ x xn c z, ReachS Nm i root x → x ≠ q → Nm x = some xn →
      (c, z) ∈ xn.liveAt i → z ≠ L := by
    intro x xn c z hx hxq hn hz hzL
    subst hzL
    by_cases hxL : x = z
    · subst hxL
      rw [hNmL] at hn; cases hn
      rcases hmem c x hz with h1 | h1
      · exact hxq (honlyL x n c hrL hNL h1).1
      · exact hvL h1.symm
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hxq (honlyL x xn c hx' hn hz).1
      · subst hxv; rw [hNv] at hn; cases hn
  have hnotFS : ∀ x xn c z, ReachS Nm i root x → Nm x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ F ∧ z ≠ S := by
    intro x xn c z hx hn hz
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact (hfr x n c z hrL hNL h1).2
      · rw [h1]; exact ⟨hvF, hvS⟩
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact (hfr x xn c z hx' hn hz).2
      · subst hxv; rw [hNv] at hn; cases hn
  -- the halves
  have hlv := KNode.lastVersion_eq_newKlongs n i
  rw [hnl] at hlv
  rw [hnl, hlv] at hN2q hN2F hN2S
  obtain ⟨r, hr⟩ : ∃ r, (n.live.drop (n.live.length / 2)).head? = some r := by
    cases hd : (n.live.drop (n.live.length / 2)) with
    | nil =>
      have : n.live.length ≤ n.live.length / 2 := List.drop_eq_nil_iff.mp hd
      have : n.live.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hlive
    | cons a _ => exact ⟨a, rfl⟩
  have hrmem : r ∈ n.live := by
    have : r ∈ n.live.drop (n.live.length / 2) := by
      cases hd : (n.live.drop (n.live.length / 2)) with
      | nil => rw [hd] at hr; cases hr
      | cons a _ => rw [hd] at hr; simp only [List.head?_cons, Option.some.injEq] at hr; subst hr; simp
    exact List.mem_of_mem_drop this
  have hshape := halves_leaf_shape i n.live [(cv, v)] r hr
  simp only [List.head?_cons] at hshape
  have hsc : (halves true i ⟨true, newKlongs i n.live⟩ [(cv, v)]).2.2 = r.1 := by
    rw [hshape]; by_cases hd : r.1 ≤ cv <;> simp [hd]
  have hwfh := halves_newKlongs_wf true i n.live [(cv, v)]
  generalize hout : halves true i ⟨true, newKlongs i n.live⟩ [(cv, v)] = out at hN2q hN2F hN2S hsc hwfh hshape
  obtain ⟨f, s, sc⟩ := out
  simp only at hN2q hN2F hN2S hsc hwfh
  subst hsc
  have hfs : f.leaf = true ∧ s.leaf = true ∧ (∀ t', Klong.time t' ∈ f.ks → t' ≤ i) ∧
      (∀ t', Klong.time t' ∈ s.ks → t' ≤ i) := by
    by_cases hd : r.1 ≤ cv <;>
    · simp only [hd, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true,
        Prod.mk.injEq] at hshape
      obtain ⟨hf, hs', _⟩ := hshape
      subst hf hs'
      exact ⟨rfl, rfl, newKlongs_times i _, newKlongs_times i _⟩
  obtain ⟨hfl, hsl, hft, hst⟩ := hfs
  have hlook := halves_leaf_lookup i n.live [(cv, v)] n.live_order r hr (by simp)
  rw [hout] at hlook
  simp only at hlook
  have hleafF : ∀ c, c < r.1 → (f.searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c hc
    rw [KNode.searchEq_live f i hwfh.1 hft, KNode.searchEq_live m i hmwf hmt, hmlook]
    have := hlook c
    simp only [hc, ↓reduceIte] at this
    rw [this]
    simp [pairLookupStep]
  have hleafS : ∀ c, r.1 ≤ c → (s.searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c hc
    rw [KNode.searchEq_live s i hwfh.2 hst, KNode.searchEq_live m i hmwf hmt, hmlook]
    have := hlook c
    simp only [show ¬ c < r.1 by omega, ↓reduceIte] at this
    rw [this]
    simp [pairLookupStep]
  -- the parent's search
  have hqsearch : ∀ c : Nat,
      (((qn.add i (.key k1 F)).add i (.key r.1 S)).searchLte i c).map (·.y) =
        (qn.searchLte i c).map (fun fd => if fd.y = L then (if c < r.1 then F else S) else fd.y) := by
    intro c
    have hA := KNode.splitParent_searchLte qn i k1 r.1 L F S hqwf hqt hk1 (hrange r.1 r.2 hrmem).1
      (fun c' z hz => by
        by_cases hc : c' ≤ k1
        · exact Or.inl hc
        · exact Or.inr ((hrange r.1 r.2 hrmem).2 c' z hz (by omega))) c
    rw [hA]
    cases hs : qn.searchLte i c with
    | none => rfl
    | some fd =>
      simp only [Option.map_some, Option.some.injEq]
      have hmemfd := KNode.searchLte_mem qn i c fd hs
      rw [KNode.liveAt_of_times qn i hqt] at hmemfd
      have hyL : fd.y = L ↔ fd.c = k1 := by
        constructor
        · intro hy
          rw [hy] at hmemfd
          exact (honlyL q qn fd.c hrq hNq (by rw [KNode.liveAt_of_times qn i hqt]; exact hmemfd)).2
        · intro hc
          rw [hc] at hmemfd
          exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup qn) hmemfd).symm.trans
            (lookup_some_of_mem (KNode.live_keys_nodup qn) hk1))
      by_cases hc : fd.c = k1
      · simp only [hc, ↓reduceIte, hyL.mpr hc, Int.ofNat_lt]
      · have hy : ¬ fd.y = L := fun h => hc (hyL.mp h)
        simp only [hc, ↓reduceIte, hy]
  have hq2l : ((qn.add i (.key k1 F)).add i (.key r.1 S)).leaf = false := by
    rw [KNode.add_leaf, KNode.add_leaf]; exact hql
  have hsame : ∀ x, x ≠ L → x ≠ q → x ≠ F → x ≠ S → N2 x = Nm x := by
    intro x h1 h2 h3 h4
    rw [hN2 x h1 h2 h3 h4, hNm x h1]
  have hsim := getFromR_split Nm N2 V2 i fuel root L q F S hwfm
    (fun c x hx hxL hxF hxS => getEqR_split Nm N2 i root L q F S qn _ m f s r.1 hNmq hql hN2q hq2l
      hqsearch hNmL hml hN2F hfl hN2S hsl hleafF hleafS hsame hnotL hnotFS c fuel x hx hxL hxF hxS)
    hsame (by rw [hN2q, hNmq]; rfl) hnotL
    (fun xn c z hxn _ hxl => by rw [hNmq] at hxn; cases hxn; rw [hql] at hxl; cases hxl) hnotFS
  have hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (m.searchEq i c').map (·.y) := by
    intro c' hc'
    rw [KNode.searchEq_live n i hnwf hnt, KNode.searchEq_live m i hmwf hmt, hmlook]
    have : (cv == c') = false := by
      cases hb : (cv == c') with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hb).symm hc'
    rw [this]; rfl
  have hA := getFromR_leaf_change_seg N Nm V V2 i fuel hfuel L pre cv root rk n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs hrk hcv hvisL huniq
    (fun key' x c' m' y' _ hx hm' hml' hs' => by
      have hrx : ReachS N i root x := fromVisits_reach N i fuel root hwf key' root x c' ReachS.root hx
      have hy' : y' ≠ v := by
        cases hfd : m'.searchEq i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact (hfr x m' c' fd.y hrx hm' (KNode.searchEq_mem m' i c' fd (hwf x m' hrx hm') hfd)).1
      exact (hV2 y' hy').symm)
  intro key' hkey'
  rw [hsim key' root ReachS.root hrootL hrootF hrootS]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full by its size, below an inner parent with room for two klongs, with
more than h klongs in its last version: the space split changes the reading by
the put alone. The premises are those of the time split rule
(`writerWP_put_timeSplit_key`), and the search tree's order for L below its
parent: L's compare values lie between the parent's klong to L and its next
one. -/
theorem writerWP_put_spaceSplit_key (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧
      n.live ≠ [] ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 2 + 1 ≤ c.p.M ∧
      ∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false)
    (hrange : ∀ q qn L n k1, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
      (k1, L) ∈ qn.live →
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
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
        z ≠ w.next ∧ z ≠ w.next + 2 ∧ z ≠ w.next + 4) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_prefix_src c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) (by subst hw2; simp) ?_
  intro w2' hr2' hp2' hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel rk w2' ht2 hp2')
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, hget, hdp⟩, ⟨hcache3, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL hget hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨htimes, hfull, hfirst, hsplit, hlive, hLroot⟩ := hleaf L n hvisL hn hnl
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  rcases hdp with ⟨hLrk, _⟩ | ⟨pre', q, k1, qn, fd, hp3, hlast, hq, hql, hqs, hc, hy, hqv⟩
  · subst hLrk
    rw [hinner n hn] at hnl
    cases hnl
  rw [hr0.1] at hq hqv
  obtain ⟨hqt, hroomq, hdeadq⟩ := hparent q qn hqv hq hql
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    have : ¬ n.size + 1 < c.p.M := by omega
    simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  -- ids in the writer's nodes are below the next id
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hne : w2'.path ++ pre' ≠ [] := by
    intro he
    have : w2'.path = [] := (List.append_eq_nil_iff.mp he).1
    rw [this] at hp2'
    simp at hp2'
  obtain ⟨d', hd'⟩ : ∃ d', (w2'.path ++ pre').length = d' + 1 := by
    cases h' : (w2'.path ++ pre').length with
    | zero => exact absurd (List.eq_nil_of_length_eq_zero h') hne
    | succ k => exact ⟨k, rfl⟩
  have hlen : w3.path.length - 1 = d' + 1 := by
    rw [hp3]; simp only [List.append_assoc, List.length_append, List.length_singleton] at hd' ⊢
    omega
  have hpq : (w3.path[d']?).map (·.2) = some q := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_left (by omega)]
    rw [List.getLast?_eq_getElem?] at hlast
    rw [hd'] at hlast
    simpa using hlast
  have hpk : w3.path[d' + 1]? = some (some k1, L) := by
    rw [hp3, List.append_assoc, ← List.append_assoc w2'.path pre' [(some k1, L)],
      List.getElem?_append_right (by omega), hd']
    simp
  have hlq : w3.nodes.lookup q = some qn := hcache3 q qn hqv hq
  have hqL : q ≠ L := by
    intro hqL'
    rw [hqL'] at hq
    rw [hn] at hq
    cases hq
    rw [hnl] at hql
    cases hql
  rw [hlen]
  have hLlt3 : L < w3.next + 2 := by have := hsrcw3 L (by rw [hlk3]; rfl); omega
  have hqlt3 : q < w3.next + 2 := by have := hsrcw3 q (by rw [hlq]; rfl); omega
  refine writerWP_mono (writerWP_appendKlongs_spaceSplit d' L q n qn k1 cv w3.next c _
    (by simpa using hlk3) (by simpa using hlq) hqL hql hfirst hfull hsplit
    (by simpa using hpq) (by simpa using hpk) hroomq hdeadq hLlt3 hqlt3) ?_
  intro _ wf hSS
  obtain ⟨hft, hftop, hfv, hfn⟩ := hSS
  simp only at hft hftop hfv hfn
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfn
  -- facts on ids
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hqlt : q < w.next := hsrcw3 q (by rw [hlq]; rfl)
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
    intro z hz
    apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega
  have hnodenone : ∀ z, w.next ≤ z → w.nodes.lookup z = none := by
    intro z hz
    cases h' : w.nodes.lookup z with
    | none => rfl
    | some _ => have := hidn z (by rw [h']; rfl); omega
  -- reachability
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwf pre _ rk ReachS.root hrk
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    eqVisits_reach _ _ _ cv c.p.fuel rk L cv hrrk hvisL
  have hk1 : (k1, L) ∈ qn.live := by
    have := KNode.searchLte_mem qn c.i cv fd hqs
    rw [KNode.liveAt_of_times qn c.i hqt, hc, hy] at this
    exact this
  have hres := getFromR_spaceSplit (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q (w.next + 2) (w.next + 2 + 2) w.next n qn
    k1 pre cv h rk hn hnl (hwf L n hrL hn) htimes hlive hq hql (hwf q qn hrq hq) hqt hk1
    (hrange q qn L n k1 hqv hq hql hn hk1)
    (by
      have hqt' : wf.taken.contains q = false := by
        rw [hft]; exact ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
      simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hfn, hqL])
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      have h1 : w.next + 2 ≠ L := by omega
      have h2 : w.next + 2 ≠ q := by omega
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn, h1, h2])
    (by
      have hyt : wf.taken.contains (w.next + 2 + 2) = false := by
        rw [hft]; exact hntake _ (by omega)
      have h1 : w.next + 2 + 2 ≠ L := by omega
      have h2 : w.next + 2 + 2 ≠ q := by omega
      have h3 : w.next + 2 + 2 ≠ w.next + 2 := by omega
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn, h1, h2, h3])
    (by
      intro x hxL hxq hxF hxS
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxq, hxF, hxS, ↓reduceIte, hr03.2.2.1])
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    hqL (by omega) (by omega) (by omega)
    (by
      simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
        hnodenone _ (Nat.le_refl _), hbase])
    hLroot.symm (by omega) (by omega) hrq hrk (keyWf_last_notin pre cv hkey) hvisL huniq hwf
    (fun x xn cc hx hxn hc => htreeK x xn cc L hx hxn hc (by simp [hn]) q qn k1 hrq hq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1))
    (fun x xn cc z hx hxn hz => by
      have := hfr x xn cc z hx hxn hz
      exact ⟨this.1, this.2.1, by omega⟩)
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

/-- The space split rule with the writer's tree and `ValueLinksOK` for TREE. -/
theorem writerWP_put_spaceSplit_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ c.p.M ≤ n.size + 1 ∧
      n.firstTime ≠ some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧
      n.live ≠ [] ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 2 + 1 ≤ c.p.M ∧
      ∀ a y b z, deadOver c.p ((qn.add c.i (.key a y)).add c.i (.key b z)) = false)
    (hrange : ∀ q qn L n k1, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
      (k1, L) ∈ qn.live →
      ∀ c' z, (c', z) ∈ n.live → k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (huniq : ∀ key' x n, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n → n.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hv : ValueLinksOK (wNode c.p base w) c.i w.top.rootKey)
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
        z ≠ w.next ∧ z ≠ w.next + 2 ∧ z ≠ w.next + 4) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  apply writerWP_put_spaceSplit_key c base hvc pre cv h rk w
    (htreeK := treeK_of_treeOK _ _ _ hT hv)
  all_goals assumption

end SIS.Tree
