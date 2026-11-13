import SIS.Tree.GetSpaceSpace
import SIS.Tree.PutInvDelFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The delete into a full leaf (bergdb 024-12, TP10): the bitmap does not fit,
or the leaf would hold too many dead klongs, and the leaf is time split into
its last version without the key. The reading after it
(`getFromR_timeSplit_del`): the key reads as no value, every other key as
before. -/

/-- The reading after a time split of the leaf L into the new node y whose live
klongs are L's but the compare value cv's, its parent q's klong k1 to L now
naming y: the key reads as no value, every other key as before. -/
theorem getFromR_timeSplit_del (N N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q y : NodeId) (n qn m : KNode)
    (k1 : Nat) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hml : m.leaf = true) (hmwf : klongsWf m.ks = true) (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i)
    (hmlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c)
    (hN2y : N2 y = some m) (hN2q : N2 q = some (qn.add i (.key k1 y)))
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ y → N2 x = N x)
    (hVL : V L = none) (hVy : V y = none)
    (hqL : q ≠ L) (hyL : y ≠ L) (hyq : y ≠ q) (hNy : N y = none)
    (hrootL : root ≠ L) (hrooty : root ≠ y) (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i → z ≠ y) :
    ∀ key', keyWf key' = true → getFromR N2 V i fuel key' root =
      if pre ++ [cv] == key' then none else getFromR N V i fuel key' root := by
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNmq : Nm q = some qn := by simp [Nm, hqL, hNq]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hmem' : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hmlook] at this
    by_cases hc : c = cv
    · subst hc; simp at this
    · have hc' : (c == cv) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [hL1]; exact lookup_some_mem this
  have hreach := reach_change N i root L y n m hNL (fun c z hz => Or.inl (hmem' c z hz)) hNy hyL
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq (by
    rw [KNode.liveAt_of_times qn i hqt]; exact hk1)
  -- the facts the renaming needs, through Nm
  have hwfm : ∀ x xn, ReachS Nm i root x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNy] at hn; cases hn
  have hnotL : ∀ x xn, ReachS Nm i root x → x ≠ q → Nm x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ L := by
    intro x xn hx hxq hn c z hz hzL
    subst hzL
    by_cases hxL : x = z
    · subst hxL
      rw [hNmL] at hn; cases hn
      exact hxq (honlyL x n c hrL hNL (hmem' c x hz)).1
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hxq (honlyL x xn c hx' hn hz).1
      · subst hxv; rw [hNy] at hn; cases hn
  have hnoty : ∀ x xn, ReachS Nm i root x → Nm x = some xn → ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ y := by
    intro x xn hx hn c z hz
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      exact hfr x n c z hrL hNL (hmem' c z hz)
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hfr x xn c z hx' hn hz
      · subst hxv; rw [hNy] at hn; cases hn
  have honly : ∀ c z, (c, z) ∈ qn.liveAt i → z = L → c = k1 := by
    intro c z hz hzL
    subst hzL
    exact (honlyL q qn c hrq hNq hz).2
  have hS := renSim_timeSplit Nm N2 i root L q y qn m k1 hqL hyL hyq hNmL hNmq hql hqwf hqt hk1
    honly hN2y hN2q (fun x h1 h2 h3 => by rw [hN2 x h1 h2 h3, hNm x h1]) hwfm hnotL hnoty
  have hren : ∀ key', getFromR Nm V i fuel key' root = getFromR N2 V i fuel key' root := by
    intro key'
    have := getFromR_ren Nm N2 V V i fuel _ L y hS (fun a => by
      by_cases ha : a = L
      · subst ha; simp [hVL, hVy]
      · simp [ha]) key' root ⟨hrooty, ReachS.root⟩
    rw [this]
    simp [hrootL]
  have hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (m.searchEq i c').map (·.y) := by
    intro c' hc'
    rw [KNode.searchEq_live n i hnwf hnt, KNode.searchEq_live m i hmwf hmt, hmlook]
    have : (c' == cv) = false := by simpa using hc'
    rw [this]; rfl
  have hA := getFromR_leaf_change_seg N Nm V V i fuel hfuel L pre cv root rk n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs hrk hcv hvisL huniq
    (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  intro key' hkey'
  rw [← hren]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-! ## The writer's time splits with nothing to insert, the values kept -/

set_option linter.unusedSimpArgs false in
/-- `writerWP_handleFullWith_timeSplit_nil` with the values kept. -/
theorem writerWP_handleFullWith_timeSplit_nilV (d' : Nat) (L q : NodeId) (n qn last : KNode)
    (k1 : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact) c w
      (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
        ∀ x, w'.nodes.lookup x =
          if x = L then some (n.toPrev (c.i - 1))
          else if x = q then some (qn.add c.i (.key k1 w.next))
          else if x = w.next then some ⟨n.leaf, last.ks⟩
          else w.nodes.lookup x) := by
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
    simp only [writerWP_pure, hql, hcs, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        w2.nodes = upsert (w.nodes ++ [(w.next, { leaf := n.leaf, ks := last.ks })]) q
          (qn.add c.i (.key k1 w.next)) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
            ∀ x, w'.nodes.lookup x =
              if x = L then some (n.toPrev (c.i - 1))
              else if x = q then some (qn.add c.i (.key k1 w.next))
              else if x = w.next then some ⟨n.leaf, last.ks⟩
              else w.nodes.lookup x) := by
      intro w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n, lookup_upsert]
        simp [show L ≠ q from fun h => hqL h.symm, List.lookup_append, hlk]
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨h2t, h2top, h2v, ?_⟩
      intro x
      rw [lookup_upsert, h2n, lookup_upsert]
      by_cases hxL : x = L
      · simp [hxL]
      · simp only [hxL, ↓reduceIte]
        by_cases hxq : x = q
        · simp [hxq]
        · simp only [hxq, ↓reduceIte, List.lookup_append]
          by_cases hxy : x = w.next
          · subst hxy; rw [hny]; simp [List.lookup]
          · simp only [hxy, ↓reduceIte]
            cases h : w.nodes.lookup x with
            | some m => rfl
            | none =>
              show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := last.ks })].lookup x) = none
              rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal _ rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
      rintro l w1 ⟨hw1, hl⟩
      subst w1 hl
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal _ rfl rfl rfl rfl

/-- `writerWP_handleFullWith_timeInPlace_nil` with the values kept. -/
theorem writerWP_handleFullWith_timeInPlace_nilV (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n last : KNode) (compact : Bool)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up depth L [] last compact) c w (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew]
  have hpar : WriterWP (parentAt depth) c w (fun _ v => v = w) := by
    unfold parentAt pathNode
    cases depth with
    | zero => simp only [writerWP_pure]
    | succ e =>
      simp only [writerWP_bind, writerWP_get]
      split
      · simp only [writerWP_pure]
      · exact writerWP_throw _ _ _ _
  refine writerWP_mono hpar ?_
  intro a w1 hw1
  subst w1
  have hrest : ∀ w2 : W, ReadsAs c.p base w w2 → w2.nodes.lookup L = some n →
      WriterWP (do
        let l ← replaceOrAdd last []
        if (l.size == 1) = true then do
            note "lone-time-klong"
            putNode L { leaf := n.leaf, ks := l.ks }
          else putNode L { leaf := n.leaf, ks := l.ks }) c w2 (fun _ w' =>
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
        ∀ y, wNode c.p base w' y = if y = L then some ⟨n.leaf, last.ks⟩ else wNode c.p base w y) := by
    intro w2 hr2 _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w3 ⟨hw3, hl⟩
    subst hw3 hl
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      refine ⟨hr2.2.2.1, hr2.2.1, hr2.2.2.2.1, ?_⟩
      intro y
      by_cases hy : y = L
      · subst hy
        simp only [wNode, hr2.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
      · rw [← hr2.1]
        simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  simp only [note, writerWP_bind] at hrest
  cases compact with
  | true =>
    simp only [↓reduceIte, note, Bool.not_true, Bool.false_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2
  | false =>
    simp only [Bool.not_false, Bool.true_and] at hcs
    simp only [hcs, ↓reduceIte, note, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2

end SIS.Tree
