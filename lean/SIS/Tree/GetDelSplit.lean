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

/-! ## The rule: a delete into a leaf below an inner parent with room -/

set_option linter.unusedSimpArgs false in
/-- The bitmap of a delete in the leaf L at the end of the key's descent, below
the inner parent q with room, the merges off: with room for the bitmap, or L
full by its size or by its dead klongs, time split (in place for a leaf the
transaction made) when its last version without the key has at most h klongs.
The state reads the key as no value, every other key as before. -/
theorem writerWP_appendDeleteKlong_get (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv k1 d' : Nat) (rk L q : NodeId) (n qn : KNode) (w w3 : W)
    (hfuel : 1 ≤ c.p.fuel) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvisL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hLt : w.taken.contains L = false) (hLval : wValue base w L = none)
    (hLroot : L ≠ w.top.rootKey)
    (hqn : wNode c.p base w q = some qn) (hql : qn.leaf = false)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) (hk1 : (k1, L) ∈ qn.live) (hqL : q ≠ L)
    (hqtk : w.taken.contains q = false)
    (hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q)
    (honlyL : ∀ x xn c', ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (c', L) ∈ xn.liveAt c.i → x = q ∧ c' = k1)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next)
    (hr3 : ReadsAs c.p base w w3)
    (hlk3 : w3.nodes.lookup L = some n) (hlq3 : w3.nodes.lookup q = some qn)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hpq : (w3.path[d']?).map (·.2) = some q) (hpk : w3.path[d' + 1]? = some (some k1, L))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hsplit : c.p.M ≤ n.size + 1 →
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (appendDeleteKlong L (d' + 1) cv) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hnwf := hwfG L n hn
  have hqwf := hwfG q qn hqn
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  -- a state whose leaf L changed to n2, n's live klongs but cv's: the delete
  have hleafc : ∀ (n2 : KNode) (w6 : W), n2.leaf = true → w6.top = w.top →
      w6.taken = w.taken → w6.vals = w.vals →
      (∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x) → wNode c.p base w6 L = some n2 →
      (∀ c', (n2.searchEq c.i c').map (·.y) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      ∀ key', keyWf key' = true →
        wGet c.p c.i base w6 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key' := by
    intro n2 w6 hl2 h6top h6taken h6vals hN hNL6 hs2
    have hV : ∀ y, wValue base w y = wValue base w6 y := by
      intro y; simp only [wValue, h6taken, h6vals]
    obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w6 L pre cv rk n n2 hfuel h6top hN
      hn hNL6 hnl hl2 (fun c' hc' => by
        rw [hs2 c']
        have hb : (c' == cv) = false := by simpa using hc'
        rw [hb]; rfl)
      hrk (keyWf_last_notin pre cv hkey) hvisL huniq (fun _ _ _ _ y _ _ _ _ _ => hV y)
    intro key' hkey'
    by_cases hk : pre ++ [cv] = key'
    · subst hk
      simp only [beq_self_eq_true, ↓reduceIte]
      rw [hown, hs2 cv]
      simp
    · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      exact hother key' hkey' (fun h => hk h.symm)
  -- the last version without cv
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  generalize hU : bitsUnion n.lastBitmap (n.bitsOf cv) = U at hne hsplit hleq hlt hlook0 hwf0
  generalize hlast : n.lastVersionGivenDel c.i U = last at hleq hlt hsplit hlook0 hwf0
  have hmwf : klongsWf (⟨n.leaf, last.ks⟩ : KNode).ks = true := hwf0
  have hmt : ∀ s, Klong.time s ∈ (⟨n.leaf, last.ks⟩ : KNode).ks → s ≤ c.i := hlt
  have hmlook : ∀ c', (⟨n.leaf, last.ks⟩ : KNode).live.lookup c' =
      if c' == cv then none else n.live.lookup c' := by
    intro c'; rw [hleq]; exact hlook0 c'
  have hms : ∀ c', ((⟨n.leaf, last.ks⟩ : KNode).searchEq c.i c').map (·.y) =
      if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [KNode.searchEq_live _ c.i hmwf hmt, hmlook, KNode.searchEq_live n c.i hnwf hnt]
  -- the outcome of a time split of the full leaf
  have htime0' : ∀ (compact : Bool), (!compact && decide (last.size > c.p.splitAbove)) = false →
      ∀ (s : String), WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 => ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro compact hcs s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3'
    have hlk3' : w3'.nodes.lookup L = some n := by rw [← hw3']; exact hlk3
    have hlq3' : w3'.nodes.lookup q = some qn := by rw [← hw3']; exact hlq3
    have hsrc3' : ∀ z, (w3'.nodes.lookup z).isSome = true → z < w.next := by rw [← hw3']; exact hsrc3
    have hpq' : (w3'.path[d']?).map (·.2) = some q := by rw [← hw3']; exact hpq
    have hpk' : w3'.path[d' + 1]? = some (some k1, L) := by rw [← hw3']; exact hpk
    have hr3' : ReadsAs c.p base w w3' := by rw [← hw3']; exact hr3
    have hnext3' : w3'.next = w.next := hr3'.2.2.2.2
    by_cases hnew : n.firstTime = some c.i
    · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nilV _ (d' + 1) L n last compact c
        base hvc w3' hlk3' (by rw [hr3'.2.2.1]; exact hLt) hnew hcs) ?_
      intro _ w4 ⟨h4t, h4top, h4v, hN4⟩
      refine hleafc ⟨n.leaf, last.ks⟩ w4 hnl (h4top.trans hr3'.2.1) (h4t.trans hr3'.2.2.1)
        (h4v.trans hr3'.2.2.2.1) ?_ (by rw [hN4]; simp) hms
      intro x hx; rw [hN4]; simp only [hx, ↓reduceIte]; rw [hr3'.1]
    · have hny : w3'.nodes.lookup w3'.next = none := by
        cases h' : w3'.nodes.lookup w3'.next with
        | none => rfl
        | some _ => have := hsrc3' _ (by rw [h']; rfl); omega
      refine writerWP_mono (writerWP_handleFullWith_timeSplit_nilV d' L q n qn last k1 compact c w3'
        hlk3' hlq3' hqL hql hnew hcs hpq' hpk' hroomq hdeadq hny) ?_
      intro _ w4 ⟨h4t, h4top, h4v, h4nodes⟩
      rw [hnext3'] at h4nodes
      have htk : w4.taken = w.taken := h4t.trans hr3'.2.2.1
      have hvl : w4.vals = w.vals := h4v.trans hr3'.2.2.2.1
      have htp : w4.top = w.top := h4top.trans hr3'.2.1
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
      have hLlt : L < w.next := hsrc3 L (by rw [hlk3]; rfl)
      have hqlt : q < w.next := hsrc3 q (by rw [hlq3]; rfl)
      have hV4 : wValue base w4 = wValue base w := by
        funext a; simp only [wValue, htk, hvl]
      have hres := getFromR_timeSplit_del (wNode c.p base w) (wNode c.p base w4) (wValue base w)
        c.i c.p.fuel hfuel w.top.rootKey L q w.next n qn ⟨n.leaf, last.ks⟩ k1 pre cv rk
        hn hnl hnwf hnt hqn hql hqwf hqt hk1 hnl hmwf hmt hmlook
        (by
          have hyt : w.taken.contains w.next = false := hntake _ (Nat.le_refl _)
          simp only [wNode, htk, hyt, Bool.false_eq_true, ↓reduceIte, h4nodes,
            show w.next ≠ L by omega, show w.next ≠ q by omega])
        (by simp only [wNode, htk, hqtk, Bool.false_eq_true, ↓reduceIte, h4nodes, hqL])
        (by
          intro x hxL hxq hxy
          rw [← hr3'.1]
          simp only [wNode, htk, hr3'.2.2.1, h4nodes, hxL, hxq, hxy, ↓reduceIte])
        hLval
        (by
          simp only [wValue, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            hvalnone _ (Nat.le_refl _), (hbase w.next (Nat.le_refl _)).2])
        hqL (by omega) (by omega)
        (by
          simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            hnodenone _ (Nat.le_refl _), (hbase w.next (Nat.le_refl _)).1])
        hLroot.symm (by omega) hrq hrk (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
        (fun x xn cc z hx hxn hz => by have := hlinks x xn cc z hx hxn hz; omega)
      intro key' hkey'
      unfold wGet
      rw [htp, hV4, hres key' hkey']
  -- the bitmap in L, with room
  have hroomc : ∀ (n' : KNode) (s : String), n'.leaf = true →
      (∀ c', (n'.searchEq c.i c').map (·.y) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      WriterWP (do note s; putNode L n'; pure false) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
        wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro n' s hl' hs'
    simp only [note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    refine hleafc n' _ hl' hr3.2.1 hr3.2.2.1 hr3.2.2.2.1 ?_ ?_ hs'
    · intro y hy
      rw [← hr3.1]
      simp only [wNode, lookup_upsert, hy, ↓reduceIte]
    · simp only [wNode, hr3.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
  have hsetAt : ∀ old, n.ks.getLast? = some (.del old) → ∀ c',
      (((n.setAt (n.size - 1) (.del U)).searchEq c.i c').map (·.y)) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro old hlst c'
    rw [← hU]
    have hw' := KNode.setAt_delete_wf n cv old hnwf hlst
    rw [KNode.searchEq_live _ c.i hw' (KNode.setAt_last_times n old _ c.i hlst hnt),
      KNode.setAt_delete_live_lookup n cv c' old hlst, KNode.searchEq_live n c.i hnwf hnt]
  have hadd : ∀ c', (((n.add c.i (.del U)).searchEq c.i c').map (·.y)) =
      if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [← hU]
    have hw' := KNode.add_delete_wf n c.i cv hnwf (by rw [hU]; exact hne)
    rw [KNode.searchEq_live _ c.i hw' (KNode.add_times n c.i _ (fun s h => by cases h) hnt),
      KNode.add_delete_live_lookup n c.i cv c', KNode.searchEq_live n c.i hnwf hnt]
  unfold appendDeleteKlong handleFull
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w3 hlk3]
  split
  · exact writerWP_throw _ _ _ _
  · rw [hU, hlast]
    have hnb : (U == n.lastBitmap) = false := by simpa using hne
    simp only [hnb, Bool.not_false, ↓reduceIte]
    have htime : ∀ (compact : Bool) (s : String), (!compact && decide (last.size > c.p.splitAbove)) = false →
        WriterWP (do note s; handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last compact; pure false)
          c w3 (fun _ w4 => ∀ key', keyWf key' = true →
            wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
      intro compact s hcs
      simp only [note, writerWP_bind, writerWP_modify]
      exact writerWP_mono (htime0' compact hcs s) (fun _ w4 h => by simp only [writerWP_pure]; exact h)
    have hrest : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
        WriterWP (if n.size + 1 < c.p.M then
          if deadOver c.p (n.add c.i (Klong.del U)) = true then do
            note "bitmap.dead"
            handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last true
            pure false
          else do
            note "bitmap.new"
            putNode L (n.add c.i (Klong.del U))
            pure false
        else do
          note "bitmap.full"
          handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [] last
          pure false) c w3 (fun _ w4 => ∀ key', keyWf key' = true →
            wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
      intro _
      by_cases hsz : n.size + 1 < c.p.M
      · simp only [hsz, decide_true, ↓reduceIte]
        by_cases hd : deadOver c.p (n.add c.i (Klong.del U)) = true
        · simp only [hd, ↓reduceIte]; exact htime true _ (by simp)
        · simp only [hd, Bool.false_eq_true, ↓reduceIte]
          exact hroomc _ _ (by rw [KNode.add_leaf]; exact hnl) hadd
      · simp only [hsz, ↓reduceIte]
        apply htime false
        have h1 : c.p.M ≤ n.size + 1 := by omega
        have h2 := hsplit h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2
    cases hg : n.ks.getLast? with
    | none =>
      simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)
    | some k =>
      cases k with
      | del old =>
        cases hlt' : (n.lastTime == some c.i) with
        | false =>
          simp only [hg, hlt', Bool.and_false, Bool.false_eq_true, ↓reduceIte]
          exact hrest (fun ⟨_, h⟩ => by simp [h] at hlt')
        | true =>
          simp only [hg, hlt', Bool.and_self, ↓reduceIte]
          by_cases hd : deadOver c.p (n.setAt (n.size - 1) (Klong.del U)) = true
          · simp only [hd, ↓reduceIte]; exact htime true _ (by simp)
          · simp only [hd, Bool.false_eq_true, ↓reduceIte]
            exact hroomc _ _ (by rw [KNode.setAt_leaf]; exact hnl) (hsetAt old hg)
      | _ =>
        simp only [hg, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact hrest (fun ⟨⟨old, h⟩, _⟩ => by rw [hg] at h; cases h)

/-- A delete of a key whose prefix is there, below an inner segment root and an
inner parent with room, by a bitmap in its segment leaf, which keeps a live
klong, the merges off: with room for the bitmap, or the leaf full by its size
or by its dead klongs, time split (in place for a leaf the transaction made)
when its last version without the key has at most h klongs. The delete changes
the reading by itself alone. -/
theorem writerWP_del_leafBelow (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc')
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z < w.next) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  apply writerWP_del_seg_leaf c base hvc pre cv rk w hrk ht hids.1 hids.2.1 hinner
  intro L n q qn k1 d' w3 hL hn hnl hqv hqn hql hk1 hqL hr3 hlk3 hlq3 hsrc3 hpq hpk _
  obtain ⟨hnt, hne, hkeep, hsplit, hLval, hLroot⟩ := hleaf L n hL hn hnl
  obtain ⟨hqt, hroomq, hdeadq⟩ := hparent q qn hqv hqn hql
  have hLt : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
  have hqtk : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hrq : ReachS (wNode c.p base w) c.i w.top.rootKey q :=
    eqVisits_reach _ _ _ cv c.p.fuel rk q cv hrrk hqv
  have hk1l : (k1, L) ∈ qn.live := by
    rw [← KNode.liveAt_of_times qn c.i hqt]; exact hk1
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_appendDeleteKlong_get c base hvc pre cv k1 d' rk L q n qn w w3
    hfuel hkey hrk hL huniq hwfG hids hbase hn hnl hnt hLt hLval hLroot hqn hql hqt hk1l hqL hqtk
    hrq (fun x xn c' hx hxn hz => htreeK x xn c' L hx hxn hz (by simp [hn]) q qn k1 hrq hqn hk1)
    hlinks hr3 hlk3 hlq3 hsrc3 hpq hpk hne hsplit hroomq (hdeadq k1)) ?_
  intro _ w4 hT4
  unfold afterDelete fresh
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hT4

/-- `writerWP_del_leafBelow` under `PutInv`: the premises of
`putInv_del_leafBelow` give the delete's reading too. -/
theorem writerWP_del_leafBelow_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (hI : PutInv c base w)
    (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧
      (c.p.M ≤ n.size + 1 →
        (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  have hvisR : ∀ x c', (x, c') ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      ReachS (wNode c.p base w) c.i w.top.rootKey x :=
    fun x c' hx => eqVisits_reach _ _ _ cv c.p.fuel rk x c' hrrk hx
  refine writerWP_del_leafBelow c base hvc pre cv rk w hfuel hmerges hkey hrk
    (fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      (pre ++ [cv]) _ q.1 q.2 ReachS.root hq))
    hI.ids hI.fresh hinner (fun x xn hn => hI.wf x xn hn) ?_
    (fun q qn hq hqn hql => by
      obtain ⟨a2, a3⟩ := hparent q qn hq hqn hql
      exact ⟨hI.times q qn hqn, a2, a3⟩)
    (fun key' x _ hkey' h1 h2 _ _ =>
      visits_unique_seg_of_tree _ _ _ _ hI.tree hI.wf pre cv rk hkey hrk key' x hkey' h1 h2)
    (fun x xn cc z hx hn hz _ x' xn' cc' hx' hn' hz' =>
      htree_of_treeOK _ _ _ hI.tree x xn cc z hx hn hz x' xn' cc' hx' hn' hz')
    hI.links
  intro L n hL hn hnl
  obtain ⟨hne, hkeep, hsplit⟩ := hleaf L n hL hn hnl
  refine ⟨hI.times L n hn, hne, hkeep, hsplit, hI.keyNoValue L n hn, ?_⟩
  intro hLr
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  obtain ⟨q, qn, c', hq, hqn, hlink⟩ := eqVisits_parent _ _ cv c.p.fuel rk L hL hLrk
  exact hI.tree.rootFree q c' (reachS_tReach _ _ _ q (hvisR q cv hq)) ⟨qn, hqn, hLr ▸ hlink⟩

end SIS.Tree
