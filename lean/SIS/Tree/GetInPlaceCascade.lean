import SIS.Tree.GetDelCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The cascades into a parent the transaction made (bergdb 024-12, TP10): its
time split in place, with the writer's cache kept
(`writerWP_appendKlongs_timeInPlaceC`), and a node replaced by one with the
same live klongs (`getFromR_congr_node`). -/

theorem writerWP_handleFullWith_timeInPlaceC (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up depth L ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        (∀ y, wNode c.p base w' y = if y = L then some l else wNode c.p base w y) ∧
        ∀ y m, w.nodes.lookup y = some m → y ≠ L → w'.nodes.lookup y = some m) := by
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
      (∀ y m, w.nodes.lookup y = some m → w2.nodes.lookup y = some m) →
      WriterWP (do
        let l ← replaceOrAdd (n.lastVersion c.i) ins
        if (l.size == 1) = true then do
            note "lone-time-klong"
            putNode L { leaf := n.leaf, ks := l.ks }
          else putNode L { leaf := n.leaf, ks := l.ks }) c w2 (fun _ w' =>
        ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
          (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
          w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
          (∀ y, wNode c.p base w' y = if y = L then some l else wNode c.p base w y) ∧
          ∀ y m, w.nodes.lookup y = some m → y ≠ L → w'.nodes.lookup y = some m) := by
    intro w2 hr2 _ hpres
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
    subst hw3
    have hm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
      cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hr2.2.2.1, hr2.2.1, hr2.2.2.2.1, hr2.2.2.2.2, ?_, ?_⟩
      · intro y
        by_cases hy : y = L
        · subst hy
          simp only [wNode, hr2.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert, hm]
        · rw [← hr2.1]
          simp only [wNode, lookup_upsert, hy, ↓reduceIte]
      · intro y m hm' hy
        simp only [lookup_upsert, hy, ↓reduceIte]
        exact hpres y m hm'
  simp only [note, writerWP_bind] at hrest
  cases compact with
  | true =>
    simp only [↓reduceIte, note, Bool.not_true, Bool.false_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk (fun _ _ h => h)
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2 (fun y m h => by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, h]; rfl)
  | false =>
    simp only [Bool.not_false, Bool.true_and] at hcs
    simp only [hcs, ↓reduceIte, note, Bool.not_false, Bool.true_and, Bool.false_eq_true]
    cases a with
    | none =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      exact hrest _ ⟨rfl, rfl, rfl, rfl, rfl⟩ hlk (fun _ _ h => h)
    | some q =>
      simp only [writerWP_bind, writerWP_pure, writerWP_modify]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads q c w base hvc)
        (writerWP_getNode_cache2 q c w)) ?_
      rintro qn w2 ⟨⟨hr2, _, _⟩, ⟨hpre2, _⟩⟩
      have hlk2 : w2.nodes.lookup L = some n := by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, hlk]; rfl
      exact hrest _ ⟨hr2.1, hr2.2.1, hr2.2.2.1, hr2.2.2.2.1, hr2.2.2.2.2⟩ hlk2 (fun y m h => by
        obtain ⟨t, ht⟩ := hpre2
        rw [← ht, List.lookup_append, h]; rfl)

/-- `writerWP_handleFullWith_timeInPlaceC` from `appendKlongs` with any klongs to
put into a full node the transaction made. -/
theorem writerWP_appendKlongs_timeInPlaceC (depth : Nat) (L : NodeId) (n : KNode)
    (ins : List (Nat × NodeId)) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hfull : ¬ (n.size + ins.length + 1 ≤ c.p.M ∧
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = false))
    (hsplit : c.p.M < n.size + ins.length + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs depth L ins) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        (∀ y, wNode c.p base w' y = if y = L then some l else wNode c.p base w y) ∧
        ∀ y m, w.nodes.lookup y = some m → y ≠ L → w'.nodes.lookup y = some m) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  split
  · rename_i hsize
    refine writerWP_handleFullWith_timeInPlaceC _ depth L n ins false c base hvc w hlk hLt hfirst ?_
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
    exact hsplit (by simpa using hsize)
  · rename_i hsize
    have hle : n.size + ins.length + 1 ≤ c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) = true := by
      cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) with
      | true => rfl
      | false => exact absurd ⟨hle, h⟩ hfull
    simp only [hd, ↓reduceIte]
    exact writerWP_handleFullWith_timeInPlaceC _ depth L n ins true c base hvc w hlk hLt hfirst
      (by simp)

/-- Two readers that differ only at q, whose nodes there have the same kind and
the same live klongs at t, read alike. -/
theorem getFromR_congr_node (N1 N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (q : NodeId) (a b : KNode)
    (hsame : ∀ x, x ≠ q → N1 x = N2 x) (ha : N1 q = some a) (hb : N2 q = some b)
    (hleaf : a.leaf = b.leaf) (hwa : klongsWf a.ks = true) (hwb : klongsWf b.ks = true)
    (hta : ∀ s, Klong.time s ∈ a.ks → s ≤ t) (htb : ∀ s, Klong.time s ∈ b.ks → s ≤ t)
    (hl : ∀ c, a.live.lookup c = b.live.lookup c) :
    ∀ key r, getFromR N1 V t fuel key r = getFromR N2 V t fuel key r := by
  have hid : ∀ z : NodeId, (if z = q then q else z) = z := fun z => by
    by_cases h : z = q <;> simp [h]
  have hS : RenSim N1 N2 t (fun _ => True) q q := by
    intro x _
    simp only [hid]
    by_cases hx : x = q
    · subst hx
      rw [ha, hb]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      cases h1; cases h2
      refine ⟨hleaf, fun c => ⟨fun _ => ⟨?_, fun _ _ => trivial⟩, fun _ => ⟨?_, fun _ _ => trivial⟩⟩⟩
      · simp only [Option.map_id']
        rw [KNode.searchEq_live _ t hwa hta, KNode.searchEq_live _ t hwb htb, hl]
      · simp only [Option.map_id']
        exact KNode.searchLte_congr _ _ t hta htb hl c
    · rw [hsame x hx]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      rw [h1] at h2; cases h2
      exact ⟨rfl, fun c => ⟨fun _ => ⟨by simp [Function.comp_def], fun _ _ => trivial⟩,
        fun _ => ⟨by simp [Function.comp_def], fun _ _ => trivial⟩⟩⟩
  intro key r
  have := getFromR_ren N1 N2 V V t fuel _ q q hS (fun a => by simp [hid]) key r trivial
  simpa [hid] using this

/-! ## The writer: a leaf's time split whose parent, made by the transaction, is full -/

/-- The state after a time split of the leaf L (its last version with the put at
the next id) whose parent q, made by the transaction and full, is time split in
place (its last version with the klong k1 to L's new node). -/
def TimeSplitQIPAfter (c : Ctx) (base : View BVal) (w w' : W) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) : Prop :=
  ∃ l lq : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
    (∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q') ∧
    lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = if k1 == q' then some w.next else qn.live.lookup q') ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ y, wNode c.p base w' y =
      if y = L then some (n.toPrev (c.i - 1))
      else if y = q then some lq
      else if y = w.next then some ⟨n.leaf, l.ks⟩
      else wNode c.p base w y

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_timeSplitQIP (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (compact : Bool) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt : w.taken.contains q = false)
    (hyt : w.taken.contains w.next = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hqfirst : qn.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hqfull : ¬ (qn.size + 1 + 1 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M < qn.size + 1 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) compact) c w
      (fun _ w' => TimeSplitQIPAfter c base w w' L q n qn k1 cv v) := by
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
    have hup : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))] →
        w1.next = w.next + 2 → w1.path = w.path → w1.taken = w.taken → w1.top = w.top →
        w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w' =>
          WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w'
            (fun _ w'' => TimeSplitQIPAfter c base w w'' L q n qn k1 cv v)) := by
      intro l hl_leaf hl_wf hl_times hl_look w1 h1n h1x h1p h1t h1top h1v
      have hw1N : ∀ y, wNode c.p base w1 y =
          if y = w.next then some ⟨n.leaf, l.ks⟩ else wNode c.p base w y := by
        intro y
        by_cases hy : y = w.next
        · subst hy
          simp only [wNode, h1t, hyt, Bool.false_eq_true, ↓reduceIte, h1n, List.lookup_append, hny]
          simp [List.lookup]
        · simp only [hy, ↓reduceIte, wNode, h1t, h1n, List.lookup_append]
          cases h : w.nodes.lookup y with
          | some m => rfl
          | none =>
            have : ([(w.next, ({ leaf := n.leaf, ks := l.ks } : KNode))].lookup y) = none := by
              rw [lookup_cons_ne _ _ _ _ hy]; rfl
            simp [this]
      refine writerWP_mono (writerWP_appendKlongs_timeInPlaceC d' q qn [(k1, w.next)] c base hvc w1
        (by rw [h1n, List.lookup_append, hlq]; rfl) (by rw [h1t]; exact hqt) hqfirst
        (by simpa using hqfull) (by simpa using hqsplit)) ?_
      intro _ w2 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, _, h2N, h2c⟩
      have hlk2 : w2.nodes.lookup L = some n :=
        h2c L n (by rw [h1n, List.lookup_append, hlk]; rfl) (fun h => hqL h.symm)
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨l, lq, hl_leaf, hl_wf, hl_times, ?_, hq_leaf, hq_wf, hq_times, ?_, by rw [h2t, h1t],
        by rw [h2top, h1top], by rw [h2v, h1v], ?_⟩
      · intro q'; rw [hl_look q']; simp [pairLookupStep]
      · intro q'; rw [hq_look q']; simp [pairLookupStep]
      · intro y
        by_cases hyL : y = L
        · subst hyL
          simp only [wNode, h2t, h1t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
        · have : wNode c.p base { w2 with nodes := upsert w2.nodes L (n.toPrev (c.i - 1)) } y =
              wNode c.p base w2 y := by
            simp only [wNode, lookup_upsert, hyL, ↓reduceIte]
          rw [this, h2N y, hw1N y]
          simp only [hyL, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl rfl rfl

theorem writerWP_appendKlongs_timeSplitQIP (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt : w.taken.contains q = false)
    (hyt : w.taken.contains w.next = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hqfirst : qn.firstTime = some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hqfull : ¬ (qn.size + 1 + 1 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 w.next)) = false))
    (hqsplit : c.p.M < qn.size + 1 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TimeSplitQIPAfter c base w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hts := fun compact hcs => writerWP_handleFullWith_timeSplitQIP d' L q n qn k1 cv v compact c
    base hvc w hlk hlq hLt hqt hyt hqL hql hfirst hqfirst hcs hpq hpk hqfull hqsplit hny
  split
  · rename_i hsize
    apply hts false
    have h1 : c.p.M ≤ n.size + 1 := by simp at hsize; omega
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
    exact hsplit h1
  · rename_i hsize
    have hlt : n.size + 1 < c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (n.add c.i (.key cv v)) = true := by
      cases h : deadOver c.p (n.add c.i (.key cv v)) with
      | true => rfl
      | false => exact absurd ⟨hlt, h⟩ hfull
    simp only [List.foldl_cons, List.foldl_nil, hd, ↓reduceIte]
    exact hts true (by simp)

/-! ## The rule: a leaf's time split whose parent, made by the transaction, is full -/

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full, with at most h klongs in its last version or full by dead klongs
only, below the parent q, an inner node the transaction made, full with the
klong to L's new node, with at most h klongs in its last version or full by dead
klongs only: L's time split and q's time split in place change the reading by
the put alone. -/
theorem writerWP_put_timeSplitQIP (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none ∧ valueOf base (w.next + 2) = none ∧
      knodeOf c.p base (w.next + 2) = none)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime ≠ some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) ∧
      wValue base w L = none ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.firstTime = some c.i ∧
      (∀ k1, ¬ (qn.size + 1 + 1 ≤ c.p.M ∧ deadOver c.p (qn.add c.i (.key k1 (w.next + 2))) = false)) ∧
      (c.p.M < qn.size + 1 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove))
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
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z ≠ w.next ∧ z ≠ w.next + 2) :
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
  obtain ⟨htimes, hfull, hfirst, hsplit, hLval, hLroot⟩ := hleaf L n hvisL hn hnl
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  rcases hdp with ⟨hLrk, _⟩ | ⟨pre', q, k1, qn, fd, hp3, hlast, hq, hql, hqs, hc, hy, hqv⟩
  · subst hLrk
    rw [hinner n hn] at hnl
    cases hnl
  rw [hr0.1] at hq hqv
  obtain ⟨hqt, hqfirst, hqfull, hqsplit⟩ := hparent q qn hqv hq hql
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
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
  have hny : w3.nodes.lookup (w3.next + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2) with
    | none => rfl
    | some _ =>
      have := hsrcw3 _ (by rw [h']; rfl)
      omega
  have hLt0 : w.taken.contains L = false := ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt0 : w.taken.contains q = false := ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hyt0 : w.taken.contains (w.next + 2) = false := by
    cases h' : w.taken.contains (w.next + 2) with
    | false => rfl
    | true => have := hidt _ h'; omega
  refine writerWP_mono (writerWP_appendKlongs_timeSplitQIP d' L q n qn k1 cv w3.next c base hvc _
    (by simpa using hlk3) (by simpa using hlq) (by simp only; rw [hr03.2.2.1]; exact hLt0)
    (by simp only; rw [hr03.2.2.1]; exact hqt0)
    (by simp only; rw [hr03.2.2.1, hnext3]; exact hyt0) hqL hql hfirst hqfirst
    (by rw [hnext3]; exact hfull) hsplit
    (by simpa using hpq) (by simpa using hpk) (by simp only; rw [hnext3]; exact hqfull k1)
    hqsplit (by simpa using hny)) ?_
  intro _ wf hTS
  obtain ⟨l, lq, hl_leaf, hl_wf, hl_times, hl_look, hq_leaf, hq_wf, hq_times, hq_look,
    hft, hftop, hfv, hfN⟩ := hTS
  simp only at hft hftop hfv hfN hq_look
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfN hl_look hq_look
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
  have hm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
    cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some (qn.add c.i (.key k1 (w.next + 2))) else wNode c.p base wf x
  have hqwf := hwf q qn hrq hq
  have hres := getFromR_timeSplit_only (wNode c.p base w) N1 (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q (w.next + 2) w.next n qn
    ⟨n.leaf, l.ks⟩ k1 pre cv h rk hn hnl (hwf L n hrL hn) htimes hq hql hqwf hqt hk1
    hnl hl_wf hl_times (by rw [hm]; exact hl_look)
    (by
      have h1 : w.next + 2 ≠ L := by omega
      have h2 : w.next + 2 ≠ q := by omega
      simp only [N1, h2, ↓reduceIte]
      rw [hfN]
      simp only [h1, h2, ↓reduceIte])
    (by simp [N1])
    (by
      intro x hxL hxq hxy
      simp only [N1, hxq, ↓reduceIte]
      rw [hfN x]
      simp only [hxL, hxq, hxy, ↓reduceIte]
      rw [← hr03.1]
      rfl)
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    (by
      rw [← hLval]
      have hl' : (w.vals ++ [(w.next, h)]).lookup L = w.vals.lookup L :=
        lookup_append_single_ne _ _ _ _ (by omega)
      simp only [wValue, hft, hfv, hl'])
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      simp only [wValue, hyt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_ne _ _ _ _ (by omega : w.next + 2 ≠ w.next),
        hvalnone _ (by omega : w.next ≤ w.next + 2), hbase.2.1])
    hqL (by omega) (by omega) (by omega) (by omega)
    (by
      simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
        hnodenone _ (Nat.le_refl _), hbase.1])
    hLroot.symm (by omega) hrq hrk (keyWf_last_notin pre cv hkey) hvisL huniq hwf
    (fun x xn cc hx hxn hc => htreeK x xn cc L hx hxn hc (by simp [hn]) q qn k1 hrq hq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1))
    (fun x xn cc z hx hxn hz => hfr x xn cc z hx hxn hz)
  have hcg := getFromR_congr_node N1 (wNode c.p base wf) (wValue base wf) c.i c.p.fuel q
    (qn.add c.i (.key k1 (w.next + 2))) lq (fun x hx => by simp [N1, hx]) (by simp [N1])
    (by rw [hfN]; simp [hqL])
    (by rw [KNode.add_leaf, hq_leaf]) (KNode.add_key_wf qn c.i k1 _ hqwf) hq_wf
    (KNode.add_times qn c.i _ (fun s h => by cases h) hqt) hq_times
    (fun c' => by rw [KNode.add_key_live_lookup_of_wf qn c.i k1 c' _ hqwf, hq_look c'])
  intro key' hkey'
  unfold wGet
  rw [hftop, ← hcg key' w.top.rootKey, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

/-! ## The writer: a leaf's space split whose parent, made by the transaction, is full -/

/-- The state after a space split of the leaf L whose parent q, made by the
transaction and full with the two klongs to L's halves, is time split in place. -/
def SpaceSplitQIPAfter (c : Ctx) (base : View BVal) (w w' : W) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) : Prop :=
  ∃ lq : KNode, lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = [(k1, w.next),
      ((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next + 2)].foldl
      (pairLookupStep q') (qn.live.lookup q')) ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ y, wNode c.p base w' y =
      if y = L then some (n.toPrev (c.i - 1))
      else if y = q then some lq
      else if y = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if y = w.next + 2 then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else wNode c.p base w y

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_spaceSplitQIP (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt : w.taken.contains q = false)
    (hyt1 : w.taken.contains w.next = false) (hyt2 : w.taken.contains (w.next + 2) = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hqfirst : qn.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hqfull : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2))) = false))
    (hqsplit : c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitQIPAfter c base w w' L q n qn k1 cv v) := by
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
      simpa using hsplit
    simp only [writerWP_pure, hql, hsz, Bool.not_false, Bool.true_and, ↓reduceIte,
      Bool.false_eq_true]
    simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split
    all_goals (try split)
    all_goals (
      simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk, putNode]
      refine writerWP_mono (writerWP_appendKlongs_timeInPlaceC d' q qn _ c base hvc _
        (by
          simp only [lookup_upsert]
          have h1 : q ≠ w.next + 2 := fun h => by rw [h, hn2] at hlq; cases hlq
          have h2 : q ≠ w.next := fun h => by rw [h, hn1] at hlq; cases hlq
          simp [h1, h2, List.lookup_append, hlq]) (by simpa using hqt) hqfirst
        (by simpa using hqfull) (by simpa using hqsplit)) ?_
      intro _ w2 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, _, h2N, h2c⟩
      have hL1 : L ≠ w.next + 2 := fun h => by rw [h, hn2] at hlk; cases hlk
      have hL2 : L ≠ w.next := fun h => by rw [h, hn1] at hlk; cases hlk
      rw [writerWP_getNode_known L n c w2 (h2c L n (by
        simp only [lookup_upsert]
        simp [hL1, hL2, List.lookup_append, hlk]) (fun h => hqL h.symm))]
      try simp only [putNode, writerWP_modify]
      refine ⟨lq, hq_leaf, hq_wf, hq_times, ?_, h2t, h2top, h2v, ?_⟩
      · intro q'; exact hq_look q'
      · intro x
        have hyt1' : w.next ∉ w.taken := by simpa using hyt1
        have hyt2' : w.next + 2 ∉ w.taken := by simpa using hyt2
        by_cases hxL : x = L
        · subst hxL
          simp only [wNode, h2t, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
        · have : wNode c.p base { w2 with nodes := upsert w2.nodes L (n.toPrev (c.i - 1)) } x =
              wNode c.p base w2 x := by
            simp only [wNode, lookup_upsert, hxL, ↓reduceIte]
          rw [this, h2N x]
          simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · simp [hxq]
          · simp only [hxq, ↓reduceIte]
            by_cases hx2 : x = w.next + 2
            · subst hx2
              simp [wNode, hyt2', lookup_upsert]
            · by_cases hx1 : x = w.next
              · subst hx1
                have : w.next ≠ w.next + 2 := by omega
                simp [wNode, hyt1', lookup_upsert, this]
              · simp only [hx2, hx1, ↓reduceIte, wNode, lookup_upsert, List.lookup_append]
                cases h : w.nodes.lookup x with
                | some m => simp
                | none =>
                  have hb1 : (x == w.next) = false := by simpa using hx1
                  have hb2 : (x == w.next + 2) = false := by simpa using hx2
                  simp [List.lookup, hb1, hb2])

theorem writerWP_appendKlongs_spaceSplitQIP (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt : w.taken.contains q = false)
    (hyt1 : w.taken.contains w.next = false) (hyt2 : w.taken.contains (w.next + 2) = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hqfirst : qn.firstTime = some c.i)
    (hfull : c.p.M < n.size + 1 + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hqfull : ¬ (qn.size + 2 + 1 ≤ c.p.M ∧ deadOver c.p ((qn.add c.i (.key k1 w.next)).add c.i
      (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 (w.next + 2))) = false))
    (hqsplit : c.p.M < qn.size + 2 + 1 → (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hn1 : w.nodes.lookup w.next = none) (hn2 : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSplitQIPAfter c base w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hf : (n.size + [(cv, v)].length + 1 > c.p.M) := by simp; omega
  simp only [hf, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplitQIP d' L q n qn k1 cv v c base hvc w hlk hlq hLt hqt hyt1
    hyt2 hqL hql hfirst hqfirst hsplit hpq hpk hqfull hqsplit hn1 hn2

/-! ## The rule: a leaf's space split whose parent, made by the transaction, is full -/

/-- A put of a key whose last segment's leaf L existed before the transaction
and is full by its size, with more than h klongs in its last version, below the
parent q, an inner node the transaction made, full by its size with the two
klongs to L's halves, with at most h klongs in its last version: L's space split
and q's time split in place change the reading by the put alone. -/
theorem writerWP_put_spaceSplitQIP (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.firstTime = some c.i ∧
      c.p.M < qn.size + 2 + 1 ∧ (qn.lastVersion c.i).size ≤ c.p.splitAbove)
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
  obtain ⟨hqt, hqfirst, hqfull, hqsplit⟩ := hparent q qn hqv hq hql
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
  have hn1 : w3.nodes.lookup (w3.next + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hn2 : w3.nodes.lookup (w3.next + 2 + 2) = none := by
    cases h' : w3.nodes.lookup (w3.next + 2 + 2) with
    | none => rfl
    | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
  have hLt0 : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt0 : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hyt0 : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt _ h'; omega
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitQIP d' L q n qn k1 cv w3.next c base hvc _
    (by simpa using hlk3) (by simpa using hlq) (by simp only; rw [hr03.2.2.1]; exact hLt0)
    (by simp only; rw [hr03.2.2.1]; exact hqt0)
    (by simp only; rw [hr03.2.2.1, hnext3]; exact hyt0 _ (by omega))
    (by simp only; rw [hr03.2.2.1, hnext3]; exact hyt0 _ (by omega))
    hqL hql hfirst hqfirst (by omega) hsplit
    (by simpa using hpq) (by simpa using hpk) (fun ⟨h, _⟩ => by omega) (fun _ => hqsplit)
    (by simpa using hn1) (by simpa using hn2)) ?_
  intro _ wf hSS
  obtain ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, hft, hftop, hfv, hfN⟩ := hSS
  simp only at hft hftop hfv hfN hq_look
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfN hq_look
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
  have hqwf := hwf q qn hrq hq
  let sc := (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2
  let q2 : KNode := (qn.add c.i (.key k1 (w.next + 2))).add c.i (.key sc (w.next + 2 + 2))
  let N1 : NodeId → Option KNode := fun x => if x = q then some q2 else wNode c.p base wf x
  have hres := getFromR_spaceSplit (wNode c.p base w) N1 (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q (w.next + 2) (w.next + 2 + 2) w.next n qn
    k1 pre cv h rk hn hnl (hwf L n hrL hn) htimes hlive hq hql hqwf hqt hk1
    (hrange q qn L n k1 hqv hq hql hn hnl hk1)
    (by simp [N1, q2, sc])
    (by
      have h1 : w.next + 2 ≠ L := by omega
      have h2 : w.next + 2 ≠ q := by omega
      simp only [N1, h2, ↓reduceIte]
      rw [hfN]
      simp only [h1, h2, ↓reduceIte])
    (by
      have h1 : w.next + 2 + 2 ≠ L := by omega
      have h2 : w.next + 2 + 2 ≠ q := by omega
      have h3 : w.next + 2 + 2 ≠ w.next + 2 := by omega
      simp only [N1, h2, ↓reduceIte]
      rw [hfN]
      simp only [h1, h2, h3, ↓reduceIte])
    (by
      intro x hxL hxq hxF hxS
      simp only [N1, hxq, ↓reduceIte]
      rw [hfN x]
      simp only [hxL, hxq, hxF, hxS, ↓reduceIte]
      rw [← hr03.1]
      rfl)
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
  have hq2wf : klongsWf q2.ks = true :=
    KNode.add_key_wf _ c.i sc _ (KNode.add_key_wf qn c.i k1 _ hqwf)
  have hq2t : ∀ s, Klong.time s ∈ q2.ks → s ≤ c.i :=
    KNode.add_times _ c.i (.key sc _) (fun s h => by cases h)
      (KNode.add_times qn c.i (.key k1 _) (fun s h => by cases h) hqt)
  have hcg := getFromR_congr_node N1 (wNode c.p base wf) (wValue base wf) c.i c.p.fuel q q2 lq
    (fun x hx => by simp [N1, hx]) (by simp [N1])
    (by rw [hfN]; simp [hqL])
    (by simp only [q2, KNode.add_leaf]; rw [hq_leaf]) hq2wf hq_wf hq2t hq_times
    (fun c' => by
      rw [hq_look c', KNode.add_key_live_lookup_of_wf _ c.i sc c' _ (KNode.add_key_wf qn c.i k1 _ hqwf),
        KNode.add_key_live_lookup_of_wf qn c.i k1 c' _ hqwf]
      simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]
      by_cases h1 : (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2 = c'
      · simp [h1, sc]
      · by_cases h2 : k1 = c'
        · simp [h1, h2, sc]
        · simp [h1, h2, sc])
  intro key' hkey'
  unfold wGet
  rw [hftop, ← hcg key' w.top.rootKey, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

/-! ## The writer: a leaf's space split in place whose parent, made by the transaction, is full -/

/-- The state after a space split in place of the leaf L, made by the
transaction, whose parent q, made by the transaction too and full with the klong
to L's second half, is time split in place. -/
def SpaceSplitInPlaceQIPAfter (c : Ctx) (base : View BVal) (w w' : W) (L q : NodeId)
    (n qn : KNode) (cv v : Nat) : Prop :=
  ∃ lq : KNode, lq.leaf = qn.leaf ∧ klongsWf lq.ks = true ∧ (∀ s, Klong.time s ∈ lq.ks → s ≤ c.i) ∧
    (∀ q', lq.live.lookup q' = [((halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2, w.next)].foldl
      (pairLookupStep q') (qn.live.lookup q')) ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ y, wNode c.p base w' y =
      if y = q then some lq
      else if y = L then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if y = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else wNode c.p base w y

set_option linter.unusedSimpArgs false in
theorem writerWP_handleFullWith_spaceSplitInPlaceQIP (d' : Nat) (L q : NodeId) (n qn : KNode)
    (cv v : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt : w.taken.contains q = false)
    (hyt : w.taken.contains w.next = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hqfirst : qn.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hqfull : c.p.M < qn.size + 1 + 1)
    (hqsplit : (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitInPlaceQIPAfter c base w w' L q n qn cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
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
    have hq2 : q ≠ w.next := by omega
    have hL2 : L ≠ w.next := by omega
    simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, writerWP_bind, writerWP_modify,
      writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_modify, writerWP_pure]
        refine writerWP_mono (writerWP_appendKlongs_timeInPlaceC d' q qn _ c base hvc _ ?_
          (by simpa using hqt) hqfirst (fun ⟨h, _⟩ => by simp at h; omega) (fun _ => hqsplit)) ?_
        · simp only [lookup_upsert, List.lookup_append, hq2, hqL, ↓reduceIte, hlq]
          rfl
        intro _ w2 ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, h2t, h2top, h2v, _, h2N, h2c⟩
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
        have hyt' : w.next ∉ w.taken := by simpa using hyt
        refine ⟨lq, hq_leaf, hq_wf, hq_times, fun q' => hq_look q', h2t, h2top, h2v, ?_⟩
        intro x
        rw [h2N x]
        by_cases hxq : x = q
        · simp [hxq, hqL]
        · simp only [hxq, ↓reduceIte]
          by_cases hxL : x = L
          · subst hxL
            have hLt' : x ∉ w.taken := by simpa using hLt
            simp [wNode, hLt', lookup_upsert, hL2, List.lookup_append, hqL.symm]
          · by_cases hx1 : x = w.next
            · subst hx1
              simp [wNode, hyt', lookup_upsert, hxL, List.lookup_append]
            · simp only [hxL, hx1, ↓reduceIte, wNode, lookup_upsert, List.lookup_append]
              cases h : w.nodes.lookup x with
              | some m => simp
              | none =>
                have hb1 : (x == w.next) = false := by simpa using hx1
                simp [List.lookup, hb1]

theorem writerWP_appendKlongs_spaceSplitInPlaceQIP (d' : Nat) (L q : NodeId) (n qn : KNode)
    (cv v : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hLt : w.taken.contains L = false) (hqt : w.taken.contains q = false)
    (hyt : w.taken.contains w.next = false)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hqfirst : qn.firstTime = some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hqfull : c.p.M < qn.size + 1 + 1)
    (hqsplit : (qn.lastVersion c.i).size ≤ c.p.splitAbove)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSplitInPlaceQIPAfter c base w w' L q n qn cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplitInPlaceQIP d' L q n qn cv v c base hvc w hlk hlq hLt hqt
    hyt hqL hql hfirst hqfirst hsplit hpq hqfull hqsplit hLn hqn

/-! ## The rule: a leaf's space split in place whose parent, made by the transaction, is full -/

/-- A put of a key whose last segment's leaf L, made by the transaction, is full
by its size with more than h klongs in its last version, below the parent q,
made by the transaction too, full by its size with the klong to L's second half,
with at most h klongs in its last version: L's space split in place and q's
time split in place change the reading by the put alone. -/
theorem writerWP_put_spaceSplitInPlaceQIP (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      n.firstTime = some c.i ∧ c.p.splitAbove < (n.lastVersion c.i).size ∧
      n.live ≠ [] ∧ L ≠ w.top.rootKey)
    (hparent : ∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w q = some qn → qn.leaf = false →
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.firstTime = some c.i ∧
      c.p.M < qn.size + 1 + 1 ∧ (qn.lastVersion c.i).size ≤ c.p.splitAbove)
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
    (hfr : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → z ≠ w.next ∧ z ≠ w.next + 2) :
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
  obtain ⟨hqt, hqfirst, hqfull, hqsplit⟩ := hparent q qn hqv hq hql
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
  have hLt0 : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqt0 : w.taken.contains q = false :=
    ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
  have hyt0 : w.taken.contains (w.next + 2) = false := by
    cases h' : w.taken.contains (w.next + 2) with
    | false => rfl
    | true => have := hidt _ h'; omega
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitInPlaceQIP d' L q n qn cv w3.next c base hvc _
    (by simpa using hlk3) (by simpa using hlq) (by simp only; rw [hr03.2.2.1]; exact hLt0)
    (by simp only; rw [hr03.2.2.1]; exact hqt0) (by simp only; rw [hr03.2.2.1, hnext3]; exact hyt0)
    hqL hql hfirst hqfirst hfull hsplit
    (by simpa using hpq) hqfull hqsplit hLlt3 hqlt3) ?_
  intro _ wf hSS
  obtain ⟨lq, hq_leaf, hq_wf, hq_times, hq_look, hft, hftop, hfv, hfN⟩ := hSS
  simp only at hft hftop hfv hfN hq_look
  rw [hr03.2.2.1] at hft
  rw [hr03.2.1] at hftop
  rw [hr03.2.2.2.1, hnext3] at hfv
  rw [hnext3] at hfN hq_look
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
  have hLt' : wf.taken.contains L = false := by
    rw [hft]; exact ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hqwf := hwf q qn hrq hq
  let sc := (halves n.leaf c.i (n.lastVersion c.i) [(cv, w.next)]).2.2
  let N1 : NodeId → Option KNode := fun x =>
    if x = q then some (qn.add c.i (.key sc (w.next + 2))) else wNode c.p base wf x
  have hres := getFromR_spaceSplitInPlace (wNode c.p base w) N1 (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q (w.next + 2) w.next n qn
    k1 pre cv h rk hn hnl (hwf L n hrL hn) htimes hlive hq hql hqwf hqt hk1
    (hrange q qn L n k1 hqv hq hql hn hnl hk1)
    (by simp [N1, sc])
    (by
      simp only [N1, show L ≠ q from fun h => hqL h.symm, ↓reduceIte]
      rw [hfN]
      simp [show L ≠ q from fun h => hqL h.symm])
    (by
      have h1 : w.next + 2 ≠ L := by omega
      have h2 : w.next + 2 ≠ q := by omega
      simp only [N1, h2, ↓reduceIte]
      rw [hfN]
      simp only [h1, h2, ↓reduceIte])
    (by
      intro x hxL hxq hxS
      simp only [N1, hxq, ↓reduceIte]
      rw [hfN x]
      simp only [hxL, hxq, hxS, ↓reduceIte]
      rw [← hr03.1]
      rfl)
    (by
      have hvt : wf.taken.contains w.next = false := by rw [hft]; exact hntake _ (Nat.le_refl _)
      simp only [wValue, hvt, Bool.false_eq_true, ↓reduceIte, hfv,
        lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))])
    (by
      intro a ha
      simp only [wValue, hft, hfv, lookup_append_single_ne _ _ _ _ ha])
    hqL (by omega) (by omega)
    (by
      simp only [wNode, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
        hnodenone _ (Nat.le_refl _), hbase])
    hLroot.symm (by omega) hrq hrk (keyWf_last_notin pre cv hkey) hvisL huniq hwf
    (fun x xn cc hx hxn hc => htreeK x xn cc L hx hxn hc (by simp [hn]) q qn k1 hrq hq
      (by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk1))
    (fun x xn cc z hx hxn hz => hfr x xn cc z hx hxn hz)
  have hcg := getFromR_congr_node N1 (wNode c.p base wf) (wValue base wf) c.i c.p.fuel q
    (qn.add c.i (.key sc (w.next + 2))) lq (fun x hx => by simp [N1, hx]) (by simp [N1])
    (by rw [hfN]; simp)
    (by rw [KNode.add_leaf, hq_leaf]) (KNode.add_key_wf qn c.i sc _ hqwf) hq_wf
    (KNode.add_times qn c.i _ (fun s h => by cases h) hqt) hq_times
    (fun c' => by
      rw [KNode.add_key_live_lookup_of_wf qn c.i sc c' _ hqwf, hq_look c']
      simp [pairLookupStep, sc])
  intro key' hkey'
  unfold wGet
  rw [hftop, ← hcg key' w.top.rootKey, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

end SIS.Tree
