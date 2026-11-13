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

end SIS.Tree
