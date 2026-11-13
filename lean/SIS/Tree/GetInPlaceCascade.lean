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

end SIS.Tree
