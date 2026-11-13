import SIS.Tree.GetSpaceSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into a full leaf that the transaction made (bergdb 024-12, TP10;
`OpGetOK`'s rules): with at most h klongs in its last version, or full by its
dead klongs only, a time split in place: the leaf becomes its last version with
the put's klong, and the parent is not changed. -/

theorem writerWP_handleFullWith_timeInPlace (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (L : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up depth L ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        ∀ y, wNode c.p base w' y = if y = L then some l else wNode c.p base w y) := by
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
        let l ← replaceOrAdd (n.lastVersion c.i) ins
        if (l.size == 1) = true then do
            note "lone-time-klong"
            putNode L { leaf := n.leaf, ks := l.ks }
          else putNode L { leaf := n.leaf, ks := l.ks }) c w2 (fun _ w' =>
        ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
          (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
          w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
          ∀ y, wNode c.p base w' y = if y = L then some l else wNode c.p base w y) := by
    intro w2 hr2 _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_replaceOrAdd_last n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look⟩
    subst hw3
    have hm : ({ leaf := n.leaf, ks := l.ks } : KNode) = l := by
      cases l; simp only at hl_leaf ⊢; rw [hl_leaf]
    split <;>
    · simp only [note, putNode, writerWP_bind, writerWP_modify]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hr2.2.2.1, hr2.2.1, hr2.2.2.2.1, hr2.2.2.2.2, ?_⟩
      intro y
      by_cases hy : y = L
      · subst hy
        simp only [wNode, hr2.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert, hm]
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

theorem writerWP_appendKlongs_timeInPlace (depth : Nat) (L : NodeId) (n : KNode) (cv v : Nat)
    (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hlk : w.nodes.lookup L = some n) (hLt : w.taken.contains L = false)
    (hfirst : n.firstTime = some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove) :
    WriterWP (appendKlongs depth L [(cv, v)]) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        ∀ y, wNode c.p base w' y = if y = L then some l else wNode c.p base w y) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  split
  · rename_i hsize
    exact writerWP_handleFullWith_timeInPlace _ depth L n [(cv, v)] false c base hvc w hlk hLt hfirst
      (by
        have h1 : c.p.M ≤ n.size + 1 := by simp at hsize; omega
        have h2 := hsplit h1
        simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]
        exact h2)
  · rename_i hsize
    have hlt : n.size + 1 < c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (n.add c.i (.key cv v)) = true := by
      cases h : deadOver c.p (n.add c.i (.key cv v)) with
      | true => rfl
      | false => exact absurd ⟨hlt, h⟩ hfull
    simp only [List.foldl_cons, List.foldl_nil, hd, ↓reduceIte]
    exact writerWP_handleFullWith_timeInPlace _ depth L n [(cv, v)] true c base hvc w hlk hLt hfirst
      (by simp)

/-- A put of a key whose last segment's leaf L the transaction made and which
is full, with at most h klongs in its last version or full by its dead klongs
only: the time split in place changes the reading by the put alone. The
premises are those of `writerWP_put_room_seg` but the room. -/
theorem writerWP_put_timeInPlace_seg (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) ∧
      n.firstTime = some c.i ∧ (c.p.M ≤ n.size + 1 → (n.lastVersion c.i).size ≤ c.p.splitAbove))
    (hnext : w.taken.contains w.next = false ∧ w.vals.lookup w.next = none)
    (huniq : ∀ key' x n, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n → n.leaf = true → key' = pre ++ [cv])
    (hfresh : ∀ key' x c' n y,
      (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n → n.leaf = true → (n.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, hget⟩
  rw [hr0.1] at hn hvisL hget
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hwf, htimes, hfull, hfirst, hsplit⟩ := hleaf L n hvisL hn hnl
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    cases hd : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hfull ⟨hlt, hd⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  refine writerWP_mono (writerWP_appendKlongs_timeInPlace _ L n cv w3.next c base hvc _
    (by simpa using hlk3) (by rw [hr03.2.2.1]; simpa using hLt) hfirst
    (by rw [hnext3]; exact hfull) hsplit) ?_
  rintro _ w6 ⟨l, hl_leaf, hl_wf, hl_times, hl_look, h6taken, h6top, h6vals, _, h6N⟩
  simp only at h6taken h6top h6vals
  rw [hr03.2.2.1] at h6taken
  rw [hr03.2.1] at h6top
  rw [hr03.2.2.2.1, hnext3] at h6vals
  have h6N' : ∀ y, wNode c.p base w6 y = if y = L then some l else wNode c.p base w y := by
    intro y
    rw [h6N y, ← hr03.1]
    rfl
  have hNL : wNode c.p base w6 L = some l := by rw [h6N' L]; simp
  have hN : ∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x := by
    intro x hx
    rw [h6N' x]
    simp [hx]
  have hV : ∀ y, y ≠ w.next → wValue base w y = wValue base w6 y := by
    intro y hy
    simp only [wValue, h6taken, h6vals, lookup_append_single_ne _ _ _ _ hy]
  have hVv : wValue base w6 w.next = some h := by
    simp only [wValue, h6taken, hnext.1, Bool.false_eq_true, ↓reduceIte, h6vals,
      lookup_append_single_self _ _ _ hnext.2]
  have hsearch : ∀ c', (l.searchEq c.i c').map (·.y) =
      if cv == c' then some w.next else (n.searchEq c.i c').map (·.y) := by
    intro c'
    rw [KNode.searchEq_live l c.i hl_wf hl_times, hl_look c', KNode.searchEq_live n c.i hwf htimes,
      hnext3]
    simp only [List.foldl_cons, List.foldl_nil, pairLookupStep]
  have hleaf' : l.leaf = true := hl_leaf.trans hnl
  obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w6 L pre cv rk n l hfuel h6top hN
    hn hNL hnl hleaf' (fun c' hc' => by
      have hb : (cv == c') = false := by
        cases hcb : (cv == c') with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hcb).symm hc'
      rw [hsearch c', hb]
      rfl)
    hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun key' x c' m y _ hx hm hml hs => hV y (hfresh key' x c' m y hx hm hml hs))
  intro key' hkey'
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    rw [hown, hsearch cv]
    simp [hVv]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    exact hother key' hkey' (fun h' => hk h'.symm)

end SIS.Tree
