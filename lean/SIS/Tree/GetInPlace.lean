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

/-! ## A space split in place below an inner parent with room -/

theorem KNode.searchLte_congr (n1 n2 : KNode) (t : Time) (h1 : ∀ s, Klong.time s ∈ n1.ks → s ≤ t)
    (h2 : ∀ s, Klong.time s ∈ n2.ks → s ≤ t) (hl : ∀ c', n1.live.lookup c' = n2.live.lookup c')
    (c : Int) : (n1.searchLte t c).map (·.y) = (n2.searchLte t c).map (·.y) := by
  have hmem : ∀ a y, (a, y) ∈ n1.live ↔ (a, y) ∈ n2.live := by
    intro a y
    rw [mem_iff_lookup _ (KNode.live_keys_nodup n1), mem_iff_lookup _ (KNode.live_keys_nodup n2), hl]
  have hs1 := n1.searchLte_spec t c
  unfold NodeSearchSpec at hs1
  rw [KNode.liveAt_of_times n1 t h1] at hs1
  cases hf : n1.searchLte t c with
  | none =>
    have hall := hs1.2.mp hf
    rw [KNode.searchLte_none_of n2 t h2 c (fun q hq => by
      have := hall q ((hmem q.1 q.2).mpr hq)
      simp only [decide_eq_false_iff_not] at this
      omega)]
  | some f =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs1.1 f hf
    simp only [decide_eq_true_eq] at hfa
    rw [KNode.searchLte_of_max n2 t h2 c f.c f.y ((hmem _ _).mp hfm) hfa (fun q hq hqc => by
      have := hfmax q ((hmem q.1 q.2).mpr hq) (by simpa using hqc)
      simpa using this)]
    rfl

/-- The parent after a space split in place of its child L: a klong at sc names
the second half S. A search that found its klong k1 to L finds L below sc and S
from sc on; any other search finds what it found. -/
theorem KNode.splitParentInPlace_searchLte (n : KNode) (t : Time) (k1 sc : Nat) (L S : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hk1 : (k1, L) ∈ n.live) (hle : k1 ≤ sc)
    (hgap : ∀ c' z, (c', z) ∈ n.live → c' ≤ k1 ∨ sc < c') (c : Int) :
    ((n.add t (.key sc S)).searchLte t c).map (·.y) =
      (n.searchLte t c).map (fun fd => if fd.c = k1 then (if c < sc then L else S) else fd.y) := by
  rw [← KNode.splitParent_searchLte n t k1 sc L L S hw ht hk1 hle hgap c]
  have hw1 := KNode.add_key_wf n t k1 L hw
  have ht1 := KNode.add_times n t (.key k1 L) (fun s h => by cases h) ht
  apply KNode.searchLte_congr _ _ t (KNode.add_times n t (.key sc S) (fun s h => by cases h) ht)
    (KNode.add_times _ t (.key sc S) (fun s h => by cases h) ht1)
  intro c'
  rw [KNode.add_key_live_lookup_of_wf n t sc c' S hw, KNode.add_key_live_lookup_of_wf _ t sc c' S hw1,
    KNode.add_key_live_lookup_of_wf n t k1 c' L hw]
  by_cases h1 : sc = c'
  · simp [h1]
  · have h1' : (sc == c') = false := by simpa using h1
    simp only [h1', Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : k1 = c'
    · subst h2
      simp only [beq_self_eq_true, ↓reduceIte]
      exact lookup_some_of_mem (KNode.live_keys_nodup n) hk1
    · have h2' : (k1 == c') = false := by simpa using h2
      simp only [h2', Bool.false_eq_true, ↓reduceIte]

/-- The state after a space split in place of a leaf L below an inner parent q
with room: L holds the first half of its last version with the put's klong,
the next id the second half, and a klong of q at the second half's first
compare value names it. -/
def SpaceSplitInPlaceAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (cv v : Nat) :
    Prop :=
  w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).1
      else if x = q then some (qn.add c.i
        (.key (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.2 w.next))
      else if x = w.next then some (halves n.leaf c.i (n.lastVersion c.i) [(cv, v)]).2.1
      else w.nodes.lookup x

theorem writerWP_handleFullWith_spaceSplitInPlace (d' : Nat) (L q : NodeId) (n qn : KNode)
    (cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M)
    (hdeadq : ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) false) c w
      (fun _ w' => SpaceSplitInPlaceAfter c w w' L q n qn cv v) := by
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
        refine writerWP_mono (writerWP_appendKlongs_room d' q qn _ w.next c _ ?_ hroomq
          (hdeadq _ _)) ?_
        · simp only [lookup_upsert, List.lookup_append, hq2, hqL, ↓reduceIte, hlq]
          rfl
        intro _ w2 hw2
        subst hw2
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
        refine ⟨rfl, rfl, rfl, ?_⟩
        intro x
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · subst hxL
          simp [hqL.symm, hL2]
        · by_cases hxq : x = q
          · subst hxq
            simp [hxL]
          · by_cases hx1 : x = w.next
            · subst hx1
              simp [hxL, hxq]
            · simp only [hxL, hxq, hx1, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hx1]; rfl

theorem writerWP_appendKlongs_spaceSplitInPlace (d' : Nat) (L q : NodeId) (n qn : KNode)
    (cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime = some c.i)
    (hfull : c.p.M ≤ n.size + 1)
    (hsplit : c.p.splitAbove < (n.lastVersion c.i).size)
    (hpq : (w.path[d']?).map (·.2) = some q)
    (hroomq : qn.size + 1 + 1 ≤ c.p.M)
    (hdeadq : ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
    (hLn : L < w.next) (hqn : q < w.next) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => SpaceSplitInPlaceAfter c w w' L q n qn cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have h1 : n.size + [(cv, v)].length + 1 > c.p.M := by simp; omega
  simp only [h1, ↓reduceIte]
  exact writerWP_handleFullWith_spaceSplitInPlace d' L q n qn cv v c w hlk hlq hqL hql hfirst hsplit
    hpq hroomq hdeadq hLn hqn

/-- After a space split in place of the leaf L of a key's last segment (its last version
with the put's klong to the new value v, in halves at the new nodes F and S;
q's klong k1, the one klong that named L, names F, and a klong at the second
half's first compare value names S), every key reads what it read but the key,
which reads the put's value. L's compare values lie between q's klong k1 and
q's next klong. -/
theorem getFromR_spaceSplitInPlace (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q S v : NodeId) (n qn : KNode)
    (k1 : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i) (hlive : n.live ≠ [])
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hrange : ∀ c' z, (c', z) ∈ n.live →
      k1 ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c' < c'')
    (hN2q : N2 q = some (qn.add i (.key (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.2 S)))
    (hN2F : N2 L = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).1)
    (hN2S : N2 S = some (halves n.leaf i (n.lastVersion i) [(cv, v)]).2.1)
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ S → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a)
    (hqL : q ≠ L) (hvL : v ≠ L) (hvS : v ≠ S) (hNv : N v = none)
    (hrootL : root ≠ L) (hrootS : root ≠ S) (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (honlyL : ∀ x xn c, ReachS N i root x → N x = some xn → (c, L) ∈ xn.liveAt i →
      x = q ∧ c = k1)
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ S) :
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
      z ≠ S := by
    intro x xn c z hx hn hz
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact (hfr x n c z hrL hNL h1).2
      · rw [h1]; exact hvS
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact (hfr x xn c z hx' hn hz).2
      · subst hxv; rw [hNv] at hn; cases hn
  have hnotFS' : ∀ x xn c z, ReachS Nm i root x → Nm x = some xn → (c, z) ∈ xn.liveAt i →
      (z ≠ L → z ≠ L) ∧ z ≠ S := fun x xn c z hx hn hz =>
    ⟨fun h => h, hnotFS x xn c z hx hn hz⟩
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
      ((qn.add i (.key r.1 S)).searchLte i c).map (·.y) =
        (qn.searchLte i c).map (fun fd => if fd.y = L then (if c < r.1 then L else S) else fd.y) := by
    intro c
    have hA := KNode.splitParentInPlace_searchLte qn i k1 r.1 L S hqwf hqt hk1 (hrange r.1 r.2 hrmem).1
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
  have hq2l : (qn.add i (.key r.1 S)).leaf = false := by
    rw [KNode.add_leaf]; exact hql
  have hsame : ∀ x, x ≠ L → x ≠ q → x ≠ L → x ≠ S → N2 x = Nm x := by
    intro x h1 h2 _ h4
    rw [hN2 x h1 h2 h4, hNm x h1]
  have hsim := getFromR_split Nm N2 V2 i fuel root L q L S hwfm
    (fun c x hx hxL hxF hxS => getEqR_split Nm N2 i root L q L S qn _ m f s r.1 hNmq hql hN2q hq2l
      hqsearch hNmL hml hN2F hfl hN2S hsl hleafF hleafS hsame hnotL hnotFS' c fuel x hx hxL hxF hxS)
    hsame (by rw [hN2q, hNmq]; rfl) hnotL
    (fun xn c z hxn _ hxl => by rw [hNmq] at hxn; cases hxn; rw [hql] at hxl; cases hxl) hnotFS'
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
  rw [hsim key' root ReachS.root hrootL hrootL hrootS]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-- A put of a key whose last segment's leaf L the transaction made and which is
full by its size, below an inner parent with room for one klong, with more than
h klongs in its last version: the space split in place changes the reading by
the put alone. The premises are those of `writerWP_put_spaceSplit_key`. -/
theorem writerWP_put_spaceSplitInPlace_key (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      (∀ s, Klong.time s ∈ qn.ks → s ≤ c.i) ∧ qn.size + 1 + 1 ≤ c.p.M ∧
      ∀ k y, deadOver c.p (qn.add c.i (.key k y)) = false)
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
  refine writerWP_mono (writerWP_appendKlongs_spaceSplitInPlace d' L q n qn cv w3.next c _
    (by simpa using hlk3) (by simpa using hlq) hqL hql hfirst hfull hsplit
    (by simpa using hpq) hroomq hdeadq hLlt3 hqlt3) ?_
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
  have hLt' : wf.taken.contains L = false := by
    rw [hft]; exact ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hres := getFromR_spaceSplitInPlace (wNode c.p base w) (wNode c.p base wf) (wValue base w)
    (wValue base wf) c.i c.p.fuel hfuel w.top.rootKey L q (w.next + 2) w.next n qn
    k1 pre cv h rk hn hnl (hwf L n hrL hn) htimes hlive hq hql (hwf q qn hrq hq) hqt hk1
    (hrange q qn L n k1 hqv hq hql hn hk1)
    (by
      have hqt' : wf.taken.contains q = false := by
        rw [hft]; exact ht (q, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hqv)
      simp only [wNode, hqt', Bool.false_eq_true, ↓reduceIte, hfn, hqL])
    (by simp only [wNode, hLt', Bool.false_eq_true, ↓reduceIte, hfn])
    (by
      have hyt : wf.taken.contains (w.next + 2) = false := by rw [hft]; exact hntake _ (by omega)
      have h1 : w.next + 2 ≠ L := by omega
      have h2 : w.next + 2 ≠ q := by omega
      simp only [wNode, hyt, Bool.false_eq_true, ↓reduceIte, hfn, h1, h2])
    (by
      intro x hxL hxq hxS
      rw [← hr03.1]
      simp only [wNode, hft, hfn, hxL, hxq, hxS, ↓reduceIte, hr03.2.2.1])
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
  intro key' hkey'
  unfold wGet
  rw [hftop, hres key' hkey']
  simp only [Op.key, Op.value]
  rfl

end SIS.Tree
