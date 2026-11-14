import SIS.Tree.HistoricalScan

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The scan's reading of a sound tree (bergdb 024-12, TP11): what a key node
holds at time t, its order, and the facts of the walk the scan relies on. -/

/-- A key node and its subtree as the scan reads them at time t: a key node
with well-formed klongs and encoded compare values; a short segment of a leaf
names a value with a hash; every other live klong names a key node with a live
klong, itself sound, whose keys, for an inner node, start at or above the
klong's compare value and below every later one. -/
def SNode (p : Params) (v : View BVal) (t : Time) : Nat → NodeId → Prop
  | 0, _ => False
  | f+1, x => ∃ n, knodeOf p v x = some n ∧ klongsWf n.ks = true ∧
      (∀ q ∈ n.liveAt t, q.1 < 2^62) ∧
      ∀ q ∈ n.liveAt t,
        ((n.leaf && segLen q.1 != 7) = true →
          ∃ nd h, v q.2 = some nd ∧ nd.isData = true ∧ valueOf v q.2 = some h) ∧
        ((n.leaf && segLen q.1 != 7) = false →
          ∃ nd, v q.2 = some nd ∧ nd.isData = false ∧ SNode p v t f q.2 ∧
            (∃ cn, knodeOf p v q.2 = some cn ∧ cn.liveAt t ≠ []) ∧
            (n.leaf = false → ∀ k ∈ treeContents p v t f q.2, ∃ c r, k.1 = c :: r ∧ q.1 ≤ c ∧
              ∀ r' ∈ n.liveAt t, q.1 < r'.1 → c < r'.1))

theorem walk_clean_node (p : Params) (v : View BVal) (t f x lo : Nat) (hi : Option Nat)
    (isRoot space : Bool) (hw : walk p v t f x lo hi isRoot space = []) :
    ∃ f' nd, f = f' + 1 ∧ v x = some nd ∧ nd.isData = false := by
  cases f with
  | zero => simp [walk] at hw
  | succ f' =>
    cases hv : v x with
    | none => simp [walk, hv] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp [walk, hv, hd] at hw
      | false => exact ⟨f', nd, rfl, rfl, hd⟩

/-- A fault-free walk gives the scan's reading of the tree. -/
theorem sNode_of_walk (p : Params) (P : Struct BVal) (t f : Nat)
    (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P) (henc : ViewEncoded (viewOf P))
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) :
    SNode p (viewOf P) t f x := by
  induction f generalizing x lo hi isRoot space with
  | zero => simp only [walk, List.cons_ne_nil] at hw
  | succ f ih =>
    obtain ⟨_, nd, _, hv, hd⟩ := walk_clean_node p _ t _ x lo hi isRoot space hw
    have hv' : P.get? x = some nd := hv
    have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hkinds hv' hd hw
    let n : KNode := ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩
    have hn : knodeOf p (viewOf P) x = some n := by
      simp [knodeOf, hv, hd, Nat.not_lt_of_ge hl, n]
    refine ⟨n, hn, walk_current_wf p _ t f x lo hi isRoot space nd hv hd hw, ?_, ?_⟩
    · intro q hq
      have he := ((knodeOf_encoded p _ x n henc hn).liveAt n t) q hq
      exact he.1
    · intro q hq
      obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi q hq
      have hedge := walk_edge_info p P t f x lo hi isRoot space nd hdata hv' hd hw q b hb
      refine ⟨fun hs => ?_, fun hs => ?_⟩
      · obtain ⟨h, hh⟩ := hedge.1 hs
        obtain ⟨nd', hnd', hdd⟩ := valueOf_view _ _ _ hh
        exact ⟨nd', h, hnd', hdd, hh⟩
      · have hcw := hedge.2 hs
        obtain ⟨f', ny, hf', hy, hny⟩ := walk_clean_node p _ t f q.2 _ _ _ _ hcw
        have hsc := ih q.2 _ _ _ _ hcw
        refine ⟨ny, hy, hny, hsc, ?_, ?_⟩
        · subst hf'
          have hy' : P.get? q.2 = some ny := hy
          have hl' := highKindsOK_walk_level p P t f' q.2 _ _ _ _ ny hkinds hy' hny hcw
          refine ⟨⟨p.heightOf ny.level == 0, klongsOf ny.hist⟩, ?_, ?_⟩
          · simp [knodeOf, hy, hny, Nat.not_lt_of_ge hl']
          · apply walk_current_nonempty p _ t f' q.2 _ _ _ _ ny hy hny hcw
            cases (p.heightOf nd.level == 0) <;> simp
        · intro hleaf k hk
          have hleaf' : (p.heightOf nd.level == 0) = false := hleaf
          simp only [hleaf', Bool.false_eq_true, ↓reduceIte] at hcw
          have hks := keyTreeSound_of_walk p P t f hkinds q.2 _ _ _ _ hcw
          have hshape := treeContents_keyShape p _ t f q.2 k hk
          obtain ⟨key, val⟩ := k
          cases key with
          | nil => simp [keyShape] at hshape
          | cons c r =>
            obtain ⟨hlo, hhi⟩ := treeContents_first_range p _ t f q.2 _ _ hks c r val hk
            refine ⟨c, r, rfl, ?_, ?_⟩
            · by_cases h0 : q.1 = 0
              · omega
              · simpa [h0] using hlo
            · intro r' hr' hlt
              obtain ⟨upper, hu, hle⟩ := childBounds_next_le (n.liveAt t) hi
                (KNode.liveAt_order n t) q b hb r' hr' hlt
              rw [hu] at hhi
              dsimp only [UpperBound] at hhi
              omega

/-- Once a sound subtree fits the fuel, more fuel changes none of its contents. -/
theorem treeContents_stable (p : Params) (v : View BVal) (t f x : Nat)
    (hs : SNode p v t f x) (g : Nat) (hg : f ≤ g) :
    treeContents p v t g x = treeContents p v t f x := by
  induction f generalizing x g with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n, hn, _, _, hc⟩ := hs
    cases g with
    | zero => omega
    | succ g =>
      simp only [treeContents, hn]
      apply flatMap_congr_mem
      intro q hq
      obtain ⟨_, hnot⟩ := hc q hq
      cases hleaf : n.leaf with
      | false =>
        obtain ⟨_, _, _, hcs, _⟩ := hnot (by simp [hleaf])
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih q.2 hcs g (by omega)
      | true =>
        simp only [↓reduceIte]
        by_cases hlen : segLen q.1 = 7
        · obtain ⟨_, _, _, hcs, _⟩ := hnot (by simp [hleaf, hlen])
          simp only [hlen, beq_self_eq_true, ↓reduceIte]
          rw [ih q.2 hcs g (by omega)]
        · simp [hlen]

theorem keyLt_cons_same (c : Nat) (a b : Key) : keyLt (c :: a) (c :: b) = keyLt a b := by
  simp [keyLt]

theorem keyLt_cons_lt (c d : Nat) (a b : Key) (h : c < d) : keyLt (c :: a) (d :: b) = true := by
  simp [keyLt, h]

/-- The keys of a sound subtree are strictly increasing. -/
theorem treeContents_sorted (p : Params) (v : View BVal) (t f x : Nat)
    (hs : SNode p v t f x) :
    (treeContents p v t f x).Pairwise (fun a b => keyLt a.1 b.1 = true) := by
  induction f generalizing x with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n, hn, _, _, hc⟩ := hs
    simp only [treeContents, hn]
    rw [List.pairwise_flatMap]
    constructor
    · intro q hq
      obtain ⟨_, hnot⟩ := hc q hq
      cases hleaf : n.leaf with
      | false =>
        obtain ⟨_, _, _, hcs, _⟩ := hnot (by simp [hleaf])
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih q.2 hcs
      | true =>
        simp only [↓reduceIte]
        by_cases hlen : segLen q.1 = 7
        · obtain ⟨_, _, _, hcs, _⟩ := hnot (by simp [hleaf, hlen])
          simp only [hlen, beq_self_eq_true, ↓reduceIte]
          rw [List.pairwise_map]
          exact (ih q.2 hcs).imp (fun h => by simpa [keyLt_cons_same] using h)
        · simp only [show (segLen q.1 == 7) = false by simp [hlen], Bool.false_eq_true,
            ↓reduceIte]
          split <;> simp
    · apply (KNode.liveAt_order n t).imp_of_mem
      intro a b ha hb hab
      cases hleaf : n.leaf with
      | true =>
        intro ka hka kb hkb
        have hh : ∀ q ∈ n.liveAt t, ∀ k ∈ (if segLen q.1 == 7 then
            (treeContents p v t f q.2).map (fun kv => (q.1 :: kv.1, kv.2))
            else match valueOf v q.2 with
              | none => []
              | some h => [([q.1], h)]), ∃ r, k.1 = q.1 :: r := by
          intro q _ k hk
          split at hk
          · obtain ⟨kv, _, he⟩ := List.mem_map.mp hk
            exact ⟨kv.1, by rw [← he]⟩
          · split at hk
            · simp at hk
            · simp only [List.mem_singleton] at hk
              exact ⟨[], by rw [hk]⟩
        obtain ⟨ra, hra⟩ := hh a ha ka hka
        obtain ⟨rb, hrb⟩ := hh b hb kb hkb
        rw [hra, hrb]
        exact keyLt_cons_lt _ _ _ _ hab
      | false =>
        intro ka hka kb hkb
        obtain ⟨_, hnota⟩ := hc a ha
        obtain ⟨_, hnotb⟩ := hc b hb
        obtain ⟨_, _, _, _, _, hra⟩ := hnota (by simp [hleaf])
        obtain ⟨_, _, _, _, _, hrb⟩ := hnotb (by simp [hleaf])
        obtain ⟨ca, ra, hka', _, hlta⟩ := hra hleaf ka hka
        obtain ⟨cb, rb, hkb', hleb, _⟩ := hrb hleaf kb hkb
        have h1 := hlta b hb hab
        rw [hka', hkb']
        exact keyLt_cons_lt _ _ _ _ (by omega)

/-- A sound key node with a live klong has keys. -/
theorem treeContents_ne_nil (p : Params) (v : View BVal) (t f x : Nat)
    (hs : SNode p v t f x) (n : KNode) (hn : knodeOf p v x = some n)
    (hne : n.liveAt t ≠ []) : treeContents p v t f x ≠ [] := by
  induction f generalizing x n with
  | zero => exact hs.elim
  | succ f ih =>
    obtain ⟨n', hn', _, _, hc⟩ := hs
    rw [hn] at hn'
    cases Option.some.inj hn'
    obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
    simp only [treeContents, hn]
    intro he
    have hq0 := (List.flatMap_eq_nil_iff.mp he) q hq
    obtain ⟨hshort, hnot⟩ := hc q hq
    cases hl : (n.leaf && segLen q.1 != 7) with
    | true =>
      obtain ⟨_, h, _, _, hv⟩ := hshort hl
      have hleaf : n.leaf = true := by simp_all
      have hlen : segLen q.1 ≠ 7 := by simp_all
      simp [hleaf, hlen, hv] at hq0
    | false =>
      obtain ⟨_, _, _, hcs, ⟨cn, hcn, hcne⟩, _⟩ := hnot hl
      have hcc := ih q.2 hcs cn hcn hcne
      cases hleaf : n.leaf with
      | false => simp [hleaf] at hq0; exact hcc hq0
      | true =>
        have hlen : segLen q.1 = 7 := by simpa [hleaf] using hl
        simp [hleaf, hlen] at hq0
        exact hcc hq0

/-! ## The scan's remainder -/

/-- A list in the scan's direction. -/
def orient {α : Type} (fw : Bool) (l : List α) : List α := if fw then l else l.reverse

/-- The pairs that klong q of node n gives, relative to n's segment, in the
scan's direction: a value's key is its compare value; a long segment prefixes
the keys of its tree; an inner klong passes its child's keys on. -/
def klongC (p : Params) (v : View BVal) (t : Time) (F : Nat) (fw : Bool) (n : KNode)
    (q : Nat × NodeId) : List (Key × Nat) :=
  if n.leaf then
    if segLen q.1 == 7 then
      (orient fw (treeContents p v t F q.2)).map (fun kv => (q.1 :: kv.1, kv.2))
    else match valueOf v q.2 with
      | none => []
      | some h => [([q.1], h)]
  else orient fw (treeContents p v t F q.2)

theorem treeContents_orient (p : Params) (v : View BVal) (t F x : Nat) (n : KNode)
    (hn : knodeOf p v x = some n) (fw : Bool) :
    orient fw (treeContents p v t (F+1) x) =
      (orient fw (n.liveAt t)).flatMap (klongC p v t F fw n) := by
  cases fw with
  | true =>
    simp only [orient, treeContents, hn, ↓reduceIte]
    apply flatMap_congr_mem
    intro q _
    cases hl : n.leaf with
    | false => simp [klongC, orient, hl]
    | true =>
      by_cases hlen : segLen q.1 = 7
      · simp [klongC, orient, hl, hlen]
      · cases hv : valueOf v q.2 <;> simp [klongC, hl, hlen, hv]
  | false =>
    simp only [orient, treeContents, hn, Bool.false_eq_true, ↓reduceIte,
      List.reverse_flatMap]
    apply flatMap_congr_mem
    intro q _
    simp only [Function.comp, klongC, orient, Bool.false_eq_true, ↓reduceIte]
    cases n.leaf with
    | false => simp
    | true =>
      by_cases hlen : segLen q.1 = 7
      · simp [hlen, List.map_reverse]
      · cases valueOf v q.2 <;> simp [hlen]

/-- The live klongs of n that a scan has still to visit from cursor lc: after
it forward, before it backward, it included when `inc`; in the scan's order. -/
def afterL (n : KNode) (t : Time) (fw inc : Bool) (lc : Int) : List (Nat × NodeId) :=
  if fw then
    (n.liveAt t).filter (fun q => if inc then decide (lc ≤ (q.1 : Int)) else decide (lc < (q.1 : Int)))
  else
    ((n.liveAt t).filter (fun q => if inc then decide ((q.1 : Int) ≤ lc)
      else decide ((q.1 : Int) < lc))).reverse

/-- The segments of a chain after its top link is popped (`scanPop`). -/
def popSegs (p : Params) (v : View BVal) (segs : List Nat) (rest : List (NodeId × Int)) :
    List Nat :=
  match rest with
  | (q, _) :: _ => if ((knodeOf p v q).map (·.leaf)) == some true then segs.dropLast else segs
  | [] => segs

/-- What a scan's chain has still to give, in its order: for each link, the
klongs of its node after its cursor, their keys with the segments passed, the
top link's cursor included when `inc` (the first step of an inclusive scan at
its start key). -/
def chainRem (p : Params) (v : View BVal) (t : Time) (F : Nat) (fw : Bool) :
    List (NodeId × Int) → List Nat → Bool → List (Key × Nat)
  | [], _, _ => []
  | (x, lc) :: rest, segs, inc =>
    (match knodeOf p v x with
     | none => []
     | some n => ((afterL n t fw inc lc).flatMap (klongC p v t F fw n)).map
        (fun kv => (segs ++ kv.1, kv.2)))
    ++ chainRem p v t F fw rest (popSegs p v segs rest) false

/-! ## The searches as the head of the remainder -/

theorem filter_eq_cons_of_min (L : List (Nat × NodeId))
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (P Q : Nat × NodeId → Bool)
    (fd : Nat × NodeId) (hfd : fd ∈ L) (hP : P fd = true)
    (hmin : ∀ q ∈ L, P q = true → fd.1 ≤ q.1)
    (hup : ∀ q ∈ L, fd.1 < q.1 → P q = true)
    (hQ : ∀ q ∈ L, Q q = true ↔ fd.1 < q.1) :
    L.filter P = fd :: L.filter Q := by
  induction L with
  | nil => simp at hfd
  | cons a L ih =>
    have hsa := (List.pairwise_cons.mp hs).1
    have hsL := (List.pairwise_cons.mp hs).2
    rcases List.mem_cons.mp hfd with rfl | hfd'
    · have hQa : Q fd = false := by
        cases h : Q fd with
        | false => rfl
        | true => have := (hQ fd (by simp)).mp h; omega
      have e1 : L.filter P = L := List.filter_eq_self.mpr
        (fun q hq => hup q (by simp [hq]) (hsa q hq))
      have e2 : L.filter Q = L := List.filter_eq_self.mpr
        (fun q hq => (hQ q (by simp [hq])).mpr (hsa q hq))
      simp [hP, hQa, e1, e2]
    · have hlt := hsa fd hfd'
      have hPa : P a = false := by
        cases h : P a with
        | false => rfl
        | true => have := hmin a (by simp) h; omega
      have hQa : Q a = false := by
        cases h : Q a with
        | false => rfl
        | true => have := (hQ a (by simp)).mp h; omega
      simp only [List.filter_cons, hPa, hQa, Bool.false_eq_true, ↓reduceIte]
      exact ih hsL hfd' (fun q hq => hmin q (by simp [hq]))
        (fun q hq => hup q (by simp [hq])) (fun q hq => hQ q (by simp [hq]))

theorem filter_eq_snoc_of_max (L : List (Nat × NodeId))
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (P Q : Nat × NodeId → Bool)
    (fd : Nat × NodeId) (hfd : fd ∈ L) (hP : P fd = true)
    (hmax : ∀ q ∈ L, P q = true → q.1 ≤ fd.1)
    (hdown : ∀ q ∈ L, q.1 < fd.1 → P q = true)
    (hQ : ∀ q ∈ L, Q q = true ↔ q.1 < fd.1) :
    L.filter P = L.filter Q ++ [fd] := by
  induction L with
  | nil => simp at hfd
  | cons a L ih =>
    have hsa := (List.pairwise_cons.mp hs).1
    have hsL := (List.pairwise_cons.mp hs).2
    rcases List.mem_cons.mp hfd with rfl | hfd'
    · have hQa : Q fd = false := by
        cases h : Q fd with
        | false => rfl
        | true => have := (hQ fd (by simp)).mp h; omega
      have e1 : L.filter P = [] := List.filter_eq_nil_iff.mpr (fun q hq h => by
        have := hmax q (by simp [hq]) h; have := hsa q hq; omega)
      have e2 : L.filter Q = [] := List.filter_eq_nil_iff.mpr (fun q hq h => by
        have := (hQ q (by simp [hq])).mp h; have := hsa q hq; omega)
      simp [hP, hQa, e1, e2]
    · have hlt := hsa fd hfd'
      have hPa : P a = true := hdown a (by simp) hlt
      have hQa : Q a = true := (hQ a (by simp)).mpr hlt
      simp only [List.filter_cons, hPa, hQa, ↓reduceIte, List.cons_append]
      rw [ih hsL hfd' (fun q hq => hmax q (by simp [hq]))
        (fun q hq => hdown q (by simp [hq])) (fun q hq => hQ q (by simp [hq]))]

theorem afterL_choice_some (n : KNode) (t : Time) (req : ScanReq) (first eqMatch : Bool)
    (lc : Int) (fd : Found) (h : scanChoice n t req first eqMatch lc = some fd) :
    afterL n t req.forward (first && req.inclusive && eqMatch) lc =
      (fd.c, fd.y) :: afterL n t req.forward false fd.c := by
  have hs := KNode.liveAt_order n t
  unfold scanChoice at h
  unfold afterL
  generalize (first && req.inclusive && eqMatch) = inc at h ⊢
  cases hfw : req.forward with
  | true =>
    simp only [hfw, ↓reduceIte] at h ⊢
    cases inc with
    | true =>
      simp only [↓reduceIte] at h ⊢
      obtain ⟨hm, ha, hd⟩ := (n.searchGte_spec t lc).1 fd h
      simp only [decide_eq_true_eq] at ha hd
      apply filter_eq_cons_of_min _ hs _ _ _ hm (by simpa using ha)
      · intro q hq hp; simpa using hd q hq (by simpa using hp)
      · intro q _ hlt; simp only [decide_eq_true_eq]; omega
      · intro q _; simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨hm, ha, hd⟩ := (n.searchGt_spec t lc).1 fd h
      simp only [decide_eq_true_eq] at ha hd
      apply filter_eq_cons_of_min _ hs _ _ _ hm (by simpa using ha)
      · intro q hq hp; simpa using hd q hq (by simpa using hp)
      · intro q _ hlt; simp only [decide_eq_true_eq]; omega
      · intro q _; simp
  | false =>
    simp only [hfw, Bool.false_eq_true, ↓reduceIte] at h ⊢
    cases inc with
    | true =>
      simp only [↓reduceIte] at h ⊢
      obtain ⟨hm, ha, hd⟩ := (n.searchLte_spec t lc).1 fd h
      simp only [decide_eq_true_eq] at ha hd
      rw [filter_eq_snoc_of_max _ hs _ (fun q => decide ((q.1 : Int) < fd.c)) _ hm
        (by simpa using ha)]
      · simp
      · intro q hq hp; simpa using hd q hq (by simpa using hp)
      · intro q _ hlt; simp only [decide_eq_true_eq]; omega
      · intro q _; simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨hm, ha, hd⟩ := (n.searchLt_spec t lc).1 fd h
      simp only [decide_eq_true_eq] at ha hd
      rw [filter_eq_snoc_of_max _ hs _ (fun q => decide ((q.1 : Int) < fd.c)) _ hm
        (by simpa using ha)]
      · simp
      · intro q hq hp; simpa using hd q hq (by simpa using hp)
      · intro q _ hlt; simp only [decide_eq_true_eq]; omega
      · intro q _; simp

theorem afterL_choice_none (n : KNode) (t : Time) (req : ScanReq) (first eqMatch : Bool)
    (lc : Int) (h : scanChoice n t req first eqMatch lc = none) :
    afterL n t req.forward (first && req.inclusive && eqMatch) lc = [] := by
  unfold scanChoice at h
  unfold afterL
  generalize (first && req.inclusive && eqMatch) = inc at h ⊢
  cases hfw : req.forward <;> cases inc <;>
    simp only [hfw, Bool.false_eq_true, ↓reduceIte] at h ⊢
  · have hh := (n.searchLt_spec t lc).2.mp h
    simpa [List.filter_eq_nil_iff] using hh
  · have hh := (n.searchLte_spec t lc).2.mp h
    simpa [List.filter_eq_nil_iff] using hh
  · have hh := (n.searchGt_spec t lc).2.mp h
    simpa [List.filter_eq_nil_iff] using hh
  · have hh := (n.searchGte_spec t lc).2.mp h
    simpa [List.filter_eq_nil_iff] using hh

end SIS.Tree
