import SIS.Tree.ScanSetupProof
import SIS.Tree.RunEncoding
import SIS.Tree.GetLatest

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! TP11 at the latest time from TP10 there (bergdb 024-12, TP11): on a sound
tree a scan gives the tree's contents in its range, in its order, the first
`limit`; the contents are the reference map's when every get is. So
`LatestScanOK` follows from `LatestGetOK` and the latest invariant, and TP11
from TP7 and `LatestGetOK`. -/

/-! ## The setup's chain gives the contents from the start key on -/

theorem setupGo_first (p : Params) (v : View BVal) (t : Time) (fw : Bool) (start : List Int)
    (f x index : Nat) (hasDiff : Bool) (ch : Chain) :
    (setupGo p v t fw start f x index hasDiff ch).first = ch.first := by
  induction f generalizing x index hasDiff ch with
  | zero => rfl
  | succ f ih =>
    cases hn : knodeOf p v x with
    | none => simp [setupGo, hn]
    | some n =>
      rw [setupGo_step p v t fw start f x index hasDiff ch n hn]
      cases setupChoice n t fw hasDiff (setupTarget fw start index) with
      | none => rfl
      | some fd =>
        simp only
        split
        · rfl
        · split
          · rw [ih]
          · rw [ih]

/-- A backward scan without a start key: the setup follows the last klong of
each inner node down to a leaf, and the chain's remainder is the whole subtree
backward. -/
theorem setupGo_last (p : Params) (v : View BVal) (t F : Nat) (d : Nat) :
    ∀ (f x : Nat) (ch : Chain), SNode p v t d x → d ≤ f → d ≤ F →
      chainRem p v t F false (setupGo p v t false [cvHi] f x 0 false ch).links
          (setupGo p v t false [cvHi] f x 0 false ch).segs false =
        (orient false (treeContents p v t F x)).map (fun kv => (ch.segs ++ kv.1, kv.2)) ++
          chainRem p v t F false ch.links (popSegs p v ch.segs ch.links) false := by
  induction d with
  | zero => intro f x ch hs; exact hs.elim
  | succ d ih =>
    intro f x ch hs hf hF
    cases f with
    | zero => omega
    | succ f =>
    have hs' := hs
    obtain ⟨n, hn, _, hb, hchildren⟩ := hs'
    have htarget : setupTarget false [cvHi] 0 = cvHi := rfl
    rw [setupGo_step p v t false [cvHi] f x 0 false ch n hn, htarget,
      treeContents_orient_F p v t d F x n hs hn hF false]
    cases hleaf : n.leaf with
    | true =>
      have hnone : setupChoice n t false false cvHi = none := by
        simp only [setupChoice, hleaf, Bool.false_eq_true, ↓reduceIte]
        apply (n.searchGte_spec t cvHi).2.mpr
        intro q hq
        have := hb q hq
        simp only [cvHi_eq, decide_eq_false_iff_not]
        omega
      rw [hnone]
      simp only [Bool.false_or, Bool.not_false, Bool.true_and, Bool.not_true,
        Bool.false_eq_true, ↓reduceIte]
      rw [chainRem_link p v t F false x _ ch.links ch.segs false n hn]
      have hs0 := afterL_sentinel n t false hb
      simp only [Bool.false_eq_true, ↓reduceIte] at hs0
      rw [hs0]
    | false =>
      cases hsc : setupChoice n t false false cvHi with
      | none =>
        have hempty : n.liveAt t = [] := by
          simp only [setupChoice, hleaf, Bool.false_eq_true, ↓reduceIte] at hsc
          have hall := (n.searchLte_spec t cvHi).2.mp hsc
          cases hl : n.liveAt t with
          | nil => rfl
          | cons q rest =>
            have := hall q (by rw [hl]; simp)
            have hq := hb q (by rw [hl]; simp)
            simp only [cvHi_eq, decide_eq_false_iff_not] at this
            omega
        simp only [Bool.false_or, Bool.not_false, Bool.true_and, Bool.true_or, ↓reduceIte]
        rw [chainRem_link p v t F false x _ ch.links ch.segs false n hn]
        simp [afterL, hempty, orient]
      | some fd =>
        have hmem := setupChoice_mem n t false false cvHi fd hsc
        have hmax : ∀ q ∈ n.liveAt t, q.1 ≤ fd.c := by
          simp only [setupChoice, hleaf, Bool.false_eq_true, ↓reduceIte] at hsc
          obtain ⟨_, _, hd⟩ := (n.searchLte_spec t cvHi).1 fd hsc
          intro q hq
          have hq' := hb q hq
          have := hd q hq (by simp only [cvHi_eq, decide_eq_true_eq]; omega)
          simpa using this
        obtain ⟨_, hnot⟩ := hchildren _ hmem
        obtain ⟨_, _, _, hcs, _, _⟩ := hnot (by simp [hleaf])
        simp only [hleaf, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        rw [ih f fd.y _ hcs (by omega) (by omega)]
        simp only
        rw [show popSegs p v ch.segs ((x, (fd.c : Int)) :: ch.links) = ch.segs by
            simpa [hleaf] using popSegs_link p v ch.segs x fd.c ch.links n hn,
          chainRem_link p v t F false x _ ch.links ch.segs false n hn, afterL_afterC]
        have hsplit := flatMap_split_bw (n.liveAt t) (KNode.liveAt_order n t) (fd.c, fd.y) hmem
          (klongC p v t F false n) (klongC p v t F false n)
          (fun q hq h => by have := hmax q hq; simp at h; omega) (fun _ _ _ => rfl)
        have hk : klongC p v t F false n (fd.c, fd.y) =
            orient false (treeContents p v t F fd.y) := by
          simp [klongC, hleaf]
        simp only [orient, Bool.false_eq_true, ↓reduceIte] at hsplit hk ⊢
        rw [hsplit, hk]
        simp [afterC, List.map_append, List.append_assoc]

/-- Whether a key is at or after the scan's start key, in the scan's
direction (strictly after unless inclusive); every key without a start key. -/
def startOK (req : ScanReq) (k : Key) : Bool :=
  match req.start with
  | none => true
  | some s => relOK req.forward req.inclusive s k

/-- The chain that the setup builds from a sound space root has, as its
remainder, the root's contents from the start key on, in the scan's order. -/
theorem chainSetup_rem (p : Params) (v : View BVal) (t : Time) (req : ScanReq)
    (hreq : req.wf = true) (r : NodeId) (hs : SNode p v t p.fuel r) :
    rem p v t p.fuel req (chainSetup p v t req r) =
      orient req.forward ((treeContents p v t p.fuel r).filter (fun kv => startOK req kv.1)) := by
  have hfuel : p.fuel = ((p.G + 1) * (p.H + 2) + 1) + 1 := rfl
  cases hst : req.start with
  | some s =>
    have hswf : keyWf s = true := by
      simp only [ScanReq.wf, hst, Bool.and_eq_true] at hreq
      exact hreq.1
    have hm := setupGo_match p v t p.fuel req.forward req.inclusive s hswf p.fuel p.fuel
      r {} s hs (Nat.le_refl _) (Nat.le_refl _) (by simp) hswf _ rfl
    unfold rem incOf chainSetup
    simp only [hst, setupGo_first]
    simp only [List.nil_append, List.length_nil] at hm
    simp only [Bool.true_and]
    rw [hm]
    simp [startOK, hst, popSegs, chainRem]
  | none =>
    have hft : ∀ l : List (Key × Nat), l.filter (fun _ => true) = l :=
      fun l => List.filter_eq_self.mpr (fun _ _ => rfl)
    simp only [startOK, hst, hft]
    unfold rem incOf chainSetup
    simp only [hst]
    cases hfw : req.forward with
    | false =>
      have hl := setupGo_last p v t p.fuel p.fuel p.fuel r {} hs (Nat.le_refl _) (Nat.le_refl _)
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [chainEq, Bool.and_false]
      rw [hl]
      simp [popSegs, chainRem]
    | true =>
      simp only [↓reduceIte, chainEq, Bool.and_false]
      rw [hfuel] at hs ⊢
      have hs' := hs
      obtain ⟨n, hn, _, hb, _⟩ := hs'
      rw [setupGo_step p v t true [cvLo] _ r 0 false {} n hn]
      have hnone : setupChoice n t true false (setupTarget true [cvLo] 0) = none := by
        simp only [setupChoice, setupTarget, Bool.false_eq_true, ↓reduceIte]
        apply (n.searchLte_spec t cvLo).2.mpr
        intro q _
        simp only [cvLo_eq, decide_eq_false_iff_not]
        omega
      rw [hnone]
      simp only [Bool.true_or, ↓reduceIte]
      rw [chainRem_link p v t _ true r _ [] [] false n hn]
      have hs0 := afterL_sentinel n t true hb
      simp only [↓reduceIte] at hs0
      rw [hs0, ← treeContents_orient_F p v t _ _ r n hs hn (Nat.le_refl _) true]
      simp [chainRem, orient]

/-! ## The order of keys -/

theorem keyLt_trichotomy (a b : Key) : keyLt a b = true ∨ a = b ∨ keyLt b a = true := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact Or.inr (Or.inl rfl)
    | cons _ _ => exact Or.inl rfl
  | cons x xs ih =>
    cases b with
    | nil => exact Or.inr (Or.inr rfl)
    | cons y ys =>
      simp only [keyLt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq,
        List.cons.injEq]
      rcases Nat.lt_trichotomy x y with h | rfl | h
      · exact Or.inl (Or.inl h)
      · rcases ih ys with h | h | h
        · exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr (Or.inl ⟨rfl, h⟩)
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
      · exact Or.inr (Or.inr (Or.inl h))

theorem endOK_not (e k : Key) (incl : Bool) :
    (if incl then !keyLt e k else keyLt k e) = !(keyLt e k || (k == e && !incl)) := by
  rcases keyLt_trichotomy k e with h | rfl | h
  · have ha := keyLt_asymm _ _ h
    have hne : (k == e) = false := by
      cases hb : (k == e) with
      | false => rfl
      | true =>
        rw [beq_iff_eq] at hb
        subst hb
        rw [keyLt_irrefl] at h
        cases h
    cases incl <;> simp [ha, hne, h]
  · cases incl <;> simp [keyLt_irrefl]
  · have ha := keyLt_asymm _ _ h
    cases incl <;> simp [ha, h]

/-- The range of a scan is its start condition and the end key's. -/
theorem inRange_eq (req : ScanReq) (k : Key) :
    inRange req k = (startOK req k && !endPast req k) := by
  rcases req with ⟨start, incl, fw, endKey, endIncl⟩
  cases start <;> cases endKey <;> simp only [inRange, startOK, endPast, relOK, endOK_not] <;> rfl

theorem takeWhile_endPast (req : ScanReq) (L : List (Key × Nat))
    (hs : L.Pairwise (fun a b => keyLt a.1 b.1 = true)) :
    L.takeWhile (fun kv => !endPast req kv.1) = L.filter (fun kv => !endPast req kv.1) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    have hsa := (List.pairwise_cons.mp hs).1
    cases hp : endPast req a.1 with
    | false =>
      simp only [List.takeWhile_cons, List.filter_cons, hp, Bool.not_false, ↓reduceIte,
        ih (List.pairwise_cons.mp hs).2]
    | true =>
      simp only [List.takeWhile_cons, List.filter_cons, hp, Bool.not_true, Bool.false_eq_true,
        ↓reduceIte]
      symm
      apply List.filter_eq_nil_iff.mpr
      intro b hb
      simp [endPast_mono req a.1 b.1 hp (Or.inl (hsa b hb))]

theorem takeWhile_true {α : Type} (l : List α) : l.takeWhile (fun _ => true) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.takeWhile_cons, ih]

/-- The scan's end key on its sorted remainder: a filter. -/
theorem takeWhile_orient (req : ScanReq) (hreq : req.wf = true) (L : List (Key × Nat))
    (hs : L.Pairwise (fun a b => keyLt a.1 b.1 = true)) :
    (orient req.forward L).takeWhile (fun kv => !endPast req kv.1) =
      orient req.forward (L.filter (fun kv => !endPast req kv.1)) := by
  cases hfw : req.forward with
  | true => exact takeWhile_endPast req L hs
  | false =>
    have he : req.endKey = none := by
      cases he : req.endKey with
      | none => rfl
      | some e => simp [ScanReq.wf, he, hfw] at hreq
    have hp : ∀ k, endPast req k = false := by intro k; simp [endPast, he]
    simp only [hp, Bool.not_false, takeWhile_true]
    exact congrArg (orient false) (List.filter_eq_self.mpr (fun _ _ => rfl)).symm

/-! ## The reference map's list -/

theorem eraseDups_nodup' {α : Type} [BEq α] [LawfulBEq α] : ∀ (l : List α), l.eraseDups.Nodup
  | [] => by simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]
  | a :: as => by
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    constructor
    · intro h
      rw [List.mem_eraseDups] at h
      simp at h
    · exact eraseDups_nodup' _
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  exact Nat.lt_succ_of_le (List.length_filter_le _ as)

theorem refFold_some (key : Key) (l : List Op) (v : Option Nat) (h : Nat)
    (hf : l.foldl (fun v op => if op.key == key then (match op with
      | .put _ h => some h
      | .del _ => none) else v) v = some h) :
    v = some h ∨ key ∈ l.map (·.key) := by
  induction l generalizing v with
  | nil => exact Or.inl (by simpa using hf)
  | cons op l ih =>
    simp only [List.foldl_cons] at hf
    rcases ih _ hf with h1 | h1
    · by_cases hk : op.key = key
      · exact Or.inr (by simp [hk])
      · left
        have hk' : (op.key == key) = false := by simpa using hk
        simpa [hk'] using h1
    · exact Or.inr (by simp only [List.map_cons, List.mem_cons]; exact Or.inr h1)

theorem refGet_some_key (ts : List Tx) (t : Time) (key : Key) (h : Nat)
    (hr : refGet ts t key = some h) : key ∈ ((ts.take t).flatMap (·.ops)).map (·.key) := by
  unfold refGet at hr
  rcases refFold_some key _ none h hr with h1 | h1
  · cases h1
  · exact h1

theorem mem_refKvs (ts : List Tx) (t : Time) (k : Key) (h : Nat) :
    (k, h) ∈ refKvs ts t ↔ refGet ts t k = some h := by
  unfold refKvs
  simp only [List.mem_mergeSort, List.mem_filterMap, List.mem_eraseDups, Option.map_eq_some_iff]
  constructor
  · rintro ⟨k', _, h', hr, he⟩
    cases he
    exact hr
  · intro hr
    exact ⟨k, refGet_some_key ts t k h hr, h, hr, rfl⟩

theorem filterMap_fst_sublist (keys : List Key) (g : Key → Option Nat) :
    List.Sublist ((keys.filterMap (fun k => (g k).map (fun h => (k, h)))).map Prod.fst) keys := by
  induction keys with
  | nil => simp
  | cons k keys ih =>
    cases hg : g k with
    | none => simp only [List.filterMap_cons, hg, Option.map_none]; exact ih.cons k
    | some h =>
      simp only [List.filterMap_cons, hg, Option.map_some, List.map_cons]
      exact ih.cons_cons k

theorem refKvs_sorted (ts : List Tx) (t : Time) :
    (refKvs ts t).Pairwise (fun a b => keyLt a.1 b.1 = true) := by
  unfold refKvs
  simp only
  generalize hL : (List.filterMap (fun k => (refGet ts t k).map (fun h => (k, h)))
    (List.map (·.key) (List.flatMap (·.ops) (List.take t ts))).eraseDups) = L
  have hnd : (L.map Prod.fst).Nodup := by
    rw [← hL]
    exact (filterMap_fst_sublist _ _).nodup (eraseDups_nodup' _)
  have hle := List.pairwise_mergeSort (le := fun a b : Key × Nat => !keyLt b.1 a.1)
    (fun a b c hab hbc => by
      simp only [Bool.not_eq_true'] at hab hbc ⊢
      cases hca : keyLt c.1 a.1 with
      | false => rfl
      | true =>
        rcases keyLt_trichotomy a.1 b.1 with h | h | h
        · have := keyLt_trans _ _ _ hca h
          rw [hbc] at this; cases this
        · rw [← h] at hbc; rw [hbc] at hca; cases hca
        · rw [hab] at h; cases h)
    (fun a b => by
      cases h : keyLt b.1 a.1 with
      | false => rfl
      | true => simp [keyLt_asymm _ _ h]) L
  have hnd' : ((L.mergeSort (fun a b => !keyLt b.1 a.1)).map Prod.fst).Nodup :=
    ((List.mergeSort_perm L _).map Prod.fst).nodup_iff.mpr hnd
  have hne := List.pairwise_map.mp hnd'
  apply (hle.and hne).imp
  intro a b ⟨h1, h2⟩
  rcases keyLt_trichotomy a.1 b.1 with h | h | h
  · exact h
  · exact absurd h h2
  · simp [h] at h1

theorem eq_of_sorted_mem (L1 L2 : List (Key × Nat))
    (h1 : L1.Pairwise (fun a b => keyLt a.1 b.1 = true))
    (h2 : L2.Pairwise (fun a b => keyLt a.1 b.1 = true))
    (hm : ∀ x, x ∈ L1 ↔ x ∈ L2) : L1 = L2 := by
  induction L1 generalizing L2 with
  | nil =>
    cases L2 with
    | nil => rfl
    | cons b L2 => exact absurd ((hm b).mpr (by simp)) (by simp)
  | cons a L1 ih =>
    cases L2 with
    | nil => exact absurd ((hm a).mp (by simp)) (by simp)
    | cons b L2 =>
      have ha1 := (List.pairwise_cons.mp h1).1
      have hb2 := (List.pairwise_cons.mp h2).1
      have hab : a = b := by
        rcases List.mem_cons.mp ((hm a).mp (by simp)) with h | h
        · exact h
        · have hba := hb2 a h
          rcases List.mem_cons.mp ((hm b).mpr (by simp)) with h' | h'
          · exact h'.symm
          · have := keyLt_trans _ _ _ (ha1 b h') hba
            rw [keyLt_irrefl] at this
            cases this
      subst hab
      congr 1
      apply ih L2 (List.pairwise_cons.mp h1).2 (List.pairwise_cons.mp h2).2
      intro x
      constructor
      · intro hx
        rcases List.mem_cons.mp ((hm x).mp (by simp [hx])) with h | h
        · subst h
          have := ha1 x hx
          rw [keyLt_irrefl] at this
          cases this
        · exact h
      · intro hx
        rcases List.mem_cons.mp ((hm x).mpr (by simp [hx])) with h | h
        · subst h
          have := hb2 x hx
          rw [keyLt_irrefl] at this
          cases this
        · exact h

/-! ## The scan on a sound tree, and at the latest time -/

/-- On a tree without faults at t, a scan gives the contents at t in its range,
in its order, the first `limit`. -/
theorem scan_eq_contents (p : Params) (P : Struct BVal) (t : Time)
    (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P) (henc : ViewEncoded (viewOf P))
    (hinv : InvOK p P t) (req : ScanReq) (hreq : req.wf = true) (limit : Nat) :
    (scan p (viewOf P) t req limit).map (fun kv => (kv.key, kv.h)) =
      (orient req.forward ((rootContents p P t).filter (fun kv => inRange req kv.1))).take limit := by
  unfold InvOK faultsAt at hinv
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hinv
  | some r =>
    simp only [hr] at hinv
    have hs := sNode_of_walk p P t p.fuel hkinds hdata henc r 0 none true true hinv
    have hc : SChain p (viewOf P) t p.fuel (chainSetup p (viewOf P) t req r).links :=
      setupGo_sChain p _ t _ _ p.fuel p.fuel p.fuel r 0 false {} hs (by simp) trivial
    have hdir : req.forward = false → req.endKey = none := by
      intro hfw
      cases he : req.endKey with
      | none => rfl
      | some e => simp [ScanReq.wf, he, hfw] at hreq
    rw [scan_eq_rem p (viewOf P) t p.fuel req limit (Nat.le_refl _) hdir r hr hc,
      chainSetup_rem p (viewOf P) t req hreq r hs]
    have hsorted := treeContents_sorted p _ t p.fuel r hs
    rw [takeWhile_orient req hreq _ (hsorted.filter _), List.filter_filter]
    unfold rootContents
    rw [hr]
    simp only [inRange_eq, Bool.and_comm]

theorem rootContents_sorted (p : Params) (P : Struct BVal) (t : Time)
    (hkinds : HighKindsOK p P) (hdata : DataEntriesOK P) (henc : ViewEncoded (viewOf P))
    (hinv : InvOK p P t) :
    (rootContents p P t).Pairwise (fun a b => keyLt a.1 b.1 = true) := by
  unfold InvOK faultsAt at hinv
  unfold rootContents
  cases hr : rootAt (viewOf P) t with
  | none => simp
  | some r =>
    simp only [hr] at hinv ⊢
    exact treeContents_sorted p _ t p.fuel r
      (sNode_of_walk p P t p.fuel hkinds hdata henc r 0 none true true hinv)

theorem refKvs_keyWf (p : Params) (ts : List Tx) (hw : Within p ts) (t : Time) (k : Key)
    (h : Nat) (hm : (k, h) ∈ refKvs ts t) : keyWf k = true := by
  have hk := refGet_some_key ts t k h ((mem_refKvs ts t k h).mp hm)
  obtain ⟨op, hop, hk⟩ := List.mem_map.mp hk
  obtain ⟨tx, htx, hop⟩ := List.mem_flatMap.mp hop
  have hwf := (hw.1 tx (List.mem_of_mem_take htx)).2
  simp only [Tx.wf, List.all_eq_true] at hwf
  rw [← hk]
  exact hwf op hop

/-- When every get at the latest time is the reference map's, the tree's
contents then are the reference map's list. -/
theorem rootContents_eq_refKvs (p : Params) (ts : List Tx) (hw : Within p ts)
    (hi : InvOK p (treeRun p ts) ts.length) (hget : LatestGetOK p) :
    rootContents p (treeRun p ts) ts.length = refKvs ts ts.length := by
  have henc := structEncoded_viewOf _ (treeRun_encoded_of_within p ts hw)
  apply eq_of_sorted_mem _ _
    (rootContents_sorted p _ _ (treeRun_highKindsOK p ts) (treeRun_dataEntriesOK p ts) henc hi)
    (refKvs_sorted ts ts.length)
  intro ⟨k, h⟩
  by_cases hk : keyWf k = true
  · rw [← get_mem_rootContents p _ _ (treeRun_highKindsOK p ts) hi k hk h, hget ts hw k hk,
      mem_refKvs]
  · constructor
    · intro hm
      exfalso
      apply hk
      unfold rootContents at hm
      cases hr : rootAt (viewOf (treeRun p ts)) ts.length with
      | none => simp [hr] at hm
      | some r =>
        rw [hr] at hm
        exact treeRun_treeContents_keyWf p ts hw ts.length p.fuel r (k, h) hm
    · intro hm
      exact absurd (refKvs_keyWf p ts hw ts.length k h hm) hk

/-- TP11 at the latest time from TP10 there and the latest invariant: the scan
needs nothing of the writer beyond what the get needs. -/
theorem latestScanOK_of_latestGet (p : Params) (hinv : LatestInvOK p)
    (hget : LatestGetOK p) : LatestScanOK p := by
  intro ts hw req limit hreq
  have hi := hinv ts hw
  rw [scan_eq_contents p _ ts.length (treeRun_highKindsOK p ts) (treeRun_dataEntriesOK p ts)
    (structEncoded_viewOf _ (treeRun_encoded_of_within p ts hw)) hi req hreq limit,
    rootContents_eq_refKvs p ts hw hi hget]
  simp only [refScan, orient]

/-- TP11 from TP7 and TP10 at the latest time (`LatestGetOK`). -/
theorem scanOK_of_latestGet (p : Params) (hinv : InvPreserved p) (hget : LatestGetOK p) :
    ScanOK p :=
  scanOK_of_latest p hinv
    (latestScanOK_of_latestGet p (fun ts hw => (hinv ts hw ts.length (Nat.le_refl _)).1) hget)

/-- TP11 from TP7 and one transaction's step of the map (`TxGetOK`). -/
theorem scanOK_of_txGet (p : Params) (hinv : InvPreserved p) (htx : TxGetOK p) : ScanOK p :=
  scanOK_of_latestGet p hinv (latestGetOK_of_txGet p htx)

end SIS.Tree
