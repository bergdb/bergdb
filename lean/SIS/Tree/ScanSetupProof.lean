import SIS.Tree.ScanNext

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The scan's setup positions its chain at the start key (bergdb 024-12,
TP11): the chain's remainder is the subtree's keys from the start key on. -/

/-- A key relative to a node is at or after the start key's rest s' in the
scan's direction (strictly after unless inclusive). -/
def relOK (fw incl : Bool) (s k : Key) : Bool :=
  if fw then (if incl then !keyLt k s else keyLt s k)
  else (if incl then !keyLt s k else keyLt k s)

theorem keyLt_asymm (a b : Key) (h : keyLt a b = true) : keyLt b a = false := by
  cases hb : keyLt b a with
  | false => rfl
  | true =>
    have := keyLt_trans _ _ _ h hb
    rw [keyLt_irrefl] at this
    cases this

theorem relOK_lt (fw incl : Bool) (s k : Key) (h : keyLt k s = true) :
    relOK fw incl s k = !fw := by
  have ha := keyLt_asymm _ _ h
  cases fw <;> cases incl <;> simp [relOK, h, ha]

theorem relOK_gt (fw incl : Bool) (s k : Key) (h : keyLt s k = true) :
    relOK fw incl s k = fw := by
  have ha := keyLt_asymm _ _ h
  cases fw <;> cases incl <;> simp [relOK, h, ha]

theorem relOK_self (fw incl : Bool) (s : Key) : relOK fw incl s s = incl := by
  cases fw <;> cases incl <;> simp [relOK, keyLt_irrefl]

theorem relOK_cons (fw incl : Bool) (c : Nat) (s k : Key) :
    relOK fw incl (c :: s) (c :: k) = relOK fw incl s k := by
  simp [relOK, keyLt_cons_same]

theorem flatMap_split_fw {β : Type} (L : List (Nat × NodeId))
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (fd : Nat × NodeId) (hfd : fd ∈ L)
    (h g : Nat × NodeId → List β)
    (hlo : ∀ q ∈ L, q.1 < fd.1 → h q = [])
    (hhi : ∀ q ∈ L, fd.1 < q.1 → h q = g q) :
    L.flatMap h = h fd ++ (L.filter (fun q => decide (fd.1 < q.1))).flatMap g := by
  induction L with
  | nil => simp at hfd
  | cons a L ih =>
    have hsa := (List.pairwise_cons.mp hs).1
    have hsL := (List.pairwise_cons.mp hs).2
    rcases List.mem_cons.mp hfd with rfl | hfd'
    · have e : L.filter (fun q => decide (fd.1 < q.1)) = L :=
        List.filter_eq_self.mpr (fun q hq => by simpa using hsa q hq)
      simp only [List.flatMap_cons, List.filter_cons, Nat.lt_irrefl, decide_false,
        Bool.false_eq_true, ↓reduceIte, e]
      congr 1
      exact flatMap_congr' L h g (fun q hq => hhi q (by simp [hq]) (hsa q hq))
    · have hlt := hsa fd hfd'
      have ha : h a = [] := hlo a (by simp) hlt
      have hna : decide (fd.1 < a.1) = false := by simp; omega
      simp only [List.flatMap_cons, ha, List.nil_append, List.filter_cons, hna,
        Bool.false_eq_true, ↓reduceIte]
      exact ih hsL hfd' (fun q hq => hlo q (by simp [hq])) (fun q hq => hhi q (by simp [hq]))

theorem flatMap_split_bw {β : Type} (L : List (Nat × NodeId))
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (fd : Nat × NodeId) (hfd : fd ∈ L)
    (h g : Nat × NodeId → List β)
    (hhi : ∀ q ∈ L, fd.1 < q.1 → h q = [])
    (hlo : ∀ q ∈ L, q.1 < fd.1 → h q = g q) :
    L.reverse.flatMap h = h fd ++ (L.filter (fun q => decide (q.1 < fd.1))).reverse.flatMap g := by
  induction L with
  | nil => simp at hfd
  | cons a L ih =>
    have hsa := (List.pairwise_cons.mp hs).1
    have hsL := (List.pairwise_cons.mp hs).2
    rcases List.mem_cons.mp hfd with rfl | hfd'
    · have e : L.filter (fun q => decide (q.1 < fd.1)) = [] :=
        List.filter_eq_nil_iff.mpr (fun q hq => by have := hsa q hq; simp; omega)
      have e2 : L.reverse.flatMap h = [] := List.flatMap_eq_nil_iff.mpr
        (fun q hq => hhi q (by simp at hq; simp [hq]) (hsa q (by simpa using hq)))
      simp [List.flatMap_append, e, e2]
    · have hlt := hsa fd hfd'
      have hya : decide (a.1 < fd.1) = true := by simp; omega
      simp only [List.reverse_cons, List.flatMap_append, List.filter_cons, hya, ↓reduceIte]
      rw [ih hsL hfd' (fun q hq => hhi q (by simp [hq])) (fun q hq => hlo q (by simp [hq]))]
      simp [hlo a (by simp) hlt]

theorem afterL_fw (n : KNode) (t : Time) (c : Nat) :
    afterL n t true false (c : Int) = (n.liveAt t).filter (fun q => decide (c < q.1)) := by
  simp [afterL]

theorem afterL_fw_inc (n : KNode) (t : Time) (c : Nat) :
    afterL n t true true (c : Int) = (n.liveAt t).filter (fun q => decide (c ≤ q.1)) := by
  simp [afterL]

theorem afterL_bw (n : KNode) (t : Time) (c : Nat) :
    afterL n t false false (c : Int) = ((n.liveAt t).filter (fun q => decide (q.1 < c))).reverse := by
  simp [afterL]

theorem afterL_bw_inc (n : KNode) (t : Time) (c : Nat) :
    afterL n t false true (c : Int) = ((n.liveAt t).filter (fun q => decide (q.1 ≤ c))).reverse := by
  simp [afterL]

/-- The contents of a sound node through its klongs, at any fuel that fits. -/
theorem treeContents_orient_F (p : Params) (v : View BVal) (t d F x : Nat) (n : KNode)
    (hs : SNode p v t (d+1) x) (hn : knodeOf p v x = some n) (hF : d + 1 ≤ F) (fw : Bool) :
    orient fw (treeContents p v t F x) =
      (orient fw (n.liveAt t)).flatMap (klongC p v t F fw n) := by
  rw [treeContents_stable p v t (d+1) x hs F hF, treeContents_orient p v t d x n hn fw]
  have hs' := hs
  obtain ⟨n', hn', _, _, hc⟩ := hs'
  rw [hn] at hn'
  cases Option.some.inj hn'
  apply flatMap_congr'
  intro q hq
  have hq' : q ∈ n.liveAt t := by
    cases fw <;> simp [orient] at hq <;> exact hq
  obtain ⟨_, hnot⟩ := hc q hq'
  cases hk : (n.leaf && segLen q.1 != 7) with
  | true =>
    have hleaf : n.leaf = true := by simp_all
    have hlen : segLen q.1 ≠ 7 := by simp_all
    simp [klongC, hleaf, hlen]
  | false =>
    obtain ⟨_, _, _, hcs, _⟩ := hnot hk
    simp only [klongC, treeContents_stable p v t d q.2 hcs F (by omega)]

/-- A link with nothing left to give passes its chain on. -/
theorem chainRem_cons_empty (p : Params) (v : View BVal) (t F : Nat) (fw : Bool)
    (x : NodeId) (lc : Int) (rest : List (NodeId × Int)) (segs : List Nat) (inc : Bool)
    (n : KNode) (hn : knodeOf p v x = some n) (he : afterL n t fw inc lc = []) :
    chainRem p v t F fw ((x, lc) :: rest) segs inc =
      chainRem p v t F fw rest (popSegs p v segs rest) false := by
  simp [chainRem, hn, he]

theorem cvHi_eq : cvHi = 9223372036854775807 := by decide

theorem cvLo_eq : cvLo = -1 := by decide

/-- Setup builds a chain of sound links within the path bound. -/
theorem setupGo_sChain (p : Params) (v : View BVal) (t : Time) (forward : Bool)
    (start : List Int) (bound fuel depth x index : Nat) (hasDiff : Bool) (ch : Chain)
    (hs : SNode p v t depth x) (hb : depth + ch.links.length ≤ bound)
    (hc : SChain p v t bound ch.links) :
    SChain p v t bound (setupGo p v t forward start fuel x index hasDiff ch).links := by
  induction fuel generalizing depth x index hasDiff ch with
  | zero => exact hc
  | succ fuel ih =>
    cases depth with
    | zero => exact hs.elim
    | succ depth =>
      have hs' := hs
      obtain ⟨n, hn, _, _, hchildren⟩ := hs'
      rw [setupGo_step p v t forward start fuel x index hasDiff ch n hn]
      cases hf : setupChoice n t forward hasDiff (setupTarget forward start index) with
      | none => exact ⟨depth+1, hs, hb, hc⟩
      | some fd =>
        have hmem := setupChoice_mem n t forward hasDiff _ fd hf
        have hparent : SChain p v t bound ((x, (fd.c : Int)) :: ch.links) :=
          ⟨depth+1, hs, hb, hc⟩
        simp only
        split
        · exact hparent
        · rename_i hstop
          obtain ⟨hshort, hnot⟩ := hchildren _ hmem
          have hk : (n.leaf && segLen fd.c != 7) = false := by
            cases hl : n.leaf with
            | false => rfl
            | true =>
              simp only [hl, Bool.true_and] at hstop ⊢
              have : segLen fd.c ≠ 7 ∨ segLen fd.c = 7 := by omega
              rcases this with h | h
              · exfalso; apply hstop; simp only [decide_eq_true_eq]
                have : segLen fd.c < 8 := Nat.mod_lt _ (by omega)
                omega
              · simp [h]
          obtain ⟨_, _, _, hcs, _⟩ := hnot hk
          split <;> apply ih depth fd.y _ _ _ hcs _ hparent <;>
            simp only [List.length_cons] <;> omega

/-- Once the setup has left the start key, it follows the last klong forward
(the first backward) down to a value: the links it adds give nothing more. -/
theorem setupGo_diff (p : Params) (v : View BVal) (t F : Nat) (fw : Bool)
    (start : List Int) (d : Nat) :
    ∀ (f x index : Nat) (ch : Chain), SNode p v t d x →
      (∃ cn, knodeOf p v x = some cn ∧ cn.liveAt t ≠ []) → d ≤ f →
      (∃ B, (setupGo p v t fw start f x index true ch).segs = ch.segs ++ B) ∧
      chainRem p v t F fw (setupGo p v t fw start f x index true ch).links
          (setupGo p v t fw start f x index true ch).segs false =
        chainRem p v t F fw ch.links (popSegs p v ch.segs ch.links) false := by
  induction d with
  | zero => intro f x index ch hs; exact hs.elim
  | succ d ih =>
    intro f x index ch hs hne hf
    obtain ⟨cn, hcn, hcne⟩ := hne
    have hs' := hs
    obtain ⟨n, hn, _, _, hchildren⟩ := hs'
    rw [hcn] at hn
    cases Option.some.inj hn
    have hord := KNode.liveAt_order cn t
    cases f with
    | zero => omega
    | succ f =>
      rw [setupGo_step p v t fw start f x index true ch cn hcn]
      -- the search picks the last (forward) or first (backward) live klong
      have hpick : ∃ fd, setupChoice cn t fw true (setupTarget fw start index) = some fd ∧
          (fd.c, fd.y) ∈ cn.liveAt t ∧ afterL cn t fw false fd.c = [] := by
        have hb := sNode_bound p v t (d+1) x hs cn hcn
        cases fw with
        | true =>
          cases hsr : cn.searchLt t cvHi with
          | none =>
            have h := (cn.searchLt_spec t cvHi).2.mp hsr
            obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hcne
            have h1 := h q hq
            have h2 := hb q hq
            simp only [cvHi_eq, decide_eq_false_iff_not] at h1
            omega
          | some fd =>
            obtain ⟨hm, _, hd⟩ := (cn.searchLt_spec t cvHi).1 fd hsr
            refine ⟨fd, by simp [setupChoice, hsr], hm, ?_⟩
            rw [afterL_fw]
            apply List.filter_eq_nil_iff.mpr
            intro q hq
            have h2 := hb q hq
            have h1 := hd q hq (by apply decide_eq_true; simp only [cvHi_eq]; omega)
            try simp only [decide_eq_true_eq] at h1
            simp only [decide_eq_true_eq]
            omega
        | false =>
          cases hsr : cn.searchGt t cvLo with
          | none =>
            have h := (cn.searchGt_spec t cvLo).2.mp hsr
            obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hcne
            have h1 := h q hq
            simp only [cvLo_eq, decide_eq_false_iff_not] at h1
            omega
          | some fd =>
            obtain ⟨hm, _, hd⟩ := (cn.searchGt_spec t cvLo).1 fd hsr
            refine ⟨fd, by simp [setupChoice, hsr], hm, ?_⟩
            rw [afterL_bw]
            simp only [List.reverse_eq_nil_iff]
            apply List.filter_eq_nil_iff.mpr
            intro q hq
            have h1 := hd q hq (by apply decide_eq_true; simp only [cvLo_eq]; omega)
            try simp only [decide_eq_true_eq] at h1
            simp only [decide_eq_true_eq]
            omega
      obtain ⟨fd, hsc, hmem, hempty⟩ := hpick
      rw [hsc]
      simp only
      obtain ⟨hshort, hnot⟩ := hchildren _ hmem
      split
      · refine ⟨⟨[], by simp⟩, ?_⟩
        exact chainRem_cons_empty p v t F fw x _ ch.links ch.segs false cn hcn hempty
      · rename_i hstop
        have hk : (cn.leaf && segLen fd.c != 7) = false := by
          cases hl : cn.leaf with
          | false => rfl
          | true =>
            simp only [hl, Bool.true_and] at hstop ⊢
            have : segLen fd.c < 8 := Nat.mod_lt _ (by omega)
            simp only [decide_eq_true_eq] at hstop
            simp; omega
        obtain ⟨_, _, _, hcs, hcne', _⟩ := hnot hk
        have hpop : ∀ segs2 : List Nat, segs2 = (if cn.leaf then ch.segs ++ [fd.c] else ch.segs) →
            popSegs p v segs2 ((x, (fd.c : Int)) :: ch.links) = ch.segs := by
          intro segs2 he
          subst he
          cases hl : cn.leaf <;> simp [popSegs, hcn, hl]
        split
        · rename_i hl
          simp only [Bool.true_or]
          obtain ⟨⟨B, hB⟩, hr⟩ := ih f fd.y (index + 1) _ hcs hcne' (by omega)
          refine ⟨⟨fd.c :: B, by rw [hB]; simp⟩, ?_⟩
          rw [hr, hpop _ (by simp [hl])]
          exact chainRem_cons_empty p v t F fw x _ ch.links ch.segs false cn hcn hempty
        · rename_i hl
          obtain ⟨⟨B, hB⟩, hr⟩ := ih f fd.y index _ hcs hcne' (by omega)
          refine ⟨⟨B, by rw [hB]⟩, ?_⟩
          rw [hr, hpop _ (by simp [hl])]
          exact chainRem_cons_empty p v t F fw x _ ch.links ch.segs false cn hcn hempty

theorem setupGo_diff' (p : Params) (v : View BVal) (t F : Nat) (fw : Bool)
    (start : List Int) (d f x index : Nat) (ch : Chain) (hs : SNode p v t d x)
    (hne : ∃ cn, knodeOf p v x = some cn ∧ cn.liveAt t ≠ []) (hf : d ≤ f) (res : Chain)
    (hres : setupGo p v t fw start f x index true ch = res) :
    (∃ B, res.segs = ch.segs ++ B) ∧
      chainRem p v t F fw res.links res.segs false =
        chainRem p v t F fw ch.links (popSegs p v ch.segs ch.links) false := by
  subst hres
  exact setupGo_diff p v t F fw start d f x index ch hs hne hf

/-! ## Classifying a node's klongs against the start key -/

/-- The klongs of a node after (forward) or before (backward) compare value c,
in the scan's order. -/
def afterC (fw : Bool) (c : Nat) (L : List (Nat × NodeId)) : List (Nat × NodeId) :=
  if fw then L.filter (fun q => decide (c < q.1)) else (L.filter (fun q => decide (q.1 < c))).reverse

theorem afterL_afterC (n : KNode) (t : Time) (fw : Bool) (c : Nat) :
    afterL n t fw false (c : Int) = afterC fw c (n.liveAt t) := by
  cases fw
  · rw [afterL_bw]; rfl
  · rw [afterL_fw]; rfl

/-- Splitting a node's klongs at a pivot: those before it give nothing forward
and all backward, those after it the reverse. -/
theorem flatMap_pivot {β : Type} (fw : Bool) (L : List (Nat × NodeId))
    (hs : L.Pairwise (fun a b => a.1 < b.1)) (fd : Nat × NodeId) (hfd : fd ∈ L)
    (G g : Nat × NodeId → List β)
    (hbefore : ∀ q ∈ L, q.1 < fd.1 → G q = if fw then [] else g q)
    (hafter : ∀ q ∈ L, fd.1 < q.1 → G q = if fw then g q else []) :
    (orient fw L).flatMap G = G fd ++ (afterC fw fd.1 L).flatMap g := by
  cases fw with
  | true =>
    exact flatMap_split_fw L hs fd hfd G g (fun q hq h => by simpa using hbefore q hq h)
      (fun q hq h => by simpa using hafter q hq h)
  | false =>
    exact flatMap_split_bw L hs fd hfd G g (fun q hq h => by simpa using hafter q hq h)
      (fun q hq h => by simpa using hbefore q hq h)

/-- The keys a klong gives: each starts with a compare value at or above the
klong's, the klong's own in a leaf, below every later klong's in an inner node. -/
theorem klongC_keys (p : Params) (v : View BVal) (t d F x : Nat) (n : KNode)
    (hs : SNode p v t (d+1) x) (hn : knodeOf p v x = some n) (hdF : d ≤ F) (fw : Bool)
    (q : Nat × NodeId) (hq : q ∈ n.liveAt t) (k : Key × Nat)
    (hk : k ∈ klongC p v t F fw n q) :
    ∃ c r, k.1 = c :: r ∧ q.1 ≤ c ∧ (n.leaf = true → c = q.1) ∧
      (n.leaf = false → ∀ r' ∈ n.liveAt t, q.1 < r'.1 → c < r'.1) := by
  obtain ⟨n', hn', _, _, hc⟩ := hs
  rw [hn] at hn'
  cases Option.some.inj hn'
  obtain ⟨_, hnot⟩ := hc q hq
  cases hleaf : n.leaf with
  | true =>
    simp only [klongC, hleaf, ↓reduceIte] at hk
    split at hk
    · obtain ⟨kv, _, he⟩ := List.mem_map.mp hk
      exact ⟨q.1, kv.1, by rw [← he], Nat.le_refl _, fun _ => rfl, fun h => by simp at h⟩
    · split at hk
      · simp at hk
      · simp only [List.mem_singleton] at hk
        exact ⟨q.1, [], by rw [hk], Nat.le_refl _, fun _ => rfl, fun h => by simp at h⟩
  | false =>
    obtain ⟨_, _, _, hcs, _, hrange⟩ := hnot (by simp [hleaf])
    simp only [klongC, hleaf, Bool.false_eq_true, ↓reduceIte] at hk
    have hk' : k ∈ treeContents p v t d q.2 := by
      rw [← treeContents_stable p v t d q.2 hcs F hdF]
      cases fw <;> simp [orient] at hk <;> exact hk
    obtain ⟨c, r, he, hle, hlt⟩ := hrange hleaf k hk'
    exact ⟨c, r, he, hle, fun h => by simp at h, fun _ => hlt⟩

theorem filter_lo {β : Type} (fw : Bool) (P : β → Bool) (l : List β)
    (h : ∀ k ∈ l, P k = !fw) : l.filter P = if fw then [] else l := by
  cases fw
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_self.mpr (fun k hk => by simpa using h k hk)
  · simp only [↓reduceIte]
    exact List.filter_eq_nil_iff.mpr (fun k hk => by simp [h k hk])

theorem filter_hi {β : Type} (fw : Bool) (P : β → Bool) (l : List β)
    (h : ∀ k ∈ l, P k = fw) : l.filter P = if fw then l else [] := by
  cases fw
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact List.filter_eq_nil_iff.mpr (fun k hk => by simp [h k hk])
  · simp only [↓reduceIte]
    exact List.filter_eq_self.mpr (fun k hk => by simpa using h k hk)

/-- A klong whose keys are below the start key's rest: forward it gives
nothing, backward all. -/
theorem klongC_lo (p : Params) (v : View BVal) (t d F x : Nat) (n : KNode)
    (hs : SNode p v t (d+1) x) (hn : knodeOf p v x = some n) (hdF : d ≤ F)
    (fw incl : Bool) (s0 : Nat) (sr : Key) (q : Nat × NodeId) (hq : q ∈ n.liveAt t)
    (hlo : (n.leaf = true → q.1 < s0) ∧
      (n.leaf = false → ∃ r' ∈ n.liveAt t, q.1 < r'.1 ∧ r'.1 ≤ s0)) :
    (klongC p v t F fw n q).filter (fun kv => relOK fw incl (s0 :: sr) kv.1) =
      if fw then [] else klongC p v t F fw n q := by
  apply filter_lo
  intro k hk
  obtain ⟨c, r, he, hle, hleafc, hinner⟩ := klongC_keys p v t d F x n hs hn hdF fw q hq k hk
  apply relOK_lt
  rw [he]
  apply keyLt_cons_lt
  cases hleaf : n.leaf with
  | true => rw [hleafc hleaf]; exact hlo.1 hleaf
  | false =>
    obtain ⟨r', hr', hqr, hrs⟩ := hlo.2 hleaf
    have := hinner hleaf r' hr' hqr
    omega

/-- A klong above the start key: forward it gives all, backward nothing. -/
theorem klongC_hi (p : Params) (v : View BVal) (t d F x : Nat) (n : KNode)
    (hs : SNode p v t (d+1) x) (hn : knodeOf p v x = some n) (hdF : d ≤ F)
    (fw incl : Bool) (s0 : Nat) (sr : Key) (q : Nat × NodeId) (hq : q ∈ n.liveAt t)
    (hhi : s0 < q.1) :
    (klongC p v t F fw n q).filter (fun kv => relOK fw incl (s0 :: sr) kv.1) =
      if fw then klongC p v t F fw n q else [] := by
  apply filter_hi
  intro k hk
  obtain ⟨c, r, he, hle, _, _⟩ := klongC_keys p v t d F x n hs hn hdF fw q hq k hk
  apply relOK_gt
  rw [he]
  apply keyLt_cons_lt
  omega

theorem setupTarget_eq (fw : Bool) (segs s' : Key) (s0 : Nat) (sr : Key)
    (hs' : s' = s0 :: sr) :
    setupTarget fw ((segs ++ s').map (fun c : Nat => (c : Int))) segs.length = (s0 : Int) := by
  subst hs'
  simp [setupTarget]

theorem chainEq_lc (ch : Chain) (s : Key) (hs : keyWf s = true) (x : NodeId) (lc : Int)
    (rest : List (NodeId × Int)) (hl : ch.links = (x, lc) :: rest)
    (hlc : lc < 0 ∨ 2^62 ≤ lc) : chainEq ch (some s) = false := by
  have hseg : ∀ c ∈ s, c < 2^62 := by
    intro c hc
    induction s with
    | nil => simp at hc
    | cons a r ih =>
      cases r with
      | nil =>
        simp only [List.mem_singleton] at hc
        subst hc
        simp only [keyWf, Bool.and_eq_true, decide_eq_true_eq] at hs
        exact hs.1.1
      | cons b r' =>
        simp only [keyWf, Bool.and_eq_true, decide_eq_true_eq] at hs
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hs.1.1.1
        · exact ih hs.2 hc
  unfold chainEq
  rw [hl]
  simp only [List.head?_cons]
  cases hg : s.getLast? with
  | none => simp
  | some c =>
    have hc := hseg c (List.mem_of_getLast? hg)
    have hne : (some (c : Int) == some lc) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
      omega
    simp [hne]

theorem chainEq_stop (ch : Chain) (segs s' : Key) (c : Nat) (x : NodeId)
    (rest : List (NodeId × Int)) (hl : ch.links = (x, (c : Int)) :: rest)
    (hsegs : ch.segs = segs) (hne : s' ≠ []) :
    chainEq ch (some (segs ++ s')) = decide (s' = [c]) := by
  unfold chainEq
  rw [hl, hsegs]
  simp only [List.head?_cons, List.length_append, List.take_left', beq_self_eq_true,
    Bool.and_true]
  cases s' with
  | nil => exact absurd rfl hne
  | cons a r =>
    cases r with
    | nil => by_cases h : a = c <;> simp [h] <;> omega
    | cons b r => simp

theorem chainEq_diff (ch : Chain) (segs B : Key) (c s0 : Nat) (sr : Key)
    (hsegs : ch.segs = segs ++ c :: B) (hne : c ≠ s0) :
    chainEq ch (some (segs ++ s0 :: sr)) = false := by
  unfold chainEq
  cases hh : ch.links.head? with
  | none => rfl
  | some lk =>
    have hne' : (ch.segs == (segs ++ s0 :: sr).take ch.segs.length) = false := by
      rw [beq_eq_false_iff_ne]
      intro h
      rw [hsegs] at h
      simp only [List.length_append, List.length_cons] at h
      rw [List.take_length_add_append] at h
      simp at h
      exact hne h.1
    simp [hne']

theorem afterL_inc_cons (n : KNode) (t : Time) (fw : Bool) (fd : Nat × NodeId)
    (hfd : fd ∈ n.liveAt t) :
    afterL n t fw true (fd.1 : Int) = fd :: afterC fw fd.1 (n.liveAt t) := by
  have hs := KNode.liveAt_order n t
  cases fw with
  | true =>
    rw [afterL_fw_inc]
    exact filter_eq_cons_of_min _ hs _ _ fd hfd (by simp) (fun q _ h => by simpa using h)
      (fun q _ h => by simp; omega) (fun q _ => by simp)
  | false =>
    rw [afterL_bw_inc]
    rw [filter_eq_snoc_of_max _ hs _ (fun q => decide (q.1 < fd.1)) fd hfd (by simp)
      (fun q _ h => by simpa using h) (fun q _ h => by simp; omega) (fun q _ => by simp)]
    simp [afterC]

/-- The klongs of a node against the start key's rest s0 :: sr, split at a
pivot klong: those before it are below the start key, those after above. -/
theorem rhs_pivot (p : Params) (v : View BVal) (t d F x : Nat) (n : KNode)
    (hs : SNode p v t (d+1) x) (hn : knodeOf p v x = some n) (hdF : d ≤ F)
    (fw incl : Bool) (s0 : Nat) (sr : Key) (fd : Nat × NodeId) (hfd : fd ∈ n.liveAt t)
    (hbefore : ∀ q ∈ n.liveAt t, q.1 < fd.1 → (n.leaf = true → q.1 < s0) ∧
      (n.leaf = false → ∃ r' ∈ n.liveAt t, q.1 < r'.1 ∧ r'.1 ≤ s0))
    (hafter : ∀ q ∈ n.liveAt t, fd.1 < q.1 → s0 < q.1) :
    (orient fw (n.liveAt t)).flatMap
        (fun q => (klongC p v t F fw n q).filter (fun kv => relOK fw incl (s0 :: sr) kv.1)) =
      (klongC p v t F fw n fd).filter (fun kv => relOK fw incl (s0 :: sr) kv.1) ++
        (afterC fw fd.1 (n.liveAt t)).flatMap (klongC p v t F fw n) :=
  flatMap_pivot fw _ (KNode.liveAt_order n t) fd hfd _ _
    (fun q hq h => klongC_lo p v t d F x n hs hn hdF fw incl s0 sr q hq (hbefore q hq h))
    (fun q hq h => klongC_hi p v t d F x n hs hn hdF fw incl s0 sr q hq (hafter q hq h))

theorem orient_filter {α : Type} (fw : Bool) (P : α → Bool) (l : List α) :
    orient fw (l.filter P) = (orient fw l).filter P := by
  cases fw <;> simp [orient, List.filter_reverse]

theorem keyWf_tail (c : Nat) (r : Key) (hw : keyWf (c :: r) = true) (hl : segLen c = 7) :
    keyWf r = true := by
  cases r with
  | nil => simp [keyWf, hl] at hw
  | cons b r =>
    simp only [keyWf, Bool.and_eq_true] at hw
    exact hw.2

theorem keyWf_short (c : Nat) (r : Key) (hw : keyWf (c :: r) = true) (hl : segLen c ≠ 7) :
    r = [] := by
  cases r with
  | nil => rfl
  | cons b r =>
    simp only [keyWf, Bool.and_eq_true, beq_iff_eq] at hw
    exact absurd hw.1.2 hl

/-- The choice of the setup, matching the start key, at a node: the largest
klong at or below the start segment (forward, or an inner node), the smallest at
or above it (a leaf, backward). -/
theorem setupChoice_match (n : KNode) (t : Time) (fw : Bool) (s0 : Nat) :
    (setupChoice n t fw false (s0 : Int) = none →
      ∀ q ∈ n.liveAt t, if fw || !n.leaf then s0 < q.1 else q.1 < s0) ∧
    (∀ fd, setupChoice n t fw false (s0 : Int) = some fd → (fd.c, fd.y) ∈ n.liveAt t ∧
      if fw || !n.leaf then fd.c ≤ s0 ∧ ∀ q ∈ n.liveAt t, q.1 ≤ s0 → q.1 ≤ fd.c
      else s0 ≤ fd.c ∧ ∀ q ∈ n.liveAt t, s0 ≤ q.1 → fd.c ≤ q.1) := by
  have hlte : setupChoice n t fw false (s0 : Int) =
      (if fw || !n.leaf then n.searchLte t s0 else n.searchGte t s0) := by
    cases fw <;> cases hl : n.leaf <;> simp [setupChoice, hl]
  rw [hlte]
  by_cases hm : (fw || !n.leaf) = true
  · simp only [hm, ↓reduceIte]
    constructor
    · intro h q hq
      have := (n.searchLte_spec t s0).2.mp h q hq
      simp only [decide_eq_false_iff_not] at this
      omega
    · intro fd h
      obtain ⟨hm', ha, hd⟩ := (n.searchLte_spec t s0).1 fd h
      refine ⟨hm', by simpa using ha, fun q hq hle => ?_⟩
      have := hd q hq (by simpa using hle)
      simpa using this
  · simp only [hm, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h q hq
      have := (n.searchGte_spec t s0).2.mp h q hq
      simp only [decide_eq_false_iff_not] at this
      omega
    · intro fd h
      obtain ⟨hm', ha, hd⟩ := (n.searchGte_spec t s0).1 fd h
      refine ⟨hm', by simpa using ha, fun q hq hle => ?_⟩
      have := hd q hq (by simpa using hle)
      simpa using this

theorem chainRem_link (p : Params) (v : View BVal) (t F : Nat) (fw : Bool) (x : NodeId)
    (lc : Int) (rest : List (NodeId × Int)) (segs : List Nat) (inc : Bool) (n : KNode)
    (hn : knodeOf p v x = some n) :
    chainRem p v t F fw ((x, lc) :: rest) segs inc =
      ((afterL n t fw inc lc).flatMap (klongC p v t F fw n)).map
          (fun kv => (segs ++ kv.1, kv.2)) ++
        chainRem p v t F fw rest (popSegs p v segs rest) false := by
  simp [chainRem, hn]

theorem popSegs_link (p : Params) (v : View BVal) (segs : List Nat) (x : NodeId) (c : Nat)
    (rest : List (NodeId × Int)) (n : KNode) (hn : knodeOf p v x = some n) :
    popSegs p v (if n.leaf then segs ++ [c] else segs) ((x, (c : Int)) :: rest) = segs := by
  cases hl : n.leaf <;> simp [popSegs, hn, hl]

/-- Setup that matches the start key from node x on: the chain's remainder is
x's keys from the start key's rest s' on, in the scan's order (the start key
itself included when the scan is inclusive and the key is there), then what
the chain below x had. -/
theorem setupGo_match (p : Params) (v : View BVal) (t F : Nat) (fw incl : Bool) (s : Key)
    (hswf : keyWf s = true) (d : Nat) :
    ∀ (f x : Nat) (ch : Chain) (s' : Key), SNode p v t d x → d ≤ f → d ≤ F →
      ch.segs ++ s' = s → keyWf s' = true →
      ∀ res, setupGo p v t fw (s.map (fun c : Nat => (c : Int))) f x ch.segs.length false ch = res →
      chainRem p v t F fw res.links res.segs (incl && chainEq res (some s)) =
        (orient fw ((treeContents p v t F x).filter (fun kv => relOK fw incl s' kv.1))).map
            (fun kv => (ch.segs ++ kv.1, kv.2)) ++
          chainRem p v t F fw ch.links (popSegs p v ch.segs ch.links) false := by
  induction d with
  | zero => intro f x ch s' hs; exact hs.elim
  | succ d ih =>
    intro f x ch s' hs hf hF hseg hwf res hres
    cases f with
    | zero => omega
    | succ f =>
    have hs' := hs
    obtain ⟨n, hn, _, _, hchildren⟩ := hs'
    obtain ⟨s0, sr, rfl⟩ : ∃ s0 sr, s' = s0 :: sr := by
      cases s' with
      | nil => simp [keyWf] at hwf
      | cons a r => exact ⟨a, r, rfl⟩
    have htarget : setupTarget fw (s.map (fun c : Nat => (c : Int))) ch.segs.length = (s0 : Int) := by
      rw [← hseg]; exact setupTarget_eq fw ch.segs _ s0 sr rfl
    rw [setupGo_step p v t fw _ f x ch.segs.length false ch n hn, htarget] at hres
    rw [orient_filter, treeContents_orient_F p v t d F x n hs hn hF fw, List.filter_flatMap]
    have hspec := setupChoice_match n t fw s0
    have hdF : d ≤ F := by omega
    cases hsc : setupChoice n t fw false (s0 : Int) with
    | none =>
      have hall := hspec.1 hsc
      rw [hsc] at hres
      simp only at hres
      subst hres
      rw [chainEq_lc _ s hswf x _ ch.links rfl (by
        cases fw <;> cases n.leaf <;> simp [cvLo, cvHi]), Bool.and_false,
        chainRem_link p v t F fw x _ ch.links ch.segs false n hn]
      congr 1
      congr 1
      cases fw with
      | true =>
        simp only [Bool.true_or, ↓reduceIte] at hall ⊢
        rw [show afterL n t true false cvLo = orient true (n.liveAt t) from
          afterL_sentinel n t true (sNode_bound p v t (d+1) x hs n hn)]
        apply flatMap_congr'
        intro q hq
        have := klongC_hi p v t d F x n hs hn hdF true incl s0 sr q hq (by
          have := hall q (by simpa [orient] using hq); simpa using this)
        simpa using this.symm
      | false =>
        cases hleaf : n.leaf with
        | false =>
          simp only [hleaf, Bool.false_or, Bool.not_false, ↓reduceIte, Bool.and_self,
            Bool.true_or] at hall ⊢
          rw [show afterL n t false false cvLo = [] by
            simp only [afterL, Bool.false_eq_true, ↓reduceIte, List.reverse_eq_nil_iff]
            apply List.filter_eq_nil_iff.mpr
            intro q _
            simp only [cvLo_eq, decide_eq_true_eq]
            omega]
          simp only [List.flatMap_nil]
          symm
          apply List.flatMap_eq_nil_iff.mpr
          intro q hq
          have hq' : q ∈ n.liveAt t := by simpa [orient] using hq
          have := klongC_hi p v t d F x n hs hn hdF false incl s0 sr q hq' (by
            have := hall q hq'; simpa using this)
          simpa using this
        | true =>
          simp only [hleaf, Bool.false_or, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
            Bool.and_false] at hall ⊢
          rw [show afterL n t false false cvHi = orient false (n.liveAt t) from
            afterL_sentinel n t false (sNode_bound p v t (d+1) x hs n hn)]
          apply flatMap_congr'
          intro q hq
          have hq' : q ∈ n.liveAt t := by simpa [orient] using hq
          have := klongC_lo p v t d F x n hs hn hdF false incl s0 sr q hq'
            ⟨fun _ => hall q hq', fun h => by simp [hleaf] at h⟩
          simpa using this.symm
    | some fd =>
      obtain ⟨hmem, hfd⟩ := hspec.2 fd hsc
      rw [hsc] at hres
      simp only at hres
      -- the pivot facts
      have hbefore : ∀ q ∈ n.liveAt t, q.1 < (fd.c, fd.y).1 → (n.leaf = true → q.1 < s0) ∧
          (n.leaf = false → ∃ r' ∈ n.liveAt t, q.1 < r'.1 ∧ r'.1 ≤ s0) := by
        intro q hq hlt
        split at hfd
        · refine ⟨fun _ => by simp at hlt; omega, fun _ => ⟨_, hmem, hlt, hfd.1⟩⟩
        · rename_i hmode
          have hleaf : n.leaf = true := by
            cases hl : n.leaf <;> simp_all
          refine ⟨fun _ => ?_, fun h => by simp [hleaf] at h⟩
          rcases Nat.lt_or_ge q.1 s0 with hc | hc
          · exact hc
          · have := hfd.2 q hq hc
            simp at hlt; omega
      have hafter : ∀ q ∈ n.liveAt t, (fd.c, fd.y).1 < q.1 → s0 < q.1 := by
        intro q hq hlt
        split at hfd
        · rcases Nat.lt_or_ge s0 q.1 with hc | hc
          · exact hc
          · have := hfd.2 q hq hc
            simp at hlt; omega
        · simp at hlt; omega
      rw [rhs_pivot p v t d F x n hs hn hdF fw incl s0 sr (fd.c, fd.y) hmem hbefore hafter]
      obtain ⟨hshort, hnot⟩ := hchildren _ hmem
      by_cases hstop : (n.leaf && decide (segLen fd.c < 7)) = true
      · simp only [hstop, ↓reduceIte] at hres
        have hleaf : n.leaf = true := by simp_all
        have hlen : segLen fd.c ≠ 7 := by simp at hstop; omega
        obtain ⟨nd, h, hy, hd, hv⟩ := hshort (by simp [hleaf, hlen])
        have hk : klongC p v t F fw n (fd.c, fd.y) = [([fd.c], h)] := by
          cases fw <;> simp [klongC, hleaf, hlen, hv]
        have hl : res.links = (x, (fd.c : Int)) :: ch.links := by rw [← hres]
        have hsg : res.segs = ch.segs := by rw [← hres]
        rw [← hseg, chainEq_stop res ch.segs (s0 :: sr) fd.c x ch.links hl hsg (by simp),
          hl, hsg, chainRem_link p v t F fw x _ ch.links ch.segs _ n hn, hk]
        by_cases heq : fd.c = s0
        · subst heq
          have hsr : sr = [] := keyWf_short _ sr hwf hlen
          subst hsr
          simp only [decide_true, Bool.and_true]
          rw [show [([fd.c], h)].filter (fun kv => relOK fw incl [fd.c] kv.1) =
              if incl then [([fd.c], h)] else [] by
            cases incl <;> simp [relOK_self]]
          cases incl with
          | true =>
            simp only [↓reduceIte]
            rw [afterL_inc_cons n t fw (fd.c, fd.y) hmem]
            simp [hk]
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
            rw [afterL_afterC]
        · have hne : (s0 :: sr = [fd.c]) = False := by simp; intro h; exact absurd h.symm heq
          simp only [hne, decide_false, Bool.and_false]
          rw [afterL_afterC]
          have hG : [([fd.c], h)].filter (fun kv => relOK fw incl (s0 :: sr) kv.1) = [] := by
            split at hfd
            · rename_i hmode
              have hfw : fw = true := by cases fw <;> simp_all
              subst hfw
              have : keyLt [fd.c] (s0 :: sr) = true := keyLt_cons_lt _ _ _ _ (by omega)
              simp [relOK_lt _ _ _ _ this]
            · rename_i hmode
              have hfw : fw = false := by cases fw <;> simp_all
              subst hfw
              have : keyLt (s0 :: sr) [fd.c] = true := keyLt_cons_lt _ _ _ _ (by omega)
              simp [relOK_gt _ _ _ _ this]
          rw [hG]
          simp
      · simp only [hstop, Bool.false_eq_true, ↓reduceIte] at hres
        have hkind : (n.leaf && segLen fd.c != 7) = false := by
          cases hl : n.leaf with
          | false => rfl
          | true =>
            simp only [hl, Bool.true_and, decide_eq_true_eq] at hstop
            have : segLen fd.c < 8 := Nat.mod_lt _ (by omega)
            simp; omega
        obtain ⟨_, _, _, hcs, hcne, _⟩ := hnot hkind
        cases hleaf : n.leaf with
        | true =>
          simp only [hleaf, ↓reduceIte, Bool.false_or] at hres
          have hlen : segLen fd.c = 7 := by simpa [hleaf] using hkind
          have hkC : klongC p v t F fw n (fd.c, fd.y) =
              (orient fw (treeContents p v t F fd.y)).map (fun kv => (fd.c :: kv.1, kv.2)) := by
            simp [klongC, hleaf, hlen]
          by_cases heq : fd.c = s0
          · subst heq
            simp only [bne_self_eq_false] at hres
            have hsr := keyWf_tail _ sr hwf hlen
            have hlen' : (ch.segs ++ [fd.c]).length = ch.segs.length + 1 := by simp
            have ih' := ih f fd.y { ch with links := (x, (fd.c : Int)) :: ch.links, seen := fd.y :: ch.seen, segs := ch.segs ++ [fd.c] }
              sr hcs (by omega) hdF (by simp [← hseg]) hsr res (by rw [← hres]; simp only [hlen'])
            rw [ih']
            simp only
            rw [show popSegs p v (ch.segs ++ [fd.c]) ((x, (fd.c : Int)) :: ch.links) = ch.segs by
                simpa [hleaf] using popSegs_link p v ch.segs x fd.c ch.links n hn,
              chainRem_link p v t F fw x _ ch.links ch.segs false n hn, afterL_afterC]
            have hG : (klongC p v t F fw n (fd.c, fd.y)).filter
                (fun kv => relOK fw incl (fd.c :: sr) kv.1) =
                ((orient fw (treeContents p v t F fd.y)).filter (fun kv => relOK fw incl sr kv.1)).map
                  (fun kv => (fd.c :: kv.1, kv.2)) := by
              rw [hkC, List.filter_map]
              simp only [Function.comp_def, relOK_cons]
            rw [hG, orient_filter]
            simp [List.map_append, List.map_map, List.append_assoc, Function.comp_def]
          · have hdiff : ((fd.c : Int) != (s0 : Int)) = true := by simp; omega
            simp only [hdiff] at hres
            obtain ⟨⟨B, hB⟩, hr⟩ := setupGo_diff' p v t F fw (s.map (fun c : Nat => (c : Int))) d f
              fd.y (ch.segs.length + 1) { ch with links := (x, (fd.c : Int)) :: ch.links, seen := fd.y :: ch.seen, segs := ch.segs ++ [fd.c] }
              hcs hcne (by omega) res hres
            rw [← hseg, chainEq_diff res ch.segs B fd.c s0 sr (by rw [hB]; simp) heq,
              Bool.and_false, hr]
            simp only
            rw [show popSegs p v (ch.segs ++ [fd.c]) ((x, (fd.c : Int)) :: ch.links) = ch.segs by
              simpa [hleaf] using popSegs_link p v ch.segs x fd.c ch.links n hn,
              chainRem_link p v t F fw x _ ch.links ch.segs false n hn, afterL_afterC]
            have hG : (klongC p v t F fw n (fd.c, fd.y)).filter
                (fun kv => relOK fw incl (s0 :: sr) kv.1) = [] := by
              apply List.filter_eq_nil_iff.mpr
              intro kv hkv
              obtain ⟨c, r, he, _, hcq, _⟩ :=
                klongC_keys p v t d F x n hs hn hdF fw (fd.c, fd.y) hmem kv hkv
              have hc : c = fd.c := hcq hleaf
              split at hfd
              · have hfw : fw = true := by cases fw <;> simp_all
                subst hfw
                have : keyLt kv.1 (s0 :: sr) = true := by
                  rw [he]; apply keyLt_cons_lt; omega
                simp [relOK_lt _ _ _ _ this]
              · have hfw : fw = false := by cases fw <;> simp_all
                subst hfw
                have : keyLt (s0 :: sr) kv.1 = true := by
                  rw [he]; apply keyLt_cons_lt; omega
                simp [relOK_gt _ _ _ _ this]
            rw [hG]
            simp
        | false =>
          simp only [hleaf, Bool.false_eq_true, ↓reduceIte] at hres
          have ih' := ih f fd.y { ch with links := (x, (fd.c : Int)) :: ch.links, seen := fd.y :: ch.seen }
            (s0 :: sr) hcs (by omega) hdF hseg hwf res hres
          rw [ih']
          simp only
          rw [show popSegs p v ch.segs ((x, (fd.c : Int)) :: ch.links) = ch.segs by
              simpa [hleaf] using popSegs_link p v ch.segs x fd.c ch.links n hn,
            chainRem_link p v t F fw x _ ch.links ch.segs false n hn, afterL_afterC]
          have hkC : klongC p v t F fw n (fd.c, fd.y) = orient fw (treeContents p v t F fd.y) := by
            simp [klongC, hleaf]
          rw [hkC, orient_filter]
          simp [List.map_append, List.append_assoc]

end SIS.Tree
