import SIS.Tree.GetPutPath
import SIS.Tree.PutInvDelRoot
import SIS.Tree.GetNewRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The delete of a key of one segment in a space whose root is a leaf (bergdb
024-12, TP10), the merges off: the bitmap in the root with room, or the root
full and split, in time with a new root, or in space with a new root over its
halves, in place for a root the transaction made. The reading after it
(`writerWP_del_leafRootR`): the key reads as no value, every other key as
before, when the writer's state after it has its paths within the fuel. -/

/-! ## The reading with the delete's leaf in place -/

/-- The reading of N with the leaf L's contents m, n's live klongs but cv's:
the delete's key reads as no value, every other key as before. -/
theorem getFromR_delVirtual (N : NodeId → Option KNode) (Val : NodeId → Option Nat) (i : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (r L rk : NodeId) (pre : List Nat) (cv : Nat) (n m : KNode)
    (hNL : N L = some n) (hnl : n.leaf = true) (hml : m.leaf = true)
    (hs : ∀ c', (m.searchEq i c').map (·.y) = if c' == cv then none else (n.searchEq i c').map (·.y))
    (hrk : segRootR N i fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' r →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv]) :
    ∀ key', keyWf key' = true → getFromR (updN N L m) Val i fuel key' r =
      if pre ++ [cv] == key' then none else getFromR N Val i fuel key' r := by
  have hA := getFromR_leaf_change_seg N (updN N L m) Val Val i fuel hfuel L pre cv r rk n m
    (fun x hx => (updN_ne _ _ _ _ hx).symm) hNL (updN_self _ _ _) hnl hml
    (fun c' hc' => by
      rw [hs c']
      have : (c' == cv) = false := by simpa using hc'
      rw [this]; rfl)
    hrk hcv hvisL huniq (fun _ _ _ _ _ _ _ _ _ _ => rfl)
  intro key' hkey'
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, hs cv]
    simp
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

/-- The space root L, a leaf whose nodes reached are below `bound`, with its
contents m, n's live klongs but cv's, in place: a tree from L whose nodes
reached are below bound, and whose reading is the delete's. -/
theorem delRoot_virtual (N : NodeId → Option KNode) (Val : NodeId → Option Nat) (i : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (L : NodeId) (n m : KNode) (cv bound : Nat)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hml : m.leaf = true) (hmwf : klongsWf m.ks = true) (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i)
    (hlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c)
    (hT : TreeOK N i L) (hwf : ∀ x xn, ReachS N i L x → N x = some xn → klongsWf xn.ks = true)
    (hlt : ∀ z, ReachS N i L z → z < bound)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel L)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' L →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = [] ++ [cv]) :
    TreeOK (updN N L m) i L ∧ (∀ z, ReachS (updN N L m) i L z → z < bound) ∧
    (∀ z zn, ReachS (updN N L m) i L z → updN N L m z = some zn → klongsWf zn.ks = true) ∧
    ∀ key', keyWf key' = true → getFromR (updN N L m) Val i fuel key' L =
      if [] ++ [cv] == key' then none else getFromR N Val i fuel key' L := by
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hsub : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hlook] at this
    by_cases hc : c = cv
    · subst hc; simp at this
    · have hc' : (c == cv) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [hL1]; exact lookup_some_mem this
  have hWx : updN N L n = N := by
    funext z
    by_cases hz : z = L
    · rw [hz, updN_self, hNL]
    · exact updN_ne _ _ _ _ hz
  obtain ⟨hV, hRV⟩ := treeOK_updN_sub N i L L n m (by rw [hWx]; exact hT) hsub
  rw [hWx] at hRV
  have hRN : ∀ z, ReachS (updN N L m) i L z → ReachS N i L z :=
    fun z hz => tReach_reachS _ _ _ _ (hRV z (reachS_tReach _ _ _ _ hz))
  have hs : ∀ c', (m.searchEq i c').map (·.y) = if c' == cv then none else (n.searchEq i c').map (·.y) := by
    intro c'; rw [KNode.searchEq_live m i hmwf hmt, hlook, KNode.searchEq_live n i hnwf hnt]
  refine ⟨hV, fun z hz => hlt z (hRN z hz), ?_, ?_⟩
  · intro z zn hz hzn
    by_cases hzL : z = L
    · subst hzL; rw [updN_self] at hzn; cases hzn; exact hmwf
    · rw [updN_ne _ _ _ _ hzL] at hzn
      exact hwf z zn (hRN z hz) hzn
  · exact getFromR_delVirtual N Val i fuel hfuel L L L [] cv n m hNL hnl hml hs rfl (by simp) hvisL huniq

/-- After a time split of the space root L, a leaf, for a delete: the new root Y
holds L's last version without cv, m; the nodes below `bound` but L are kept.
The delete's key reads as no value, every other key as before. -/
theorem getFromR_delRootTime (N A : NodeId → Option KNode) (Val : NodeId → Option Nat) (i : Time)
    (fuel : Nat) (hfuel : 1 ≤ fuel) (L Y : NodeId) (n m : KNode) (cv bound : Nat)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hml : m.leaf = true) (hmwf : klongsWf m.ks = true) (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i)
    (hlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c)
    (hT : TreeOK N i L) (hwf : ∀ x xn, ReachS N i L x → N x = some xn → klongsWf xn.ks = true)
    (hlt : ∀ z, ReachS N i L z → z < bound)
    (hAY : A Y = some m) (hA : ∀ z, z ≠ L → z < bound → A z = N z)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel L)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' L →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = [] ++ [cv]) :
    ∀ key', keyWf key' = true → getFromR A Val i fuel key' Y =
      if [] ++ [cv] == key' then none else getFromR N Val i fuel key' L := by
  obtain ⟨hV, hVlt, hVwf, hVread⟩ := delRoot_virtual N Val i fuel hfuel L n m cv bound hNL hnl hnwf hnt
    hml hmwf hmt hlook hT hwf hlt hvisL huniq
  have hren := getFromR_rename_root (updN N L m) A Val i fuel L Y m m (updN_self _ _ _) hAY rfl
    (fun _ _ => rfl) (fun _ _ => rfl) hVwf
    (fun z hz hzL => by rw [hA z hzL (hVlt z hz), updN_ne _ _ _ _ hzL])
    (fun z zn c hz hzn hc => hV.rootFree z c (reachS_tReach _ _ _ _ hz) ⟨zn, hzn, hc⟩)
  intro key' hkey'
  rw [hren key', hVread key' hkey']

/-- After a space split of the space root L, a leaf, for a delete: the new root
Y over the halves F and S of L's last version without cv, `newKlongs i pairs`;
the nodes below `bound` but L are kept (F is L for a split in place). When the
paths from Y fit the fuel, the delete's key reads as no value, every other key
as before. -/
theorem getFromR_delRootSpace (N A : NodeId → Option KNode) (Val : NodeId → Option Nat) (i : Time)
    (fuel : Nat) (hfuel2 : 2 ≤ fuel) (L F S Y : NodeId) (n : KNode) (cv bound : Nat)
    (pairs : List (Nat × NodeId)) (hps : CvSorted pairs) (hpne : pairs ≠ [])
    (hpl : ∀ c, pairs.lookup c = if c == cv then none else n.live.lookup c)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hT : TreeOK N i L) (hwf : ∀ x xn, ReachS N i L x → N x = some xn → klongsWf xn.ks = true)
    (hlt : ∀ z, ReachS N i L z → z < bound)
    (hAY : A Y = some ⟨false, newKlongs i [(0, F),
      ((halves true i ⟨true, newKlongs i pairs⟩ []).2.2, S)]⟩)
    (hAF : A F = some (halves true i ⟨true, newKlongs i pairs⟩ []).1)
    (hAS : A S = some (halves true i ⟨true, newKlongs i pairs⟩ []).2.1)
    (hA : ∀ z, z ≠ L → z < bound → A z = N z)
    (hfit : PathsFit A i Y fuel)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel L)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' L →
      (x, cv) ∈ eqVisits N i cv fuel L → N x = some m' → m'.leaf = true → key' = [] ++ [cv]) :
    ∀ key', keyWf key' = true → getFromR A Val i fuel key' Y =
      if [] ++ [cv] == key' then none else getFromR N Val i fuel key' L := by
  let m : KNode := ⟨true, newKlongs i pairs⟩
  have hml : m.leaf = true := rfl
  have hmwf : klongsWf m.ks = true := klongsWf_newKlongs i pairs
  have hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i := newKlongs_times i pairs
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hmlook' : ∀ c, m.live.lookup c = pairs.lookup c := by
    intro c
    rw [KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c hpn]
  have hmlook : ∀ c, m.live.lookup c = if c == cv then none else n.live.lookup c := by
    intro c; rw [hmlook', hpl]
  obtain ⟨hV, hVlt, hVwf, hVread⟩ := delRoot_virtual N Val i fuel (by omega) L n m cv bound hNL hnl hnwf
    hnt hml hmwf hmt hmlook hT hwf hlt hvisL huniq
  -- the halves
  obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
    cases hd : (pairs.drop (pairs.length / 2)) with
    | nil =>
      have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
      have : pairs.length = 0 := by omega
      exact absurd (List.eq_nil_of_length_eq_zero this) hpne
    | cons a _ => exact ⟨a, rfl⟩
  have hshape := halves_leaf_shape i pairs [] r hr
  simp only [List.head?_nil, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hshape
  have hsc : (halves true i ⟨true, newKlongs i pairs⟩ []).2.2 = r.1 := by rw [hshape]
  have hwfh := halves_newKlongs_wf true i pairs []
  have hlook := halves_leaf_lookup i pairs [] hps r hr (by simp)
  generalize hout : halves true i ⟨true, newKlongs i pairs⟩ [] = out at hAY hAF hAS hsc hwfh hshape hlook
  obtain ⟨f, s, sc⟩ := out
  simp only at hAY hAF hAS hsc hwfh hlook
  subst hsc
  simp only [Prod.mk.injEq] at hshape
  obtain ⟨hf, hs', _⟩ := hshape
  have hfl : f.leaf = true := by rw [hf]
  have hsl : s.leaf = true := by rw [hs']
  have hft : ∀ t', Klong.time t' ∈ f.ks → t' ≤ i := by rw [hf]; exact newKlongs_times i _
  have hst : ∀ t', Klong.time t' ∈ s.ks → t' ≤ i := by rw [hs']; exact newKlongs_times i _
  simp only [List.foldl_nil] at hlook
  have hleafF : ∀ c, c < r.1 → (f.searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c hc
    rw [KNode.searchEq_live f i hwfh.1 hft, KNode.searchEq_live m i hmwf hmt, hmlook']
    have := hlook c
    simp only [hc, ↓reduceIte] at this
    exact this
  have hleafS : ∀ c, r.1 ≤ c → (s.searchEq i c).map (·.y) = (m.searchEq i c).map (·.y) := by
    intro c hc
    rw [KNode.searchEq_live s i hwfh.2 hst, KNode.searchEq_live m i hmwf hmt, hmlook']
    have := hlook c
    simp only [show ¬ c < r.1 by omega, ↓reduceIte] at this
    exact this
  have hnew := getFromR_newRootRead (updN N L m) A Val i fuel L F S Y m f s r.1 (updN_self _ _ _) hAY
    hAF hAS hfl hsl (fun _ => hleafF) (fun _ => hleafS) (fun h => absurd h (by simp [m]))
    (fun h => absurd h (by simp [m])) hVwf
    (fun z hz hzL => by rw [hA z hzL (hVlt z hz), updN_ne _ _ _ _ hzL])
    (fun z zn c hz hzn hc => hV.rootFree z c (reachS_tReach _ _ _ _ hz) ⟨zn, hzn, hc⟩) hfit hfuel2
  intro key' hkey'
  rw [hnew key', hVread key' hkey']

/-! ## The writer's splits of the space root for a delete, the values kept -/

/-- `writerWP_handleFullWith_rootSpaceSplit_nil` with the values kept. -/
theorem writerWP_handleFullWith_rootSpaceSplit_nilV (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitNilAfter c w w' L n last ∧ w'.vals = w.vals) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  have hL3 : L ≠ w.next + 2 + 2 := by omega
  simp only [newKey, fresh, setMadeFor, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
        · simp only [lookup_upsert, List.lookup_append, hL1, hL2, hL3, ↓reduceIte, hlk]
          rfl
        refine ⟨⟨rfl, rfl, ?_⟩, by first | rfl | trivial⟩
        intro x
        simp only [lookup_upsert, List.lookup_append]
        by_cases hxL : x = L
        · subst hxL; simp
        · simp only [hxL, ↓reduceIte]
          by_cases h3 : x = w.next + 2 + 2
          · subst h3
            simp [show w.next + 2 + 2 ≠ w.next by omega]
          · simp only [h3, ↓reduceIte]
            by_cases h2 : x = w.next + 2
            · subst h2; simp
            · simp only [h2, ↓reduceIte]
              by_cases h1 : x = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                cases h : w.nodes.lookup x with
                | some m => rfl
                | none =>
                  show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                    ([(w.next + 2, { leaf := n.leaf, ks := [] })].lookup x)).or
                    ([(w.next + 2 + 2, { leaf := false, ks := [] })].lookup x) = none
                  rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2, lookup_cons_ne _ _ _ _ h3]; rfl

/-- `writerWP_handleFullWith_rootTimeSplit_nil` with the values kept. -/
theorem writerWP_handleFullWith_rootTimeSplit_nilV (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hLn : L < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 L [] last compact) c w (fun _ w' =>
      RootTimeSplitNilAfter c w w' L n last ∧ w'.vals = w.vals) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hL1 : L ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_nil last c _) ?_
    rintro l w1 ⟨hw1, hl⟩
    subst w1 hl
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known L n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨⟨rfl, rfl, ?_⟩, by first | rfl | trivial⟩
          intro x
          show (upsert _ L _).lookup x = _
          rw [lookup_upsert]
          by_cases hxL : x = L
          · simp [hxL]
          · simp only [hxL, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl

set_option linter.unusedSimpArgs false in
/-- `writerWP_handleFullWith_rootSpaceSplitInPlace_nil` with the values kept. -/
theorem writerWP_handleFullWith_rootSpaceSplitInPlace_nilV
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (L : NodeId) (n last : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hfirst : n.firstTime = some c.i)
    (hsplit : c.p.splitAbove < last.size) (hLn : L < w.next)
    (hny : w.nodes.lookup (w.next + 2) = none) :
    WriterWP (handleFullWith up 0 L [] last false) c w
      (fun _ w' => RootSpaceSplitInPlaceNilAfter c w w' L n last ∧ w'.vals = w.vals) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  have hsz : decide (last.size > c.p.splitAbove) = true := by
    simp only [decide_eq_true_eq, gt_iff_lt]; exact hsplit
  simp only [hnew, parentAt, writerWP_pure, hsz, Bool.not_false, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte]
  have hL1 : L ≠ w.next := by omega
  have hL2 : L ≠ w.next + 2 := by omega
  simp only [newKey, fresh, setMadeFor, replacedBy, note, putNode, newSuperRoot, writerWP_bind,
    writerWP_modify, writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    split <;>
    · simp only [writerWP_modify, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          split <;>
          · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set,
              Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            refine ⟨⟨rfl, rfl, ?_⟩, by first | rfl | trivial⟩
            intro x
            simp only [lookup_upsert, List.lookup_append]
            by_cases hxL : x = L
            · subst hxL; simp [hL1, hL2]
            · simp only [hxL, ↓reduceIte]
              by_cases h1 : x = w.next
              · subst h1; simp
              · simp only [h1, ↓reduceIte]
                by_cases h2 : x = w.next + 2
                · subst h2
                  rw [show w.nodes.lookup (w.next + 2) = none from hny]
                  have hb : (w.next + 2 == w.next) = false := by simp
                  simp [List.lookup, hb]
                · simp only [h2, ↓reduceIte]
                  cases h : w.nodes.lookup x with
                  | some m => rfl
                  | none =>
                    show (((none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := [] })].lookup x)).or
                      ([(w.next + 2, _)].lookup x)) = none
                    rw [lookup_cons_ne _ _ _ _ h1, lookup_cons_ne _ _ _ _ h2]; rfl

/-! ## The delete's bitmap in the space root -/

set_option maxHeartbeats 800000 in
/-- The bitmap of a delete of [cv] in the space root, a leaf: with room, the
root loses cv's klong; full, it is split in time (in place for a root the
transaction made) or in space (in place or not) under a new root. The state
reads as the delete, when its paths fit the fuel. -/
theorem writerWP_appendDeleteKlong_rootR (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv : Nat) (n : KNode) (w w3 : W)
    (hkey : keyWf [cv] = true) (hsa : 1 ≤ c.p.splitAbove)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (htkfresh : ∀ z, w.next ≤ z → w.taken.contains z = false)
    (hr3 : ReadsAs c.p base w w3) (hlk3 : w3.nodes.lookup w.top.rootKey = some n)
    (hsrc3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (huniq : ∀ key' x m', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some m' → m'.leaf = true → key' = [] ++ [cv]) :
    WriterWP (appendDeleteKlong w.top.rootKey 0 cv) c w3 (fun _ w4 =>
      PathsFit (wNode c.p base w4) c.i w4.top.rootKey c.p.fuel → ∀ key', keyWf key' = true →
        wGet c.p c.i base w4 key' = if [] ++ [cv] == key' then none else wGet c.p c.i base w key') := by
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hLt : w.taken.contains w.top.rootKey = false := (wNode_cases _ _ _ _ _ hroot).1
  have hnwf := hwfG _ _ hroot
  have hnt := htimesG _ _ hroot
  have hnext3 : w3.next = w.next := hr3.2.2.2.2
  have hLn : w.top.rootKey < w.next := hsrc3 _ (by rw [hlk3]; rfl)
  have hfree3 : ∀ z, w.next ≤ z → w3.nodes.lookup z = none := by
    intro z hz
    cases h' : w3.nodes.lookup z with
    | none => rfl
    | some _ => have := hsrc3 z (by rw [h']; rfl); omega
  have hev : eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hroot, hnl]
  have hvisL : (w.top.rootKey, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey := by
    rw [hev]; simp
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => hwfG x xn h
  have hreachlt : ∀ z, ReachS (wNode c.p base w) c.i w.top.rootKey z → z < w.next := by
    intro z hz
    cases hz with
    | root => exact hLn
    | step u un c' _ hu hun hmem => exact hlinksAll u c' z ⟨un, hun, hmem⟩
  obtain ⟨hleq, hlt, _⟩ := delLast_facts n c.i cv
  have hlook0 := KNode.delete_live_lookup n c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  obtain ⟨pairs, hpks, hps⟩ :=
    KNode.lastVersionGivenDel_order n c.i (bitsUnion n.lastBitmap (n.bitsOf cv))
  generalize hlastd : n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv)) = last
    at hleq hlt hlook0 hwf0 hpks
  have hlastE : last = ⟨true, newKlongs c.i pairs⟩ := by
    rw [← hleq, hnl, hpks]; rfl
  have hml : last.leaf = true := by rw [hlastE]
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hpl : ∀ c', pairs.lookup c' = if c' == cv then none else n.live.lookup c' := by
    intro c'
    rw [← hlook0 c', hlastE, KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c' hpn]
  -- the state after a split of the root, from w3 with a note
  have hN4 : ∀ (w4 : W) (s : String), w4.taken = ({ w3 with trail := s :: w3.trail } : W).taken →
      ∀ z, z ≠ w.top.rootKey → z < w.next →
      w4.nodes.lookup z = ({ w3 with trail := s :: w3.trail } : W).nodes.lookup z →
      wNode c.p base w4 z = wNode c.p base w z := by
    intro w4 s h4t z _ _ h4z
    rw [← hr3.1]
    simp only [wNode, h4t, h4z]
  have hv4 : ∀ (w4 : W) (s : String), w4.taken = ({ w3 with trail := s :: w3.trail } : W).taken →
      w4.vals = ({ w3 with trail := s :: w3.trail } : W).vals → wValue base w4 = wValue base w := by
    intro w4 s h4t h4v
    funext a
    simp only [wValue, h4t, h4v, hr3.2.2.1, hr3.2.2.2.1]
  have htk4 : ∀ (w4 : W) (s : String), w4.taken = ({ w3 with trail := s :: w3.trail } : W).taken →
      ∀ z, w.next ≤ z → w4.taken.contains z = false := by
    intro w4 s h4t z hz
    rw [h4t]; show w3.taken.contains z = false; rw [hr3.2.2.1]; exact htkfresh z hz
  by_cases hsp : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
      c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < last.size
  · obtain ⟨hnotTD, hfull, hbig⟩ := hsp
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    refine writerWP_appendDeleteKlong_spaceGenD c w.top.rootKey n cv 0 w3 _ hlk3 hne hnotTD hfull
      (fun s => ?_)
    unfold handleFull
    rw [hlastd]
    by_cases hmade : n.firstTime = some c.i
    · -- in place: the root keeps the first half, a new root above
      refine writerWP_mono (writerWP_handleFullWith_rootSpaceSplitInPlace_nilV _ w.top.rootKey n last c _
        hlk3 hmade hbig (by show w.top.rootKey < w3.next; omega) (hfree3 (w3.next + 2) (by omega))) ?_
      rintro _ w4 ⟨⟨h4t, h4root, h4n⟩, h4v⟩ hfit key' hkey'
      rw [hnl, hlastE] at h4n
      simp only at h4root
      rw [hnext3] at h4root
      unfold wGet
      rw [hv4 w4 s h4t h4v, h4root]
      rw [h4root] at hfit
      have hF : w.top.rootKey ≠ w.next := by omega
      have hS : w.next + 2 ≠ w.top.rootKey := by omega
      have hS2 : w.next + 2 ≠ w.next := by omega
      exact getFromR_delRootSpace (wNode c.p base w) (wNode c.p base w4) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey w.top.rootKey w.next (w.next + 2) n cv w.next pairs hps hpne hpl hroot hnl hnwf hnt
        hT hwfR hreachlt
        (by
          simp only [wNode, htk4 w4 s h4t (w.next + 2) (by omega), Bool.false_eq_true, ↓reduceIte, h4n,
            hnext3, hS, hS2]
          rfl)
        (by simp only [wNode, h4t, h4n, ↓reduceIte]; show (if w3.taken.contains _ then _ else _) = _
            rw [hr3.2.2.1, hLt]; rfl)
        (by simp only [wNode, htk4 w4 s h4t w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4n,
            hnext3, Ne.symm hF])
        (fun z h1 h2 => hN4 w4 s h4t z h1 h2 (by
          rw [h4n z]; simp only [h1, show z ≠ w3.next by omega, show z ≠ w3.next + 2 by omega, ↓reduceIte]))
        hfit hvisL huniq key' hkey'
    · -- the halves and a new root
      refine writerWP_mono (writerWP_handleFullWith_rootSpaceSplit_nilV _ w.top.rootKey n last c _
        hlk3 hmade hbig (by show w.top.rootKey < w3.next; omega)) ?_
      rintro _ w4 ⟨⟨h4t, h4root, h4n⟩, h4v⟩ hfit key' hkey'
      rw [hnl, hlastE] at h4n
      simp only at h4root
      rw [hnext3] at h4root
      unfold wGet
      rw [hv4 w4 s h4t h4v, h4root]
      rw [h4root] at hfit
      have h1 : w.next ≠ w.top.rootKey := by omega
      have h2 : w.next + 2 ≠ w.top.rootKey := by omega
      have h3 : w.next + 2 + 2 ≠ w.top.rootKey := by omega
      have h21 : w.next + 2 ≠ w.next := by omega
      have h31 : w.next + 2 + 2 ≠ w.next := by omega
      have h32 : w.next + 2 + 2 ≠ w.next + 2 := by omega
      exact getFromR_delRootSpace (wNode c.p base w) (wNode c.p base w4) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey w.next (w.next + 2) (w.next + 2 + 2) n cv w.next pairs hps hpne hpl hroot hnl hnwf hnt
        hT hwfR hreachlt
        (by
          simp only [wNode, htk4 w4 s h4t (w.next + 2 + 2) (by omega), Bool.false_eq_true, ↓reduceIte, h4n,
            hnext3, h3, h31, h32]
          rfl)
        (by simp only [wNode, htk4 w4 s h4t w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4n,
            hnext3, h1])
        (by simp only [wNode, htk4 w4 s h4t (w.next + 2) (by omega), Bool.false_eq_true, ↓reduceIte, h4n,
            hnext3, h2, h21])
        (fun z hz1 hz2 => hN4 w4 s h4t z hz1 hz2 (by
          rw [h4n z]
          simp only [hz1, show z ≠ w3.next by omega, show z ≠ w3.next + 2 by omega,
            show z ≠ w3.next + 2 + 2 by omega, ↓reduceIte]))
        hfit hvisL huniq key' hkey'
  · refine writerWP_appendDeleteKlong_timeGenD c base hvc [] cv 0 w.top.rootKey w.top.rootKey n w w3
      (fun w4 => PathsFit (wNode c.p base w4) c.i w4.top.rootKey c.p.fuel) (by omega) hkey rfl hvisL
      huniq hwfG hroot hnl hnt hLt hr3 hlk3 hne
      (fun h1 h2 => by rw [hlastd]; exact Nat.le_of_not_lt (fun h3 => hsp ⟨h1, h2, h3⟩))
      (fun compact s hcs hfirst => ?_)
    unfold handleFull
    rw [hlastd] at hcs ⊢
    refine writerWP_mono (writerWP_handleFullWith_rootTimeSplit_nilV _ w.top.rootKey n last compact c _
      hlk3 hfirst hcs (by show w.top.rootKey < w3.next; omega) (hfree3 w3.next (by omega))) ?_
    rintro _ w4 ⟨⟨h4t, h4root, h4n⟩, h4v⟩ _ key' hkey'
    rw [hleq] at h4n
    simp only at h4root
    rw [hnext3] at h4root
    unfold wGet
    rw [hv4 w4 s h4t h4v, h4root]
    have h1 : w.next ≠ w.top.rootKey := by omega
    exact getFromR_delRootTime (wNode c.p base w) (wNode c.p base w4) (wValue base w) c.i c.p.fuel (by omega)
      w.top.rootKey w.next n last cv w.next hroot hnl hnwf hnt hml hwf0 hlt hlook0 hT hwfR hreachlt
      (by simp only [wNode, htk4 w4 s h4t w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, h4n,
          hnext3, h1])
      (fun z hz1 hz2 => hN4 w4 s h4t z hz1 hz2 (by
        rw [h4n z]; simp only [hz1, show z ≠ w3.next by omega, ↓reduceIte]))
      hvisL huniq key' hkey'

/-! ## The delete in a space whose root is a leaf -/

set_option maxHeartbeats 800000 in
/-- A delete of a key of one segment [cv] in a space whose root is a leaf, the
merges off, whose bitmap changes: the root loses cv's klong (it may be emptied
and kept, the upward delete's first case), or is split, in time or in space,
under a new root, in place for a root the transaction made. The reading changes
by the delete alone, when the writer's state after it has its paths within the
fuel (`PathsFit`). -/
theorem writerWP_del_leafRootR (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv : Nat) (w : W) (n : KNode)
    (hmerges : c.p.merges = false) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf [cv] = true)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (huniq : ∀ key' x m', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some m' → m'.leaf = true → key' = [cv]) :
    WriterWP (putKv (.del [cv])) c w (fun _ w' =>
      PathsFit (wNode c.p base w') c.i w'.top.rootKey c.p.fuel → ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del [cv]) == key' then Op.value (.del [cv]) else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hids
  have hrt := (wNode_cases _ _ _ _ _ hroot).1
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  have htkfresh : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hp2 : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have hev : eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2, hr02.1]
    simp [eqVisits, hroot, hnl]
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hev, hr02.2.2.1]
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  refine writerWP_mono (writerWP_and
    (writerWP_descendLte_path cv c base hvc c.p.fuel w.top.rootKey w2 ht2 (by rw [hp2]; rfl))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel w.top.rootKey w2 ht2)) ?_
  intro L w3 ⟨⟨hr23, n', hn', _, hlk3, _, _, hdp⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr02.1] at hn'
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
  obtain ⟨hLr, hp3⟩ : L = w.top.rootKey ∧ w3.path = w2.path := by
    rcases hdp with h | ⟨pre', q, k1, qn, fd, _, _, hq, hql, _, _, _, hqv⟩
    · exact h
    · rw [hev] at hqv
      simp only [List.mem_singleton, Prod.mk.injEq] at hqv
      rw [hqv.1, hr02.1, hroot] at hq
      cases hq
      rw [hnl] at hql
      cases hql
  subst hLr
  rw [hroot] at hn'
  cases hn'
  have hlk3' : w3.nodes.lookup w.top.rootKey = some n := by simpa using hlk3
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rw [hw2n] at h1; exact hidn z h1
    · exact hidv z h1
  have hlen : w3.path.length - 1 = 0 := by rw [hp3, hp2]; rfl
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen]
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ n c _ hlk3']
  have hb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by simpa using hne
  simp only [hb, Bool.false_eq_true, ↓reduceIte]
  have hcore := writerWP_appendDeleteKlong_rootR c base hvc cv n w w3 hkey hsa hroot hnl hwfG htimesG hT
    hlinksAll htkfresh hr03 hlk3' hsrcw3 hne huniq
  -- the continuation after the bitmap: the merges off, the marker's id
  have hcont : ∀ (w4 : W), (PathsFit (wNode c.p base w4) c.i w4.top.rootKey c.p.fuel →
      ∀ key', keyWf key' = true →
        wGet c.p c.i base w4 key' = if [] ++ [cv] == key' then none else wGet c.p c.i base w key') →
      WriterWP fresh c w4 (fun _ w5 => PathsFit (wNode c.p base w5) c.i w5.top.rootKey c.p.fuel →
        ∀ key', keyWf key' = true →
        wGet c.p c.i base w5 key' = if [cv] == key' then none else wGet c.p c.i base w key') := by
    intro w4 h4
    unfold fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    intro hfit key' hkey'
    have := h4 hfit key' hkey'
    simp only [List.nil_append] at this
    exact this
  cases hk : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
  | false =>
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind]
    refine writerWP_ghOf_cached _ n c _ hlk3' _ (fun gh => ?_)
    refine writerWP_mono hcore ?_
    intro _ w4 h4
    unfold afterDelete
    simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte,
      writerWP_pure, Bool.not_false]
    exact hcont w4 h4
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_bind]
    unfold climb pathNode
    simp only [writerWP_bind, writerWP_read, writerWP_get]
    rw [show w3.path[0]? = some (none, w.top.rootKey) by rw [hp3, hp2]; rfl]
    simp only [writerWP_pure]
    rw [writerWP_getNode_known _ n c _ hlk3']
    simp only [hnl, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure, beq_self_eq_true,
      note, writerWP_modify, writerWP_bind]
    refine writerWP_mono (writerWP_appendDeleteKlong_rootR c base hvc cv n w _ hkey hsa hroot hnl hwfG
      htimesG hT hlinksAll htkfresh hr03 hlk3' hsrcw3 hne huniq) ?_
    intro _ w4 h4
    simp only [writerWP_pure, Bool.not_false, ↓reduceIte, writerWP_bind]
    exact hcont w4 h4

end SIS.Tree
