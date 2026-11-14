import SIS.Tree.KlongWellFormed
import SIS.Tree.IntervalSearchProof
import SIS.Tree.KeyWellFormed
import SIS.Tree.KlongRoundTrip

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The scalar compare-value restriction in the key predicate. -/
def CompareValueOK (c : Nat) : Prop := c < 2^62 ∧ c % 8 = 0

@[simp] theorem compareValueOK_zero : CompareValueOK 0 := by unfold CompareValueOK; decide +kernel

def KlongEncoded : Klong → Prop
  | .key c _ => CompareValueOK c
  | _ => True

def KlongsEncoded (ks : List Klong) : Prop := ∀ k ∈ ks, KlongEncoded k

def PairsEncoded (pairs : List (Nat × NodeId)) : Prop :=
  ∀ q ∈ pairs, CompareValueOK q.1

@[simp] theorem klongsEncoded_nil : KlongsEncoded [] := by simp [KlongsEncoded]

@[simp] theorem klongsEncoded_cons (k : Klong) (ks : List Klong) :
    KlongsEncoded (k :: ks) ↔ KlongEncoded k ∧ KlongsEncoded ks := by
  simp [KlongsEncoded]

@[simp] theorem klongsEncoded_append (ks qs : List Klong) :
    KlongsEncoded (ks ++ qs) ↔ KlongsEncoded ks ∧ KlongsEncoded qs := by
  simp [KlongsEncoded, List.mem_append, or_imp, forall_and]

theorem KlongsEncoded.subset {ks qs : List Klong} (hq : KlongsEncoded qs)
    (hs : ks ⊆ qs) : KlongsEncoded ks := fun k hk => hq k (hs hk)

theorem KlongsEncoded.take {ks : List Klong} (hk : KlongsEncoded ks) (i : Nat) :
    KlongsEncoded (ks.take i) := hk.subset (List.take_subset i ks)

theorem KlongsEncoded.drop {ks : List Klong} (hk : KlongsEncoded ks) (i : Nat) :
    KlongsEncoded (ks.drop i) := hk.subset (List.drop_subset i ks)

theorem KlongsEncoded.prefixAt {ks : List Klong} (hk : KlongsEncoded ks) (t : Time) :
    KlongsEncoded (prefixAt ks t) := hk.subset (List.takeWhile_subset _)

theorem KlongsEncoded.add (n : KNode) (t : Time) (k : Klong)
    (hn : KlongsEncoded n.ks) (hk : KlongEncoded k) : KlongsEncoded (n.add t k).ks := by
  unfold KNode.add
  split
  · split <;> simpa [hn, KlongEncoded] using hk
  · simpa [hn, KlongEncoded] using hk

theorem KlongsEncoded.set (ks : List Klong) (i : Nat) (k : Klong)
    (hs : KlongsEncoded ks) (hk : KlongEncoded k) : KlongsEncoded (ks.set i k) := by
  intro q hq
  rcases List.mem_or_eq_of_mem_set hq with hq | hq
  · exact hs q hq
  · subst q; exact hk

theorem klongsEncoded_map_shape (ks : List Klong) :
    KlongsEncoded (ks.map klongShape) ↔ KlongsEncoded ks := by
  constructor
  · intro h k hk
    have hh := h (klongShape k) (List.mem_map.mpr ⟨k, hk, rfl⟩)
    cases k <;> exact hh
  · intro h q hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have hh := h k hk
    cases k <;> exact hh

theorem klongsEncoded_of_shape (ks qs : List Klong)
    (he : ks.map klongShape = qs.map klongShape) (hq : KlongsEncoded qs) :
    KlongsEncoded ks := by
  apply (klongsEncoded_map_shape ks).mp
  rw [he]
  exact (klongsEncoded_map_shape qs).mpr hq

theorem KlongsEncoded.repoint (n : KNode) (i : Nat) (y : NodeId)
    (hn : KlongsEncoded n.ks) : KlongsEncoded (n.repoint i y).ks :=
  klongsEncoded_of_shape _ _ (n.repoint_shape i y) hn

theorem KlongsEncoded.replaceKlong (ks : List Klong) (t cv : Nat) (y : NodeId)
    (hn : KlongsEncoded ks) (out : List Klong)
    (hr : replaceKlong ks t cv y = .ok (some out)) : KlongsEncoded out :=
  klongsEncoded_of_shape _ _ (replaceKlong_shape ks t cv y out hr) hn

theorem KlongsEncoded.lastVersionGivenDel (n : KNode) (t : Time) (del : List Nat)
    (hn : KlongsEncoded n.ks) : KlongsEncoded (n.lastVersionGivenDel t del).ks := by
  intro k hk
  cases k with
  | time a => trivial
  | del bits => trivial
  | key c y =>
    have hcv : c ∈ ((n.lastVersionGivenDel t del).ks.filterMap (fun k => match k with
        | .key a _ => some a | _ => none)) := List.mem_filterMap.mpr ⟨_, hk, rfl⟩
    obtain ⟨z, i, hzip, _⟩ := (n.lastVersionGivenDel_has_key t del c).mp hcv
    exact hn (.key c z) (List.fst_mem_of_mem_zipIdx hzip)

theorem KlongsEncoded.live (n : KNode) (hn : KlongsEncoded n.ks) : PairsEncoded n.live := by
  intro q hq
  obtain ⟨y, i, hzip, _⟩ := (n.live_has_key q.1).mp (List.mem_map.mpr ⟨q, hq, rfl⟩)
  exact hn _ (List.fst_mem_of_mem_zipIdx hzip)

theorem KlongsEncoded.liveAt (n : KNode) (hn : KlongsEncoded n.ks) (t : Time) :
    PairsEncoded (n.liveAt t) := by
  rw [n.liveAt_eq_live_prefix]
  exact KlongsEncoded.live _ (hn.prefixAt t)

theorem KlongsEncoded.searchLte (n : KNode) (hn : KlongsEncoded n.ks)
    (t : Time) (target : Int) (fd : Found) (hf : n.searchLte t target = some fd) :
    CompareValueOK fd.c :=
  hn.liveAt n t _ ((n.searchLte_spec t target).1 fd hf).1

@[simp] theorem pairsEncoded_nil : PairsEncoded [] := by simp [PairsEncoded]

@[simp] theorem pairsEncoded_cons (q : Nat × NodeId) (pairs : List (Nat × NodeId)) :
    PairsEncoded (q :: pairs) ↔ CompareValueOK q.1 ∧ PairsEncoded pairs := by
  simp [PairsEncoded]

@[simp] theorem pairsEncoded_append (pairs qs : List (Nat × NodeId)) :
    PairsEncoded (pairs ++ qs) ↔ PairsEncoded pairs ∧ PairsEncoded qs := by
  simp [PairsEncoded, List.mem_append, or_imp, forall_and]

theorem PairsEncoded.subset {pairs qs : List (Nat × NodeId)} (hq : PairsEncoded qs)
    (hs : pairs ⊆ qs) : PairsEncoded pairs := fun q hq' => hq q (hs hq')

theorem PairsEncoded.take {pairs : List (Nat × NodeId)} (hp : PairsEncoded pairs) (i : Nat) :
    PairsEncoded (pairs.take i) := hp.subset (List.take_subset i pairs)

theorem PairsEncoded.drop {pairs : List (Nat × NodeId)} (hp : PairsEncoded pairs) (i : Nat) :
    PairsEncoded (pairs.drop i) := hp.subset (List.drop_subset i pairs)

theorem PairsEncoded.renameHead (pairs : List (Nat × NodeId)) (c : Nat)
    (hp : PairsEncoded pairs) (hc : CompareValueOK c) : PairsEncoded (renameHead c pairs) := by
  cases pairs with
  | nil => exact pairsEncoded_nil
  | cons q rest => exact pairsEncoded_cons _ _ |>.mpr ⟨hc, fun a ha => hp a (List.mem_cons_of_mem q ha)⟩

theorem PairsEncoded.headD (pairs : List (Nat × NodeId)) (hp : PairsEncoded pairs) :
    CompareValueOK ((pairs.head?.map Prod.fst).getD 0) := by
  cases pairs with
  | nil => exact compareValueOK_zero
  | cons q rest => exact hp q List.mem_cons_self

theorem KlongsEncoded.newKlongs (t : Time) (pairs : List (Nat × NodeId)) (hp : PairsEncoded pairs) :
    KlongsEncoded (newKlongs t pairs) := by
  change KlongsEncoded (.time t :: pairs.map (fun q => .key q.1 q.2))
  simp only [klongsEncoded_cons, KlongEncoded, true_and]
  intro k hk
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hk
  exact hp q hq

theorem keyWf_pairs_encoded (key : Key) (hw : keyWf key = true) :
    ∀ c ∈ key, CompareValueOK c := keyWf_segment_encoding key hw

theorem KlongsEncoded.headCv (ks : List Klong) (hs : KlongsEncoded ks) :
    CompareValueOK (match ks.head? with | some (.key c _) => c | _ => 0) := by
  cases ks with
  | nil => exact compareValueOK_zero
  | cons k rest =>
    cases k with
    | time t => exact compareValueOK_zero
    | del bits => exact compareValueOK_zero
    | key c y => exact hs _ List.mem_cons_self

theorem KlongsEncoded.renameFirstZero (ks : List Klong) (hs : KlongsEncoded ks) :
    KlongsEncoded (match ks with | .key _ y :: rest => .key 0 y :: rest | ks => ks) := by
  cases ks with
  | nil => exact hs
  | cons k rest =>
    cases k with
    | time t => exact hs
    | del bits => exact hs
    | key c y =>
      exact klongsEncoded_cons _ _ |>.mpr ⟨compareValueOK_zero, (klongsEncoded_cons _ _).mp hs |>.2⟩

theorem halves_encoded (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId))
    (hlast : KlongsEncoded last.ks) (hins : PairsEncoded ins) :
    KlongsEncoded (halves leaf t last ins).1.ks ∧
      KlongsEncoded (halves leaf t last ins).2.1.ks ∧
      CompareValueOK (halves leaf t last ins).2.2 := by
  let body := last.ks.drop 1
  let count := ((last.size - 1) / 2 + 1) - 1
  let first := body.take count
  let rest := body.drop count
  let sc := match rest.head? with | some (.key c _) => c | _ => 0
  let toSecond := match ins.head? with | some (c, _) => decide (sc ≤ c) | none => false
  let second := if leaf then rest else match rest with
    | .key _ y :: r => .key 0 y :: r
    | ks => ks
  let extra := ins.map (fun (c, y) =>
    if !leaf && toSecond && c == sc then Klong.key 0 y else Klong.key c y)
  have hf : KlongsEncoded first := (hlast.drop 1).take count
  have hr : KlongsEncoded rest := (hlast.drop 1).drop count
  have hc : CompareValueOK sc := hr.headCv rest
  have hs : KlongsEncoded second := by
    dsimp only [second]
    split
    · exact hr
    · cases hrst : rest with
      | nil => exact klongsEncoded_nil
      | cons k qs =>
        have hparts : KlongEncoded k ∧ KlongsEncoded qs := by simpa [hrst] using hr
        cases k with
        | key c y => exact (klongsEncoded_cons _ _).mpr ⟨compareValueOK_zero, hparts.2⟩
        | time t => exact (klongsEncoded_cons _ _).mpr hparts
        | del bits => exact (klongsEncoded_cons _ _).mpr hparts
  have he : KlongsEncoded extra := by
    intro k hk
    obtain ⟨⟨c,y⟩, hcy, rfl⟩ := List.mem_map.mp hk
    dsimp only
    split
    · exact compareValueOK_zero
    · exact hins _ hcy
  have hout : halves leaf t last ins =
      if toSecond then (⟨leaf, .time t :: first⟩, ⟨leaf, .time t :: second ++ extra⟩, sc)
      else (⟨leaf, .time t :: first ++ extra⟩, ⟨leaf, .time t :: second⟩, sc) := rfl
  rw [hout]
  cases ht : toSecond <;> simp [hf, hs, he, hc, KlongEncoded]

theorem mergeKlongs_encoded (inner : Bool) (cap cR : Nat) (lvL lvR : List (Nat × NodeId))
    (hL : PairsEncoded lvL) (hR : PairsEncoded lvR) (hcR : CompareValueOK cR) :
    PairsEncoded (mergeKlongs inner cap cR lvL lvR).1 ∧
      ∀ second, (mergeKlongs inner cap cR lvL lvR).2 = some second →
        PairsEncoded second.1 ∧ CompareValueOK second.2 := by
  have he : PairsEncoded (mergeList inner cR lvL lvR) := by
    unfold mergeList
    apply pairsEncoded_append _ _ |>.mpr
    refine ⟨hL, ?_⟩
    split
    · exact hR.renameHead lvR cR hcR
    · exact hR
  unfold mergeKlongs splitMerged
  split
  · exact ⟨he, by intro second hs; cases hs⟩
  · refine ⟨he.take _, ?_⟩
    intro second hs
    have heq := Option.some.inj hs
    subst second
    refine ⟨?_, (he.drop _).headD _⟩
    split
    · exact (he.drop _).renameHead _ 0 compareValueOK_zero
    · exact he.drop _

theorem KlongsEncoded.insertSorted (ks : List Klong) (cv : Nat) (y : NodeId)
    (hk : KlongsEncoded ks) (hc : CompareValueOK cv) : KlongsEncoded (SIS.Tree.insertSorted ks cv y) := by
  induction ks with
  | nil => simpa [SIS.Tree.insertSorted, KlongEncoded] using hc
  | cons k rest ih =>
    have hh := (klongsEncoded_cons _ _).mp hk
    cases k with
    | time t => simpa [SIS.Tree.insertSorted, KlongEncoded] using ih hh.2
    | del bits => simpa [SIS.Tree.insertSorted, KlongEncoded] using ih hh.2
    | key c z =>
      simp only [SIS.Tree.insertSorted]
      split
      · simp [hc, show CompareValueOK c from hh.1, hh.2, KlongEncoded]
      · exact (klongsEncoded_cons _ _).mpr ⟨hh.1, ih hh.2⟩

def ValueEncoded : BVal → Prop
  | .key c _ => CompareValueOK c
  | _ => True

def HistoryEncoded (es : History BVal) : Prop := ∀ e ∈ es, ValueEncoded e.val

@[simp] theorem historyEncoded_nil : HistoryEncoded [] := by simp [HistoryEncoded]

@[simp] theorem historyEncoded_append (es fs : History BVal) :
    HistoryEncoded (es ++ fs) ↔ HistoryEncoded es ∧ HistoryEncoded fs := by
  simp [HistoryEncoded, List.mem_append, or_imp, forall_and]

theorem parseKlongEntry_encoded (acc : KlongParseState) (e : Entry BVal)
    (ha : KlongsEncoded acc.1) (he : ValueEncoded e.val) :
    KlongsEncoded (parseKlongEntry acc e).1 := by
  have hk : KlongsEncoded (if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]) := by
    split <;> simp [ha, KlongEncoded]
  unfold parseKlongEntry
  cases hv : e.val with
  | key c y => simpa [hv, KlongEncoded, ValueEncoded] using And.intro hk he
  | del cs =>
    cases cs with
    | nil => exact hk
    | cons c cs => simpa [hv, KlongEncoded] using hk
  | rootKey y => exact hk
  | skip j z => exact hk
  | top z => exact hk
  | data h => exact hk

theorem klongsOf_encoded (es : History BVal) (he : HistoryEncoded es) :
    KlongsEncoded (klongsOf es) := by
  rw [klongsOf_eq_parse]
  unfold parseKlongEntries
  have hfold : ∀ (qs : History BVal) (acc : KlongParseState),
      HistoryEncoded qs → KlongsEncoded acc.1 →
        KlongsEncoded (qs.foldl parseKlongEntry acc).1 := by
    intro qs
    induction qs with
    | nil => intro acc _ ha; exact ha
    | cons e qs ih =>
      intro acc hq ha
      exact ih _ (fun q hmem => hq q (List.mem_cons_of_mem e hmem))
        (parseKlongEntry_encoded acc e ha (hq e List.mem_cons_self))
  exact hfold es ([], none, []) he klongsEncoded_nil

theorem encodeKlong_encoded (full : List Klong) (acc : KlongEntryState) (k : Klong)
    (ha : HistoryEncoded acc.1) (hk : KlongEncoded k) :
    HistoryEncoded (encodeKlong full acc k).1 := by
  cases k with
  | time t =>
    simp only [encodeKlong]
    split
    · exact ha
    · exact historyEncoded_append _ _ |>.mpr ⟨ha, by simp [HistoryEncoded, ValueEncoded, marker]⟩
  | key c y =>
    exact historyEncoded_append _ _ |>.mpr ⟨ha, by simpa [HistoryEncoded, ValueEncoded, KlongEncoded] using hk⟩
  | del bits =>
    exact historyEncoded_append _ _ |>.mpr ⟨ha, by simp [HistoryEncoded, ValueEncoded]⟩

theorem entriesOf_encoded (ks : List Klong) (hk : KlongsEncoded ks) :
    HistoryEncoded (entriesOf ks) := by
  rw [entriesOf_eq_encode]
  unfold finishKlongEntries
  have hfold : ∀ (qs : List Klong) (acc : KlongEntryState),
      KlongsEncoded qs → HistoryEncoded acc.1 →
        HistoryEncoded (qs.foldl (encodeKlong ks) acc).1 := by
    intro qs
    induction qs with
    | nil => intro acc _ ha; exact ha
    | cons k qs ih =>
      intro acc hq ha
      have hparts := (klongsEncoded_cons _ _).mp hq
      exact ih _ hparts.2 (encodeKlong_encoded ks acc k ha hparts.1)
  have hf := hfold ks ([], 0, [], true) hk historyEncoded_nil
  split
  · exact hf
  · exact historyEncoded_append _ _ |>.mpr ⟨hf, by simp [HistoryEncoded, ValueEncoded, marker]⟩

theorem encoded_searchLte {n : KNode} {t : Time} {target : Int} {fd : Found}
    (hf : n.searchLte t target = some fd) (hn : KlongsEncoded n.ks) : CompareValueOK fd.c :=
  KlongsEncoded.searchLte n hn t target fd hf

theorem encoded_cv {n : KNode} {i cv : Nat}
    (hc : n.cv? i = some cv) (hn : KlongsEncoded n.ks) : CompareValueOK cv := by
  unfold KNode.cv? at hc
  cases hk : n.ks[i]? with
  | none => simp [hk] at hc
  | some k =>
    have hg := hn k (List.mem_of_getElem? hk)
    cases k with
    | time t => simp [hk] at hc
    | del bits => simp [hk] at hc
    | key c y =>
      have he : c = cv := by simpa [hk] using hc
      subst cv
      exact hg

theorem encoded_searchEq (n : KNode) (t : Time) (cv : Nat) (fd : Found)
    (hf : n.searchEq t cv = some fd) (hn : KlongsEncoded n.ks) : CompareValueOK fd.c := by
  let step := fun (acc : Option Time × List Nat × Option Found) (q : Klong × Nat) =>
    if acc.2.1.contains q.2 then acc else match q.1 with
    | .time x => (some x, acc.2.1, acc.2.2)
    | .key c y => if c == cv then (acc.1, acc.2.1, some ⟨cv, q.2, acc.1.getD 0, y⟩) else acc
    | .del bits => (acc.1, bits, match acc.2.2 with
      | some f => if bits.contains f.idx then none else some f
      | none => none)
  have hfold : ∀ (xs : List (Klong × Nat)) (acc : Option Time × List Nat × Option Found),
      (∀ q ∈ xs, KlongEncoded q.1) →
      (∀ f, acc.2.2 = some f → CompareValueOK f.c) →
      ∀ f, (xs.foldl step acc).2.2 = some f → CompareValueOK f.c := by
    intro xs
    induction xs with
    | nil => intro acc _ ha; exact ha
    | cons q qs ih =>
      intro acc hq ha
      apply ih (step acc q) (fun a hm => hq a (List.mem_cons_of_mem q hm))
      intro f hff
      have hkey := hq q List.mem_cons_self
      rcases q with ⟨k, i⟩
      dsimp only [step] at hff
      split at hff
      · exact ha f hff
      · cases k with
        | time x => exact ha f hff
        | key c y =>
          simp only at hff
          split at hff
          · rename_i hcc
            have hc : c = cv := by simpa using hcc
            have he : (⟨cv, i, acc.1.getD 0, y⟩ : Found) = f := by simpa using hff
            subst f
            subst cv
            exact hkey
          · exact ha f hff
        | del bits =>
          cases hh : acc.2.2 with
          | none => simp [hh] at hff
          | some found =>
            simp only [hh] at hff
            split at hff
            · cases hff
            · have he : found = f := Option.some.inj hff
              subst f
              exact ha found hh
  exact hfold (prefixAt n.ks t).zipIdx (none, [], none)
    (fun q hq => hn.prefixAt t q.1 (List.fst_mem_of_mem_zipIdx hq))
    (by intro f h; cases h) fd hf

theorem encoded_merge_second {inner : Bool} {cap cR : Nat} {left right : List (Nat × NodeId)}
    {second : List (Nat × NodeId) × Nat}
    (hs : (mergeKlongs inner cap cR left right).2 = some second)
    (hL : PairsEncoded left) (hR : PairsEncoded right) (hcR : CompareValueOK cR) :
    PairsEncoded second.1 ∧ CompareValueOK second.2 :=
  (mergeKlongs_encoded inner cap cR left right hL hR hcR).2 second hs

theorem encoded_tail_eq {ks rest : List Klong} {k : Klong}
    (he : ks = k :: rest) (hk : KlongsEncoded ks) : KlongsEncoded rest := by
  rw [he] at hk
  exact (klongsEncoded_cons _ _).mp hk |>.2

theorem encoded_head_eq {ks rest : List Klong} {k : Klong}
    (he : ks = k :: rest) (hk : KlongsEncoded ks) : KlongEncoded k := by
  rw [he] at hk
  exact (klongsEncoded_cons _ _).mp hk |>.1

theorem encoded_tail_two_eq {ks rest : List Klong} {k l : Klong}
    (he : ks = k :: l :: rest) (hk : KlongsEncoded ks) : KlongsEncoded rest := by
  rw [he] at hk
  exact (klongsEncoded_cons _ _).mp ((klongsEncoded_cons _ _).mp hk).2 |>.2

theorem encoded_halves_first (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId))
    (hlast : KlongsEncoded last.ks) (hins : PairsEncoded ins) :
    KlongsEncoded (halves leaf t last ins).1.ks := (halves_encoded leaf t last ins hlast hins).1

theorem encoded_halves_second (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId))
    (hlast : KlongsEncoded last.ks) (hins : PairsEncoded ins) :
    KlongsEncoded (halves leaf t last ins).2.1.ks := (halves_encoded leaf t last ins hlast hins).2.1

theorem encoded_halves_cv (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId))
    (hlast : KlongsEncoded last.ks) (hins : PairsEncoded ins) :
    CompareValueOK (halves leaf t last ins).2.2 := (halves_encoded leaf t last ins hlast hins).2.2

theorem KlongsEncoded.toPrev (n : KNode) (t : Time) (hn : KlongsEncoded n.ks) :
    KlongsEncoded (n.toPrev t).ks := hn.prefixAt t

theorem KlongsEncoded.lastVersion (n : KNode) (t : Time) (hn : KlongsEncoded n.ks) :
    KlongsEncoded (n.lastVersion t).ks := hn.lastVersionGivenDel n t n.lastBitmap

theorem encoded_merge_first (inner : Bool) (cap cR : Nat) (left right : List (Nat × NodeId))
    (hL : PairsEncoded left) (hR : PairsEncoded right) (hcR : CompareValueOK cR) :
    PairsEncoded (mergeKlongs inner cap cR left right).1 :=
  (mergeKlongs_encoded inner cap cR left right hL hR hcR).1

theorem encoded_merge_second_list {inner : Bool} {cap cR : Nat} {left right ks : List (Nat × NodeId)}
    {cv : Nat} (hs : (mergeKlongs inner cap cR left right).2 = some (ks, cv))
    (hL : PairsEncoded left) (hR : PairsEncoded right) (hcR : CompareValueOK cR) :
    PairsEncoded ks := (encoded_merge_second hs hL hR hcR).1

theorem encoded_merge_second_value {inner : Bool} {cap cR : Nat} {left right ks : List (Nat × NodeId)}
    {cv : Nat} (hs : (mergeKlongs inner cap cR left right).2 = some (ks, cv))
    (hL : PairsEncoded left) (hR : PairsEncoded right) (hcR : CompareValueOK cR) :
    CompareValueOK cv := (encoded_merge_second hs hL hR hcR).2

theorem encoded_replacedKlong {ks : List Klong} {t cv : Nat} {y : NodeId} {out : List Klong}
    (hr : replaceKlong ks t cv y = .ok (some out)) (hn : KlongsEncoded ks) : KlongsEncoded out :=
  KlongsEncoded.replaceKlong ks t cv y hn out hr

def MergeOutputEncoded : Option (NodeId × Nat) → Prop
  | none => True
  | some q => CompareValueOK q.2

theorem encoded_mergeOutput {out : Option (NodeId × Nat)} {q : NodeId × Nat}
    (he : out = some q) (ho : MergeOutputEncoded out) : CompareValueOK q.2 := by
  rw [he] at ho
  exact ho

end SIS.Tree
