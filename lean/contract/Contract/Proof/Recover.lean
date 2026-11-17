/-
The contract package (bergdb 030-14): the proofs for the reads from the
model's view (Recover.lean).

* The live klongs of the entries (`live_klongsOfE`): for klongs that meet W1
  to W5, the klongs that their entries read as (`klongsOfE`) have the same
  live klongs. With BridgeMap.lean's fold of `blive` (`stOf_spec`).
* Reads that agree (`Good.transfer`, `get_eq_of_agree`, `scan_eq_of_agree`):
  a tree whose nodes, from the space root down through the live klongs, agree
  with those of a sound tree (the same level, kind and live klongs, or the
  same value) reads as that tree.
-/
import Mathlib.Tactic
import Contract.Recover
import Contract.Proof.BridgeMap
import Contract.Proof.Get
import Contract.Proof.Scan

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive setAssoc)

/-! ## The live klongs of the entries -/

theorem foldl_fix {α β : Type} (f : β → α → β) (b : β) :
    ∀ l : List α, (∀ a ∈ l, f b a = b) → l.foldl f b = b
  | [], _ => rfl
  | a :: r, h => by
    simp only [List.foldl_cons]
    rw [h a List.mem_cons_self]
    exact foldl_fix f b r (fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))

/-- The fold of the live klongs is the first part of `blive`'s fold. -/
theorem foldl_liveStep : ∀ (hist : History BVal) (m : List (Nat × Option Nat)) (a b : Option Nat),
    hist.foldl liveStep m = (hist.foldl SIS.Check.bstep (m, a, b)).1
  | [], _, _, _ => rfl
  | e :: r, m, a, b => by
    simp only [List.foldl_cons]
    obtain ⟨t, v⟩ := e
    cases v with
    | key c y => exact foldl_liveStep r _ a b
    | del cs => exact foldl_liveStep r _ a b
    | rootKey y => exact foldl_liveStep r _ _ _
    | skip j z => exact foldl_liveStep r _ _ _
    | top z => exact foldl_liveStep r _ _ _
    | data v => exact foldl_liveStep r _ _ _

theorem liveOfE_entriesOf (ks : List Klong) : liveOfE (entriesOf ks) = (stOf ks).1 :=
  foldl_liveStep _ [] none none

/-- The fold of the live klongs of the entries of well-formed klongs, with W5,
gives the node's live klongs. -/
theorem lookup_liveOfE (ks : List Klong) (hwf : klongsWf ks = true) (hfull : fullOk ks = true)
    (c : Nat) : ((liveOfE (entriesOf ks)).lookup c).bind id = (live ks).lookup c := by
  obtain ⟨_, _, _, s4⟩ := stOf_spec ks (wf5_of ks hwf hfull)
  rw [liveOfE_entriesOf, s4 c, lookup_live ks hwf c]
  cases (kc c ks.zipIdx).getLast? with
  | none => rfl
  | some a =>
    by_cases hd : a.1 ∈ lastBitmap ks <;> simp [hd, Option.filter]

theorem liveOfE_nodup (ks : List Klong) (hwf : klongsWf ks = true) (hfull : fullOk ks = true) :
    ((liveOfE (entriesOf ks)).map (·.1)).Nodup := by
  rw [liveOfE_entriesOf]
  exact (stOf_spec ks (wf5_of ks hwf hfull)).2.2.1

/-- The key klongs of an association list. -/
abbrev keysOf (m : List (Nat × Option Nat)) : List Klong :=
  m.filterMap (fun cv => cv.2.map (Klong.key cv.1))

theorem mem_keysOf {m : List (Nat × Option Nat)} {k : Klong} (h : k ∈ keysOf m) :
    ∃ c y, k = .key c y := by
  simp only [keysOf, List.mem_filterMap] at h
  obtain ⟨⟨c, v⟩, _, hv⟩ := h
  cases v with
  | none => simp at hv
  | some y =>
    simp only [Option.map_some, Option.some.injEq] at hv
    exact ⟨c, y, hv.symm⟩

theorem klongsOfE_eq (hist : History BVal) : klongsOfE hist = .time 0 :: keysOf (liveOfE hist) :=
  rfl

theorem lastBitmap_klongsOfE (hist : History BVal) : lastBitmap (klongsOfE hist) = [] := by
  rw [klongsOfE_eq]
  unfold lastBitmap
  simp only [List.foldl_cons]
  apply foldl_fix
  intro k hk
  obtain ⟨c, y, rfl⟩ := mem_keysOf hk
  rfl

/-- The klongs of the entries are well formed. -/
theorem klongsOfE_wf (hist : History BVal) : klongsWf (klongsOfE hist) = true := by
  rw [klongsOfE_eq]
  simp only [klongsWf, Bool.and_eq_true]
  constructor
  · simp only [timesOk, List.foldl_cons, Bool.true_and]
    rw [foldl_fix]
    intro k hk
    obtain ⟨c, y, rfl⟩ := mem_keysOf hk
    rfl
  · unfold bitmapsOk
    rw [foldl_fix]
    intro ki hki
    have hk : ki.1 ∈ Klong.time 0 :: keysOf (liveOfE hist) := List.fst_mem_of_mem_zipIdx hki
    rcases List.mem_cons.mp hk with h0 | h0
    · rw [h0]; rfl
    · obtain ⟨c, y, hcy⟩ := mem_keysOf h0
      rw [hcy]; rfl

/-- The pointees of the key klongs of compare value c. -/
def ptrsC (c : Nat) (l : List Klong) : List NodeId :=
  l.filterMap (fun k => match k with
    | .key c' y => if c' = c then some y else none
    | _ => none)

theorem kc_map_snd (c : Nat) : ∀ (l : List Klong) (n : Nat),
    (kc c (l.zipIdx n)).map (·.2) = ptrsC c l
  | [], _ => rfl
  | k :: r, n => by
    have ih := kc_map_snd c r (n + 1)
    simp only [kc, ptrsC, List.zipIdx_cons, List.filterMap_cons] at ih ⊢
    cases k with
    | key c' y =>
      by_cases h : c' = c
      · simp only [h, ite_true, List.map_cons]
        rw [ih]
      · simp only [h, ite_false]
        exact ih
    | time t => exact ih
    | del b => exact ih

theorem ptrsC_keysOf (c : Nat) : ∀ m : List (Nat × Option Nat),
    ptrsC c (keysOf m) = m.filterMap (fun cv => if cv.1 = c then cv.2 else none)
  | [] => rfl
  | (c', v) :: r => by
    have ih := ptrsC_keysOf c r
    cases v with
    | none =>
      simp only [keysOf, ptrsC, List.filterMap_cons, Option.map_none] at ih ⊢
      rw [ih]
      by_cases h : c' = c <;> simp [h]
    | some y =>
      simp only [keysOf, ptrsC, List.filterMap_cons, Option.map_some] at ih ⊢
      rw [ih]

theorem getLast_filterMap_lookup (c : Nat) : ∀ m : List (Nat × Option Nat), (m.map (·.1)).Nodup →
    (m.filterMap (fun cv => if cv.1 = c then cv.2 else none)).getLast? = (m.lookup c).bind id
  | [], _ => rfl
  | (c', v) :: r, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [List.filterMap_cons, List.lookup_cons]
    by_cases h : c' = c
    · subst h
      have hr : r.filterMap (fun cv => if cv.1 = c' then cv.2 else none) = [] := by
        rw [List.filterMap_eq_nil_iff]
        intro cv hcv
        have : cv.1 ≠ c' := fun he => hn.1 (List.mem_map.mpr ⟨cv, hcv, he⟩)
        simp [this]
      simp only [ite_true, beq_self_eq_true, hr]
      cases v <;> rfl
    · have hb : (c == c') = false := by simp; omega
      simp only [h, ite_false, hb]
      exact getLast_filterMap_lookup c r hn.2

/-- The live klongs of the klongs of an association list with distinct
compare values: for each compare value, its pointee, if it has one. -/
theorem lookup_live_keysOf (m : List (Nat × Option Nat)) (hn : (m.map (·.1)).Nodup) (c : Nat) :
    (live (.time 0 :: keysOf m)).lookup c = (m.lookup c).bind id := by
  have h1 := lookup_liveWith (lastBitmap (.time 0 :: keysOf m)) c (Klong.time 0 :: keysOf m).zipIdx
    [] List.Pairwise.nil
  have hlb : lastBitmap (.time 0 :: keysOf m) = [] := by
    have := lastBitmap_klongsOfE []
    unfold lastBitmap at this ⊢
    simp only [List.foldl_cons]
    apply foldl_fix
    intro k hk
    obtain ⟨c, y, rfl⟩ := mem_keysOf hk
    rfl
  have h2 : (live (.time 0 :: keysOf m)).lookup c =
      match ((kc c (Klong.time 0 :: keysOf m).zipIdx).filter
        (fun a => !(lastBitmap (.time 0 :: keysOf m)).contains a.1)).getLast? with
      | some a => some a.2
      | none => none := h1
  rw [h2, hlb]
  simp only [List.contains_nil, Bool.not_false, List.filter_true]
  have h3 : (match (kc c (Klong.time 0 :: keysOf m).zipIdx).getLast? with
      | some a => some a.2
      | none => none) = ((kc c (Klong.time 0 :: keysOf m).zipIdx).map (·.2)).getLast? := by
    rw [List.getLast?_map]
    cases (kc c (Klong.time 0 :: keysOf m).zipIdx).getLast? <;> rfl
  rw [h3, kc_map_snd]
  have h4 : ptrsC c (.time 0 :: keysOf m) = ptrsC c (keysOf m) := rfl
  rw [h4, ptrsC_keysOf, getLast_filterMap_lookup c m hn]

/-- Two lists in strictly increasing order of their compare values, with the
same pairs, are one. -/
theorem eq_of_mem_sorted : ∀ {m1 m2 : List (Nat × NodeId)}, m1.Pairwise CvLt →
    m2.Pairwise CvLt → (∀ a, a ∈ m1 ↔ a ∈ m2) → m1 = m2
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr List.mem_cons_self) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp List.mem_cons_self) (by simp)
  | a :: r1, b :: r2, h1, h2, h => by
    rw [List.pairwise_cons] at h1 h2
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp List.mem_cons_self) with hab | ha
      · exact hab
      · rcases List.mem_cons.mp ((h b).mpr List.mem_cons_self) with hba | hb
        · exact hba.symm
        · have := h1.1 b hb
          have := h2.1 a ha
          unfold CvLt at *
          omega
    subst hab
    rw [eq_of_mem_sorted h1.2 h2.2 ?_]
    intro x
    constructor
    · intro hx
      rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with hxa | hx'
      · subst hxa
        have := h1.1 x hx
        unfold CvLt at this; omega
      · exact hx'
    · intro hx
      rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with hxa | hx'
      · subst hxa
        have := h2.1 x hx
        unfold CvLt at this; omega
      · exact hx'

theorem eq_of_lookup {m1 m2 : List (Nat × NodeId)} (h1 : m1.Pairwise CvLt)
    (h2 : m2.Pairwise CvLt) (h : ∀ c, m1.lookup c = m2.lookup c) : m1 = m2 := by
  apply eq_of_mem_sorted h1 h2
  rintro ⟨c, y⟩
  rw [← lookup_iff_mem h1, ← lookup_iff_mem h2, h c]

/-- The map keeps the live klongs: the klongs that the entries of well-formed
klongs with W5 read as have the same live klongs, in the same order. -/
theorem live_klongsOfE (ks : List Klong) (hwf : klongsWf ks = true) (hfull : fullOk ks = true) :
    live (klongsOfE (entriesOf ks)) = live ks := by
  apply eq_of_lookup (live_sorted _) (live_sorted _)
  intro c
  rw [klongsOfE_eq, lookup_live_keysOf _ (liveOfE_nodup ks hwf hfull), lookup_liveOfE ks hwf hfull]

/-! ## Reads that agree -/

/-- Two objects read alike: two key nodes with the same level, kind and live
klongs, the second one's klongs well formed; or two values that are one. -/
def ObjAgree : Obj → Obj → Prop
  | .val v, .val v' => v' = v
  | .key n, .key n' =>
    n'.level = n.level ∧ n'.leaf = n.leaf ∧ live n'.ks = live n.ks ∧ klongsWf n'.ks = true
  | _, _ => False

/-- A tree s' that agrees with a sound tree s on a set R of nodes that holds
the live pointees of its key nodes is sound where s is, and holds what s
holds. -/
theorem Good.transfer {s s' : Tree} (R : NodeId → Prop)
    (hR : ∀ x n c y, R x → s.obj x = some (.key n) → (c, y) ∈ live n.ks → R y)
    (hag : ∀ x o, R x → s.obj x = some o → ∃ o', s'.obj x = some o' ∧ ObjAgree o o')
    {x : NodeId} {lo : Nat} {hi : Option Nat} (hG : Good s x lo hi) :
    R x → Good s' x lo hi ∧ L s' x = L s x := by
  induction hG with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro hRx
    obtain ⟨o', ho', hagx⟩ := hag x _ hRx hobj
    cases o' with
    | val v => exact absurd hagx (by simp [ObjAgree])
    | key n' =>
      obtain ⟨hlev, hleaf, hlive, hwf'⟩ := hagx
      have hRy : ∀ c y, (c, y) ∈ live n.ks → R y := fun c y hm => hR x n c y hRx hobj hm
      have hval' : ∀ c y, n.leaf = true → (c, y) ∈ live n.ks → isLong c = false →
          s'.obj y = s.obj y := by
        intro c y hl hm hs
        obtain ⟨v, hv⟩ := hval hl c y hm hs
        obtain ⟨o2, ho2, hag2⟩ := hag y _ (hRy c y hm) hv
        cases o2 with
        | val v2 => rw [ho2, hv]; simp only [ObjAgree] at hag2; rw [hag2]
        | key m2 => exact absurd hag2 (by simp [ObjAgree])
      have hG' : Good s' x lo hi := by
        refine Good.mk x lo hi n' ho' hwf' ?_ ?_ ?_ ?_ ?_ ?_
        · intro c y hm; rw [hlive] at hm; exact hhi c y hm
        · intro hl c y hm; rw [hlive] at hm; rw [hleaf] at hl; exact hlo hl c y hm
        · intro hl c y hm hs
          rw [hlive] at hm; rw [hleaf] at hl
          rw [hval' c y hl hm hs]
          exact hval hl c y hm hs
        · intro c y hm hk
          rw [hlive] at hm; rw [hleaf] at hk
          obtain ⟨m, hm1, hm2, hm3⟩ := hkey c y hm hk
          obtain ⟨o2, ho2, hag2⟩ := hag y _ (hRy c y hm) hm1
          cases o2 with
          | val v2 => exact absurd hag2 (by simp [ObjAgree])
          | key m2 =>
            obtain ⟨h1, _, h3, _⟩ := hag2
            exact ⟨m2, ho2, by rw [h1, hlev]; exact hm2, by rw [h3]; exact hm3⟩
        · intro hl c y hm hs
          rw [hlive] at hm; rw [hleaf] at hl
          exact (ihseg hl c y hm hs (hRy c y hm)).1
        · intro hl pre c y post he
          rw [hlive] at he; rw [hleaf] at hl
          have hm : (c, y) ∈ live n.ks := by rw [he]; simp
          exact (ihkid hl pre c y post he (hRy c y hm)).1
      refine ⟨hG', ?_⟩
      rw [hG'.L_eq ho', (Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid).L_eq hobj,
        hlive, hleaf]
      apply List.flatMap_congr
      rintro ⟨c, y⟩ hm
      simp only
      unfold klongList
      cases hl : n.leaf with
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        obtain ⟨pre, post, he⟩ := List.append_of_mem hm
        exact (ihkid hl pre c y post he (hRy c y hm)).2
      | true =>
        simp only [ite_true]
        cases hs : isLong c with
        | true =>
          simp only [ite_true]
          rw [(ihseg hl c y hm hs (hRy c y hm)).2]
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          rw [hval' c y hl hm hs]

/-- A get on a sound tree: what its space root holds for the key. -/
theorem get_of_good {s : Tree} {r : NodeId} (hr : s.root = some r) (hG : Good s r 0 none)
    (k : Key) : get s k = (L s r).lookup k := by
  unfold get
  rw [hr]
  simp only
  apply Option.ext
  intro v
  rw [hG.getGo_iff _ (le_refl _)]
  show (k, v) ∈ L s r ↔ List.lookup k (L s r) = some v
  rw [lookup_iff_mem hG.sorted]

/-- A scan on a sound tree: the keys and values that its space root holds,
in the scan's range and order, the first `limit`. -/
theorem scan_of_good {s : Tree} {r : NodeId} (hr : s.root = some r) (hG : Good s r 0 none)
    (req : ScanReq) (hreq : req.wf = true) (limit : Nat) :
    scan s req limit = refScan (L s r) req limit := by
  obtain ⟨n, ho⟩ : ∃ n, s.obj r = some (.key n) := by
    cases hG with
    | mk _ _ _ n hobj _ _ _ _ _ _ _ => exact ⟨n, hobj⟩
  unfold scan
  rw [hr]
  simp only
  have hend : req.endKey ≠ none → req.forward = true := by
    intro he
    simp only [ScanReq.wf, Bool.and_eq_true] at hreq
    cases hk : req.endKey with
    | none => exact absurd hk he
    | some e => rw [hk] at hreq; simp only [Bool.and_eq_true] at hreq; exact hreq.2.2
  obtain ⟨hpath, hstart⟩ := setup_start hG req hreq ho
  rw [scanGo_spec hG req hend _ (by omega) limit _ (Or.inr hpath), hstart]
  show _ = refScan (L s r) req limit
  unfold refScan
  have hf : ((L s r).filter (fun kv => inRange req kv.1)) =
      ((L s r).filter (fun kv => inStart req kv.1)).filter (fun kv => inEnd req kv.1) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro kv _
    rw [inRange_eq, Bool.and_comm]
  simp only [hf]
  cases req.forward with
  | true => simp [dir]
  | false => simp [dir, List.filter_reverse]

/-- Two trees with one space root, the first sound, the second agreeing with
it on a set of nodes that holds the root and the live pointees of its key
nodes: every get gives the same. -/
theorem get_eq_of_agree {s s' : Tree} {r : NodeId} (hr : s.root = some r) (hr' : s'.root = some r)
    (hG : Good s r 0 none) (R : NodeId → Prop)
    (hR : ∀ x n c y, R x → s.obj x = some (.key n) → (c, y) ∈ live n.ks → R y)
    (hag : ∀ x o, R x → s.obj x = some o → ∃ o', s'.obj x = some o' ∧ ObjAgree o o')
    (hRr : R r) (k : Key) : get s' k = get s k := by
  obtain ⟨hG', hL⟩ := hG.transfer R hR hag hRr
  rw [get_of_good hr' hG', get_of_good hr hG, hL]

/-- And every scan. -/
theorem scan_eq_of_agree {s s' : Tree} {r : NodeId} (hr : s.root = some r)
    (hr' : s'.root = some r) (hG : Good s r 0 none) (R : NodeId → Prop)
    (hR : ∀ x n c y, R x → s.obj x = some (.key n) → (c, y) ∈ live n.ks → R y)
    (hag : ∀ x o, R x → s.obj x = some o → ∃ o', s'.obj x = some o' ∧ ObjAgree o o')
    (hRr : R r) (req : ScanReq) (hreq : req.wf = true) (limit : Nat) :
    scan s' req limit = scan s req limit := by
  obtain ⟨hG', hL⟩ := hG.transfer R hR hag hRr
  rw [scan_of_good hr' hG' req hreq, scan_of_good hr hG req hreq, hL]

end Contract
