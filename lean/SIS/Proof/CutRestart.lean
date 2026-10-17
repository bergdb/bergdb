/-
Proofs about reclaim, part 9 (bergdb item 001, WP R5): runs that restart from
cut streams. A cut of a cut, and of a stream with a record appended; on a
state related to the run's (`CutRel`: the run's stream cut at m, its D, its
nodes for the lookups from f on and for D), a transaction appends the run's
record and keeps the relation (`step_congr_cut`).
-/
import SIS.Proof.CutRecover
import SIS.Proof.Fresh

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem Record.cut_cut (R : Record V T) : R.cut.cut = R.cut := by
  unfold Record.cut
  simp only [List.map_map]
  rfl

theorem cutStream_zero (S : Stream V T) : cutStream 0 S = S := by
  apply List.ext_getElem?
  intro r
  rw [cutStream_getElem?]
  cases S[r]? with
  | none => rfl
  | some R => simp

theorem cutStream_cutStream (c m : Nat) (S : Stream V T) :
    cutStream c (cutStream m S) = cutStream (max c m) S := by
  apply List.ext_getElem?
  intro r
  rw [cutStream_getElem?, cutStream_getElem?, cutStream_getElem?]
  cases S[r]? with
  | none => rfl
  | some R =>
    simp only [Option.map_some]
    by_cases h1 : r < m
    · by_cases h2 : r < c
      · simp only [h1, h2, show r < max c m by omega, ↓reduceIte, Record.cut_cut]
      · simp only [h1, h2, show r < max c m by omega, ↓reduceIte]
    · by_cases h2 : r < c
      · simp only [h1, h2, show r < max c m by omega, ↓reduceIte]
      · simp only [h1, h2, show ¬ r < max c m by omega, ↓reduceIte]

theorem cutStream_append_one {m : Nat} {S : Stream V T} (h : m ≤ S.length) (R : Record V T) :
    cutStream m (S ++ [R]) = cutStream m S ++ [R] := by
  apply List.ext_getElem?
  intro r
  rw [cutStream_getElem?]
  rcases Nat.lt_or_ge r S.length with hr | hr
  · rw [List.getElem?_append_left hr, List.getElem?_append_left (by rw [cutStream_length]; exact hr),
      cutStream_getElem?]
  · rw [List.getElem?_append_right hr, List.getElem?_append_right (by rw [cutStream_length]; exact hr),
      cutStream_length]
    cases hR : [R][r - S.length]? with
    | none => rfl
    | some R' => simp only [Option.map_some, show ¬ r < m by omega, ↓reduceIte]

theorem cutStream_building {m : Nat} {S : Stream V T} (h : m ≤ S.length) (vs : List (Version V)) :
    (cutStream m S).building vs = cutStream m (S.building vs) := by
  unfold Stream.building
  rw [cutStream_append_one h]

theorem lv_cut_recNo_map (m : Nat) (S : Stream V T) (z : NodeId) :
    ((cutStream m S).lv z).map (fun v => (z, v.recNo)) = (S.lv z).map (fun v => (z, v.recNo)) := by
  have := lv_cut_recNo m S z
  cases h1 : (cutStream m S).lv z with
  | none =>
    rw [h1] at this
    cases h2 : S.lv z with
    | none => rfl
    | some w => rw [h2] at this; simp at this
  | some w =>
    rw [h1] at this
    cases h2 : S.lv z with
    | none => rw [h2] at this; simp at this
    | some w' =>
      rw [h2] at this
      simp only [Option.map_some, Option.some.injEq] at this ⊢
      rw [this]

/-- A version written on a stream cut at m names the records it names on the
whole stream. -/
theorem mkVersion_cut {m : Nat} {S : Stream V T} (h : m ≤ S.length) (sp : Spec V T)
    (vs : List (Version V)) (i : Nat) (x : NodeId) (n : Node V) :
    mkVersion sp ((cutStream m S).building vs) i x n = mkVersion sp (S.building vs) i x n := by
  unfold mkVersion
  rw [cutStream_building h]
  congr 2
  funext y
  have := lv_cut_recNo m (S.building vs) y
  cases h1 : (cutStream m (S.building vs)).lv y with
  | none =>
    rw [h1] at this
    cases h2 : (S.building vs).lv y with
    | none => rfl
    | some w => rw [h2] at this; simp at this
  | some w =>
    rw [h1] at this
    cases h2 : (S.building vs).lv y with
    | none => rw [h2] at this; simp at this
    | some w' =>
      rw [h2] at this
      simp only [Option.map_some, Option.some.injEq] at this ⊢
      rw [this]

/-! ### Parts of a step on structures that agree on some nodes -/

section Congr

variable {sp : Spec V T}

/-- Writing nodes xs on a stream cut at m, from P', gives what writing them on the
whole stream from P gives, when P' and P have the same nodes xs. -/
theorem writeAll_cut_congr {m : Nat} {S : Stream V T} (hm : m ≤ S.length) (i : Nat)
    {P P' : Struct V} : ∀ (xs : List NodeId), (∀ x ∈ xs, P'.get? x = P.get? x) →
      ∀ (vs : List (Version V)), writeAll sp (cutStream m S) i P' xs vs = writeAll sp S i P xs vs := by
  intro xs
  induction xs with
  | nil => intro _ vs; rfl
  | cons x xs ih =>
    intro h vs
    rw [writeAll_cons, writeAll_cons, h x List.mem_cons_self]
    cases hx : P.get? x with
    | none => exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _
    | some n =>
      simp only
      rw [mkVersion_cut hm]
      exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

theorem byLevel_congr_on {P P' : Struct V} (xs : List NodeId) (h : ∀ x ∈ xs, P'.get? x = P.get? x) :
    byLevel P' xs = byLevel P xs := by
  unfold byLevel
  have := List.map_mergeSort (f := id) (l := xs)
    (r := fun a b => decide (((P'.get? a).map (·.level)).getD 0 ≤ ((P'.get? b).map (·.level)).getD 0))
    (s := fun a b => decide (((P.get? a).map (·.level)).getD 0 ≤ ((P.get? b).map (·.level)).getD 0))
    (fun a ha b hb => by simp only [id, h a ha, h b hb])
  simpa using this

/-- BergDB's still-dirty test looks at P only through the nodes it tests. -/
theorem stillDirtyOf_javaTest_congr_on (al : Algo V T) (hj : al.stillDirty = javaTest sp)
    {P P' : Struct V} (S S' : Stream V T) (i : Time) :
    ∀ (taken : List NodeId), (∀ x ∈ taken, P'.get? x = P.get? x) → ∀ (acc : Dirty × List NodeId),
      taken.foldl (fun (acc : Dirty × List NodeId) x =>
        if al.stillDirty S' P' acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) acc =
      taken.foldl (fun (acc : Dirty × List NodeId) x =>
        if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) acc := by
  intro taken
  induction taken with
  | nil => intro _ acc; rfl
  | cons x xs ih =>
    intro h acc
    simp only [List.foldl_cons]
    have hx : al.stillDirty S' P' acc.1 i x = al.stillDirty S P acc.1 i x := by
      rw [hj]; simp only [javaTest, h x List.mem_cons_self]
    rw [hx]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) _

theorem stillDirtyOf_cut_congr (al : Algo V T) (hj : al.stillDirty = javaTest sp)
    {P P' : Struct V} (S S' : Stream V T) (D : Dirty) (i : Time) (taken : List NodeId)
    (h : ∀ x ∈ taken, P'.get? x = P.get? x) :
    stillDirtyOf al S' P' D i taken = stillDirtyOf al S P D i taken := by
  unfold stillDirtyOf
  exact stillDirtyOf_javaTest_congr_on al hj S S' i taken h _

/-- Filtering a list of ids sorted by mergeSort is sorting the filtered list. -/
theorem filter_mergeSort_nat (l : List Nat) (p : Nat → Bool) :
    (l.mergeSort (fun a b => decide (a ≤ b))).filter p = (l.filter p).mergeSort (fun a b => decide (a ≤ b)) := by
  have hp : ((l.mergeSort (fun a b => decide (a ≤ b))).filter p).Perm
      ((l.filter p).mergeSort (fun a b => decide (a ≤ b))) :=
    ((List.mergeSort_perm _ _).filter p).trans (List.mergeSort_perm _ _).symm
  apply List.Perm.eq_of_pairwise (le := fun a b => decide (a ≤ b) = true) _ _ _ hp
  · intro a b _ _ h1 h2
    simp only [decide_eq_true_eq] at h1 h2
    omega
  · exact (List.pairwise_mergeSort (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _).filter p
  · exact List.pairwise_mergeSort (by intro a b c; simp only [decide_eq_true_eq]; omega)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) _

/-- The nodes below a reachable node at t are the same in P' as in P, when P' has P's
node for every node but the root that is reachable at t in P (which has A4). -/
theorem reachFrom_agree {P P' : Struct V} {t : Time} (hls : LiveSub sp) (hp : PtrsOK sp P)
    (hroot : (P.get? root).isSome)
    (h : ∀ y, Reach sp P t y → y ≠ root → P'.get? y = P.get? y) :
    ∀ (b : Nat) (x : NodeId) (n : Node V), n.level < b → P.get? x = some n → Reach sp P t x →
      reachFrom sp P' t x n = reachFrom sp P t x n := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hroot
  intro b
  induction b with
  | zero => intro x n hb; omega
  | succ b ih =>
    intro x n hb hx hr
    rw [reachFrom_eq, reachFrom_eq]
    congr 1
    apply flatMap_congr_mem
    intro y hy
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    obtain ⟨m, hm, hlt⟩ := hp x n hx e (mem_upTo.mp he).1 y hye
    have hyr : Reach sp P t y := Reach.child hr hx hy hm hlt
    have hyroot : y ≠ root := by
      intro hy0
      subst hy0
      rw [h0, Option.some.injEq] at hm
      subst hm
      rcases reach_level_root hr h0 n hx with h1 | h1
      · subst h1; rw [h0, Option.some.injEq] at hx; subst hx; omega
      · omega
    rw [h y hyr hyroot, hm]
    simp only [hlt, ↓reduceIte]
    exact ih y m (by omega) hm hyr

/-- Marking on structures that agree for lookups at time i (from f on) marks the same
nodes. -/
theorem marked_cutAgree {f t i : Time} {P P' : Struct V} (h : CutAgree sp f t P P') (hls : LiveSub sp)
    (hp : PtrsOK sp P) (h1 : f ≤ i) (h2 : i ≤ t) (c : Changes V) (x : NodeId) :
    marked sp P' c i x = marked sp P c i x := by
  unfold marked
  rw [h.reachable_eq hls hp h1 h2 x]
  cases hr : reachable sp P i x with
  | false => rfl
  | true =>
    simp only [Bool.true_and]
    have hR : Reach sp P i x := (reachable_iff _ _ _ _).mp hr
    have hag : ∀ y, Reach sp P i y → y ≠ root → P'.get? y = P.get? y := by
      intro y hy hyr
      exact h.nodes y i h1 h2 (fun _ => hyr) ((reachable_iff _ _ _ _).mpr hy)
    by_cases hx : sp.virt = true ∧ x = root
    · obtain ⟨hv, rfl⟩ := hx
      obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
      obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
      obtain ⟨hlev, hlive⟩ := h.rootLive hv n n' hn hn'
      rw [hn, hn']
      simp only
      congr 1
      rw [reachFrom_eq, reachFrom_eq, ← hlive i h1 h2, ← hlev]
      congr 1
      apply flatMap_congr_mem
      intro y hy
      obtain ⟨e, he, hye⟩ := hls _ _ hy
      obtain ⟨m, hm, hlt⟩ := hp root n hn e (mem_upTo.mp he).1 y hye
      have hyr : Reach sp P i y := Reach.child hR hn hy hm hlt
      have hy0 : y ≠ root := by
        intro hy0; subst hy0; rw [hn, Option.some.injEq] at hm; subst hm; omega
      rw [hag y hyr hy0, hm]
      simp only [hlt, ↓reduceIte]
      exact reachFrom_agree hls hp h.rootP hag (m.level + 1) y m (by omega) hm hyr
    · have hx' : sp.virt = true → x ≠ root := fun hv hxr => hx ⟨hv, hxr⟩
      rw [h.nodes x i h1 h2 hx' hr]
      cases hn : P.get? x with
      | none => rfl
      | some n => simp only; rw [reachFrom_agree hls hp h.rootP hag (n.level + 1) x n (by omega) hn hR]

/-- Step 3 with marking, on structures that agree for lookups at time i and have the
same touched nodes, finds the same nodes (a virtual root is never among them). -/
theorem gotDirty3_cutAgree (al : Algo V T) (hmk : al.mark = true) {f t i : Time} {P P' : Struct V}
    (h : CutAgree sp f t P P') (hls : LiveSub sp) (hp : PtrsOK sp P) (h1 : f ≤ i) (h2 : i ≤ t)
    (S S' : Stream V T) (vs vs' : List (Version V)) (c : Changes V) (D : Dirty)
    (htouch : ∀ x ∈ c.touch, written sp x = true → P'.get? x = P.get? x) :
    gotDirty3 sp al S' vs' P' c D i = gotDirty3 sp al S vs P c D i := by
  unfold gotDirty3
  simp only [hmk, ↓reduceIte, List.filter_append]
  -- The marked nodes that may be written: the same in both.
  have hmem : ∀ x, written sp x = true → (x ∈ markOf sp P' c D i ↔ x ∈ markOf sp P c D i) := by
    intro x hw
    unfold markOf
    rw [List.mem_mergeSort, List.mem_mergeSort, List.mem_filter, List.mem_filter,
      mem_allIds, mem_allIds, marked_cutAgree h hls hp h1 h2 c x]
    constructor
    · rintro ⟨hs, hq⟩
      simp only [Bool.and_eq_true] at hq
      obtain ⟨⟨hi, hd⟩, hm⟩ := hq
      have hr : reachable sp P i x = true := by unfold marked at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
      have hx : sp.virt = true → x ≠ root := by
        intro hv hxr; subst hxr; simp [written, hv] at hw
      have hn := h.nodes x i h1 h2 hx hr
      rw [hn] at hs
      simp only [isIndex, hn] at hi
      exact ⟨hs, by simp only [Bool.and_eq_true, isIndex]; exact ⟨⟨hi, hd⟩, hm⟩⟩
    · rintro ⟨hs, hq⟩
      simp only [Bool.and_eq_true] at hq
      obtain ⟨⟨hi, hd⟩, hm⟩ := hq
      have hr : reachable sp P i x = true := by unfold marked at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
      have hx : sp.virt = true → x ≠ root := by
        intro hv hxr; subst hxr; simp [written, hv] at hw
      have hn := h.nodes x i h1 h2 hx hr
      rw [← hn] at hs
      simp only [isIndex, ← hn] at hi
      exact ⟨hs, by simp only [Bool.and_eq_true, isIndex]; exact ⟨⟨hi, hd⟩, hm⟩⟩
  have hbase : (markOf sp P' c D i).filter (written sp) = (markOf sp P c D i).filter (written sp) := by
    unfold markOf
    rw [filter_mergeSort_nat, filter_mergeSort_nat]
    apply mergeSort_eq_of_mem (nodup_filter (nodup_filter (nodup_eraseDups _) _) _)
      (nodup_filter (nodup_filter (nodup_eraseDups _) _) _)
    intro x
    have e1 : ∀ (Q : Struct V), x ∈ (((Q.map (·.1)).eraseDups).filter
        (fun x => isIndex Q x && !inD D x && marked sp Q c i x)).filter
        (written sp) ↔ x ∈ markOf sp Q c D i ∧ written sp x = true := by
      intro Q
      unfold markOf allIds
      rw [List.mem_mergeSort, List.mem_filter]
    rw [e1 P', e1 P]
    constructor
    · rintro ⟨hx, hw⟩; exact ⟨(hmem x hw).mp hx, hw⟩
    · rintro ⟨hx, hw⟩; exact ⟨(hmem x hw).mpr hx, hw⟩
  rw [hbase]
  congr 1
  unfold touchOf
  rw [filter_mergeSort_nat, filter_mergeSort_nat]
  apply mergeSort_eq_of_mem (nodup_filter (nodup_filter (nodup_eraseDups _) _) _)
    (nodup_filter (nodup_filter (nodup_eraseDups _) _) _)
  intro x
  simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  constructor
  · rintro ⟨⟨hx, ⟨hi, hd⟩, hb⟩, hw⟩
    have ht : x ∈ c.touch := List.mem_eraseDups.mp hx
    refine ⟨⟨hx, ⟨?_, hd⟩, ?_⟩, hw⟩
    · simpa only [isIndex, htouch x ht hw] using hi
    · cases hc : (markOf sp P c D i).contains x with
      | false => rfl
      | true =>
        have hm := (hmem x hw).mpr (List.contains_iff_mem.mp hc)
        rw [List.contains_iff_mem.mpr hm] at hb; cases hb
  · rintro ⟨⟨hx, ⟨hi, hd⟩, hb⟩, hw⟩
    have ht : x ∈ c.touch := List.mem_eraseDups.mp hx
    refine ⟨⟨hx, ⟨?_, hd⟩, ?_⟩, hw⟩
    · simpa only [isIndex, htouch x ht hw] using hi
    · cases hc : (markOf sp P' c D i).contains x with
      | false => rfl
      | true =>
        have hm := (hmem x hw).mp (List.contains_iff_mem.mp hc)
        rw [List.contains_iff_mem.mpr hm] at hb; cases hb

/-- With a virtual root: two root histories of root entries with the same live
children give the same root child as their last entry's. -/
theorem lastRootChild_eq (hvl : VirtLiveOK sp) (hv : sp.virt = true) (hptrs : ∀ z, sp.ptrs (sp.rootVal z) = [z])
    {h h' : History V} (hr : ∀ e ∈ h, ∃ z, e.val = sp.rootVal z) (hr' : ∀ e ∈ h', ∃ z, e.val = sp.rootVal z)
    (hl : sp.live h = sp.live h') :
    (h.getLast?.bind (fun e => (sp.ptrs e.val).head?)) = (h'.getLast?.bind (fun e => (sp.ptrs e.val).head?)) := by
  rw [hvl hv h hr, hvl hv h' hr'] at hl
  cases he : h.getLast? with
  | none =>
    cases he' : h'.getLast? with
    | none => rfl
    | some e' =>
      rw [he, he'] at hl
      obtain ⟨z, hz⟩ := hr' e' (List.mem_of_getLast? he')
      simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, hz, hptrs] at hl
      cases hl
  | some e =>
    cases he' : h'.getLast? with
    | none =>
      rw [he, he'] at hl
      obtain ⟨z, hz⟩ := hr e (List.mem_of_getLast? he)
      simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, hz, hptrs] at hl
      cases hl
    | some e' =>
      rw [he, he'] at hl
      simp only [Option.map_some, Option.getD_some] at hl
      simp only [Option.bind_some, hl]

/-- top(i) on structures that agree for lookups at time s (from f on), on the
stream cut at m, is top(i) on the whole stream. -/
theorem topOf_cutAgree {f t s : Time} {P P' : Struct V} (h : CutAgree sp f t P P') (hvl : VirtLiveOK sp)
    (hfs : f ≤ s) (hst : s ≤ t) (hptrs : sp.virt = true → ∀ z, sp.ptrs (sp.rootVal z) = [z])
    (hrootv : sp.virt = true → ∀ n, P.get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z)
    {m : Nat} {S : Stream V T} : topOf sp P' (cutStream m S) s = topOf sp P S s := by
  unfold topOf
  by_cases hv : sp.virt = true
  · simp only [hv, ↓reduceIte]
    unfold topV
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h.rootP
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp h.rootP'
    rw [hn, hn']
    simp only [Option.bind_some]
    have hz := lastRootChild_eq hvl hv (hptrs hv)
      (fun e he => h.rootVals' hv n' hn' e (mem_upTo.mp he).1)
      (fun e he => hrootv hv n hn e (mem_upTo.mp he).1)
      ((h.rootLive hv n n' hn hn').2 s hfs hst).symm
    cases he : (n'.hist.upTo s).getLast? with
    | none =>
      rw [he] at hz
      cases he2 : (n.hist.upTo s).getLast? with
      | none => rfl
      | some e2 =>
        rw [he2] at hz
        simp only [Option.bind_none, Option.bind_some] at hz
        simp only
        rw [← hz]
    | some e =>
      rw [he] at hz
      cases he2 : (n.hist.upTo s).getLast? with
      | none =>
        rw [he2] at hz
        simp only [Option.bind_none, Option.bind_some] at hz
        simp only
        rw [hz]
      | some e2 =>
        rw [he2] at hz
        simp only [Option.bind_some] at hz
        simp only
        rw [hz]
        cases (sp.ptrs e2.val).head? with
        | none => rfl
        | some z =>
          simp only
          rw [lv_cut_recNo_map]
  · have hv' : sp.virt = false := by simpa using hv
    simp only [hv', Bool.false_eq_true, ↓reduceIte]
    rw [lv_cut_recNo_map]

end Congr

/-! ### The relation, and a step on related states -/

/-- The state db' of a run that restarted from cut streams, and the state db of the
run without restarts and cuts, after transaction k: db''s stream is db's, cut at m;
the same D; P agrees with db's for lookups from f to k (`CutAgree`), and has db's
node for every node of D; m ≤ f ≤ db's first available time. -/
structure CutRel (sp : Spec V T) (m f k : Nat) (db' db : DB V T) : Prop where
  stream : db'.S = cutStream m db.S
  dirty : db'.D = db.D
  agree : CutAgree sp f k db.P db'.P
  dNodes : ∀ x, inD db.D x = true → db'.P.get? x = db.P.get? x
  mf : m ≤ f
  fa : f ≤ lastFa db.S

section Step

variable (sp : Spec V T) (al : Algo V T)

/-- A root after a change keeps entries for root children. -/
theorem rootVals_apply {P : Struct V} {i : Time} {c : Changes V}
    (hr : ∀ n, P.get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z)
    (hadds : ∀ a ∈ c.adds, a.1 = root → ∃ z, a.2 = sp.rootVal z) (hroot : (P.get? root).isSome) :
    ∀ n, (P.apply i c).get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z := by
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hroot
  intro n hn e he
  rw [get?_apply_of_get? h0, Option.some.injEq] at hn
  subst hn
  rcases List.mem_append.mp he with he | he
  · exact hr n0 h0 e he
  · obtain ⟨-, hm⟩ := mem_addsFor.mp he
    exact hadds _ hm rfl

/-- A node that step 3 finds is reachable at i after the change, or touched, and
so reachable at i - 1 before it; it may be written. -/
theorem mem_gotDirty3 (hmk : al.mark = true) {S : Stream V T} {vs : List (Version V)} {P : Struct V}
    {c : Changes V} {D : Dirty} {i : Time} {x : NodeId} (hx : x ∈ gotDirty3 sp al S vs P c D i) :
    written sp x = true ∧ (reachable sp P i x = true ∨ x ∈ c.touch) := by
  unfold gotDirty3 at hx
  simp only [hmk, ↓reduceIte, List.mem_filter, List.mem_append] at hx
  obtain ⟨hx, hw⟩ := hx
  refine ⟨hw, ?_⟩
  rcases hx with hx | hx
  · left
    unfold markOf at hx
    rw [List.mem_mergeSort, List.mem_filter] at hx
    have := hx.2
    simp only [Bool.and_eq_true] at this
    unfold marked at this
    simp only [Bool.and_eq_true] at this
    exact this.2.1
  · right
    unfold touchOf at hx
    rw [List.mem_mergeSort, List.mem_filter] at hx
    exact List.mem_eraseDups.mp hx.1

/-- A transaction on related states (`CutRel`) appends the same record, and the
states after it are related. BergDB's bookkeeping (marking, `javaTest`); with a
virtual root, `ExecRootOK` and `VirtLiveOK`; the policies do not look at what a
cut removes (`PolicyCutOK`). -/
theorem step_congr_cut (hsp : SpecOK sp) {db db' : DB V T} {k : Nat} (hinv : Inv sp db k)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp)
    (hvl : VirtLiveOK sp) (hpol : PolicyCutOK al) {m f : Nat} (h : CutRel sp m f k db' db)
    (hfs : lastFa db.S ≤ lastSp db.S) (tr : T)
    (hstep : StepOK sp db.P (k + 1) (sp.exec tr (k + 1) (view sp db.P k))) :
    (parts sp al db' tr).R = (parts sp al db tr).R ∧
      CutRel sp m f (k + 1) (step sp al db' tr) (step sp al db tr) := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hlen' : db'.S.length = k + 1 := by rw [h.stream, cutStream_length, hlen]
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hffa := h.fa
  have hfk : f ≤ k := by omega
  have hmS : m ≤ db.S.length := by have := h.mf; omega
  have hroot : sp.virt = true → ∀ n, db.P.get? root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z := by
    intro hv n hn e he
    obtain ⟨z, -, -, hval⟩ := (hinv.vr hv).rootEntry n hn e he
    exact ⟨z, hval⟩
  -- 1. The change.
  have hc : (parts sp al db' tr).c = (parts sp al db tr).c := by
    rw [parts_c, parts_c, hlen', hlen]
    simp only [Nat.add_sub_cancel]
    exact exec_cutAgree hex h.agree hfk hls hinv.ptrs hroot tr (k + 1)
  have hcd : (parts sp al db tr).c = sp.exec tr (k + 1) (view sp db.P k) := by
    rw [parts_c, hlen]; rfl
  have hstep' : StepOK sp db.P (k + 1) (parts sp al db tr).c := by rw [hcd]; exact hstep
  have hadds : sp.virt = true → ∀ a ∈ (parts sp al db tr).c.adds, a.1 = root → ∃ z, a.2 = sp.rootVal z :=
    fun hv => (hstep'.virt hv).root_adds
  have hP1 : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := by rw [parts_P, hlen]
  have hP2 : (parts sp al db' tr).P = db'.P.apply (k + 1) (parts sp al db tr).c := by
    rw [parts_P, hlen', hc]
  have hag1 : CutAgree sp f (k + 1) (parts sp al db tr).P (parts sp al db' tr).P := by
    rw [hP1, hP2]
    exact h.agree.apply hfk hls hinv.ptrs hinv.times hstep' hvl hroot hadds
  -- Nodes that the step reads have the same node in both.
  have hDn : ∀ x, inD db.D x = true → (parts sp al db' tr).P.get? x = (parts sp al db tr).P.get? x := by
    intro x hx
    rw [hP1, hP2, get?_apply, get?_apply, h.dNodes x hx]
  have hgrow : Grow db.P k (parts sp al db tr).P := by rw [hP1]; exact grow_apply _ _ _ (by omega)
  have hrn : ∀ x, written sp x = true → reachable sp (parts sp al db tr).P (k + 1) x = true →
      (parts sp al db' tr).P.get? x = (parts sp al db tr).P.get? x := by
    intro x hw hr
    exact hag1.nodes x (k + 1) (by omega) (Nat.le_refl _)
      (fun hv hx => by subst hx; simp [written, hv] at hw) hr
  have htn : ∀ x ∈ (parts sp al db tr).c.touch, written sp x = true →
      (parts sp al db' tr).P.get? x = (parts sp al db tr).P.get? x := by
    intro x hx hw
    have hr0 := hstep'.touchReach x hx
    simp only [Nat.add_sub_cancel] at hr0
    have hr : reachable sp (parts sp al db tr).P k x = true := by
      rw [reachable_grow hls hinv.ptrs hinv.rootIn hgrow (Nat.le_refl _)]; exact hr0
    exact hag1.nodes x k hfk (by omega) (fun hv hx => by subst hx; simp [written, hv] at hw) hr
  -- 2. Data.
  have hvs0 : (parts sp al db' tr).vs0 = (parts sp al db tr).vs0 := by
    rw [parts_vs0, parts_vs0, hlen', hlen, hc, h.stream]
    apply writeAll_cut_congr hmS
    intro x hx
    obtain ⟨nn, hnn, hxe⟩ := List.mem_map.mp hx
    subst hxe
    have hnew := (List.mem_filter.mp hnn).1
    apply hrn
    · have hf := hstep'.fresh nn hnew
      have hne : nn.id ≠ root := by
        intro hxr
        rw [hxr] at hf
        obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
        rw [h0] at hf; cases hf
      simp [written, hne]
    · rw [hP1]; exact hstep'.newReachable nn hnew
  -- 3. Got dirty.
  have hgd3 : (parts sp al db' tr).gd3 = (parts sp al db tr).gd3 := by
    show gotDirty3 sp al db'.S (parts sp al db' tr).vs0 (parts sp al db' tr).P (parts sp al db' tr).c
        db'.D db'.S.length =
      gotDirty3 sp al db.S (parts sp al db tr).vs0 (parts sp al db tr).P (parts sp al db tr).c
        db.D db.S.length
    rw [hc, h.dirty, hlen', hlen]
    exact gotDirty3_cutAgree al hmk hag1 hls (step_pfacts sp al db tr hsp hinv hstep').ptrs
      (by omega) (Nat.le_refl _) _ _ _ _ _ _ htn
  have hgdn : ∀ x ∈ (parts sp al db tr).gd3,
      (parts sp al db' tr).P.get? x = (parts sp al db tr).P.get? x := by
    intro x hx
    have hx' : x ∈ gotDirty3 sp al db.S (parts sp al db tr).vs0 (parts sp al db tr).P
        (parts sp al db tr).c db.D db.S.length := hx
    obtain ⟨hw, hr | ht⟩ := mem_gotDirty3 sp al hmk hx'
    · rw [hlen] at hr; exact hrn x hw hr
    · exact htn x ht hw
  have hD1 : (parts sp al db' tr).D1 = (parts sp al db tr).D1 := by
    rw [parts_D1, parts_D1, hgd3, h.dirty, hlen', hlen]
  have hD1n : ∀ e ∈ (parts sp al db tr).D1,
      (parts sp al db' tr).P.get? e.1 = (parts sp al db tr).P.get? e.1 := by
    intro e he
    rcases (step_D1_mem sp al db tr hlen e).mp he with h1 | ⟨-, h1⟩
    · exact hDn e.1 ((inD_iff _ _).mpr ⟨e.2, h1⟩)
    · exact hgdn e.1 h1
  -- 4. Startup pos, first available time.
  have hpol' := hpol m db.S (parts sp al db tr).D1 (k + 1) tr (parts sp al db tr).s (Nat.le_trans h.mf h.fa)
  have hs : (parts sp al db' tr).s = (parts sp al db tr).s := by
    rw [parts_s, parts_s, hD1, hlen', hlen, h.stream, hpol'.1]
  have hfa : (parts sp al db' tr).fa = (parts sp al db tr).fa := by
    rw [parts_fa, parts_fa, hD1, hs, hlen', hlen, h.stream, hpol'.2]
  -- 5, 6. Taken, written.
  have htakenn : ∀ x ∈ (parts sp al db tr).taken,
      (parts sp al db' tr).P.get? x = (parts sp al db tr).P.get? x := by
    intro x hx
    rw [parts_taken, byLevel, List.mem_mergeSort] at hx
    obtain ⟨e, he, hex⟩ := List.mem_map.mp hx
    subst hex
    exact hD1n e (List.mem_filter.mp he).1
  have htaken : (parts sp al db' tr).taken = (parts sp al db tr).taken := by
    rw [parts_taken, parts_taken, hD1, hs]
    apply byLevel_congr_on
    intro x hx
    obtain ⟨e, he, hex⟩ := List.mem_map.mp hx
    subst hex
    exact hD1n e (List.mem_filter.mp he).1
  have hD2 : (parts sp al db' tr).D2 = (parts sp al db tr).D2 := by
    rw [parts_D2, parts_D2, hD1, hs]
  have hvs : (parts sp al db' tr).vs = (parts sp al db tr).vs := by
    rw [parts_vs, parts_vs, htaken, hvs0, hlen', hlen, h.stream]
    exact writeAll_cut_congr hmS _ _ htakenn _
  have hS' : (parts sp al db' tr).S' = cutStream m (parts sp al db tr).S' := by
    rw [parts_S', parts_S', hvs, h.stream, cutStream_building hmS]
  -- 7. Still dirty.
  have hr7 : (parts sp al db' tr).r7 = (parts sp al db tr).r7 := by
    rw [parts_r7, parts_r7, hD2, htaken, hlen', hlen]
    exact stillDirtyOf_cut_congr al hj _ _ _ _ _ htakenn
  -- 8. The record.
  have hsk1 : lastSp db.S ≤ (parts sp al db tr).s := by
    rw [parts_s]; unfold startupPos; rw [hlen]; simp only [Nat.add_sub_cancel]; omega
  have hsk2 : (parts sp al db tr).s ≤ k + 1 := by
    rw [parts_s]; unfold startupPos; rw [hlen]; simp only [Nat.add_sub_cancel]; omega
  have htop : topOf sp (parts sp al db' tr).P (parts sp al db' tr).S' (parts sp al db tr).s =
      topOf sp (parts sp al db tr).P (parts sp al db tr).S' (parts sp al db tr).s := by
    rw [hS']
    exact topOf_cutAgree hag1 hvl (by omega) hsk2 (fun hv => (hinv.vr hv).rootPtrs)
      (fun hv => by rw [hP1]; exact rootVals_apply sp (hroot hv) (hadds hv) hinv.rootIn)
  have hR : (parts sp al db' tr).R = (parts sp al db tr).R := by
    rw [parts_R, parts_R, hs, hvs, hgd3, hr7, hfa, ← htop]
  refine ⟨hR, ?_⟩
  rw [step_eq_parts, step_eq_parts]
  refine ⟨?_, ?_, ?_, ?_, h.mf, ?_⟩
  · simp only
    rw [hR, h.stream, cutStream_append_one hmS]
  · simp only; rw [hr7]
  · exact hag1
  · intro x hx
    simp only at hx ⊢
    rcases step_D_cases sp al db tr hinv hx with h1 | h1 | h1
    · exact hDn x h1
    · exact hgdn x h1
    · exact htakenn x ((step_r7_shape sp al db tr hlen).2.subset h1)
  · have hl : lastFa (db.S ++ [(parts sp al db tr).R]) = (parts sp al db tr).fa := by
      simp [lastFa, parts_R]
    show f ≤ lastFa (db.S ++ [(parts sp al db tr).R])
    rw [hl, parts_fa]
    unfold firstAvail
    have := h.fa
    have : lastFa db.S ≤ (parts sp al db tr).s := by omega
    omega

end Step

end SIS
