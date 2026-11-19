/-
The contract package (bergdb 030-24): `TScheme` (Contract/ReclaimScheme.lean,
bergdb 030-23) is false. It speaks of every run that meets `RunOK`, and
`RunOK` alone allows a transaction to move a live child to another current
parent while the old parent keeps a dead pointer to it, which A6' (`adoptAt`,
`EvictRunOK`) excludes and BergDB's tree does not do.

The run: a virtual root 0, a top node 30, an index node 20 with children 1
and 2, and leaves 3 and 4 below them. Transaction 1 gives node 1 a new child
101 in leaf 3's slot and puts leaf 3 in node 2's slot, in place of leaf 4:
leaf 3 moves to another current parent while node 1 keeps a dead pointer to
it (A6' fails). Transaction 3, a reclaim step, touches 3, 2, 20 and 30 and
gives node 2 a new child 104 in that slot; transaction 6 gives 101 a new
child; transactions 2, 4 and 5 change nothing. With the startup pos at
i - 1 and the first available time 3, RC holds for the cut c = 1, the end
e = 3 and the state k = 6, with both waits (v = 4). After T(6), node 1 is in
D, its latest version, of record 2, names leaf 3's version of record 0, and
leaf 3's latest version is of record 4: `CutOK`'s part 3 fails.

The kernel evaluates the run (`decide +kernel`). `List.mergeSort` and
`List.merge` are defined by well-founded recursion, which the kernel does not
evaluate here, so the run is evaluated in the form `runK`, which sorts with
the same algorithm by structural recursion on a fuel (`msortF`) and equals
`run` (`run_eq`).
-/
import Contract.ReclaimScheme
import SIS.Example

namespace Contract.AdoptionExample

open SIS (Spec Algo DB Struct Changes Version Record Dirty Node History reachable
  reachList reachFrom written lastSp lastFa inD run CutOK RunOK javaTest isTop isIndex pointees
  view step init markOf touchOf byLevel gotDirty3 gotDirtyOf allIds marked writeAll startupPos
  firstAvail stillDirtyOf topOf)
open SIS.Example (Val)

/-! ## Sorting by structural recursion -/

section Sorting

variable {α : Type}

/-- `List.merge` with a fuel, by structural recursion. -/
def mergeF (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | n + 1, x :: xs, y :: ys =>
    if le x y then x :: mergeF le n xs (y :: ys) else y :: mergeF le n (x :: xs) ys

theorem mergeF_eq (le : α → α → Bool) : ∀ (n : Nat) (xs ys : List α),
    xs.length + ys.length ≤ n → mergeF le n xs ys = List.merge xs ys le := by
  intro n
  induction n with
  | zero =>
    intro xs ys h
    have h1 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst h1; subst h2; simp [mergeF]
  | succ n ih =>
    intro xs ys h
    cases xs with
    | nil => simp [mergeF]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeF]
      | cons y ys =>
        simp only [mergeF, List.cons_merge_cons]
        split
        · rw [ih xs (y :: ys) (by simp at h ⊢; omega)]
        · rw [ih (x :: xs) ys (by simp at h ⊢; omega)]

/-- `List.mergeSort` with a fuel, by structural recursion: the same splits and
merges. -/
def msortF (le : α → α → Bool) : Nat → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | n + 1, a :: b :: xs =>
    mergeF le (xs.length + 2) (msortF le n ((a :: b :: xs).take ((xs.length + 3) / 2)))
      (msortF le n ((a :: b :: xs).drop ((xs.length + 3) / 2)))

theorem msortF_eq (le : α → α → Bool) : ∀ (n : Nat) (l : List α),
    l.length ≤ n → msortF le n l = l.mergeSort le := by
  intro n
  induction n with
  | zero =>
    intro l h
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [msortF]
  | succ n ih =>
    intro l h
    match l with
    | [] => simp [msortF]
    | [a] => simp [msortF]
    | a :: b :: xs =>
      rw [List.mergeSort]
      simp only [msortF, List.MergeSort.Internal.splitInTwo_fst,
        List.MergeSort.Internal.splitInTwo_snd, List.length_cons]
      simp only [List.length_cons] at h
      rw [ih _ (by simp; omega), ih _ (by simp; omega)]
      rw [mergeF_eq]
      simp only [List.length_mergeSort, List.length_take, List.length_drop, List.length_cons]
      omega

end Sorting

/-! ## The run in a form the kernel evaluates -/

section Run

variable {V T : Type} [DecidableEq V]

/-- `markOf` with `msortF`. -/
def markOfK (sp : Spec V T) (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) :
    List NodeId :=
  let l := (allIds P).filter (fun x => isIndex P x && !inD D x && marked sp P c i x)
  msortF (fun a b => decide (a ≤ b)) l.length l

/-- `touchOf` with `msortF`. -/
def touchOfK (P : Struct V) (c : Changes V) (D : Dirty) (base : List NodeId) : List NodeId :=
  let l := c.touch.eraseDups.filter (fun x => isIndex P x && !inD D x && !base.contains x)
  msortF (fun a b => decide (a ≤ b)) l.length l

/-- `byLevel` with `msortF`. -/
def byLevelK (P : Struct V) (xs : List NodeId) : List NodeId :=
  msortF (fun a b =>
    decide (((P.get? a).map (·.level)).getD 0 ≤ ((P.get? b).map (·.level)).getD 0)) xs.length xs

omit [DecidableEq V] in
theorem markOf_eq (sp : Spec V T) (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) :
    markOf sp P c D i = markOfK sp P c D i := by
  unfold markOf markOfK
  rw [msortF_eq _ _ _ (Nat.le_refl _)]

omit [DecidableEq V] in
theorem touchOf_eq (P : Struct V) (c : Changes V) (D : Dirty) (base : List NodeId) :
    touchOf P c D base = touchOfK P c D base := by
  unfold touchOf touchOfK
  rw [msortF_eq _ _ _ (Nat.le_refl _)]

omit [DecidableEq V] in
theorem byLevel_eq (P : Struct V) (xs : List NodeId) : byLevel P xs = byLevelK P xs := by
  unfold byLevel byLevelK
  rw [msortF_eq _ _ _ (Nat.le_refl _)]

/-- `gotDirty3` with `markOfK` and `touchOfK`. -/
def gotDirty3K (sp : Spec V T) (al : Algo V T) (S : SIS.Stream V T) (vs0 : List (Version V))
    (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) : List NodeId :=
  let base := if al.mark then markOfK sp P c D i else gotDirtyOf sp (S.building vs0) P D i
  (base ++ touchOfK P c D base).filter (written sp)

theorem gotDirty3_eq (sp : Spec V T) (al : Algo V T) (S : SIS.Stream V T)
    (vs0 : List (Version V)) (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) :
    gotDirty3 sp al S vs0 P c D i = gotDirty3K sp al S vs0 P c D i := by
  unfold gotDirty3 gotDirty3K
  simp only [markOf_eq, touchOf_eq]

/-- `step` with `gotDirty3K` and `byLevelK`. -/
def stepK (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) : DB V T :=
  let i := db.S.length
  let c := sp.exec tr i (view sp db.P (i - 1))
  let P := db.P.apply i c
  let vs0 := writeAll sp db.S i P ((c.new.filter (·.isData)).map (·.id)) []
  let gd3 := gotDirty3K sp al db.S vs0 P c db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let fa : Nat := firstAvail al db.S D1 i tr s
  let taken := byLevelK P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  let vs := writeAll sp db.S i P taken vs0
  let S' : SIS.Stream V T := db.S.building vs
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s, fa := fa }
  { P := P, D := r7.1, S := db.S ++ [R] }

theorem step_eq (sp : Spec V T) (al : Algo V T) : step sp al = stepK sp al := by
  funext db tr
  unfold step stepK
  simp only [gotDirty3_eq, byLevel_eq]

/-- `init` with `byLevelK`. -/
def initK (sp : Spec V T) : DB V T :=
  let P := sp.init
  let vs := writeAll sp [] 0 P (byLevelK P ((P.map (·.1)).filter (written sp))) []
  let S' : SIS.Stream V T := SIS.Stream.building [] vs
  { P := P, D := [],
    S := [{ trans := none, sp := 0, vers := vs, gd := [], top := topOf sp P S' 0 }] }

omit [DecidableEq V] in
theorem init_eq (sp : Spec V T) : init sp = initK sp := by
  unfold init initK
  simp only [byLevel_eq]

/-- `run` with `stepK` and `initK`. -/
def runK (sp : Spec V T) (al : Algo V T) (ts : List T) : DB V T :=
  ts.foldl (stepK sp al) (initK sp)

theorem run_eq (sp : Spec V T) (al : Algo V T) (ts : List T) :
    run sp al ts = runK sp al ts := by
  unfold run runK
  rw [step_eq, init_eq]

end Run

/-! ## The witness -/

/-- The initial structure: virtual root 0, top node 30, index node 20 with
children 1 and 2 (level 2), leaves 3 and 4 (level 1), data nodes 7 and 8. -/
def P0 : Struct Val :=
  [(0, SIS.Example.mk 1000 [.slot 0 30]), (30, SIS.Example.mk 100 [.ref 20]),
   (20, SIS.Example.mk 3 [.slot 0 1, .slot 1 2]),
   (1, SIS.Example.mk 2 [.slot 0 3]), (2, SIS.Example.mk 2 [.slot 0 4]),
   (3, SIS.Example.mk 1 [.slot 0 7]), (4, SIS.Example.mk 1 [.slot 0 8]),
   (7, { level := 0, isData := true, hist := [⟨0, .dat 7⟩] }),
   (8, { level := 0, isData := true, hist := [⟨0, .dat 8⟩] })]

/-- The changes of transactions 1 to 6: 1 moves leaf 3 from node 1 to node 2,
3 is a reclaim step with a touch, 6 changes 101; 2, 4 and 5 change nothing. -/
def change (i : Nat) : Changes Val :=
  match i with
  | 1 => { new := [⟨101, 1, false⟩, ⟨102, 0, true⟩],
           adds := [(101, .slot 0 102), (102, .dat 102),
                    (1, .slot 0 101), (2, .slot 0 3)] }
  | 3 => { new := [⟨104, 1, false⟩, ⟨105, 0, true⟩],
           adds := [(104, .slot 0 105), (105, .dat 105), (2, .slot 0 104)],
           touch := [3, 2, 20, 30] }
  | 6 => { new := [⟨106, 0, true⟩], adds := [(106, .dat 106), (101, .slot 0 106)] }
  | _ => { new := [], adds := [] }

def sp : Spec Val Nat :=
  { ptrs := SIS.Example.ptrs, live := SIS.Example.live, exec := fun tr _ _ => change tr,
    init := P0, virt := true, topLevel := 100, rootVal := .slot 0 }

/-- BergDB's still-dirty test and the marking; the startup pos at i - 1, the
first available time 3. -/
def al : Algo Val Nat :=
  { policy := fun _ _ i _ => i - 1, stillDirty := javaTest sp, mark := true,
    faPolicy := fun _ _ _ _ => 3 }

def ts : List Nat := List.range' 1 6

/-! ## Lemmas for the checks -/

theorem get?_mem {P : Struct Val} {x : NodeId} {n : Node Val} (h : P.get? x = some n) :
    (x, n) ∈ P := by
  obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  simp

theorem mem_reachList {P : Struct Val} {t : Time} {x : NodeId}
    (h : reachable sp P t x = true) : x ∈ reachList sp P t := by
  simpa [reachable] using h

theorem slotOf_some (k : Nat) : ∀ (h : History Val) (acc : Option NodeId) (y : NodeId),
    h.foldl (fun acc e => match e.val with
      | .slot k' y => if k' = k then some y else acc
      | _ => acc) acc = some y →
    acc = some y ∨ ∃ e ∈ h, y ∈ SIS.Example.ptrs e.val := by
  intro h
  induction h with
  | nil => intro acc y hy; exact Or.inl hy
  | cons e h ih =>
    intro acc y hy
    rw [List.foldl_cons] at hy
    rcases ih _ y hy with h1 | ⟨e', he', hy'⟩
    · cases hv : e.val with
      | slot k' z =>
        rw [hv] at h1
        simp only at h1
        split at h1
        · cases h1
          exact Or.inr ⟨e, List.mem_cons_self, by simp [hv, SIS.Example.ptrs]⟩
        · exact Or.inl h1
      | ref z => rw [hv] at h1; exact Or.inl h1
      | dat z => rw [hv] at h1; exact Or.inl h1
      | dead z => rw [hv] at h1; exact Or.inl h1
    · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hy'⟩

/-- A live pointer of the example's `live` is a pointer of an entry. -/
theorem live_sub (h : History Val) (y : NodeId) (hy : y ∈ SIS.Example.live h) :
    ∃ e ∈ h, y ∈ SIS.Example.ptrs e.val := by
  simp only [SIS.Example.live, List.mem_eraseDups, List.mem_append, List.mem_filterMap] at hy
  rcases hy with ⟨e, he, hv⟩ | ⟨k, -, hk⟩
  · refine ⟨e, he, ?_⟩
    cases hval : e.val with
    | ref z => rw [hval] at hv; cases hv; simp [SIS.Example.ptrs]
    | slot _ _ => rw [hval] at hv; cases hv
    | dat _ => rw [hval] at hv; cases hv
    | dead _ => rw [hval] at hv; cases hv
  · rcases slotOf_some k h none y hk with h1 | h1
    · cases h1
    · exact h1

/-! ## RunOK -/

/-- The fields of `StepOK` for the example's spec, as a check: every
quantifier over node ids is over the nodes of the structure or the nodes
reachable then, and no transaction makes a root child. -/
def stepB (P : Struct Val) (i : Nat) (c : Changes Val) : Bool :=
  let P' := P.apply i c
  c.new.all (fun n => (P.get? n.id).isNone) &&
  decide (c.new.map (·.id)).Nodup &&
  c.adds.all (fun a => reachable sp P' i a.1) &&
  c.adds.all (fun a => match P.get? a.1 with | some n => !n.isData | none => true) &&
  c.adds.all (fun a => c.new.all (fun n => !(n.id == a.1 && n.isData) || (sp.ptrs a.2).isEmpty)) &&
  c.adds.all (fun a => (sp.ptrs a.2).all (fun y => match P'.get? a.1, P'.get? y with
    | some n, some m => decide (m.level < n.level)
    | _, _ => false)) &&
  c.new.all (fun n => reachable sp P' i n.id) &&
  (reachList sp P' i).all (fun y => reachable sp P (i - 1) y || (c.new.map (·.id)).contains y) &&
  c.new.all (fun nn => decide (nn.level < sp.topLevel)) &&
  c.adds.all (fun a => match P.get? a.1 with
    | some n => a.1 == SIS.root || decide (n.level < sp.topLevel)
    | none => true) &&
  decide (c.adds.filter (fun a => a.1 == SIS.root) =
    (c.new.filter (fun nn => decide (sp.topLevel ≤ nn.level))).map
      (fun nn => (SIS.root, sp.rootVal nn.id))) &&
  P'.all (fun p => !isTop sp P' p.1 ||
    (pointees sp p.2.hist).all (fun y => !isTop sp P' y || !reachable sp P' i y)) &&
  c.touch.all (fun x => isIndex P x) &&
  c.touch.all (fun x => reachable sp P (i - 1) x) &&
  c.touch.all (fun x => P.all (fun q => !reachable sp P (i - 1) q.1 ||
    !(reachFrom sp P (i - 1) q.1 q.2).contains x || c.touch.contains q.1 || q.1 == SIS.root))

theorem stepB_sound {P : Struct Val} {i : Nat} {c : Changes Val} (h : stepB P i c = true) :
    SIS.StepOK sp P i c := by
  simp only [stepB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc] at h
  obtain ⟨hfresh, hdist, hcur, hfix, hnoptr, hlev, hnew, hnores, hntop, htopf, hroot, hdead,
    htidx, htreach, htup⟩ := h
  refine ⟨?_, hdist, hcur, ?_, ?_, ?_, hnew, ?_, ?_, htidx, htreach, ?_⟩
  · intro n hn
    simpa using hfresh n hn
  · intro a ha n hn
    have := hfix a ha
    rw [hn] at this
    simpa using this
  · intro a ha n hn hid hd
    have := hnoptr a ha n hn
    simp only [hid, beq_self_eq_true, hd, Bool.and_self, Bool.not_true, Bool.false_or,
      List.isEmpty_iff] at this
    exact this
  · intro a ha y hy
    have := hlev a ha y hy
    split at this
    · rename_i n m h1 h2
      exact ⟨n, m, h1, h2, by simpa using this⟩
    · cases this
  · intro y hy
    have := hnores y (mem_reachList hy)
    simp only [Bool.or_eq_true, List.contains_iff_mem] at this
    exact this
  · intro _
    refine ⟨?_, ?_, hroot, ?_, ?_⟩
    · intro nn hnn hl
      have := hntop nn hnn
      exact absurd hl (by omega)
    · intro a ha n hn hr
      have := htopf a ha
      rw [hn] at this
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at this
      rcases this with h1 | h1
      · exact absurd h1 hr
      · exact h1
    · intro nn hnn hl
      have := hntop nn hnn
      exact absurd hl (by omega)
    · intro z n hz hzt y hy hyt
      have := hdead (z, n) (get?_mem hz)
      simp only [hzt, Bool.not_true, Bool.false_or, List.all_eq_true] at this
      have := this y hy
      simp only [hyt, Bool.not_true, Bool.false_or, Bool.not_eq_true'] at this
      exact this
  · intro x hx p np hp hnp hxp
    have := htup x hx (p, np) (get?_mem hnp)
    have h1 : (reachFrom sp P (i - 1) p np).contains x = true := List.contains_iff_mem.mpr hxp
    simp only [hp, h1, Bool.not_true, Bool.false_or, Bool.or_eq_true, List.contains_iff_mem,
      beq_iff_eq] at this
    rcases this with h | h
    · exact Or.inl h
    · exact Or.inr ⟨rfl, h⟩

theorem specOK : SIS.SpecOK sp where
  liveSub := live_sub
  initDistinct := by decide +kernel
  initRoot := by decide +kernel
  initTime := by decide +kernel
  initData := by decide +kernel
  initLevels := by
    have h : P0.all (fun p => p.2.hist.all (fun e => (SIS.Example.ptrs e.val).all (fun y =>
        match P0.get? y with
        | some m => decide (m.level < p.2.level)
        | none => false))) = true := by decide +kernel
    intro p hp e he y hy
    simp only [List.all_eq_true] at h
    have := h p hp e he y hy
    split at this
    · rename_i m hm
      exact ⟨m, hm, by simpa using this⟩
    · cases this
  initReachable := by decide +kernel
  virtInit := by
    intro _
    have h0 : P0.get? SIS.root = some (SIS.Example.mk 1000 [.slot 0 30]) := by decide +kernel
    refine ⟨fun z => rfl, ?_, by decide +kernel, ?_⟩
    · intro n hn
      change P0.get? SIS.root = some n at hn
      rw [h0] at hn
      cases hn
      rfl
    · intro n hn
      change P0.get? SIS.root = some n at hn
      rw [h0] at hn
      cases hn
      decide +kernel

theorem runOK : RunOK sp al ts := by
  refine ⟨specOK, ?_⟩
  intro j hj
  have hj6 : j < 6 := hj
  apply stepB_sound
  rw [run_eq]
  show stepB (runK sp al (ts.take j)).P (j + 1) (change ts[j]) = true
  have hts : ts[j] = j + 1 := by simp [ts, Nat.add_comm]
  rw [hts]
  interval_cases j <;> decide +kernel

/-! ## RC at the cut 1, the end 3 and the state 6 -/

/-- RC2 as a check over the nodes reachable at e. -/
def rc2B (db : DB Val Nat) (e c : Nat) : Bool :=
  (reachList sp db.P e).all (fun d => match db.P.get? d with
    | some m => !m.isData || (match db.S.lv d with
      | some u => decide (c ≤ u.recNo)
      | none => false)
    | none => true)

theorem rc2B_sound {db : DB Val Nat} {e c : Nat} (h : rc2B db e c = true) : RC2 sp db e c := by
  intro d m hm hmd hr
  simp only [rc2B, List.all_eq_true] at h
  have := h d (mem_reachList hr)
  rw [hm] at this
  simp only [hmd, Bool.not_true, Bool.false_or] at this
  split at this
  · rename_i u hu
    exact ⟨u, hu, by simpa using this⟩
  · cases this

/-- RC3 as a check over the nodes reachable at e. -/
def rc3B (db : DB Val Nat) (e : Nat) : Bool :=
  (reachList sp db.P e).all (fun x => match db.P.get? x with
    | some n => n.isData || !written sp x ||
        (reachFrom sp db.P e x n).any (fun d => match db.P.get? d with
          | some m => m.isData
          | none => false)
    | none => true)

theorem rc3B_sound {db : DB Val Nat} {e : Nat} (h : rc3B db e = true) : RC3 sp db e := by
  intro x n hn hnd hw hr
  simp only [rc3B, List.all_eq_true] at h
  have := h x (mem_reachList hr)
  rw [hn] at this
  simp only [hnd, hw, Bool.not_true, Bool.false_or, List.any_eq_true] at this
  obtain ⟨d, hd, hdm⟩ := this
  split at hdm
  · rename_i m hm
    exact ⟨d, m, hd, hm, hdm⟩
  · cases hdm

theorem rc : RC sp al ts 1 3 6 := by
  refine ⟨by decide, ?_, rc2B_sound ?_, rc3B_sound ?_, 4, ?_, ?_⟩ <;>
    rw [run_eq] <;> decide +kernel

/-! ## CutOK's part 3 fails -/

theorem not_cutOK : ¬ CutOK sp 1 (run sp al (ts.take 6)) 6 := by
  rintro ⟨-, -, h3, -⟩
  rw [run_eq] at h3
  have hx : inD (runK sp al (ts.take 6)).D 1 = true := by decide +kernel
  have hs : ((runK sp al (ts.take 6)).S.lv 1).isSome = true := by decide +kernel
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  have hr : ((runK sp al (ts.take 6)).S.lv 1).bind (fun v => v.ref? 3) = some 0 := by
    decide +kernel
  rw [hv, Option.bind_some] at hr
  have h4 : ((runK sp al (ts.take 6)).S.lv 3).map (·.recNo) = some 4 := by decide +kernel
  have := (h3 1 hx v hv).2 3 0 hr (by decide)
  rw [h4] at this
  cases this

/-- `TScheme` is false for a spec that breaks A6' (bergdb 030-24). -/
theorem tscheme_false : ¬ TScheme sp al := by
  intro h
  exact not_cutOK (h rfl rfl ts runOK 1 3 6 (by decide) rc)

end Contract.AdoptionExample
