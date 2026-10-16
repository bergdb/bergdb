/-
Proofs, part 5: the parts of a transaction, runs, and the invariant.
-/
import SIS.Proof.Write

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### The parts of transaction i -/

/-- The values computed by `step`, one per line of 6.1. -/
structure Parts (V T : Type) where
  i : Nat
  c : Changes V
  P : Struct V
  vs0 : List (Version V)
  gd3 : List NodeId
  D1 : Dirty
  s : Nat
  taken : List NodeId
  D2 : Dirty
  vs : List (Version V)
  S' : Stream V T
  r7 : Dirty × List NodeId
  R : Record V T

/-- The parts of transaction `tr` run on `db`, as in `step`. -/
def parts (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) : Parts V T :=
  let i := db.S.length
  let c := sp.exec tr i (view sp db.P (i - 1))
  let P := db.P.apply i c
  let vs0 := writeAll sp db.S i P ((c.new.filter (·.isData)).map (·.id)) []
  let gd3 := (if al.mark then markOf sp P c db.D i else gotDirtyOf sp (db.S.building vs0) P db.D i).filter
    (written sp)
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  let vs := writeAll sp db.S i P taken vs0
  let S' : Stream V T := db.S.building vs
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s }
  { i := i, c := c, P := P, vs0 := vs0, gd3 := gd3, D1 := D1, s := s, taken := taken,
    D2 := D2, vs := vs, S' := S', r7 := r7, R := R }

theorem step_eq_parts (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    step sp al db tr =
      { P := (parts sp al db tr).P, D := (parts sp al db tr).r7.1,
        S := db.S ++ [(parts sp al db tr).R] } := rfl

section PartsLemmas

variable (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T)

theorem parts_i : (parts sp al db tr).i = db.S.length := rfl
theorem parts_c : (parts sp al db tr).c =
    sp.exec tr db.S.length (view sp db.P (db.S.length - 1)) := rfl
theorem parts_P : (parts sp al db tr).P = db.P.apply db.S.length (parts sp al db tr).c := rfl
theorem parts_vs0 : (parts sp al db tr).vs0 =
    writeAll sp db.S db.S.length (parts sp al db tr).P
      (((parts sp al db tr).c.new.filter (·.isData)).map (·.id)) [] := rfl
theorem parts_gd3 : (parts sp al db tr).gd3 =
    (if al.mark then markOf sp (parts sp al db tr).P (parts sp al db tr).c db.D db.S.length
    else gotDirtyOf sp (db.S.building (parts sp al db tr).vs0) (parts sp al db tr).P db.D
      db.S.length).filter (written sp) := rfl
theorem parts_D1 : (parts sp al db tr).D1 =
    db.D ++ (parts sp al db tr).gd3.map (fun x => (x, db.S.length)) := rfl
theorem parts_s : (parts sp al db tr).s =
    startupPos al db.S (parts sp al db tr).D1 db.S.length tr := rfl
theorem parts_taken : (parts sp al db tr).taken =
    byLevel (parts sp al db tr).P
      (((parts sp al db tr).D1.filter
        (fun e : NodeId × Nat => decide (e.2 ≤ (parts sp al db tr).s))).map (·.1)) := rfl
theorem parts_D2 : (parts sp al db tr).D2 =
    (parts sp al db tr).D1.filter (fun e : NodeId × Nat => decide ((parts sp al db tr).s < e.2)) :=
  rfl
theorem parts_vs : (parts sp al db tr).vs =
    writeAll sp db.S db.S.length (parts sp al db tr).P (parts sp al db tr).taken
      (parts sp al db tr).vs0 := rfl
theorem parts_S' : (parts sp al db tr).S' = db.S.building (parts sp al db tr).vs := rfl
theorem parts_r7 : (parts sp al db tr).r7 =
    stillDirtyOf al (parts sp al db tr).S' (parts sp al db tr).P (parts sp al db tr).D2
      db.S.length (parts sp al db tr).taken := rfl
theorem parts_R : (parts sp al db tr).R =
    { trans := some tr, sp := (parts sp al db tr).s, vers := (parts sp al db tr).vs,
      gd := (parts sp al db tr).gd3 ++ (parts sp al db tr).r7.2,
      top := topOf sp (parts sp al db tr).P (parts sp al db tr).S' (parts sp al db tr).s } := rfl

end PartsLemmas

/-! ### Step 7 with the exact test -/

theorem stillDirtyOf_filter (al : Algo V T) (S : Stream V T) (P : Struct V) (i : Time)
    (f : NodeId → Bool) (hf : ∀ D x, al.stillDirty S P D i x = f x) (taken : List NodeId) :
    ∀ (D : Dirty) (L : List NodeId),
      taken.foldl (fun (acc : Dirty × List NodeId) x =>
        if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, L) =
      (D ++ (taken.filter f).map (fun x => (x, i)), L ++ taken.filter f) := by
  induction taken with
  | nil => intro D L; simp
  | cons x taken ih =>
    intro D L
    simp only [List.foldl_cons]
    rw [hf]
    by_cases hx : f x = true
    · simp only [hx, ite_true]
      rw [ih]
      simp [hx]
    · simp only [hx]
      simp only [Bool.false_eq_true, ite_false]
      rw [ih]
      simp [hx]

theorem stillDirtyOf_exact (sp : Spec V T) (al : Algo V T) (hex : al.stillDirty = exactTest sp)
    (S : Stream V T) (P : Struct V) (D : Dirty) (i : Time) (taken : List NodeId) :
    stillDirtyOf al S P D i taken =
      (D ++ (taken.filter (fun x => dirty sp S P i x)).map (fun x => (x, i)),
        taken.filter (fun x => dirty sp S P i x)) := by
  unfold stillDirtyOf
  rw [stillDirtyOf_filter al S P i (fun x => dirty sp S P i x) (by intro D x; rw [hex]; rfl)]
  simp

/-! ### Runs -/

/-- The state of a run after its first j transactions. -/
def st (sp : Spec V T) (al : Algo V T) (ts : List T) (j : Nat) : DB V T :=
  run sp al (ts.take j)

theorem st_zero (sp : Spec V T) (al : Algo V T) (ts : List T) : st sp al ts 0 = init sp := by
  simp [st, run]

theorem st_succ (sp : Spec V T) (al : Algo V T) (ts : List T) {j : Nat} (hj : j < ts.length) :
    st sp al ts (j + 1) = step sp al (st sp al ts j) ts[j] := by
  simp only [st, run]
  have h1 : ts.take (j + 1) = ts.take j ++ [ts[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [h1, List.foldl_append]; rfl

theorem st_length (sp : Spec V T) (al : Algo V T) (ts : List T) :
    st sp al ts ts.length = run sp al ts := by
  simp [st]

/-! ### The startup's D -/

/-- The D that startup rebuilds: gd(j) for the transactions j of the
startup section. -/
def sectionD (S : Stream V T) : Dirty :=
  (sectionIdx S (lastSp S)).flatMap (fun j =>
    match S[j]? with
    | some R => R.gd.map (fun x => (x, j))
    | none => [])

theorem startup_D (sp : Spec V T) (ruleR : Bool) (S : Stream V T) :
    (startupWith sp ruleR S).D = sectionD S := rfl

/-! ### The invariant -/

/-- With a virtual root: z is a root child of P, with node n, created at time
c: an index node whose entries, of which there is at least one, are all at c. -/
def TopAt (sp : Spec V T) (P : Struct V) (z : NodeId) (n : Node V) (c : Time) : Prop :=
  P.get? z = some n ∧ z ≠ root ∧ sp.topLevel ≤ n.level ∧ n.isData = false ∧ n.hist ≠ [] ∧
    ∀ e ∈ n.hist, e.time = c

/-- What holds after every transaction k of a run with a virtual root
(`Spec.virt`; option (a) of Q7). Added 2026-10-16 (F1-008-11, WP E3). -/
structure VInv (sp : Spec V T) (db : DB V T) (k : Nat) : Prop where
  /-- R1 (from `VirtInit`, kept here for startup): the root's entry for a
  child points to that child. -/
  rootPtrs : ∀ z, sp.ptrs (sp.rootVal z) = [z]
  /-- The root is never in D and never written. -/
  rootND : inD db.D root = false
  rootNV : ∀ (r : Nat) (R : Record V T), db.S[r]? = some R → ∀ v ∈ R.vers, v.node ≠ root
  /-- The root: an index node, on its initial level. -/
  rootIdx : ∀ n, db.P.get? root = some n → n.isData = false ∧ n.level = rootLevel sp
  /-- Every root child was created at some time. -/
  tops : ∀ z, isTop sp db.P z = true → ∃ n c, TopAt sp db.P z n c
  /-- A version of a root child has the root child's whole history. -/
  topVers : ∀ z m c, TopAt sp db.P z m c → ∀ r w, db.S.versionAt r z = some w → w.hist = m.hist
  /-- The root's history: sorted by time, without two entries at one time; an
  entry at time c is for the root child created at c; every root child has its
  entry. -/
  rootSorted : ∀ n, db.P.get? root = some n → n.hist.Pairwise (fun e e' => e.time < e'.time)
  rootEntry : ∀ n, db.P.get? root = some n → ∀ e ∈ n.hist,
    ∃ z m, TopAt sp db.P z m e.time ∧ e.val = sp.rootVal z
  topEntry : ∀ z m c, TopAt sp db.P z m c → ∀ n, db.P.get? root = some n →
    (⟨c, sp.rootVal z⟩ : Entry V) ∈ n.hist
  /-- A root child points only to older root children (among the root children). -/
  older : ∀ z m c, TopAt sp db.P z m c → ∀ y ∈ pointees sp m.hist, isTop sp db.P y = true →
    ∃ m' c', TopAt sp db.P y m' c' ∧ c' < c
  /-- R4 holds now. -/
  closed : ∀ z m c y m' c', TopAt sp db.P z m c → TopAt sp db.P y m' c' → c' < c →
    y ∈ topClosure sp db.P z m
  /-- The latest version of a root child that did not stay dirty when it was
  written names the latest version of each root child it points to, and these
  are not in D. BergDB's still-dirty test, which looks at dead pointers too,
  gives this. -/
  fresh : ∀ z v, isTop sp db.P z = true → db.S.lv z = some v → (z, v.recNo) ∉ db.D →
    ∀ y ∈ pointees sp v.hist, isTop sp db.P y = true →
      inD db.D y = false ∧ v.ref? y = (db.S.lv y).map (·.recNo)

/-- What holds after every transaction k of a run. -/
structure Inv (sp : Spec V T) (db : DB V T) (k : Nat) : Prop where
  -- The stream.
  len : db.S.length = k + 1
  recNo : ∀ (r : Nat) (R : Record V T), db.S[r]? = some R → ∀ v ∈ R.vers, v.recNo = r
  versNodup : ∀ (r : Nat) (R : Record V T), db.S[r]? = some R → (R.vers.map (·.node)).Nodup
  spLt : lastSp db.S < k ∨ (k = 0 ∧ lastSp db.S = 0)
  vh : ∀ (r : Nat) (R : Record V T), db.S[r]? = some R → ∀ v ∈ R.vers,
    ∃ n, db.P.get? v.node = some n ∧ v.hist = n.hist.upTo r ∧ v.level = n.level ∧
      v.isData = n.isData
  ref : ∀ (r : Nat) (R : Record V T), db.S[r]? = some R → ∀ v ∈ R.vers,
    ∃ pre, pre <+: R.vers ∧ ∀ y, v.ref? y =
      if y ∈ pointees sp v.hist then ((Stream.building (db.S.take r) pre).lv y).map (·.recNo) else none
  top : ∀ R, db.S.getLast? = some R → R.top = topOf sp db.P db.S (lastSp db.S)
  -- The structure.
  times : ∀ x n, db.P.get? x = some n → ∀ e ∈ n.hist, e.time ≤ k
  ptrs : PtrsOK sp db.P
  data : ∀ x n, db.P.get? x = some n → n.isData = true → ∀ e ∈ n.hist, sp.ptrs e.val = []
  er : ∀ x n, db.P.get? x = some n → ∀ e ∈ n.hist, reachable sp db.P e.time x = true
  rootIn : (db.P.get? root).isSome
  born : ∀ x, (db.P.get? x).isSome → ∃ t ≤ k, reachable sp db.P t x = true
  -- D.
  inv1 : db.D = sectionD db.S
  dNodup : (db.D.map (·.1)).Nodup
  dIndex : ∀ e ∈ db.D, isIndex db.P e.1 = true
  inv2 : ∀ x, isIndex db.P x = true → written sp x = true → dirty sp db.S db.P k x = true →
    inD db.D x = true
  inv3 : ∀ x d v, (x, d) ∈ db.D → db.S.lv x = some v →
    d ≤ v.recNo ∨ ∀ t < d, reachable sp db.P t x = true → good sp db.S db.P t v = true
  inv4 : ∀ x d, (x, d) ∈ db.D → db.S.lv x = none → ∀ t < d, reachable sp db.P t x = false
  dataV : ∀ x n, db.P.get? x = some n → n.isData = true →
    ∃ v, db.S.lv x = some v ∧ v.hist = n.hist
  -- A virtual root.
  vr : sp.virt = true → VInv sp db k

end SIS
