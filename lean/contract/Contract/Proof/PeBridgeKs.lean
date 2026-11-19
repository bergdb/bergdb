/-
bergdb 030-21, part 2: the bridge's clauses for the klongs that PE's emit
writes (Bridge.lean, section 3.3), and what a sound shaped node reaches
(section 3.4), for PeBridge.lean.

* W5 (`fullOk`) is kept by emit (`fullOk_emitKs`): the one bitmap emit
  writes is the last one and every key klong of each compare value removed,
  and an old bitmap's bits are below its index (W2), so its check does not
  look at the klongs appended. A new node has no bitmap (`fullOk_newKs`), nor
  has the start's space root (`fullOk_start`).
* F4: an old node that emit extends gets a time klong of i and more after
  it, no time klong among them (`extKs4_emitKs`); a new node's klongs are a
  time klong of i and key klongs (`madeKs_newKs`).
* Along `Rch` from a node that is `Good` and `Shaped`, every node reached is
  in the walk from it with its fuel or more (`rch_reachAt`), and every key
  node reached has its live klongs pointing to nodes of lower levels
  (`rch_live_low`: a shaped node's level is at least 1, above a value's 0).
-/
import Contract.Bridge
import Contract.Proof.Prefix
import Contract.Proof.PeSeg

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg}

/-! ## The start -/

theorem fullOk_start : fullOk [Klong.time 0] = true := by decide

/-! ## F4 -/

/-- emit's klongs: a time klong of i, a bitmap if a compare value is removed,
and the key klongs of the entries added. -/
theorem emitKs_cons (i : Time) (ks : List Klong) (F : List (Nat × NodeId)) :
    emitKs i ks F = .time i :: ((if (removedCvs (live ks) F).isEmpty then [] else
      [.del (emitBits ks (removedCvs (live ks) F))]) ++ keysOf (addedOf (live ks) F)) := by
  unfold emitKs emitHead
  split <;> simp

theorem keysOf_notTime (A : List (Nat × NodeId)) : ∀ k ∈ keysOf A, k.isTime = false := by
  intro k hk
  simp only [keysOf, List.mem_map] at hk
  obtain ⟨a, _, rfl⟩ := hk
  rfl

theorem madeKs_newKs (i : Time) (F : List (Nat × NodeId)) : madeKs i (newKs i F) = true := by
  simp only [newKs, madeKs, beq_self_eq_true, Bool.true_and, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  exact keysOf_notTime F

theorem madeKs_emitKs (i : Time) (ks : List Klong) (F : List (Nat × NodeId)) :
    madeKs i (emitKs i ks F) = true := by
  rw [emitKs_cons]
  simp only [madeKs, beq_self_eq_true, Bool.true_and, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true]
  intro k hk
  rcases List.mem_append.mp hk with h | h
  · split at h
    · simp at h
    · simp only [List.mem_singleton] at h
      subst h; rfl
  · exact keysOf_notTime _ k h

theorem extKs4_emitKs {ks : List Klong} {i : Time} {F : List (Nat × NodeId)}
    (h : emitKs i ks F ≠ [.time i]) : extKs4 i ks (ks ++ emitKs i ks F) = true := by
  unfold extKs4
  rw [Bool.or_eq_true]
  right
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.drop_left, List.length_append]
  refine ⟨⟨List.isPrefixOf_iff_prefix.mpr (List.prefix_append ks _), madeKs_emitKs i ks F⟩, ?_⟩
  rw [emitKs_cons] at h ⊢
  revert h
  generalize ((if (removedCvs (live ks) F).isEmpty then [] else
      [Klong.del (emitBits ks (removedCvs (live ks) F))]) ++ keysOf (addedOf (live ks) F)) = r
  intro h
  cases r with
  | nil => exact absurd rfl h
  | cons k r => simp

/-! ## W5 -/

/-- W5 holds if every bitmap meets `bmFull` (`fullFold_of`). -/
theorem fullOk_of {ks : List Klong}
    (h : ∀ l1 b l2, ks = l1 ++ Klong.del b :: l2 → bmFull ks l1.length (lastBitmap l1) b = true) :
    fullOk ks = true :=
  fullFold_of ks ks h

/-- `bmFull` of a bitmap whose bits are below its index looks only at the
klongs before it. -/
theorem bmFull_extend {p q : List Klong} {i : Nat} (hi : i ≤ p.length) {before bits : List Nat}
    (hb : ∀ j ∈ bits, j < i) (h : bmFull p i before bits = true) :
    bmFull (p ++ q) i before bits = true := by
  have hcv : ∀ j, j < i → cvAt (p ++ q) j = cvAt p j :=
    fun j hj => Contract.cvAt_append_left p q (by omega)
  simp only [bmFull, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.mem_range,
    bne_iff_ne, ne_eq] at h ⊢
  intro j hj
  rcases h j hj with h1 | h1
  · exact Or.inl h1
  · right
    intro j' hj'
    rw [hcv j (hb j hj), hcv j' hj']
    exact h1 j' hj'

theorem fullOk_newKs (i : Time) (F : List (Nat × NodeId)) : fullOk (newKs i F) = true := by
  apply fullOk_of
  intro l1 b l2 he
  have hm : Klong.del b ∈ newKs i F := by rw [he]; simp
  simp [newKs, keysOf] at hm

/-- The one bitmap among emit's klongs: after its time klong, the bitmap
`emitBits`. -/
theorem emitKs_del {i : Time} {ks : List Klong} {F : List (Nat × NodeId)} {a l2 : List Klong}
    {b : List Nat} (he : emitKs i ks F = a ++ Klong.del b :: l2) :
    a = [.time i] ∧ b = emitBits ks (removedCvs (live ks) F) := by
  have hk : ∀ {a' l2' : List Klong}, keysOf (addedOf (live ks) F) ≠ a' ++ Klong.del b :: l2' := by
    intro a' l2' h
    have hm : Klong.del b ∈ keysOf (addedOf (live ks) F) := by rw [h]; simp
    simp [keysOf] at hm
  rw [emitKs_cons] at he
  cases a with
  | nil => simp at he
  | cons x a =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    split at he
    · simp only [List.nil_append] at he
      exact absurd he hk
    · cases a with
      | nil =>
        simp only [List.singleton_append, List.nil_append, List.cons.injEq, Klong.del.injEq] at he
        exact ⟨rfl, he.1.symm⟩
      | cons y a =>
        simp only [List.cons_append, List.cons.injEq] at he
        exact absurd he.2 hk

/-- **W5 is kept by emit.** -/
theorem fullOk_emitKs {ks : List Klong} (hwf : klongsWf ks = true) (hf : fullOk ks = true)
    (i : Time) (F : List (Nat × NodeId)) : fullOk (ks ++ emitKs i ks F) = true := by
  apply fullOk_of
  intro l1 b l2 he
  rcases List.append_eq_append_iff.mp he with ⟨a, hl1, hE⟩ | ⟨c', hks, hd⟩
  · -- the bitmap emit writes
    obtain ⟨rfl, rfl⟩ := emitKs_del hE
    subst hl1
    rw [lastBitmap_snoc]
    simp only [bmFull, List.all_eq_true, Bool.or_eq_true, List.contains_iff_mem, List.mem_range,
      bne_iff_ne, ne_eq, List.length_append, List.length_singleton]
    intro j hj
    unfold emitBits at hj
    rcases List.mem_append.mp hj with h1 | h1
    · exact Or.inl h1
    · right
      obtain ⟨c, hc, hjc⟩ := mem_bitsIn.mp h1
      have hjl := cvAt_lt hjc
      intro j' hj'
      rw [Contract.cvAt_append_left _ _ hjl, hjc]
      by_cases hj'l : j' < ks.length
      · rw [Contract.cvAt_append_left _ _ hj'l]
        by_cases heq : cvAt ks j' = some c
        · exact Or.inr (List.mem_append_right _ (mem_bitsIn.mpr ⟨c, hc, heq⟩))
        · exact Or.inl heq
      · have : j' = ks.length := by omega
        subst this
        left
        rw [emitKs_cons]
        simp [cvAt]
  · -- an old bitmap
    cases c' with
    | nil =>
      simp only [List.nil_append] at hd
      rw [emitKs_cons] at hd
      simp at hd
    | cons x c' =>
      simp only [List.cons_append, List.cons.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      have hks' : ks = l1 ++ Klong.del b :: c' := hks
      have hb := (bmW_of_wf hwf l1 b c' hks').1
      have hfull := (fullFold_spec ks ks).2 hf l1 b c' hks'
      exact bmFull_extend (by rw [hks']; simp) hb hfull

/-! ## What a sound shaped node reaches -/

/-- From a value, `Rch` goes nowhere. -/
theorem rch_val {T : Tree} {z y : NodeId} {v : Nat} (hz : T.obj z = some (.val v))
    (hr : Rch T z y) : y = z := by
  cases hr with
  | refl => rfl
  | step hx _ _ => rw [hz] at hx; cases hx

/-- Every node a sound node reaches through live klongs is in the walk from it
with its fuel or more. -/
theorem rch_reachAt_good {T : Tree} {x y : NodeId} (hr : Rch T x y) :
    ∀ {lo : Nat} {hi : Option Nat}, Good T x lo hi → ∀ f, T.fuel x ≤ f → y ∈ reachAt T f x := by
  induction hr with
  | refl x => intro _ _ _ f _; exact mem_reachAt_self' T f x
  | @step x z y n c hx hc hr ih =>
    intro lo hi hg f hf
    have hfu : T.fuel x = n.level + 1 := by simp [Tree.fuel, hx]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [reachAt_key hx, List.mem_cons, List.mem_flatMap]
    right
    refine ⟨(c, z), hc, ?_⟩
    rcases good_kids hg hx c z hc with ⟨m, hm, hlt, lo', hi', hg'⟩ | ⟨v, hv⟩
    · have hfz : T.fuel z = m.level + 1 := by simp [Tree.fuel, hm]
      exact ih hg' f' (by omega)
    · rw [rch_val hv hr]
      exact mem_reachAt_self' T f' z

/-- **What a sound shaped node reaches is in its walk** (the shape is not
needed: `rch_reachAt_good`; it is a premise as in `rch_live_low`). -/
theorem rch_reachAt {T : Tree} {x y : NodeId} {lo : Nat} {hi : Option Nat} {g h : Nat}
    (hg : Good T x lo hi) (hsh : Shaped cf T g h x) (hr : Rch T x y) :
    ∀ f, T.fuel x ≤ f → y ∈ reachAt T f x := by
  have _ := hsh
  exact rch_reachAt_good hr hg

/-- A live child of a sound shaped node: a sound shaped key node, or a value. -/
theorem kid_good {T : Tree} {x z : NodeId} {n : KNode} {c : Nat} {lo : Nat} {hi : Option Nat}
    {g h : Nat} (hg : Good T x lo hi) (hsh : Shaped cf T g h x) (hx : T.obj x = some (.key n))
    (hc : (c, z) ∈ live n.ks) :
    (∃ lo' hi' g' h', Good T z lo' hi' ∧ Shaped cf T g' h' z) ∨ ∃ v, T.obj z = some (.val v) := by
  cases hg with
  | mk _ _ _ n' hobj _ _ _ hval _ hseg hkid =>
    rw [hx] at hobj
    obtain rfl : n = n' := by injection hobj with h1; injection h1
    cases hsh with
    | leaf hobj' hleaf _ _ hlong =>
      rw [hx] at hobj'
      obtain rfl : n = _ := by injection hobj' with h1; injection h1
      by_cases hl : isLong c = true
      · exact Or.inl ⟨0, none, _, _, hseg hleaf c z hc hl, hlong c z hc hl⟩
      · exact Or.inr (hval hleaf c z hc (by simpa using hl))
    | inner hobj' hleaf _ _ _ _ hkids =>
      rw [hx] at hobj'
      obtain rfl : n = _ := by injection hobj' with h1; injection h1
      obtain ⟨pre, post, he⟩ := List.append_of_mem hc
      exact Or.inl ⟨_, _, _, _, hkid (by simpa using hleaf) pre c z post he, hkids c z hc⟩

/-- Along `Rch` from a sound shaped node: a sound shaped key node, or a value. -/
theorem rch_good {T : Tree} {x y : NodeId} (hr : Rch T x y) :
    ∀ {lo : Nat} {hi : Option Nat} {g h : Nat}, Good T x lo hi → Shaped cf T g h x →
      (∃ lo' hi' g' h', Good T y lo' hi' ∧ Shaped cf T g' h' y) ∨ ∃ v, T.obj y = some (.val v) := by
  induction hr with
  | refl x => intro lo hi g h hg hsh; exact Or.inl ⟨lo, hi, g, h, hg, hsh⟩
  | @step x z y n c hx hc hr ih =>
    intro lo hi g h hg hsh
    rcases kid_good hg hsh hx hc with ⟨lo', hi', g', h', hg', hsh'⟩ | ⟨v, hv⟩
    · exact ih hg' hsh'
    · rw [rch_val hv hr]
      exact Or.inr ⟨v, hv⟩

/-- **A key node a sound shaped node reaches points lower**: every live klong
of it names a node of a lower level. -/
theorem rch_live_low {T : Tree} {x y : NodeId} {lo : Nat} {hi : Option Nat} {g h : Nat}
    (hg : Good T x lo hi) (hsh : Shaped cf T g h x) (hr : Rch T x y) {m : KNode}
    (hy : T.obj y = some (.key m)) :
    ∀ c z, (c, z) ∈ live m.ks → ∃ o, T.obj z = some o ∧ lvl o < m.level := by
  intro c z hc
  rcases rch_good hr hg hsh with ⟨lo', hi', g', h', hg', hsh'⟩ | ⟨v, hv⟩
  · obtain ⟨m', hm', hlev, _⟩ := shaped_obj hsh'
    rw [hy] at hm'
    obtain rfl : m = m' := by injection hm' with h1; injection h1
    rcases good_kids hg' hy c z hc with ⟨m'', hz, hlt, _⟩ | ⟨v, hv⟩
    · exact ⟨_, hz, hlt⟩
    · refine ⟨_, hv, ?_⟩
      simp only [lvl, hlev, Cfg.lev]
      omega
  · rw [hy] at hv; cases hv

end Contract.PE
