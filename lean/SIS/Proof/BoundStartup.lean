/-
Proofs for one statement of bounded startup (bergdb item 007; 007-01 and
007-03): T3 as a count of transactions, T4 and a cold start's reads joined
(SIS/BoundStartupTheorems.lean). Added 2026-11-13.

The proof: `coldReadsJ_height_noD` bounds the reads by the section's
versions, its top-node header reads, the transactions of the section and the
merges' sibling follows. T3 (`T3_takeB_count`) bounds the transactions of a
section, after the run and after each of its prefixes; with that, the last
Hp + 1 sections hold at most (Hp + 1) N transactions, which bounds the debt D
after every prefix (`T4_debt_java_tree_height`). T4's record
(`T4_record_gd_height`) then bounds each record's versions and gd by a
transaction and the debt.
-/
import SIS.BoundColdReadsTheorems
import SIS.BoundT4GdTheorems
import SIS.BoundHeightTheorems
import SIS.BoundTakeBytesCountTheorems
import SIS.Proof.BoundT4

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Sums -/

theorem sum_map_le_mul {α : Type} (l : List α) (f : α → Nat) (c : Nat) (h : ∀ x ∈ l, f x ≤ c) :
    (l.map f).sum ≤ l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    rw [Nat.succ_mul]
    omega

/-! ### Prefixes of a run -/

theorem take_take_of_le (ts : List T) {t i : Nat} (h : t ≤ i) : (ts.take i).take t = ts.take t := by
  rw [List.take_take, Nat.min_eq_left h]

theorem runOK_take {sp : Spec V T} {al : Algo V T} {ts : List T} (hok : RunOK sp al ts) (i : Nat) :
    RunOK sp al (ts.take i) := by
  refine ⟨hok.1, ?_⟩
  intro j hj
  have hj' : j < ts.length := by rw [List.length_take] at hj; omega
  have hji : j ≤ i := by rw [List.length_take] at hj; omega
  have h := hok.2 j hj'
  simp only [List.getElem_take]
  rw [take_take_of_le ts hji]
  exact h

theorem treeRunOK_take {sp : Spec V T} {al : Algo V T} {ts : List T} (htree : TreeRunOK sp al ts)
    (i : Nat) : TreeRunOK sp al (ts.take i) := by
  intro j hj
  have hj' : j < ts.length := by rw [List.length_take] at hj; omega
  have hji : j + 1 ≤ i := by rw [List.length_take] at hj; omega
  rw [take_take_of_le ts hji]
  exact htree j hj'

theorem changeAt_take (sp : Spec V T) (al : Algo V T) (ts : List T) {i τ : Nat} (h : τ ≤ i) :
    changeAt sp al (ts.take i) τ = changeAt sp al ts τ := by
  cases τ with
  | zero => rfl
  | succ j =>
    have h1 : (ts.take i)[j]? = ts[j]? := by
      simp [show j < i by omega]
    simp only [changeAt, h1, take_take_of_le ts (show j ≤ i by omega)]

/-! ### The startup positions -/

/-- With every section of at most N transactions, the last n sections hold at
most n N. -/
theorem sub_spIter_le (S : Stream V T) (K N : Nat) (hle : ∀ j ≤ K, spAt S j ≤ j)
    (hN : ∀ j ≤ K, j - spAt S j ≤ N) : ∀ n j, j ≤ K → j - spIter S n j ≤ n * N
  | 0, j, _ => by simp [spIter]
  | n + 1, j, hj => by
    show j - spIter S n (spAt S j) ≤ (n + 1) * N
    have h1 := hle j hj
    have h2 := hN j hj
    have h3 := sub_spIter_le S K N hle hN n (spAt S j) (by omega)
    have h4 := spIter_le S K hle n (spAt S j) (by omega)
    rw [Nat.succ_mul]
    omega

/-- T3 in transactions, as a bound N. -/
theorem sec_len_le (L M m : Nat) (hm : 0 < m) (h : (L - 2) * m < 2 * M ∨ L ≤ 1) :
    L ≤ 2 * M / m + 2 := by
  rcases h with h | h
  · have h1 : L - 2 < 2 * M / m + 1 := by
      apply Nat.lt_of_not_le
      intro hc
      have h2 : (2 * M / m + 1) * m ≤ (L - 2) * m := Nat.mul_le_mul_right m hc
      have h3 := Nat.div_add_mod (2 * M) m
      have h4 := Nat.mod_lt (2 * M) hm
      rw [Nat.succ_mul, Nat.mul_comm] at h2
      omega
    generalize 2 * M / m = q at h1 ⊢
    omega
  · generalize 2 * M / m = q
    omega

section T3

variable (sp : Spec V T) (al : Algo V T) (size : Record V T → Nat) (sd : Time → Nat)
  (pace : Pace V T) (nodeB maxB : Nat) (M m : Nat) (ts : List T)

/-- T3 for every prefix of the run: the section after T(j) has at most
N = 2 M / m + 2 transactions. -/
theorem sec_prefix_le (hp : al.policy = takePolicyB size sd pace nodeB maxB) (hm0 : 0 < m)
    (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R)
    (hfit : ∀ j < ts.length, ∀ τ,
      ((run sp al (ts.take j)).D.filter (fun e => e.2 == τ)).length * nodeB ≤ maxB)
    (j : Nat) (hj : j ≤ ts.length) :
    (sectionIdx (run sp al (ts.take j)).S (lastSp (run sp al (ts.take j)).S)).length ≤
      2 * M / m + 2 := by
  apply sec_len_le _ M m hm0
  have hpre : (run sp al (ts.take j)).S <+: (run sp al ts).S := by
    have := st_S_prefix (sp := sp) (al := al) (ts := ts) hj (Nat.le_refl _)
    rw [st_length] at this
    exact this
  have h := T3_takeB_count sp al size sd pace nodeB maxB hp M m (ts.take j)
    (fun i hi hil => hM i hi (by rw [List.length_take] at hil; omega))
    (fun R hR => hm R (hpre.subset hR))
    (fun j' hj' τ => by
      have hj'' : j' ≤ j := by rw [List.length_take] at hj'; omega
      rw [take_take_of_le ts hj'']
      exact hfit j' (by rw [List.length_take] at hj'; omega) τ)
  exact h

variable {sp al ts}

/-- T4's debt after every prefix of the run, by T3: the last Hp + 1 sections
hold at most (Hp + 1) N transactions, each of at most (H + 1) A nodes on the
access paths of its change. -/
theorem debt_prefix_le (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (htree : TreeRunOK sp al ts)
    (hp : al.policy = takePolicyB size sd pace nodeB maxB) (hm0 : 0 < m)
    (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R)
    (hfit : ∀ j < ts.length, ∀ τ,
      ((run sp al (ts.take j)).D.filter (fun e => e.2 == τ)).length * nodeB ≤ maxB)
    (H Hp Q A : Nat)
    (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root)
    (hHp : ∀ t ≤ ts.length, ∀ e ∈ (run sp al (ts.take t)).D,
      PtrHeightLe sp (run sp al (ts.take t)).P Hp e.1)
    (hQ : ∀ t ≤ ts.length, ∀ z, (ptrParents sp (run sp al (ts.take t)).P z).length ≤ Q)
    (hA : ∀ τ, 0 < τ → τ ≤ ts.length →
      (changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length +
        (changeAt sp al ts τ).touch.length ≤ A)
    (i : Nat) (hi : i ≤ ts.length) :
    (run sp al (ts.take i)).D.length ≤
      geomSum Q Hp * ((Hp + 1) * (2 * M / m + 2) * ((H + 1) * A)) := by
  have hst := algOK_of sp al (Or.inl hj)
  have hlen : (ts.take i).length = i := by rw [List.length_take]; omega
  have h := T4_debt_java_tree_height sp al (ts.take i) (runOK_take hok i) hj
    (treeRunOK_take htree i) Hp H Q (hHp i hi)
    (fun t ht => by
      rw [hlen] at ht
      rw [take_take_of_le ts ht]
      exact hH t (by omega))
    (hQ i hi)
  simp only [hlen] at h
  -- The startup positions of the prefix's stream.
  have hle : ∀ j ≤ i, spAt (run sp al (ts.take i)).S j ≤ j :=
    spAt_st_le (sp := sp) (al := al) (ts := ts) hok hst hi
  have hN : ∀ j ≤ i, j - spAt (run sp al (ts.take i)).S j ≤ 2 * M / m + 2 := by
    intro j hji
    have h1 : spAt (run sp al (ts.take i)).S j = lastSp (run sp al (ts.take j)).S :=
      spAt_st (sp := sp) (al := al) (ts := ts) hok hst hi hji
    have h2 := sec_prefix_le sp al size sd pace nodeB maxB M m ts hp hm0 hM hm hfit j (by omega)
    have h3 : (run sp al (ts.take j)).S.length = j + 1 :=
      st_len (sp := sp) (al := al) (ts := ts) hok hst (by omega)
    rw [h1]
    unfold sectionIdx at h2
    rw [List.length_range', h3] at h2
    omega
  have hsub := sub_spIter_le (run sp al (ts.take i)).S i (2 * M / m + 2) hle hN (Hp + 1) i
    (Nat.le_refl _)
  generalize hag : spIter (run sp al (ts.take i)).S (Hp + 1) i = a at h hsub
  have hsum : ((List.range' (a + 1) (i - a)).map (fun τ =>
        (H + 1) * ((changeAt sp al (ts.take i) τ).new.length +
          (changeAt sp al (ts.take i) τ).adds.length) +
          (changeAt sp al (ts.take i) τ).touch.length)).sum ≤ (i - a) * ((H + 1) * A) := by
    have := sum_map_le_mul (List.range' (a + 1) (i - a)) (fun τ =>
        (H + 1) * ((changeAt sp al (ts.take i) τ).new.length +
          (changeAt sp al (ts.take i) τ).adds.length) +
          (changeAt sp al (ts.take i) τ).touch.length) ((H + 1) * A) (by
      intro τ hτ
      rw [List.mem_range'_1] at hτ
      rw [changeAt_take sp al ts (by omega : τ ≤ i)]
      have h1 := hA τ (by omega) (by omega)
      have h2 : (H + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length) +
          (changeAt sp al ts τ).touch.length ≤
          (H + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length +
            (changeAt sp al ts τ).touch.length) := by
        rw [Nat.mul_add (H + 1) _ ((changeAt sp al ts τ).touch.length)]
        have : (changeAt sp al ts τ).touch.length ≤ (H + 1) * (changeAt sp al ts τ).touch.length :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      exact Nat.le_trans h2 (Nat.mul_le_mul_left _ h1))
    rw [List.length_range'] at this
    exact this
  have h3 : (i - a) * ((H + 1) * A) ≤ (Hp + 1) * (2 * M / m + 2) * ((H + 1) * A) :=
    Nat.mul_le_mul_right _ hsub
  exact Nat.le_trans h (Nat.mul_le_mul_left _ (Nat.le_trans hsum h3))

end T3

/-! ### T4's record of each transaction -/

theorem changeAt_succ_exec (sp : Spec V T) (al : Algo V T) (ts : List T) {i : Nat} (hi : i < ts.length) :
    changeAt sp al ts (i + 1) = sp.exec ts[i] (i + 1) (view sp (run sp al (ts.take i)).P i) := by
  simp [changeAt, List.getElem?_eq_getElem hi]

/-- T4's record R(i + 1), with the debt before it at most Dm and T(i + 1) of at
most A nodes and entries: R(i + 1) holds T(i + 1), at most A + Dm versions,
and a gd of at most (H + 1) A + Dm ids. -/
theorem record_le {sp : Spec V T} {al : Algo V T} {ts : List T} (hok : RunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (htree : TreeRunOK sp al ts) (H A Dm : Nat)
    (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root)
    (hA : ∀ τ, 0 < τ → τ ≤ ts.length →
      (changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length +
        (changeAt sp al ts τ).touch.length ≤ A)
    (hD : ∀ i ≤ ts.length, (run sp al (ts.take i)).D.length ≤ Dm)
    (i : Nat) (hi : i < ts.length) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ R.trans = some ts[i] ∧
      R.vers.length ≤ A + Dm ∧ R.gd.length ≤ (H + 1) * A + Dm := by
  obtain ⟨R, hR, hRB, hgd⟩ := T4_record_gd_height sp al ts hok (Or.inl hj) i hi (htree i hi) H
    (hH (i + 1) (by omega))
  have hlen : (run sp al (ts.take i)).S.length = i + 1 := by
    rw [run_length, List.length_take]; omega
  obtain ⟨htr, -, hvers, -⟩ := hRB
  simp only [hlen, Nat.add_sub_cancel] at hvers
  rw [← changeAt_succ_exec sp al ts hi] at hvers
  have hA' := hA (i + 1) (by omega) (by omega)
  have hDi := hD i (by omega)
  have hf : ((changeAt sp al ts (i + 1)).new.filter (·.isData)).length ≤
      (changeAt sp al ts (i + 1)).new.length := List.length_filter_le _ _
  refine ⟨R, hR, htr, by omega, ?_⟩
  have h2 : (H + 1) * ((changeAt sp al ts (i + 1)).new.length +
      (changeAt sp al ts (i + 1)).adds.length) + (changeAt sp al ts (i + 1)).touch.length ≤
      (H + 1) * A := by
    have h3 : (changeAt sp al ts (i + 1)).touch.length ≤
        (H + 1) * (changeAt sp al ts (i + 1)).touch.length := Nat.le_mul_of_pos_left _ (by omega)
    have h4 := Nat.mul_le_mul_left (H + 1) hA'
    rw [Nat.mul_add (H + 1) _ ((changeAt sp al ts (i + 1)).touch.length)] at h4
    omega
  omega

/-! ### The versions a start finds -/

theorem newest_mem {S : Stream V T} {s : Nat} {x : NodeId} {w : Version V}
    (h : newest S s x = some w) : (∃ R ∈ S, w ∈ R.vers) ∧ w.node = x := by
  unfold newest at h
  obtain ⟨R, hR, hf⟩ := List.exists_of_findSome?_eq_some h
  have hx := List.find?_some hf
  simp only [beq_iff_eq] at hx
  exact ⟨⟨R, List.mem_of_mem_drop (List.mem_reverse.mp hR), List.mem_of_find?_eq_some hf⟩, hx⟩

theorem lv_mem {S : Stream V T} {x : NodeId} {w : Version V}
    (h : S.lv x = some w) : (∃ R ∈ S, w ∈ R.vers) ∧ w.node = x := by
  unfold Stream.lv at h
  obtain ⟨R, hR, hf⟩ := List.exists_of_findSome?_eq_some h
  have hx := List.find?_some hf
  simp only [beq_iff_eq] at hx
  exact ⟨⟨R, List.mem_reverse.mp hR, List.mem_of_find?_eq_some hf⟩, hx⟩

theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 := h a List.mem_cons_self
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

/-- Rule 4's top-node header reads: at most Pt for each id of a section's gd,
with every version of a top node in the stream (a node other than the root on
level `topLevel` or above) pointing to at most Pt nodes. -/
theorem topHeaderReads_le (sp : Spec V T) (S : Stream V T) (s Pt : Nat)
    (hPt : ∀ R ∈ S, ∀ v ∈ R.vers, v.node ≠ root → sp.topLevel ≤ v.level →
      (pointees sp v.hist).length ≤ Pt) :
    topHeaderReads sp S s ≤ ((sectionIdx S s).map (fun j =>
      match S[j]? with
      | some R => R.gd.length * Pt
      | none => 0)).sum := by
  unfold topHeaderReads
  apply sum_map_le_sum_map
  intro j _
  cases hS : S[j]? with
  | none => simp
  | some R =>
    simp only
    apply sum_map_le_mul
    intro x _
    cases hw : (newest S s x).or (S.lv x) with
    | none => simp
    | some w =>
      simp only
      have hmem : (∃ R ∈ S, w ∈ R.vers) ∧ w.node = x := by
        cases hn : newest S s x with
        | some w' =>
          rw [hn] at hw
          simp only [Option.some_or, Option.some.injEq] at hw
          subst hw
          exact newest_mem hn
        | none =>
          rw [hn] at hw
          simp only [Option.none_or] at hw
          exact lv_mem hw
      obtain ⟨⟨R', hR', hw'⟩, hwx⟩ := hmem
      split
      · rename_i hc
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hc
        exact hPt R' hR' w hw' (by rw [hwx]; exact hc.1.2) hc.2
      · exact Nat.zero_le _

/-! ### The statement -/

theorem bounded_startup_of (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (size : Record V T → Nat) (sd : Time → Nat) (pace : Pace V T) (nodeB maxB : Nat)
    (hp : al.policy = takePolicyB size sd pace nodeB maxB)
    (M m : Nat) (hm0 : 0 < m) (hM : ∀ i, 0 < i → i ≤ ts.length → sd i ≤ M)
    (hm : ∀ R ∈ (run sp al ts).S, m ≤ size R)
    (hfit : ∀ j < ts.length, ∀ τ,
      ((run sp al (ts.take j)).D.filter (fun e => e.2 == τ)).length * nodeB ≤ maxB)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root)
    (Hp Q : Nat)
    (hHp : ∀ t ≤ ts.length, ∀ e ∈ (run sp al (ts.take t)).D,
      PtrHeightLe sp (run sp al (ts.take t)).P Hp e.1)
    (hQ : ∀ t ≤ ts.length, ∀ z, (ptrParents sp (run sp al (ts.take t)).P z).length ≤ Q)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (sib : T → Nat) (A K B Pt V0 : Nat)
    (hA : ∀ τ, 0 < τ → τ ≤ ts.length →
      (changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length +
        (changeAt sp al ts τ).touch.length + ((changeAt sp al ts τ).adds.map (fun a => w a.2)).sum ≤ A)
    (hK : ∀ τ, 0 < τ → τ ≤ ts.length → k τ ≤ K)
    (hB : ∀ tr ∈ ts, sib tr ≤ B)
    (hPt : ∀ R ∈ (run sp al ts).S, ∀ v ∈ R.vers, v.node ≠ root → sp.topLevel ≤ v.level →
      (pointees sp v.hist).length ≤ Pt)
    (hV0 : ∀ R ∈ (run sp al []).S, R.vers.length ≤ V0) :
    lazyReads sp sib (run sp al ts).S ≤
      (2 * M / m + 3) * (V0 + A + geomSum Q Hp * ((Hp + 1) * (2 * M / m + 2) * ((H + 1) * A))) + 2 +
      (2 * M / m + 2) * (((H + 1) * A +
        geomSum Q Hp * ((Hp + 1) * (2 * M / m + 2) * ((H + 1) * A))) * Pt) +
      2 * ((2 * M / m + 2) * ((H + 1) * (A + K))) + 2 * ((2 * M / m + 2) * B) := by
  have hst := algOK_of sp al (Or.inl hj)
  have hA3 : ∀ τ, 0 < τ → τ ≤ ts.length →
      (changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length +
        (changeAt sp al ts τ).touch.length ≤ A := fun τ h1 h2 => by
    have := hA τ h1 h2; omega
  have hD := debt_prefix_le size sd pace nodeB maxB M m hok hj htree hp hm0 hM hm hfit H Hp Q A
    hH hHp hQ hA3
  generalize hDm : geomSum Q Hp * ((Hp + 1) * (2 * M / m + 2) * ((H + 1) * A)) = Dm at hD ⊢
  generalize hN : 2 * M / m + 2 = N at hD ⊢
  have hN3 : 2 * M / m + 3 = N + 1 := by omega
  rw [hN3]
  have hrec := record_le hok hj htree H A Dm hH hA3 hD
  have h1 := coldReadsJ_height_noD sp al sib ts hok hla hj htree0 htree w k hdrop H hH
  simp only at h1
  have hSlen : (run sp al ts).S.length = ts.length + 1 := run_length sp al ts
  -- T3: the section has at most N transactions.
  have hsec : (sectionIdx (run sp al ts).S (lastSp (run sp al ts).S)).length ≤ N := by
    have := sec_prefix_le sp al size sd pace nodeB maxB M m ts hp hm0 hM hm hfit ts.length
      (Nat.le_refl _)
    rw [List.take_length] at this
    omega
  generalize hS : (run sp al ts).S = S at h1 hsec hSlen hrec hPt
  generalize hs : lastSp S = s at h1 hsec
  have hmem : ∀ j ∈ sectionIdx S s, 0 < j ∧ j ≤ ts.length := by
    intro j hj
    unfold sectionIdx at hj
    rw [List.mem_range'_1] at hj
    omega
  generalize hL : (sectionIdx S s).length = L at hsec
  -- Every version of the section.
  have hV : sectionVersions S s ≤ (N + 1) * (V0 + A + Dm) := by
    unfold sectionVersions
    have hall : ∀ R ∈ S.drop s, R.vers.length ≤ V0 + A + Dm := by
      intro R hR
      obtain ⟨j, hjl, hjR⟩ := List.mem_iff_getElem.mp (List.mem_of_mem_drop hR)
      cases j with
      | zero =>
        have hpre : (run sp al []).S <+: S := by
          have := st_S_prefix (sp := sp) (al := al) (ts := ts) (Nat.zero_le ts.length)
            (Nat.le_refl _)
          rw [st_length] at this
          rw [← hS]
          exact this
        have h0 : 0 < (run sp al []).S.length := by rw [run_length]; omega
        have hR0 : (run sp al []).S[0] = S[0] := hpre.getElem h0
        have := hV0 _ (List.getElem_mem h0)
        rw [hR0, hjR] at this
        omega
      | succ i =>
        obtain ⟨R', hR', -, hv, -⟩ := hrec i (by omega)
        rw [List.getElem?_eq_getElem hjl, hjR, Option.some.injEq] at hR'
        subst hR'
        omega
    have := sum_map_le_mul (S.drop s) (fun R => R.vers.length) (V0 + A + Dm) hall
    rw [List.length_drop] at this
    have hlen : S.length - s ≤ N + 1 := by
      unfold sectionIdx at hL
      rw [List.length_range'] at hL
      omega
    exact Nat.le_trans this (Nat.mul_le_mul_right _ hlen)
  -- Rule 4's top-node header reads.
  have hT : topHeaderReads sp S s ≤ N * (((H + 1) * A + Dm) * Pt) := by
    have h2 := topHeaderReads_le sp S s Pt hPt
    have h3 := sum_map_le_mul (sectionIdx S s) (fun j =>
      match S[j]? with
      | some R => R.gd.length * Pt
      | none => 0) (((H + 1) * A + Dm) * Pt) (by
        intro j hj
        obtain ⟨hj0, hj1⟩ := hmem j hj
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        obtain ⟨R, hR, -, -, hg⟩ := hrec i (by omega)
        simp only [hR]
        exact Nat.mul_le_mul_right _ hg)
    rw [hL] at h3
    exact Nat.le_trans h2 (Nat.le_trans h3 (Nat.mul_le_mul_right _ hsec))
  -- The transactions of the section.
  have hX : ((sectionIdx S s).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j))).sum ≤
      N * ((H + 1) * (A + K)) := by
    have h3 := sum_map_le_mul (sectionIdx S s) (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j)) ((H + 1) * (A + K)) (by
        intro j hj
        obtain ⟨hj0, hj1⟩ := hmem j hj
        apply Nat.mul_le_mul_left
        have := hA j hj0 hj1
        have := hK j hj0 hj1
        omega)
    rw [hL] at h3
    exact Nat.le_trans h3 (Nat.mul_le_mul_right _ hsec)
  -- The merges' sibling follows.
  have hSib : sibReach sib S ≤ N * B := by
    unfold sibReach
    rw [hs]
    have h3 := sum_map_le_mul (sectionIdx S s) (fun j =>
      match S[j]? with
      | some R => match R.trans with
        | some tr => sib tr
        | none => 0
      | none => 0) B (by
        intro j hj
        obtain ⟨hj0, hj1⟩ := hmem j hj
        obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
        obtain ⟨R, hR, htr, -, -⟩ := hrec i (by omega)
        simp only [hR, htr]
        exact hB _ (List.getElem_mem _))
    rw [hL] at h3
    exact Nat.le_trans h3 (Nat.mul_le_mul_right _ hsec)
  omega

end SIS
