/-
bergdb 030-37: dead-klong counting ignores pointees. The decision made
with symbolic fresh pointers therefore has the count of the emitted node.
-/
import Contract.Proof.DnbFillHistory

namespace Contract.PE

open DNB PeProof PeProof.Abs

/-- Erase only a key klong's pointee. -/
def erasePtr : Klong → Klong
  | .key c _ => .key c 0
  | k => k

theorem lastBitmap_erasePtr (ks : List Klong) :
    lastBitmap (ks.map erasePtr) = lastBitmap ks := by
  unfold lastBitmap
  rw [List.foldl_map]
  congr 1
  funext d k
  cases k <;> rfl

theorem deadCount_erasePtr (ks : List Klong) :
    deadCount (ks.map erasePtr) = deadCount ks := by
  simp only [deadCount]
  rw [lastBitmap_erasePtr, List.zipIdx_map, List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro ki hki
  obtain ⟨k, j⟩ := ki
  simp only [Function.comp_apply, Prod.map, id_eq]
  cases k with
  | time t => rfl
  | del bits => rfl
  | key c y =>
    simp only [erasePtr, ← List.map_drop, List.any_map]
    congr 1
    apply List.any_congr rfl
    intro k
    cases k <;> rfl

/-- No compare value occurs twice as a key klong. -/
def DistinctKeys (ks : List Klong) : Prop :=
  ks.Pairwise (fun a b => ∀ c x y, a = .key c x → b ≠ .key c y)

theorem deadCount_zero {ks : List Klong} (hb : lastBitmap ks = []) (hd : DistinctKeys ks) :
    deadCount ks = 0 := by
  simp only [deadCount, hb, List.contains_nil, Bool.false_or]
  apply List.length_eq_zero_iff.mpr
  rw [List.filter_eq_nil_iff]
  rintro ⟨k, j⟩ hm
  obtain ⟨_, hj, hkj⟩ := List.mem_zipIdx hm
  simp only [Nat.zero_add, Nat.sub_zero] at hj hkj
  cases k with
  | time t => simp
  | del bits => simp
  | key c x =>
    intro ha
    obtain ⟨k', hk', he⟩ := List.any_eq_true.mp ha
    cases k' with
    | time t => cases he
    | del bits => cases he
    | key c' y =>
      have hc : c' = c := by simpa using he
      subst c'
      obtain ⟨t, ht, hkt⟩ := List.mem_drop_iff_getElem.mp hk'
      have hrel := List.pairwise_iff_getElem.mp hd j (j + 1 + t) hj (by omega) (by omega)
      exact hrel c x y hkj.symm hkt

theorem deadCount_newKs {i : Time} {F : List (Nat × NodeId)} (hF : F.Pairwise CvLtA) :
    deadCount (newKs i F) = 0 := by
  apply deadCount_zero
  · simp [newKs, keysOf, lastBitmap, List.foldl_map]
  · simp only [DistinctKeys, newKs, keysOf, List.pairwise_cons, List.pairwise_map]
    refine ⟨(by intro a ha c x y he; cases he), ?_⟩
    apply hF.imp
    intro a b hab c x y ha hb
    simp only [Klong.key.injEq] at ha hb
    change a.1 < b.1 at hab
    omega

theorem emitKs_erase_eq {s : Tree} {i : Time} {ks : List Klong}
    {F' : List (Nat × NodeId)} {F : List (Nat × Option NodeId)}
    (hm : MatchF s F' F) (hlive : ∀ c y, (c, y) ∈ live ks → s.obj y ≠ none) :
    (emitKs i ks F').map erasePtr = (appendKsO i ks F).map erasePtr := by
  unfold emitKs appendKsO
  rw [List.map_append, List.map_append, removedCvs_congr (live ks) hm.cvs]
  congr 1
  unfold keysOf addedOf
  simp only [List.map_map]
  induction hm with
  | nil => rfl
  | @cons a b F' F hab hrest IH =>
    obtain ⟨c, y⟩ := a
    obtain ⟨c', o⟩ := b
    obtain ⟨hc, hptr⟩ := hab
    simp only at hc hptr
    subst c'
    have hp : ((live ks).lookup c != some y) = isAdded (live ks) (c, o) := by
      rcases hptr with rfl | ⟨rfl, hy⟩
      · rfl
      · simp only [isAdded, bne_iff_ne, ne_eq]
        intro hl
        exact hlive c y (lookup_mem hl) hy
    simp only [List.filter_cons, hp]
    split <;> simp only [List.map_cons, Function.comp_apply, erasePtr, IH]

/-- Safe dead-klong count, with zero meaning the rule is disabled. -/
def DeadSafe (cf : Cfg) (ks : List Klong) : Prop :=
  cf.theta = 0 ∨ deadCount ks ≤ cf.theta

theorem dec_append_dead {cf : Cfg} {i : Time} {n : KNode} {join : Bool}
    {F : List (Nat × Option NodeId)} (hd : decideNode cf i (some n) join F = .append) :
    DeadSafe cf (n.ks ++ appendKsO i n.ks F) := by
  unfold decideNode at hd
  simp only at hd
  split at hd
  · cases hd
  · split at hd
    · split at hd
      · split at hd <;> cases hd
      · rename_i hdead
        simp only [deadOver, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
          not_and, Nat.not_lt] at hdead
        by_cases hz : cf.theta = 0
        · exact Or.inl hz
        · exact Or.inr (hdead hz)
    · cases hd

theorem emitKs_dead_eq {s : Tree} {i : Time} {ks : List Klong}
    {F' : List (Nat × NodeId)} {F : List (Nat × Option NodeId)}
    (hm : MatchF s F' F) (hlive : ∀ c y, (c, y) ∈ live ks → s.obj y ≠ none) :
    deadCount (ks ++ emitKs i ks F') = deadCount (ks ++ appendKsO i ks F) := by
  rw [← deadCount_erasePtr (ks ++ emitKs i ks F'),
    ← deadCount_erasePtr (ks ++ appendKsO i ks F)]
  rw [List.map_append, List.map_append, emitKs_erase_eq hm hlive]

end Contract.PE
