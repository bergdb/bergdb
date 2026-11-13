import SIS.Tree.KlongRoundTrip
import SIS.Tree.RunPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

def lastTimeStep (cur : Option Time) : Klong → Option Time
  | .time t => some t
  | _ => cur

abbrev lastTimeOf (ks : List Klong) : Option Time := (⟨false, ks⟩ : KNode).lastTime

theorem lastTimeFold_origin (ks : List Klong) (cur : Option Time) (t : Time)
    (ht : ks.foldl lastTimeStep cur = some t) : cur = some t ∨ .time t ∈ ks := by
  induction ks generalizing cur with
  | nil => exact Or.inl ht
  | cons k ks ih =>
    rcases ih (lastTimeStep cur k) ht with hh | hh
    · cases k with
      | key c y => exact Or.inl hh
      | del bits => exact Or.inl hh
      | time u =>
        have he : u = t := Option.some.inj hh
        subst u
        exact Or.inr List.mem_cons_self
    · exact Or.inr (List.mem_cons_of_mem k hh)

theorem lastTimeOf_some_mem (ks : List Klong) (t : Time) (ht : lastTimeOf ks = some t) :
    .time t ∈ ks := by
  have hh := lastTimeFold_origin ks none t ht
  rcases hh with hh | hh
  · cases hh
  · exact hh

theorem prefixAt_ne_of_future_mem (ks : List Klong) (t u : Time)
    (hu : t < u) (hm : .time u ∈ ks) : prefixAt ks t ≠ ks := by
  intro he
  have ha := List.all_takeWhile (p := fun k : Klong => match k with
    | .time a => decide (a ≤ t) | _ => true) (l := ks)
  change (prefixAt ks t).all _ = true at ha
  rw [he] at ha
  have hb := List.all_eq_true.mp ha (.time u) hm
  simp only [decide_eq_true_eq] at hb
  omega

theorem prefixAt_append_stopped (ks more : List Klong) (t : Time) (hs : prefixAt ks t ≠ ks) :
    prefixAt (ks ++ more) t = prefixAt ks t := by
  unfold prefixAt
  rw [List.takeWhile_append]
  split
  · rename_i hlen
    exact (hs ((List.takeWhile_prefix _).eq_of_length hlen)).elim
  · rfl

theorem prefixAt_append_future_time (ks more : List Klong) (t i : Time) (hi : t < i) :
    prefixAt (ks ++ .time i :: more) t = prefixAt ks t := by
  unfold prefixAt
  rw [List.takeWhile_append]
  split
  · rename_i hlen
    have he := (List.takeWhile_prefix (l := ks) _).eq_of_length hlen
    simp only [List.takeWhile_cons, show decide (i ≤ t) = false by simp; omega,
      Bool.false_eq_true, ↓reduceIte, List.append_nil]
    exact he.symm
  · rfl

/-- Appending at a later transaction time never changes an earlier physical
prefix, including the branch that reuses the existing final time klong. -/
theorem KNode.add_prefixAt_past (n : KNode) (i t : Time) (hi : t < i) (k : Klong) :
    prefixAt (n.add i k).ks t = prefixAt n.ks t := by
  unfold KNode.add
  split
  · rename_i old last hlast
    split
    · exact prefixAt_append_future_time n.ks [k] t i hi
    · rename_i hle
      have hm : .time last ∈ n.ks := lastTimeOf_some_mem n.ks last hlast
      have ht : t < last := by omega
      exact prefixAt_append_stopped n.ks [k] t (prefixAt_ne_of_future_mem n.ks t last ht hm)
  · exact prefixAt_append_future_time n.ks [k] t i hi

theorem lastTimeOf_append_time (ks : List Klong) (t : Time) :
    lastTimeOf (ks ++ [.time t]) = some t := by
  simp [lastTimeOf, KNode.lastTime, List.foldl_append]

theorem lastTimeOf_append_key (ks : List Klong) (c : Nat) (y : NodeId) :
    lastTimeOf (ks ++ [.key c y]) = lastTimeOf ks := by
  simp [lastTimeOf, KNode.lastTime, List.foldl_append]

theorem lastTimeOf_append_delete (ks : List Klong) (bits : List Nat) :
    lastTimeOf (ks ++ [.del bits]) = lastTimeOf ks := by
  simp [lastTimeOf, KNode.lastTime, List.foldl_append]

theorem parseKlongEntry_lastTime (acc : KlongParseState) (e : Entry BVal)
    (ha : lastTimeOf acc.1 = acc.2.1) :
    lastTimeOf (parseKlongEntry acc e).1 = (parseKlongEntry acc e).2.1 := by
  let base := if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]
  have hb : lastTimeOf base = some e.time := by
    dsimp only [base]
    split
    · rename_i he
      exact ha.trans (by simpa using he)
    · exact lastTimeOf_append_time acc.1 e.time
  unfold parseKlongEntry
  cases hv : e.val with
  | key c y => exact (lastTimeOf_append_key base c y).trans hb
  | del cs =>
    cases cs with
    | nil => exact hb
    | cons c cs => exact (lastTimeOf_append_delete base _).trans hb
  | rootKey y => exact hb
  | skip j z => exact hb
  | top z => exact hb
  | data h => exact hb

theorem parseKlongEntries_lastTime (es : History BVal) :
    lastTimeOf (parseKlongEntries es).1 = (parseKlongEntries es).2.1 := by
  have hf : ∀ (qs : History BVal) (acc : KlongParseState), lastTimeOf acc.1 = acc.2.1 →
      lastTimeOf (qs.foldl parseKlongEntry acc).1 = (qs.foldl parseKlongEntry acc).2.1 := by
    intro qs
    induction qs with
    | nil => intro acc ha; exact ha
    | cons e qs ih => intro acc ha; exact ih _ (parseKlongEntry_lastTime acc e ha)
  exact hf es ([], none, []) rfl

theorem parseKlongEntry_prefixAt_future (acc : KlongParseState) (e : Entry BVal) (t : Time)
    (ha : lastTimeOf acc.1 = acc.2.1) (ht : t < e.time) :
    prefixAt (parseKlongEntry acc e).1 t = prefixAt acc.1 t := by
  let base := if acc.2.1 == some e.time then acc.1 else acc.1 ++ [.time e.time]
  have hbase : prefixAt base t = prefixAt acc.1 t := by
    dsimp only [base]
    split
    · rfl
    · exact prefixAt_append_future_time acc.1 [] t e.time ht
  have hstop : prefixAt base t ≠ base := by
    apply prefixAt_ne_of_future_mem base t e.time ht
    dsimp only [base]
    split
    · rename_i he
      exact lastTimeOf_some_mem acc.1 e.time (ha.trans (by simpa using he))
    · simp
  unfold parseKlongEntry
  cases hv : e.val with
  | key c y => exact (prefixAt_append_stopped base _ t hstop).trans hbase
  | del cs =>
    cases cs with
    | nil => exact hbase
    | cons c cs => exact (prefixAt_append_stopped base _ t hstop).trans hbase
  | rootKey y => exact hbase
  | skip j z => exact hbase
  | top z => exact hbase
  | data h => exact hbase

/-- Future history appends leave every earlier parsed prefix unchanged.
This uses no well-formedness or history-order assumption. -/
theorem klongsOf_prefixAt_append_future (es more : History BVal) (t : Time)
    (hm : ∀ e ∈ more, t < e.time) :
    prefixAt (klongsOf (es ++ more)) t = prefixAt (klongsOf es) t := by
  have hf : ∀ (qs : History BVal) (acc : KlongParseState),
      (∀ e ∈ qs, t < e.time) → lastTimeOf acc.1 = acc.2.1 →
        prefixAt (qs.foldl parseKlongEntry acc).1 t = prefixAt acc.1 t := by
    intro qs
    induction qs with
    | nil => intro acc _ _; rfl
    | cons e qs ih =>
      intro acc hq ha
      rw [List.foldl_cons, ih _ (fun q h => hq q (List.mem_cons_of_mem e h))
        (parseKlongEntry_lastTime acc e ha)]
      exact parseKlongEntry_prefixAt_future acc e t ha (hq e List.mem_cons_self)
  rw [klongsOf_eq_parse, klongsOf_eq_parse]
  simp only [parseKlongEntries, List.foldl_append]
  exact hf more (parseKlongEntries es) hm (parseKlongEntries_lastTime es)

end SIS.Tree
