/-
The contract package (bergdb 030-17): Java's search through the skip pointers
at a time t at or after f reads only the top nodes that `TopFrom f` keeps
(RecoverCut.lean): on any top that holds a top built by the clauses from f,
it finds what it finds on that top (`findTop_from`, `findRoot_from`).

The route. Along the first loop every top node met has a root time at or
after t, so at or after f: each is kept, so both searches meet the same nodes
and make the same choices (`skipDown_from`). The fuel: the steps go to older
top nodes made at or after f, and the kept top has a distinct entry for each
of those (the ids of a top built by the clauses are distinct), so its length
is fuel enough. The top node found at the end is the top node of time t; if
it was made before f, it is the top node of time f.
-/
import Mathlib.Tactic
import Contract.RecoverCut
import Contract.Proof.Top

namespace Contract

theorem atOrAfter_le {x t : Time} {mid : Bool} (h : atOrAfter x t mid = true) : t ≤ x := by
  cases mid
  · simpa [atOrAfter] using h
  · exact Nat.le_of_lt (by simpa [atOrAfter] using h)

/-- The ids of a top built by the clauses are distinct. -/
theorem TopGood.nodup {tp : Top} (hg : TopGood tp) : (tp.map (·.1)).Nodup := by
  induction hg with
  | nil => exact List.nodup_nil
  | snoc tp z n _ hz _ _ ih =>
    rw [List.map_append, List.nodup_append]
    refine ⟨ih, by simp, ?_⟩
    intro a ha b hb
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
    subst hb
    intro he
    subst he
    obtain ⟨q, hq, hqa⟩ := List.mem_map.mp ha
    unfold Top.node at hz
    have := List.lookup_eq_none_iff.mp hz q hq
    simp [hqa] at this

/-- The top node of a time is the last made at or before it. -/
theorem topAt_max {tp : Top} (hg : TopGood tp) {t : Time} {zn : NodeId × TopNode}
    (h : topAt tp t = some zn) :
    zn ∈ tp ∧ zn.2.time ≤ t ∧ ∀ zm ∈ tp, zm.2.time ≤ t → zm.2.time ≤ zn.2.time := by
  unfold topAt at h
  have hm := List.mem_filter.mp (List.mem_of_getLast? h)
  have hpw : (tp.filter (fun zn => decide (zn.2.time ≤ t))).Pairwise
      (fun a b => a.2.time < b.2.time) := hg.pairwise.sublist List.filter_sublist
  refine ⟨hm.1, by simpa using hm.2, ?_⟩
  intro zm hzm hle
  rcases last_rel hpw h zm (List.mem_filter.mpr ⟨hzm, by simpa using hle⟩) with h1 | h1
  · rw [h1]
  · exact Nat.le_of_lt h1

/-- The top nodes of tp made at or after f and before the root time x. -/
def below (tp : Top) (f x : Time) : Nat :=
  (tp.filter (fun zm => decide (f ≤ zm.2.time ∧ zm.2.time < x))).length

/-- The search's first loop on a top that keeps the top nodes made at or
after f meets the same top nodes as on the top itself, from a top node at or
after the lookup time t ≥ f, with fuel enough on both. -/
theorem skipDown_from {tp tp' : Top} (hg : TopGood tp) {f t : Time} {mid : Bool}
    (hk : ∀ zn ∈ tp, f ≤ zn.2.time → tp'.node zn.1 = some zn.2) (hft : f ≤ t) :
    ∀ (F1 F2 : Nat) (z : NodeId) (n : TopNode), (z, n) ∈ tp → atOrAfter n.time t mid = true →
      below tp f n.time < F1 → below tp f n.time < F2 →
      skipDown tp' t mid F1 z = skipDown tp t mid F2 z
  | 0, _, _, _, _, _, h1, _ => absurd h1 (Nat.not_lt_zero _)
  | _ + 1, 0, _, _, _, _, _, h2 => absurd h2 (Nat.not_lt_zero _)
  | F1 + 1, F2 + 1, z, n, hm, ha, h1, h2 => by
    have hnt : t ≤ n.time := atOrAfter_le ha
    have hz' : tp'.node z = some n := hk (z, n) hm (le_trans hft hnt)
    have hz : tp.node z = some n := hg.lookup hm
    simp only [skipDown, hz, hz']
    cases hr : rightMostGte n t mid with
    | none => rfl
    | some y =>
      simp only
      unfold rightMostGte at hr
      cases hfd : n.skips.reverse.find? (fun q => atOrAfter q.2.2 t mid) with
      | none => simp [hfd] at hr
      | some q =>
        simp only [hfd, Option.map_some, Option.some.injEq] at hr
        subst hr
        have hqm := List.mem_reverse.mp (List.mem_of_find?_eq_some hfd)
        have hqa := List.find?_some hfd
        obtain ⟨ny, hmy, hty, hlt⟩ := hg.skip hm hqm
        have hya : atOrAfter ny.time t mid = true := by rw [hty]; exact hqa
        have hyt : t ≤ ny.time := atOrAfter_le hya
        have hdec : below tp f ny.time < below tp f n.time := by
          unfold below
          exact length_filter_lt _ _ tp
            (fun x _ hx => by
              simp only [decide_eq_true_eq] at hx ⊢
              exact ⟨hx.1, Nat.lt_trans hx.2 hlt⟩)
            (q.2.1, ny) hmy (by simp only [decide_eq_true_eq]; exact ⟨le_trans hft hyt, hlt⟩)
            (by simp)
        exact skipDown_from hg hk hft F1 F2 q.2.1 ny hmy hya (by omega) (by omega)

/-- A top that keeps the top nodes of tp made at or after f has at least as
many entries as there are such top nodes. -/
theorem length_from_le {tp tp' : Top} (hg : TopGood tp) {f : Time}
    (hk : ∀ zn ∈ tp, f ≤ zn.2.time → tp'.node zn.1 = some zn.2) :
    (tp.filter (fun zm => decide (f ≤ zm.2.time))).length ≤ tp'.length := by
  have hnd : ((tp.filter (fun zm => decide (f ≤ zm.2.time))).map (·.1)).Nodup :=
    hg.nodup.sublist (List.filter_sublist.map _)
  have hsub : (tp.filter (fun zm => decide (f ≤ zm.2.time))).map (·.1) ⊆ tp'.map (·.1) := by
    intro a ha
    obtain ⟨zn, hzn, rfl⟩ := List.mem_map.mp ha
    have h1 := List.mem_filter.mp hzn
    have h2 := hk zn h1.1 (by simpa using h1.2)
    exact List.mem_map.mpr ⟨(zn.1, zn.2), mem_of_lookup h2, rfl⟩
  have := (hnd.subperm hsub).length_le
  simpa using this

/-- Java's search at a time t at or after f finds, on a top that holds the top
tp from f, the top node that it finds on tp. -/
theorem findTop_from {tp tp' : Top} (hg : TopGood tp) {f : Time} (hf : TopFrom f tp tp')
    {t : Time} (hft : f ≤ t) (mid : Bool) : findTop tp' t mid = findTop tp t mid := by
  unfold findTop
  rw [hf.last]
  cases hl : tp.getLast? with
  | none => rfl
  | some wn =>
    obtain ⟨w, nw⟩ := wn
    have hwm := List.mem_of_getLast? hl
    simp only
    by_cases hwt : nw.time ≤ t
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hwt), ite_eq_left_of_eq_true _ _ (eq_true hwt)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hwt), ite_eq_right_of_eq_false _ _ (eq_false hwt)]
      have hwt' : t < nw.time := Nat.lt_of_not_le hwt
      have hwa : atOrAfter nw.time t mid = true := by
        cases mid <;> simp [atOrAfter, hwt', Nat.le_of_lt hwt']
      have hfuel : (tp.filter (fun zm => decide (zm.2.time < nw.time))).length < tp.length := by
        have := length_filter_lt (fun zm : NodeId × TopNode => decide (zm.2.time < nw.time))
          (fun _ => true) tp (fun _ _ _ => rfl) (w, nw) hwm rfl (by simp)
        simpa using this
      have hb1 : below tp f nw.time < tp.length := by
        have := length_filter_lt (fun zm : NodeId × TopNode =>
            decide (f ≤ zm.2.time ∧ zm.2.time < nw.time))
          (fun _ => true) tp (fun _ _ _ => rfl) (w, nw) hwm rfl (by simp)
        simpa [below] using this
      have hb2 : below tp f nw.time < tp'.length := by
        have h1 := length_filter_lt (fun zm : NodeId × TopNode =>
            decide (f ≤ zm.2.time ∧ zm.2.time < nw.time))
          (fun zm => decide (f ≤ zm.2.time)) tp
          (fun x _ hx => by simp only [decide_eq_true_eq] at hx ⊢; exact hx.1) (w, nw) hwm
          (by simp only [decide_eq_true_eq]; exact le_trans hft (Nat.le_of_lt hwt')) (by simp)
        have h2 := length_from_le hg hf.keep
        unfold below
        omega
      rw [skipDown_from hg hf.keep hft tp'.length tp.length w nw hwm hwa hb2 hb1]
      obtain ⟨nf, hzf, hfa, _⟩ := skipDown_spec hg t mid tp.length w nw (hg.lookup hwm) hwa hfuel
      have hzf' : tp'.node (skipDown tp t mid tp.length w) = some nf :=
        hf.keep (_, nf) (mem_of_lookup hzf) (le_trans hft (atOrAfter_le hfa))
      rw [hzf, hzf']

/-- Java's search at a time t at or after f gives, on a top that holds the top
tp from f, the space root that it gives on tp. -/
theorem findRoot_from {tp tp' : Top} (hg : TopGood tp) {f : Time} (hf : TopFrom f tp tp')
    {t : Time} (hft : f ≤ t) (mid : Bool) : findRoot tp' t mid = findRoot tp t mid := by
  unfold findRoot
  rw [findTop_from hg hf hft mid, findTop_right hg t mid]
  cases h : topAt tp t with
  | none => rfl
  | some zn =>
    obtain ⟨hm, hle, hmax⟩ := topAt_max hg h
    obtain ⟨z, n⟩ := zn
    simp only [Option.map_some]
    rw [hg.lookup hm]
    by_cases hfz : f ≤ n.time
    · rw [hf.keep (z, n) hm hfz]
    · have hf' : topAt tp f = some (z, n) :=
        topAt_eq hg hm (Nat.le_of_lt (Nat.lt_of_not_le hfz))
          (fun zm hzm h => hmax zm hzm (le_trans h hft))
      rw [hf.atF (z, n) hf']

/-- Java's get and scan at a time t at or after f, on a top that holds the top
tp from f, are those on tp. -/
theorem jget_from {tp tp' : Top} (hg : TopGood tp) {f : Time} (hf : TopFrom f tp tp')
    {t : Time} (hft : f ≤ t) (mid : Bool) (s : Tree) (key : Key) :
    jget s tp' t mid key = jget s tp t mid key := by
  unfold jget
  rw [findRoot_from hg hf hft mid]

theorem jscan_from {tp tp' : Top} (hg : TopGood tp) {f : Time} (hf : TopFrom f tp tp')
    {t : Time} (hft : f ≤ t) (mid : Bool) (s : Tree) (req : ScanReq) (limit : Nat) :
    jscan s tp' t mid req limit = jscan s tp t mid req limit := by
  unfold jscan
  rw [findRoot_from hg hf hft mid]

/-- A top built by the clauses holds itself from every time. -/
theorem TopGood.topFrom {tp : Top} (hg : TopGood tp) (f : Time) : TopFrom f tp tp :=
  ⟨rfl, fun _ hm _ => hg.lookup hm, fun _ h => hg.lookup (topAt_max hg h).1⟩

/-- Holding from f holds from every later time. -/
theorem TopFrom.mono {tp tp' : Top} (hg : TopGood tp) {f g : Time} (hf : TopFrom f tp tp')
    (hfg : f ≤ g) : TopFrom g tp tp' := by
  refine ⟨hf.last, fun zn hm hg' => hf.keep zn hm (le_trans hfg hg'), ?_⟩
  intro zn h
  obtain ⟨hm, _, hmax⟩ := topAt_max hg h
  by_cases hfz : f ≤ zn.2.time
  · exact hf.keep zn hm hfz
  · obtain ⟨z, n⟩ := zn
    exact hf.atF (z, n) (topAt_eq hg hm (Nat.le_of_lt (Nat.lt_of_not_le hfz))
      (fun zm hzm h => hmax zm hzm (le_trans h hfg)))

end Contract
