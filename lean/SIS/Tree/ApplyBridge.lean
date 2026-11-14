/-
The tree model (bergdb 024-12, TP7): the structure after a transaction, read
as key nodes, is the writer's overlay. `changesOf` gives each key node of the
overlay that the transaction did not take back the entries of the
transaction's time; `Struct.apply` adds them to the node's history. Since the
writer changes no klong of an earlier time (`execW_good`), holds each node
once (`execW_cacheUnique`) and keeps its klongs well formed (`execW_klongsWf`),
the history after the transaction is that of the overlay's klongs
(`apply_keyNode`): its klongs are the overlay's. A key node that the
transaction did not hold is unchanged.

With it a statement about the klongs of every overlay node at a
transaction's end is one about the key nodes of P after it
(`keyHistOK_step`: klongs well formed, klongs that give the history).
-/
import SIS.Tree.WriterGoodOps
import SIS.Tree.WriterCacheUnique
import SIS.Tree.ExportHistory
import SIS.Tree.ExportLedger
import SIS.Tree.EntriesSplit
import SIS.Tree.WriterKlongOps
import SIS.Tree.InvInit
import SIS.Tree.RunPrefix

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Lists -/

/-- The entries of time i that `changesOf` gives node x from the overlay. -/
theorem keyAdds_filter (nodes : List (NodeId × KNode)) (taken : List NodeId) (i : Time)
    (x : NodeId) (hn : (nodes.map (·.1)).Nodup) :
    ((((nodes.filter (fun q => !taken.contains q.1)).flatMap (fun q =>
      ((entriesOf q.2.ks).filter (fun e => e.time == i)).map (fun e => (q.1, e.val)))).filter
        (fun a => a.1 == x)).map (fun a => (⟨i, a.2⟩ : Entry BVal))) =
      match nodes.lookup x with
      | some n => if taken.contains x then [] else (entriesOf n.ks).filter (fun e => e.time == i)
      | none => [] := by
  induction nodes with
  | nil => rfl
  | cons q nodes ih =>
    obtain ⟨y, m⟩ := q
    simp only [List.map_cons, List.nodup_cons] at hn
    have ih' := ih hn.2
    by_cases hy : y = x
    · subst hy
      have hlook : nodes.lookup y = none := by
        apply List.lookup_eq_none_iff.mpr
        intro q hq
        have : q.1 ≠ y := fun he => hn.1 (List.mem_map.mpr ⟨q, hq, he⟩)
        simpa using fun he => this he.symm
      rw [hlook] at ih'
      simp only [List.lookup_cons, beq_self_eq_true]
      by_cases ht : taken.contains y = true
      · simp only [List.filter_cons, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        exact ih'
      · simp only [List.filter_cons, ht, Bool.not_false, ↓reduceIte, List.flatMap_cons,
          List.filter_append, List.map_append, ih', List.append_nil, Bool.false_eq_true]
        rw [List.filter_eq_self.mpr (by
          intro a ha
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
          simp), List.map_map]
        have hid : ∀ e ∈ (entriesOf m.ks).filter (fun e => e.time == i),
            ((fun a : NodeId × BVal => (⟨i, a.2⟩ : Entry BVal)) ∘ fun e => (y, e.val)) e = e := by
          intro e he
          have ht : e.time = i := by simpa using (List.mem_filter.mp he).2
          cases e
          simp_all
        rw [List.map_congr_left hid, List.map_id']
    · have hxy : (x == y) = false := by simpa using fun he : x = y => hy he.symm
      simp only [List.lookup_cons, hxy]
      rw [← ih']
      by_cases ht : taken.contains y = true
      · simp only [List.filter_cons, ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      · simp only [List.filter_cons, ht, Bool.not_false, ↓reduceIte, List.flatMap_cons,
          List.filter_append, List.map_append]
        rw [List.filter_eq_nil_iff.mpr (by
          intro a ha
          obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
          simpa using hy), List.map_nil, List.nil_append]

/-- The entries that a transaction's changes add to node x, if x is no value
and no top node of the transaction: the entries of the transaction's time of
the overlay's node x, none if the overlay has none or the transaction took
it back. -/
theorem addsFor_changesOf (i : Time) (w : W) (x : NodeId)
    (hn : (w.nodes.map (·.1)).Nodup) (hv : ∀ q ∈ w.vals, q.1 ≠ x)
    (ht : w.newTop = true → x ≠ root ∧ x ≠ w.top.id) :
    addsFor (changesOf i w) i x =
      match w.nodes.lookup x with
      | some n => if w.taken.contains x then [] else (entriesOf n.ks).filter (fun e => e.time == i)
      | none => [] := by
  have hvals : (w.vals.map (fun q => (q.1, BVal.data q.2))).filter (fun a => a.1 == x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
    simpa using hv q hq
  have htop : (if w.newTop then
      (root, BVal.top w.top.id) :: (w.top.id, BVal.rootKey w.top.rootKey) ::
        w.top.skips.map (fun q => (w.top.id, BVal.skip q.1 q.2))
      else ([] : List (NodeId × BVal))).filter (fun a => a.1 == x) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro a ha
    split at ha
    · rename_i hnt
      obtain ⟨h1, h2⟩ := ht hnt
      simp only [List.mem_cons, List.mem_map] at ha
      rcases ha with rfl | rfl | ⟨q, _, rfl⟩
      · simpa using fun he : root = x => h1 he.symm
      · simpa using fun he : w.top.id = x => h2 he.symm
      · simpa using fun he : w.top.id = x => h2 he.symm
    · cases ha
  unfold addsFor changesOf
  simp only
  rw [filter_id_mergeSort, List.filter_append, List.filter_append, hvals, htop, List.append_nil,
    List.append_nil]
  exact keyAdds_filter w.nodes w.taken i x hn

/-! ## The writer's view of P -/

/-- Every key node of P: its klongs are well formed and give its history. -/
def KeyHistOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    klongsWf (klongsOf nd.hist) = true ∧ entriesOf (klongsOf nd.hist) = nd.hist

theorem upTo_eq_self (h : History BVal) (t : Time) (ht : ∀ e ∈ h, e.time ≤ t) : h.upTo t = h := by
  unfold History.upTo
  apply List.filter_eq_self.mpr
  intro e he
  simpa using ht e he

/-- A node of the view at t of a structure without later entries is the node
of P. -/
theorem view_eq_get? (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (x : NodeId) (nd : Node BVal) (h : view (treeSpec p) P t x = some nd) : P.get? x = some nd := by
  unfold view at h
  split at h
  · cases hx : P.get? x with
    | none => simp [hx] at h
    | some old =>
      have he : {old with hist := old.hist.upTo t} = nd := by simpa [hx] using h
      rw [upTo_eq_self old.hist t (hP _ (mem_of_get? hx))] at he
      rw [← he]
  · cases h

theorem rootless_some_eq (v : View BVal) (x : NodeId) (nd : Node BVal) (h : rootless v x = some nd) :
    v x = some nd := by
  unfold rootless at h
  split at h
  · cases h
  · exact h

/-- The premises of the writer's run on P@(i-1) that are about the links of
P: no klong of a key node of the view names an id of the transaction, and
every key node of the view has a klong. Both follow from invariants of P
(`PointersOK`; a history for every key node). -/
structure ViewLinksOK (B : NodeId) (p : Params) (v : View BVal) : Prop where
  ptrs : ∀ x nd, v x = some nd → ∀ cv y, Klong.key cv y ∈ klongsOf nd.hist → y < B
  nonempty : ∀ x nd, v x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    klongsOf nd.hist ≠ []

theorem viewGood_of (p : Params) (P : Struct BVal) (i : Time) (B : NodeId) (hpos : 0 < i)
    (hfresh : ∀ q ∈ P, q.1 < B) (htimes : StructTimesLE P (i - 1))
    (hl : ViewLinksOK B p (view (treeSpec p) P (i - 1))) :
    ViewGood B { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } := by
  refine ⟨hpos, ?_, ?_, ?_, ?_⟩
  · exact viewIdsBelow_rootless B _ (viewIdsBelow_view p P (i - 1) B hfresh)
  · intro x nd hx e he
    have hg := view_eq_get? p P (i - 1) htimes x nd (rootless_some_eq _ x nd hx)
    have := htimes _ (mem_of_get? hg) e he
    show e.time < i
    omega
  · intro x nd hx cv y hk
    exact hl.ptrs x nd (rootless_some_eq _ x nd hx) cv y hk
  · intro x nd hx hd hlv
    exact hl.nonempty x nd (rootless_some_eq _ x nd hx) hd hlv

theorem viewKlongsWf_of (p : Params) (P : Struct BVal) (t : Time) (htimes : StructTimesLE P t)
    (hH : KeyHistOK p P) : ViewKlongsWf p (view (treeSpec p) P t) := by
  intro x nd hx hd hl
  exact (hH x nd (view_eq_get? p P t htimes x nd hx) hd hl).1

/-! ## The key nodes after a transaction -/

theorem newNodeOf_new_mem (c : Changes BVal) (x : NodeId) (nd : Node BVal)
    (h : newNodeOf c x = some nd) :
    ∃ nn ∈ c.new, nn.id = x ∧ nd = { level := nn.level, isData := nn.isData, hist := [] } := by
  unfold newNodeOf Struct.get? at h
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
  have hm : (x, nd) ∈ c.new.map (fun n =>
      (n.id, ({ level := n.level, isData := n.isData, hist := [] } : Node BVal))) := by
    rw [he]; simp
  obtain ⟨nn, hn, heq⟩ := List.mem_map.mp hm
  cases heq
  exact ⟨nn, hn, rfl, rfl⟩

theorem made_unique (B : NodeId) (w : W) (hA : AllocatedIds B w) (a b : NewNode)
    (ha : a ∈ w.made) (hb : b ∈ w.made) (hid : a.id = b.id) : a = b := by
  have hnd := hA.2.1
  generalize w.made = l at ha hb hnd
  induction l with
  | nil => cases ha
  | cons m l ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'
      exact (hnd.1 (List.mem_map.mpr ⟨b, hb', hid.symm⟩)).elim
    · subst hb'
      exact (hnd.1 (List.mem_map.mpr ⟨a, ha', hid⟩)).elim
    · exact ih ha' hb' hnd.2

/-- The structure after a transaction, read as key nodes, is the writer's
overlay. For a successful run of the writer at time i on P@(i-1) (ids of P
below the transaction's first id, no entry of P after i - 1, a root above the
key levels, key nodes whose klongs are well formed and give their histories,
`ViewLinksOK`), every key node x of the structure after it is

* a node of the overlay that the transaction did not take back: its history
  is that of the overlay's klongs, so its klongs are the overlay's; or
* a key node of P as it was, not in the overlay or taken back. -/
theorem apply_keyNode (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)
    (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (x : NodeId) (nd' : Node BVal) (hx : (P.apply i (changesOf i w)).get? x = some nd')
    (hd : nd'.isData = false) (hlv : nd'.level ≤ p.keyMax) :
    (∃ n, w.nodes.lookup x = some n ∧ w.taken.contains x = false ∧
      nd'.hist = entriesOf n.ks ∧ klongsOf nd'.hist = n.ks ∧ klongsWf n.ks = true) ∨
    (P.get? x = some nd' ∧ (w.nodes.lookup x = none ∨ w.taken.contains x = true)) := by
  have hvg := viewGood_of p P i tx.base hpos hfresh htimes hl
  have hgood := execW_good p tx i _ bs w hvg he
  have hnodup : (w.nodes.map (·.1)).Nodup :=
    execW_cacheUnique p tx i _ bs w (viewIdsBelow_view p P (i - 1) tx.base hfresh) he
  have hwf := execW_klongsWf p tx i _ bs w (viewKlongsWf_of p P (i - 1) htimes hH) he
  have halloc := execW_allocatedIds p tx i _ bs w he
  have hledger := execW_ledger p tx i _ bs w he
  obtain ⟨r, hr, hrl⟩ := hroot
  have hrootB : root < tx.base := hfresh _ (mem_of_get? hr)
  rw [get?_apply] at hx
  -- The node before the entries, and what the transaction adds to it.
  have hadds : ∀ nd0, (P.get? x).or (newNodeOf (changesOf i w) x) = some nd0 →
      nd0.isData = false → nd0.level ≤ p.keyMax →
      ((P.get? x = some nd0 ∧ x < tx.base) ∨
        (P.get? x = none ∧ tx.base ≤ x ∧ nd0.hist = [] ∧ w.taken.contains x = false ∧
          ∃ n, (x, n) ∈ w.nodes)) ∧
      addsFor (changesOf i w) i x =
        match w.nodes.lookup x with
        | some n =>
          if w.taken.contains x then [] else (entriesOf n.ks).filter (fun e => e.time == i)
        | none => [] := by
    intro nd0 h0 hd0 hl0
    cases hpx : P.get? x with
    | some old =>
      rw [hpx] at h0
      have hold : old = nd0 := by simpa using h0
      subst hold
      have hxB : x < tx.base := hfresh _ (mem_of_get? hpx)
      refine ⟨Or.inl ⟨rfl, hxB⟩, ?_⟩
      apply addsFor_changesOf i w x hnodup
      · intro q hq he'
        have := (halloc.2.2 _ (hledger.2.1 q hq)).1
        simp only at this
        omega
      · intro hnt
        obtain ⟨lvl, _, hm⟩ := hledger.2.2 hnt
        have := (halloc.2.2 _ hm).1
        refine ⟨?_, by simp only at this; omega⟩
        intro hxr
        rw [hxr, hr] at hpx
        have : r = old := by simpa using hpx
        subst this
        exact absurd hl0 (by omega)
    | none =>
      rw [hpx] at h0
      have h0' : newNodeOf (changesOf i w) x = some nd0 := by simpa using h0
      obtain ⟨nn, hnn, hid, hnd0⟩ := newNodeOf_new_mem _ x nd0 h0'
      obtain ⟨hmade, hnt⟩ := changesOf_new_mem i w nn hnn
      subst hid
      have hB := (halloc.2.2 nn hmade).1
      have hnnd : nn.isData = false := by rw [hnd0] at hd0; exact hd0
      have hnnl : nn.level ≤ p.keyMax := by rw [hnd0] at hl0; exact hl0
      obtain ⟨n0, hn0⟩ := hledger.1 nn hmade hnnd hnnl
      refine ⟨Or.inr ⟨rfl, hB, by rw [hnd0], hnt, n0, hn0⟩, ?_⟩
      apply addsFor_changesOf i w nn.id hnodup
      · intro q hq he'
        have hq' := hledger.2.1 q hq
        have := made_unique tx.base w halloc _ _ hq' hmade he'
        rw [← this] at hnnd
        cases hnnd
      · intro hnt'
        obtain ⟨lvl, hlvl, hm⟩ := hledger.2.2 hnt'
        refine ⟨by omega, ?_⟩
        intro hxt
        have := made_unique tx.base w halloc _ _ hm hmade hxt.symm
        rw [← this] at hnnl
        have hlvl' : p.keyMax < lvl := hlvl
        simp only at hnnl
        omega
  cases h0 : (P.get? x).or (newNodeOf (changesOf i w) x) with
  | none => simp [h0] at hx
  | some nd0 =>
    rw [h0] at hx
    have hnd' : nd' = { nd0 with hist := nd0.hist ++ addsFor (changesOf i w) i x } := by
      simpa using hx.symm
    have hd0 : nd0.isData = false := by rw [hnd'] at hd; exact hd
    have hl0 : nd0.level ≤ p.keyMax := by rw [hnd'] at hlv; exact hlv
    obtain ⟨hcase, hadd⟩ := hadds nd0 h0 hd0 hl0
    cases hlook : w.nodes.lookup x with
    | none =>
      rw [hlook] at hadd
      rcases hcase with ⟨hp0, _⟩ | ⟨_, _, _, _, n, hn⟩
      · refine Or.inr ⟨?_, Or.inl rfl⟩
        rw [hp0, hnd', hadd, List.append_nil]
      · have := List.lookup_eq_none_iff.mp hlook (x, n) hn
        simp at this
    | some n =>
      rw [hlook] at hadd
      cases htk : w.taken.contains x with
      | true =>
        simp only [htk, ↓reduceIte] at hadd
        rcases hcase with ⟨hp0, _⟩ | ⟨_, _, _, hnt, _⟩
        · refine Or.inr ⟨?_, Or.inr rfl⟩
          rw [hp0, hnd', hadd, List.append_nil]
        · rw [htk] at hnt
          cases hnt
      | false =>
        simp only [htk, Bool.false_eq_true, ↓reduceIte] at hadd
        have hg := cacheGood_lookup tx.base _ w hgood x n hlook
        have hwn := writerKlongsWf_lookup w hwf x n hlook
        obtain ⟨hsplit, _⟩ := entriesOf_split n.ks i hpos hwn hg.times
        have hold := hg.old
        simp only at hold
        have hbase : entriesOf (baseKlongs (rootless (view (treeSpec p) P (i - 1))) x) = nd0.hist := by
          rcases hcase with ⟨hp0, hxB⟩ | ⟨hp0, hxB, hh0, _, _⟩
          · rcases hg.origin with ⟨ndv, hv, _, _⟩ | hge
            · have hv' := view_eq_get? p P (i - 1) htimes x ndv (rootless_some_eq _ x ndv hv)
              rw [hp0] at hv'
              have : nd0 = ndv := by simpa using hv'
              subst this
              have hb : baseKlongs (rootless (view (treeSpec p) P (i - 1))) x = klongsOf nd0.hist := by
                have hv2 : rootless (view (treeSpec p) P (i - 1)) x = some nd0 := hv
                unfold baseKlongs
                rw [hv2]
              rw [hb]
              exact (hH x nd0 hp0 hd0 hl0).2
            · omega
          · have hnone : rootless (view (treeSpec p) P (i - 1)) x = none := by
              cases hv : rootless (view (treeSpec p) P (i - 1)) x with
              | none => rfl
              | some ndv =>
                have hv' := view_eq_get? p P (i - 1) htimes x ndv (rootless_some_eq _ x ndv hv)
                rw [hp0] at hv'
                cases hv'
            have hb : baseKlongs (rootless (view (treeSpec p) P (i - 1))) x = [] := by
              unfold baseKlongs
              rw [hnone]
            rw [hb, hh0]
            rfl
        have hhist : nd'.hist = entriesOf n.ks := by
          rw [hnd', hadd]
          show nd0.hist ++ _ = _
          rw [← hbase, ← hold]
          exact hsplit.symm
        refine Or.inl ⟨n, rfl, rfl, hhist, ?_, hwn⟩
        rw [hhist]
        exact klongsRoundTrip n.ks hwn

end SIS.Tree
