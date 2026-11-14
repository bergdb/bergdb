import SIS.Tree.GetCommit
import SIS.Tree.KlongAppend
import SIS.Tree.NodeMap
import SIS.Tree.KlongPreservation
import SIS.Tree.TimeSplitMap
import SIS.Tree.KlongWellFormed
import SIS.Tree.MergeLiveOrder
import SIS.Tree.WriterSteps
import SIS.Tree.WriterBook

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A frame for the writer's reading (bergdb 024-12, TP10, `OpGetOK`): the
reading of a key visits nodes, each with the compare value it searches; a
change of one segment leaf that keeps the search of every compare value but
one changes the reading of no key that does not search that one there. -/

/-- The nodes a search through one segment tree visits, each with the compare
value searched. -/
def eqVisits (nodeOf : NodeId → Option KNode) (t : Time) (cv : Nat) :
    Nat → NodeId → List (NodeId × Nat)
  | 0, _ => []
  | f + 1, x => (x, cv) ::
    match nodeOf x with
    | none => []
    | some n =>
      if n.leaf then []
      else
        match n.searchLte t cv with
        | none => []
        | some fd => eqVisits nodeOf t cv f fd.y

/-- The nodes a reading of a key visits, each with the compare value searched
(the key's segment of the node's tree). -/
def fromVisits (nodeOf : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    List Nat → NodeId → List (NodeId × Nat)
  | [], _ => []
  | [cv], r => eqVisits nodeOf t cv fuel r
  | cv :: rest, r => eqVisits nodeOf t cv fuel r ++
    match getEqR nodeOf t cv fuel r with
    | some y => fromVisits nodeOf t fuel rest y
    | none => []

/-- Two node readers agree for a search of compare value c at node x: the same
node, or two segment leaves whose searches of c give the same pointer. -/
def AgreeAt (N1 N2 : NodeId → Option KNode) (t : Time) (x : NodeId) (c : Nat) : Prop :=
  N1 x = N2 x ∨ ∃ n1 n2, N1 x = some n1 ∧ N2 x = some n2 ∧ n1.leaf = true ∧ n2.leaf = true ∧
    (n1.searchEq t c).map (·.y) = (n2.searchEq t c).map (·.y)

theorem getEqR_frame (N1 N2 : NodeId → Option KNode) (t : Time) (cv : Nat) (f : Nat)
    (x : NodeId) (h : ∀ q ∈ eqVisits N1 t cv f x, AgreeAt N1 N2 t q.1 q.2) :
    getEqR N1 t cv f x = getEqR N2 t cv f x ∧ eqVisits N1 t cv f x = eqVisits N2 t cv f x := by
  induction f generalizing x with
  | zero => exact ⟨rfl, rfl⟩
  | succ f ih =>
    have hx := h (x, cv) (by simp [eqVisits])
    rcases hx with he | ⟨n1, n2, h1, h2, hl1, hl2, hs⟩
    · simp only [getEqR, eqVisits]
      rw [← he]
      cases hn : N1 x with
      | none => exact ⟨rfl, rfl⟩
      | some n =>
        simp only
        split
        · exact ⟨rfl, rfl⟩
        · cases hf : n.searchLte t cv with
          | none => exact ⟨rfl, rfl⟩
          | some fd =>
            simp only
            have hrest : ∀ q ∈ eqVisits N1 t cv f fd.y, AgreeAt N1 N2 t q.1 q.2 := by
              intro q hq
              apply h q
              simp only [eqVisits, hn]
              rename_i hleaf
              simp only [hleaf, Bool.false_eq_true, ↓reduceIte, hf, List.mem_cons]
              exact Or.inr hq
            obtain ⟨e1, e2⟩ := ih fd.y hrest
            exact ⟨e1, by rw [e2]⟩
    · simp only [getEqR, eqVisits, h1, h2, hl1, hl2, ↓reduceIte]
      exact ⟨hs, trivial⟩

theorem getEqR_some_visit (N : NodeId → Option KNode) (t : Time) (cv f : Nat) (r y : NodeId)
    (h : getEqR N t cv f r = some y) :
    ∃ x n, (x, cv) ∈ eqVisits N t cv f r ∧ N x = some n ∧ n.leaf = true ∧
      (n.searchEq t cv).map (·.y) = some y := by
  induction f generalizing r with
  | zero => simp [getEqR] at h
  | succ f ih =>
    simp only [getEqR] at h
    cases hn : N r with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only at h
      split at h
      · rename_i hleaf
        exact ⟨r, n, by simp [eqVisits], hn, hleaf, h⟩
      · rename_i hleaf
        cases hf : n.searchLte t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          simp only at h
          obtain ⟨x, m, hx, hm, hl, hs⟩ := ih fd.y h
          refine ⟨x, m, ?_, hm, hl, hs⟩
          simp only [eqVisits, hn, hleaf, Bool.false_eq_true, ↓reduceIte, hf, List.mem_cons]
          exact Or.inr hx

/-- The frame of a reading: node readers that agree at every node it visits,
for the compare value it searches there, and value readers that agree at
every pointer that a visited segment leaf gives, give the same reading. -/
theorem getFromR_frame (N1 N2 : NodeId → Option KNode) (V1 V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (key : List Nat) (r : NodeId)
    (h : ∀ q ∈ fromVisits N1 t fuel key r, AgreeAt N1 N2 t q.1 q.2)
    (hval : ∀ x c n y, (x, c) ∈ fromVisits N1 t fuel key r → N1 x = some n → n.leaf = true →
      (n.searchEq t c).map (·.y) = some y → V1 y = V2 y) :
    getFromR N1 V1 t fuel key r = getFromR N2 V2 t fuel key r := by
  induction key generalizing r with
  | nil => rfl
  | cons cv rest ih =>
    cases rest with
    | nil =>
      simp only [fromVisits] at h hval
      obtain ⟨e1, _⟩ := getEqR_frame N1 N2 t cv fuel r h
      simp only [getFromR]
      rw [← e1]
      cases hg : getEqR N1 t cv fuel r with
      | none => rfl
      | some y =>
        simp only [Option.bind_some]
        obtain ⟨x, n, hx, hn, hl, hs⟩ := getEqR_some_visit N1 t cv fuel r y hg
        exact hval x cv n y hx hn hl hs
    | cons d rest' =>
      simp only [fromVisits] at h hval
      have h1 : ∀ q ∈ eqVisits N1 t cv fuel r, AgreeAt N1 N2 t q.1 q.2 :=
        fun q hq => h q (List.mem_append_left _ hq)
      obtain ⟨e1, _⟩ := getEqR_frame N1 N2 t cv fuel r h1
      simp only [getFromR]
      rw [← e1]
      cases hg : getEqR N1 t cv fuel r with
      | none => rfl
      | some y =>
        simp only
        have h2 : ∀ q ∈ fromVisits N1 t fuel (d :: rest') y, AgreeAt N1 N2 t q.1 q.2 := by
          intro q hq
          apply h q
          apply List.mem_append_right
          rw [hg]
          exact hq
        have hy0 : AgreeAt N1 N2 t y d := by
          apply h2 (y, d)
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          cases rest' <;> simp [fromVisits, eqVisits]
        have hsome : (N1 y).isSome = (N2 y).isSome := by
          rcases hy0 with he | ⟨n1, n2, h1', h2', _⟩
          · rw [he]
          · rw [h1', h2']; rfl
        rw [← hsome]
        split
        · apply ih y h2
          intro x c n z hxc hn hl hs
          apply hval x c n z _ hn hl hs
          apply List.mem_append_right
          rw [hg]
          exact hxc
        · rfl

/-- A leaf changed at one compare value: every other key's reading stays. -/
theorem getFromR_leaf_change (N1 N2 : NodeId → Option KNode) (V1 V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (L : NodeId) (cv : Nat)
    (hN : ∀ x, x ≠ L → N1 x = N2 x)
    (hL : ∃ n1 n2, N1 L = some n1 ∧ N2 L = some n2 ∧ n1.leaf = true ∧ n2.leaf = true ∧
      ∀ c, c ≠ cv → (n1.searchEq t c).map (·.y) = (n2.searchEq t c).map (·.y))
    (key : List Nat) (r : NodeId) (hnot : (L, cv) ∉ fromVisits N1 t fuel key r)
    (hval : ∀ x c n y, (x, c) ∈ fromVisits N1 t fuel key r → N1 x = some n → n.leaf = true →
      (n.searchEq t c).map (·.y) = some y → V1 y = V2 y) :
    getFromR N1 V1 t fuel key r = getFromR N2 V2 t fuel key r := by
  apply getFromR_frame N1 N2 V1 V2 t fuel hfuel key r _ hval
  intro q hq
  by_cases hx : q.1 = L
  · obtain ⟨n1, n2, h1, h2, hl1, hl2, hs⟩ := hL
    have hc : q.2 ≠ cv := by
      intro hc
      apply hnot
      have : q = (L, cv) := by rw [← hx, ← hc]
      rw [← this]
      exact hq
    right
    exact ⟨n1, n2, hx ▸ h1, hx ▸ h2, hl1, hl2, hs q.2 hc⟩
  · exact Or.inl (hN q.1 hx)

/-! ## The writer's reads keep what its state reads -/

/-- The writer's view is the base where it has a node. -/
def ViewCoherent (c : Ctx) (base : View BVal) : Prop :=
  ∀ x nd, c.view x = some nd → base x = some nd

theorem viewCoherent_ctxOf (p : Params) (ts : List Tx) :
    ViewCoherent (ctxOf p ts) (viewOf (treeRun p ts)) := by
  intro x nd h
  simp only [ctxOf, rootless] at h
  split at h
  · cases h
  · obtain ⟨nd0, h0, hnd⟩ := view_some p _ _ _ _ h
    subst hnd
    rw [upTo_of_timesLE _ _ (treeRun_timesLE p ts) x nd0 h0]
    exact h0

/-- Two writer states read alike: the same nodes and values through the base,
the same super root, taken-back nodes, values made, next id and trail. -/
def ReadsAs (p : Params) (base : View BVal) (w v : W) : Prop :=
  wNode p base v = wNode p base w ∧ v.top = w.top ∧ v.taken = w.taken ∧ v.vals = w.vals ∧
    v.next = w.next

theorem ReadsAs.refl (p : Params) (base : View BVal) (w : W) : ReadsAs p base w w :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem ReadsAs.trans (p : Params) (base : View BVal) (u v w : W) (h1 : ReadsAs p base u v)
    (h2 : ReadsAs p base v w) : ReadsAs p base u w :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem ReadsAs.value (p : Params) (base : View BVal) (w v : W) (h : ReadsAs p base w v) :
    wValue base v = wValue base w := by
  funext y
  simp only [wValue, h.2.2.1, h.2.2.2.1]

/-- A read of node x caches what the state reads of it, if it is not taken back. -/
theorem writerWP_getNode_reads (x : NodeId) (c : Ctx) (w : W) (base : View BVal)
    (hvc : ViewCoherent c base) :
    WriterWP (getNode x) c w (fun n v => ReadsAs c.p base w v ∧ v.nodes.lookup x = some n ∧
      (w.taken.contains x = false → wNode c.p base w x = some n)) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    refine ⟨ReadsAs.refl _ _ _, hn, fun ht => ?_⟩
    have ht' : x ∉ w.taken := by simpa using ht
    simp [wNode, ht', hn]
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hv
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hkind
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        have hb := hvc x nd hv
        have hk : knodeOf c.p base x =
            some { leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist } := by
          simp only [knodeOf, hb]
          simp only [Bool.or_eq_true, decide_eq_true_eq] at hkind
          simp [hkind]
        refine ⟨⟨?_, rfl, rfl, rfl, rfl⟩, by simp [List.lookup_append, hn], ?_⟩
        · funext y
          simp only [wNode]
          split
          · rfl
          · rw [List.lookup_append]
            by_cases hy : y = x
            · subst hy
              rw [hn]
              simp [hk]
            · cases hl : w.nodes.lookup y with
              | some m => rfl
              | none =>
                have hyx : (y == x) = false := by simpa using hy
                simp [List.lookup, hyx]
        · intro ht
          have ht' : x ∉ w.taken := by simpa using ht
          simp [wNode, ht', hn, hk]
    · exact writerWP_throw _ _ _ _

theorem writerWP_pathAdd_reads (cv : Option Nat) (x : NodeId) (c : Ctx) (w : W)
    (base : View BVal) :
    WriterWP (pathAdd cv x) c w (fun _ v => ReadsAs c.p base w v) := by
  simp only [pathAdd, writerWP_modify]
  exact ⟨by funext y; rfl, rfl, rfl, rfl, rfl⟩

/-- A descent of the writer follows its state's reading to the segment leaf
of cv, if no node on the way was taken back. -/
theorem writerWP_descendLte_reads (cv : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (f : Nat) (x : NodeId) (w : W),
    (∀ q ∈ eqVisits (wNode c.p base w) c.i cv f x, w.taken.contains q.1 = false) →
    WriterWP (descendLte cv f x) c w (fun L v => ReadsAs c.p base w v ∧
      ∃ n, wNode c.p base w L = some n ∧ n.leaf = true ∧ v.nodes.lookup L = some n ∧
        (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv f x ∧
        getEqR (wNode c.p base w) c.i cv f x = (n.searchEq c.i cv).map (·.y)) := by
  intro f
  induction f with
  | zero => intro x w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w ht
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_getNode_reads x c w base hvc) ?_
    intro n v ⟨hrv, hlk, hwn⟩
    have hx := hwn (ht (x, cv) (by simp [eqVisits]))
    split
    · rename_i hleaf
      simp only [writerWP_pure]
      refine ⟨hrv, n, hx, hleaf, hlk, by simp [eqVisits], ?_⟩
      simp [getEqR, hx, hleaf]
    · rename_i hleaf
      split
      · exact writerWP_throw _ _ _ _
      · rename_i fd hfd
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_pathAdd_reads (some fd.c) fd.y c v base) ?_
        intro _ v1 hr1
        have hr01 := ReadsAs.trans _ _ _ _ _ hrv hr1
        have hvis : ∀ q ∈ eqVisits (wNode c.p base v1) c.i cv f fd.y,
            v1.taken.contains q.1 = false := by
          intro q hq
          rw [hr01.1] at hq
          rw [hr01.2.2.1]
          apply ht q
          simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
          exact Or.inr hq
        refine writerWP_mono (ih fd.y v1 hvis) ?_
        intro L v2 ⟨hr2, m, hm, hml, hlk2, hvisL, hget⟩
        rw [hr01.1] at hm hvisL hget
        refine ⟨ReadsAs.trans _ _ _ _ _ hr01 hr2, m, hm, hml, hlk2, ?_, ?_⟩
        · simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
          exact Or.inr hvisL
        · simp only [getEqR, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd]
          exact hget

/-! ## A put into a segment leaf with room -/

theorem KNode.add_times (n : KNode) (t : Time) (k : Klong) (hk : ∀ s, k ≠ .time s)
    (h : ∀ s, Klong.time s ∈ n.ks → s ≤ t) : ∀ s, Klong.time s ∈ (n.add t k).ks → s ≤ t := by
  intro s hs
  unfold KNode.add at hs
  split at hs
  · split at hs
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
      rcases hs with hs | hs | hs
      · exact h s hs
      · cases hs; exact Nat.le_refl _
      · exact absurd hs.symm (hk s)
    · simp only [List.mem_append, List.mem_singleton] at hs
      rcases hs with hs | hs
      · exact h s hs
      · exact absurd hs.symm (hk s)
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hs
    rcases hs with hs | hs | hs
    · exact h s hs
    · cases hs; exact Nat.le_refl _
    · exact absurd hs.symm (hk s)

theorem KNode.searchEq_live (n : KNode) (t : Time) (hw : klongsWf n.ks = true)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) :
    (n.searchEq t c).map (·.y) = n.live.lookup c := by
  rw [searchEqSpec n t c hw, KNode.liveAt_eq_live_prefix,
    prefixAt_of_times n.ks t (fun k hk s hs => by subst hs; exact ht s hk)]

/-- A key klong added at time t: the search of its compare value at t gives its
pointer, of any other what it gave. -/
theorem KNode.add_key_searchEq (n : KNode) (t : Time) (cv : Nat) (y : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (c : Nat) :
    ((n.add t (.key cv y)).searchEq t c).map (·.y) =
      if cv == c then some y else (n.searchEq t c).map (·.y) := by
  rw [KNode.searchEq_live _ t (KNode.add_key_wf n t cv y hw)
      (KNode.add_times n t _ (fun s h => by cases h) ht) c,
    KNode.add_key_live_lookup_of_wf n t cv c y hw, KNode.searchEq_live n t hw ht c]

theorem lookup_cons_eq {β : Type} (a : NodeId) (b : β) (l : List (NodeId × β)) (y : NodeId)
    (h : y = a) : ((a, b) :: l).lookup y = some b := by
  subst h
  show (match y == y with | true => some b | false => l.lookup y) = some b
  rw [beq_self_eq_true]

theorem lookup_cons_ne {β : Type} (a : NodeId) (b : β) (l : List (NodeId × β)) (y : NodeId)
    (h : y ≠ a) : ((a, b) :: l).lookup y = l.lookup y := by
  have hb : (y == a) = false := by simpa using h
  show (match y == a with | true => some b | false => l.lookup y) = l.lookup y
  rw [hb]

theorem lookup_map_replace_other (ns : List (NodeId × KNode)) (x y : NodeId) (n : KNode)
    (hy : y ≠ x) : (ns.map (fun q => if q.1 == x then (x, n) else q)).lookup y = ns.lookup y := by
  induction ns with
  | nil => rfl
  | cons a ns ih =>
    obtain ⟨a1, a2⟩ := a
    rw [List.map_cons]
    by_cases ha : a1 = x
    · subst ha
      rw [if_pos (by simp), lookup_cons_ne _ _ _ _ hy, lookup_cons_ne _ _ _ _ hy, ih]
    · rw [if_neg (by simpa using ha)]
      by_cases hya : y = a1
      · rw [lookup_cons_eq _ _ _ _ hya, lookup_cons_eq _ _ _ _ hya]
      · rw [lookup_cons_ne _ _ _ _ hya, lookup_cons_ne _ _ _ _ hya, ih]

theorem lookup_map_replace_self (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hx : ∃ q ∈ ns, q.1 = x) : (ns.map (fun q => if q.1 == x then (x, n) else q)).lookup x = some n := by
  induction ns with
  | nil => obtain ⟨q, hq, _⟩ := hx; cases hq
  | cons a ns ih =>
    obtain ⟨a1, a2⟩ := a
    rw [List.map_cons]
    by_cases ha : a1 = x
    · subst ha
      rw [if_pos (by simp), lookup_cons_eq _ _ _ _ rfl]
    · rw [if_neg (by simpa using ha), lookup_cons_ne _ _ _ _ (fun h => ha h.symm)]
      obtain ⟨q, hq, hqx⟩ := hx
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact absurd hqx ha
      · exact ih ⟨q, hq', hqx⟩

theorem lookup_append_single_ne {β : Type} (l : List (NodeId × β)) (x y : NodeId) (b : β)
    (hy : y ≠ x) : (l ++ [(x, b)]).lookup y = l.lookup y := by
  rw [List.lookup_append]
  cases h : l.lookup y with
  | some m => rfl
  | none =>
    show (none : Option β).or (((x, b) :: []).lookup y) = none
    rw [lookup_cons_ne _ _ _ _ hy]
    rfl

theorem lookup_upsert (ns : List (NodeId × KNode)) (x y : NodeId) (n : KNode) :
    (upsert ns x n).lookup y = if y = x then some n else ns.lookup y := by
  unfold upsert
  split
  · rename_i hany
    obtain ⟨q, hq, hqx⟩ := List.any_eq_true.mp hany
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl]
      exact lookup_map_replace_self ns y n ⟨q, hq, by simpa using hqx⟩
    · rw [if_neg hy]
      exact lookup_map_replace_other ns x y n hy
  · rename_i hany
    by_cases hy : y = x
    · subst hy
      rw [if_pos rfl]
      apply lookup_append_single_self
      apply List.lookup_eq_none_iff.mpr
      intro q hq
      have h1 : ¬ (q.1 == y) = true := fun h => hany (List.any_eq_true.mpr ⟨q, hq, h⟩)
      simp only [beq_iff_eq] at h1
      simp only [bne_iff_ne, ne_eq]
      exact fun h => h1 h.symm
    · rw [if_neg hy]
      exact lookup_append_single_ne ns x y n hy

/-- The search of a segment tree, after a change of its leaf L alone, ends at
L with L's new search. -/
theorem getEqR_change_leaf (N1 N2 : NodeId → Option KNode) (t : Time) (cv : Nat) (L : NodeId)
    (n2 : KNode) (hN2 : N2 L = some n2) (hl2 : n2.leaf = true) :
    ∀ (f : Nat) (r : NodeId), (∀ q ∈ eqVisits N1 t cv f r, q.1 ≠ L → N1 q.1 = N2 q.1) →
      (L, cv) ∈ eqVisits N1 t cv f r → (∀ n1, N1 L = some n1 → n1.leaf = true) →
      getEqR N2 t cv f r = (n2.searchEq t cv).map (·.y) := by
  intro f
  induction f with
  | zero => intro r _ hL; simp [eqVisits] at hL
  | succ f ih =>
    intro r hN hL hl1
    by_cases hr : r = L
    · subst hr
      simp [getEqR, hN2, hl2]
    · have hrN := hN (r, cv) (by simp [eqVisits]) hr
      simp only at hrN
      simp only [eqVisits, List.mem_cons] at hL
      rcases hL with hL | hL
      · exact absurd (Prod.mk.inj hL).1.symm hr
      · simp only [getEqR]
        rw [← hrN]
        cases hn : N1 r with
        | none => rw [hn] at hL; cases hL
        | some m =>
          rw [hn] at hL
          simp only at hL ⊢
          split at hL
          · cases hL
          · rename_i hml
            simp only [hml, Bool.false_eq_true, ↓reduceIte]
            cases hf : m.searchLte t cv with
            | none => rw [hf] at hL; cases hL
            | some fd =>
              rw [hf] at hL
              simp only
              apply ih fd.y _ hL hl1
              intro q hq hqL
              apply hN q _ hqL
              simp only [eqVisits, hn, hml, Bool.false_eq_true, ↓reduceIte, hf, List.mem_cons]
              exact Or.inr hq

/-! ## A delete of a key that has no value -/

theorem KNode.searchEq_noop (n : KNode) (t : Time) (cv : Nat) (hw : klongsWf n.ks = true)
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hu : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    (n.searchEq t cv).map (·.y) = none := by
  rw [KNode.searchEq_live n t hw ht, KNode.delete_lookup_noop n cv hu cv]
  simp

/-! ## A delete that leaves its leaf a live klong (merges off) -/

theorem writerWP_ghOf_cached (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (hn : w.nodes.lookup x = some n) (post : Nat × Nat → W → Prop) (hp : ∀ gh, post gh w) :
    WriterWP (ghOf x) c w post := by
  unfold ghOf
  simp only [writerWP_bind]
  rw [writerWP_getNode_known x n c w hn]
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact hp _
  · exact writerWP_throw _ _ _ _

theorem KNode.setAt_last_times (n : KNode) (old bits : List Nat) (t : Time)
    (hlast : n.ks.getLast? = some (.del old)) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ s, Klong.time s ∈ (n.setAt (n.size - 1) (.del bits)).ks → s ≤ t := by
  obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
  have hnew : (n.setAt (n.size - 1) (.del bits)).ks = pre ++ [.del bits] := by
    simp [KNode.setAt, KNode.size, hpre]
  intro s hs
  rw [hnew] at hs
  rcases List.mem_append.mp hs with hs | hs
  · exact ht s (by rw [hpre]; exact List.mem_append_left _ hs)
  · simp at hs

/-! ## Keys of several segments -/

/-- The root of the segment tree that a key's prefix leads to. -/
def segRootR (N : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    List Nat → NodeId → Option NodeId
  | [], r => some r
  | c :: rest, r =>
    match getEqR N t c fuel r with
    | some y => if (N y).isSome then segRootR N t fuel rest y else none
    | none => none

theorem getFromR_append (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (pre : List Nat) (cv : Nat) (r : NodeId) :
    getFromR N V t fuel (pre ++ [cv]) r =
      (segRootR N t fuel pre r).bind (fun rk => getFromR N V t fuel [cv] rk) := by
  induction pre generalizing r with
  | nil => rfl
  | cons c rest ih =>
    have hne : rest ++ [cv] ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
      cases h : rest ++ [cv] with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [List.cons_append]
    rw [he]
    simp only [getFromR, segRootR]
    rw [← he]
    cases getEqR N t c fuel r with
    | none => rfl
    | some y =>
      simp only
      split
      · exact ih y
      · rfl

theorem fromVisits_append (N : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (pre : List Nat) (cv : Nat) (r rk : NodeId) (hrk : segRootR N t fuel pre r = some rk) :
    ∀ q ∈ eqVisits N t cv fuel rk, q ∈ fromVisits N t fuel (pre ++ [cv]) r := by
  induction pre generalizing r with
  | nil =>
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    intro q hq
    exact hq
  | cons c rest ih =>
    intro q hq
    have hne : rest ++ [cv] ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
      cases h : rest ++ [cv] with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [segRootR] at hrk
    simp only [List.cons_append]
    rw [he]
    simp only [fromVisits]
    apply List.mem_append_right
    cases hg : getEqR N t c fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk ⊢
      split at hrk
      · rw [← he]; exact ih y hrk q hq
      · cases hrk

theorem fromVisits_cv_mem (N : NodeId → Option KNode) (t : Time) (fuel : Nat) :
    ∀ (key : List Nat) (r : NodeId) (q : NodeId × Nat), q ∈ fromVisits N t fuel key r → q.2 ∈ key := by
  have heq : ∀ (s f : Nat) (r : NodeId) (q : NodeId × Nat), q ∈ eqVisits N t s f r → q.2 = s := by
    intro s f
    induction f with
    | zero => intro r q hq; simp [eqVisits] at hq
    | succ f ih =>
      intro r q hq
      simp only [eqVisits, List.mem_cons] at hq
      rcases hq with rfl | hq
      · rfl
      · split at hq
        · cases hq
        · split at hq
          · cases hq
          · split at hq
            · cases hq
            · exact ih _ q hq
  intro key
  induction key with
  | nil => intro r q hq; simp [fromVisits] at hq
  | cons c rest ih =>
    intro r q hq
    cases rest with
    | nil =>
      simp only [fromVisits] at hq
      simp [heq c fuel r q hq]
    | cons d rest' =>
      simp only [fromVisits] at hq
      rcases List.mem_append.mp hq with hq | hq
      · simp [heq c fuel r q hq]
      · split at hq
        · exact List.mem_cons_of_mem c (ih _ q hq)
        · cases hq

theorem segRootR_frame (N1 N2 : NodeId → Option KNode) (t : Time) (fuel : Nat) (cv : Nat)
    (hsome : ∀ x, (N1 x).isSome = (N2 x).isSome) :
    ∀ (pre : List Nat) (r : NodeId),
      (∀ q ∈ fromVisits N1 t fuel (pre ++ [cv]) r, q.2 ≠ cv → AgreeAt N1 N2 t q.1 q.2) →
      cv ∉ pre → segRootR N1 t fuel pre r = segRootR N2 t fuel pre r := by
  intro pre
  induction pre with
  | nil => intro r _ _; rfl
  | cons c rest ih =>
    intro r h hcv
    have hc : c ≠ cv := fun h' => hcv (by simp [h'])
    have hne : rest ++ [cv] ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
      cases h' : rest ++ [cv] with
      | nil => exact absurd h' hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    have hvis : ∀ q ∈ fromVisits N1 t fuel (c :: d :: rest') r, q.2 ≠ cv →
        AgreeAt N1 N2 t q.1 q.2 := fun q hq => h q (by rw [List.cons_append, he]; exact hq)
    simp only [fromVisits] at hvis
    have h1 : ∀ q ∈ eqVisits N1 t c fuel r, AgreeAt N1 N2 t q.1 q.2 := by
      intro q hq
      apply hvis q (List.mem_append_left _ hq)
      have := fromVisits_cv_mem N1 t fuel [c] r q (by simpa [fromVisits] using hq)
      simp at this
      rw [this]; exact hc
    obtain ⟨e1, _⟩ := getEqR_frame N1 N2 t c fuel r h1
    simp only [segRootR]
    rw [← e1]
    cases hg : getEqR N1 t c fuel r with
    | none => rfl
    | some y =>
      simp only
      rw [← hsome y]
      split
      · apply ih y _ (fun h' => hcv (List.mem_cons_of_mem c h'))
        intro q hq hq2
        apply hvis q _ hq2
        apply List.mem_append_right
        rw [hg]
        simp only
        rw [← he]
        exact hq
      · rfl

/-- After a change of a leaf at a key's compare value alone, the key reads what
the leaf's new search gives and every other key what it read, for a key of any
number of segments: the change is in
the leaf L of its last segment's tree, whose root rk its prefix leads to. -/
theorem wGet_leaf_change_seg (p : Params) (base : View BVal) (i : Time) (w w' : W)
    (L : NodeId) (pre : List Nat) (cv : Nat) (rk : NodeId) (n n2 : KNode) (hfuel : 1 ≤ p.fuel)
    (htop : w'.top = w.top)
    (hN : ∀ x, x ≠ L → wNode p base w x = wNode p base w' x)
    (hn : wNode p base w L = some n) (hn2 : wNode p base w' L = some n2)
    (hl : n.leaf = true) (hl2 : n2.leaf = true)
    (hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (n2.searchEq i c').map (·.y))
    (hrk : segRootR (wNode p base w) i p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits (wNode p base w) i cv p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode p base w) i p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode p base w) i cv p.fuel rk →
      wNode p base w x = some m → m.leaf = true → key' = pre ++ [cv])
    (hV : ∀ key' x c' m y, key' ≠ pre ++ [cv] →
      (x, c') ∈ fromVisits (wNode p base w) i p.fuel key' w.top.rootKey →
      wNode p base w x = some m → m.leaf = true → (m.searchEq i c').map (·.y) = some y →
      wValue base w y = wValue base w' y) :
    wGet p i base w' (pre ++ [cv]) = ((n2.searchEq i cv).map (·.y)).bind (wValue base w') ∧
      ∀ key', keyWf key' = true → key' ≠ pre ++ [cv] →
        wGet p i base w' key' = wGet p i base w key' := by
  have hsome : ∀ x, (wNode p base w x).isSome = (wNode p base w' x).isSome := by
    intro x
    by_cases hx : x = L
    · subst hx; rw [hn, hn2]; rfl
    · rw [hN x hx]
  have hagree : ∀ (q : NodeId × Nat), q.2 ≠ cv →
      AgreeAt (wNode p base w) (wNode p base w') i q.1 q.2 := by
    intro q hq
    by_cases hx : q.1 = L
    · right
      exact ⟨n, n2, hx ▸ hn, hx ▸ hn2, hl, hl2, hs q.2 hq⟩
    · exact Or.inl (hN q.1 hx)
  constructor
  · unfold wGet
    rw [htop, getFromR_append, ← segRootR_frame (wNode p base w) (wNode p base w') i p.fuel cv
      hsome pre w.top.rootKey (fun q _ hq => hagree q hq) hcv, hrk]
    simp only [Option.bind_some, getFromR]
    rw [getEqR_change_leaf (wNode p base w) (wNode p base w') i cv L n2 hn2 hl2 p.fuel rk
      (fun q _ hq => hN q.1 hq) hvisL (fun n1 h1 => by rw [hn] at h1; cases h1; exact hl)]
  · intro key' hkey' hk
    unfold wGet
    rw [htop]
    symm
    apply getFromR_leaf_change (wNode p base w) (wNode p base w') (wValue base w)
      (wValue base w') i p.fuel hfuel L cv hN ⟨n, n2, hn, hn2, hl, hl2, hs⟩ key' w.top.rootKey
    · intro hmem
      exact hk (huniq key' L n hkey' hmem hvisL hn hl)
    · intro x c' m y hx hm hml hsy
      exact hV key' x c' m y hk hx hm hml hsy

/-- The writer's walk down a key's prefix, every segment there: reads only,
and gets to the root of the last segment's tree. -/
theorem writerWP_putSegs_prefix (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (cv : Nat) (post : Bool → W → Prop) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W),
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      (∀ w', ReadsAs c.p base w w' → WriterWP (setValue rk cv key value) c w' post) →
      WriterWP (putSegs key value (pre ++ [cv]) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w _ hrk hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append, putSegs.eq_2]
    exact hcont w (ReadsAs.refl _ _ _)
  | cons s rest ih =>
    intro r rk w ht hrk hcont
    have hne : rest ++ [cv] ≠ [] := by simp
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ [cv]) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · rename_i hysome
        obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
          cases h' : rest ++ [cv] with
          | nil => exact absurd h' hne
          | cons d rest' => exact ⟨d, rest', rfl⟩
        have hvis : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (s :: d :: rest') r,
            w.taken.contains q.1 = false := by
          intro q hq; apply ht q; rw [List.cons_append, he]; exact hq
        simp only [fromVisits] at hvis
        have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
            w.taken.contains q.1 = false := fun q hq => hvis q (List.mem_append_left _ hq)
        unfold setNode
        wpSimplify
        refine writerWP_mono (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1) ?_
        intro L w3 ⟨hr3, n, hn, hnl, hlk3, _, hget⟩
        rw [writerWP_getNode_known L n c _ hlk3]
        rw [hg] at hget
        cases hfd : n.searchEq c.i s with
        | none => rw [hfd] at hget; cases hget
        | some fd =>
          rw [hfd] at hget
          simp only [Option.map_some, Option.some.injEq] at hget
          simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
          rw [← hget]
          generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, y)] } : W) = w4
          have hr04 : ReadsAs c.p base w w4 := by
            subst hw4
            exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
          apply ih y rk w4
          · intro q hq
            rw [hr04.2.2.1]
            rw [hr04.1] at hq
            apply hvis q
            apply List.mem_append_right
            rw [hg]
            simp only
            rw [← he]
            exact hq
          · rw [hr04.1]; exact hrk
          · intro w' hr'
            exact hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr')
      · cases hrk

theorem keyWf_last_notin (pre : List Nat) (cv : Nat) (h : keyWf (pre ++ [cv]) = true) :
    cv ∉ pre := by
  have hlast : ∀ (l : List Nat), keyWf (l ++ [cv]) = true → segLen cv ≠ 7 := by
    intro l
    induction l with
    | nil => intro hk; simp only [List.nil_append, keyWf, Bool.and_eq_true, bne_iff_ne, ne_eq] at hk; exact hk.2
    | cons a l ih =>
      intro hk
      cases l with
      | nil =>
        simp only [List.cons_append, List.nil_append, keyWf, Bool.and_eq_true] at hk
        exact ih (by simpa [keyWf] using hk.2)
      | cons b l' =>
        simp only [List.cons_append, keyWf, Bool.and_eq_true] at hk
        exact ih (by simpa using hk.2)
  have hpre : ∀ (l : List Nat), keyWf (l ++ [cv]) = true → ∀ a ∈ l, segLen a = 7 := by
    intro l
    induction l with
    | nil => intro _ a ha; cases ha
    | cons a l ih =>
      intro hk b hb
      have hk' : keyWf (a :: (l ++ [cv])) = true := by simpa using hk
      obtain ⟨d, rest, he⟩ : ∃ d rest, l ++ [cv] = d :: rest := by
        cases h' : l ++ [cv] with
        | nil => simp at h'
        | cons d rest => exact ⟨d, rest, rfl⟩
      rw [he] at hk'
      simp only [keyWf, Bool.and_eq_true, beq_iff_eq] at hk'
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hk'.1.2
      · exact ih (by rw [he]; exact hk'.2) b hb
  intro hcv
  exact hlast pre h (hpre pre h cv hcv)

/-- A put into a segment leaf with room (no split, no compaction) changes what
the writer's state reads by the put alone, for a key of any number of segments,
every segment of its prefix there. -/
theorem writerWP_put_room_seg (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false)
    (hnext : w.taken.contains w.next = false ∧ w.vals.lookup w.next = none)
    (huniq : ∀ key' x n, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n → n.leaf = true → key' = pre ++ [cv])
    (hfresh : ∀ key' x c' n y,
      (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n → n.leaf = true → (n.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, hget⟩
  rw [hr0.1] at hn hvisL hget
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hwf, htimes, hroom, hdead⟩ := hleaf L n hvisL hn hnl
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = true := by
    rw [hnext3, hdead]; simp [hroom]
  simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
  suffices hfin : ∀ w6 : W, w6.taken = w.taken → w6.top = w.top →
      w6.vals = w.vals ++ [(w.next, h)] →
      (∀ x, w6.nodes.lookup x = if x = L then some (n.add c.i (.key cv w.next))
        else w3.nodes.lookup x) →
      ∀ key', keyWf key' = true → wGet c.p c.i base w6 key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key' by
    refine hfin _ hr03.2.2.1 hr03.2.1 ?_ ?_
    · simp only; rw [hr03.2.2.2.1, hnext3]
    · intro x; simp only; rw [lookup_upsert, hnext3]
  intro w6 h6taken h6top h6vals h6nodes
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hN : ∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x := by
    intro x hx
    rw [← hr03.1]
    simp only [wNode, h6taken, h6nodes, if_neg hx, hr03.2.2.1]
  have hNL : wNode c.p base w6 L = some (n.add c.i (.key cv w.next)) := by
    simp only [wNode, h6taken, hLt, Bool.false_eq_true, ↓reduceIte, h6nodes, if_pos rfl]
  have hV : ∀ y, y ≠ w.next → wValue base w y = wValue base w6 y := by
    intro y hy
    simp only [wValue, h6taken, h6vals, lookup_append_single_ne _ _ _ _ hy]
  have hVv : wValue base w6 w.next = some h := by
    simp only [wValue, h6taken, hnext.1, Bool.false_eq_true, ↓reduceIte, h6vals,
      lookup_append_single_self _ _ _ hnext.2]
  have hsearch : ∀ c', ((n.add c.i (.key cv w.next)).searchEq c.i c').map (·.y) =
      if cv == c' then some w.next else (n.searchEq c.i c').map (·.y) :=
    KNode.add_key_searchEq n c.i cv w.next hwf htimes
  have hleaf' : (n.add c.i (.key cv w.next)).leaf = true := by rw [KNode.add_leaf]; exact hnl
  obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w6 L pre cv rk n _ hfuel h6top hN
    hn hNL hnl hleaf' (fun c' hc' => by
      have hb : (cv == c') = false := by
        cases hcb : (cv == c') with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hcb).symm hc'
      rw [hsearch c', hb]
      rfl)
    hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun key' x c' m y _ hx hm hml hs => hV y (hfresh key' x c' m y hx hm hml hs))
  intro key' hkey'
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    rw [hown, hsearch cv]
    simp [hVv]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    exact hother key' hkey' (fun h' => hk h'.symm)

/-- A delete of a key that has no value changes nothing that the writer's state
reads, and the key reads none, for a key of any number of segments, every
segment of its prefix there. -/
theorem writerWP_del_noop_seg (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, hget⟩
  rw [hr0.1] at hn hvisL hget
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hwf, htimes, hnoop⟩ := hleaf L n hvisL hn hnl
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnoopb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by
    rw [hnoop]; simp
  simp only [hnoopb, ↓reduceIte, writerWP_pure, Bool.not_true, Bool.false_eq_true]
  intro key' hkey'
  have hsame : wGet c.p c.i base w3 key' = wGet c.p c.i base w key' := by
    unfold wGet
    rw [hr03.1, hr03.2.1, ReadsAs.value _ _ _ _ hr03]
  rw [hsame]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    unfold wGet
    rw [getFromR_append, hrk]
    simp only [Option.bind_some, getFromR]
    rw [hget, KNode.searchEq_noop n c.i cv hwf htimes hnoop]
    rfl
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]

/-! ## A node moved to a new id -/

/-- Reader N2 is reader N1 with node L at id y (ren: L to y, any other id to
itself), on the ids of the domain D: same kinds, and searches that give the
renamed pointers. -/
def RenSim (N1 N2 : NodeId → Option KNode) (t : Time) (D : NodeId → Prop) (L y : NodeId) :
    Prop :=
  ∀ x, D x →
    let x2 := if x = L then y else x
    ((N1 x).isSome = (N2 x2).isSome) ∧ ∀ n1 n2, N1 x = some n1 → N2 x2 = some n2 →
      n1.leaf = n2.leaf ∧ ∀ c,
        (n1.leaf = true → ((n1.searchEq t c).map (·.y)).map (fun z => if z = L then y else z) =
          (n2.searchEq t c).map (·.y) ∧ ∀ fd, n1.searchEq t c = some fd → D fd.y) ∧
        (n1.leaf = false → ((n1.searchLte t c).map (·.y)).map (fun z => if z = L then y else z) =
          (n2.searchLte t c).map (·.y) ∧ ∀ fd, n1.searchLte t c = some fd → D fd.y)

theorem getEqR_ren (N1 N2 : NodeId → Option KNode) (t : Time) (D : NodeId → Prop) (L y : NodeId)
    (hS : RenSim N1 N2 t D L y) (c : Nat) :
    ∀ (f : Nat) (x : NodeId), D x →
      (getEqR N1 t c f x).map (fun z => if z = L then y else z) =
        getEqR N2 t c f (if x = L then y else x) := by
  intro f
  induction f with
  | zero => intro x _; rfl
  | succ f ih =>
    intro x hx
    obtain ⟨hsome, hrest⟩ := hS x hx
    simp only [getEqR]
    cases h1 : N1 x with
    | none =>
      rw [h1] at hsome
      cases h2 : N2 (if x = L then y else x) with
      | none => rfl
      | some n2 => rw [h2] at hsome; cases hsome
    | some n1 =>
      rw [h1] at hsome
      cases h2 : N2 (if x = L then y else x) with
      | none => rw [h2] at hsome; cases hsome
      | some n2 =>
        obtain ⟨hl, hc⟩ := hrest n1 n2 h1 h2
        simp only
        cases hl1 : n1.leaf with
        | true =>
          rw [hl1] at hl
          simp only [← hl, ↓reduceIte]
          exact ((hc c).1 hl1).1
        | false =>
          rw [hl1] at hl
          simp only [← hl, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨hs, hD⟩ := (hc c).2 hl1
          cases hf1 : n1.searchLte t c with
          | none =>
            rw [hf1] at hs
            cases hf2 : n2.searchLte t c with
            | none => rfl
            | some f2 => rw [hf2] at hs; cases hs
          | some f1 =>
            rw [hf1] at hs
            cases hf2 : n2.searchLte t c with
            | none => rw [hf2] at hs; cases hs
            | some f2 =>
              rw [hf2] at hs
              simp only [Option.map_some, Option.some.injEq] at hs
              simp only
              rw [← hs]
              exact ih f1.y (hD f1 hf1)

theorem getEqR_ren_dom (N1 N2 : NodeId → Option KNode) (t : Time) (D : NodeId → Prop)
    (L y : NodeId) (hS : RenSim N1 N2 t D L y) (c : Nat) :
    ∀ (f : Nat) (x z : NodeId), D x → getEqR N1 t c f x = some z → D z := by
  intro f
  induction f with
  | zero => intro x z _ h; simp [getEqR] at h
  | succ f ih =>
    intro x z hx h
    obtain ⟨_, hrest⟩ := hS x hx
    simp only [getEqR] at h
    cases h1 : N1 x with
    | none => rw [h1] at h; cases h
    | some n1 =>
      rw [h1] at h
      simp only at h
      cases h2 : N2 (if x = L then y else x) with
      | none =>
        have hs := (hS x hx).1
        rw [h1, h2] at hs
        cases hs
      | some n2 =>
        obtain ⟨_, hc⟩ := hrest n1 n2 h1 h2
        split at h
        · rename_i hl1
          cases hf : n1.searchEq t c with
          | none => rw [hf] at h; cases h
          | some fd =>
            rw [hf] at h
            simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]
            exact ((hc c).1 hl1).2 fd hf
        · rename_i hl1
          simp only [Bool.not_eq_true] at hl1
          cases hf : n1.searchLte t c with
          | none => rw [hf] at h; cases h
          | some fd =>
            rw [hf] at h
            simp only at h
            exact ih fd.y z (((hc c).2 hl1).2 fd hf) h

/-- A reading through a reader with node L moved to id y is the reading before,
from the renamed root, given values that the move keeps. -/
theorem getFromR_ren (N1 N2 : NodeId → Option KNode) (V1 V2 : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (D : NodeId → Prop) (L y : NodeId) (hS : RenSim N1 N2 t D L y)
    (hV : ∀ a, V1 a = V2 (if a = L then y else a)) :
    ∀ (key : List Nat) (r : NodeId), D r →
      getFromR N1 V1 t fuel key r = getFromR N2 V2 t fuel key (if r = L then y else r) := by
  intro key
  induction key with
  | nil => intro r _; rfl
  | cons cv rest ih =>
    intro r hr
    have he := getEqR_ren N1 N2 t D L y hS cv fuel r hr
    cases rest with
    | nil =>
      simp only [getFromR]
      rw [← he]
      cases hg : getEqR N1 t cv fuel r with
      | none => rfl
      | some z => simp only [Option.map_some, Option.bind_some]; exact hV z
    | cons d rest' =>
      simp only [getFromR]
      rw [← he]
      cases hg : getEqR N1 t cv fuel r with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        have hz : D z := getEqR_ren_dom N1 N2 t D L y hS cv fuel r z hr hg
        have hsome : (N1 z).isSome = (N2 (if z = L then y else z)).isSome := (hS z hz).1
        rw [← hsome]
        split
        · exact ih z hz
        · rfl

/-! ## A put into a full leaf that the transaction made: a time split in place -/

theorem writerWP_replaceOrAdd_last (n : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd (n.lastVersion c.i) ins) c w (fun out v => v = w ∧
      out.leaf = n.leaf ∧ klongsWf out.ks = true ∧ (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
      ∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) := by
  obtain ⟨pairs, hks, horder⟩ := n.lastVersionGivenDel_order c.i n.lastBitmap
  have hnd : (pairs.map Prod.fst).Nodup := List.pairwise_map.mpr
    (horder.imp (by intro a b hab; omega))
  have he : n.lastVersion c.i = ⟨n.leaf, newKlongs c.i pairs⟩ := by
    unfold KNode.lastVersion
    cases hout : n.lastVersionGivenDel c.i n.lastBitmap
    rw [hout] at hks
    simp only at hks
    subst hks
    simp only [newKlongs, KNode.mk.injEq, and_true]
    have h2 : (n.lastVersionGivenDel c.i n.lastBitmap).leaf = n.leaf := rfl
    rw [hout] at h2
    exact h2
  have hlookup : ∀ q, pairs.lookup q = n.live.lookup q := by
    intro q
    have hh := n.lastVersionGivenDel_pairs_lookup c.i n.lastBitmap q
    rw [KNode.live_lookup]
    simpa [hks, List.filterMap_map, Function.comp_def] using hh
  rw [he]
  refine writerWP_mono (writerWP_replaceOrAdd_map n.leaf pairs ins hnd c w) ?_
  rintro out v ⟨hleaf, ⟨more, hmore, _⟩, hmap, hv⟩
  refine ⟨hv, hleaf, by rw [hmore]; exact klongsWf_newKlongs _ _, ?_, ?_⟩
  · intro s hs
    rw [hmore] at hs
    simp only [newKlongs, List.mem_cons, List.mem_map] at hs
    rcases hs with hs | ⟨q, _, hq⟩
    · cases hs; exact Nat.le_refl _
    · cases hq
  · intro q
    rw [hmap, hlookup]

end SIS.Tree
