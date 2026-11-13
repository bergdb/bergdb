import SIS.Tree.GetOpInv
import SIS.Tree.KlongAppend
import SIS.Tree.NodeMap

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

theorem lookup_append_single_self {β : Type} (l : List (NodeId × β)) (x : NodeId) (b : β)
    (hn : l.lookup x = none) : (l ++ [(x, b)]).lookup x = some b := by
  rw [List.lookup_append, hn]
  show (none : Option β).or (((x, b) :: []).lookup x) = some b
  rw [lookup_cons_eq _ _ _ _ rfl]
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

/-- A put of a key of one segment into a segment leaf with room (no split, no
compaction) changes what the writer's state reads by the put alone. The
premises are what an invariant of the writer's state inside a transaction must
give: no node on the key's path taken back; the leaf's klongs well formed, of
no later time, with room; the next id fresh; and the uniqueness that TP7's
invariant lacks (`sharedSegment_changes_other_key`): no other key searches the
key's compare value at its leaf. -/
theorem writerWP_put_room (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (ht : ∀ q ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false)
    (hnext : w.taken.contains w.next = false ∧ w.vals.lookup w.next = none)
    (huniq : ∀ key' x n, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some n → n.leaf = true → key' = [cv])
    (hfresh : ∀ key' x c' n y,
      (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n → n.leaf = true → (n.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put [cv] h) == key' then Op.value (.put [cv] h) else wGet c.p c.i base w key') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2) c.i cv c.p.fuel w.top.rootKey,
      w2.taken.contains q.1 = false := by
    rw [hr02.1, hr02.2.2.1]; exact ht
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel w.top.rootKey w2 ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, hget⟩
  rw [hr02.1] at hn hvisL hget
  have hr03 := ReadsAs.trans _ _ _ _ _ hr02 hr23
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
        if Op.key (.put [cv] h) == key' then Op.value (.put [cv] h)
        else wGet c.p c.i base w key' by
    refine hfin _ hr03.2.2.1 hr03.2.1 ?_ ?_
    · simp only; rw [hr03.2.2.2.1, hnext3]
    · intro x; simp only; rw [lookup_upsert, hnext3]
  intro w6 h6taken h6top h6vals h6nodes
  have hLt : w.taken.contains L = false := ht (L, cv) hvisL
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
  have hleaf' : (n.add c.i (.key cv w.next)).leaf = true := by
    unfold KNode.add; split <;> (try split) <;> exact hnl
  intro key' hkey'
  unfold wGet
  rw [h6top]
  by_cases hk : [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    simp only [getFromR]
    rw [getEqR_change_leaf (wNode c.p base w) (wNode c.p base w6) c.i cv L _ hNL hleaf'
      c.p.fuel w.top.rootKey (fun q _ hq => hN q.1 hq) hvisL
      (fun n1 h1 => by rw [hn] at h1; cases h1; exact hnl), hsearch]
    simp [hVv]
  · have hk' : ([cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    symm
    apply getFromR_leaf_change (wNode c.p base w) (wNode c.p base w6) (wValue base w)
      (wValue base w6) c.i c.p.fuel hfuel L cv hN
      ⟨n, _, hn, hNL, hnl, hleaf', fun c' hc' => by
        have hb : (cv == c') = false := by
          cases hcb : (cv == c') with
          | false => rfl
          | true => exact absurd (beq_iff_eq.mp hcb).symm hc'
        rw [hsearch c', hb]
        rfl⟩
      key' w.top.rootKey
    · intro hmem
      exact hk (huniq key' L n hkey' hmem hvisL hn hnl).symm
    · intro x c' m y hx hm hml hs
      exact hV y (hfresh key' x c' m y hx hm hml hs)

end SIS.Tree