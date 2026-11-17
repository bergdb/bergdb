/-
The contract package (bergdb 030-10): `handleFullWith` when it does a space
split (Java's `Dag.spaceSplit` and `spaceSplitInPlace`): the full node x is
replaced by two nodes with the halves of its last version and the klongs set;
the parent, an inner node, gets the second half's klong (and the first
half's, if x is from before the transaction); at the space root a new root
names the two.
-/
import Contract.Proof.WriterCascadeDefs

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (M Ctx)

/-! ## 1. The steps of the writer -/

theorem ss_wp_step {α β : Type} {f : M α} {g : α → M β} {c : Ctx} {w w1 : MW} {a : α}
    {post : β → MW → Prop} (hf : f c w = .ok (a, w1)) (h : WP (g a) c w1 post) :
    WP (f >>= g) c w post := by
  intro r w' hr
  apply h r w'
  have : (f >>= g) c w = g a c w1 := by
    show (f c w).bind _ = _
    rw [hf]; rfl
  rw [← this]; exact hr

/-- The state after the count of the space splits. -/
def ssSp (w : MW) : MW := { w with spaceSplits := w.spaceSplits + 1 }

/-- The state after `note`. -/
def ssNote (w : MW) (t : String) : MW := { w with trail := t :: w.trail }

/-- The state after `setMadeFor`. -/
def ssMF (w : MW) (m : NodeId) (o : Option NodeId) : MW :=
  { w with madeFor := match o with
    | some o' => (m, o') :: w.madeFor
    | none => w.madeFor }

theorem ss_modify (c : Ctx) (w : MW) :
    (modify (fun w : MW => { w with spaceSplits := w.spaceSplits + 1 }) : M Unit) c w =
      .ok ((), ssSp w) := rfl

theorem ss_note (c : Ctx) (w : MW) (t : String) :
    SIS.Tree.note t c w = .ok ((), ssNote w t) := rfl

theorem ss_setMadeFor (c : Ctx) (w : MW) (m : NodeId) (o : Option NodeId) :
    SIS.Tree.setMadeFor m o c w = .ok ((), ssMF w m o) := by
  cases o <;> rfl

theorem ss_read (c : Ctx) (w : MW) : (read : M Ctx) c w = .ok (c, w) := rfl

theorem ss_pure {α : Type} (a : α) (c : Ctx) (w : MW) : (pure a : M α) c w = .ok (a, w) := rfl

/-! ## 2. Klongs -/

theorem ss_liveWith_mem (del : List Nat) : ∀ (l : List (Klong × Nat)) (m : List (Nat × NodeId))
    (a : Nat × NodeId),
    a ∈ l.foldl (fun m (ki : Klong × Nat) => match ki with
      | (k, i) => match k with
        | .key c y => if del.contains i then m else insertCv c y m
        | _ => m) m →
    a ∈ m ∨ ∃ i, (Klong.key a.1 a.2, i) ∈ l
  | [], m, a, h => Or.inl h
  | (k, i) :: r, m, a, h => by
    simp only [List.foldl_cons] at h
    rcases ss_liveWith_mem del r _ a h with h1 | ⟨i', h1⟩
    · cases k with
      | time t => exact Or.inl h1
      | del b => exact Or.inl h1
      | key c y =>
        simp only at h1
        split at h1
        · exact Or.inl h1
        · rcases mem_insertCv h1 with h2 | h2
          · right
            refine ⟨i, ?_⟩
            rw [h2]
            exact List.mem_cons_self
          · exact Or.inl h2
    · exact Or.inr ⟨i', List.mem_cons_of_mem _ h1⟩

/-- A live klong is a key klong of the node. -/
theorem ss_live_mem {ks : List Klong} {c : Nat} {y : NodeId} (h : (c, y) ∈ live ks) :
    Klong.key c y ∈ ks := by
  unfold live liveWith at h
  rcases ss_liveWith_mem (lastBitmap ks) ks.zipIdx [] (c, y) h with h1 | ⟨i, h1⟩
  · simp at h1
  · obtain ⟨hlt, heq⟩ := List.mem_zipIdx' h1
    have h2 : Klong.key c y = ks[i] := heq
    rw [h2]
    exact List.getElem_mem hlt

/-- A pair of a list in order set again: the same list. -/
theorem ss_insertCv_mem {L : List (Nat × NodeId)} (hs : L.Pairwise CvLt) {c : Nat} {y : NodeId}
    (hm : (c, y) ∈ L) : insertCv c y L = L := by
  obtain ⟨pre, post, he⟩ := List.append_of_mem hm
  have hpre : ∀ a ∈ pre, a.1 < c := by
    intro a ha
    rw [he, List.pairwise_append] at hs
    exact hs.2.2 a ha (c, y) List.mem_cons_self
  rw [he, tr_insertCv_replace post hpre]

theorem ss_key_ksOf {n : MNode} {c : Nat} {y : NodeId} (h : SIS.Tree.Klong.key c y ∈ n.ks) :
    Klong.key c y ∈ ksOf n :=
  List.mem_map_of_mem (f := kOf) h

theorem ss_time_ksOf {n : MNode} {t : Time} (h : SIS.Tree.Klong.time t ∈ n.ks) :
    Klong.time t ∈ ksOf n :=
  List.mem_map_of_mem (f := kOf) h

theorem ss_time_of_ksOf {n : MNode} {t : Time} (h : Klong.time t ∈ ksOf n) :
    SIS.Tree.Klong.time t ∈ n.ks := by
  obtain ⟨k, hk, e⟩ := List.mem_map.mp h
  rw [kOf_eq_time e] at hk
  exact hk

theorem ss_timesLe {n : MNode} {i : Time} (h : ∀ t, SIS.Tree.Klong.time t ∈ n.ks → t ≤ i) :
    TimesLe n i := fun t ht => h t (ss_time_of_ksOf ht)

/-! ## 3. The node before the transaction -/

theorem ss_prefix_append (t : Time) (E : List Klong) : ∀ (L : List Klong),
    ((∃ x, t < x ∧ Klong.time x ∈ L) ∨ (∃ x more, t < x ∧ E = Klong.time x :: more)) →
    prefixAt (L ++ E) t = prefixAt L t
  | [], h => by
    rcases h with ⟨x, _, hx⟩ | ⟨x, more, hx, rfl⟩
    · simp at hx
    · simp [prefixAt, List.takeWhile, Nat.not_le.mpr hx]
  | k :: L, h => by
    have hL : (∀ x, k = Klong.time x → x ≤ t) →
        prefixAt (L ++ E) t = prefixAt L t := by
      intro hk
      refine ss_prefix_append t E L ?_
      rcases h with ⟨x, hx, hm⟩ | h
      · rcases List.mem_cons.mp hm with e | hm
        · have h1 : (x : Nat) ≤ t := hk x e.symm
          exact absurd hx (Nat.not_lt.mpr h1)
        · exact Or.inl ⟨x, hx, hm⟩
      · exact Or.inr h
    unfold prefixAt at hL ⊢
    cases k with
    | time x' =>
      by_cases hx' : x' ≤ t
      · simp only [List.cons_append, List.takeWhile_cons, hx', decide_true, ite_true]
        rw [hL (fun x e => by cases e; exact hx')]
      · simp [hx']
    | key c y =>
      simp only [List.cons_append, List.takeWhile_cons, ite_true]
      rw [hL (fun x e => by cases e)]
    | del b =>
      simp only [List.cons_append, List.takeWhile_cons, ite_true]
      rw [hL (fun x e => by cases e)]

theorem ss_prefix_add {n : MNode} {i : Time} (hi : 0 < i) (c : Nat)
    (y : NodeId) : prefixAt (ksOf (n.add i (.key c y))) (i - 1) = prefixAt (ksOf n) (i - 1) := by
  rcases ksOf_add n i (.key c y) with ⟨he, _⟩ | ⟨he, lt, hl, hle⟩
  · rw [he]
    exact ss_prefix_append _ _ _ (Or.inr ⟨i, _, by omega, rfl⟩)
  · rw [he]
    refine ss_prefix_append _ _ _ (Or.inl ⟨lt, by omega, ?_⟩)
    exact lastT_mem (by rw [lastT_ksOf]; exact hl)

theorem ss_prefix_addAll {i : Time} (hi : 0 < i) (ins : List (Nat × NodeId)) : ∀ {n : MNode},
    prefixAt (ksOf (addAll i n ins)) (i - 1) = prefixAt (ksOf n) (i - 1) := by
  induction ins with
  | nil => intro n; rfl
  | cons cy ins ih =>
    intro n
    rw [addAll_cons, ih, ss_prefix_add hi]

theorem ss_split_prefix {i : Time} (hi : 0 < i) : ∀ (L : List Klong),
    (∀ t, Klong.time t ∈ L → t ≤ i) →
    L = prefixAt L (i - 1) ∨ ∃ more, L = prefixAt L (i - 1) ++ Klong.time i :: more
  | [], _ => Or.inl rfl
  | k :: L, h => by
    have ih := ss_split_prefix hi L (fun t ht => h t (List.mem_cons_of_mem _ ht))
    have hk' : (∀ x, k = Klong.time x → x ≤ i - 1) → (k :: L = prefixAt (k :: L) (i - 1) ∨
        ∃ more, k :: L = prefixAt (k :: L) (i - 1) ++ Klong.time i :: more) := by
      intro hk
      have e : prefixAt (k :: L) (i - 1) = k :: prefixAt L (i - 1) := by
        unfold prefixAt
        cases k with
        | time x => simp [hk x rfl]
        | key c y => simp
        | del b => simp
      rw [e]
      rcases ih with e1 | ⟨more, e1⟩
      · exact Or.inl (by rw [← e1])
      · exact Or.inr ⟨more, by rw [List.cons_append, ← e1]⟩
    cases k with
    | time x =>
      by_cases hx : x ≤ i - 1
      · exact hk' (fun x' e => by cases e; exact hx)
      · have h1 : @LE.le Nat _ x i := h x List.mem_cons_self
        have h2 : ¬ @LE.le Nat _ x (i - 1) := hx
        have hxi : @Eq Nat x i := by omega
        subst hxi
        right
        refine ⟨L, ?_⟩
        unfold prefixAt
        simp [hx]
    | key c y => exact hk' (fun x e => by cases e)
    | del b => exact hk' (fun x e => by cases e)

/-- The frame of a node from that of the node with key klongs added. -/
theorem ss_ext_of_addAll {n : MNode} {i : Time} {ins : List (Nat × NodeId)} {ks0 : List Klong}
    (h0 : ∀ t, Klong.time t ∈ ks0 → t < i) (hf : ∃ t0 rest, ks0 = Klong.time t0 :: rest)
    (ht : TimesLe n i)
    (h : ksOf (addAll i n ins) = ks0 ∨
      ∃ more, ksOf (addAll i n ins) = ks0 ++ Klong.time i :: more) :
    ksOf (n.toPrev (i - 1)) = ks0 ∧
      (ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more) := by
  obtain ⟨t0, rest, hks0⟩ := hf
  have hi : 0 < i := by
    have h2 : @LT.lt Nat _ t0 i := h0 t0 (by rw [hks0]; exact List.mem_cons_self)
    omega
  have h1 := toPrev_ext h0 ⟨t0, rest, hks0⟩ h
  rw [ksOf_toPrev, ss_prefix_addAll hi ins] at h1
  rw [ksOf_toPrev]
  refine ⟨h1, ?_⟩
  rcases ss_split_prefix hi (ksOf n) ht with e | ⟨more, e⟩
  · rw [h1] at e
    exact Or.inl e
  · rw [h1] at e
    exact Or.inr ⟨more, e⟩

/-! ## 4. The books, the frame, BalancedOK and the top over the steps -/

/-- What the steps of a split keep: the frame, BalancedOK, the put's books
with nodes without klongs allowed (those in E), and the top. -/
structure SsOk (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (E : NodeId → Prop) (w : MW) : Prop where
  frame : Frame i s (dirtyOf w) (treeOf i s w)
  books : PutBooksE p i base s w
  top : WTopInv i s tp w.top w.newTop
  empty : ∀ y m, w.nodes.lookup y = some m → w.taken.contains y = false → m.ks = [] → E y

theorem SsOk.toBooks {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {E : NodeId → Prop} {w : MW} (hO : SsOk p i base s tp E w) (hE : ∀ y, ¬ E y) :
    PutBooks p i base s w :=
  hO.books.toBooks (fun y m hy ht he => hE y (hO.empty y m hy ht he))

theorem ssOk_newKey {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {E E' : NodeId → Prop} {w : MW} (hb : Books i base s tp) (hO : SsOk p i base s tp E w)
    {g h : Nat} {leaf : Bool} {ks : List MKlong} (hg : g ≤ p.G) (hh : h ≤ p.H)
    (hl : leaf = (h == 0)) (hks : ks = [] ∨ ∃ rest, ks = .time i :: rest)
    (htimes : ∀ t, SIS.Tree.Klong.time t ∈ ks → t ≤ i)
    (hE : ∀ z, (z = w.next ∧ ks = []) ∨ E z → E' z) :
    SsOk p i base s tp E' (w.afterNewKey p g h leaf ks) ∧
      ∀ z, (treeOf i s (w.afterNewKey p g h leaf ks)).obj z =
        if z = w.next then some (.key ⟨p.keyLevel g h, leaf, ks.map kOf⟩)
        else (treeOf i s w).obj z := by
  obtain ⟨-, hs, hn, -, ht, hm⟩ := treeOf_freshE hb hO.books (Nat.le_refl _)
  refine ⟨⟨frame_afterNewKey p g h leaf ks hO.frame hs hn ht hm,
    putBooksE_afterNewKey hb hO.books hg hh hl hks htimes, hO.top, ?_⟩, fun z => ?_⟩
  · intro y m hy hty he
    rcases prim_lookup_afterNewKey hn hy with ⟨rfl, rfl⟩ | ⟨_, hy⟩
    · exact hE _ (Or.inl ⟨rfl, he⟩)
    · exact hE _ (Or.inr (hO.empty y m hy hty he))
  · rw [treeOf_afterNewKey i s p g h leaf ks hs hn ht hm]
    rfl

theorem ssOk_withNode {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {E E' : NodeId → Prop} {w : MW} (hO : SsOk p i base s tp E w) {x : NodeId} {m m' : MNode}
    (hx : w.nodes.lookup x = some m) (ht : w.taken.contains x = false)
    (hleaf : m'.leaf = m.leaf)
    (hfst : m'.ks.head? = m.ks.head? ∨ (m.ks = [] ∧ ∃ rest, m'.ks = .time i :: rest))
    (htimes : ∀ t, SIS.Tree.Klong.time t ∈ m'.ks → t ≤ i)
    (hext : ∀ n0, s.obj x = some (.key n0) →
      ksOf m' = n0.ks ∨ ∃ more, ksOf m' = n0.ks ++ Klong.time i :: more)
    (hne : m'.ks ≠ []) (hE : ∀ z, z ≠ x → E z → E' z) :
    SsOk p i base s tp E' (w.withNode x m') ∧
      ∀ z, (treeOf i s (w.withNode x m')).obj z =
        if z = x then some (.key ⟨wLevel s w x, m'.leaf, ksOf m'⟩) else (treeOf i s w).obj z := by
  refine ⟨⟨frame_withNode hO.frame hx ht hleaf hext,
    putBooksE_withNode hO.books hx ht hleaf hfst htimes, hO.top, ?_⟩, fun z => ?_⟩
  · intro y m0 hy hty he
    rcases prim_lookup_withNode hy with ⟨rfl, rfl⟩ | ⟨hyx, hy⟩
    · exact absurd he hne
    · exact hE y hyx (hO.empty y m0 hy hty he)
  · rw [treeOf_withNode i s m' ht]
    rfl

theorem ss_wLevel_newKey {s : Tree} {w : MW} (p : MParams) (g h : Nat) (leaf : Bool)
    (ks : List MKlong) (hs : s.obj w.next = none) (hm : ∀ m ∈ w.made, m.id ≠ w.next) :
    wLevel s (w.afterNewKey p g h leaf ks) w.next = p.keyLevel g h := by
  have hf : w.made.find? (fun m => m.id == w.next) = none := by
    rw [List.find?_eq_none]
    intro m hm'
    simpa using hm m hm'
  simp [wLevel, hs, MW.afterNewKey, List.find?_append, hf]

/-! ## 5. The state before the step -/

/-- The state before the step keeps what the steps keep, and its map is that
of the state with the klongs added (the "if" state), but at x. -/
theorem ss_start {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPre p i base s tp w depth x n ins C)
    (htx : w.taken.contains x = false) :
    SsOk p i base s tp (fun _ => False) w ∧
      (treeOf i s (w.withNode x (addAll i n ins))).obj x =
        some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) ∧
      ∀ z, z ≠ x → (treeOf i s (w.withNode x (addAll i n ins))).obj z = (treeOf i s w).obj z := by
  have hI := h.hyp
  have hA : treeOf i s (w.withNode x (addAll i n ins)) = (treeOf i s w).set x
      (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [treeOf_withNode i s _ htx, addAll_leaf]
  have hAx : (treeOf i s (w.withNode x (addAll i n ins))).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf (addAll i n ins)⟩) := by
    rw [hA]; simp [Tree.set]
  have hAz : ∀ z, z ≠ x → (treeOf i s (w.withNode x (addAll i n ins))).obj z =
      (treeOf i s w).obj z := by
    intro z hz; rw [hA]; simp [Tree.set, hz]
  have hW : treeOf i s w = (treeOf i s (w.withNode x (addAll i n ins))).set x
      (.key ⟨wLevel s w x, n.leaf, ksOf n⟩) := by
    apply prim_tree_ext
    · intro z
      by_cases hz : z = x
      · subst hz
        rw [treeOf_obj_overlay i s h.look htx]
        simp [Tree.set, ksOf]
      · simp only [Tree.set, hz, ite_false]
        rw [hAz z hz]
    · rfl
  refine ⟨⟨?_, h.books.toE, hI.top, ?_⟩, hAx, hAz⟩
  · rw [hW]
    have hD := dirtyOf_withNode (n' := addAll i n ins) h.look
    refine hI.frame.set (fun y hy => by rw [hD] at hy; exact hy) (mem_dirtyOf_of_lookup h.look)
      (fun o0 ho0 => ?_)
    obtain ⟨o', ho', he, -⟩ := hI.frame.1 x o0 ho0
    rw [hAx] at ho'
    cases ho'
    cases o0 with
    | val v => exact absurd he (by simp [Ext])
    | key n0 =>
      obtain ⟨he1, he2, he3⟩ := he
      refine ⟨he1, he2, (ss_ext_of_addAll (prim_timesBefore (hb.times x n0 ho0))
        (hb.first x n0 ho0) (ss_timesLe (h.books.times x n h.look)) he3).2⟩
  · intro y m hy hty he
    obtain ⟨t, rest, hr⟩ := h.books.timeFirst y m hy hty
    rw [hr] at he
    cases he

/-! ## 6. The halves -/

/-- The halves of the full node's last version, with the klongs set, as the
contract sees them. -/
theorem ss_halves {p : MParams} {i : Time} {n : MNode} {ins : List (Nat × NodeId)}
    (hp : ParamsOK p) (hwf : klongsWf (ksOf n) = true) (hsize : n.size ≤ p.M)
    (hfirst : ∃ t rest, n.ks = .time t :: rest)
    (hlen : ins.length = 1 ∨ ins.length = 2)
    (htwo : ∀ a y1 b y2, ins = [(a, y1), (b, y2)] → a < b ∧ (∃ y, (a, y) ∈ live (ksOf n)) ∧
      ∀ c' y', (c', y') ∈ live (ksOf n) → a < c' → b < c')
    (hcase : p.splitAbove < (n.lastVersion i).size)
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc)) :
    ∃ L1 y0 rest, live (ksOf (addAll i n ins)) = L1 ++ (sc, y0) :: rest ∧ L1 ≠ [] ∧
      f.leaf = n.leaf ∧ s2.leaf = n.leaf ∧
      live (ksOf f) = L1 ∧ live (ksOf s2) = (if n.leaf then sc else 0, y0) :: rest ∧
      klongsWf (ksOf f) = true ∧ klongsWf (ksOf s2) = true ∧
      (∃ rest1, f.ks = .time i :: rest1) ∧ (∃ rest2, s2.ks = .time i :: rest2) ∧
      (∀ t, SIS.Tree.Klong.time t ∈ f.ks → t ≤ i) ∧
      (∀ t, SIS.Tree.Klong.time t ∈ s2.ks → t ≤ i) ∧
      f.size ≤ p.M ∧ s2.size ≤ p.M ∧
      (∀ c y, SIS.Tree.Klong.key c y ∈ f.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) ∧
      (∀ c y, SIS.Tree.Klong.key c y ∈ s2.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) := by
  have hs := live_sorted (ksOf n)
  have hl := lastVersion_ks (n := n) i
  have hlen' : (live (ksOf n)).length + 1 = (n.lastVersion i).size := by
    rw [← ksOf_length, hl, List.length_cons, List.length_map]
  have hle : (live (ksOf n)).length + 1 ≤ n.size := by
    rw [← ksOf_length]
    obtain ⟨t, rest, hr⟩ := hfirst
    exact live_length_le ⟨t, rest.map kOf, by simp [ksOf, hr, kOf]⟩
  have h2 : 2 ≤ (live (ksOf n)).length := by
    have := hp.splitLo
    omega
  obtain ⟨⟨sc0, yy⟩, hget⟩ : ∃ e, (live (ksOf n))[(live (ksOf n)).length / 2]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hsc0 : (sc0, yy) ∈ live (ksOf n) := List.mem_of_getElem? hget
  have hins : (∀ cy ∈ ins, cy.1 < sc0) ∨ (∀ cy ∈ ins, sc0 ≤ cy.1) := by
    rcases hlen with h1 | h1
    · obtain ⟨⟨a, y1⟩, rfl⟩ : ∃ cy, ins = [cy] := List.length_eq_one_iff.mp h1
      by_cases ha : a < sc0
      · exact Or.inl (by simpa using ha)
      · exact Or.inr (by simpa using Nat.le_of_not_lt ha)
    · obtain ⟨⟨a, y1⟩, ⟨b, y2⟩, rfl⟩ : ∃ c1 c2, ins = [c1, c2] := List.length_eq_two.mp h1
      obtain ⟨hab, -, hlt⟩ := htwo a y1 b y2 rfl
      by_cases ha : sc0 ≤ a
      · exact Or.inr (by simp; omega)
      · have := hlt sc0 yy hsc0 (by omega)
        exact Or.inl (by simp; omega)
  obtain ⟨hc, hfl, hsl, L1, y0, rest, hfold, hL1, -, -, hlf, hls, hwff, hwfs, hf1, hs1, htf, hts,
    hszf, hszs, hkf, hks⟩ := halves_spec n.leaf i hs hl h2 ⟨yy, hget⟩ ins hins hH
  subst hc
  have hlenins : ins.length ≤ 2 := by omega
  refine ⟨L1, y0, rest, by rw [addAll_live hwf, hfold], hL1, hfl, hsl, hlf, hls, hwff, hwfs, hf1,
    hs1, fun t ht => Nat.le_of_eq (htf t (ss_time_ksOf ht)),
    fun t ht => Nat.le_of_eq (hts t (ss_time_ksOf ht)), ?_, ?_, ?_, ?_⟩
  · have := hp.size
    omega
  · have := hp.size
    omega
  · intro c y hy
    rcases hkf c y (ss_key_ksOf hy) with hy | hy
    · obtain ⟨⟨c', y'⟩, hm, e⟩ := List.mem_map.mp hy
      simp only at e
      subst e
      exact ⟨c', (addAll_key_mem ins n).mpr (Or.inl (ss_live_mem hm))⟩
    · obtain ⟨⟨c', y'⟩, hm, e⟩ := List.mem_map.mp hy
      simp only at e
      subst e
      exact ⟨c', (addAll_key_mem ins n).mpr (Or.inr hm)⟩
  · intro c y hy
    rcases hks c y (ss_key_ksOf hy) with hy | hy
    · obtain ⟨⟨c', y'⟩, hm, e⟩ := List.mem_map.mp hy
      simp only at e
      subst e
      exact ⟨c', (addAll_key_mem ins n).mpr (Or.inl (ss_live_mem hm))⟩
    · obtain ⟨⟨c', y'⟩, hm, e⟩ := List.mem_map.mp hy
      simp only at e
      subst e
      exact ⟨c', (addAll_key_mem ins n).mpr (Or.inr hm)⟩

/-! ## 7. The key access path above x -/

/-- Above x the path is in the "if" state's map A a chain of inner nodes from
the space root, each one level above the next; so x is not on it above its
depth, and its parent q is reached in A, with a live klong (k1, x). -/
theorem ss_path {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPre p i base s tp w (d + 1) x n ins C)
    {c0 : Option Nat} (hon : w.path[d + 1]? = some (c0, x)) (htx : w.taken.contains x = false) :
    ∃ k1 cq q nq, w.path[d]? = some (cq, q) ∧ w.path[d + 1]? = some (some k1, x) ∧
      w.nodes.lookup q = some nq ∧ w.taken.contains q = false ∧ q ≠ x ∧ nq.leaf = false ∧
      (k1, x) ∈ live (ksOf nq) ∧
      q ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
        ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey ∧
      wLevel s w x + 1 = wLevel s w q ∧
      (∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x) := by
  obtain ⟨-, hAx, hAz⟩ := ss_start hb h htx
  have hI := h.hyp
  have hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x := by
    intro e c u he hu hux
    rw [hux] at hu
    exact h.nodup e (d + 1) c c0 x (by omega) le_rfl hu hon
  -- the nodes on the path are reached in A
  have hreach : ∀ e, e ≤ d + 1 → ∀ c u, w.path[e]? = some (c, u) →
      u ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
        ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey := by
    intro e
    induction e with
    | zero =>
      intro _ c u hu
      rw [h.path.root] at hu
      cases hu
      exact tc_self _ _ _
    | succ e ih =>
      intro he c u hu
      obtain ⟨c0', u', c', y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
      rw [h2] at hu
      cases hu
      have hq := ih (by omega) _ _ h1
      have hux := hnx e c0' u' (by omega) h1
      rw [← hAz u' hux] at h3
      have hz := tc_kid h3 h4 (tc_self _ nu.level u)
      exact hI.sound.good.tr_closed hq (g := nu.level + 1) hz
  obtain ⟨c0', q, k1, y, nq', h1, h2, h3, h4⟩ := h.path.links d (by omega)
  rw [hon] at h2
  cases h2
  obtain ⟨_, u2, nq, h5, h6, h7⟩ := h.path.nodes d (by omega)
  rw [h1] at h5
  cases h5
  rw [treeOf_obj_overlay i s h6 h7] at h3
  cases h3
  have hqx := hnx d c0' q le_rfl h1
  have hinner := h.inner d c0' q nq (by omega) h1 h6
  have hqr := hreach d (by omega) _ _ h1
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s h6 h7]
  have hqR : q ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
    rw [reach_of_root hI.root]; exact hqr
  obtain ⟨-, -, hb3⟩ := hI.balanced q hqR _ hAq
  obtain ⟨m', hm1, hm2⟩ := hb3 hinner k1 x h4
  rw [hAx] at hm1
  cases hm1
  exact ⟨k1, c0', q, nq, h1, hon, h6, h7, hqx, hinner, h4, hqr, hm2, hnx⟩

/-! ## 8. Helpers for the cases -/

theorem SsOk.congr {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {E : NodeId → Prop} {w w' : MW} (hO : SsOk p i base s tp E w)
    (h1 : w'.nodes = w.nodes) (h2 : w'.vals = w.vals) (h3 : w'.taken = w.taken)
    (h4 : w'.made = w.made) (h5 : w'.top = w.top) (h6 : w'.newTop = w.newTop)
    (h7 : w'.gh = w.gh) (h8 : w'.next = w.next) (h9 : w'.outside = w.outside) :
    SsOk p i base s tp E w' := by
  cases w; cases w'
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := hO.books
  exact ⟨hO.frame, ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩, hO.top, hO.empty⟩

theorem ss_nodeOk_names {b : Nat} {T : Tree} {m : KNode} (h : nodeOk ⟨b⟩ T m = true) {c : Nat}
    {y : NodeId} (hm : Klong.key c y ∈ m.ks) : (T.obj y).isSome = true := by
  simp only [nodeOk, Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 _ hm

theorem ss_nodeIs {B : Tree} {u : NodeId} {lev : Nat} {m : MNode} {L : List (Nat × NodeId)}
    {M : Nat} (hu : B.obj u = some (.key ⟨lev, m.leaf, ksOf m⟩)) (hlive : live (ksOf m) = L)
    (hwf : klongsWf (ksOf m) = true) (hsz : m.size ≤ M)
    (hnames : ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks → (B.obj y).isSome = true) :
    NodeIs B u lev m.leaf L M := by
  refine ⟨_, hu, rfl, rfl, hlive, ?_⟩
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨by rw [ksOf_length]; exact hsz, hwf⟩, ?_⟩
  intro k hk
  obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hk
  cases k0 with
  | time t => rfl
  | key c y => exact hnames c y hk0
  | del b => rfl

theorem ss_nodeIs_root {B : Tree} {r a b : NodeId} {lev : Nat} {sc : Nat} {M : Nat} {i : Time}
    (hsc : 0 < sc) (hM : 3 ≤ M)
    (hr : B.obj r = some (.key ⟨lev, false,
      ([.time i, .key 0 a, .key sc b] : List MKlong).map kOf⟩))
    (ha : (B.obj a).isSome = true) (hb : (B.obj b).isSome = true) :
    NodeIs B r lev false [(0, a), (sc, b)] M := by
  have e : ([.time i, .key 0 a, .key sc b] : List MKlong).map kOf =
      .time i :: [(0, a), (sc, b)].map (fun cy => Klong.key cy.1 cy.2) := rfl
  rw [e] at hr
  refine ⟨_, hr, rfl, rfl, live_version (by simp [CvLt, hsc]) i, ?_⟩
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨by simp; omega, klongsWf_version i _⟩, ?_⟩
  intro k hk
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl
  · rfl
  · exact ha
  · exact hb

/-- The live klongs of the halves are live klongs of x with the klongs
added. -/
theorem ss_halves_live {i : Time} {n : MNode} {ins : List (Nat × NodeId)} {f s2 : MNode}
    {sc : Nat} {L1 rest : List (Nat × NodeId)} {y0 : NodeId}
    (hsplit : live (ksOf (addAll i n ins)) = L1 ++ (sc, y0) :: rest) (hlf : live (ksOf f) = L1)
    (hls : live (ksOf s2) = (if n.leaf then sc else 0, y0) :: rest) :
    (∀ c y, (c, y) ∈ live (ksOf f) → ∃ c', (c', y) ∈ live (ksOf (addAll i n ins))) ∧
    (∀ c y, (c, y) ∈ live (ksOf s2) → ∃ c', (c', y) ∈ live (ksOf (addAll i n ins))) := by
  refine ⟨fun c y hy => ⟨c, by rw [hsplit]; rw [hlf] at hy; exact List.mem_append_left _ hy⟩,
    fun c y hy => ?_⟩
  rw [hls] at hy
  rcases List.mem_cons.mp hy with e | e
  · simp only [Prod.mk.injEq] at e
    rw [e.2]
    exact ⟨sc, by rw [hsplit]; simp⟩
  · exact ⟨c, by rw [hsplit]; simp [e]⟩

/-- A node that a key klong of x with the klongs added names exists in the
"if" state's map, if x is reached there. -/
theorem ss_named_some {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {depth : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hb : Books i base s tp) (h : CasPre p i base s tp w depth x n ins C)
    (htx : w.taken.contains x = false)
    (hx : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey)
    {y : NodeId} (hy : ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) :
    ((treeOf i s (w.withNode x (addAll i n ins))).obj y).isSome = true := by
  obtain ⟨-, hAx, -⟩ := ss_start hb h htx
  obtain ⟨c', hc'⟩ := hy
  exact ss_nodeOk_names (h.hyp.sound.nodes x hx _ hAx) hc'

/-- The state after `newSuperRoot` has the same nodes and next id or more. -/
theorem ss_afterSuperRoot_next (w : MW) (p : MParams) (i : Time) (y : NodeId) :
    w.next ≤ (MW.afterSuperRoot w p i y).next := by
  unfold MW.afterSuperRoot
  split
  · exact Nat.le_refl _
  · exact Nat.le_add_right _ _

/-- `PInv` after `newSuperRoot r` from a state that keeps what the steps keep,
with the map's tree sound from r. -/
theorem ss_pinv_superRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {E : NodeId → Prop} {w : MW} (hb : Books i base s tp)
    (hO : SsOk p i base s tp E w) (hE : ∀ y, ¬ E y) (r : NodeId)
    (hS : Sound p.M none (treeOf i s (MW.afterSuperRoot w p i r)) r C)
    (hB : Balanced p (treeOf i s (MW.afterSuperRoot w p i r))) :
    PInv p i base s tp none C (MW.afterSuperRoot w p i r) ∧
      (treeOf i s (MW.afterSuperRoot w p i r)).obj = (treeOf i s w).obj ∧
      (MW.afterSuperRoot w p i r).top.rootKey = r := by
  obtain ⟨hobjF, hrootF, hdirtyF⟩ := treeOf_afterSuperRoot i s p r hO.books.ids.1
  have hrk := (afterSuperRoot_fields w p i r).1
  refine ⟨⟨by rw [hrk]; exact hrootF, by rw [hrk]; exact hS, ?_,
    topInv_afterSuperRoot r hO.top hb hO.books.ids.2.2.2.1, hB,
    putBooks_afterSuperRoot r (hO.toBooks hE)⟩, hobjF, hrk⟩
  · obtain ⟨f1, f2, -⟩ := hO.frame
    refine ⟨fun y o hy => ?_, fun y m hy hsy => ?_,
      ⟨[(i, r)], treeOf_afterSuperRoot_roots i s p r w, by simp⟩⟩
    · obtain ⟨o', h1, h2, h3⟩ := f1 y o hy
      exact ⟨o', by rw [hobjF]; exact h1, h2, by rw [hdirtyF]; exact h3⟩
    · rw [hdirtyF]
      rw [hobjF] at hy
      exact f2 y m hy hsy

/-- BalancedOK of the map B after a tree rule from the map A: B reaches what
A reaches and the nodes of N; off N the two agree; key nodes keep their
levels; the nodes of N meet the rule in B. -/
theorem ss_bal_of {p : MParams} {A B : Tree} {N : List NodeId} {r r' : NodeId}
    (hA : Balanced p A) (hrA : A.root = some r) (hrB : B.root = some r')
    (hRB : ∀ z ∈ reachAt B (B.fuel r') r', z ∈ reachAt A (A.fuel r) r ∨ z ∈ N)
    (hold : ∀ z, z ∉ N → B.obj z = A.obj z)
    (hlev : ∀ y m, A.obj y = some (.key m) → ∃ m', B.obj y = some (.key m') ∧
      m'.level = m.level)
    (hnew : ∀ z ∈ N, z ∈ reachAt B (B.fuel r') r' → ∀ m, B.obj z = some (.key m) →
      0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
      (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks → ∃ m', B.obj y = some (.key m') ∧
        m'.level + 1 = m.level)) : Balanced p B := by
  refine Balanced.of_reach hA (fun z hz => ?_) (fun z _ hz => hold z hz) hlev
    (fun z hz hzR m hm => hnew z hz (by rw [reach_of_root hrB] at hzR; exact hzR) m hm)
  rw [reach_of_root hrB] at hz
  rcases hRB z hz with h1 | h1
  · left
    rw [reach_of_root hrA]
    exact h1
  · exact Or.inr h1

/-- The levels of the key nodes of A in B, from B = A off N and the levels of
the nodes of N. -/
theorem ss_lev_of {A B : Tree} {N : List NodeId} (hold : ∀ z, z ∉ N → B.obj z = A.obj z)
    (hN : ∀ z ∈ N, ∀ m, A.obj z = some (.key m) → ∃ m', B.obj z = some (.key m') ∧
      m'.level = m.level) :
    ∀ y m, A.obj y = some (.key m) → ∃ m', B.obj y = some (.key m') ∧ m'.level = m.level := by
  intro y m hy
  by_cases hyN : y ∈ N
  · exact hN y hyN m hy
  · exact ⟨m, by rw [hold y hyN, hy], rfl⟩

/-- A node of N in B with the level and the kind of a node u reached in A and
live klongs that name what live klongs of u name: it meets the rule. -/
theorem ss_rule_node {p : MParams} {A B : Tree} {u : NodeId} {nu m : KNode}
    (hA : Balanced p A) (huR : u ∈ reach A) (hAu : A.obj u = some (.key nu))
    (hlev : ∀ y m, A.obj y = some (.key m) → ∃ m', B.obj y = some (.key m') ∧
      m'.level = m.level)
    (hml : m.leaf = nu.leaf) (hmlev : m.level = nu.level)
    (hlive : ∀ c y, (c, y) ∈ live m.ks → (∃ c', (c', y) ∈ live nu.ks) ∨
      ∃ m', B.obj y = some (.key m') ∧ m'.level + 1 = m.level) :
    0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
      (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks → ∃ m', B.obj y = some (.key m') ∧
        m'.level + 1 = m.level) := by
  obtain ⟨h0, h1, h2⟩ := hA u huR nu hAu
  refine ⟨by rw [hmlev]; exact h0, by rw [hml, hmlev]; exact h1, fun hl c y hy => ?_⟩
  rcases hlive c y hy with ⟨c', hc'⟩ | hB
  · obtain ⟨m1, hm1, hm2⟩ := h2 (by rw [← hml]; exact hl) c' y hc'
    obtain ⟨m', hm3, hm4⟩ := hlev y m1 hm1
    exact ⟨m', hm3, by rw [hm4, hmlev]; exact hm2⟩
  · exact hB

/-- A new root over two nodes on the level below it meets the rule. -/
theorem ss_rule_root {p : MParams} {B : Tree} {a b : NodeId} {sc lev : Nat} {i : Time}
    (hpos : 0 < lev) (hh : p.heightOf lev ≠ 0)
    (ha : ∃ m', B.obj a = some (.key m') ∧ m'.level + 1 = lev)
    (hb : ∃ m', B.obj b = some (.key m') ∧ m'.level + 1 = lev) :
    0 < lev ∧ false = (p.heightOf lev == 0) ∧
      (false = false → ∀ c y,
        (c, y) ∈ live (([.time i, .key 0 a, .key sc b] : List MKlong).map kOf) →
        ∃ m', B.obj y = some (.key m') ∧ m'.level + 1 = lev) := by
  refine ⟨hpos, by simp [hh], fun _ c y hy => ?_⟩
  have := ss_live_mem hy
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at this
  rcases this with e | e | e
  · simp [kOf] at e
  · simp only [kOf, Klong.key.injEq] at e
    rw [e.2]; exact ha
  · simp only [kOf, Klong.key.injEq] at e
    rw [e.2]; exact hb

/-! ## 9. At the space root, x made by the transaction -/

theorem ss_ne_add {a b : Nat} (h : 0 < b) : a ≠ a + b := by omega

theorem ss_ne_of_lt_add {a b c : Nat} (h : a < b) : a ≠ b + c := by omega

theorem ss_le_add {a b c : Nat} (h : b = a + c) : a ≤ b := by omega

theorem ss_ite_neg {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem ss_ite_pos {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ss_root_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = (ssNote w4 "split.space3.inplace").afterNewKey p g (hh + 1) false
      [.time i, .key 0 x, .key sc w.next])
    (e6 : w6 = ssMF w5 (w.next + 2) (w5.madeFor.lookup x)) :
    CasPost p i base s tp w 0 x n ins C () (MW.afterSuperRoot w6 p i (w.next + 2)) := by
  intro hout
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  have hxr : x = w.top.rootKey := by
    have := h.path.root
    rw [hon] at this
    cases this
    rfl
  obtain ⟨hO, hAx, hAz⟩ := ss_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hA0 := (treeOf_fresh hb hI.books (Nat.le_refl w.next)).1
  have hA2 := (treeOf_fresh hb hI.books (Nat.le_add_right w.next 2)).1
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey := by
    rw [← hxr]; exact tc_self _ _ _
  -- the bound of the new root
  have hout6 : w6.outside = [] := by
    rw [← hout]
    exact ((afterSuperRoot_fields w6 p i (w.next + 2)).2.2.2.2.2.2.2.2).symm
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e6, e5] at hout6
      simp [ssMF, MW.afterNewKey, hc] at hout6
    · exact hc
  -- the states
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hlk1 : ∀ y, y ≠ w.next → w1.nodes.lookup y = w.nodes.lookup y := by
    intro y hy
    rw [e1]
    exact prim_lookup_append_ne _ _ hy
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hwl1 : ∀ y, y ≠ w.next → wLevel s w1 y = wLevel s w y := by
    intro y hy
    rw [e1]
    exact prim_wLevel_afterNewKey hy
  have hwl1n : wLevel s w1 w.next = p.keyLevel g hh := by
    rw [e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl)
      (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hO2 : SsOk p i base s tp (fun z => z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.books.timeFirst x n hlook htx
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO3 : SsOk p i base s tp (fun z => z = w.next) w3 ∧
      ∀ z, (treeOf i s w3).obj z = if z = x then some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩)
        else (treeOf i s w2).obj z := by
    have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
    rw [e3, ← hwx]
    refine ssOk_withNode hO2 (by rw [hN2, hlk1 x (Nat.ne_of_lt hxlt)]; exact hlook)
      (by rw [hk2]; exact htx) hfl
      (Or.inl hfst) htf (fun n0 hn0 => by rw [hsx] at hn0; cases hn0)
      (by rw [hf1]; simp) (fun z _ hz => hz)
  have hN3 : ∀ y, y ≠ x → w3.nodes.lookup y = w2.nodes.lookup y := by
    intro y hy
    rw [e3]
    exact lookup_upsert_ne _ _ hy
  have hwl3 : wLevel s w3 = wLevel s w1 := by rw [e3, ← hwl2]; rfl
  have hO4 : SsOk p i base s tp (fun _ => False) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz hz')
  have hn4 : w4.next = w.next + 2 := by rw [e4, e3, e2]; exact hn1
  have hO5 : SsOk p i base s tp (fun _ => False) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩)
        else (treeOf i s w4).obj z := by
    rw [e5, ← hn4]
    refine ssOk_newKey hb (hO4.1.congr (w' := ssNote w4 "split.space3.inplace") rfl rfl rfl rfl
      rfl rfl rfl rfl rfl) hgG hH1 (by simp)
      (Or.inr ⟨_, rfl⟩) (by simp) (by simp)
  have hO6 : SsOk p i base s tp (fun _ => False) w6 := by
    rw [e6]
    exact hO5.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT6 : treeOf i s w6 = treeOf i s w5 := by rw [e6]; rfl
  -- the map after the step
  have hobjF := (treeOf_afterSuperRoot i s p (w.next + 2) hO6.books.ids.1).1
  have hBr : (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj (w.next + 2) =
      some (.key ⟨p.keyLevel g (hh + 1), false,
        ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩) := by
    rw [hobjF, hT6, hO5.2, ss_ite_pos rfl]
  have hBs : (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj w.next =
      some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) := by
    rw [hobjF, hT6, hO5.2, ss_ite_neg (ss_ne_add (by decide)), hO4.2, ss_ite_pos rfl]
  have hBx : (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj x =
      some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [hobjF, hT6, hO5.2, ss_ite_neg (ss_ne_of_lt_add hxlt), hO4.2, ss_ite_neg (Nat.ne_of_lt hxlt),
      hO3.2,
      ss_ite_pos rfl]
  have hBo : ∀ z, z ≠ w.next + 2 → z ≠ w.next → z ≠ x →
      (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj z = (treeOf i s w).obj z := by
    intro z h1 h2 h3
    rw [hobjF, hT6, hO5.2, ss_ite_neg h1, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h3, hT2, hO1.2,
      ss_ite_neg h2]
  have hBA : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj z).isSome = true := by
    intro z hz
    by_cases h1 : z = w.next + 2
    · rw [h1, hBr]; rfl
    by_cases h2 : z = w.next
    · rw [h2, hBs]; rfl
    by_cases h3 : z = x
    · rw [h3, hBx]; rfl
    rw [hBo z h1 h2 h3, ← hAz z h3]
    exact hz
  have hS : Sound p.M (some x) (treeOf i s (w.withNode x (addAll i n ins))) w.top.rootKey C :=
    hI.sound
  rw [← hxr] at hS
  have hsc0 : 0 < sc := Good.tr_split_lo hS.good hAx hsplit hL1
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (ss_named_some hb h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) x (wLevel s w x) n.leaf
      L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs hBx hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) w.next (wLevel s w x)
      n.leaf (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl, hlev]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) (w.next + 2)
      (wLevel s w x + 1) false [(0, x), (sc, w.next)] p.M := by
    rw [hlev, ← keyLevel_succ]
    exact ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBx]; rfl)
      (by rw [hBs]; rfl)
  obtain ⟨hSB, -, hRB⟩ := Sound.spaceSplitRoot hS hAx hsplit hL1 (Or.inl rfl) hA0
    (Nat.ne_of_lt hxlt) hA2 ⟨(ss_ne_of_lt_add hxlt).symm, (ss_ne_add (by decide)).symm⟩ hNf hNs
    hNr (by rw [hBx]; rfl)
    (fun z h1 _ h3 h4 => by rw [hBo z h4 h3 h1, hAz z h1])
  -- BalancedOK of the map after the step
  have hxR : x ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
    rw [reach_of_root hI.root]
    show x ∈ reachAt _ ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey)
      w.top.rootKey
    rw [← hxr]; exact tc_self _ _ _
  have hold : ∀ z, z ∉ [x, w.next, w.next + 2] →
      (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hBo z hz.2.2 hz.2.1 hz.1, hAz z hz.1]
  have hlevB := ss_lev_of hold (by
    intro z hz m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · rw [hAx] at hm; cases hm; exact ⟨_, hBx, rfl⟩
    · rw [hA0] at hm; cases hm
    · rw [hA2] at hm; cases hm)
  have hHL := ss_halves_live hsplit hlf hls
  have hBal : Balanced p (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) := by
    refine ss_bal_of hI.balanced hI.root
      (treeOf_afterSuperRoot i s p (w.next + 2) hO6.books.ids.1).2.1 (fun z hz => ?_) hold hlevB
      (fun z hz _ m hm => ?_)
    · rcases hRB z hz with h1 | h1 | h1 | h1
      · left
        have hW0r : (w.withNode x (addAll i n ins)).top.rootKey = x := hxr.symm
        rw [hW0r]; exact h1
      · right; simp [h1]
      · right; simp [h1]
      · right; simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · rw [hBx] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx hlevB hfl rfl
          (fun c y hy => Or.inl (hHL.1 c y hy))
      · rw [hBs] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx hlevB hsl hlev.symm
          (fun c y hy => Or.inl (hHL.2 c y hy))
      · rw [hBr] at hm; cases hm
        refine ss_rule_root (keyLevel_pos p g (hh + 1)) (by rw [heightOf_keyLevel p hH1]; simp)
          ⟨_, hBx, by rw [hlev, keyLevel_succ]⟩ ⟨_, hBs, by rw [keyLevel_succ]⟩
  obtain ⟨hPI, -, hrkF⟩ := ss_pinv_superRoot hb hO6 (fun _ h => h) (w.next + 2) hSB hBal
  refine ⟨hPI, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [(afterSuperRoot_fields w6 p i (w.next + 2)).2.2.2.2.2.2.2.1, e6, e5, e4, e3, e2, e1]
    rfl
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot 0 c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [(afterSuperRoot_fields w6 p i (w.next + 2)).2.2.1,
      show w6.nodes = w5.nodes by rw [e6]; rfl]
    have e5n : w5.nodes = w4.nodes ++ [(w4.next, ⟨false, [.time i, .key 0 x, .key sc w.next]⟩)] :=
      by rw [e5]; rfl
    rw [e5n, prim_lookup_append_ne _ _ (by rw [hn4]; exact ss_ne_of_lt_add hylt), e4, MW.withNode,
      lookup_upsert_ne _ _ (Nat.ne_of_lt hylt), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hylt)]
    exact hy
  · have h6 : w6.next = w.next + 4 := by rw [e6, e5]; show w4.next + 2 = _; rw [hn4]
    exact Nat.le_trans (ss_le_add h6) (ss_afterSuperRoot_next w6 p i (w.next + 2))
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrkF] at hz
    have hW0r : (w.withNode x (addAll i n ins)).top.rootKey = x := hxr.symm
    rw [hW0r]
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]
      exact Or.inl (tc_self _ _ _)
    · rw [h1]
      exact Or.inr (Nat.le_refl _)
    · rw [h1]
      exact Or.inr (Nat.le_add_right _ _)

theorem ss_root_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up 0 x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w 0 x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_zero _ _) ?_
  dsimp only
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (newSuperRoot_eq v _ h.hyp.top) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine (wp_pure _ _ _ _).mpr ?_
  exact ss_root_inPlace_post hp hb h hcase hin hgh hH rfl rfl rfl rfl rfl rfl

/-! ## 10. At the space root, x from before the transaction -/

/-- `newSuperRoot r` keeps what the steps keep, once every node kept has
klongs. -/
theorem ssOk_superRoot {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    (hb : Books i base s tp) (hO : SsOk p i base s tp (fun _ => False) w) (r : NodeId) :
    SsOk p i base s tp (fun _ => False) (MW.afterSuperRoot w p i r) ∧
      (treeOf i s (MW.afterSuperRoot w p i r)).obj = (treeOf i s w).obj ∧
      (treeOf i s (MW.afterSuperRoot w p i r)).root = some r ∧
      (MW.afterSuperRoot w p i r).top.rootKey = r := by
  obtain ⟨hobjF, hrootF, hdirtyF⟩ := treeOf_afterSuperRoot i s p r hO.books.ids.1
  obtain ⟨hrk, -, hnodes, -, htaken, -⟩ := afterSuperRoot_fields w p i r
  refine ⟨⟨?_, (putBooks_afterSuperRoot r (hO.toBooks (fun _ h => h))).toE,
    topInv_afterSuperRoot r hO.top hb hO.books.ids.2.2.2.1, ?_⟩, hobjF, hrootF, hrk⟩
  · obtain ⟨f1, f2, -⟩ := hO.frame
    refine ⟨fun y o hy => ?_, fun y m hy hsy => ?_,
      ⟨[(i, r)], treeOf_afterSuperRoot_roots i s p r w, by simp⟩⟩
    · obtain ⟨o', h1, h2, h3⟩ := f1 y o hy
      exact ⟨o', by rw [hobjF]; exact h1, h2, by rw [hdirtyF]; exact h3⟩
    · rw [hdirtyF]
      rw [hobjF] at hy
      exact f2 y m hy hsy
  · intro y m hy hty he
    rw [hnodes] at hy
    rw [htaken] at hty
    exact hO.empty y m hy hty he

/-- `PInv` of a state that keeps what the steps keep, with every node kept
with klongs and its map sound from its root. -/
theorem ss_pinv {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {w : MW} (hO : SsOk p i base s tp (fun _ => False) w)
    (hr : (treeOf i s w).root = some w.top.rootKey)
    (hS : Sound p.M none (treeOf i s w) w.top.rootKey C) (hB : Balanced p (treeOf i s w)) :
    PInv p i base s tp none C w :=
  ⟨hr, hS, hO.frame, hO.top, hB, hO.toBooks (fun _ h => h)⟩

/-- x cut back to before the transaction: its klongs of s. -/
theorem ss_toPrev {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPre p i base s tp w depth x n ins C)
    (htx : w.taken.contains x = false) {n0 : KNode} (hs : s.obj x = some (.key n0)) :
    ksOf (n.toPrev (i - 1)) = n0.ks := by
  obtain ⟨-, hAx, -⟩ := ss_start hb h htx
  obtain ⟨o', ho', he, -⟩ := h.hyp.frame.1 x _ hs
  rw [hAx] at ho'
  cases ho'
  exact (ss_ext_of_addAll (prim_timesBefore (hb.times x n0 hs)) (hb.first x n0 hs)
    (ss_timesLe (h.books.times x n h.look)) he.2.2).1

theorem ss_mem_toPrev {n : MNode} {t : Time} {k : MKlong} (h : k ∈ (n.toPrev t).ks) : k ∈ n.ks :=
  List.takeWhile_subset _ h

theorem ss_toPrev_head {n : MNode} {t t0 : Time} {rest : List MKlong}
    (h : n.ks = .time t0 :: rest) (ht : t0 ≤ t) :
    ∃ rest', (n.toPrev t).ks = .time t0 :: rest' := by
  show ∃ rest', SIS.Tree.prefixAt n.ks t = _
  unfold SIS.Tree.prefixAt
  rw [h, List.takeWhile_cons]
  simp [ht]

theorem ss_wp_putNode {c : Ctx} {w : MW} {x : NodeId} {m : MNode} {post : Unit → MW → Prop}
    (h : post () (w.withNode x m)) : WP (SIS.Tree.putNode x m) c w post := by
  intro r w' hr
  rw [putNode_eq] at hr
  cases hr
  exact h

theorem ss_lookup_newKey {w : MW} {p : MParams} {g h : Nat} {leaf : Bool} {ks : List MKlong}
    {y : NodeId} (hy : y ≠ w.next) :
    (w.afterNewKey p g h leaf ks).nodes.lookup y = w.nodes.lookup y :=
  prim_lookup_append_ne _ _ hy

theorem ss_lookup_withNode {w : MW} {x y : NodeId} {m : MNode} (hy : y ≠ x) :
    (w.withNode x m).nodes.lookup y = w.nodes.lookup y :=
  lookup_upsert_ne _ _ hy

theorem ss_root_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp)
    (h : CasPre p i base s tp w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 w7 w8 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = (ssNote w3 "split.space3").afterNewKey p g (hh + 1) false [])
    (e5 : w5 = ssMF w4 (w.next + 4) (some x))
    (e6 : w6 = w5.withNode w.next f) (e7 : w7 = w6.withNode (w.next + 2) s2)
    (e8 : w8 = w7.withNode (w.next + 4) ⟨false, [.time i, .key 0 w.next, .key sc (w.next + 2)]⟩) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } (MW.afterSuperRoot w8 p i (w.next + 4))
      (CasPost p i base s tp w 0 x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hn2 : w2.next = w.next + 4 := by rw [e2]; show w1.next + 2 = _; rw [hn1]
  have hn3 : w3.next = w.next + 4 := by rw [e3]; exact hn2
  -- the node lookups through the steps
  have hlk : ∀ y, y ≠ w.next → y ≠ w.next + 2 → y ≠ w.next + 4 →
      w8.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2 h4
    rw [e8, ss_lookup_withNode h4, e7, ss_lookup_withNode h2, e6, ss_lookup_withNode h1,
      show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space3") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  have hlk9 : (MW.afterSuperRoot w8 p i (w.next + 4)).nodes.lookup x = some n := by
    rw [(afterSuperRoot_fields w8 p i _).2.2.1, hlk x (Nat.ne_of_lt hxlt)
      (ss_ne_of_lt_add hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  refine ss_wp_step (getNode_hit _ hlk9) ?_
  refine ss_wp_putNode ?_
  intro hout
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  have hxr : x = w.top.rootKey := by
    have := h.path.root
    rw [hon] at this
    cases this
    rfl
  obtain ⟨hO, hAx, hAz⟩ := ss_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.books.timeFirst x n hlook htx
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hA0 := (treeOf_fresh hb hI.books (Nat.le_refl w.next)).1
  have hA2 := (treeOf_fresh hb hI.books (Nat.le_add_right w.next 2)).1
  have hA4 := (treeOf_fresh hb hI.books (Nat.le_add_right w.next 4)).1
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey := by
    rw [← hxr]; exact tc_self _ _ _
  -- the bound of the new root
  have hout4 : w4.outside = [] := by
    rw [← hout]
    show w4.outside = (MW.afterSuperRoot w8 p i (w.next + 4)).outside
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.2.2.2.2, e8, e7, e6, e5]
    rfl
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e4] at hout4
      simp [MW.afterNewKey, hc] at hout4
    · exact hc
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO3 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w3 := by
    rw [e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT3 : treeOf i s w3 = treeOf i s w2 := by rw [e3]; rfl
  have hfr3 := treeOf_freshE hb hO3.books (Nat.le_refl w3.next)
  rw [hn3] at hfr3
  obtain ⟨-, hs4, hn4', -, ht4, hm4⟩ := hfr3
  have hO4 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false, []⟩) else (treeOf i s w3).obj z := by
    rw [e4, ← hn3]
    exact ssOk_newKey hb (hO3.congr (w' := ssNote w3 "split.space3") rfl rfl rfl rfl rfl rfl rfl rfl
      rfl) hgG hH1 (by simp) (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO5 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hk5 : w5.taken = w.taken := by rw [e5, e4, e3, e2, e1]; rfl
  have hM5 : wLevel s w5 = wLevel s w4 := by rw [e5]; rfl
  have hw4n : ∀ y, y ≠ w.next + 4 → wLevel s w5 y = wLevel s w2 y := by
    intro y hy
    rw [hM5, e4, prim_wLevel_afterNewKey (w := ssNote w3 "split.space3")
      (by show y ≠ w3.next; rw [hn3]; exact hy)]
    rw [e3]
    rfl
  have hwl0 : wLevel s w5 w.next = p.keyLevel g hh := by
    rw [hw4n _ (ss_ne_add (by decide)), e2,
      prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_add (by decide)), e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hwl2 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by
    rw [hw4n _ (by
      have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
      rw [Nat.add_assoc] at this
      exact this), e2, ← hn1]
    exact ss_wLevel_newKey p g hh n.leaf [] (by rw [hn1]; exact hs2) (by rw [hn1]; exact hm2)
  have hwl4 : wLevel s w5 (w.next + 4) = p.keyLevel g (hh + 1) := by
    rw [hM5, e4, ← hn3]
    exact ss_wLevel_newKey (w := ssNote w3 "split.space3") p g (hh + 1) false []
      (by show s.obj w3.next = none; rw [hn3]; exact hs4)
      (by show ∀ m ∈ w3.made, m.id ≠ w3.next; rw [hn3]; exact hm4)
  have hN5 : ∀ y, y ≠ w.next + 4 → y ≠ w.next + 2 → w5.nodes.lookup y = w1.nodes.lookup y := by
    intro y h4 h2
    rw [show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space3") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2)]
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hold5 : ∀ y, y < w.next → (treeOf i s w5).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT5, hO4.2, ss_ite_neg (ss_ne_of_lt_add hy), hT3, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy),
      hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO6 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w5).obj z := by
    rw [e6, ← hwl0]
    refine ssOk_withNode hO5 (m := ⟨n.leaf, []⟩)
      (by rw [hN5 _ (ss_ne_add (by decide)) (ss_ne_add (by decide)), hlk1n])
      (by rw [hk5]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr hz'
      · exact absurd hz' hz
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne40 : w.next + 4 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne42 : w.next + 4 ≠ w.next + 2 := by
    have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
    rw [Nat.add_assoc] at this
    exact this.symm
  have hlk1 : w1.nodes.lookup (w.next + 2) = none := by rw [← hn1]; rw [hn1]; exact hn2'
  have hO7 : SsOk p i base s tp (fun z => z = w.next + 4) w7 ∧
      ∀ z, (treeOf i s w7).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w6).obj z := by
    have hwl6 : wLevel s w6 (w.next + 2) = p.keyLevel g hh := by rw [e6]; exact hwl2
    rw [e7, ← hwl6]
    refine ssOk_withNode hO6.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e6]; show w5.taken.contains _ = false
        rw [hk5, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0')
      (by rw [hs1]; simp) ?_
    · rw [e6, ss_lookup_withNode hne20, show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
        ss_lookup_newKey (w := ssNote w3 "split.space3")
          (by show _ ≠ w3.next; rw [hn3]; exact hne42.symm),
        show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hlk1)
    · intro z hz hz'
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' hz
  have hO8 : SsOk p i base s tp (fun _ => False) w8 ∧
      ∀ z, (treeOf i s w8).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩)
        else (treeOf i s w7).obj z := by
    have hwl7 : wLevel s w7 (w.next + 4) = p.keyLevel g (hh + 1) := by rw [e7, e6]; exact hwl4
    rw [e8, ← hwl7]
    refine ssOk_withNode hO7.1 (m := ⟨false, []⟩) ?_
      (by
        rw [e7, e6]; show w5.taken.contains _ = false
        rw [hk5, show w.taken = w3.taken by rw [e3, e2, e1]; rfl]; exact ht4) rfl
      (Or.inr ⟨rfl, _, rfl⟩) (by simp) (fun n0 hn0' => by rw [hs4] at hn0'; cases hn0')
      (by simp) (fun _ hz h => hz h)
    · rw [e7, ss_lookup_withNode hne42, e6, ss_lookup_withNode hne40,
        show w5.nodes = w4.nodes by rw [e5]; rfl, e4, ← hn3]
      exact prim_lookup_append_self (l := (ssNote w3 "split.space3").nodes) _
        (by show w3.nodes.lookup w3.next = none; rw [hn3]; exact hn4')
  obtain ⟨hO9, hobj9, hroot9, hrk9⟩ := ssOk_superRoot hb hO8.1 (w.next + 4)
  have htx9 : (MW.afterSuperRoot w8 p i (w.next + 4)).taken.contains x = false := by
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.1, e8, e7, e6]
    show w5.taken.contains x = false
    rw [hk5]; exact htx
  have hO10 := ssOk_withNode (E' := fun _ => False) hO9 hlk9 htx9 rfl (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (ss_toPrev hb h htx hn0'))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  -- the map after the step
  have hxn : x ≠ w.next := Nat.ne_of_lt hxlt
  have hxn2 : x ≠ w.next + 2 := ss_ne_of_lt_add hxlt
  have hxn4 : x ≠ w.next + 4 := ss_ne_of_lt_add hxlt
  have hB : ∀ z, z ≠ x → (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj z = (treeOf i s w8).obj z := by
    intro z hz
    rw [hO10.2, ss_ite_neg hz, hobj9]
  have hBr : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj (w.next + 4) = some (.key ⟨p.keyLevel g (hh + 1), false,
        ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩) := by
    rw [hB _ hxn4.symm, hO8.2, ss_ite_pos rfl]
  have hBs : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj (w.next + 2) = some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) := by
    rw [hB _ hxn2.symm, hO8.2, ss_ite_neg hne42.symm, hO7.2, ss_ite_pos rfl]
  have hBf : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj w.next = some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) := by
    rw [hB _ hxn.symm, hO8.2, ss_ite_neg hne40.symm, hO7.2, ss_ite_neg hne20.symm, hO6.2,
      ss_ite_pos rfl]
  have hBx : ((treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj x).isSome = true := by
    rw [hO10.2, ss_ite_pos rfl]; rfl
  have hBo : ∀ z, z ≠ x → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 4 →
      (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1)))).obj z = (treeOf i s w).obj z := by
    intro z h0 h1 h2 h4
    rw [hB z h0, hO8.2, ss_ite_neg h4, hO7.2, ss_ite_neg h2, hO6.2, ss_ite_neg h1, hT5, hO4.2,
      ss_ite_neg h4, hT3, hO2.2, ss_ite_neg h2, hO1.2, ss_ite_neg h1]
  have hBA : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1)))).obj z).isSome = true := by
    intro z hz
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    by_cases h1 : z = w.next
    · rw [h1, hBf]; rfl
    by_cases h2 : z = w.next + 2
    · rw [h2, hBs]; rfl
    by_cases h4 : z = w.next + 4
    · rw [h4, hBr]; rfl
    rw [hBo z h0 h1 h2 h4, ← hAz z h0]
    exact hz
  have hS : Sound p.M (some x) (treeOf i s (w.withNode x (addAll i n ins))) w.top.rootKey C :=
    hI.sound
  rw [← hxr] at hS
  have hsc0 : 0 < sc := Good.tr_split_lo hS.good hAx hsplit hL1
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1)))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (ss_named_some hb h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) w.next (wLevel s w x) n.leaf L1 p.M := by
    rw [← hfl, hlev]
    exact ss_nodeIs hBf hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) (w.next + 2) (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl, hlev]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) (w.next + 4) (wLevel s w x + 1) false
      [(0, w.next), (sc, w.next + 2)] p.M := by
    rw [hlev, ← keyLevel_succ]
    exact ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBf]; rfl)
      (by rw [hBs]; rfl)
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplitRoot hS hAx hsplit hL1 (Or.inr hA0) hA2 hne20.symm hA4
    ⟨hne40, hne42⟩ hNf hNs hNr hBx
    (fun z h0 h1 h2 h4 => by rw [hBo z h0 h1 h2 h4, hAz z h0])
  -- BalancedOK of the map after the step
  have hxR : x ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
    rw [reach_of_root hI.root]
    show x ∈ reachAt _ ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey)
      w.top.rootKey
    rw [← hxr]; exact tc_self _ _ _
  have h8' : w8.next = w.next + 6 := by
    rw [e8, e7, e6, e5, e4]
    show w3.next + 2 = _
    rw [hn3]
  have hwx9 : wLevel s (MW.afterSuperRoot w8 p i (w.next + 4)) x = wLevel s w x := by
    rw [wLevel_afterSuperRoot s p i _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt
      (by rw [h8']; exact Nat.le_add_right _ _))),
      show wLevel s w8 = wLevel s w5 by rw [e8, e7, e6]; rfl, hw4n x hxn4, e2,
      prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact hxn2), e1]
    exact prim_wLevel_afterNewKey hxn
  have hold : ∀ z, z ∉ [x, w.next, w.next + 2, w.next + 4] →
      (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x (n.toPrev (i - 1)))).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    rw [hBo z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2, hAz z hz.1]
  have hlevB := ss_lev_of hold (by
    intro z hz m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · rw [hAx] at hm; cases hm
      exact ⟨_, by rw [hO10.2, ss_ite_pos rfl], hwx9⟩
    · rw [hA0] at hm; cases hm
    · rw [hA2] at hm; cases hm
    · rw [hA4] at hm; cases hm)
  have hHL := ss_halves_live hsplit hlf hls
  have hBal : Balanced p (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) := by
    refine ss_bal_of hI.balanced hI.root (r' := w.next + 4)
      (by rw [treeOf_withNode i s _ htx9]; exact hroot9) (fun z hz => ?_) hold hlevB
      (fun z hz hzR m hm => ?_)
    · rcases hRB z hz with h1 | h1 | h1 | h1
      · left
        have hW0r : (w.withNode x (addAll i n ins)).top.rootKey = x := hxr.symm
        rw [hW0r]; exact h1
      · right; simp [h1]
      · right; simp [h1]
      · right; simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact absurd hzR (hxB hxn.symm)
      · rw [hBf] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx hlevB hfl hlev.symm
          (fun c y hy => Or.inl (hHL.1 c y hy))
      · rw [hBs] at hm; cases hm
        exact ss_rule_node hI.balanced hxR hAx hlevB hsl hlev.symm
          (fun c y hy => Or.inl (hHL.2 c y hy))
      · rw [hBr] at hm; cases hm
        refine ss_rule_root (keyLevel_pos p g (hh + 1)) (by rw [heightOf_keyLevel p hH1]; simp)
          ⟨_, hBf, by rw [keyLevel_succ]⟩ ⟨_, hBs, by rw [keyLevel_succ]⟩
  have hrk10 : ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))).top.rootKey = w.next + 4 := hrk9
  have hroot10 : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).root = some (w.next + 4) := by
    rw [treeOf_withNode i s _ htx9]
    exact hroot9
  refine ⟨ss_pinv hO10.1 (by rw [hrk10]; exact hroot10) (by rw [hrk10]; exact hSB) hBal,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · show (MW.afterSuperRoot w8 p i (w.next + 4)).path = w.path
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.2.2.2.1, e8, e7, e6, e5, e4, e3, e2, e1]
    rfl
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot 0 c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx, (afterSuperRoot_fields w8 p i (w.next + 4)).2.2.1,
      hlk y (Nat.ne_of_lt hylt) (ss_ne_of_lt_add hylt) (ss_ne_of_lt_add hylt)]
    exact hy
  · have h8 : w8.next = w.next + 6 := by
      rw [e8, e7, e6, e5, e4]
      show w3.next + 2 = _
      rw [hn3]
    exact Nat.le_trans (ss_le_add h8) (ss_afterSuperRoot_next w8 p i (w.next + 4))
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrk10] at hz
    have hW0r : (w.withNode x (addAll i n ins)).top.rootKey = x := hxr.symm
    rw [hW0r]
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]; exact Or.inr (Nat.le_refl _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)

theorem ss_root_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w 0 x n ins C)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up 0 x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w 0 x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  have hin' : (n.firstTime == some i) = false := by simpa using hin
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_zero _ _) ?_
  dsimp only
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin']
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (newSuperRoot_eq v _ h.hyp.top) ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact ss_root_new_post hp hb h hcase hin hgh hH rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## 11. Under an inner parent: the parent's step -/

/-- `getNode` changes no node outside the bounds. -/
theorem ss_getNode_outside (c : Ctx) (w : MW) (x : NodeId) :
    WP (SIS.Tree.getNode x) c w (fun _ w1 => w1.outside = w.outside) := by
  unfold SIS.Tree.getNode
  rw [wp_bind]
  refine (wp_get _ _ _).mpr ?_
  cases hl : w.nodes.lookup x with
  | some n => exact (wp_pure _ _ _ _).mpr rfl
  | none =>
    dsimp only
    rw [wp_bind]
    refine (wp_read _ _ _).mpr ?_
    cases hv : c.view x with
    | none => exact wp_throw _ _ _ _
    | some nd =>
      dsimp only
      split
      · exact wp_throw _ _ _ _
      · rw [wp_bind]
        refine (wp_set _ _ _ _).mpr ?_
        exact (wp_pure _ _ _ _).mpr rfl

/-- x cut back after the parent's step: under the bounds, x is the node n
then. -/
theorem ss_wp_getPut {c : Ctx} {w : MW} {x : NodeId} {t : Time} {n : MNode} {Q : MW → Prop}
    (h : w.outside = [] → w.nodes.lookup x = some n ∧ Q (w.withNode x (n.toPrev t))) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev t)) c w
      (fun _ w' => w'.outside = [] → Q w') := by
  rw [wp_bind]
  intro n' w1 hg
  have ho := ss_getNode_outside c w x n' w1 hg
  refine ss_wp_putNode (fun hout => ?_)
  have hout' : w.outside = [] := by rw [← ho]; exact hout
  obtain ⟨hlk, hQ⟩ := h hout'
  rw [getNode_hit c hlk] at hg
  simp only [Except.ok.injEq, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  exact hQ

/-- The state before the parent's step `up`: if it holds the halves (first and
second) and is otherwise the state before x's step, it meets the parent's
`CasPre`, and the parent's "if" state reaches what A reaches and the halves,
and not x if x was replaced. -/
theorem ss_parent_pre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPre p i base s tp w (d + 1) x n ins C)
    (htx : w.taken.contains x = false)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode}
    (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hq4 : w.taken.contains q = false) (hqx : q ≠ x) (hql : nq.leaf = false)
    (hk1 : (k1, x) ∈ live (ksOf nq))
    (hqr : q ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey)
    (hlq : wLevel s w x + 1 = wLevel s w q)
    (hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x)
    {f s2 : MNode} {sc : Nat} {L1 rest : List (Nat × NodeId)} {y0 : NodeId}
    (hsplit : live (ksOf (addAll i n ins)) = L1 ++ (sc, y0) :: rest) (hL1 : L1 ≠ [])
    (hfl : f.leaf = n.leaf) (hsl : s2.leaf = n.leaf) (hlf : live (ksOf f) = L1)
    (hls : live (ksOf s2) = (if n.leaf then sc else 0, y0) :: rest)
    (hwff : klongsWf (ksOf f) = true) (hwfs : klongsWf (ksOf s2) = true)
    (hszf : f.size ≤ p.M) (hszs : s2.size ≤ p.M)
    (hkf : ∀ c y, SIS.Tree.Klong.key c y ∈ f.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins))
    (hks : ∀ c y, SIS.Tree.Klong.key c y ∈ s2.ks → ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins))
    {first second : NodeId} {insU : List (Nat × NodeId)} {wU : MW}
    (hOU : SsOk p i base s tp (fun _ => False) wU)
    (hpU : wU.path = w.path) (htopU : wU.top = w.top) (hntU : wU.newTop = w.newTop)
    (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hwlU : ∀ y, y < w.next → wLevel s wU y = wLevel s w y)
    (hobjU : ∀ z, z ≠ first → z ≠ second → (treeOf i s wU).obj z = (treeOf i s w).obj z)
    (hfU : (treeOf i s wU).obj first = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩))
    (hsU : (treeOf i s wU).obj second = some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩))
    (hfirst : first = x ∨ w.next ≤ first) (hsecond : w.next ≤ second) (hfs : first ≠ second)
    (hins : (insU = [(sc, second)] ∧ first = x) ∨ insU = [(k1, first), (sc, second)]) :
    CasPre p i base s tp wU d q nq insU C ∧
      (first ≠ x → x ∉ reachOf i s (wU.withNode q (addAll i nq insU))) ∧
      (∀ z ∈ reachOf i s (wU.withNode q (addAll i nq insU)),
        z ∈ reachOf i s (w.withNode x (addAll i n ins)) ∨ z = first ∨ z = second) ∧
      x ∈ reachOf i s (w.withNode x (addAll i n ins)) := by
  obtain ⟨-, hAx, hAz⟩ := ss_start hb h htx
  have hI := h.hyp
  have hlook := h.look
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (treeOf i s (w.withNode x (addAll i n ins))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  -- q's node: well formed, of size M at most
  have hnq := hI.sound.nodes q hqr _ hAq
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  have hnq' := hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq'
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq'
  rw [ksOf_length] at hnqs
  -- x is reached in A, and a kid of q there
  obtain ⟨loq, hiq, hgq⟩ := hI.sound.good.tr_reach_good _ q hqr _ hAq
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, -, hpp⟩ := live_split he
  have hkx := (hgq.tr_kids hAq _ (bounds_mem hiq he)).2.2.2 (by simp [hql])
  obtain ⟨mx, hmx, -, -, hgx⟩ := hkx
  simp only [hql, Bool.false_eq_true, ite_false] at hgx
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x (addAll i n ins)))
      ((treeOf i s (w.withNode x (addAll i n ins))).fuel w.top.rootKey) w.top.rootKey :=
    hI.sound.good.tr_closed hqr (g := wLevel s w q + 1) (tc_kid hAq hk1 (tc_self _ _ x))
  have hsc1 : max loq k1 < sc := Good.tr_split_lo hgx hAx hsplit hL1
  have hscpost : ∀ b ∈ post, sc < b.1 :=
    tr_lt_post hpp (Good.tr_hi hgx hAx (y := y0) (by rw [hsplit]; simp))
  -- the klongs for the parent
  have hlenU : insU.length = 1 ∨ insU.length = 2 := by
    rcases hins with ⟨rfl, -⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmemU : ∀ c y, (c, y) ∈ insU → y = first ∨ y = second := by
    intro c y hm
    rcases hins with ⟨rfl, -⟩ | rfl
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      exact Or.inr hm.2
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm
      · exact Or.inl hm.2
      · exact Or.inr hm.2
  have hliveU : insU.foldl (fun m cy => insertCv cy.1 cy.2 m) (live (ksOf nq)) =
      insertCv sc second (insertCv k1 first (live (ksOf nq))) := by
    rcases hins with ⟨rfl, rfl⟩ | rfl
    · simp only [List.foldl_cons, List.foldl_nil]
      rw [ss_insertCv_mem (live_sorted _) hk1]
    · rfl
  -- the state at q
  have hkq : wU.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq : wU.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  have hwq : wLevel s wU q = wLevel s w q := hwlU q hqlt
  have hqf : q ≠ first := by
    rcases hfirst with e | e
    · rw [e]; exact hqx
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt e)
  have hqs : q ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt hsecond)
  obtain ⟨tq, rq, hrq⟩ := (hOU.toBooks (fun _ h => h)).timeFirst q nq hlkq hkq
  obtain ⟨rq', hrq'⟩ := addAll_first (i := i) hrq insU
  have hOq := ssOk_withNode (E' := fun _ => False) hOU hlkq hkq (addAll_leaf i nq insU)
    (Or.inl (by rw [hrq', hrq]; rfl))
    (fun t ht => addAll_timesLe (ss_timesLe (hOU.books.times q nq hlkq)) insU t (ss_time_ksOf ht))
    (fun n0 hs0 => addAll_ext (prim_timesBefore (hb.times q n0 hs0))
      (frame_overlay_ext hOU.frame hlkq hkq hs0).2.2 insU)
    (by rw [hrq']; simp) (fun _ _ h => h)
  -- the parent's "if" state's map B
  have hBq : (treeOf i s (wU.withNode q (addAll i nq insU))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq insU)⟩) := by
    rw [hOq.2, ss_ite_pos rfl, addAll_leaf, hwq]
  have hBo : ∀ z, z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z = (treeOf i s wU).obj z := by
    intro z hz
    rw [hOq.2, ss_ite_neg hz]
  have hBx : ((treeOf i s (wU.withNode q (addAll i nq insU))).obj x).isSome = true := by
    rw [hBo x hqx.symm]
    by_cases hxf : x = first
    · rw [hxf, hfU]; rfl
    · have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
      rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; rfl
  have hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z =
        (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
    intro z h0 h1 h2 h3
    rw [hBo z h3, hobjU z h1 h2, hAz z h0]
  have hBA : ∀ z, ((treeOf i s (w.withNode x (addAll i n ins))).obj z).isSome = true →
      ((treeOf i s (wU.withNode q (addAll i nq insU))).obj z).isSome = true := by
    intro z hz
    by_cases h3 : z = q
    · rw [h3, hBq]; rfl
    by_cases h1 : z = first
    · rw [h1, hBo _ hqf.symm, hfU]; rfl
    by_cases h2 : z = second
    · rw [h2, hBo _ hqs.symm, hsU]; rfl
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    rw [hsame z h0 h1 h2 h3]
    exact hz
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf (addAll i n ins)) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s (wU.withNode q (addAll i nq insU))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (ss_named_some hb h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) first (wLevel s w x) n.leaf
      L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs (by rw [hBo _ hqf.symm]; exact hfU) hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) second (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl]
    refine ss_nodeIs (by rw [hBo _ hqs.symm]; exact hsU) ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNq : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) q (wLevel s w q) false
      (insertCv sc second (insertCv k1 first (live (ksOf nq)))) (bnd p.M (some q) q) := by
    rw [← hql, ← addAll_leaf i nq insU, ← hliveU, ← addAll_live hnqwf]
    refine ss_nodeIs (by rw [hBq, addAll_leaf]) rfl (addAll_wf hnqwf insU) ?_ ?_
    · simp only [bnd, ite_true]
      have := addAll_size i nq insU
      rcases hlenU with e | e <;> rw [e] at this <;> omega
    · intro c y hy
      rcases (addAll_key_mem insU nq).mp (ss_key_ksOf hy) with h1 | h1
      · exact hBA y (ss_nodeOk_names hnq h1)
      · rcases hmemU c y h1 with e | e
        · rw [e, hBo _ hqf.symm, hfU]; rfl
        · rw [e, hBo _ hqs.symm, hsU]; rfl
  have hfirstA : first = x ∨ (treeOf i s (w.withNode x (addAll i n ins))).obj first = none := by
    rcases hfirst with e | e
    · exact Or.inl e
    · exact Or.inr (treeOf_fresh hb hI.books e).1
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplit (ex' := some q) hI.sound hqr hAq hql hk1 hAx hsplit
    hL1 hfirstA (treeOf_fresh hb hI.books hsecond).1 hfs hNf hNs hNq hBx hsame
  have hrkq : (wU.withNode q (addAll i nq insU)).top.rootKey = w.top.rootKey := by
    show wU.top.rootKey = _
    rw [htopU]
  refine ⟨⟨hlkq, ⟨cq, by rw [hpU]; exact hq1⟩, ?_, ?_, ?_, hOU.toBooks (fun _ h => h), hnqwf,
    hnqs, hlenU, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the path
    refine ⟨by rw [hpU, htopU]; exact h.path.root, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨c, u, n', h1, h2, h3⟩ := h.path.nodes e (by omega)
      have hux := hnx e c u he h1
      have hult : u < w.next := h.books.ids.1 u n' h2
      exact ⟨c, u, n', by rw [hpU]; exact h1, by rw [hlkU u hux hult]; exact h2,
        by rw [hkU]; exact h3⟩
    · obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
      have hux := hnx e c0 u (by omega) h1
      obtain ⟨n', hn', -⟩ := h.path.lookup (Nat.le_of_lt (by omega : e < d + 1)) h1
      have hult : u < w.next := h.books.ids.1 u n' hn'
      have huf : u ≠ first := by
        rcases hfirst with e' | e'
        · rw [e']; exact hux
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hult e')
      have hus : u ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hult hsecond)
      exact ⟨c0, u, c, y, nu, by rw [hpU]; exact h1, by rw [hpU]; exact h2,
        by rw [hobjU u huf hus]; exact h3, h4⟩
  · -- no node twice on the path
    intro e e' c c' u he he' h1 h2
    rw [hpU] at h1 h2
    exact h.nodup e e' c c' u he (by omega) h1 h2
  · -- the path is inner
    intro e c u nu he h1 h2
    rw [hpU] at h1
    obtain ⟨n', hn', ht'⟩ := h.path.lookup (Nat.le_of_lt (by omega : e < d + 1)) h1
    have hux := hnx e c u (by omega) h1
    have hult : u < w.next := h.books.ids.1 u n' hn'
    rw [hlkU u hux hult, hn'] at h2
    rw [← Option.some.inj h2]
    exact h.inner e c u n' (by omega) h1 hn'
  · -- two klongs: the halves of x
    intro a y1 b y2 heq
    rcases hins with ⟨rfl, -⟩ | rfl
    · simp at heq
    · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at heq
      obtain ⟨⟨rfl, -⟩, rfl, -⟩ := heq
      refine ⟨by omega, ⟨x, hk1⟩, fun c' y' hm hlt => ?_⟩
      rw [he] at hm
      rcases List.mem_append.mp hm with hm | hm
      · have := hpre _ hm
        simp only at this
        omega
      · rcases List.mem_cons.mp hm with hm | hm
        · cases hm
          omega
        · exact hscpost _ hm
  · -- the parent's "if" state
    have hrootQ : (treeOf i s (wU.withNode q (addAll i nq insU))).root = some w.top.rootKey := by
      rw [treeOf_withNode i s _ hkq]
      have e1 : (treeOf i s wU).root = (treeOf i s (w.withNode x (addAll i n ins))).root := by
        simp only [Tree.root, treeOf, hntU, htopU]
        rfl
      exact e1.trans hI.root
    have hxR : x ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
      rw [reach_of_root hI.root]; exact hxreach
    have hqR : q ∈ reach (treeOf i s (w.withNode x (addAll i n ins))) := by
      rw [reach_of_root hI.root]; exact hqr
    have hHL := ss_halves_live hsplit hlf hls
    have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
    have hBf' : (treeOf i s (wU.withNode q (addAll i nq insU))).obj first =
        some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by rw [hBo _ hqf.symm, hfU]
    have hBs' : (treeOf i s (wU.withNode q (addAll i nq insU))).obj second =
        some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩) := by rw [hBo _ hqs.symm, hsU]
    have hBx' : ∃ m', (treeOf i s (wU.withNode q (addAll i nq insU))).obj x = some (.key m') ∧
        m'.level = wLevel s w x := by
      rw [hBo x hqx.symm]
      by_cases hxf : x = first
      · have e := hfU
        rw [← hxf] at e
        rw [e]; exact ⟨_, rfl, rfl⟩
      · rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; exact ⟨_, rfl, rfl⟩
    have hold : ∀ z, z ∉ [x, first, second, q] →
        (treeOf i s (wU.withNode q (addAll i nq insU))).obj z =
          (treeOf i s (w.withNode x (addAll i n ins))).obj z := by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      exact hsame z hz.1 hz.2.1 hz.2.2.1 hz.2.2.2
    have hlevB := ss_lev_of hold (by
      intro z hz m hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      have hxcase : ∀ m, (treeOf i s (w.withNode x (addAll i n ins))).obj x = some (.key m) →
          ∃ m', (treeOf i s (wU.withNode q (addAll i nq insU))).obj x = some (.key m') ∧
            m'.level = m.level := by
        intro m hm
        rw [hAx] at hm
        cases hm
        exact hBx'
      rcases hz with e | e | e | e
      · rw [e] at hm ⊢; exact hxcase m hm
      · rcases hfirst with ef | ef
        · rw [e, ef] at hm ⊢; exact hxcase m hm
        · rw [e, (treeOf_fresh hb hI.books ef).1] at hm; cases hm
      · rw [e, (treeOf_fresh hb hI.books hsecond).1] at hm; cases hm
      · rw [e] at hm ⊢
        rw [hAq] at hm
        cases hm
        exact ⟨_, hBq, rfl⟩)
    have hBal : Balanced p (treeOf i s (wU.withNode q (addAll i nq insU))) := by
      refine ss_bal_of hI.balanced hI.root hrootQ (fun z hz => ?_) hold hlevB
        (fun z hz hzR m hm => ?_)
      · rcases hRB z hz with h1 | h1 | h1
        · exact Or.inl h1
        · right; simp [h1]
        · right; simp [h1]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        have hfr : ∀ m, (treeOf i s (wU.withNode q (addAll i nq insU))).obj first =
            some (.key m) → 0 < m.level ∧ m.leaf = (p.heightOf m.level == 0) ∧
            (m.leaf = false → ∀ c y, (c, y) ∈ live m.ks →
              ∃ m', (treeOf i s (wU.withNode q (addAll i nq insU))).obj y = some (.key m') ∧
                m'.level + 1 = m.level) := by
          intro m hm
          rw [hBf'] at hm
          cases hm
          exact ss_rule_node hI.balanced hxR hAx hlevB hfl rfl
            (fun c y hy => Or.inl (hHL.1 c y hy))
        rcases hz with e | e | e | e
        · rw [e] at hzR hm
          by_cases hxf : x = first
          · rw [hxf] at hm; exact hfr m hm
          · exact absurd hzR (hxB (Ne.symm hxf))
        · rw [e] at hm; exact hfr m hm
        · rw [e, hBs'] at hm
          cases hm
          exact ss_rule_node hI.balanced hxR hAx hlevB hsl rfl
            (fun c y hy => Or.inl (hHL.2 c y hy))
        · rw [e, hBq] at hm
          cases hm
          refine ss_rule_node hI.balanced hqR hAq hlevB rfl rfl (fun c y hy => ?_)
          rw [addAll_live hnqwf] at hy
          rcases mem_foldl_insertCv_src insU _ hy with h1 | h1
          · exact Or.inl ⟨c, h1⟩
          · rcases hmemU c y h1 with e' | e'
            · rw [e']; exact Or.inr ⟨_, hBf', hlq⟩
            · rw [e']; exact Or.inr ⟨_, hBs', hlq⟩
    exact ⟨by rw [hrkq]; exact hrootQ, by rw [hrkq]; exact hSB, hOq.1.frame, hOq.1.top, hBal,
      hOq.1.toBooks (fun _ h => h)⟩
  · intro hfx
    unfold reachOf
    rw [hrkq]
    exact hxB hfx
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrkq] at hz
    exact hRB z hz
  · exact hxreach

/-! ## 12. Under an inner parent: x made by the transaction -/

theorem ss_parent_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w (d + 1) x n ins C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = ssNote w4 "split.space1.inplace") :
    WP (up q [(sc, w.next)] >>= fun _ => pure ()) { p := p, i := i, view := v } w5
      (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1, cq', q', nq', hq1', hon', hq3', hq4, hqx, hql, hk1, hqr, hlq, hnx⟩ :=
    ss_path hb h hon htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  obtain ⟨hO, hAx, hAz⟩ := ss_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  -- the states
  have hlk1 : ∀ y, y ≠ w.next → w1.nodes.lookup y = w.nodes.lookup y := by
    intro y hy
    rw [e1]
    exact prim_lookup_append_ne _ _ hy
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hwl1 : ∀ y, y ≠ w.next → wLevel s w1 y = wLevel s w y := by
    intro y hy
    rw [e1]
    exact prim_wLevel_afterNewKey hy
  have hwl1n : wLevel s w1 w.next = p.keyLevel g hh := by
    rw [e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hO2 : SsOk p i base s tp (fun z => z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.books.timeFirst x n hlook htx
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
  have hO3 : SsOk p i base s tp (fun z => z = w.next) w3 ∧
      ∀ z, (treeOf i s w3).obj z = if z = x then some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩)
        else (treeOf i s w2).obj z := by
    rw [e3, ← hwx]
    refine ssOk_withNode hO2 (by rw [hN2, hlk1 x (Nat.ne_of_lt hxlt)]; exact hlook)
      (by rw [hk2]; exact htx) hfl
      (Or.inl hfst) htf (fun n0 hn0 => by rw [hsx] at hn0; cases hn0)
      (by rw [hf1]; simp) (fun z _ hz => hz)
  have hN3 : ∀ y, y ≠ x → w3.nodes.lookup y = w2.nodes.lookup y := by
    intro y hy
    rw [e3]
    exact lookup_upsert_ne _ _ hy
  have hwl3 : wLevel s w3 = wLevel s w1 := by rw [e3, ← hwl2]; rfl
  have hO4 : SsOk p i base s tp (fun _ => False) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) (by rw [hs1]; simp)
      (fun z hz hz' => hz hz')
  have hO5 : SsOk p i base s tp (fun _ => False) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hn5 : w5.next = w.next + 2 := by rw [e5, e4, e3, e2, e1]; rfl
  obtain ⟨hpre, -, hreach, hxr⟩ := ss_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hlq hnx
    hsplit hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := x) (second := w.next)
    (insU := [(sc, w.next)]) hO5
    (by rw [e5, e4, e3, e2, e1]; rfl) (by rw [e5, e4, e3, e2, e1]; rfl)
    (by rw [e5, e4, e3, e2, e1]; rfl) (by rw [e5, e4, e3, e2, e1]; rfl)
    (by
      intro y hyx hy
      rw [e5, e4]
      show (w3.withNode w.next s2).nodes.lookup y = _
      rw [ss_lookup_withNode (Nat.ne_of_lt hy), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hy)])
    (by
      intro y hy
      rw [show wLevel s w5 = wLevel s w1 by rw [e5, e4, ← hwl3]; rfl]
      exact hwl1 y (Nat.ne_of_lt hy))
    (by
      intro z h1 h2
      rw [hT5, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h1, hT2, hO1.2, ss_ite_neg h2])
    (by rw [hT5, hO4.2, ss_ite_neg (Nat.ne_of_lt hxlt), hO3.2, ss_ite_pos rfl])
    (by rw [hT5, hO4.2, ss_ite_pos rfl, hlev])
    (Or.inl rfl) (Nat.le_refl _) (Nat.ne_of_lt hxlt) (Or.inl ⟨rfl, rfl⟩)
  rw [wp_bind]
  refine WP.mono (hup q _ w5 nq C hpre) (fun _ w' hpost => (wp_pure _ _ _ _).mpr ?_)
  intro hout
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hpU : w5.path = w.path := by rw [e5, e4, e3, e2, e1]; rfl
  refine ⟨hPI, hCP.path.trans hpU, ?_, ?_, ?_⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    refine hCP.off y ny ?_ (fun d' c hd' => by rw [hpU]; exact hnot d' c (by omega))
    rw [e5, e4]
    show (w3.withNode w.next s2).nodes.lookup y = _
    rw [ss_lookup_withNode (Nat.ne_of_lt hylt), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hylt)]
    exact hy
  · exact Nat.le_trans (ss_le_add hn5) hCP.next
  · intro z hz
    rcases hCP.reach z hz with h1 | h1
    · rcases hreach z h1 with h2 | h2 | h2
      · exact Or.inl h2
      · rw [h2]; exact Or.inl hxr
      · rw [h2]; exact Or.inr (Nat.le_refl _)
    · exact Or.inr (Nat.le_trans (ss_le_add hn5) h1)

theorem ss_parent_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w (d + 1) x n ins C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  obtain ⟨k1, cq, q, nq, hq1, -, hq3, -, -, hql, -⟩ := ss_path hb h hon htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true, hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ss_parent_inPlace_post hp hb h hup hcase hin hgh hq1 hq3 hH rfl rfl rfl rfl rfl

/-! ## 13. Under an inner parent: x from before the transaction -/

theorem ss_parent_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w (d + 1) x n ins C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} {k1 : Nat} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hon' : w.path[d + 1]? = some (some k1, x))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = ssNote w3 "split.space1")
    (e5 : w5 = w4.withNode w.next f) (e6 : w6 = w5.withNode (w.next + 2) s2) :
    WP (up q [(k1, w.next), (sc, w.next + 2)] >>= fun _ =>
        SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } w6 (CasPost p i base s tp w (d + 1) x n ins C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hql, hk1, hqr, hlq, hnx⟩ :=
    ss_path hb h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  obtain ⟨hO, hAx, hAz⟩ := ss_start hb h htx
  have hI := h.hyp
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    ss_halves hp h.wf h.size (h.books.timeFirst x n hlook htx) h.len h.two hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.books.timeFirst x n hlook htx
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO4 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w4 := by
    rw [e4, e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT4 : treeOf i s w4 = treeOf i s w2 := by rw [e4, e3]; rfl
  have hk4 : w4.taken = w.taken := by rw [e4, e3, e2, e1]; rfl
  have hN4 : w4.nodes = w2.nodes := by rw [e4, e3]; rfl
  have hM4 : w4.made = w2.made := by rw [e4, e3]; rfl
  have hwl4 : wLevel s w4 = wLevel s w2 := by unfold wLevel; rw [hM4]
  have hwl0 : wLevel s w4 w.next = p.keyLevel g hh := by
    rw [hwl4, e2, prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hwl2 : wLevel s w4 (w.next + 2) = p.keyLevel g hh := by
    rw [hwl4, e2, ← hn1]
    exact ss_wLevel_newKey p g hh n.leaf [] (by rw [hn1]; exact hs2) (by rw [hn1]; exact hm2)
  have hwlo : ∀ y, y < w.next → wLevel s w4 y = wLevel s w y := by
    intro y hy
    rw [hwl4, e2, prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_of_lt_add hy), e1]
    exact prim_wLevel_afterNewKey (Nat.ne_of_lt hy)
  have hlk4 : ∀ y, y ≠ w.next → y ≠ w.next + 2 → w4.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2
    rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  have hold4 : ∀ y, y < w.next → (treeOf i s w4).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT4, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy), hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO5 : SsOk p i base s tp (fun z => z = w.next + 2) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w4).obj z := by
    rw [e5, ← hwl0]
    refine ssOk_withNode hO4 (m := ⟨n.leaf, []⟩)
      (by rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
          exact prim_lookup_append_self _ _ hn0)
      (by rw [hk4]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') (by rw [hf1]; simp) ?_
    · intro z hz hz'
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' hz
  have hO6 : SsOk p i base s tp (fun _ => False) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w5).obj z := by
    have hwl5 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by rw [e5]; exact hwl2
    rw [e6, ← hwl5]
    refine ssOk_withNode hO5.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e5]; show w4.taken.contains _ = false
        rw [hk4, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0')
      (by rw [hs1]; simp) (fun _ hz h => hz h)
    · rw [e5, ss_lookup_withNode hne20, hN4, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hn2')
  have hpU : w6.path = w.path := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hn6 : w6.next = w.next + 4 := by rw [e6, e5, e4, e3, e2]; show w1.next + 2 = _; rw [hn1]
  have hlk6 : ∀ y, y ≠ x → y < w.next → w6.nodes.lookup y = w.nodes.lookup y := by
    intro y _ hy
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hy), e5, ss_lookup_withNode (Nat.ne_of_lt hy),
      hlk4 y (Nat.ne_of_lt hy) (ss_ne_of_lt_add hy)]
  obtain ⟨hpre, hxnot, hreach, -⟩ := ss_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hlq hnx
    hsplit hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := w.next)
    (second := w.next + 2) (insU := [(k1, w.next), (sc, w.next + 2)]) hO6.1 hpU
    (by rw [e6, e5, e4, e3, e2, e1]; rfl) (by rw [e6, e5, e4, e3, e2, e1]; rfl)
    (by rw [e6, e5, e4, e3, e2, e1]; rfl) hlk6
    (by
      intro y hy
      rw [show wLevel s w6 = wLevel s w4 by rw [e6, e5]; rfl]
      exact hwlo y hy)
    (by
      intro z h1 h2
      rw [hO6.2, ss_ite_neg h2, hO5.2, ss_ite_neg h1, hT4, hO2.2, ss_ite_neg h2, hO1.2,
        ss_ite_neg h1])
    (by rw [hO6.2, ss_ite_neg hne20.symm, hO5.2, ss_ite_pos rfl, hlev])
    (by rw [hO6.2, ss_ite_pos rfl, hlev])
    (Or.inr (Nat.le_refl _)) (Nat.le_add_right _ _) hne20.symm (Or.inr rfl)
  rw [wp_bind]
  refine WP.mono (hup q _ w6 nq C hpre) (fun _ (w' : MW) hpost => ?_)
  refine ss_wp_getPut (n := n) (fun hout => ?_)
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hlk6x : w6.nodes.lookup x = some n := by
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hxlt), e5, ss_lookup_withNode (Nat.ne_of_lt hxlt),
      hlk4 x (Nat.ne_of_lt hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  have hlkx : w'.nodes.lookup x = some n := by
    refine hCP.off x n hlk6x ?_
    intro d' c hd' e
    rw [hpU] at e
    exact hnx d' c x hd' e rfl
  have hsx : (s.obj x).isSome = true := (h.books.first x n hlook htx).mpr hin
  have htx' : w'.taken.contains x = false := by
    cases e : w'.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hPI.books.taken x e)
      have := (hPI.books.ids.2.2.1 m hm).2
      rw [hmx] at this
      rw [(hb.ids x this).1] at hsx
      cases hsx
  have hxnr : x ∉ reachOf i s w' := by
    intro hx
    rcases hCP.reach x hx with h1 | h1
    · exact hxnot hxlt.ne' h1
    · rw [hn6] at h1
      exact absurd (Nat.lt_of_lt_of_le hxlt (Nat.le_trans (Nat.le_add_right _ 4) h1))
        (Nat.lt_irrefl _)
  have hO' : SsOk p i base s tp (fun _ => False) w' :=
    ⟨hPI.frame, hPI.books.toE, hPI.top, fun y m hy ht he => by
      obtain ⟨t, r, hr⟩ := hPI.books.timeFirst y m hy ht
      rw [hr] at he
      cases he⟩
  have hO'' := ssOk_withNode (E' := fun _ => False) hO' hlkx htx' rfl (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (ss_toPrev hb h htx hn0'))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  have ha : ∀ z ∈ reachOf i s w', (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).obj z =
      (treeOf i s w').obj z := by
    intro z hz
    have hzx : z ≠ x := fun e => hxnr (e ▸ hz)
    rw [hO''.2, ss_ite_neg hzx]
  have hrx : w'.top.rootKey ≠ x := fun e => hxnr (by unfold reachOf; rw [e]; exact tc_self _ _ _)
  have hfuel : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey =
      (treeOf i s w').fuel w'.top.rootKey := by
    simp only [Tree.fuel, hO''.2, ss_ite_neg hrx]
  have hreach' : reachOf i s (w'.withNode x (n.toPrev (i - 1))) = reachOf i s w' := by
    unfold reachOf
    show reachAt _ ((treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey)
      w'.top.rootKey = _
    rw [hfuel]
    exact reachAt_agree _ _ ha
  have hSB : Sound p.M none (treeOf i s (w'.withNode x (n.toPrev (i - 1))))
      (w'.withNode x (n.toPrev (i - 1))).top.rootKey C := by
    refine Sound.agree hPI.sound ha (fun z hz => ?_)
    by_cases hzx : z = x
    · rw [hzx, hO''.2, ss_ite_pos rfl]; rfl
    · rw [hO''.2, ss_ite_neg hzx]; exact hz
  have hroot : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root =
      some (w'.withNode x (n.toPrev (i - 1))).top.rootKey := by
    rw [treeOf_withNode i s _ htx']
    exact hPI.root
  have hBal3 : Balanced p (treeOf i s (w'.withNode x (n.toPrev (i - 1)))) := by
    have hrB : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root = some w'.top.rootKey := by
      rw [treeOf_withNode i s _ htx']; exact hPI.root
    refine Balanced.of_reach (N := [x]) hPI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
      (levels_kept_withNode i s _ hlkx htx') (fun z hz hzR => ?_)
    · left
      rw [reach_of_root hrB] at hz
      rw [reach_of_root hPI.root]
      have hz' : z ∈ reachOf i s (w'.withNode x (n.toPrev (i - 1))) := hz
      rw [hreach'] at hz'
      exact hz'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hO''.2, ss_ite_neg hz]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rw [hz, reach_of_root hrB] at hzR
      have hz' : x ∈ reachOf i s (w'.withNode x (n.toPrev (i - 1))) := hzR
      rw [hreach'] at hz'
      exact absurd hz' hxnr
  refine ⟨hlkx, ss_pinv hO''.1 hroot hSB hBal3, ⟨hCP.path.trans hpU, ?_, ?_, ?_⟩⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) (some k1) le_rfl (by rw [e]; exact hon')
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx]
    refine hCP.off y ny (by rw [hlk6 y hyx hylt]; exact hy) ?_
    intro d' c hd'
    rw [hpU]
    exact hnot d' c (by omega)
  · exact Nat.le_trans (ss_le_add hn6) hCP.next
  · intro z hz
    rw [hreach'] at hz
    rcases hCP.reach z hz with h1 | h1
    · rcases hreach z h1 with h2 | h2 | h2
      · exact Or.inl h2
      · rw [h2]; exact Or.inr (Nat.le_refl _)
      · rw [h2]; exact Or.inr (Nat.le_add_right _ _)
    · exact Or.inr (Nat.le_trans (ss_le_add hn6) h1)

theorem ss_klongAt {c : Ctx} {w w0 : MW} {d k : Nat} {x : NodeId} (hp : w.path = w0.path)
    (h : w0.path[d]? = some (some k, x)) : SIS.Tree.klongAt d c w = .ok (k, w) :=
  klongAt_eq c (by rw [hp]; exact h)

theorem ss_parent_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {ins : List (Nat × NodeId)} {w : MW} {n : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPre p i base s tp w (d + 1) x n ins C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) (hin : ¬ n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up (d + 1) x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w (d + 1) x n ins C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  obtain ⟨k1, cq, q, nq, hq1, hon', hq3, -, -, hql, -⟩ := ss_path hb h hon htx
  have hc' : (!false && decide ((n.lastVersion i).size > p.splitAbove)) = true := by
    simpa using hcase
  have hin' : (n.firstTime == some i) = false := by simpa using hin
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin', hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i (n.lastVersion i) ins = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_klongAt rfl hon') ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact ss_parent_new_post hp hb h hup hcase hin hgh hq1 hq3 hon' hH rfl rfl rfl rfl rfl rfl

/-! ## 14. The step

`handleFullWith` with a space split: at the space root or under an inner
parent, x made by the transaction or not. (`Shows` is not needed: every node
read is in the overlay.) -/

theorem handleFull_space {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {ins : List (Nat × NodeId)} {w : MW} {n : MNode} {C : List (Key × Nat)}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (h : CasPre p i base s tp w depth x n ins C)
    (hup : ∀ d, depth = d + 1 → UpOk p i base s tp v up d)
    (hcase : p.splitAbove < (n.lastVersion i).size) :
    WP (SIS.Tree.handleFullWith up depth x ins (n.lastVersion i) false)
      { p := p, i := i, view := v } w (CasPost p i base s tp w depth x n ins C) := by
  cases depth with
  | zero =>
    by_cases hin : n.firstTime = some i
    · exact ss_root_inPlace hp hb h hcase hin
    · exact ss_root_new hp hb h hcase hin
  | succ d =>
    by_cases hin : n.firstTime = some i
    · exact ss_parent_inPlace hp hb h (hup d rfl) hcase hin
    · exact ss_parent_new hp hb h (hup d rfl) hcase hin

end Contract

