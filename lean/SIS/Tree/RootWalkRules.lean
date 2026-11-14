/-
The walk of the kinds with the space root (`KrInv`: `KdInv` and `RootK`, the
writer's space root a key node), a copy of the kinds walk (WriterKinds*.lean)
whose names begin with kr; `newSuperRoot` takes a key node.

The tree model (bergdb 024-12, TP7): the kinds of the nodes that the klongs
of the writer's overlay name (`KindCache`, SIS/Tree/OverlayKinds.lean),
walked together with the books (`Book`). This file: the key klongs of the
node functions, as a statement about a compare value and a pointer (a leaf's
klongs keep their compare values; an inner node's may get the empty key,
which does not matter for its kind), the state of the walk, and the writer's
primitive steps.
-/
import SIS.Tree.OverlayKinds
import SIS.Tree.WriterBookMerge
import SIS.Tree.MergeFrameDead
import SIS.Tree.WriterSteps
import SIS.Tree.GetSplit
import SIS.Tree.WalkComplete
import SIS.Tree.CacheGood
import SIS.Tree.WriterNonemptyRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Key klongs with compare values -/

/-- Every key klong (c, y) of ks meets P c y. -/
def krKs (P : Nat → NodeId → Prop) (ks : List Klong) : Prop :=
  ∀ c y, Klong.key c y ∈ ks → P c y

/-- Every pair (c, y) of l meets P c y. -/
def krPairs (P : Nat → NodeId → Prop) (l : List (Nat × NodeId)) : Prop := ∀ q ∈ l, P q.1 q.2

/-- P does not look at the compare value. -/
def krFree (P : Nat → NodeId → Prop) : Prop := ∀ c c' y, P c y → P c' y

theorem krKs_nil (P : Nat → NodeId → Prop) : krKs P [] := by
  intro c y h; cases h

theorem krKs_of_sub {P : Nat → NodeId → Prop} {a b : List Klong} (hs : ∀ k ∈ a, k ∈ b)
    (h : krKs P b) : krKs P a := fun c y hm => h c y (hs _ hm)

theorem krKs_append {P : Nat → NodeId → Prop} {a b : List Klong} (ha : krKs P a)
    (hb : krKs P b) : krKs P (a ++ b) := by
  intro c y hm
  rcases List.mem_append.mp hm with hm | hm
  · exact ha c y hm
  · exact hb c y hm

theorem krKs_cons_time {P : Nat → NodeId → Prop} (t : Time) {r : List Klong} (h : krKs P r) :
    krKs P (.time t :: r) := by
  intro c y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · exact h c y hm

theorem krKs_cons_del {P : Nat → NodeId → Prop} (b : List Nat) {r : List Klong} (h : krKs P r) :
    krKs P (.del b :: r) := by
  intro c y hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm
  · exact h c y hm

theorem krKs_cons_key {P : Nat → NodeId → Prop} {c : Nat} {y : NodeId} {r : List Klong}
    (hy : P c y) (h : krKs P r) : krKs P (.key c y :: r) := by
  intro c' z hm
  rcases List.mem_cons.mp hm with hm | hm
  · cases hm; exact hy
  · exact h c' z hm

theorem krKs_add_key {P : Nat → NodeId → Prop} {n : KNode} (t : Time) {c : Nat} {y : NodeId}
    (hn : krKs P n.ks) (hy : P c y) : krKs P (n.add t (.key c y)).ks := by
  have hk : krKs P [.time t, .key c y] :=
    krKs_cons_time t (krKs_cons_key hy (krKs_nil P))
  have hk1 : krKs P [.key c y] := krKs_cons_key hy (krKs_nil P)
  unfold KNode.add
  split
  · split
    · exact krKs_append hn hk
    · exact krKs_append hn hk1
  · exact krKs_append hn hk

theorem krKs_add_del {P : Nat → NodeId → Prop} {n : KNode} (t : Time) (b : List Nat)
    (hn : krKs P n.ks) : krKs P (n.add t (.del b)).ks := by
  have hk : krKs P [.time t, .del b] :=
    krKs_cons_time t (krKs_cons_del b (krKs_nil P))
  have hk1 : krKs P [.del b] := krKs_cons_del b (krKs_nil P)
  unfold KNode.add
  split
  · split
    · exact krKs_append hn hk
    · exact krKs_append hn hk1
  · exact krKs_append hn hk

theorem krKs_setAt_del {P : Nat → NodeId → Prop} {n : KNode} (i : Nat) (b : List Nat)
    (hn : krKs P n.ks) : krKs P (n.setAt i (.del b)).ks := by
  intro c y hm
  rcases List.mem_or_eq_of_mem_set hm with hm | hm
  · exact hn c y hm
  · cases hm

theorem krKs_toPrev {P : Nat → NodeId → Prop} {n : KNode} (t : Time) (hn : krKs P n.ks) :
    krKs P (n.toPrev t).ks :=
  krKs_of_sub (fun _ hk => (List.takeWhile_sublist _).subset hk) hn

/-- Klong i pointed to y keeps its compare value. -/
theorem krKs_repoint {P : Nat → NodeId → Prop} {n : KNode} (i : Nat) {y : NodeId}
    (hn : krKs P n.ks) (hy : ∀ c z, n.ks[i]? = some (.key c z) → P c y) :
    krKs P (n.repoint i y).ks := by
  unfold KNode.repoint
  split
  · rename_i c z hz
    intro c' y' hm
    rcases List.mem_or_eq_of_mem_set hm with hm | hm
    · exact hn c' y' hm
    · cases hm; exact hy c z hz
  · exact hn

theorem kr_setCv {P : Nat → NodeId → Prop} (m : List (Nat × NodeId)) (c : Nat) (y : NodeId)
    (hm : krPairs P m) (hy : P c y) : krPairs P (setCv m c y) := by
  unfold setCv
  split
  · intro q hq
    obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · subst he; exact hy
    · subst he; exact hm a ha
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hm q hq
    · rw [List.mem_singleton.mp hq]; exact hy

theorem kr_lastVersionFold {P : Nat → NodeId → Prop} (del : List Nat) (xs : List (Klong × Nat))
    (hx : ∀ q ∈ xs, ∀ cv y, q.1 = .key cv y → P cv y) (m : List (Nat × NodeId))
    (hm : krPairs P m) :
    krPairs P (xs.foldl (fun m (q : Klong × Nat) => match q.1 with
      | .key c y => if del.contains q.2 then m else setCv m c y
      | _ => m) m) := by
  induction xs generalizing m with
  | nil => exact hm
  | cons q xs ih =>
    rw [List.foldl_cons]
    apply ih (fun e he => hx e (List.mem_cons_of_mem _ he))
    obtain ⟨k, i⟩ := q
    cases k with
    | key c y =>
      dsimp only
      split
      · exact hm
      · exact kr_setCv m c y hm (hx _ List.mem_cons_self c y rfl)
    | time t => exact hm
    | del b => exact hm

theorem krKs_lastVersionGivenDel {P : Nat → NodeId → Prop} {n : KNode} (t : Time)
    (del : List Nat) (hn : krKs P n.ks) : krKs P (n.lastVersionGivenDel t del).ks := by
  unfold KNode.lastVersionGivenDel
  dsimp only
  apply krKs_cons_time
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  cases he
  have hq' := (List.mem_mergeSort).mp hq
  have hf := kr_lastVersionFold (P := P) del n.ks.zipIdx ?_ [] (fun q h => by cases h)
  · exact hf _ hq'
  · intro e he cv' y' hk
    have hm' : e.1 ∈ n.ks := List.fst_mem_of_mem_zipIdx (by obtain ⟨a, b⟩ := e; exact he)
    rw [hk] at hm'
    exact hn cv' y' hm'

theorem krKs_of_pairs_map {P : Nat → NodeId → Prop} {l : List (Nat × NodeId)}
    (f : Nat × NodeId → Klong) (hf : ∀ q, f q = .key q.1 q.2 ∨ (krFree P ∧ ∃ c, f q = .key c q.2))
    (h : krPairs P l) : krKs P (l.map f) := by
  intro cv y hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  rcases hf q with hc | ⟨hP, c, hc⟩
  · rw [hc] at he; cases he; exact h q hq
  · rw [hc] at he; cases he; exact hP _ _ _ (h q hq)

theorem kr_ite_key (b : Prop) [Decidable b] (a c : Nat) (y : NodeId) :
    ∃ c', (if b then Klong.key a y else Klong.key c y) = Klong.key c' y := by
  by_cases h : b
  · exact ⟨a, by simp [h]⟩
  · exact ⟨c, by simp [h]⟩

theorem kr_halves_shape {P : Nat → NodeId → Prop} (b leaf : Bool) (t : Time)
    (f s insK : List Klong) (sc : Nat) (hf : krKs P f) (hs : krKs P s) (hi : krKs P insK) :
    krKs P (if b = true then ((⟨leaf, .time t :: f⟩ : KNode), (⟨leaf, .time t :: s ++ insK⟩ : KNode), sc)
      else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)).1.ks ∧
    krKs P (if b = true then ((⟨leaf, .time t :: f⟩ : KNode), (⟨leaf, .time t :: s ++ insK⟩ : KNode), sc)
      else (⟨leaf, .time t :: f ++ insK⟩, ⟨leaf, .time t :: s⟩, sc)).2.1.ks := by
  cases b
  · exact ⟨krKs_cons_time t (krKs_append hf hi), krKs_cons_time t hs⟩
  · exact ⟨krKs_cons_time t hf, krKs_cons_time t (krKs_append hs hi)⟩

theorem krKs_halves {P : Nat → NodeId → Prop} (leaf : Bool) (t : Time) {last : KNode}
    {ins : List (Nat × NodeId)} (hP : leaf = false → krFree P) (hl : krKs P last.ks)
    (hi : krPairs P ins) :
    krKs P (halves leaf t last ins).1.ks ∧ krKs P (halves leaf t last ins).2.1.ks := by
  have hbody : krKs P (last.ks.drop 1) :=
    krKs_of_sub (fun _ hk => List.mem_of_mem_drop hk) hl
  have hf : ∀ j, krKs P ((last.ks.drop 1).take j) :=
    fun j => krKs_of_sub (fun _ hk => List.mem_of_mem_take hk) hbody
  have hs : ∀ j, krKs P ((last.ks.drop 1).drop j) :=
    fun j => krKs_of_sub (fun _ hk => List.mem_of_mem_drop hk) hbody
  have hs' : ∀ (s : List Klong), krKs P s → krFree P → krKs P (match s with
      | .key _ y :: r => .key 0 y :: r
      | s => s) := by
    intro s h hF
    split
    · rename_i c y r
      exact krKs_cons_key (hF _ _ _ (h c y List.mem_cons_self))
        (krKs_of_sub (fun _ hk => List.mem_cons_of_mem _ hk) h)
    · exact h
  unfold halves
  dsimp only
  apply kr_halves_shape
  · exact hf _
  · cases leaf with
    | true => exact hs _
    | false => exact hs' _ (hs _) (hP rfl)
  · apply krKs_of_pairs_map _ _ hi
    intro q
    cases leaf with
    | true => left; simp
    | false =>
      right
      exact ⟨hP rfl, kr_ite_key _ _ _ _⟩

theorem kr_replaceKlong_go {P : Nat → NodeId → Prop} (t : Time) (c : Nat) {y : NodeId}
    (hy : P c y) (rest pre : List Klong) (cur : Option Time) (ks' : List Klong)
    (hp : krKs P pre) (hr : krKs P rest)
    (h : replaceKlong.go t c y pre rest cur = .ok (some ks')) : krKs P ks' := by
  induction rest generalizing pre cur with
  | nil => simp [replaceKlong.go] at h
  | cons k r ih =>
    have hr' : krKs P r := krKs_of_sub (fun _ hk => List.mem_cons_of_mem _ hk) hr
    cases k with
    | time x =>
      simp only [replaceKlong.go] at h
      exact ih _ _ (krKs_append hp (krKs_cons_time x (krKs_nil P))) hr' h
    | key c' y' =>
      simp only [replaceKlong.go] at h
      split at h
      · cases h
        exact krKs_append hp (krKs_cons_key hy hr')
      · exact ih _ _ (krKs_append hp (krKs_cons_key (hr c' y' List.mem_cons_self)
          (krKs_nil P))) hr' h
    | del b => simp [replaceKlong.go] at h

theorem krKs_replaceKlong {P : Nat → NodeId → Prop} {ks : List Klong} {t : Time} {c : Nat}
    {y : NodeId} {ks' : List Klong} (h : replaceKlong ks t c y = .ok (some ks'))
    (hk : krKs P ks) (hy : P c y) : krKs P ks' :=
  kr_replaceKlong_go t c hy ks [] none ks' (krKs_nil P) hk h

theorem krKs_insertSorted {P : Nat → NodeId → Prop} {ks : List Klong} (cv : Nat) {y : NodeId}
    (hk : krKs P ks) (hy : P cv y) : krKs P (insertSorted ks cv y) := by
  induction ks with
  | nil => exact krKs_cons_key hy (krKs_nil P)
  | cons k r ih =>
    have hr : krKs P r := krKs_of_sub (fun _ h => List.mem_cons_of_mem _ h) hk
    have hcons : ∀ s, krKs P s → krKs P (k :: s) := by
      intro s hs cv z hm
      rcases List.mem_cons.mp hm with hm | hm
      · rw [← hm] at hk; exact hk cv z List.mem_cons_self
      · exact hs cv z hm
    unfold insertSorted
    split
    · split
      · exact krKs_cons_key hy hk
      · exact hcons _ (ih hr)
    · exact hcons _ (ih hr)

theorem krKs_renameKey {P : Nat → NodeId → Prop} {ks : List Klong} {t : Klong} {c1 : Nat}
    {y1 : NodeId} {r : List Klong} (c' : Nat) (hP : krFree P) (he : ks = t :: .key c1 y1 :: r)
    (hk : krKs P ks) : krKs P (t :: .key c' y1 :: r) := by
  subst he
  intro cv y hm
  rcases List.mem_cons.mp hm with hm | hm
  · exact hk cv y (hm ▸ List.mem_cons_self)
  · rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact hP _ _ _ (hk c1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · exact hk cv y (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))

/-! ## The state of the walk -/

/-- The writer's space root is a key node: one of the overlay's `gh`, or one of
the oracle. -/
def RootK (K : KindOracle) (w : W) : Prop := ∃ g, IsKeySeg K w w.top.rootKey g

/-- What the walk of the kinds keeps besides the books, with B the
transaction's first id: the kinds of the overlay's klongs, of the key access
path and of the made nodes' replaced nodes; a value made is no key node; a
node of the path that has a node after it, and a made node of `madeFor`, are
key nodes of the overlay; the space root is a key node (`RootK`). -/

structure KrInv (K : KindOracle) (B : NodeId) (w : W) : Prop where
  cache : KindCache K w
  path : PathKinds K w
  made : MadeForSeg K w
  vals : ∀ q ∈ w.vals, B ≤ q.1 ∧ q.1 < w.next ∧ q.1 ∉ w.gh.map (·.1)
  pathGh : ∀ d a q, w.path[d]? = some (a, q) → d + 1 < w.path.length → q ∈ w.gh.map (·.1)
  madeGh : ∀ q ∈ w.madeFor, q.1 ∈ w.gh.map (·.1)
  pathSome : ∀ d a q, w.path[d + 1]? = some (a, q) → a ≠ none
  root : RootK K w

/-- A state and a later one: the books' relation, and every value stays. -/
def KrLe (w v : W) : Prop := Kept w v ∧ ∀ q ∈ w.vals, q ∈ v.vals

theorem KrLe.refl (w : W) : KrLe w w := ⟨Kept.refl w, fun _ h => h⟩

theorem KrLe.trans {a b d : W} (h1 : KrLe a b) (h2 : KrLe b d) : KrLe a d :=
  ⟨h1.1.trans h2.1, fun q hq => h2.2 q (h1.2 q hq)⟩

theorem KrLe.same {w v : W} (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hv : v.vals = w.vals) :
    KrLe w v := ⟨Kept.same hn hg, fun q hq => by rw [hv]; exact hq⟩

theorem IsKeySeg.krMono {K : KindOracle} {w v : W} {y : NodeId} {g : Nat} (h : IsKeySeg K w y g)
    (hk : KrLe w v) : IsKeySeg K v y g := by
  rcases h with ⟨hh, hm⟩ | h
  · exact Or.inl ⟨hh, hk.1.2 _ hm⟩
  · exact Or.inr h

theorem RootK.mono {K : KindOracle} {w v : W} (h : RootK K w) (hk : KrLe w v)
    (ht : v.top.rootKey = w.top.rootKey) : RootK K v := by
  obtain ⟨g, hg⟩ := h
  exact ⟨g, by rw [ht]; exact hg.krMono hk⟩

theorem IsValId.krMono {K : KindOracle} {w v : W} {y : NodeId} (h : IsValId K w y)
    (hk : KrLe w v) : IsValId K v y := by
  rcases h with ⟨hh, hm⟩ | h
  · exact Or.inl ⟨hh, hk.2 _ hm⟩
  · exact Or.inr h

theorem KindKlong.krMono {K : KindOracle} {w v : W} {g h c : Nat} {y : NodeId}
    (hy : KindKlong K w g h c y) (hk : KrLe w v) : KindKlong K v g h c y :=
  ⟨fun h0 => (hy.1 h0).krMono hk,
   fun h0 => ⟨fun h7 => ((hy.2 h0).1 h7).krMono hk, fun h7 => ((hy.2 h0).2 h7).krMono hk⟩⟩

theorem krKs_mono {K : KindOracle} {w v : W} {g h : Nat} {ks : List Klong}
    (hks : krKs (KindKlong K w g h) ks) (hk : KrLe w v) : krKs (KindKlong K v g h) ks :=
  fun c y hm => (hks c y hm).krMono hk

theorem krPairs_mono {K : KindOracle} {w v : W} {g h : Nat} {l : List (Nat × NodeId)}
    (hl : krPairs (KindKlong K w g h) l) (hk : KrLe w v) : krPairs (KindKlong K v g h) l :=
  fun q hq => (hl q hq).krMono hk

/-- An inner node's klong: its compare value does not matter. -/
theorem kr_free {K : KindOracle} {w : W} {g h : Nat} (hh : h ≠ 0) : krFree (KindKlong K w g h) :=
  fun _ _ _ hy => ⟨hy.1, fun h0 => absurd h0 hh⟩

theorem kr_free_of_leaf {K : KindOracle} {w : W} {g h : Nat} {leaf : Bool} (hl : leaf = (h == 0)) :
    leaf = false → krFree (KindKlong K w g h) := by
  intro hf
  apply kr_free
  intro h0
  subst h0
  simp at hl
  rw [hl] at hf
  cases hf

/-! ## Facts of the state -/

section Facts

variable {K : KindOracle} {B : NodeId} {c : Ctx} {w : W}

theorem kr_mem_ids {x : NodeId} {g h : Nat} (hm : (x, g, h) ∈ w.gh) : x ∈ w.gh.map (·.1) :=
  List.mem_map.mpr ⟨_, hm, rfl⟩

/-- A key node is no value. -/
theorem kr_not_val (hb : Book B c w) (hk : ViewKinds K B c) (hi : KrInv K B w) {y : NodeId}
    {g h : Nat} (hm : (y, g, h) ∈ w.gh) : ¬ IsValId K w y := by
  rintro (⟨hh, hv⟩ | hv)
  · exact (hi.vals _ hv).2.2 (kr_mem_ids hm)
  · rcases hb.tag y g h hm with ⟨nd, hnd, hd, hl, _, _⟩ | ⟨hB, _, _⟩
    · exact hk.notBoth y _ (hk.node y nd hnd hd hl) hv
    · have := hk.oldVal y hv
      omega

theorem kr_isKey {x : NodeId} {g h : Nat} (hm : (x, g, h) ∈ w.gh) : IsKeySeg K w x g :=
  Or.inl ⟨h, hm⟩

/-- The klongs of an overlay node, by its entry in `gh`. -/
theorem kr_cache_node (hi : KrInv K B w) {x : NodeId} {n : KNode} {g h : Nat}
    (hl : w.nodes.lookup x = some n) (hm : (x, g, h) ∈ w.gh) : krKs (KindKlong K w g h) n.ks :=
  fun cv y hy => hi.cache x n g h (bk_mem_of_lookup _ _ _ hl) hm cv y hy

/-- A new id is no id of `gh`. -/
theorem kr_next_not (hb : Book B c w) : w.next ∉ w.gh.map (·.1) := by
  intro hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have := hb.bound q hq
  rw [he] at this
  exact Nat.lt_irrefl _ this

end Facts

/-- Every field that the walk reads is kept, and the next id does not go down. -/
theorem KrInv.frame {K : KindOracle} {B : NodeId} {w : W} (hi : KrInv K B w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hv : v.vals = w.vals)
    (hm : v.madeFor = w.madeFor) (hp : v.path = w.path) (hx : w.next ≤ v.next)
    (ht : v.top.rootKey = w.top.rootKey) :
    KrInv K B v := by
  have hle : KrLe w v := KrLe.same hn hg hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hi.root.mono hle ht⟩
  · intro x n g h hn' hg' cv y hy
    rw [hn] at hn'; rw [hg] at hg'
    exact (hi.cache x n g h hn' hg' cv y hy).krMono hle
  · intro d a q cv y h1 h2 g h hg'
    rw [hp] at h1 h2; rw [hg] at hg'
    exact (hi.path d a q cv y h1 h2 g h hg').krMono hle
  · intro q hq g h hg'
    rw [hm] at hq; rw [hg] at hg'
    exact (hi.made q hq g h hg').krMono hle
  · intro q hq
    rw [hv] at hq
    obtain ⟨h1, h2, h3⟩ := hi.vals q hq
    exact ⟨h1, by omega, by rw [hg]; exact h3⟩
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact hi.pathGh d a q h1 h2
  · intro q hq
    rw [hm] at hq; rw [hg]
    exact hi.madeGh q hq
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- The same with the path emptied. -/
theorem KrInv.clear {K : KindOracle} {B : NodeId} {w : W} (hi : KrInv K B w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hv : v.vals = w.vals)
    (hm : v.madeFor = w.madeFor) (hp : v.path = []) (hx : w.next ≤ v.next)
    (ht : v.top.rootKey = w.top.rootKey) :
    KrInv K B v := by
  have h0 : KrInv K B { w with path := [] } :=
    ⟨hi.cache, by intro d a q cv y h1; simp at h1, hi.made, hi.vals,
      by intro d a q h1; simp at h1, hi.madeGh, by intro d a q h1; simp at h1, hi.root⟩
  exact h0.frame v hn hg hv hm hp hx ht

/-! ## The states the primitive steps make -/

/-- A node of the view loaded into the overlay. -/
theorem KrInv.load {K : KindOracle} {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w)
    (hv : ViewIdsBelow B c.view) (hk : ViewKinds K B c) (hi : KrInv K B w) (x : NodeId)
    (nd : Node BVal) (hnd : c.view x = some nd) (hd : nd.isData = false)
    (hlv : nd.level ≤ c.p.keyMax) (hn0 : w.nodes.lookup x = none) (v : W)
    (hn : v.nodes = w.nodes ++ [(x, ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩)])
    (hg : v.gh = (x, c.p.segOf nd.level, c.p.heightOf nd.level) :: w.gh)
    (hvl : v.vals = w.vals) (hm : v.madeFor = w.madeFor) (hp : v.path = w.path)
    (hx : v.next = w.next) (ht : v.top.rootKey = w.top.rootKey) : KrInv K B v := by
  have hxn : x ∉ w.nodes.map (·.1) := bk_not_mem_ids_of_lookup _ x hn0
  have hxg : x ∉ w.gh.map (·.1) := by
    intro h; apply hxn; rw [hb.ids]; exact List.mem_reverse.mpr h
  have hle : KrLe w v :=
    ⟨Kept.grow _ [(x, c.p.segOf nd.level, c.p.heightOf nd.level)] hn hg,
      fun q hq => by rw [hvl]; exact hq⟩
  have hxB : x < B := hv x nd hnd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hi.root.mono hle ht⟩
  · intro y m g h hm' hg' cv z hz
    rw [hn] at hm'; rw [hg] at hg'
    simp only [List.mem_append, List.mem_singleton] at hm'
    simp only [List.mem_cons] at hg'
    rcases hm' with hm' | hm'
    · rcases hg' with hg' | hg'
      · cases hg'
        exact absurd (bk_mem_ids_of_mem _ _ _ hm') hxn
      · exact (hi.cache y m g h hm' hg' cv z hz).krMono hle
    · cases hm'
      rcases hg' with hg' | hg'
      · cases hg'
        have hkl := hk.klongs x nd hnd hd hlv cv z hz
        exact ⟨fun h0 => Or.inr (hkl.1 h0),
          fun h0 => ⟨fun h7 => Or.inr ((hkl.2 h0).1 h7), fun h7 => Or.inr ((hkl.2 h0).2 h7)⟩⟩
      · exact absurd (kr_mem_ids hg') hxg
  · intro d a q cv y h1 h2 g h hg'
    rw [hp] at h1 h2; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    have hqg := hi.pathGh d a q h1 (List.getElem?_eq_some_iff.mp h2).1
    rcases hg' with hg' | hg'
    · cases hg'; exact absurd hqg hxg
    · exact (hi.path d a q cv y h1 h2 g h hg').krMono hle
  · intro q hq g h hg'
    rw [hm] at hq; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    rcases hg' with hg' | hg'
    · have := hi.madeGh q hq
      rw [congrArg Prod.fst hg'] at this
      exact absurd this hxg
    · exact (hi.made q hq g h hg').krMono hle
  · intro q hq
    rw [hvl] at hq
    obtain ⟨h1, h2, h3⟩ := hi.vals q hq
    refine ⟨h1, by omega, ?_⟩
    rw [hg]
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by omega, h3⟩
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact List.mem_cons_of_mem _ (hi.pathGh d a q h1 h2)
  · intro q hq
    rw [hm] at hq; rw [hg]
    exact List.mem_cons_of_mem _ (hi.madeGh q hq)
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- A new key node with klongs of the right kind. -/
theorem KrInv.create {K : KindOracle} {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w)
    (hi : KrInv K B w) (g h : Nat) (N : KNode) (hks : krKs (KindKlong K w g h) N.ks) (v : W)
    (hn : v.nodes = w.nodes ++ [(w.next, N)]) (hg : v.gh = (w.next, g, h) :: w.gh)
    (hv : v.vals = w.vals) (hm : v.madeFor = w.madeFor) (hp : v.path = w.path)
    (hx : v.next = w.next + 2) (ht : v.top.rootKey = w.top.rootKey) : KrInv K B v ∧ KrLe w v := by
  have hxg := kr_next_not hb
  have hxn : w.next ∉ w.nodes.map (·.1) := by
    rw [hb.ids]; intro h; exact hxg (List.mem_reverse.mp h)
  have hle : KrLe w v := ⟨Kept.grow _ [(w.next, g, h)] hn hg, fun q hq => by rw [hv]; exact hq⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hi.root.mono hle ht⟩, hle⟩
  · intro y m g' h' hm' hg' cv z hz
    rw [hn] at hm'; rw [hg] at hg'
    simp only [List.mem_append, List.mem_singleton] at hm'
    simp only [List.mem_cons] at hg'
    rcases hm' with hm' | hm'
    · rcases hg' with hg' | hg'
      · cases hg'
        exact absurd (bk_mem_ids_of_mem _ _ _ hm') hxn
      · exact (hi.cache y m g' h' hm' hg' cv z hz).krMono hle
    · cases hm'
      rcases hg' with hg' | hg'
      · cases hg'
        exact (hks cv z hz).krMono hle
      · exact absurd (kr_mem_ids hg') hxg
  · intro d a q cv y h1 h2 g' h' hg'
    rw [hp] at h1 h2; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    have hqg := hi.pathGh d a q h1 (List.getElem?_eq_some_iff.mp h2).1
    rcases hg' with hg' | hg'
    · cases hg'; exact absurd hqg hxg
    · exact (hi.path d a q cv y h1 h2 g' h' hg').krMono hle
  · intro q hq g' h' hg'
    rw [hm] at hq; rw [hg] at hg'
    simp only [List.mem_cons] at hg'
    rcases hg' with hg' | hg'
    · have := hi.madeGh q hq
      rw [congrArg Prod.fst hg'] at this
      exact absurd this hxg
    · exact (hi.made q hq g' h' hg').krMono hle
  · intro q hq
    rw [hv] at hq
    obtain ⟨h1, h2, h3⟩ := hi.vals q hq
    refine ⟨h1, by omega, ?_⟩
    rw [hg]
    simp only [List.map_cons, List.mem_cons, not_or]
    exact ⟨by omega, h3⟩
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact List.mem_cons_of_mem _ (hi.pathGh d a q h1 h2)
  · intro q hq
    rw [hm] at hq; rw [hg]
    exact List.mem_cons_of_mem _ (hi.madeGh q hq)
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-! ## The primitive steps -/

section Steps

variable (K : KindOracle) (B : NodeId)

end Steps

end SIS.Tree
