/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)): the
state of the walk (`HtInv`: `HtCache` and the key access path's heights) with
the books (`Book`), and the writer's primitive steps. The klongs that a step
stores are of the right height when they are live klongs of a node of that
height, or pairs that name nodes one height below.
-/
import SIS.Tree.HeightsNode

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The key access path goes one height down at every inner node of it that is
not taken back. -/
def PathHt (H : NodeId → Nat → Prop) (w : W) : Prop :=
  ∀ d a q cv y, w.path[d]? = some (a, q) → w.path[d + 1]? = some (some cv, y) →
    ∀ g h, (q, g, h) ∈ w.gh → w.taken.contains q = false → h ≠ 0 → HasHt H w y (h - 1)

/-- The state of the walk of the heights, with B the transaction's first id:
the overlay's heights, the key access path's, and what is not taken back: the
space root, every id below B. That the path's first n nodes are not taken back
is `PathFreeTo`, which the steps that use it carry. -/
structure HtInv (H : NodeId → Nat → Prop) (B : NodeId) (c : Ctx) (w : W) : Prop where
  cache : HtCache c H w
  path : PathHt H w
  pathGh : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d]? = some (a, q) →
    d + 1 < w.path.length → q ∈ w.gh.map (·.1)
  rootFree : w.taken.contains w.top.rootKey = false
  takenAbove : ∀ x, w.taken.contains x = true → B ≤ x
  pathSome : ∀ (d : Nat) (a : Option Nat) (q : NodeId), w.path[d + 1]? = some (a, q) → a ≠ none

/-- What the view must meet besides `ViewHeights`: B is above its ids and above
every pointer of its key nodes. -/
structure ViewHtOK (H : NodeId → Nat → Prop) (B : NodeId) (c : Ctx) : Prop where
  ids : ViewIdsBelow B c.view
  heights : ViewHeights H B c
  ptrs : ∀ x nd, c.view x = some nd → ∀ cv y, Klong.key cv y ∈ klongsOf nd.hist → y < B
  times : ∀ x nd, c.view x = some nd → ∀ t, Klong.time t ∈ klongsOf nd.hist → t ≤ c.i

/-- The key access path's first n nodes are not taken back. -/
def PathFreeTo (w : W) (n : Nat) : Prop :=
  ∀ (d : Nat) (a : Option Nat) (q : NodeId), d < n → w.path[d]? = some (a, q) →
    w.taken.contains q = false

theorem PathFreeTo.mono {w : W} {n m : Nat} (h : PathFreeTo w n) (hm : m ≤ n) : PathFreeTo w m :=
  fun d a q hd hq => h d a q (by omega) hq

theorem PathFreeTo.congr {w v : W} {n : Nat} (h : PathFreeTo w n) (hp : v.path = w.path)
    (ht : v.taken = w.taken) : PathFreeTo v n := by
  intro d a q hd hq
  rw [hp] at hq; rw [ht]
  exact h d a q hd hq

theorem HtCache.congr {c : Ctx} {H : NodeId → Nat → Prop} {w v : W} (hc : HtCache c H w) (hn : v.nodes = w.nodes)
    (hg : v.gh = w.gh) (ht : v.taken = w.taken) : HtCache c H v := by
  intro x n g h hn' hg' htk
  rw [hn] at hn'; rw [hg] at hg'; rw [ht] at htk
  exact (hc x n g h hn' hg' htk).mono (fun q hq => by rw [hg]; exact hq)
    (fun y hy => by rw [ht]; exact hy)

theorem ht_free_of_eq {w v : W} (ht : v.taken = w.taken) :
    ∀ y, w.taken.contains y = false → v.taken.contains y = false := fun y h => by rw [ht]; exact h

/-- The fields that the walk reads kept. -/
theorem HtInv.frame {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hi : HtInv H B c w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hp : v.path = w.path)
    (ht : v.taken = w.taken) (htop : v.top.rootKey = w.top.rootKey) : HtInv H B c v := by
  have hgm : ∀ q ∈ w.gh, q ∈ v.gh := fun q hq => by rw [hg]; exact hq
  have hf := ht_free_of_eq ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n g h hn' hg' htk
    rw [hn] at hn'; rw [hg] at hg'; rw [ht] at htk
    exact (hi.cache x n g h hn' hg' htk).mono hgm hf
  · intro d a q cv y h1 h2 g h hg' htk hh
    rw [hp] at h1 h2; rw [hg] at hg'; rw [ht] at htk
    exact (hi.path d a q cv y h1 h2 g h hg' htk hh).mono hgm
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact hi.pathGh d a q h1 h2
  · rw [ht, htop]; exact hi.rootFree
  · intro x hx
    rw [ht] at hx
    exact hi.takenAbove x hx
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- The same with the path emptied. -/
theorem HtInv.clear {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hi : HtInv H B c w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hp : v.path = [])
    (ht : v.taken = w.taken) (htop : v.top.rootKey = w.top.rootKey) : HtInv H B c v := by
  have h0 : HtInv H B c { w with path := [] } :=
    ⟨fun x n g h hn hg' htk => (hi.cache x n g h hn hg' htk).mono (fun q hq => hq) (fun y hy => hy),
      by intro d a q cv y h1; simp at h1, by intro d a q h1; simp at h1,
      hi.rootFree, hi.takenAbove, by intro d a q h1; simp at h1⟩
  exact h0.frame v hn hg hp ht htop

/-- A node of the view loaded into the overlay. -/
theorem HtInv.load {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hb : Book B c w)
    (hvo : ViewHtOK H B c) (hi : HtInv H B c w) (x : NodeId)
    (nd : Node BVal) (hnd : c.view x = some nd) (hd : nd.isData = false)
    (hlv : nd.level ≤ c.p.keyMax) (hn0 : w.nodes.lookup x = none) (v : W)
    (hn : v.nodes = w.nodes ++ [(x, ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩)])
    (hg : v.gh = (x, c.p.segOf nd.level, c.p.heightOf nd.level) :: w.gh)
    (hp : v.path = w.path) (ht : v.taken = w.taken) (htop : v.top.rootKey = w.top.rootKey) :
    HtInv H B c v := by
  have hxn : x ∉ w.nodes.map (·.1) := bk_not_mem_ids_of_lookup _ x hn0
  have hxg : x ∉ w.gh.map (·.1) := by
    intro h; apply hxn; rw [hb.ids]; exact List.mem_reverse.mpr h
  have hgm : ∀ q ∈ w.gh, q ∈ v.gh := fun q hq => by rw [hg]; exact List.mem_cons_of_mem _ hq
  have hf := ht_free_of_eq ht
  have hfree : ∀ y, y < B → v.taken.contains y = false := by
    intro y hy
    cases hc : v.taken.contains y with
    | false => rfl
    | true =>
      rw [ht] at hc
      exact absurd (hi.takenAbove y hc) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y m g h hm' hg' htk
    rw [hn] at hm'; rw [hg] at hg'
    simp only [List.mem_append, List.mem_singleton] at hm'
    simp only [List.mem_cons] at hg'
    rcases hm' with hm' | hm'
    · rcases hg' with hg' | hg'
      · cases hg'
        exact absurd (bk_mem_ids_of_mem _ _ _ hm') hxn
      · rw [ht] at htk
        exact (hi.cache y m g h hm' hg' htk).mono hgm hf
    · cases hm'
      rcases hg' with hg' | hg'
      · cases hg'
        have hptr : ∀ cv z, (cv, z) ∈ (nodeK c.p nd).live ∨
            (cv, z) ∈ ((nodeK c.p nd).toPrev (c.i - 1)).live → z < B := by
          intro cv z hz
          rcases hz with hz | hz
          · exact hvo.ptrs x nd hnd cv z (ht_live_mem hz)
          · have hm := ht_live_mem hz
            exact hvo.ptrs x nd hnd cv z ((prefixAt_prefix _ _).subset hm)
        refine ⟨fun cv z hz => ⟨hfree z (hptr cv z (Or.inl hz)), fun h0 => ?_⟩,
          fun cv z hz => ⟨hfree z (hptr cv z (Or.inr hz)), fun h0 => ?_⟩, hvo.times x nd hnd⟩
        · exact Or.inr (hvo.heights.live x nd hnd hd hlv h0 cv z hz)
        · exact Or.inr (hvo.heights.prev x nd hnd hd hlv h0 cv z hz)
      · exact absurd (kd_mem_ids hg') hxg
  · intro d a q cv y h1 h2 g h hg' htk hh
    rw [hp] at h1 h2; rw [hg] at hg'; rw [ht] at htk
    simp only [List.mem_cons] at hg'
    have hqg := hi.pathGh d a q h1 (List.getElem?_eq_some_iff.mp h2).1
    rcases hg' with hg' | hg'
    · cases hg'; exact absurd hqg hxg
    · exact (hi.path d a q cv y h1 h2 g h hg' htk hh).mono hgm
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact List.mem_cons_of_mem _ (hi.pathGh d a q h1 h2)
  · rw [ht, htop]; exact hi.rootFree
  · intro y hy
    rw [ht] at hy
    exact hi.takenAbove y hy
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- A new key node meeting `NodeHt` for its height. -/
theorem HtInv.create {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hb : Book B c w)
    (hi : HtInv H B c w) (g h : Nat) (N : KNode) (hks : NodeHt c H w h N) (v : W)
    (hn : v.nodes = w.nodes ++ [(w.next, N)]) (hg : v.gh = (w.next, g, h) :: w.gh)
    (hp : v.path = w.path) (ht : v.taken = w.taken) (htop : v.top.rootKey = w.top.rootKey) :
    HtInv H B c v := by
  have hxg := kd_next_not hb
  have hxn : w.next ∉ w.nodes.map (·.1) := by
    rw [hb.ids]; intro h; exact hxg (List.mem_reverse.mp h)
  have hgm : ∀ q ∈ w.gh, q ∈ v.gh := fun q hq => by rw [hg]; exact List.mem_cons_of_mem _ hq
  have hf := ht_free_of_eq ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y m g' h' hm' hg' htk
    rw [hn] at hm'; rw [hg] at hg'; rw [ht] at htk
    simp only [List.mem_append, List.mem_singleton] at hm'
    simp only [List.mem_cons] at hg'
    rcases hm' with hm' | hm'
    · rcases hg' with hg' | hg'
      · cases hg'
        exact absurd (bk_mem_ids_of_mem _ _ _ hm') hxn
      · exact (hi.cache y m g' h' hm' hg' htk).mono hgm hf
    · cases hm'
      rcases hg' with hg' | hg'
      · cases hg'
        exact hks.mono hgm hf
      · exact absurd (kd_mem_ids hg') hxg
  · intro d a q cv y h1 h2 g' h' hg' htk hh
    rw [hp] at h1 h2; rw [hg] at hg'; rw [ht] at htk
    simp only [List.mem_cons] at hg'
    have hqg := hi.pathGh d a q h1 (List.getElem?_eq_some_iff.mp h2).1
    rcases hg' with hg' | hg'
    · cases hg'; exact absurd hqg hxg
    · exact (hi.path d a q cv y h1 h2 g' h' hg' htk hh).mono hgm
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact List.mem_cons_of_mem _ (hi.pathGh d a q h1 h2)
  · rw [ht, htop]; exact hi.rootFree
  · intro y hy
    rw [ht] at hy
    exact hi.takenAbove y hy
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- A node of the overlay stored again, meeting `NodeHt` for its height. -/
theorem HtInv.store {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hi : HtInv H B c w)
    (x : NodeId) (n' n0 : KNode) (hl : w.nodes.lookup x = some n0)
    (hks : ∀ g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → NodeHt c H w h n')
    (v : W) (hn : v.nodes = upsert w.nodes x n') (hg : v.gh = w.gh) (hp : v.path = w.path)
    (ht : v.taken = w.taken) (htop : v.top.rootKey = w.top.rootKey) : HtInv H B c v := by
  have hgm : ∀ q ∈ w.gh, q ∈ v.gh := fun q hq => by rw [hg]; exact hq
  have hf := ht_free_of_eq ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y m g h hm' hg' htk
    rw [hn] at hm'; rw [hg] at hg'; rw [ht] at htk
    rcases bk_mem_upsert w.nodes x n' n0 hl y m hm' with ⟨rfl, rfl⟩ | hm'
    · exact (hks g h hg' htk).mono hgm hf
    · exact (hi.cache y m g h hm' hg' htk).mono hgm hf
  · intro d a q cv y h1 h2 g h hg' htk hh
    rw [hp] at h1 h2; rw [hg] at hg'; rw [ht] at htk
    exact (hi.path d a q cv y h1 h2 g h hg' htk hh).mono hgm
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    exact hi.pathGh d a q h1 h2
  · rw [ht, htop]; exact hi.rootFree
  · intro y hy
    rw [ht] at hy
    exact hi.takenAbove y hy
  · intro d a q h1
    rw [hp] at h1
    exact hi.pathSome d a q h1

/-- A node of the key access path added after its last node q, by a live klong
of q that names y. -/
theorem HtInv.add {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W} (hi : HtInv H B c w) (cv : Nat) (y : NodeId)
    (hlast : ∀ a q, w.path.getLast? = some (a, q) → q ∈ w.gh.map (·.1) ∧
      ∀ g h, (q, g, h) ∈ w.gh → w.taken.contains q = false → h ≠ 0 → HasHt H w y (h - 1))
    (v : W) (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hp : v.path = w.path ++ [(some cv, y)])
    (ht : v.taken = w.taken) (htop : v.top.rootKey = w.top.rootKey) : HtInv H B c v := by
  have hgm : ∀ q ∈ w.gh, q ∈ v.gh := fun q hq => by rw [hg]; exact hq
  have hf := ht_free_of_eq ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x n g h hn' hg' htk
    rw [hn] at hn'; rw [hg] at hg'; rw [ht] at htk
    exact (hi.cache x n g h hn' hg' htk).mono hgm hf
  · intro d a q cv' y' h1 h2 g h hg' htk hh
    rw [hp] at h1 h2; rw [hg] at hg'; rw [ht] at htk
    have hd1 : d + 1 < w.path.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp h2).1
      simpa using this
    by_cases hlt : d + 1 < w.path.length
    · rw [List.getElem?_append_left (by omega)] at h1
      rw [List.getElem?_append_left hlt] at h2
      exact (hi.path d a q cv' y' h1 h2 g h hg' htk hh).mono hgm
    · have hd : d + 1 = w.path.length := by omega
      rw [List.getElem?_append_left (by omega)] at h1
      rw [List.getElem?_append_right (by omega), hd, Nat.sub_self] at h2
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h2
      obtain ⟨⟨rfl⟩, rfl⟩ := h2
      have hgl : w.path.getLast? = some (a, q) := by
        rw [List.getLast?_eq_getElem?]
        have : w.path.length - 1 = d := by omega
        rw [this]; exact h1
      exact ((hlast a q hgl).2 g h hg' htk hh).mono hgm
  · intro d a q h1 h2
    rw [hp] at h1 h2; rw [hg]
    simp only [List.length_append, List.length_singleton] at h2
    by_cases hlt : d + 1 < w.path.length
    · rw [List.getElem?_append_left (by omega)] at h1
      exact hi.pathGh d a q h1 hlt
    · have hd : d + 1 = w.path.length := by omega
      rw [List.getElem?_append_left (by omega)] at h1
      have hgl : w.path.getLast? = some (a, q) := by
        rw [List.getLast?_eq_getElem?]
        have : w.path.length - 1 = d := by omega
        rw [this]; exact h1
      exact (hlast a q hgl).1
  · rw [ht, htop]; exact hi.rootFree
  · intro y hy'
    rw [ht] at hy'
    exact hi.takenAbove y hy'
  · intro d a q h1
    rw [hp] at h1
    by_cases hlt : d + 1 < w.path.length
    · rw [List.getElem?_append_left hlt] at h1
      exact hi.pathSome d a q h1
    · have hd : d + 1 = w.path.length := by
        have := (List.getElem?_eq_some_iff.mp h1).1
        simp at this; omega
      rw [List.getElem?_append_right (by omega), hd, Nat.sub_self] at h1
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at h1
      rw [← h1.1]; simp

end SIS.Tree
