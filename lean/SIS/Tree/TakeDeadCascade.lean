/-
The take-back's (C) and the node facts through a cascade of splits (bergdb
024-12, TP4; `J2N`, TakeDeadCollapse.lean), at node-map level, against the node
shapes agreed with latest for `writerWP_appendKlongs_chainGRV`: every node the
cascade changed or made (`CascadeShapeJ`) is a chain node left behind
(`toPrev`), a last version or a split's half (`ShadowShaped`: a time klong of t,
then key klongs, a klong with a later one of its compare value naming a node
below B or a value), or the top with its klongs put in (key klongs added whose
compare values' old live pointers are below B or values, or the in-place
repoint of a segment leaf's klong to a segment root the transaction made):
`j2rest_cascade`.
-/
import SIS.Tree.TakeDeadUp
import SIS.Tree.TakeCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## A last version -/

/-- A time klong of t, then key klongs of distinct compare values. -/
def LastShaped (t : Time) (n : KNode) : Prop :=
  ∃ l : List (Nat × NodeId), n.ks = newKlongs t l ∧ (l.map Prod.fst).Nodup

theorem lastShaped_facts (t : Time) (n : KNode) (h : LastShaped t n) (hpos : 0 < t) (B : NodeId)
    (vals : List NodeId) :
    DeadLiveK n t B vals ∧ prefixAt n.ks (t - 1) = [] ∧ n.firstTime = some t := by
  obtain ⟨l, hks, hnd⟩ := h
  have hn : n = ⟨n.leaf, newKlongs t l⟩ := by cases n; simp only at hks; rw [hks]
  refine ⟨?_, by rw [hks]; exact newKlongs_prefix t l hpos, by rw [hn]; exact newKlongs_firstTime _ t l⟩
  intro i cv y hi _ _
  rw [hn] at hi ⊢
  have hkl : (cv, y) ∈ l := key_mem_newKlongs t l cv y (List.mem_of_getElem? hi)
  refine ⟨⟨cv, (mrg_newKlongs_liveAt_iff _ t l hnd cv y).mpr hkl⟩, fun _ => ?_⟩
  rw [newKlongs_lastBitmap]
  exact newKlongs_lastLive t l hnd i cv y hi

/-- A time klong of t, then key klongs only, a klong with a later klong of its
compare value naming a node below B or a value (a split's half, where the
klongs put in follow the node's last version). -/
def ShadowShaped (t : Time) (B : NodeId) (vals : List NodeId) (n : KNode) : Prop :=
  (∃ ks', n.ks = .time t :: ks' ∧ ∀ k ∈ ks', ∃ cv y, k = Klong.key cv y) ∧
  ∀ (a b cv : Nat) (y y' : NodeId), a < b → n.ks[a]? = some (Klong.key cv y) →
    n.ks[b]? = some (Klong.key cv y') → y < B ∨ y ∈ vals

theorem shadowShaped_facts (t : Time) (B : NodeId) (vals : List NodeId) (n : KNode)
    (h : ShadowShaped t B vals n) (hpos : 0 < t) :
    DeadLiveK n t B vals ∧ prefixAt n.ks (t - 1) = [] ∧ n.firstTime = some t := by
  obtain ⟨⟨ks', hks, hkey⟩, hsh⟩ := h
  have hpre : prefixAt n.ks (t - 1) = [] := by
    rw [hks]; unfold prefixAt
    simp only [List.takeWhile_cons]
    have : decide (t ≤ t - 1) = false := by simp; omega
    simp [this]
  have hft : n.firstTime = some t := by
    unfold KNode.firstTime; rw [hks]; simp
  have hbm : n.lastBitmap = [] := by
    unfold KNode.lastBitmap
    rw [hks, show Klong.time t :: ks' = [] ++ (Klong.time t :: ks') from rfl,
      lastBitmapOf_append_nodel [] _ (fun b hb => ?_)]
    · rfl
    · rcases List.mem_cons.mp hb with h | h
      · cases h
      · obtain ⟨cv, y, he⟩ := hkey _ h; cases he
  have ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t := by
    intro s hs
    rw [hks] at hs
    rcases List.mem_cons.mp hs with h | h
    · cases h; exact Nat.le_refl _
    · obtain ⟨cv, y, he⟩ := hkey _ h; cases he
  refine ⟨fun i cv y hi hB hv => ?_, hpre, hft⟩
  have hLL : LastLive n.ks n.lastBitmap i cv := by
    rw [hbm]
    refine ⟨⟨y, hi⟩, List.not_mem_nil, fun j y' hij hj => ?_⟩
    rcases hsh i j cv y y' hij hi hj with h | h
    · omega
    · exact absurd h hv
  exact ⟨⟨cv, liveAt_of_lastLive n t ht i cv y hi hLL⟩, fun _ => hLL⟩

theorem shadowShaped_of_lastShaped (t : Time) (B : NodeId) (vals : List NodeId) (n : KNode)
    (h : LastShaped t n) : ShadowShaped t B vals n := by
  obtain ⟨l, hks, hnd⟩ := h
  refine ⟨⟨_, hks, fun k hk => ?_⟩, fun a b cv y y' hab ha hb => ?_⟩
  · obtain ⟨q, _, he⟩ := List.mem_map.mp hk
    exact ⟨q.1, q.2, he.symm⟩
  · exfalso
    have hn : n = ⟨n.leaf, newKlongs t l⟩ := by cases n; simp only at hks; rw [hks]
    rw [hn] at ha hb
    have hLL := newKlongs_lastLive t l hnd a cv y ha
    exact List.not_mem_nil (hLL.2.2 b y' hab hb)

/-! ## Key klongs added -/

/-- (C) at a node with a key klong of k added, when k's old live pointer is
below B or a value. -/
theorem deadLiveK_addKey (n : KNode) (t : Time) (B : NodeId) (vals : List NodeId) (k : Nat)
    (y : NodeId) (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hD : DeadLiveK n t B vals) (hold : ∀ z, (k, z) ∈ n.liveAt t → z < B ∨ z ∈ vals) :
    DeadLiveK (n.add t (.key k y)) t B vals := by
  obtain ⟨more, hks, hnd, hmore, hlastk⟩ : ∃ more, (n.add t (.key k y)).ks = n.ks ++ more ∧
      (∀ b, Klong.del b ∉ more) ∧ (∀ c z, Klong.key c z ∈ more → c = k ∧ z = y) ∧
      ∀ i', n.ks.length ≤ i' → ∀ c z, more[i' - n.ks.length]? = some (Klong.key c z) →
        ∀ j', i' < j' → more[j' - n.ks.length]? = none := by
    rcases KNode.add_key_ks n t k y with h | h
    · refine ⟨[.time t, .key k y], h, by simp, by simp, fun i' hi' c z hm j' hj' => ?_⟩
      have hlt : i' - n.ks.length < 2 := (List.getElem?_eq_some_iff.mp hm).1
      have hne : i' - n.ks.length ≠ 0 := by
        intro h0; rw [h0] at hm; simp at hm
      simp only [List.getElem?_eq_none_iff, List.length_cons, List.length_nil]
      omega
    · refine ⟨[.key k y], h, by simp, by simp, fun i' hi' c z hm j' hj' => ?_⟩
      have hlt : i' - n.ks.length < 1 := (List.getElem?_eq_some_iff.mp hm).1
      simp only [List.getElem?_eq_none_iff, List.length_cons, List.length_nil]
      omega
  have hbm : (n.add t (.key k y)).lastBitmap = n.lastBitmap := by
    unfold KNode.lastBitmap
    rw [hks]
    exact lastBitmapOf_append_nodel n.ks more hnd
  intro i cv z hi hB hv
  rw [hks] at hi
  rcases Nat.lt_or_ge i n.ks.length with hil | hil
  · rw [List.getElem?_append_left hil] at hi
    obtain ⟨⟨c0, hc0⟩, hL0⟩ := hD i cv z hi hB hv
    have hck0 : c0 ≠ k := by
      intro h
      rw [h] at hc0
      rcases hold z hc0 with h' | h'
      · omega
      · exact hv h'
    refine ⟨⟨c0, KNode.add_liveAt_keep n k y t hw ht c0 z hc0 hck0⟩, fun hl => ?_⟩
    have hLi := hL0 (by rw [← KNode.add_leaf n t (.key k y)]; exact hl)
    have hcvk : cv ≠ k := by
      intro h
      rw [h] at hi hLi
      have hci := liveAt_of_lastLive n t ht i k z hi hLi
      rcases hold z hci with h' | h'
      · omega
      · exact hv h'
    rw [hbm, hks]
    obtain ⟨⟨y0, hy0⟩, hid, hilater⟩ := hLi
    refine ⟨⟨y0, by rw [List.getElem?_append_left hil]; exact hy0⟩, hid, fun j' y' hij' hj' => ?_⟩
    rcases Nat.lt_or_ge j' n.ks.length with hjl | hjl
    · rw [List.getElem?_append_left hjl] at hj'
      exact hilater j' y' hij' hj'
    · rw [List.getElem?_append_right hjl] at hj'
      exact absurd (hmore cv y' (List.mem_of_getElem? hj')).1 hcvk
  · rw [List.getElem?_append_right hil] at hi
    have hm := hmore cv z (List.mem_of_getElem? hi)
    obtain ⟨hcv, hzy⟩ := hm
    have hi0 := hi
    rw [hcv, hzy] at hi0
    rw [hcv, hzy]
    refine ⟨⟨k, KNode.add_liveAt_new n k y t hw ht⟩, fun _ => ?_⟩
    rw [hbm, hks]
    refine ⟨⟨y, by rw [List.getElem?_append_right hil]; exact hi0⟩, ?_, ?_⟩
    · intro hid
      have := KNode.wf_bitmap_bounds n hw i hid
      simp only [KNode.size] at this
      omega
    · intro j' y' hij' hj'
      exfalso
      rw [List.getElem?_append_right (by omega)] at hj'
      rw [hlastk i hil cv z hi j' hij'] at hj'
      cases hj'

/-- Key klongs added, of distinct compare values each with its old live pointer
below B or a value: (C) kept, and the klongs before t, the first time, the
leaf flag, well-formedness and the times. -/
theorem addKeys_facts (t : Time) (B : NodeId) (vals : List NodeId) (hpos : 0 < t) :
    ∀ (ins : List (Nat × NodeId)) (n : KNode), klongsWf n.ks = true →
      (∀ s, Klong.time s ∈ n.ks → s ≤ t) → DeadLiveK n t B vals →
      (ins.map Prod.fst).Nodup →
      (∀ q ∈ ins, ∀ z, (q.1, z) ∈ n.liveAt t → z < B ∨ z ∈ vals) →
      DeadLiveK (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n) t B vals ∧
      prefixAt (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).ks (t - 1) = prefixAt n.ks (t - 1) ∧
      (∀ s, n.firstTime = some s → (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).firstTime = some s) := by
  intro ins
  induction ins with
  | nil => intro n _ _ hD _ _; exact ⟨hD, rfl, fun _ h => h⟩
  | cons q ins ih =>
    intro n hw ht hD hnd hold
    obtain ⟨cv, y⟩ := q
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    have hD1 := deadLiveK_addKey n t B vals cv y hw ht hD (hold (cv, y) List.mem_cons_self)
    have hw1 := KNode.add_key_wf n t cv y hw
    have ht1 := KNode.add_times n t (.key cv y) (fun s h => by cases h) ht
    have hold1 : ∀ q ∈ ins, ∀ z, (q.1, z) ∈ (n.add t (.key cv y)).liveAt t → z < B ∨ z ∈ vals := by
      intro q hq z hz
      have hqc : q.1 ≠ cv := fun he => hnd.1 (by rw [← he]; exact List.mem_map_of_mem hq)
      rw [KNode.liveAt_of_times _ t ht1] at hz
      have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) q.1 z hz
      rw [KNode.add_key_live_lookup_of_wf n t cv q.1 y hw] at hl
      have hb : (cv == q.1) = false := by simpa using Ne.symm hqc
      rw [hb] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      have hz0 : (q.1, z) ∈ n.liveAt t := by
        rw [KNode.liveAt_of_times n t ht]; exact bk_mem_of_lookup _ _ _ hl
      exact hold q (List.mem_cons_of_mem _ hq) z hz0
    obtain ⟨hD2, hp2, hf2⟩ := ih _ hw1 ht1 hD1 hnd.2 hold1
    refine ⟨hD2, by rw [hp2]; exact KNode.prefixAt_add n t _ hpos, fun s hs => hf2 s ?_⟩
    exact KNode.firstTime_add_some n t _ s hs

/-! ## A segment leaf's klong repointed -/

/-- (C) at a segment leaf whose one klong to x, at or above B and no value, is
pointed to y. -/
theorem deadLiveK_repoint (N : NodeId → Option KNode) (t : Time) (r B : NodeId) (vals : List NodeId)
    (q x y : NodeId) (qn : KNode) (k j : Nat) (hT : TreeOK N t r) (hD : DeadLiveK qn t B vals)
    (hq : TReach N t r q) (hqn : N q = some qn) (hql : qn.leaf = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hj : qn.linkIndex x k = some j) (hk : (k, x) ∈ qn.liveAt t) (hBx : B ≤ x) (hxv : x ∉ vals) :
    DeadLiveK (qn.repoint j y) t B vals := by
  have hjk : qn.ks[j]? = some (.key k x) := kd_linkIndex_some qn x k j hj
  have hLj : LastLive qn.ks qn.lastBitmap j k := (hD j k x hjk hBx hxv).2 hql
  have hrp : qn.repoint j y = qn.setAt j (.key k y) := by
    unfold KNode.repoint; rw [hjk]
  have hbm : (qn.repoint j y).lastBitmap = qn.lastBitmap :=
    KNode.lastBitmap_of_shapeOf (KNode.repoint_shapeOf qn j y)
  intro i cv z hi hB hv
  rw [hrp] at hi
  simp only [KNode.setAt] at hi
  by_cases hij : i = j
  · subst hij
    have hjl : i < qn.ks.length := (List.getElem?_eq_some_iff.mp hjk).1
    rw [List.getElem?_set_self hjl] at hi
    simp only [Option.some.injEq, Klong.key.injEq] at hi
    rw [← hi.1, ← hi.2]
    refine ⟨⟨k, liveAt_repoint_new qn x y k i t hj hqt⟩, fun _ => ?_⟩
    rw [hbm, hrp]
    exact lastLive_set_self qn.ks qn.lastBitmap i k y hLj
  · rw [List.getElem?_set_ne (Ne.symm hij)] at hi
    obtain ⟨⟨c0, hc0⟩, hL0⟩ := hD i cv z hi hB hv
    have hzx : z ≠ x := by
      intro hzx
      rw [hzx] at hi hc0
      have hLi := hL0 hql
      by_cases hck : cv = k
      · rw [hck] at hLi
        obtain ⟨_, hid, hilater⟩ := hLi
        obtain ⟨_, hjd, hjlater⟩ := hLj
        rcases Nat.lt_or_ge i j with h | h
        · exact hjd (hilater j x h hjk)
        · exact hid (hjlater i x (by omega) (by rw [hi, hck]))
      · have hci := liveAt_of_lastLive qn t hqt i cv x hi hLi
        exact hck (hT.oneLink q cv q k x hq hq ⟨qn, hqn, hci⟩ ⟨qn, hqn, hk⟩).2
    refine ⟨⟨c0, ?_⟩, fun hl => ?_⟩
    · refine liveAt_repoint_keep qn x y k j t hj hqt c0 z hc0 (fun hck => hzx ?_)
      rw [hck] at hc0
      exact (KNode.liveAt_fun qn t k x z hk hc0).symm
    · rw [hbm, hrp]
      exact lastLive_set_other qn.ks qn.lastBitmap i cv j k y (hL0 (by rw [← bk_repoint_leaf]; exact hl)) hLj hij

/-! ## (C) and the node facts after a cascade, at node-map level -/

end SIS.Tree
