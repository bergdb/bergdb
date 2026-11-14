/-
The take-back's (C) and the node facts through a bitmap of the delete (bergdb
024-12, TP4; `J2N`, TakeDeadCollapse.lean). A bitmap that deletes compare value
cv in node x (`appendDeleteKlong` with room: a bitmap added, or the
transaction's own bitmap set in place, `BitmapOf`) keeps x's key klongs, its
klongs before t and its first time; a key klong of x to a node at or above B
that is no value keeps a live klong, and in a leaf stays the last live klong of
its compare value, when cv's live pointer is below B or a value
(`deadLiveK_bitmap`). One node changed so: `j2_change_one`.
-/
import SIS.Tree.TakeDeadMerge
import SIS.Tree.WriterGetUpW

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (C) at one node. -/
def DeadLiveK (n : KNode) (t : Time) (B : NodeId) (vals : List NodeId) : Prop :=
  ∀ (i : Nat) (cv : Nat) (y : NodeId), n.ks[i]? = some (Klong.key cv y) → B ≤ y → y ∉ vals →
    (∃ c, (c, y) ∈ n.liveAt t) ∧ (n.leaf = true → LastLive n.ks n.lastBitmap i cv)

theorem deadLiveK_of_N (N : NodeId → Option KNode) (t : Time) (B : NodeId) (vals : List NodeId)
    (hD : DeadLiveN N t B vals) (q : NodeId) (qn : KNode) (hq : N q = some qn) :
    DeadLiveK qn t B vals :=
  fun i cv y hi hB hv => hD q qn hq i cv y hi hB hv

/-- A klong that is the last live one of its compare value is live. -/
theorem liveAt_of_lastLive (n : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (i c : Nat) (y : NodeId) (hk : n.ks[i]? = some (Klong.key c y))
    (hl : LastLive n.ks n.lastBitmap i c) : (c, y) ∈ n.liveAt t := by
  rw [KNode.liveAt_of_times n t ht]
  apply mem_of_lookup_nodup
  rw [KNode.live_lookup]
  exact keyLookup_of_last _ _ _ i y hk hl

/-! ## The bitmap's node -/

/-- n' is n with a bitmap deleting cv at t: added, or the transaction's own last
bitmap set in place. -/
def BitmapOf (n n' : KNode) (t : Time) (cv : Nat) : Prop :=
  n' = n.add t (.del (bitsUnion n.lastBitmap (n.bitsOf cv))) ∨
  ∃ pre old, n.ks = pre ++ [.del old] ∧ n.lastTime = some t ∧
    n' = n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))

theorem getElem_append_nokey (ks0 s' : List Klong) (i c : Nat) (y : NodeId)
    (h : (ks0 ++ s')[i]? = some (Klong.key c y)) (hs : ∀ c' y', Klong.key c' y' ∉ s') :
    ks0[i]? = some (Klong.key c y) := by
  rcases Nat.lt_or_ge i ks0.length with hi | hi
  · rw [List.getElem?_append_left hi] at h; exact h
  · rw [List.getElem?_append_right hi] at h
    exact absurd (List.mem_of_getElem? h) (hs c y)

theorem bitmapOf_key (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv)
    (i c : Nat) (y : NodeId) (h : n'.ks[i]? = some (Klong.key c y)) :
    n.ks[i]? = some (Klong.key c y) := by
  rcases hb with rfl | ⟨pre, old, hpre, _, rfl⟩
  · rcases KNode.add_ks n t (.del (bitsUnion n.lastBitmap (n.bitsOf cv))) with he | he <;> rw [he] at h
    · exact getElem_append_nokey _ _ i c y h (by simp)
    · exact getElem_append_nokey _ _ i c y h (by simp)
  · rw [KNode.setAt_last_delete_ks n pre old _ hpre] at h
    have := getElem_append_nokey _ _ i c y h (by simp)
    rw [hpre]
    have hi : i < pre.length := (List.getElem?_eq_some_iff.mp this).1
    rw [List.getElem?_append_left hi]; exact this

theorem bitmapOf_key_fwd (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv)
    (i c : Nat) (y : NodeId) (h : n.ks[i]? = some (Klong.key c y)) :
    n'.ks[i]? = some (Klong.key c y) := by
  have hi : i < n.ks.length := (List.getElem?_eq_some_iff.mp h).1
  rcases hb with rfl | ⟨pre, old, hpre, _, rfl⟩
  · rcases KNode.add_ks n t (.del (bitsUnion n.lastBitmap (n.bitsOf cv))) with he | he <;>
      rw [he, List.getElem?_append_left hi] <;> exact h
  · rw [KNode.setAt_last_delete_ks n pre old _ hpre]
    rw [hpre] at h hi
    have hi' : i < pre.length := by
      rcases Nat.lt_or_ge i pre.length with h1 | h1
      · exact h1
      · rw [List.getElem?_append_right h1] at h
        have : i - pre.length = 0 := by simp at hi; omega
        rw [this] at h; simp at h
    rw [List.getElem?_append_left hi'] at h ⊢; exact h

theorem bitmapOf_lastBitmap (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv) :
    n'.lastBitmap = bitsUnion n.lastBitmap (n.bitsOf cv) := by
  rcases hb with rfl | ⟨pre, old, hpre, _, rfl⟩
  · exact KNode.add_delete_lastBitmap _ _ _
  · change lastBitmapOf _ = _
    rw [KNode.setAt_last_delete_ks n pre old _ hpre, lastBitmapOf_append_delete]

theorem bitmapOf_leaf (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv) :
    n'.leaf = n.leaf := by
  rcases hb with rfl | ⟨_, _, _, _, rfl⟩
  · exact KNode.add_leaf _ _ _
  · rfl

/-- The bitmap set in place agrees with n up to its last time klong. -/
theorem bitmapOf_set_agree (n : KNode) (t : Time) (cv : Nat) (pre : List Klong) (old : List Nat)
    (hpre : n.ks = pre ++ [.del old]) (ti : Nat) (hk : n.ks[ti]? = some (.time t)) :
    ∀ i, i ≤ ti → (n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks[i]? =
      n.ks[i]? := by
  intro i hi
  have hne : ti ≠ n.ks.length - 1 := by
    intro he
    rw [hpre] at hk he
    simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel] at he
    rw [he, List.getElem?_append_right (Nat.le_refl _)] at hk
    simp at hk
  have htl : ti < n.ks.length := (List.getElem?_eq_some_iff.mp hk).1
  simp only [KNode.setAt, KNode.size]
  rw [List.getElem?_set_ne (by omega)]

theorem bitmapOf_prefix (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv) (hpos : 0 < t) :
    prefixAt n'.ks (t - 1) = prefixAt n.ks (t - 1) := by
  rcases hb with rfl | ⟨pre, old, hpre, hlt, rfl⟩
  · exact KNode.prefixAt_add n t _ hpos
  · obtain ⟨ti, _, hk⟩ := KNode.lastTime_anchor n t hlt
    exact prefixAt_agree n.ks _ t ti hpos hk (bitmapOf_set_agree n t cv pre old hpre ti hk)

theorem bitmapOf_firstTime (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv)
    (s : Time) (hs : n.firstTime = some s) : n'.firstTime = some s := by
  rcases hb with rfl | ⟨pre, old, hpre, hlt, rfl⟩
  · exact KNode.firstTime_add_some n t _ s hs
  · obtain ⟨ti, _, hk⟩ := KNode.lastTime_anchor n t hlt
    rw [KNode.firstTime_agree n _ ti t hk (bitmapOf_set_agree n t cv pre old hpre ti hk)]
    exact hs

theorem bitmapOf_lastLive (n n' : KNode) (t : Time) (cv : Nat) (hb : BitmapOf n n' t cv)
    (i c : Nat) (hl : LastLive n.ks n.lastBitmap i c) (hc : c ≠ cv) :
    LastLive n'.ks n'.lastBitmap i c := by
  obtain ⟨⟨y, hy⟩, hni, hlater⟩ := hl
  rw [bitmapOf_lastBitmap n n' t cv hb]
  refine ⟨⟨y, bitmapOf_key_fwd n n' t cv hb i c y hy⟩, ?_, fun j y' hij hj => ?_⟩
  · rw [mem_bitsUnion_iff]
    rintro (h | h)
    · exact hni h
    · exact KNode.not_mem_bitsOf_of_key_ne n c cv y i (List.mem_zipIdx_iff_getElem?.mpr hy) hc h
  · rw [mem_bitsUnion_iff]
    exact Or.inl (hlater j y' hij (bitmapOf_key n n' t cv hb j c y' hj))

/-- (C) at a node through a bitmap deleting cv, when cv's live pointer is below
B or a value. -/
theorem deadLiveK_bitmap (n n' : KNode) (t : Time) (cv : Nat) (B : NodeId) (vals : List NodeId)
    (hb : BitmapOf n n' t cv) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hD : DeadLiveK n t B vals) (hcv : ∀ y, (cv, y) ∈ n.liveAt t → y < B ∨ y ∈ vals)
    (hlive : ∀ c z, (c, z) ∈ n'.liveAt t ↔ (c, z) ∈ n.liveAt t ∧ c ≠ cv) :
    DeadLiveK n' t B vals := by
  intro i c' y hi hB hv
  have hi0 := bitmapOf_key n n' t cv hb i c' y hi
  obtain ⟨⟨c, hc⟩, hleaf⟩ := hD i c' y hi0 hB hv
  have hccv : c ≠ cv := by
    intro he
    rw [he] at hc
    rcases hcv y hc with h | h
    · omega
    · exact hv h
  refine ⟨⟨c, (hlive c y).mpr ⟨hc, hccv⟩⟩, fun hl => ?_⟩
  rw [bitmapOf_leaf n n' t cv hb] at hl
  have hLL := hleaf hl
  have hc'cv : c' ≠ cv := by
    intro he
    rw [he] at hLL hi0
    have := liveAt_of_lastLive n t ht i cv y hi0 hLL
    rcases hcv y this with h | h
    · omega
    · exact hv h
  exact bitmapOf_lastLive n n' t cv hb i c' hLL hc'cv

/-! ## One node changed -/

/-- `J2N` after one node x changed, with its klongs before t and first time
kept and (C) at it; what the tree reached is reached after or is no node, and x
with a klong of t is reached after. -/
theorem j2_change_one (N N' : NodeId → Option KNode) (t : Time) (r r' B : NodeId)
    (vals : List NodeId) (x : NodeId) (n n' : KNode) (hJ : J2N N t r B vals)
    (hx : N x = some n) (hx' : N' x = some n') (hother : ∀ z, z ≠ x → N' z = N z)
    (hpre : prefixAt n'.ks (t - 1) = prefixAt n.ks (t - 1))
    (hft : ∀ s, n.firstTime = some s → n'.firstTime = some s) (hDK : DeadLiveK n' t B vals)
    (hreach : ∀ u, TReach N t r u → TReach N' t r' u ∨ N u = none)
    (hxR : Klong.time t ∈ n'.ks → TReach N' t r' x) : J2N N' t r' B vals := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u un hu hm
    by_cases hux : u = x
    · rw [hux, hx'] at hu; cases hu; rw [hux]; exact hxR hm
    · rw [hother u hux] at hu
      rcases hreach u (hTt u un hu hm) with h | h
      · exact h
      · rw [h] at hu; cases hu
  · intro u un hu
    by_cases hux : u = x
    · rw [hux, hx'] at hu; cases hu; exact hDK
    · rw [hother u hux] at hu; exact hD u un hu
  · intro u un hu cv y hk
    by_cases hux : u = x
    · rw [hux, hx'] at hu; cases hu
      rw [hpre] at hk; exact hO x n hx cv y hk
    · rw [hother u hux] at hu; exact hO u un hu cv y hk
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux, hx'] at hu; cases hu
      obtain ⟨s, hs, hf⟩ := hS x n hx (by rw [← hux]; exact huB)
      exact ⟨s, hs, hft s hf⟩
    · rw [hother u hux] at hu; exact hS u un hu huB
  · intro u un hu huB
    by_cases hux : u = x
    · rw [hux, hx'] at hu; cases hu
      exact hft t (hM x n hx (by rw [← hux]; exact huB))
    · rw [hother u hux] at hu; exact hM u un hu huB
  · intro y hy
    by_cases hyx : y = x
    · rw [hyx] at hy; rw [hV x hy] at hx; cases hx
    · rw [hother y hyx]; exact hV y hy

/-! ## The bitmap at the writer's level -/

set_option linter.unusedSimpArgs false in
/-- `writerWP_appendDeleteKlong_room_frame` with x's node after exactly a bitmap
of cv (`BitmapOf`). -/
theorem writerWP_appendDeleteKlong_room_exact (x : NodeId) (depth cv : Nat) (n : KNode) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hw : klongsWf n.ks = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hroom : n.size + 1 < c.p.M)
    (hdead1 : deadOver c.p (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false)
    (hdead2 : deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w'.next = w.next ∧ w'.madeFor = w.madeFor ∧
      ∃ n', w'.nodes = upsert w.nodes x n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
        (∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') ∧
        BitmapOf n n' c.i cv) := by
  have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
      simpa using hne
    cases hgl : n.ks.getLast? with
    | none =>
      simp only [hno, hroom', hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure, hgl]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
        KNode.add_times n c.i _ (fun s h => by cases h) hnt, fun c' => n.add_delete_live_lookup c.i cv c', Or.inl rfl⟩
    | some k =>
      cases k with
      | del old =>
        obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hgl
        cases hlt : (n.lastTime == some c.i)
        · simp only [hno, hroom', hdead2, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
            KNode.add_times n c.i _ (fun s h => by cases h) hnt,
            fun c' => n.add_delete_live_lookup c.i cv c', Or.inl rfl⟩
        · simp only [hno, hdead1, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_true,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.setAt_leaf _ _ _, KNode.setAt_delete_wf n cv old hw hgl,
            KNode.setAt_last_del_times n c.i old _ hgl hnt,
            fun c' => n.setAt_delete_live_lookup cv c' old hgl,
            Or.inr ⟨pre, old, hpre, by simpa using hlt, rfl⟩⟩
      | _ =>
        simp only [hno, hroom', hdead2, hgl, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
          KNode.add_times n c.i _ (fun s h => by cases h) hnt,
          fun c' => n.add_delete_live_lookup c.i cv c', Or.inl rfl⟩

end SIS.Tree
