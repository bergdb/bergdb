/-
LE-b at the writer (bergdb 024-22, `OpTreeOK`; `emptyKeyNext`): the empty key
of an inner node takes the pointer of the next live klong, whose compare value
is deleted. With room and no compaction it keeps the writer's tree
(`writerWP_emptyKeyNext_tree`): the next child is still named once, the empty
key's old child is left behind.
-/
import SIS.Tree.WriterTreeCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- LE-b's choice of the next klong, one klong at a time. -/
def lebStep (del0 : List Nat) (best : Option (Nat × Nat × NodeId)) (q : Klong × Nat) :
    Option (Nat × Nat × NodeId) :=
  match q.1 with
  | .key cv y =>
    if del0.contains q.2 then best else
      match best with
      | none => some (q.2, cv, y)
      | some (_, jcv, _) => if cv ≤ jcv then some (q.2, cv, y) else best
  | _ => best

def LebOK (ks : List Klong) (del0 : List Nat) (best : Option (Nat × Nat × NodeId)) : Prop :=
  ∀ i cv y, best = some (i, cv, y) → ks[i]? = some (.key cv y) ∧ i ∉ del0 ∧
    ∀ j y', i < j → ks[j]? = some (.key cv y') → j ∈ del0

theorem lebOK_step (ks : List Klong) (del0 : List Nat) (best : Option (Nat × Nat × NodeId))
    (k : Klong) (hb : LebOK ks del0 best) : LebOK (ks ++ [k]) del0 (lebStep del0 best (k, ks.length)) := by
  have keep : ∀ i cv y, best = some (i, cv, y) → (∀ y', k = .key cv y' → ks.length ∈ del0) →
      (ks ++ [k])[i]? = some (.key cv y) ∧ i ∉ del0 ∧
        ∀ j y', i < j → (ks ++ [k])[j]? = some (.key cv y') → j ∈ del0 := by
    intro i cv y hbest hk
    obtain ⟨hy, hd, hl⟩ := hb i cv y hbest
    have hi : i < ks.length := by rw [List.getElem?_eq_some_iff] at hy; exact hy.1
    refine ⟨by rw [getElem?_append_single_lt _ _ _ hi]; exact hy, hd, ?_⟩
    intro j y' hij hj
    rcases Nat.lt_trichotomy j ks.length with h1 | h1 | h1
    · rw [getElem?_append_single_lt _ _ _ h1] at hj; exact hl j y' hij hj
    · subst h1; rw [getElem?_append_single_eq] at hj
      simp only [Option.some.injEq] at hj
      exact hk y' hj
    · rw [getElem?_append_single_gt _ _ _ h1] at hj; cases hj
  have fresh : ∀ cv y, k = .key cv y → ks.length ∉ del0 →
      (ks ++ [k])[ks.length]? = some (.key cv y) ∧ ks.length ∉ del0 ∧
        ∀ j y', ks.length < j → (ks ++ [k])[j]? = some (.key cv y') → j ∈ del0 := by
    intro cv y hk hd
    refine ⟨by rw [getElem?_append_single_eq, hk], hd, ?_⟩
    intro j y' hij hj
    rw [getElem?_append_single_gt _ _ _ hij] at hj; cases hj
  intro i cv y h
  unfold lebStep at h
  cases k with
  | time t => exact keep i cv y h (fun _ he => by cases he)
  | del b => exact keep i cv y h (fun _ he => by cases he)
  | key c0 y0 =>
    simp only at h
    by_cases hd : del0.contains ks.length = true
    · simp only [hd, ↓reduceIte] at h
      exact keep i cv y h (fun _ _ => by simpa using hd)
    · have hd' : ks.length ∉ del0 := by simpa using hd
      simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
      cases best with
      | none =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact fresh _ _ rfl hd'
      | some b =>
        rcases b with ⟨i0, jcv, jy⟩
        simp only at h
        by_cases hle : c0 ≤ jcv
        · simp only [hle, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          exact fresh _ _ rfl hd'
        · simp only [hle, ↓reduceIte] at h
          refine keep i cv y h (fun y' he => ?_)
          exfalso
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          simp only [Klong.key.injEq] at he
          omega

theorem lebOK_fold (del0 : List Nat) (ks : List Klong) :
    LebOK ks del0 (ks.zipIdx.foldl (lebStep del0) none) := by
  have key : ∀ rs : List Klong, LebOK rs.reverse del0 (rs.reverse.zipIdx.foldl (lebStep del0) none) := by
    intro rs
    induction rs with
    | nil => intro i cv y h; cases h
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact lebOK_step rs.reverse del0 _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- The key-lookup fold with one key klong's pointer changed: the same result,
or the new pointer. -/
theorem keyLookupFold_set_cv (del : List Nat) (c : Nat) (y : NodeId) :
    ∀ (xs : List (Klong × Nat)) (i : Nat) (c0 old : Nat) (v v' : Option NodeId),
      (v' = v ∨ (v' = some y ∧ c = c0)) →
      (∀ k j, (k, j) ∈ xs → j = i → k = .key c0 old) →
      (xs.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q)).foldl (keyLookupStep del c) v' =
        xs.foldl (keyLookupStep del c) v ∨
      ((xs.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q)).foldl (keyLookupStep del c) v' =
        some y ∧ c = c0) := by
  intro xs
  induction xs with
  | nil => intro i c0 old v v' hv _; simpa using hv
  | cons q qs ih =>
    intro i c0 old v v' hv hi
    rcases q with ⟨k, j⟩
    simp only [List.map_cons, List.foldl_cons]
    apply ih i c0 old _ _ _ (fun k' j' h hj => hi k' j' (List.mem_cons_of_mem _ h) hj)
    by_cases hj : j = i
    · have hk := hi k j List.mem_cons_self hj
      subst hk
      simp only [hj, ↓reduceIte, keyLookupStep]
      split
      · exact hv
      · split
        · rename_i hcc
          exact Or.inr ⟨rfl, (beq_iff_eq.mp hcc).symm⟩
        · exact hv
    · simp only [hj, ↓reduceIte, keyLookupStep]
      cases k with
      | key a z =>
        simp only
        split
        · exact hv
        · split
          · exact Or.inl rfl
          · exact hv
      | time t => exact hv
      | del b => exact hv

/-- A key klong pointed to y in place: a live klong at any time is the node's
or names y. -/
theorem KNode.repoint_liveAt_cv (n : KNode) (i : Nat) (y : NodeId) (t : Time) (c : Nat) (z : NodeId)
    (h : (c, z) ∈ (n.repoint i y).liveAt t) : (c, z) ∈ n.liveAt t ∨ (z = y ∧ n.cv? i = some c) := by
  unfold KNode.repoint at h
  split at h
  · rename_i c0 old hk
    have hn := KNode.liveAt_keys_nodup ({ n with ks := n.ks.set i (.key c0 y) } : KNode) t
    have hl := lookup_of_mem_nodup _ hn c z h
    rw [KNode.liveAt_lookup] at hl
    -- the prefix and the bitmap
    have hp : ∀ b, n.ks[i]? = some b → (fun k => match k with
        | Klong.time x => decide (x ≤ t)
        | _ => true) b = (fun k => match k with
        | Klong.time x => decide (x ≤ t)
        | _ => true) (Klong.key c0 y) := by
      intro b hb; rw [hk] at hb; simp only [Option.some.injEq] at hb; subst hb; rfl
    have hpre : prefixAt (n.ks.set i (.key c0 y)) t = (prefixAt n.ks t).set i (.key c0 y) := by
      unfold prefixAt
      exact takeWhile_set _ n.ks i _ hp
    have hpk : (prefixAt n.ks t)[i]? = some (.key c0 old) ∨ (prefixAt n.ks t)[i]? = none := by
      cases hq : (prefixAt n.ks t)[i]? with
      | none => exact Or.inr rfl
      | some b =>
        left
        have hpf : (prefixAt n.ks t).IsPrefix n.ks := prefixAt_prefix n.ks t
        have := prefix_getElem?_some _ _ hpf i b hq
        rw [hk] at this
        simp only [Option.some.injEq] at this
        rw [← this]
    have hdel : ({ n with ks := n.ks.set i (.key c0 y) } : KNode).delAt t = n.delAt t := by
      unfold KNode.delAt
      simp only
      rw [hpre]
      cases hq : (prefixAt n.ks t)[i]? with
      | none => simp [List.set_eq_of_length_le (by
          rw [List.getElem?_eq_none_iff] at hq; exact hq)]
      | some b =>
        rcases hpk with h1 | h1
        · exact lastBitmapOf_set_key _ i c0 y ⟨old, h1⟩
        · rw [h1] at hq; cases hq
    simp only at hl
    rw [hpre, hdel] at hl
    unfold keyLookup at hl
    have hz : (List.set (prefixAt n.ks t) i (Klong.key c0 y)).zipIdx =
        (prefixAt n.ks t).zipIdx.map (fun q => if q.2 = i then (Klong.key c0 y, q.2) else q) := by
      apply List.ext_getElem
      · simp
      · intro j h1 h2
        simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_set, Nat.zero_add]
        by_cases hji : j = i
        · simp [hji]
        · simp [hji, Ne.symm hji]
    rw [hz] at hl
    have hsrc : ∀ k j, (k, j) ∈ (prefixAt n.ks t).zipIdx → j = i → k = .key c0 old := by
      intro k j hm hj
      subst hj
      have h1 : (prefixAt n.ks t)[j]? = some k := List.mem_zipIdx_iff_getElem?.mp hm
      have hpf : (prefixAt n.ks t).IsPrefix n.ks := prefixAt_prefix n.ks t
      have h2 := prefix_getElem?_some _ _ hpf j k h1
      rw [hk] at h2
      simp only [Option.some.injEq] at h2
      exact h2.symm
    rcases keyLookupFold_set_cv (n.delAt t) c y _ i c0 old none none (Or.inl rfl) hsrc with h1 | h1
    · rw [hl] at h1
      left
      apply mem_of_lookup_nodup _ c z
      rw [KNode.liveAt_lookup]
      exact h1.symm
    · rw [hl] at h1
      simp only [Option.some.injEq] at h1
      refine Or.inr ⟨h1.1, ?_⟩
      rw [h1.2]; simp [KNode.cv?, hk]
  · exact Or.inl h


/-- LE-b's node with room, its choices free: the transaction's own bitmap set
in place or added, the empty key's klong pointed in place or added. -/
def lebNode (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId) : KNode :=
  let union := bitsUnion n.lastBitmap (n.bitsOf jcv)
  let n1 := if htd then n.setAt (n.size - 1) (.del union) else n.add tt (.del union)
  if lip then n1.repoint e jy else n1.add tt (.key 0 jy)


/-- The live klongs of LE-b's node: the empty key names jy, jcv is deleted,
the others are the node's. -/
theorem lebNode_liveAt (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId)
    (hwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ tt)
    (htdh : htd = true → ∃ old, n.ks.getLast? = some (.del old))
    (he : ∃ y0, n.ks[e]? = some (.key 0 y0))
    (hne : bitsUnion n.lastBitmap (n.bitsOf jcv) ≠ n.lastBitmap) :
    ∀ cc z, (cc, z) ∈ (lebNode n tt htd lip e jcv jy).liveAt tt →
      (cc = 0 ∧ z = jy) ∨ ((cc, z) ∈ n.liveAt tt ∧ cc ≠ jcv) := by
  obtain ⟨y0, hey⟩ := he
  have hel : e < n.ks.length := by rw [List.getElem?_eq_some_iff] at hey; exact hey.1
  -- the bitmap step
  have hn1 : ∃ n1 : KNode, (if htd then n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))
      else n.add tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))) = n1 ∧
      klongsWf n1.ks = true ∧ (∀ s, Klong.time s ∈ n1.ks → s ≤ tt) ∧ n1.ks[e]? = some (.key 0 y0) ∧
      ∀ cc z, (cc, z) ∈ n1.liveAt tt → cc ≠ jcv ∧ (cc, z) ∈ n.liveAt tt := by
    cases htd with
    | true =>
      obtain ⟨old, hlast⟩ := htdh rfl
      simp only [↓reduceIte]
      have hen : e ≠ n.size - 1 := by
        intro hh
        rw [List.getLast?_eq_getElem?] at hlast
        simp only [KNode.size] at hh
        rw [← hh, hey] at hlast; cases hlast
      have ht1 := KNode.setAt_last_del_times n tt old (bitsUnion n.lastBitmap (n.bitsOf jcv)) hlast hnt
      refine ⟨_, rfl, KNode.setAt_delete_wf n jcv old hwf hlast, ht1, ?_, ?_⟩
      · simp only [KNode.setAt]; rw [List.getElem?_set_ne (Ne.symm hen)]; exact hey
      · exact fun cc z hm => liveAt_sub_of_lookup n _ tt jcv hnt ht1
          (fun c'' => n.setAt_delete_live_lookup jcv c'' old hlast) cc z hm
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have ht1 := KNode.add_times n tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))
        (fun s h => by cases h) hnt
      refine ⟨_, rfl, KNode.add_delete_wf n tt jcv hwf hne, ht1, ?_, ?_⟩
      · rw [n.add_getElem?_lt tt _ e hel]; exact hey
      · exact fun cc z hm => liveAt_sub_of_lookup n _ tt jcv hnt ht1
          (fun c'' => n.add_delete_live_lookup tt jcv c'') cc z hm
  obtain ⟨n1, hn1e, hw1, ht1, he1, hsub1⟩ := hn1
  intro cc z hm
  unfold lebNode at hm
  simp only at hm
  rw [hn1e] at hm
  cases lip with
  | true =>
    simp only [↓reduceIte] at hm
    rcases KNode.repoint_liveAt_cv n1 e jy tt cc z hm with h | ⟨hz, hc⟩
    · obtain ⟨h1, h2⟩ := hsub1 cc z h
      exact Or.inr ⟨h2, h1⟩
    · simp only [KNode.cv?, he1, Option.some.injEq] at hc
      exact Or.inl ⟨hc.symm, hz⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hm
    rcases KNode.add_key_liveAt_mem n1 tt 0 jy hw1 ht1 cc z hm with ⟨h1, h2⟩ | ⟨_, h⟩
    · exact Or.inl ⟨h1, h2⟩
    · obtain ⟨h1, h2⟩ := hsub1 cc z h
      exact Or.inr ⟨h2, h1⟩

/-- The tree after LE-b at a reached node x: the empty key names the next
child jy, whose compare value jcv is deleted. -/
theorem treeOK_leb_after (p : Params) (base : View BVal) (t : Time) (w : W) (x : NodeId) (n n2 : KNode)
    (jcv : Nat) (jy : NodeId) (hT : TreeOK (wNode p base w) t w.top.rootKey)
    (hx : TReach (wNode p base w) t w.top.rootKey x)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hj : (jcv, jy) ∈ n.liveAt t)
    (hn2 : ∀ cc z, (cc, z) ∈ n2.liveAt t → (cc = 0 ∧ z = jy) ∨ ((cc, z) ∈ n.liveAt t ∧ cc ≠ jcv)) :
    TreeOK (wNode p base { w with nodes := upsert w.nodes x n2 }) t w.top.rootKey := by
  have hwx : wNode p base w x = some n := by simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, hlk]
  apply treeOK_of_node_relink (wNode p base w) _ t w.top.rootKey x n n2 hT hwx
  · simp only [wNode, hxt, Bool.false_eq_true, ↓reduceIte, lookup_upsert]
  · intro y hy; simp only [wNode, lookup_upsert, hy, ↓reduceIte]
  · intro cc z hm
    rcases hn2 cc z hm with ⟨_, hz⟩ | ⟨h, _⟩
    · exact ⟨jcv, by rw [hz]; exact hj⟩
    · exact ⟨cc, h⟩
  · intro cc cc' z h1 h2
    have hjl : TLink (wNode p base w) t x jcv jy := ⟨n, hwx, hj⟩
    rcases hn2 cc z h1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases hn2 cc' z h2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
    · rw [a1, a2]
    · rw [b1] at a2
      exact absurd (hT.oneLink x cc' x jcv jy hx hx ⟨n, hwx, a2⟩ hjl).2 b2
    · rw [b2] at a1
      exact absurd (hT.oneLink x cc x jcv jy hx hx ⟨n, hwx, a1⟩ hjl).2 b1
    · exact (hT.oneLink x cc x cc' z hx hx ⟨n, hwx, a1⟩ ⟨n, hwx, a2⟩).2


theorem need_le_three (b1 b2 b3 : Bool) :
    ((if b1 = true then 0 else 1) + (if b2 = true then 0 else 1)) + (if b3 = true then 0 else 1) ≤ 3 := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp

theorem writerWP_emptyKeyNext_tree (x : NodeId) (depth : Nat) (n : KNode) (c : Ctx) (base : View BVal)
    (w : W) (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hx : TReach (wNode c.p base w) c.i w.top.rootKey x)
    (hlk : w.nodes.lookup x = some n) (hxt : w.taken.contains x = false)
    (hwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hroom : n.size + 3 ≤ c.p.M)
    (hdead : ∀ b1 b2 e jcv jy, deadOver c.p (lebNode n c.i b1 b2 e jcv jy) = false) :
    WriterWP (emptyKeyNext x depth) c w (fun _ w' => TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  unfold emptyKeyNext
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · rename_i e0 j0 jcv jy hE hJ
    have hJ' : n.ks.zipIdx.foldl (lebStep (bitsUnion n.lastBitmap (n.bitsOf 0))) none =
        some (j0, jcv, jy) := hJ
    obtain ⟨hkj, hjd, hjl⟩ := lebOK_fold _ n.ks j0 jcv jy hJ'
    have hb0 : j0 ∉ n.bitsOf 0 := fun h => hjd ((mem_bitsUnion_iff _ _ _).mpr (Or.inr h))
    have hj0 : jcv ≠ 0 := by
      intro h; subst h
      exact hb0 ((n.mem_bitsOf_iff 0 j0).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hkj⟩)
    have hLL : LastLive n.ks n.lastBitmap j0 jcv := by
      refine ⟨⟨jy, hkj⟩, fun h => hjd ((mem_bitsUnion_iff _ _ _).mpr (Or.inl h)), ?_⟩
      intro j y' hij hj
      rcases (mem_bitsUnion_iff _ _ _).mp (hjl j y' hij hj) with h | h
      · exact h
      · obtain ⟨y'', hy''⟩ := (n.mem_bitsOf_iff 0 j).mp h
        rw [List.mem_zipIdx_iff_getElem?.mp hy''] at hj
        simp only [Option.some.injEq, Klong.key.injEq] at hj
        exact absurd hj.1.symm hj0
    have hjlive : (jcv, jy) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]
      apply mem_of_lookup_nodup
      rw [KNode.live_lookup]
      exact keyLookup_of_last _ _ _ j0 jy hkj hLL
    have hne : bitsUnion n.lastBitmap (n.bitsOf jcv) ≠ n.lastBitmap := by
      intro he
      have : j0 ∈ bitsUnion n.lastBitmap (n.bitsOf jcv) := (mem_bitsUnion_iff _ _ _).mpr
        (Or.inr ((n.mem_bitsOf_iff jcv j0).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hkj⟩))
      rw [he] at this
      exact hLL.2.1 this
    have he0 : ∃ y0, n.ks[e0]? = some (.key 0 y0) := by
      have hm : e0 ∈ n.bitsOf 0 := List.mem_of_getLast? hE
      obtain ⟨y0, hy0⟩ := (n.mem_bitsOf_iff 0 e0).mp hm
      exact ⟨y0, List.mem_zipIdx_iff_getElem?.mp hy0⟩
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    apply writerWP_ite_true _ (Nat.le_trans (Nat.add_le_add_left (need_le_three _ _ _) _) hroom)
    apply writerWP_ite_false _ (fun hd => absurd (hd.symm.trans (hdead _ _ e0 jcv jy)) (by decide))
    simp only [note, putNode, writerWP_bind, writerWP_modify]
    apply treeOK_leb_after c.p base c.i w x n _ jcv jy hT hx hlk hxt hjlive
    refine lebNode_liveAt n c.i _ _ e0 jcv jy hwf hnt ?htd he0 hne
    case htd =>
      intro h
      cases hg : n.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
  · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
