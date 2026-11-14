/-
LE-b in the upward delete (bergdb 024-22): the stop node's empty key names the
next child (`writerWP_emptyKeyNext_room_frame`, `lebNode_live_lookup`), and the
tree with the chain dropped and the stop node relinked (`treeOK_dropSubtree_tr`).
-/
import SIS.Tree.WriterGetUpW
import SIS.Tree.RangeLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `treeOK_dropSubtree` with the stop node's links relinked: each live klong of
s after names what a live klong of s before named, by a compare value f maps. -/
theorem treeOK_dropSubtree_tr (L L' : NodeId → Option KNode) (t : Time) (r s y0 : NodeId)
    (cs : Nat) (sn sn' : KNode) (Gone : NodeId → Prop) (f : Nat → Nat) (ht : TreeOK L t r)
    (hs : TReach L t r s) (hsn : L s = some sn) (hcs : (cs, y0) ∈ sn.liveAt t)
    (hsn' : L' s = some sn')
    (hslinks : ∀ c z, (c, z) ∈ sn'.liveAt t → ∃ c0, (c0, z) ∈ sn.liveAt t ∧ c0 ≠ cs ∧ f c0 = c)
    (hsG : ¬ Gone s) (hGr : ¬ Gone r)
    (hG : ∀ g, Gone g → g = y0 ∨ ∀ u c, TReach L t r u → TLink L t u c g → Gone u)
    (hother : ∀ x, x ≠ s → ¬ Gone x → L' x = L x) : TreeOK L' t r := by
  have hsy : TLink L t s cs y0 := ⟨sn, hsn, hcs⟩
  have hnotG : ∀ u c z, TReach L t r u → ¬ Gone u → TLink L t u c z → u ≠ s ∨ c ≠ cs →
      ¬ Gone z := by
    intro u c z hu hug hl hne hz
    rcases hG z hz with h | h
    · rw [h] at hl
      obtain ⟨h1, h2⟩ := ht.oneLink u c s cs y0 hu hs hl hsy
      rcases hne with hne | hne
      · exact hne h1
      · exact hne h2
    · exact hug (h u c hu hl)
  apply treeOK_transfer_gone L L' t r r (fun _ => False) Gone
    (fun u c => if u = s then (s, f c) else (u, c)) ht (fun _ h => h.elim)
  · exact Or.inl ⟨rfl, hGr⟩
  · intro u c z hu hug hl
    have huR : TReach L t r u := by
      rcases hu with h | h
      · exact h
      · exact h.elim
    obtain ⟨m, hm, hcm⟩ := hl
    by_cases hus : u = s
    · rw [hus, hsn'] at hm
      simp only [Option.some.injEq] at hm
      subst hm
      obtain ⟨c0, hmem, hc, hf⟩ := hslinks c z hcm
      have hl0 : TLink L t s c0 z := ⟨sn, hsn, hmem⟩
      exact Or.inr ⟨hnotG s c0 z hs hsG hl0 (Or.inr hc), s, c0, hs, hl0, by
        simp only [↓reduceIte, hf, hus]⟩
    · rw [hother u hus hug] at hm
      have hl0 : TLink L t u c z := ⟨m, hm, hcm⟩
      exact Or.inr ⟨hnotG u c z huR hug hl0 (Or.inl hus), u, c, huR, hl0, by simp [hus]⟩
  · intro _ _ _ _ z _ _ _ _ hz
    exact hz.elim
  · intro _ h; exact h.elim
  · by_cases hr : r = s
    · rw [hr, hsn']; exact ⟨_, rfl⟩
    · rw [hother r hr hGr]; exact ht.rootKey

theorem zipIdx_pairwise_lt {α : Type} : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).Pairwise (fun a b => a.2 < b.2) := by
  intro l
  induction l with
  | nil => intro k; exact List.Pairwise.nil
  | cons a rest ih =>
    intro k
    rw [List.zipIdx_cons]
    refine List.Pairwise.cons ?_ (ih (k + 1))
    intro b hb
    have := (List.mem_zipIdx hb).1
    simp only
    omega

theorem bitsOf_sorted (n : KNode) (c : Nat) : (n.bitsOf c).Pairwise (· < ·) := by
  unfold KNode.bitsOf
  apply List.pairwise_filterMap.mpr
  apply (zipIdx_pairwise_lt n.ks 0).imp
  intro a b hab x hx y hy
  rcases a with ⟨ka, ia⟩
  rcases b with ⟨kb, ib⟩
  cases ka with
  | key c1 y1 =>
    cases kb with
    | key c2 y2 =>
      simp only at hx hy hab
      split at hx <;> split at hy
      all_goals (try cases hx)
      all_goals (try cases hy)
      all_goals omega
    | _ => simp at hy
  | _ => simp at hx

theorem bitsOf_le_last (n : KNode) (c e : Nat) (hE : (n.bitsOf c).getLast? = some e) :
    ∀ j, j ∈ n.bitsOf c → j ≤ e := by
  intro j hj
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hE
  have hs := bitsOf_sorted n c
  rw [hys] at hs hj
  rcases List.mem_append.mp hj with h | h
  · have := (List.pairwise_append.mp hs).2.2 j h e (by simp)
    omega
  · simp at h; omega

/-- LE-b's node: the empty key names jy, compare value jcv is deleted, the other
live lookups are the node's. -/
theorem lebNode_live_lookup (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy y0 : NodeId)
    (hwf : klongsWf n.ks = true)
    (htdh : htd = true → ∃ old, n.ks.getLast? = some (.del old))
    (he : n.ks[e]? = some (.key 0 y0)) (helive : e ∉ n.lastBitmap)
    (helast : ∀ j y', e < j → n.ks[j]? = some (.key 0 y') → False)
    (hj0 : jcv ≠ 0) (hne : bitsUnion n.lastBitmap (n.bitsOf jcv) ≠ n.lastBitmap) (c : Nat) :
    (lebNode n tt htd lip e jcv jy).live.lookup c =
      if c = 0 then some jy else if c = jcv then none else n.live.lookup c := by
  have hel : e < n.ks.length := by rw [List.getElem?_eq_some_iff] at he; exact he.1
  have hn1 : ∃ n1 : KNode, (if htd = true then n.setAt (n.size - 1)
        (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))
      else n.add tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))) = n1 ∧
      klongsWf n1.ks = true ∧ n1.lastBitmap = bitsUnion n.lastBitmap (n.bitsOf jcv) ∧
      (∀ c, n1.live.lookup c = if c == jcv then none else n.live.lookup c) ∧
      (∀ (j c' : Nat) (y' : NodeId), n1.ks[j]? = some (Klong.key c' y') →
        n.ks[j]? = some (Klong.key c' y')) ∧
      n1.ks[e]? = some (Klong.key 0 y0) := by
    cases htd with
    | true =>
      obtain ⟨old, hlast⟩ := htdh rfl
      obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hlast
      have hks := n.setAt_last_delete_ks pre old (bitsUnion n.lastBitmap (n.bitsOf jcv)) hpre
      simp only [↓reduceIte]
      have hepre : e < pre.length := by
        rw [hpre] at he hel
        rcases Nat.lt_or_ge e pre.length with h | h
        · exact h
        · exfalso
          simp only [List.length_append, List.length_singleton] at hel
          have : e = pre.length := by omega
          subst this
          simp at he
      refine ⟨_, rfl, KNode.setAt_delete_wf n jcv old hwf hlast, ?_,
        fun c' => n.setAt_delete_live_lookup jcv c' old hlast, ?_, ?_⟩
      · change lastBitmapOf _ = _
        rw [hks, lastBitmapOf_append_delete]
      · intro j c' y' hj
        rw [hks] at hj
        rw [hpre]
        rcases Nat.lt_or_ge j pre.length with h | h
        · rw [List.getElem?_append_left h] at hj
          rw [List.getElem?_append_left h]; exact hj
        · rw [List.getElem?_append_right h] at hj
          rcases Nat.lt_or_ge (j - pre.length) 1 with h' | h'
          · have : j - pre.length = 0 := by omega
            rw [this] at hj; simp at hj
          · rw [List.getElem?_eq_none (by simp; omega)] at hj; cases hj
      · rw [hks, List.getElem?_append_left hepre]
        rw [hpre, List.getElem?_append_left hepre] at he
        exact he
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, KNode.add_delete_wf n tt jcv hwf hne, KNode.add_delete_lastBitmap _ _ _,
        fun c' => n.add_delete_live_lookup tt jcv c', ?_, ?_⟩
      · intro j c' y' hj
        exact KNode.add_getElem?_key n tt _ c' (fun y h => by cases h) j y' hj
      · rw [KNode.add_getElem?_lt n tt _ e hel]; exact he
  obtain ⟨n1, hn1e, hw1, hb1, hl1, hk1, he1⟩ := hn1
  unfold lebNode
  simp only
  rw [hn1e]
  cases lip with
  | true =>
    simp only [↓reduceIte]
    have hLL : LastLive n1.ks n1.lastBitmap e 0 := by
      refine ⟨⟨y0, he1⟩, ?_, ?_⟩
      · rw [hb1]
        intro h
        rcases (mem_bitsUnion_iff _ _ _).mp h with h | h
        · exact helive h
        · obtain ⟨y1, hy1⟩ := (n.mem_bitsOf_iff jcv e).mp h
          have := List.mem_zipIdx_iff_getElem?.mp hy1
          rw [he] at this
          simp only [Option.some.injEq, Klong.key.injEq] at this
          exact hj0 this.1.symm
      · intro j y' hj hjk
        exact (helast j y' hj (hk1 j 0 y' hjk)).elim
    rw [KNode.repoint_last_live_lookup n1 e 0 y0 jy he1 hLL c, hl1 c]
    by_cases hc : c = 0
    · simp [hc]
    · simp only [hc, ↓reduceIte]
      by_cases hcj : c = jcv <;> simp [hcj]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [KNode.add_key_live_lookup_of_wf n1 tt 0 c jy hw1, hl1 c]
    by_cases hc : c = 0
    · simp [hc]
    · have h0 : ((0 : Nat) == c) = false := by simpa using (Ne.symm hc)
      simp only [h0, hc, Bool.false_eq_true, ↓reduceIte]
      by_cases hcj : c = jcv <;> simp [hcj]

/-- LE-b's node is well formed and of no later time. -/
theorem lebNode_wf_times (n : KNode) (tt : Time) (htd lip : Bool) (e jcv : Nat) (jy : NodeId)
    (hwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ tt)
    (htdh : htd = true → ∃ old, n.ks.getLast? = some (.del old))
    (hne : bitsUnion n.lastBitmap (n.bitsOf jcv) ≠ n.lastBitmap) :
    klongsWf (lebNode n tt htd lip e jcv jy).ks = true ∧
      ∀ s, Klong.time s ∈ (lebNode n tt htd lip e jcv jy).ks → s ≤ tt := by
  have hn1 : ∃ n1 : KNode, (if htd = true then n.setAt (n.size - 1)
        (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))
      else n.add tt (.del (bitsUnion n.lastBitmap (n.bitsOf jcv)))) = n1 ∧
      klongsWf n1.ks = true ∧ ∀ s, Klong.time s ∈ n1.ks → s ≤ tt := by
    cases htd with
    | true =>
      obtain ⟨old, hlast⟩ := htdh rfl
      simp only [↓reduceIte]
      exact ⟨_, rfl, KNode.setAt_delete_wf n jcv old hwf hlast,
        KNode.setAt_last_del_times n tt old _ hlast hnt⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact ⟨_, rfl, KNode.add_delete_wf n tt jcv hwf hne,
        KNode.add_times n tt _ (fun s h => by cases h) hnt⟩
  obtain ⟨n1, hn1e, hw1, ht1⟩ := hn1
  unfold lebNode
  simp only
  rw [hn1e]
  cases lip with
  | true =>
    simp only [↓reduceIte]
    exact ⟨by rw [KNode.repoint_klongsWf]; exact hw1, KNode.repoint_times n1 e jy tt ht1⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨KNode.add_key_wf n1 tt 0 jy hw1, KNode.add_times n1 tt _ (fun s h => by cases h) ht1⟩

end SIS.Tree
