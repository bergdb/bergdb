/-
Root collapse at the writer (bergdb 024-22, `OpTreeOK`; `collapseRoot`): the
klong that `onlyLiveKlong` finds is the last live key klong of the node
(`onlyLiveKlong_last`), so it names a live child (`onlyLiveKlong_link`).
-/
import SIS.Tree.WriterTreeRetarget

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The fold of `onlyLiveKlong` so far: its choice is a key klong the bitmap
keeps, after which every key klong is deleted. -/
def OnlyOK (ks : List Klong) (del : List Nat) (acc : Option (Option (Nat × Nat))) : Prop :=
  ∀ i c, acc = some (some (i, c)) →
    (∃ y, ks[i]? = some (.key c y)) ∧ i ∉ del ∧ ∀ j c' y', i < j → ks[j]? = some (.key c' y') → j ∈ del

def onlyStep (del : List Nat) (acc : Option (Option (Nat × Nat))) (q : Klong × Nat) :
    Option (Option (Nat × Nat)) :=
  match acc with
  | none => none
  | some cur =>
    match q.1 with
    | .key c _ =>
      if del.contains q.2 then acc else
        match cur with
        | some (_, cv) => if c != cv then none else some (some (q.2, c))
        | none => some (some (q.2, c))
    | _ => acc

theorem onlyOK_step (ks : List Klong) (del : List Nat) (acc : Option (Option (Nat × Nat))) (k : Klong)
    (ha : OnlyOK ks del acc) : OnlyOK (ks ++ [k]) del (onlyStep del acc (k, ks.length)) := by
  have keep : ∀ i c, acc = some (some (i, c)) → (∀ c' y', k = .key c' y' → ks.length ∈ del) →
      (∃ y, (ks ++ [k])[i]? = some (.key c y)) ∧ i ∉ del ∧
        ∀ j c' y', i < j → (ks ++ [k])[j]? = some (.key c' y') → j ∈ del := by
    intro i c hacc hk
    obtain ⟨⟨y0, hy0⟩, hd, hl⟩ := ha i c hacc
    have hi : i < ks.length := by rw [List.getElem?_eq_some_iff] at hy0; exact hy0.1
    refine ⟨⟨y0, by rw [getElem?_append_single_lt _ _ _ hi]; exact hy0⟩, hd, ?_⟩
    intro j c' y' hij hj
    rcases Nat.lt_trichotomy j ks.length with h1 | h1 | h1
    · rw [getElem?_append_single_lt _ _ _ h1] at hj; exact hl j c' y' hij hj
    · subst h1; rw [getElem?_append_single_eq] at hj
      simp only [Option.some.injEq] at hj
      exact hk c' y' hj
    · rw [getElem?_append_single_gt _ _ _ h1] at hj; cases hj
  have fresh : ∀ c y, k = .key c y → ks.length ∉ del →
      (∃ y', (ks ++ [k])[ks.length]? = some (.key c y')) ∧ ks.length ∉ del ∧
        ∀ j c' y', ks.length < j → (ks ++ [k])[j]? = some (.key c' y') → j ∈ del := by
    intro c y hk hd
    refine ⟨⟨y, by rw [getElem?_append_single_eq, hk]⟩, hd, ?_⟩
    intro j c' y' hij hj
    rw [getElem?_append_single_gt _ _ _ hij] at hj; cases hj
  intro i c h
  unfold onlyStep at h
  cases acc with
  | none => cases h
  | some cur =>
    simp only at h
    cases k with
    | time t => exact keep i c h (fun _ _ he => by cases he)
    | del b => exact keep i c h (fun _ _ he => by cases he)
    | key c0 y0 =>
      simp only at h
      by_cases hd : del.contains ks.length = true
      · simp only [hd, ↓reduceIte] at h
        exact keep i c h (fun _ _ _ => by simpa using hd)
      · have hd' : ks.length ∉ del := by simpa using hd
        simp only [hd, Bool.false_eq_true, ↓reduceIte] at h
        cases cur with
        | none =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fresh c0 y0 rfl hd'
        | some pc =>
          rcases pc with ⟨i0, cv⟩
          simp only at h
          split at h
          · cases h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact fresh c0 y0 rfl hd'

theorem onlyOK_fold (del : List Nat) (ks : List Klong) :
    OnlyOK ks del (ks.zipIdx.foldl (onlyStep del) (some none)) := by
  have key : ∀ rs : List Klong, OnlyOK rs.reverse del
      (rs.reverse.zipIdx.foldl (onlyStep del) (some none)) := by
    intro rs
    induction rs with
    | nil => intro i c h; cases h
    | cons k rs ih =>
      rw [List.reverse_cons, List.zipIdx_append, List.foldl_append]
      simp only [List.zipIdx_cons, List.zipIdx_nil, Nat.zero_add, List.foldl_cons, List.foldl_nil]
      exact onlyOK_step rs.reverse del _ k ih
  have := key ks.reverse
  rwa [List.reverse_reverse] at this

/-- `onlyLiveKlong` finds the last live key klong of the node. -/
theorem onlyLiveKlong_last (n : KNode) (i : Nat) (h : n.onlyLiveKlong = some i) :
    ∃ c y, n.ks[i]? = some (.key c y) ∧ LastLive n.ks n.lastBitmap i c := by
  have hf := onlyOK_fold n.lastBitmap n.ks
  unfold KNode.onlyLiveKlong at h
  simp only at h
  split at h
  · rename_i i0 c0 hr
    simp only [Option.some.injEq] at h
    subst h
    have hr' : n.ks.zipIdx.foldl (onlyStep n.lastBitmap) (some none) = some (some (i0, c0)) := hr
    obtain ⟨⟨y, hy⟩, hd, hl⟩ := hf i0 c0 hr'
    exact ⟨c0, y, hy, ⟨y, hy⟩, hd, fun j y' hij hj => hl j c0 y' hij hj⟩
  · cases h

/-- The tree after the root r gives way to its child y, whatever becomes of r:
it is the tree from y, and it reaches only nodes r reached, not r. -/
theorem treeOK_collapse_reach (N N' : NodeId → Option KNode) (t : Time) (r y : NodeId) (c : Nat)
    (hT : TreeOK N t r) (hl : TLink N t r c y) (hy : ∃ m, N y = some m)
    (hother : ∀ x, x ≠ r → N' x = N x) :
    TreeOK N' t y ∧ ∀ z, TReach N' t y z → TReach N t r z ∧ z ≠ r := by
  refine ⟨treeOK_collapseSpace N N' t r y c hT hl hy hother, ?_⟩
  have hyr : TReach N t r y := TReach.link TReach.root hl
  have hsub := tReach_trans N t r y hyr
  have hnr : ∀ x, TReach N t y x → x ≠ r := by
    intro x hx hxr
    rw [hxr] at hx
    cases hx with
    | root => exact hT.rootFree r c TReach.root hl
    | link hz hl' => exact hT.rootFree _ _ (hsub _ hz) hl'
  intro z hz
  have h1 := tReach_of_agree N N' t y (fun x hx => hother x (hnr x hx)) z hz
  exact ⟨hsub z h1, hnr z h1⟩

/-- What root collapse at the space root keeps: the writer's tree, its reached
nodes not taken back and of no later time, the live klongs of its reached
inner nodes naming nodes. -/
def CollInv (c : Ctx) (base : View BVal) (w : W) : Prop :=
  TreeOK (wNode c.p base w) c.i w.top.rootKey ∧
  (∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false) ∧
  (∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
    ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i) ∧
  (∀ y yn cc z, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
    yn.leaf = false → (cc, z) ∈ yn.liveAt c.i → ∃ m, wNode c.p base w z = some m)

theorem collInv_of_readsAs (c : Ctx) (base : View BVal) (w v : W) (hr : ReadsAs c.p base w v)
    (h : CollInv c base w) : CollInv c base v := by
  unfold CollInv at *
  rw [hr.1, hr.2.1, hr.2.2.1]
  exact h

/-- One collapse step keeps `CollInv`: the root r with a live klong to the
child y, the super root now naming y, nothing else changed but r and its
taking back. -/
theorem collInv_step (c : Ctx) (base : View BVal) (w w' : W) (y : NodeId) (cc : Nat)
    (h : CollInv c base w) (hl : TLink (wNode c.p base w) c.i w.top.rootKey cc y)
    (hrn : ∀ m, wNode c.p base w w.top.rootKey = some m → m.leaf = false)
    (htop : w'.top.rootKey = y)
    (ht : ∀ z, z ≠ w.top.rootKey → w'.taken.contains z = w.taken.contains z)
    (hn : ∀ z, z ≠ w.top.rootKey → w'.nodes.lookup z = w.nodes.lookup z) : CollInv c base w' := by
  obtain ⟨hT, hU, hTi, hL⟩ := h
  have hN : ∀ z, z ≠ w.top.rootKey → wNode c.p base w' z = wNode c.p base w z := by
    intro z hz; simp only [wNode, ht z hz, hn z hz]
  have hy : ∃ m, wNode c.p base w y = some m := by
    obtain ⟨m, hm, hc⟩ := hl
    exact hL _ m cc y TReach.root hm (hrn m hm) hc
  obtain ⟨hT', hreach⟩ := treeOK_collapse_reach (wNode c.p base w) (wNode c.p base w') c.i
    w.top.rootKey y cc hT hl hy hN
  unfold CollInv
  rw [htop]
  refine ⟨hT', fun z hz => ?_, fun z zn hz hzn => ?_, fun z zn cc' z' hz hzn hzl hmem => ?_⟩
  · obtain ⟨h1, h2⟩ := hreach z hz
    rw [ht z h2]; exact hU z h1
  · obtain ⟨h1, h2⟩ := hreach z hz
    rw [hN z h2] at hzn
    exact hTi z zn h1 hzn
  · obtain ⟨h1, h2⟩ := hreach z hz
    rw [hN z h2] at hzn
    obtain ⟨m, hmm⟩ := hL z zn cc' z' h1 hzn hzl hmem
    -- z' is reached from y, so it is not the old root
    have hz'R : TReach (wNode c.p base w') c.i y z' := TReach.link hz ⟨zn, by rw [hN z h2]; exact hzn, hmem⟩
    obtain ⟨_, hz'r⟩ := hreach z' hz'R
    exact ⟨m, by rw [hN z' hz'r]; exact hmm⟩

end SIS.Tree
