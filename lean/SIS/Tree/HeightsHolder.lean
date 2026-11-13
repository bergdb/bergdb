/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)): a node
taken back (`takenBack`). The walk asks that no kept node has a live klong to it
(`NoLiveHolder`). That fact comes from the take-back's state: a node of the
transaction is named only by klongs of the transaction's time, a node holding
one is reached (`TtReachedN`), and among the nodes reached one klong names it
(`TreeOK.oneLink`): `liveHolder_unique` gives that holder, the parent.
-/
import SIS.Tree.WriterHeightsDel
import SIS.Tree.TakeDeadCollapse

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

theorem ht_nodup_reverse {l : List Nat} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_reverse]
  exact h.imp (fun h1 h2 => h1 h2.symm)

/-- A node of the overlay under its id. -/
theorem ht_lookup_of_mem {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) {q : NodeId} {m : KNode}
    (hm : (q, m) ∈ w.nodes) : w.nodes.lookup q = some m := by
  have hnd : (w.nodes.map (·.1)).Nodup := by
    rw [hb.ids]; exact ht_nodup_reverse hb.nodup
  exact lookup_of_mem_nodup _ hnd q m hm

/-- No kept node of the overlay has a live klong to o, now or before the
transaction. -/
def NoLiveHolder (c : Ctx) (w : W) (o : NodeId) : Prop :=
  ∀ q n, (q, n) ∈ w.nodes → w.taken.contains q = false →
    (∀ cv, (cv, o) ∉ n.live) ∧ (∀ cv, (cv, o) ∉ (n.toPrev (c.i - 1)).live)

/-- The one live holder of a node of the transaction: a node with a live klong
to o, a node at or above B, is reached and names it by the parent's klong. -/
theorem liveHolder_unique (N : NodeId → Option KNode) (t : Time) (r B : NodeId) (hpos : 0 < t)
    (hTt : TtReachedN N t r) (hO : OldBelowN N t B) (hTi : TimesN N t) (hT : TreeOK N t r)
    (o : NodeId) (hB : B ≤ o) (p : NodeId) (cp : Nat) (hp : TReach N t r p)
    (hpo : TLink N t p cp o) :
    ∀ q qn, N q = some qn → ∀ cv, (cv, o) ∈ qn.liveAt t → q = p ∧ cv = cp := by
  intro q qn hq cv hl
  have hk : Klong.key cv o ∈ qn.ks := KNode.liveAt_key_mem qn t cv o hl
  have htm := time_of_new N t B hpos hO hTi q qn hq cv o hk hB
  have hr := hTt q qn hq htm
  obtain ⟨h1, h2⟩ := hT.oneLink q cv p cp o hr hp ⟨qn, hq, hl⟩ hpo
  exact ⟨h1, h2⟩

/-- No klong before the transaction names a node of the transaction. -/
theorem prevHolder_none (N : NodeId → Option KNode) (t : Time) (B : NodeId)
    (hO : OldBelowN N t B) (o : NodeId) (hB : B ≤ o) :
    ∀ q qn, N q = some qn → ∀ cv, (cv, o) ∉ (qn.toPrev (t - 1)).live := by
  intro q qn hq cv hl
  have hk := ht_live_mem hl
  have := hO q qn hq cv o hk
  omega

/-- `takenBack o` keeps the walk when no kept node holds o, o is not the space
root, and o is a node of the transaction. -/
theorem ht_takenBack (B : NodeId) (o : NodeId) (c : Ctx) (vr w : W) (n : KNode)
    (hl : vr.nodes.lookup o = some n) (hk : Kept vr w) (hb : Book B c w) (hi : HtInv H B c w)
    (hno : NoLiveHolder c w o) (hroot : w.top.rootKey ≠ o) (hB : B ≤ o) :
    WriterWP (takenBack o) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v ∧
      v.path = w.path ∧ v.taken = o :: w.taken) := by
  refine writerWP_mono (writerWP_and (book_takenBack B o c vr w n hl hk hb)
    (?_ : WriterWP (takenBack o) c w (fun _ v => HtInv H B c v ∧ v.path = w.path ∧
      v.taken = o :: w.taken))) ?_
  · simp only [takenBack, writerWP_modify]
    have hfree : ∀ y, w.taken.contains y = false → y ≠ o →
        (o :: w.taken).contains y = false := by
      intro y hy hyo
      simp only [List.contains_cons, Bool.or_eq_false_iff]
      exact ⟨by simpa using hyo, hy⟩
    refine ⟨⟨?_, ?_, hi.pathGh, ?_, ?_, hi.pathSome⟩, by trivial, by trivial⟩
    · intro x m g h hm hg htk
      have htk' : w.taken.contains x = false ∧ x ≠ o := by
        simp only [List.contains_cons, Bool.or_eq_false_iff] at htk
        exact ⟨htk.2, fun he => by subst he; simp at htk⟩
      have hN := hi.cache x m g h hm hg htk'.1
      have hho := hno x m hm htk'.1
      refine ⟨fun cv y hy => ⟨hfree y (hN.1 cv y hy).1 (fun he => ?_), (hN.1 cv y hy).2⟩,
        fun cv y hy => ⟨hfree y (hN.2 cv y hy).1 (fun he => ?_), (hN.2 cv y hy).2⟩, hN.3⟩
      · subst he; exact hho.1 cv hy
      · subst he; exact hho.2 cv hy
    · intro d a q cv y h1 h2 g h hg htk hh
      have htk' : w.taken.contains q = false := by
        simp only [List.contains_cons, Bool.or_eq_false_iff] at htk
        exact htk.2
      exact hi.path d a q cv y h1 h2 g h hg htk' hh
    · exact hfree _ hi.rootFree hroot
    · intro x hx
      simp only [List.contains_cons, Bool.or_eq_true] at hx
      rcases hx with hx | hx
      · have : x = o := by simpa using hx
        subst this; exact hB
      · exact hi.takenAbove x hx
  · rintro _ v ⟨⟨hb', hk'⟩, hi', hp, ht⟩
    exact ⟨hb', hi', hk', hp, ht⟩

/-- A store of the leaf's klong of x pointed to x's child keeps the leaf without
a live klong to x, when the leaf's live klongs to x were that one. -/
theorem ht_repoint_drops {n : KNode} {x y : NodeId} {k j : Nat} (hj : n.linkIndex x k = some j)
    (hxy : y ≠ x) (hone : ∀ cv, (cv, x) ∈ n.live → cv = k) :
    ∀ cv, (cv, x) ∉ (n.repoint j y).live := by
  intro cv hcv
  have hl := lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cv x hcv
  rw [KNode.repoint_live_lookup n x y k j hj cv] at hl
  split at hl
  · cases hl; exact hxy rfl
  · rename_i hne
    have := hone cv (mem_of_lookup_nodup _ cv x hl)
    subst this
    simp at hne

theorem ht_repoint_prev_drops {n : KNode} {t : Time} {x y : NodeId} {j : Nat} (hxy : y ≠ x)
    (hprev : ∀ cv, (cv, x) ∉ (n.toPrev t).live) :
    ∀ cv, (cv, x) ∉ ((n.repoint j y).toPrev t).live := by
  intro cv hcv
  unfold KNode.repoint at hcv
  split at hcv
  · rename_i a y0 hjk
    have hf : PtrSwapL (fun z => z = y) n.ks (n.setAt j (.key a y)).ks :=
      ht_swapL_set n.ks j a y0 y hjk rfl
    rcases ht_live_swap (n := n.toPrev t) (n' := (n.setAt j (.key a y)).toPrev t)
      (ht_swapL_prefixAt t hf) hcv with h1 | h1
    · exact hprev cv h1
    · exact hxy h1.symm
  · exact hprev cv hcv

/-- The holders of x at w: only the path's node above x (at depth - 1), by the
path's klong of x; none before the transaction. -/
def HolderAt (c : Ctx) (w : W) (x : NodeId) (depth : Nat) : Prop :=
  (∀ q n, (q, n) ∈ w.nodes → w.taken.contains q = false → ∀ cv, (cv, x) ∈ n.live →
    depth ≠ 0 ∧ (∃ a, w.path[depth - 1]? = some (a, q)) ∧ w.path[depth]? = some (some cv, x)) ∧
  (∀ q n, (q, n) ∈ w.nodes → w.taken.contains q = false → ∀ cv, (cv, x) ∉ (n.toPrev (c.i - 1)).live)

set_option maxHeartbeats 1600000 in
/-- `takeBackRoot` of the inner root x, the path's node at depth, made by the
transaction and with one live klong, of the empty key: its child takes its place
and x is taken back. -/
theorem ht_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) (c : Ctx) (w : W)
    (hvo : ViewHtOK H B c) (_hpos : 0 < c.i) (hb : Book B c w) (hi : HtInv H B c w)
    (g h : Nat) (hx : (x, g, h) ∈ w.gh) (n : KNode) (hn : w.nodes.lookup x = some n)
    (hnl : n.leaf = false) (honly : n.onlyLiveKlong = some only) (hcv0 : n.cv? only = some 0)
    (a : Option Nat) (hpx : w.path[depth]? = some (a, x)) (hpf : PathFreeTo w (depth + 1))
    (hhold : HolderAt c w x depth) (hroot : depth ≠ 0 → w.top.rootKey ≠ x) (hB : B ≤ x)
    (hseg : ∀ a' q, depth ≠ 0 → w.path[depth - 1]? = some (a', q) → ∃ g', (q, g', 0) ∈ w.gh) :
    WriterWP (takeBackRoot x depth only) c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ Kept w v) := by
  have hxf : w.taken.contains x = false := hpf depth a x (by omega) hpx
  have hN := hi.cache x n g h (bk_mem_of_lookup _ _ _ hn) hx hxf
  have hh0 : h ≠ 0 := by
    have := kd_leaf hb hn hx
    rw [hnl] at this
    intro h0; subst h0; simp at this
  unfold takeBackRoot
  htSimp
  refine writerWP_mono (kd_getNode_hit x n c w hn) ?_
  rintro n' w1 ⟨hnn, hww⟩
  rw [hnn, hww]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i child hchild
    have hlive : (0, child) ∈ n.live := by
      have := (onlyLiveKlong_liveAt n c.i only child hN.3 honly hchild hcv0).1
      rw [KNode.liveAt_of_times n c.i hN.3] at this
      exact this
    have hcf : w.taken.contains child = false := (hN.1 0 child hlive).1
    have hch : HasHt H w child (h - 1) := (hN.1 0 child hlive).2 hh0
    have hcx : child ≠ x := by
      intro he; subst he
      obtain ⟨hd, _⟩ := hhold.1 child n (bk_mem_of_lookup _ _ _ hn) hxf 0 hlive
      obtain ⟨_, hq, hq'⟩ := hhold.1 child n (bk_mem_of_lookup _ _ _ hn) hxf 0 hlive
      rw [hpx] at hq'
      simp only [Option.some.injEq, Prod.mk.injEq] at hq'
      obtain ⟨a', ha'⟩ := hq
      have hx' : (child, g, h) ∈ w.gh := hx
      -- x would be its own parent on the path: depth - 1 < depth names x at both
      have hlt : depth - 1 < depth := by omega
      have := hi.path (depth - 1) a' child 0 child ha' (by
        rw [show depth - 1 + 1 = depth by omega, hpx, hq'.1]) g h hx' hxf hh0
      have e := hasHt_tag hb hvo.heights hx' this
      omega
    have hframeNote : ∀ (s : String) (u : W), WriterWP (note s) c u
        (fun _ v => v.nodes = u.nodes ∧ v.gh = u.gh ∧ v.path = u.path ∧ v.taken = u.taken ∧
          v.top.rootKey = u.top.rootKey) := fun s u => htFrame_note s c u
    cases depth with
    | zero =>
      htSimp
      refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c w hvo hb hi) (hframeNote _ w)) ?_
      rintro _ w2 ⟨⟨hb2, hi2, hle2, hp2⟩, hn2, -, -, ht2, -⟩
      refine writerWP_mono (writerWP_and (hw_newSuperRoot B child c w2 hvo hb2 hi2 (ht_free_le hcf hle2))
        (?_ : WriterWP (newSuperRoot child) c w2 (fun _ v => v.nodes = w2.nodes ∧ v.taken = w2.taken ∧
          v.top.rootKey = child))) ?_
      · unfold newSuperRoot note fresh
        repeat' first
          | (simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure,
              writerWP_modify])
          | split
          | (refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl)
      · rintro _ w3 ⟨⟨hb3, hi3, hle3, hp3⟩, hn3, ht3, hr3⟩
        have hno : NoLiveHolder c w3 x := by
          intro q m hm htq
          rw [hn3, hn2] at hm; rw [ht3, ht2] at htq
          refine ⟨fun cv hcv => ?_, fun cv hcv => hhold.2 q m hm htq cv hcv⟩
          exact (hhold.1 q m hm htq cv hcv).1 rfl
        refine writerWP_mono (ht_takenBack B x c w w3 n hn (hle2.trans hle3).1 hb3 hi3 hno
          (by rw [hr3]; exact hcx) hB) ?_
        rintro _ w4 ⟨hb4, hi4, hk4, -, -⟩
        exact ⟨hb4, hi4, (hle2.trans hle3).1.trans hk4⟩
    | succ d =>
      htSimp
      refine writerWP_mono (writerWP_and (hw_keeps B (ht_note B _) c w hvo hb hi) (hframeNote _ w)) ?_
      rintro _ w2 ⟨⟨hb2, hi2, hle2, hp2⟩, hn2, -, -, ht2, htop2⟩
      refine writerWP_mono (kd_pathNode d c w2) ?_
      rintro leaf w2a ⟨hw2a, a', hpl⟩
      rw [hw2a]
      have hpl0 : w.path[d]? = some (a', leaf) := by rw [← hp2]; exact hpl
      have hlg : leaf ∈ w.gh.map (·.1) :=
        hi.pathGh d a' leaf hpl0 (List.getElem?_eq_some_iff.mp hpx).1
      obtain ⟨⟨q0, gq0, hq0'⟩, hqm0, hqe0⟩ := List.mem_map.mp hlg
      simp only at hqe0
      rw [hqe0] at hqm0
      obtain ⟨ln, hln⟩ := kd_lookup_of_tag hb hqm0
      have hln2 : w2.nodes.lookup leaf = some ln := by rw [hn2]; exact hln
      refine writerWP_mono (kd_getNode_hit leaf ln c w2 hln2) ?_
      rintro ln' w2b ⟨hlnb, hw2b⟩
      rw [hlnb, hw2b]
      refine writerWP_mono (kd_klongAt (d + 1) c w2) ?_
      rintro k w2c ⟨hw2c, y, hpk⟩
      rw [hw2c]
      have hpk0 : w.path[d + 1]? = some (some k, y) := by rw [← hp2]; exact hpk
      rw [hpx] at hpk0
      simp only [Option.some.injEq, Prod.mk.injEq] at hpk0
      obtain ⟨rfl, rfl⟩ := hpk0
      split
      · rename_i j hj
        split
        · exact writerWP_throw _ _ _ _
        · htSimp
          have hlf : w.taken.contains leaf = false := hpf d a' leaf (by omega) hpl0
          obtain ⟨gq, hq0⟩ := hseg a' leaf (by omega) (by simpa using hpl0)
          have hNl := hi.cache leaf ln gq 0 (bk_mem_of_lookup _ _ _ hln) hq0 hlf
          have hrep : NodeHt c H w2 0 (ln.repoint j child) :=
            (nodeHt_repoint hNl j child (fun _ => ht_P_val hcf)).htMono hle2
          refine writerWP_mono (writerWP_and (ht_putNode_of B leaf _ c w2 w2 w2 ln hb2 hi2 hln2
            (HtLe.refl _) (bk_repoint_leaf _ _ _) gq 0 (HtLe.gh' hq0 hle2) (HtLe.refl _) hrep)
            (writerWP_and (kd_putNode_other leaf _ ln c w2 hln2)
              (?_ : WriterWP (putNode leaf (ln.repoint j child)) c w2 (fun _ v => v.top = w2.top)))) ?_
          · simp only [putNode, writerWP_modify]
          rintro _ w3 ⟨⟨hb3, hi3, hle3, hp3, hl3⟩, hoth, htop3⟩
          have hno : NoLiveHolder c w3 x := by
            intro q m hm htq
            have htq0 : w.taken.contains q = false := by rw [← ht2, ← hle3.2]; exact htq
            by_cases hql : q = leaf
            · subst hql
              have hm' : w3.nodes.lookup q = some m := ht_lookup_of_mem hb3 hm
              rw [hl3] at hm'
              cases hm'
              refine ⟨ht_repoint_drops hj hcx (fun cv hcv => ?_), ht_repoint_prev_drops hcx
                (fun cv hcv => hhold.2 q ln (bk_mem_of_lookup _ _ _ hln) htq0 cv hcv)⟩
              obtain ⟨_, _, hq2⟩ := hhold.1 q ln (bk_mem_of_lookup _ _ _ hln) htq0 cv hcv
              rw [hpx] at hq2
              simp only [Option.some.injEq, Prod.mk.injEq] at hq2
              exact hq2.1.symm
            · have hm0 : (q, m) ∈ w.nodes := by
                have hnd : (w3.nodes.map (·.1)).Nodup := by
                  rw [hb3.ids]; exact ht_nodup_reverse hb3.nodup
                have hlq := lookup_of_mem_nodup _ hnd q m hm
                rw [hoth q hql, hn2] at hlq
                exact bk_mem_of_lookup _ _ _ hlq
              refine ⟨fun cv hcv => ?_, fun cv hcv => hhold.2 q m hm0 htq0 cv hcv⟩
              obtain ⟨_, ⟨a2, ha2⟩, _⟩ := hhold.1 q m hm0 htq0 cv hcv
              simp only [Nat.add_sub_cancel] at ha2
              rw [hpl0] at ha2
              simp only [Option.some.injEq, Prod.mk.injEq] at ha2
              exact hql ha2.2.symm
          have hr2 : w2.top.rootKey = w.top.rootKey := htop2
          refine writerWP_mono (ht_takenBack B x c w w3 n hn ((hle2.trans hle3).1) hb3 hi3 hno
            (by rw [htop3, hr2]; exact hroot (by omega)) hB) ?_
          rintro _ w4 ⟨hb4, hi4, hk4, -, -⟩
          exact ⟨hb4, hi4, (hle2.trans hle3).1.trans hk4⟩
      · exact writerWP_throw _ _ _ _

end SIS.Tree
