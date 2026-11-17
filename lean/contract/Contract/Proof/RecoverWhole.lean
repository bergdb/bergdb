/-
The contract package (bergdb 030-17): a tree that holds the model's structure
whole holds its view at every time (`MeetsFull.holdsView_whole`), and the
tree as written holds the structure whole (`MeetsFull.tree_holdsP`).

The route. A node of the view after transaction k at a time t, but the root
and the top node of t, is a node of the tree after t (030-14's `reach3`), so
on a level below the top nodes' (030-07's `TopInv.low`), so not a top node of
the structure. A tree that holds the structure whole gives it klongs that are
well formed and whose entries are its whole history; cut at t they are well
formed and have its entries up to t, which are the view's (Prefix.lean). A
value's history is its one data entry.
-/
import Mathlib.Tactic
import Contract.RecoverWhole
import Contract.Proof.Prefix
import Contract.Proof.RecoverCut

namespace Contract

open SIS (Struct Entry History Node View Reach)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist} {top : Nat → Top}

theorem isTop_congr {sp : SIS.Spec BVal Nat} {P P' : Struct BVal} (hP : ∀ x, P.get? x = P'.get? x)
    (x : NodeId) : SIS.isTop sp P x = SIS.isTop sp P' x := by
  unfold SIS.isTop
  rw [hP x]

theorem kindOfP_congr (kind : Nat → Bool) {P P' : Struct BVal} (hP : ∀ x, P.get? x = P'.get? x) :
    kindOfP kind P = kindOfP kind P' := by
  funext x
  simp only [kindOfP, hP x]

/-- Holding a structure whole depends only on its nodes. -/
theorem holdsP_congr {sp : SIS.Spec BVal Nat} {P P' : Struct BVal}
    (hP : ∀ x, P.get? x = P'.get? x) {lf : NodeId → Bool} {s : Tree} (hs : HoldsP sp P' lf s) :
    HoldsP sp P lf s := by
  intro x N hx0 htop hN
  rw [isTop_congr hP x] at htop
  rw [hP x] at hN
  exact hs x N hx0 htop hN

theorem isTop_false {sp : SIS.Spec BVal Nat} {P : Struct BVal} {x : NodeId} {N : Node BVal}
    (hN : P.get? x = some N) (hl : N.level < sp.topLevel) : SIS.isTop sp P x = false := by
  unfold SIS.isTop
  rw [hN]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le]
  exact Or.inr hl

/-- A tree that holds the model's structure after transaction k whole, with
the kinds of the levels, holds its view at every time t up to k. -/
theorem MeetsFull.holdsView_whole (hm : MeetsFull p h top) {kind : Nat → Bool} {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) {s : Tree}
    (hs : HoldsP h.spec (h.P k) (kindOfP kind (h.P k)) s) :
    HoldsView (SIS.view h.spec (h.P k) t) (kindOf kind (SIS.view h.spec (h.P k) t)) t s := by
  have ht : t ≤ h.txs.length := le_trans htk hk
  have hi := hm.meetsBridge.binv t ht
  have ti := (hm.meetsBridgeTop.inv t ht).2
  have hvl := view_later hm.meetsBridge htk hk
  intro x n hx0 hxz hv
  have hv0 := hv
  -- the node of the structure after k
  have hv' := hv
  unfold SIS.view at hv'
  split at hv'
  case isFalse => cases hv'
  obtain ⟨N, hN, hnN⟩ := Option.map_eq_some_iff.mp hv'
  have hkind : kindOf kind (SIS.view h.spec (h.P k) t) x = kind n.level := by
    simp [kindOf, hv0]
  rw [hvl] at hv hxz
  obtain ⟨n0, z, nz, y, ny, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  have hvz : viewTop (SIS.view h.spec (h.P t) t) = some z := by
    have hr0 : Reach h.spec (h.P t) t SIS.root := Reach.root n0 h0
    have hv00 := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hr0) h0
    have hl0' : blive (n0.hist.upTo t) = [z] := hl0
    simp [viewTop, hv00, hl0']
  have hrx : SIS.reachable h.spec (h.P t) t x = true := by
    by_contra hnr
    simp [SIS.view, hnr] at hv
  rw [SIS.reachable_iff] at hrx
  rcases hi.reach3 h0 hl0 hz hly hroot hy hrx with h1 | h1 | h1
  · exact absurd h1 hx0
  · exact absurd (by rw [hvz, h1]) hxz
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hi.reach_obj h1)
  have hlow := ti.low x o ho
  have hrx' := hi.mem_reach_model h1
  cases o with
  | key nt =>
    have hP : (h.P t).get? x = some ⟨nt.level, false, entriesOf nt.ks⟩ := hi.rep x _ ho
    rw [view_of_reachable hrx' hP] at hv
    injection hv with hv
    subst hv
    have hNl : N.level = nt.level := by simpa using congrArg Node.level hnN
    have hNd : N.isData = false := by simpa using congrArg Node.isData hnN
    have hNh : N.hist.upTo t = (entriesOf nt.ks).upTo t := by simpa using congrArg Node.hist hnN
    have htop : SIS.isTop h.spec (h.P k) x = false := isTop_false hN (by rw [hNl]; exact hlow)
    obtain ⟨kn, hkn, hlev, hleaf, hwf, hfull, hent⟩ := (hs x N hx0 htop hN).1 hNd
    refine ⟨fun _ => ⟨kn, hkn, by rw [hlev, hNl], ?_, klongsWf_prefixAt hwf t,
      fullOk_prefixAt hwf hfull t, ?_⟩, fun hd => by simp at hd⟩
    · rw [hkind, hleaf]
      simp [kindOfP, hN, hNl]
    · simp only [klongsWf, Bool.and_eq_true] at hwf
      rw [entriesOf_prefixAt hwf.1 t, hent, hNh]
  | val v =>
    obtain ⟨t0, ht0, hP⟩ := hi.rep x _ ho
    have hup : SIS.History.upTo [(⟨t0, .data v⟩ : Entry BVal)] t = [⟨t0, .data v⟩] := by
      apply SIS.upTo_of_forall
      intro e he
      simp only [List.mem_singleton] at he
      subst he
      exact ht0
    rw [view_of_reachable hrx' hP, hup] at hv
    injection hv with hv
    subst hv
    have hNl : N.level = 0 := by simpa using congrArg Node.level hnN
    have hNd : N.isData = true := by simpa using congrArg Node.isData hnN
    have htop : SIS.isTop h.spec (h.P k) x = false := isTop_false hN (by rw [hNl]; exact hlow)
    obtain ⟨v', hd', hsv⟩ := (hs x N hx0 htop hN).2 hNd
    -- the value in the tree after k
    have hsub := hm.meetsBridge.sub_at k htk hk
    rw [hi.timely.at_eq] at hsub
    have hko := hsub.1 x _ ho
    simp only [Tree.at, Option.map_eq_some_iff] at hko
    obtain ⟨o', ho', hat⟩ := hko
    cases o' with
    | key kn => simp [Obj.at] at hat
    | val v2 =>
      simp only [Obj.at, Obj.val.injEq] at hat
      subst hat
      obtain ⟨t1, _, hPk⟩ := (hm.meetsBridge.binv k hk).rep x _ ho'
      rw [hPk] at hN
      injection hN with hN
      subst hN
      have hvv : v' = v2 := by
        simp [dataOf] at hd'
        exact hd'.symm
      subst hvv
      exact ⟨fun hd => by simp at hd, fun _ => ⟨v', by simp [dataOf], hsv⟩⟩

/-- The same for any structure with the nodes of the model's after k (as a
startup gives back). -/
theorem MeetsFull.holdsView_same (hm : MeetsFull p h top) {kind : Nat → Bool} {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) {P : Struct BVal}
    (hP : ∀ x, P.get? x = (h.P k).get? x) {s : Tree} (hs : HoldsP h.spec P (kindOfP kind P) s) :
    HoldsView (SIS.view h.spec P t) (kindOf kind (SIS.view h.spec P t)) t s := by
  rw [SIS.SameNodes.view hP t]
  apply hm.holdsView_whole hk htk
  rw [kindOfP_congr kind hP] at hs
  exact holdsP_congr (fun x => (hP x).symm) hs

/-- The tree as written after transaction k holds the model's structure after
k whole, with the kinds of the levels. -/
theorem MeetsFull.tree_holdsP (hm : MeetsFull p h top) {kind : Nat → Bool} (hkd : KindsOK kind h)
    {k : Nat} (hk : k ≤ h.txs.length) :
    HoldsP h.spec (h.P k) (kindOfP kind (h.P k)) (h.tree k) := by
  have hi := hm.meetsBridge.binv k hk
  have ti := (hm.meetsBridgeTop.inv k hk).2
  intro x N hx0 htop hN
  cases ho : (h.tree k).obj x with
  | none =>
    rcases ti.other x N hN ho with h1 | ⟨zn, hzn⟩
    · exact absurd h1 hx0
    · obtain ⟨hz, hlev, _⟩ := ti.topNode (x, zn) hzn
      simp only at hz hlev
      have : SIS.isTop h.spec (h.P k) x = true := by
        unfold SIS.isTop
        rw [hz]
        simp only [bne_iff_ne, ne_eq, hx0, not_false_eq_true, decide_eq_true_eq,
          Bool.and_eq_true, true_and]
        exact hlev
      rw [this] at htop
      cases htop
  | some o =>
    cases o with
    | key nt =>
      have hP : (h.P k).get? x = some ⟨nt.level, false, entriesOf nt.ks⟩ := hi.rep x _ ho
      rw [hP] at hN
      injection hN with hN
      subst hN
      obtain ⟨hwf, hfull⟩ := hi.wf x nt ho
      refine ⟨fun _ => ⟨nt, rfl, rfl, ?_, hwf, hfull, rfl⟩, fun hd => by simp at hd⟩
      simp only [kindOfP, hP]
      exact hm.meetsBridge.kinds hkd k hk x nt ho
    | val v =>
      obtain ⟨t0, _, hP⟩ := hi.rep x _ ho
      rw [hP] at hN
      injection hN with hN
      subst hN
      exact ⟨fun hd => by simp at hd, fun _ => ⟨v, by simp [dataOf], rfl⟩⟩

end Contract
