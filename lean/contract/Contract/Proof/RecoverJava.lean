/-
The contract package (bergdb 030-14): Java's readers on a tree that holds the
model's view (RecoverJava.lean). A tree that holds the view after transaction
k at a time t, read at t, agrees with the history's tree after t on every
node that tree reaches: the same level and kind, and klongs whose live klongs
are the same, since both lists of klongs have the same entries
(`live_klongsOfE`, twice). So Java's get and scan from the view's space root
read as on the history's tree, which reads as the plain map.
-/
import Mathlib.Tactic
import Contract.RecoverJava
import Contract.Proof.RecoverModel

namespace Contract

open SIS (Struct Entry History Node View Reach)
open SIS.Check (BVal blive)

variable {p : Params} {h : BHist}

theorem viewTree_root (V : View BVal) (lf : NodeId → Bool) :
    (viewTree V lf).root = viewRoot V := by
  cases hv : viewRoot V <;> simp [viewTree, Tree.root, hv]

/-- The view's space root is the tree's, at every time t up to k. -/
theorem MeetsBridge.viewRoot_eq (hm : MeetsBridge p h) {k t : Nat} (hk : k ≤ h.txs.length)
    (htk : t ≤ k) : viewRoot (SIS.view h.spec (h.P k) t) = (h.tree t).root := by
  rw [view_later hm htk hk, ← viewTree_root _ (leafOf (h.tree t))]
  exact ((hm.binv t (le_trans htk hk)).view_agree (leafOf (h.tree t))
    (fun x n _ hx => by simp [leafOf, hx])).1

/-- The view's top node is the link's, after transaction t at t. -/
theorem BInv.viewTop_eq {t : Nat} (hi : BInv h t) :
    ∃ z, viewTop (SIS.view h.spec (h.P t) t) = some z ∧ (h.tree t).obj z = none := by
  obtain ⟨n0, z, nz, y, n, h0, hl0, hz, hlz, hly, hroot, hy, hny, hs0, hsz⟩ := hi.link
  have hr0 : Reach h.spec (h.P t) t SIS.root := Reach.root n0 h0
  refine ⟨z, ?_, hsz⟩
  have hv0 := view_of_reachable ((SIS.reachable_iff _ _ _ _).mpr hr0) h0
  have hl0' : blive (n0.hist.upTo t) = [z] := hl0
  simp [viewTop, hv0, hl0']

/-- A tree that holds the view after transaction k at a time t up to k: Java's
get and scan from the view's space root, on the tree read at t, give what the
plain map after the first t transactions gives. -/
theorem MeetsBridge.holds_reads (hm : MeetsBridge p h) (hM : 1 ≤ p.M) {k t : Nat}
    (hk : k ≤ h.txs.length) (htk : t ≤ k) (lf : NodeId → Bool)
    (hlf : ∀ x n, x ∈ reach (h.tree t) → (h.tree t).obj x = some (.key n) → lf x = n.leaf)
    {s : Tree} (hs : HoldsView (SIS.view h.spec (h.P k) t) lf t s) {r : NodeId}
    (hr : viewRoot (SIS.view h.spec (h.P k) t) = some r) :
    (∀ key, getGo (s.at t) ((s.at t).fuel r) key r =
      refGet (refMap ((h.txs.map (·.ops)).take t)) key) ∧
    (∀ req, req.wf = true → ∀ limit,
      scanGo (s.at t) req (2 * (s.at t).fuel r + 2) limit (chainSetup (s.at t) req ((s.at t).fuel r) r) =
        refScan (refMap ((h.txs.map (·.ops)).take t)) req limit) := by
  have hrt := hm.viewRoot_eq hk htk
  rw [view_later hm htk hk] at hs
  have ht : t ≤ h.txs.length := le_trans htk hk
  have hi := hm.binv t ht
  have hmt := hm.meets hM t ht
  have hlen : ((h.txs.take t).map (·.ops)).length = t := by simp; omega
  obtain ⟨hinv, hcont⟩ := hmt.at_time t (by rw [hlen])
  rw [hi.timely.at_eq] at hinv hcont
  have htake : ((h.txs.take t).map (·.ops)).take t = (h.txs.map (·.ops)).take t := by
    rw [List.take_of_length_le (by rw [hlen]), List.map_take]
  rw [htake] at hcont
  obtain ⟨r0, hr0, hG⟩ := invOk_good hinv
  have hrr : r = r0 := by rw [hr, hr0] at hrt; injection hrt
  subst hrr
  obtain ⟨n0, hobj0⟩ : ∃ n0, (h.tree t).obj r = some (.key n0) := by
    cases hG with
    | mk _ _ _ n hobj _ _ _ _ _ _ _ => exact ⟨n, hobj⟩
  have hreach : reach (h.tree t) = reachAt (h.tree t) ((h.tree t).fuel r) r := by
    unfold reach; rw [hr0]
  have hR : ∀ x n c y, x ∈ reach (h.tree t) → (h.tree t).obj x = some (.key n) →
      (c, y) ∈ live n.ks → y ∈ reach (h.tree t) := by
    intro x n c y hx hn hy
    rw [hreach] at hx ⊢
    exact reachAt_closed hi.lev _ r _ hobj0 (by simp [Tree.fuel, hobj0, lvl]) x n c y hx hn hy
  have hRr : r ∈ reach (h.tree t) := by rw [hreach]; exact mem_reachAt_self _ _ _
  obtain ⟨z, hz, hsz⟩ := hi.viewTop_eq
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hs0, _⟩ := hi.link
  have hag : ∀ x o, x ∈ reach (h.tree t) → (h.tree t).obj x = some o →
      ∃ o', (s.at t).obj x = some o' ∧ ObjAgree o o' := by
    intro x o hx ho
    have hx0 : x ≠ SIS.root := by
      intro he; rw [he, hs0] at ho; cases ho
    have hxz : viewTop (SIS.view h.spec (h.P t) t) ≠ some x := by
      rw [hz]; intro he; injection he with he; subst he; rw [hsz] at ho; cases ho
    have hrx := hi.mem_reach_model hx
    have hrep := hi.rep x o ho
    cases o with
    | key nx =>
      have hP : (h.P t).get? x = some ⟨nx.level, false, entriesOf nx.ks⟩ := hrep
      have hup : (entriesOf nx.ks).upTo t = entriesOf nx.ks := by
        apply SIS.upTo_of_forall
        intro e he
        rcases entriesFrom_time_mem nx.ks [] 0 [] e he with h1 | h1
        · omega
        · exact hi.timely.1 x nx ho e.time h1
      have hv := view_of_reachable hrx hP
      rw [hup] at hv
      obtain ⟨kn, hkn, hlev, hleaf, hwf, hfull, hent⟩ := (hs x _ hx0 hxz hv).1 rfl
      refine ⟨.key { kn with ks := prefixAt kn.ks t }, ?_, ?_⟩
      · simp [Tree.at, hkn, Obj.at]
      · obtain ⟨hwf0, hfull0⟩ := hi.wf x nx ho
        have hl : lf x = nx.leaf := hlf x nx hx ho
        refine ⟨hlev, by rw [hleaf, hl], ?_, hwf⟩
        simp only at hent ⊢
        rw [← live_klongsOfE _ hwf hfull, hent, live_klongsOfE _ hwf0 hfull0]
    | val v =>
      obtain ⟨t0, ht0, hP⟩ := hrep
      have hup : SIS.History.upTo [(⟨t0, .data v⟩ : Entry BVal)] t = [⟨t0, .data v⟩] := by
        apply SIS.upTo_of_forall
        intro e he
        simp only [List.mem_singleton] at he
        subst he
        exact ht0
      have hv := view_of_reachable hrx hP
      rw [hup] at hv
      obtain ⟨v', hd, hsv⟩ := (hs x _ hx0 hxz hv).2 rfl
      have hvv : v' = v := by
        simp [dataOf] at hd
        exact hd.symm
      subst hvv
      exact ⟨.val v', by simp [Tree.at, hsv, Obj.at], rfl⟩
  obtain ⟨hG', hL⟩ := hG.transfer _ hR hag hRr
  constructor
  · intro key
    rw [getGo_of_good hG', hL, ← get_of_good hr0 hG, get_contents hinv, hcont]
    rfl
  · intro req hreq limit
    rw [scanFrom_of_good hG' req hreq, hL, ← scan_of_good hr0 hG req hreq,
      scan_contents hinv req hreq, hcont]

/-- Java's readers, from any top whose search at t finds the view's space
root, on a tree that holds the view after transaction k at t with the kinds
that its levels give, are right at t, for a history that meets K-LEVEL. -/
theorem MeetsBridge.java_reads (hm : MeetsBridge p h) (hM : 1 ≤ p.M) {kind : Nat → Bool}
    (hkd : KindsOK kind h) {k t : Nat} (hk : k ≤ h.txs.length) (htk : t ≤ k) {s : Tree}
    {tp : Top} {mid : Bool}
    (hs : HoldsView (SIS.view h.spec (h.P k) t) (kindOf kind (SIS.view h.spec (h.P k) t)) t s)
    (htop : findRoot tp t mid = viewRoot (SIS.view h.spec (h.P k) t)) :
    JReadsRight s tp t mid (h.txs.map (·.ops)) := by
  have hrt := hm.viewRoot_eq hk htk
  have ht : t ≤ h.txs.length := le_trans htk hk
  have hi := hm.binv t ht
  obtain ⟨_, _, _, y, _, _, _, _, _, _, hroot, _⟩ := hi.link
  rw [hroot] at hrt
  have hlf : ∀ x n, x ∈ reach (h.tree t) → (h.tree t).obj x = some (.key n) →
      kindOf kind (SIS.view h.spec (h.P k) t) x = n.leaf := by
    intro x n hx ho
    rw [view_later hm htk hk]
    have hrx := hi.mem_reach_model hx
    have hP : (h.P t).get? x = some ⟨n.level, false, entriesOf n.ks⟩ := hi.rep x _ ho
    simp only [kindOf, view_of_reachable hrx hP]
    exact (hm.kinds hkd t ht x n ho).symm
  obtain ⟨hg, hsc⟩ := hm.holds_reads hM hk htk _ hlf hs hrt
  constructor
  · intro key
    unfold jget
    rw [htop, hrt]
    exact hg key
  · intro req hreq limit
    unfold jscan
    rw [htop, hrt]
    exact hsc req hreq limit

end Contract
