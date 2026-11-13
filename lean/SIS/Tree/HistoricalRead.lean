import SIS.Tree.HistoricalPrefix
import SIS.Tree.WalkEdges
import SIS.Proof.Util

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem addsFor_future (c : Changes BVal) (i t : Time) (x : NodeId) (ht : t < i) :
    ∀ e ∈ addsFor c i x, t < e.time := by
  intro e he
  rw [(mem_addsFor.mp he).1]
  exact ht

theorem addsFor_upTo_past (c : Changes BVal) (i t : Time) (x : NodeId) (ht : t < i) :
    (addsFor c i x).upTo t = [] := upTo_eq_nil _ t (addsFor_future c i t x ht)

theorem newNodeOf_hist_nil (c : Changes BVal) (x : NodeId) (n : Node BVal)
    (hn : newNodeOf c x = some n) : n.hist = [] := by
  obtain ⟨node, _, he⟩ := List.mem_map.mp (mem_of_get? hn)
  have hnode := congrArg Prod.snd he
  dsimp only at hnode
  rw [← hnode]

theorem topAt_apply_past (P : Struct BVal) (i t : Time) (c : Changes BVal) (ht : t < i) :
    topAt (viewOf (P.apply i c)) t = topAt (viewOf P) t := by
  unfold topAt viewOf
  rw [get?_apply]
  cases hr : P.get? root with
  | some n =>
    simp only [hr, Option.some_or, Option.map_some]
    rw [upTo_append, addsFor_upTo_past c i t root ht, List.append_nil]
  | none =>
    simp only [hr, Option.none_or]
    cases hn : newNodeOf c root with
    | none => rfl
    | some n =>
      simp only [hn, Option.map_some, newNodeOf_hist_nil c root n hn,
        List.nil_append, addsFor_upTo_past c i t root ht]
      rfl

theorem rootKeyOf_apply_some (P : Struct BVal) (i : Time) (c : Changes BVal)
    (x y : NodeId) (hy : rootKeyOf (viewOf P) x = some y) :
    rootKeyOf (viewOf (P.apply i c)) x = some y := by
  unfold rootKeyOf viewOf at hy ⊢
  cases hx : P.get? x with
  | none => simp [hx] at hy
  | some n =>
    simp only [hx, Option.bind_some] at hy
    rw [get?_apply_of_get? hx]
    simp only [Option.bind_some, List.findSome?_append, hy, Option.some_or]

theorem rootAt_apply_some_past (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (r : NodeId) (hr : rootAt (viewOf P) t = some r) :
    rootAt (viewOf (P.apply i c)) t = some r := by
  unfold rootAt at hr ⊢
  rw [topAt_apply_past P i t c ht]
  cases hz : topAt (viewOf P) t with
  | none => simp [hz] at hr
  | some z =>
    simp only [hz, Option.bind_some] at hr ⊢
    exact rootKeyOf_apply_some P i c z r hr

theorem valueOf_apply_some (P : Struct BVal) (i : Time) (c : Changes BVal)
    (x h : Nat) (hv : valueOf (viewOf P) x = some h) :
    valueOf (viewOf (P.apply i c)) x = some h := by
  unfold valueOf viewOf at hv ⊢
  cases hx : P.get? x with
  | none => simp [hx] at hv
  | some n =>
    cases hd : n.isData with
    | false => simp [hx, hd] at hv
    | true =>
      simp only [hx, hd, ↓reduceIte] at hv
      rw [get?_apply_of_get? hx]
      simp only [hd, ↓reduceIte, List.findSome?_append, hv, Option.some_or]

theorem knodeOf_apply_past (p : Params) (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (x : NodeId) (n : KNode) (hn : knodeOf p (viewOf P) x = some n) :
    ∃ next, knodeOf p (viewOf (P.apply i c)) x = some next ∧ next.leaf = n.leaf ∧
      prefixAt next.ks t = prefixAt n.ks t := by
  unfold knodeOf viewOf at hn
  cases hx : P.get? x with
  | none => simp [hx] at hn
  | some nd =>
    simp only [hx] at hn
    split at hn
    · cases hn
    · rename_i hkind
      have he := Option.some.inj hn
      subst n
      let next : KNode := ⟨p.heightOf nd.level == 0, klongsOf (nd.hist ++ addsFor c i x)⟩
      refine ⟨next, ?_, rfl, ?_⟩
      · simp [knodeOf, viewOf, get?_apply_of_get? hx, hkind, next]
      · exact klongsOf_prefixAt_append_future nd.hist _ t (addsFor_future c i t x ht)

theorem KNode.liveAt_eq_of_prefix (a b : KNode) (t : Time)
    (he : prefixAt a.ks t = prefixAt b.ks t) : a.liveAt t = b.liveAt t := by
  simp only [KNode.liveAt, KNode.delAt, KNode.lastVersionGivenDel, he]
  rfl

/-- Appending future entries does not change the map enumerated by a
fault-free old walk. Only the old structure supplies the walk and data facts. -/
theorem treeContents_apply_past (p : Params) (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (hP : HighKindsOK p P) (hdata : DataEntriesOK P)
    (f x lo : Nat) (hi : Option Nat) (isRoot space : Bool)
    (hw : walk p (viewOf P) t f x lo hi isRoot space = []) :
    treeContents p (viewOf (P.apply i c)) t f x = treeContents p (viewOf P) t f x := by
  induction f generalizing x lo hi isRoot space with
  | zero => rfl
  | succ f ih =>
    cases hx : P.get? x with
    | none => simp [walk, viewOf, hx] at hw
    | some nd =>
      cases hd : nd.isData with
      | true => simp [walk, viewOf, hx, hd] at hw
      | false =>
        have hl := highKindsOK_walk_level p P t f x lo hi isRoot space nd hP hx hd hw
        let n : KNode := ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩
        have hn : knodeOf p (viewOf P) x = some n := by
          simp [knodeOf, viewOf, hx, hd, Nat.not_lt_of_ge hl, n]
        obtain ⟨next, hn', hleaf, hpre⟩ := knodeOf_apply_past p P i t c ht x n hn
        have hlive := next.liveAt_eq_of_prefix n t hpre
        simp only [treeContents, hn, hn', hlive, hleaf]
        apply flatMap_congr_mem
        intro q hq
        obtain ⟨b, hb⟩ := childBounds_exists (n.liveAt t) hi q hq
        have he := walk_edge_info p P t f x lo hi isRoot space nd hdata hx hd hw q b hb
        change ((n.leaf && segLen q.1 != 7) = true → _) ∧
          ((n.leaf && segLen q.1 != 7) = false → _) at he
        cases hnl : n.leaf with
        | false =>
          have hc := he.2 (by simp [hnl])
          have hi' := ih q.2 _ _ _ _ hc
          simpa only [hnl, Bool.false_eq_true, ↓reduceIte] using hi'
        | true =>
          by_cases hlen : segLen q.1 = 7
          · have hc := he.2 (by simp [hnl, hlen])
            have hi' := ih q.2 _ _ _ _ hc
            simp only [hnl, hlen, beq_self_eq_true, ↓reduceIte]
            rw [hi']
          · obtain ⟨h, hvalue⟩ := he.1 (by simp [hnl, hlen])
            have hnext := valueOf_apply_some P i c q.2 h hvalue
            simp [hnl, hlen, hvalue, hnext]

theorem rootContents_apply_past (p : Params) (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (hP : HighKindsOK p P) (hdata : DataEntriesOK P) (hi : InvOK p P t) :
    rootContents p (P.apply i c) t = rootContents p P t := by
  unfold InvOK faultsAt at hi
  cases hr : rootAt (viewOf P) t with
  | none => simp [hr] at hi
  | some r =>
    simp only [hr] at hi
    unfold rootContents
    rw [rootAt_apply_some_past P i t c ht r hr, hr]
    exact treeContents_apply_past p P i t c ht hP hdata p.fuel r 0 none true true hi

theorem get_apply_past_of_invariants (p : Params) (P : Struct BVal) (i t : Time) (c : Changes BVal)
    (ht : t < i) (hP : HighKindsOK p P) (hnext : HighKindsOK p (P.apply i c))
    (hdata : DataEntriesOK P) (hi : InvOK p P t) (hi' : InvOK p (P.apply i c) t)
    (key : Key) (hkey : keyWf key = true) :
    get p (viewOf (P.apply i c)) t key = get p (viewOf P) t key := by
  rw [get_lookup_rootContents p _ t hnext hi' key hkey,
    get_lookup_rootContents p P t hP hi key hkey,
    rootContents_apply_past p P i t c ht hP hdata hi]

end SIS.Tree
