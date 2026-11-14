import SIS.Tree.PutInvSeg
import SIS.Tree.WriterTreeNewSeg

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by the put of a key whose last segment is new (bergdb 024-12,
TP10; the rule of prover latest's put into a new segment leaf): the leaf L of the
segment before gets a klong (c0, y) to a new segment leaf y, the next id, which
holds the klong (cl, v) of the new value. The order bound of L's parents is the
descent's, or none when L is the root of its segment tree
(`segRootR_noInner`). -/

/-- No reachable inner node links the root of a segment tree that a key's
prefix leads to. -/
theorem segRootR_noInner (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre : List Nat) (rk : NodeId)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) :
    ∀ q qn k1, ReachS (wNode c.p base w) c.i w.top.rootKey q → wNode c.p base w q = some qn →
      qn.leaf = false → (k1, rk) ∈ qn.live → False := by
  intro q qn k1 hq hqn hql hk
  rcases List.eq_nil_or_concat pre with hnil | ⟨pre', k, hpre⟩
  · subst hnil
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    have hk' : (k1, w.top.rootKey) ∈ qn.liveAt c.i := by
      rw [KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk
    exact hI.rootFree' q qn k1 hq hqn hk'
  · rw [List.concat_eq_append] at hpre
    subst hpre
    rw [segRootR_snoc] at hrk
    cases hr : segRootR (wNode c.p base w) c.i c.p.fuel pre' w.top.rootKey with
    | none => rw [hr] at hrk; cases hrk
    | some rq =>
      rw [hr] at hrk
      simp only [Option.bind_some] at hrk
      cases hg : getEqR (wNode c.p base w) c.i k c.p.fuel rq with
      | none => rw [hg] at hrk; cases hrk
      | some y =>
        rw [hg] at hrk
        simp only at hrk
        split at hrk
        · cases hrk
          exact segRoot_noInner c base w hI pre' k rq _ hr hg q qn k1 hq hqn hql hk
        · cases hrk

/-- The bound of the parents of the leaf that a key's compare value reaches in
the segment tree of rk: the descent's, or no inner parent at all. -/
theorem parentBound_gen (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (pre : List Nat) (cv : Nat) (rk L : NodeId)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) :
    ∀ q qn k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (k1, L) ∈ qn.live →
      k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'' := by
  intro q qn k1 hq hqn hql hk
  by_cases hLrk : L = rk
  · subst hLrk
    exact absurd (segRootR_noInner c base w hI pre L hrk q qn k1 hq hqn hql hk) id
  · have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
      segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
    exact parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1 hq hqn hk

/-- The parts about the tree after the put of a key whose last segment is new:
L gets (c0, y), y a new leaf with the one live klong (cl, v). -/
theorem putInvT_newSeg (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (c0 cl : Nat) (L y v : NodeId) (n m : KNode) (hy : w.next ≤ y) (hv : w.next ≤ v) (hyv : y ≠ v)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hL' : wNode c.p base w' L = some (n.add c.i (.key c0 y)))
    (hy' : wNode c.p base w' y = some m) (hml : m.leaf = true)
    (hm : ∀ c' z, (c', z) ∈ m.liveAt c.i → c' = cl ∧ z = v)
    (hother : ∀ x, x ≠ L → x ≠ y → wNode c.p base w' x = wNode c.p base w x)
    (hpar : ∀ q qn k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (k1, L) ∈ qn.live →
      k1 ≤ c0 ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → c0 < c'') :
    PutInvT c base w' := by
  have hLnext := hI.lt_next L n hn
  have hvN : wNode c.p base w v = none := hI.none_of_ge v hv
  have hvN' : wNode c.p base w' v = none := by
    rw [hother v (by omega) (Ne.symm hyv)]; exact hvN
  have hwf := hI.wf L n hn
  have hnt := hI.times L n hn
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      ReachS (wNode c.p base w) c.i w.top.rootKey x ∨ x = y ∨ x = v := by
    rw [htop]
    apply reachS_closed _ _ _ (fun x => ReachS (wNode c.p base w) c.i w.top.rootKey x ∨ x = y ∨
      x = v) (Or.inl ReachS.root)
    intro x xn cc z hx hxn hz
    rcases hx with hx | hx | hx
    · by_cases hxL : x = L
      · subst hxL
        rw [hL'] at hxn
        cases hxn
        rcases KNode.add_key_liveAt_mem n c.i c0 y hwf hnt cc z hz with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr (Or.inl h2)
        · exact Or.inl (ReachS.step x n cc z hx hn h2)
      · have := hI.reach_lt x hx
        rw [hother x hxL (by omega)] at hxn
        exact Or.inl (ReachS.step x xn cc z hx hxn hz)
    · subst hx; rw [hy'] at hxn; cases hxn
      exact Or.inr (Or.inr (hm cc z hz).2)
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with hx | hx | hx
    · exact hI.untaken x hx
    · subst hx; exact hI.untaken_of_ge _ hy
    · subst hx; exact hI.untaken_of_ge _ hv
  · intro q qn L2 n2 k1 hq hqn hql hn2 hnl2 hk
    rcases hsub q hq with hq' | hq' | hq'
    · have := hI.reach_lt q hq'
      have hqL : q ≠ L := by
        intro he; subst he; rw [hL'] at hqn; cases hqn
        rw [KNode.add_leaf, hnl] at hql; cases hql
      rw [hother q hqL (by omega)] at hqn
      have hk' : (k1, L2) ∈ qn.liveAt c.i := by
        rw [KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk
      have hL2y : L2 ≠ y := by have := hI.links q qn k1 L2 hq' hqn hk'; omega
      by_cases hL2 : L2 = L
      · subst hL2
        rw [hL'] at hn2
        cases hn2
        exact leafOrderAt_add qn n k1 c0 y c.i hwf hnt
          (hI.order q qn L2 n k1 hq' hqn hql hn hnl hk) (hpar q qn k1 hq' hqn hql hk)
      · rw [hother L2 hL2 hL2y] at hn2
        exact hI.order q qn L2 n2 k1 hq' hqn hql hn2 hnl2 hk
    · subst hq'; rw [hy'] at hqn; cases hqn; rw [hml] at hql; cases hql
    · subst hq'; rw [hvN'] at hqn; cases hqn

/-- The put of a key pre ++ [c0, cl] whose leaf L for c0 has no klong of c0 and
room: L gets (c0, y) for a new segment leaf y at the next id, which holds the
new value's klong (cl, v), v the id after it; nothing else the state reads
changes. -/
theorem writerWP_put_newSeg_after (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hidn : ∀ z, (w.nodes.lookup z).isSome = true → z < w.next)
    (hidv : ∀ z, (c.view z).isSome = true → z < w.next)
    (hidt : ∀ z, w.taken.contains z = true → z < w.next)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' => ∃ L n,
      (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 ∧
      wNode c.p base w L = some n ∧ n.leaf = true ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
      wNode c.p base w' L = some (n.add c.i (.key c0 w.next)) ∧
      wNode c.p base w' w.next = some ((⟨true, []⟩ : KNode).add c.i (.key cl (w.next + 2))) ∧
      ∀ x, x ≠ L → x ≠ w.next → wNode c.p base w' x = wNode c.p base w x) := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 [cl] pre _ rk0 hrk
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre ++ [c0, cl]) (some h) [c0, cl] (by simp) _ pre
    w.top.rootKey rk0 w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by subst hw2; simp) ?_
  intro w2' hr2' _ hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 [cl] (by simp)]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i c0 c.p.fuel rk0,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk q hq)
  refine writerWP_mono (writerWP_and (writerWP_descendLte_reads c0 c base hvc c.p.fuel rk0 w2' ht1)
    (writerWP_descendLte_cache c0 c base hvc c.p.fuel rk0 w2' ht1)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hnone, hroom⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hLt : w.taken.contains L = false := ht (L, c0) (hvk _ hvisL)
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.top = w3.top →
      WriterWP (setValue w3.next cl (pre ++ [c0, cl]) (some h)) c ws (fun _ w' => ∃ L' n',
        (L', c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 ∧
        wNode c.p base w L' = some n' ∧ n'.leaf = true ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
        wNode c.p base w' L' = some (n'.add c.i (.key c0 w.next)) ∧
        wNode c.p base w' w.next = some ((⟨true, []⟩ : KNode).add c.i (.key cl (w.next + 2))) ∧
        ∀ x, x ≠ L' → x ≠ w.next → wNode c.p base w' x = wNode c.p base w x) := by
    intro ws h1 h2 h3 h5
    have hlkc : ws.nodes.lookup w3.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w3.next ≠ L by omega, ↓reduceIte]
      rw [List.lookup_append]
      have : w3.nodes.lookup w3.next = none := by
        cases h' : w3.nodes.lookup w3.next with
        | none => rfl
        | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
      rw [this]; simp [List.lookup]
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    unfold setValue
    simp only [writerWP_bind, writerWP_read]
    rw [show descendLte cl c.p.fuel w3.next = descendLte cl (f2 + 1) w3.next by rw [hf2]]
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known _ e c ws hlkc]
    simp only [e, ↓reduceIte, writerWP_pure]
    unfold newValue fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
    rw [writerWP_getNode_known _ e c _ (by simpa using hlkc)]
    have hcond : (decide ((e.size) + 1 < c.p.M) && !deadOver c.p (e.add c.i (.key cl ws.next))) = true := by
      simp only [e, KNode.size, List.length_nil, deadOver_empty_add]
      simp; omega
    simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    have g1 := h1
    rw [h2, hnext3]
    rw [hnext3] at g1
    have hLne : L ≠ w.next := by omega
    have hlookf : ∀ x, (upsert ws.nodes w.next (e.add c.i (.key cl (w.next + 2)))).lookup x =
        if x = w.next then some (e.add c.i (.key cl (w.next + 2)))
        else if x = L then some (n.add c.i (.key c0 w.next)) else w3.nodes.lookup x := by
      intro x
      rw [lookup_upsert, g1, lookup_upsert, List.lookup_append]
      by_cases hx1 : x = w.next
      · simp [hx1]
      · simp only [hx1, ↓reduceIte]
        by_cases hx2 : x = L
        · simp [hx2]
        · simp only [hx2, ↓reduceIte]
          cases h' : w3.nodes.lookup x with
          | some _ => rfl
          | none =>
            show (none : Option KNode).or ([(w.next, e)].lookup x) = none
            rw [lookup_cons_ne _ _ _ _ hx1]; rfl
    have g3 : ws.taken = w.taken := h3.trans hr03.2.2.1
    refine ⟨L, n, hvisL, hn, hnl, g3, h5.trans hr03.2.1, ?_, ?_, ?_⟩
    · simp only [wNode, g3, hLt, Bool.false_eq_true, ↓reduceIte, hlookf, hLne]
    · simp only [wNode, g3, hntake _ (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte, hlookf]
      rfl
    · intro x hxL hxy
      rw [← hr03.1]
      simp only [wNode, g3, hr03.2.2.1, hlookf, hxy, hxL, ↓reduceIte]
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    rw [putSegs.eq_2]
    exact hrest _ rfl rfl rfl rfl

/-- The put of a key pre ++ [c0, cl] whose prefix is there and whose leaf for
c0 has no klong of c0 and room keeps `PutInv` (the writer's tree after it
given). -/
theorem putInv_put_newSeg (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq =>
    hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) _ _ q.1 q.2
      ReachS.root hq)
  refine writerWP_mono (writerWP_put_newSeg_after c base hB.coherent pre c0 cl h rk0 w hM hrk ht
    hI.ids.1 hI.ids.2.1 hI.ids.2.2.1 hcur) ?_
  intro _ w' ⟨L, n, hL, hn, hnl, htk, htop, hL', hy', hother⟩
  refine putInvT_newSeg c base w w' hI c0 cl L w.next (w.next + 2) n _ (Nat.le_refl _) (by omega)
    (by omega) hn hnl htk htop hL' hy' (by rw [KNode.add_leaf]) ?_ hother
    (parentBound_gen c base w hI pre c0 rk0 L hrk hL)
  intro c' z hm
  have he : (⟨true, []⟩ : KNode).add c.i (.key cl (w.next + 2)) =
      ⟨true, newKlongs c.i [(cl, w.next + 2)]⟩ := rfl
  rw [he] at hm
  have := liveAt_newKlongs_mem true c.i c.i _ c' z hm
  simpa using this

end SIS.Tree
