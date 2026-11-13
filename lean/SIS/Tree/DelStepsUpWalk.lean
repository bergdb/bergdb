/-
The walk of a delete with the merges on to its leaf's upward delete (bergdb
024-12, case (4)'s delete steps, `DelEmptyM`): the key's access path from the
space root across its segments (the path premises of the upward delete), with
an invariant J carried along (the books).
-/
import SIS.Tree.DelStepsBook
import SIS.Tree.DelStepsRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A delete, the merges on, up to its leaf's upward delete: the continuation
gets the leaf L, its node n, the state w3 there (read as w, with J), and the
path P from the space root to L in w's tree, cached in w3. After the upward
delete comes `fresh`, which Post must survive. -/
theorem writerWP_del_toLeafM (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (J : W → Prop) (hJ0 : J w)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Option Nat) (x : NodeId) (v : W), J v → J { v with path := v.path ++ [(s, x)] })
    (hJs : ∀ (v : W), J v → J { v with path := [] })
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hcont : ∀ (L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W),
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w L = some n →
      n.leaf = true → ReadsAs c.p base w w3 → J w3 → w3.nodes.lookup L = some n →
      w3.path = (none, w.top.rootKey) :: P →
      LinkedFrom (wNode c.p base w) c.i w.top.rootKey P →
      nodeAt w.top.rootKey P P.length = L →
      (∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
        some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)) →
      WriterWP (deleteUpward L P.length cv (pre ++ [cv])) c w3 (fun _ v => Post v)) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hw2p : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  have hJ2 : J w2 := by rw [← hw2]; exact hJp _ _ _ (hJs w hJ0)
  refine writerWP_putSegs_prefix_linkedSJ c base hvc (pre ++ [cv]) none [cv] (by simp) _ J hJd hJp pre
    w.top.rootKey rk w2 hJ2 (by rw [hr02.1]; exact hwfG) (by rw [hr02.1, hr02.2.2.1]; exact ht)
    (by rw [hr02.1]; exact hrk) (by rw [hw2p]; simp) ?_
  intro w2' hr2' hJ2' _ hsrc2' ⟨ps, hp2', hps, hpse, hpsc⟩
  rw [hr02.1] at hps hpsc
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_2]
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel rk w2' ht2))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) (hJd cv c.p.fuel rk w2' hJ2')) ?_
  intro L w3 ⟨⟨⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, _, hpre3⟩⟩, hJ3⟩
  rw [hr0.1] at hn hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w.top.rootKey) :: P := by rw [hp3, hp2', hw2p, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hps (by rw [hpse]; exact LinkedFrom.of_pathFrom _ _ cv rk steps hpf)
  have hXD : nodeAt w.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, hpse, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk steps hpf
    (fun mm hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hm : nodeAt w.top.rootKey P i ∈ (w.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hpsc _ hm _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w.top.rootKey P i = nodeAt rk steps j := by
        rw [hP, hj, nodeAt_append_right, hpse]
      have hvj : (nodeAt rk steps j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps rk steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  have hlen3 : w3.path.length - 1 = P.length := by rw [hp3']; simp
  unfold pathSize
  wpSimplify
  rw [hlen3]
  refine writerWP_mono (hcont L n P w3 hvisL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX) ?_
  intro noop v hv
  cases noop
  · simp only [Bool.not_false, ↓reduceIte, writerWP_bind]
    exact writerWP_mono (hfresh v hv) (fun _ _ h => by simp only [writerWP_pure]; exact h)
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    exact hv

/-- `DelInvF` at a state w' inside a delete of key from w0 (between operations,
with `PutInv` and the fuel premise), from `CollGetInv` at w', the walk's ranges
at w', the books at w', and the reading of w' as the delete of key from a state
v that reads as w0. -/
theorem delInvF_of_collGetInv (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (w0 v w' : W) (key : Key)
    (hI0 : PutInv c base w0) (hF0 : SegFits (wNode c.p base w0) c.i (c.p.fuel - 1) w0.top.rootKey)
    (hrv : ReadsAs c.p base w0 v)
    (hCG : CollGetInv c base w' w') (hRO : RangeOrder (wNode c.p base w') c.i w'.top.rootKey)
    (hbook : PutBook c B top0 w')
    (hread : ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' = if key == key' then none else wGet c.p c.i base v key') :
    DelInvF c base w0 key (c.p.fuel + 1) w' := by
  have hG := putInvG_of_book c base B top0 w' hB hbook
  have hT := hCG.1.1
  have hPI : PutInv c base w' := putInv_of_parts c base w' hG hT
    (fun y hy => hCG.1.2.1 y (reachS_tReach _ _ _ _ hy))
    (leafOrder_of_rangeOrder _ _ _ hRO hG.times)
  refine ⟨hPI, hG, hRO, fun y yn cc z hy hyn hl hz => hCG.1.2.2.2 y yn cc z hy hyn hl hz, ?_, ?_,
    B, top0, hB, hbook⟩
  · simp only [Nat.add_sub_cancel]
    exact segFits_mono _ _ _ _ _ hCG.2.2.1 (by omega)
  · intro key' hk'
    have hwfv : ∀ x xn, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
        wNode c.p base w' x = some xn → klongsWf xn.ks = true := fun x xn _ h => hPI.wf x xn h
    have hwfw : ∀ x xn, ReachS (wNode c.p base w0) c.i w0.top.rootKey x →
        wNode c.p base w0 x = some xn → klongsWf xn.ks = true := fun x xn _ h => hI0.wf x xn h
    rw [wGetAt_eq_wGet c base w' _ (by omega) hwfv hCG.2.2.1, wGetAt_eq_wGet c base w0 _ (by omega) hwfw hF0,
      hread key' hk']
    have hsame : wGet c.p c.i base v key' = wGet c.p c.i base w0 key' := by
      unfold wGet
      rw [hrv.1, hrv.2.1, ReadsAs.value _ _ _ _ hrv]
    rw [hsame]

end SIS.Tree
