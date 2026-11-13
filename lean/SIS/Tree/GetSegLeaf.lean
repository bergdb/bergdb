import SIS.Tree.GetSegInPlace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Every put of a key pre0 ++ [k1, cv] whose last segment's tree is one leaf L,
below the segment leaf q of the segment before with room for one klong (bergdb
024-12, TP10; `OpGetOK`'s rules together): with room, or by a time split or a
space split of L, in place for a leaf the transaction made, the reading changes
by the put alone, under `PutInv` (`writerWP_put_segLeaf_inv`). The writer's tree
gives that q is not reached from L (`notReach_parent_of_tree`). -/

/-- Below a node reached with the segment list ks, the nodes reached with ks and
more. -/
theorem reachS_tPathK (N : NodeId → Option KNode) (t : Time) (r a : NodeId) (ks : List Nat)
    (ha : TPathK N t r a ks) :
    ∀ x, ReachS N t a x → ∃ extra, TPathK N t r x (ks ++ extra) := by
  intro x hx
  induction hx with
  | root => exact ⟨[], by simpa using ha⟩
  | step y n c z _ hn hz ih =>
    obtain ⟨e, he⟩ := ih
    by_cases hl : n.leaf = true
    · exact ⟨e ++ [c], by rw [← List.append_assoc]; exact TPathK.seg he hn hl ⟨n, hn, hz⟩⟩
    · exact ⟨e, TPathK.inner he hn (by simpa using hl) ⟨n, hn, hz⟩⟩

/-- The leaf q of a key's segment before is not reached from the segment's root
L that q's klong names. -/
theorem notReach_parent_of_tree (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (root : NodeId)
    (ht : TreeOK N t root) (hwf : ∀ x n, N x = some n → klongsWf n.ks = true)
    (pre0 : List Nat) (k1 : Nat) (rq L : NodeId)
    (hrq : segRootR N t fuel pre0 root = some rq) (hL : getEqR N t k1 fuel rq = some L) :
    ∀ q, (q, k1) ∈ eqVisits N t k1 fuel rq → ∀ x, ReachS N t L x → x ≠ q := by
  intro q hq x hx hxq
  subst x
  have hrqp : TPathK N t root rq pre0 := by
    have := segRootR_tPathK N t root fuel hwf pre0 root [] rq TPathK.root hrq
    simpa using this
  have hqp := (eqVisits_tPathK N t root k1 fuel rq pre0 hrqp q k1 hq).1
  have hLp := getEqR_tPathK N t root k1 hwf fuel rq pre0 L hrqp hL
  obtain ⟨e, he⟩ := reachS_tPathK N t root L (pre0 ++ [k1]) hLp q hx
  have := tPathK_unique N t root ht q pre0 hqp _ he
  have hlen := congrArg List.length this
  simp at hlen

theorem writerWP_put_segLeaf_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre0 : List Nat) (k1 cv h : Nat) (rq L : NodeId) (n : KNode) (w : W) (hI : PutInv c base w)
    (hsa : 1 ≤ c.p.splitAbove) (hkey : keyWf (pre0 ++ [k1, cv]) = true)
    (hrq : segRootR (wNode c.p base w) c.i c.p.fuel pre0 w.top.rootKey = some rq)
    (hL : getEqR (wNode c.p base w) c.i k1 c.p.fuel rq = some L)
    (hNL : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (hseg : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true →
      qn.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (putKv (.put (pre0 ++ [k1, cv]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre0 ++ [k1, cv]) h) == key' then Op.value (.put (pre0 ++ [k1, cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hI.ids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hI.wf x xn hn
  have hkey' : pre0 ++ [k1, cv] = (pre0 ++ [k1]) ++ [cv] := by simp
  have hsegL : segRootR (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1]) w.top.rootKey = some L := by
    rw [segRootR_snoc, hrq]
    simp only [Option.bind_some, hL, hNL, Option.isSome_some, ↓reduceIte]
  have hrrq : ReachS (wNode c.p base w) c.i w.top.rootKey rq :=
    segRootR_reach _ _ _ _ hwfR pre0 _ rq ReachS.root hrq
  have hrL : ReachS (wNode c.p base w) c.i w.top.rootKey L :=
    segRootR_reach _ _ _ _ hwfR (pre0 ++ [k1]) _ L ReachS.root hsegL
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre0 ++ [k1, cv]) w.top.rootKey,
      w.taken.contains q.1 = false := fun q hq => hI.untaken q.1
    (fromVisits_reach _ _ _ _ hwfR _ _ q.1 q.2 ReachS.root hq)
  have ht' : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel ((pre0 ++ [k1]) ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := by rw [← hkey']; exact ht
  have hevL : eqVisits (wNode c.p base w) c.i cv c.p.fuel L = [(L, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hNL, hnl]
  have hLroot : L ≠ w.top.rootKey := by
    intro he
    obtain ⟨x, xn, hx, hxn, _, hs⟩ := getEqR_some_visit _ _ k1 c.p.fuel rq L hL
    have hrx : ReachS (wNode c.p base w) c.i w.top.rootKey x :=
      eqVisits_reach _ _ _ k1 c.p.fuel rq x k1 hrrq hx
    cases hfd : xn.searchEq c.i k1 with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      have hm := KNode.searchEq_mem xn c.i k1 fd (hI.wf x xn hxn) hfd
      rw [hs, he] at hm
      exact hI.tree.rootFree x k1 (reachS_tReach _ _ _ x hrx) ⟨xn, hxn, hm⟩
  have huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel L →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre0 ++ [k1, cv] := by
    intro key' x _ hk h1 h2 _ _
    rw [hkey']
    exact visits_unique_seg_of_tree _ _ _ _ hI.tree hI.wf (pre0 ++ [k1]) cv L
      (by rw [← hkey']; exact hkey) hsegL key' x hk h1 h2
  have huniq' : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel L →
      wNode c.p base w x = some n' → n'.leaf = true → key' = (pre0 ++ [k1]) ++ [cv] := by
    intro key' x n' h1 h2 h3 h4 h5; rw [← hkey']; exact huniq key' x n' h1 h2 h3 h4 h5
  have htreeK : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i → (wNode c.p base w z).isSome = true →
      ∀ x' xn' cc', ReachS (wNode c.p base w) c.i w.top.rootKey x' →
        wNode c.p base w x' = some xn' → (cc', z) ∈ xn'.liveAt c.i → x = x' ∧ cc = cc' :=
    fun x xn cc z hx hn hz _ x' xn' cc' hx' hn' hz' =>
      htree_of_treeOK _ _ _ hI.tree x xn cc z hx hn hz x' xn' cc' hx' hn' hz'
  have hnotq := notReach_parent_of_tree _ _ _ _ hI.tree hI.wf pre0 k1 rq L hrq hL
  have hnext : w.taken.contains w.next = false ∧ w.vals.lookup w.next = none := by
    refine ⟨?_, ?_⟩
    · cases h' : w.taken.contains w.next with
      | false => rfl
      | true => have := hidt _ h'; omega
    · apply List.lookup_eq_none_iff.mpr
      intro q' hq'
      have := hidvals q' hq'
      simp only [bne_iff_ne, ne_eq]
      omega
  have hfresh : ∀ key' x c' n' y,
      (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → (n'.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next := by
    intro key' x c' n' y hx hn' _ hs
    have hrx := fromVisits_reach _ _ _ _ hwfR key' _ x c' ReachS.root hx
    cases hfd : n'.searchEq c.i c' with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      have := hI.links x n' c' fd.y hrx hn' (KNode.searchEq_mem n' c.i c' fd (hI.wf x n' hn') hfd)
      omega
  have hat : ∀ (P : KNode → Prop), P n → ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv
      c.p.fuel L → wNode c.p base w L' = some n' → n'.leaf = true → P n' := by
    intro P hP L' n' hL' hn' _
    rw [hevL] at hL'
    have : L' = L := by simpa using hL'
    subst this
    rw [hNL] at hn'
    cases hn'
    exact hP
  have hlive : c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
    intro hlt he
    have := KNode.lastVersion_size n c.i
    simp only [KNode.cnt, he, List.length_nil] at this
    omega
  have hsegT : ∀ q qn, (q, k1) ∈ eqVisits (wNode c.p base w) c.i k1 c.p.fuel rq →
      wNode c.p base w q = some qn → qn.leaf = true → ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i :=
    fun q qn _ hqn _ => hI.times q qn hqn
  rw [hkey']
  by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
  · exact writerWP_put_room_seg c base hvc (pre0 ++ [k1]) cv h L w hfuel (by rw [← hkey']; exact hkey)
      hsegL ht'
      (fun L' n' hL' hn' hnl' => hat (fun m => klongsWf m.ks = true ∧
        (∀ s, Klong.time s ∈ m.ks → s ≤ c.i) ∧ m.size + 1 < c.p.M ∧
        deadOver c.p (m.add c.i (.key cv w.next)) = false)
        ⟨hI.wf L n hNL, hI.times L n hNL, hroom.1, hroom.2⟩ L' n' hL' hn' hnl')
      hnext huniq' hfresh
  · rw [← hkey']
    by_cases hnew : n.firstTime = some c.i
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_segSpaceSplitInPlace c base hvc pre0 k1 cv h rq L n w hkey hrq ht hI.ids
          hI.fresh hL hNL hnl
          ⟨hI.times L n hNL, hsp.1, hnew, hsp.2, hlive hsp.2, hI.keyNoValue L n hNL, hLroot⟩
          hsegT huniq hwfR htreeK hnotq
          (fun x xn cc z hx hn hz => by
            have := hI.links x xn cc z hx hn hz
            exact ⟨by omega, by omega, by omega⟩)
      · rw [hkey']
        exact writerWP_put_timeInPlace_seg c base hvc (pre0 ++ [k1]) cv h L w hfuel
          (by rw [← hkey']; exact hkey) hsegL ht'
          (fun L' n' hL' hn' hnl' => hat (fun m => klongsWf m.ks = true ∧
            (∀ s, Klong.time s ∈ m.ks → s ≤ c.i) ∧
            ¬ (m.size + 1 < c.p.M ∧ deadOver c.p (m.add c.i (.key cv w.next)) = false) ∧
            m.firstTime = some c.i ∧ (c.p.M ≤ m.size + 1 → (m.lastVersion c.i).size ≤ c.p.splitAbove))
            ⟨hI.wf L n hNL, hI.times L n hNL, hroom, hnew,
              fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩ L' n' hL' hn' hnl')
          hnext huniq' hfresh
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_segSpaceSplit c base hvc pre0 k1 cv h rq L n w hkey hrq ht hI.ids
          hI.fresh hL hNL hnl
          ⟨hI.times L n hNL, hsp.1, hnew, hsp.2, hlive hsp.2, hI.keyNoValue L n hNL, hLroot⟩
          (fun q qn hq hqn hql => ⟨hI.times q qn hqn, (hseg q qn hq hqn hql).1,
            (hseg q qn hq hqn hql).2⟩)
          huniq hwfR htreeK hnotq
          (fun x xn cc z hx hn hz => by
            have := hI.links x xn cc z hx hn hz
            exact ⟨by omega, by omega, by omega, by omega⟩)
      · exact writerWP_put_segTimeSplit c base hvc pre0 k1 cv h rq L n w hkey hrq ht hI.ids
          ⟨(hI.fresh _ (Nat.le_refl _)).1, (hI.fresh (w.next + 2) (by omega)).2,
            (hI.fresh (w.next + 2) (by omega)).1⟩ hL hNL hnl
          ⟨hI.times L n hNL, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩),
            hI.keyNoValue L n hNL, hLroot⟩
          (fun q qn hq hqn hql => ⟨hI.times q qn hqn, (hseg q qn hq hqn hql).1,
            (hseg q qn hq hqn hql).2⟩)
          huniq hwfR htreeK hnotq
          (fun x xn cc z hx hn hz => by
            have := hI.links x xn cc z hx hn hz
            exact ⟨by omega, by omega⟩)

/-- `writerWP_put_newSeg` under `PutInv`: a put of a key pre ++ [c0, cl] whose
prefix is there and whose leaf for c0 has no klong of c0 and room. -/
theorem writerWP_put_newSeg_inv (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W) (hI : PutInv c base w) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [c0, cl]) h) == key' then Op.value (.put (pre ++ [c0, cl]) h)
        else wGet c.p c.i base w key') := by
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hI.wf x xn hn
  have hrkp : TPathK (wNode c.p base w) c.i w.top.rootKey rk0 pre := by
    have := segRootR_tPathK _ _ _ _ hI.wf pre _ [] rk0 TPathK.root hrk
    simpa using this
  refine writerWP_put_newSeg c base hvc pre c0 cl h rk0 w hM hrk
    (fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ hwfR _ _ q.1 q.2 ReachS.root hq))
    hI.ids hI.fresh ?_ hwfR hI.links
  intro L n hL hn hnl
  obtain ⟨hnone, hroom⟩ := hcur L n hL hn hnl
  have hLp := (eqVisits_tPathK _ _ _ c0 _ rk0 pre hrkp L c0 hL).1
  refine ⟨hI.wf L n hn, hI.times L n hn, hnone, hroom, ?_, ?_⟩
  · intro key' _ h1
    obtain ⟨j, hxj, hj⟩ := fromVisits_tPathK _ _ _ _ hI.wf key' _ [] TPathK.root L c0 h1
    simp only [List.nil_append] at hxj
    have htake : key'.take j = pre := tPathK_unique _ _ _ hI.tree L _ hxj pre hLp
    have hsplit : key' = pre ++ key'.drop j := by rw [← htake, List.take_append_drop]
    have hdrop : (key'.drop j).head? = some c0 := by rw [List.head?_drop]; exact hj
    cases hd : key'.drop j with
    | nil => rw [hd] at hdrop; cases hdrop
    | cons d rest =>
      rw [hd] at hdrop hsplit
      simp only [List.head?_cons, Option.some.injEq] at hdrop
      subst hdrop
      exact ⟨rest, hsplit⟩
  · intro c' h1
    obtain ⟨j, hxj, hj⟩ := fromVisits_tPathK _ _ _ _ hI.wf pre _ [] TPathK.root L c' h1
    simp only [List.nil_append] at hxj
    have htake : pre.take j = pre := tPathK_unique _ _ _ hI.tree L _ hxj pre hLp
    have hjlt : j < pre.length := by
      have := List.getElem?_eq_some_iff.mp hj
      exact this.1
    have hlen := congrArg List.length htake
    simp only [List.length_take] at hlen
    omega

end SIS.Tree
