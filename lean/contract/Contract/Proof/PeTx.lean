/-
bergdb 030-21: PE's transaction meets the writer's contract, TREE and the
top's clauses (`pe_step`), and every history PE writes meets them
(`pe_meetsTop`, `pe_meetsTop_start`).

The writer's state after the transaction of time t is the tree, its top and
the next fresh id; `Inv` is what PE keeps of it: the contract's invariants
and TREE (at t: every klong of a time at most t), PE's shape from the space
root (`Shaped`), every key node meets the rules of one node, the ids from
`next` on are no nodes, the top's own rules (`TopInv`), and the space roots
are the top nodes' root pointers. From `Inv` at i - 1, a transaction PE
accepts at i meets the contract (clauses 1 to 3), TREE, the top's clauses,
and leaves `Inv` at i. The segments' part is PeSeg.lean (`seg_space`).
-/
import Contract.Proof.PeSeg
import Contract.PeStatement
import Contract.TheoremsTop

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys

variable {cf : Cfg}

/-! ## The transaction unfolded -/

theorem peTx_spec {i : Time} {s : Tree} {tp : Top} {next : NodeId} {ops : List Op} {o : Out}
    (h : peTx cf i s tp next ops = some o) :
    opsOk cf (dropNoops cf ops) = true ∧
    ∃ r n v acc1 v' c0 r' acc2, s.root = some r ∧ getKey s r = some n ∧
      plan cf i s fuel r 0 (cf.htOf n.level) (dropNoops cf ops) ⟨[], next⟩ = some (v, acc1) ∧
      settleRoot cf i s fuel 0 v true = some (some v') ∧
      emit cf i s v' acc1 = some ([(c0, r')], acc2) ∧
      ((r' = r ∧ o = ⟨acc2.ws, s.roots, tp, acc2.next⟩) ∨
        (r' ≠ r ∧ o = ⟨acc2.ws, s.roots ++ [(i, r')],
          tp ++ [(acc2.next, newTopNode tp i r')], acc2.next + 1⟩)) := by
  unfold peTx at h
  simp only at h
  split at h
  · cases h
  rename_i hok
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hok
  refine ⟨by simpa using hok, ?_⟩
  split at h
  · cases h
  rename_i r hr
  split at h
  · cases h
  rename_i n hn
  split at h
  · cases h
  rename_i v acc1 hp
  split at h
  · rename_i v' hsr
    split at h
    · rename_i c0 r' acc2 he
      refine ⟨r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, ?_⟩
      split at h
      · rename_i heq
        left
        exact ⟨by simpa using heq, (Option.some.inj h).symm⟩
      · rename_i hne
        right
        refine ⟨by simpa using hne, ?_⟩
        simp only [Acc.fresh] at h
        exact (Option.some.inj h).symm
    · cases h
  · cases h

/-! ## The tree after the writes -/

theorem lookup_of_mem_nodup {W : List (NodeId × Obj)} (hnd : (W.map (·.1)).Nodup) :
    ∀ {p : NodeId × Obj}, p ∈ W → W.lookup p.1 = some p.2 := by
  induction W with
  | nil => intro p hp; cases hp
  | cons a rest ih =>
    intro p hp
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with rfl | hp2
    · simp [List.lookup]
    · have hne : p.1 ≠ a.1 := by
        intro he
        exact hnd.1 (he ▸ List.mem_map_of_mem hp2)
      obtain ⟨k, b⟩ := a
      have hne' : (p.1 == k) = false := by simpa using hne
      simp only [List.lookup, hne']
      exact ih hnd.2 hp2

theorem lookup_none_of_not_mem {W : List (NodeId × Obj)} {x : NodeId} (hx : x ∉ W.map (·.1)) :
    W.lookup x = none := by
  induction W with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    obtain ⟨k, b⟩ := a
    have hne' : (x == k) = false := by simpa using hx.1
    simp only [List.lookup, hne']
    exact ih hx.2

theorem applyWs_after {s : Tree} {W : List (NodeId × Obj)} {roots : List (Time × NodeId)}
    {U : List NodeId} (hnd : (W.map (·.1)).Nodup) : After s (applyWs s W roots) W U where
  ws := fun p hp => by simp [applyWs, lookup_of_mem_nodup hnd hp]
  keep := fun z _ hz => by simp [applyWs, lookup_none_of_not_mem hz]
  exist := fun z hz => by
    simp only [applyWs]
    cases W.lookup z <;> simp [hz]

theorem applyWs_obj_of_not {s : Tree} {W : List (NodeId × Obj)} {roots : List (Time × NodeId)}
    {x : NodeId} (hx : x ∉ W.map (·.1)) : (applyWs s W roots).obj x = s.obj x := by
  simp [applyWs, lookup_none_of_not_mem hx]

theorem applyWs_obj_of_mem {s : Tree} {W : List (NodeId × Obj)} {roots : List (Time × NodeId)}
    (hnd : (W.map (·.1)).Nodup) {p : NodeId × Obj} (hp : p ∈ W) :
    (applyWs s W roots).obj p.1 = some p.2 := by
  simp [applyWs, lookup_of_mem_nodup hnd hp]

theorem applyWs_obj_cases {s : Tree} {W : List (NodeId × Obj)} {roots : List (Time × NodeId)}
    (hnd : (W.map (·.1)).Nodup) (x : NodeId) :
    (∃ o, (x, o) ∈ W ∧ (applyWs s W roots).obj x = some o) ∨
      (x ∉ W.map (·.1) ∧ (applyWs s W roots).obj x = s.obj x) := by
  by_cases hx : x ∈ W.map (·.1)
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact Or.inl ⟨p.2, hp, applyWs_obj_of_mem hnd hp⟩
  · exact Or.inr ⟨hx, applyWs_obj_of_not hx⟩

/-! ## Small facts -/

/-- omega through the aliases `Time` and `NodeId` of Nat. -/
macro "tomega" : tactic => `(tactic| ((try unfold Time at *) <;> (try unfold NodeId at *) <;> omega))

theorem dropKey_zero (op : Op) : dropKey 0 op = op := by
  cases op <;> rfl

theorem map_dropKey_zero (ops : List Op) : ops.map (dropKey 0) = ops := by
  rw [show dropKey 0 = id from funext dropKey_zero, List.map_id]

theorem newTopNode_time (tp : Top) (i : Time) (r : NodeId) : (newTopNode tp i r).time = i := by
  unfold newTopNode; split <;> rfl

theorem newTopNode_root (tp : Top) (i : Time) (r : NodeId) : (newTopNode tp i r).root = r := by
  unfold newTopNode; split <;> rfl

theorem keyOk_of {k : Key} (h1 : keyWf k = true) (h2 : k.length + 0 ≤ cf.G + 1) : keyOk cf k = true := by
  unfold keyOk
  rw [h1, Bool.true_and, decide_eq_true_eq]
  exact h2

theorem key_ne_nil {k : Key} (h : keyOk cf k = true) : 0 < k.length := by
  cases k with
  | nil => simp [keyOk, keyWf] at h
  | cons a r => simp

theorem roots_times {tp : Top} {next : NodeId} {t : Time} (h : TopInv tp next t) :
    ∀ r ∈ rootsOf tp, r.1 ≤ t := by
  intro r hr
  simp only [rootsOf, List.mem_map] at hr
  obtain ⟨⟨z, n⟩, hm, rfl⟩ := hr
  exact h.times z n hm

theorem root_snoc (roots : List (Time × NodeId)) (i : Time) (r : NodeId) :
    ({ obj := fun _ => none, roots := roots ++ [(i, r)] } : Tree).root = some r := by
  simp [Tree.root]

/-! ## The transaction -/

/-- **PE's transaction meets the writer's contract, TREE and the top's
clauses.** From a state that PE keeps (`Inv` at i - 1: the tree meets the
contract's invariants and TREE, is shaped as PE's trees, every key node meets
the rules of one node and has no klong of time i or later, no node has an id
from `next` on, and the top meets its rules), every transaction that PE
accepts at time i (`peTx` gives `some o`) meets the contract (clauses 1 to 3,
with D the nodes written), the tree after meets TREE at i, the top after
meets the top's clauses, and the state after is again one PE keeps, at i. -/
theorem pe_step (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hw : peTx cf i s tp next ops = some o) :
    Contract cf.params i s ops o.D (o.tree s) ∧ Contract.TreeOk ((o.tree s).at i) ∧
      TopStep i tp o.top ∧ (o.tree s).roots = rootsOf o.top ∧ Inv cf i (o.tree s) o.top o.next := by
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk cf i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by have := hI.tree; unfold Contract.TreeOk at this; rwa [reach_eq_R hr] at this
  obtain ⟨r0, hr0, hsh0⟩ := hI.shaped
  have hrr : r0 = r := by rw [hr] at hr0; exact (Option.some.inj hr0).symm
  subst hrr
  have hobj : s.obj r0 = some (.key n) := getKey_obj hn
  have hht : htIn cf s r0 = cf.htOf n.level := by simp [htIn, hobj]
  have hpre : SegPre cf i s 0 (some r0) (dropNoops cf ops) ⟨[], next⟩ :=
    { sok := hsok
      fresh := hI.fresh
      ops := fun op hop => by
        have h1 : keyOk cf op.key = true := List.all_eq_true.mp hok op hop
        exact ⟨h1, key_ne_nil h1⟩
      root := fun r1 h => by
        cases h
        exact ⟨hsh0, hgood, hnd⟩ }
  obtain ⟨W, hWok, hold, hT⟩ := seg_space hcf hpre (hht ▸ hp) hsr he
  have hws : acc2.ws = W := by simpa using hWok.ws
  -- the output's parts
  have hows : o.ws = W := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hws
  have hnext : acc2.next ≤ o.next := by
    rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Nat.le_refl _
    · exact Nat.le_succ _
  have hroots : o.roots = s.roots ∨ o.roots = s.roots ++ [(i, r')] := by
    rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  set T := o.tree s with hTdef
  have hTobj : T.obj = (applyWs s W o.roots).obj := by simp [hTdef, Out.tree, hows]
  have hTroots : T.roots = o.roots := rfl
  have hafter : After s T W (R s r0) := by
    have := applyWs_after (s := s) (roots := o.roots) (U := R s r0) hWok.nodup
    exact ⟨fun p hp => by rw [hTobj]; exact this.ws p hp,
      fun z hz hz' => by rw [hTobj]; exact this.keep z hz hz',
      fun z hz => by rw [hTobj]; exact this.exist z hz⟩
  obtain ⟨hnok, hh, ht⟩ := hT T hafter
  have hcases : ∀ x, (∃ ob, (x, ob) ∈ W ∧ T.obj x = some ob) ∨
      (x ∉ W.map (·.1) ∧ T.obj x = s.obj x) := by
    intro x
    rw [hTobj]
    exact applyWs_obj_cases hWok.nodup x
  -- the space root after
  have hTroot : T.root = some r' := by
    rcases hout with ⟨heq, rfl⟩ | ⟨_, rfl⟩
    · show s.root = some r'
      rw [hr, heq]
    · show (s.roots ++ [(i, r')]).getLast?.map (·.2) = some r'
      simp
  -- the times
  have hrootT : ∀ q ∈ s.roots, q.1 ≤ i - 1 := by rw [hI.roots]; exact roots_times hI.top
  have hTat : T.at i = T := by
    apply tree_at_self
    · intro x nk hx u hu
      rcases hcases x with ⟨ob, hm, hx'⟩ | ⟨_, hx'⟩
      · rw [hx] at hx'
        exact hWok.times (x, ob) hm nk (by rw [Option.some.inj hx']) u hu
      · rw [hx] at hx'
        exact Nat.le_of_lt ((hsok x nk hx'.symm).2.2 u hu)
    · intro q hq
      rw [hTroots] at hq
      rcases hroots with h | h <;> rw [h] at hq
      · have := hrootT q hq; tomega
      · rcases List.mem_append.mp hq with hq | hq
        · have := hrootT q hq; tomega
        · simp at hq; rw [hq]
  have hsat : s.at (i - 1) = s := sok_at hsok (fun q hq => by have := hrootT q hq; tomega)
  -- clauses 1 and 2
  have hreachT : reach T = R T r' := reach_eq_R hTroot
  obtain ⟨hinvT, hcontT⟩ := clauses_of_good hTroot ht.good
    (fun z hz nk hnk => ht.nok z (hreachT ▸ hz) nk hnk) ht.rootLive
  have hkeys : ∀ kv ∈ L s r0, keyOk cf kv.1 = true := by
    intro kv hkv
    obtain ⟨h1, h2⟩ := keys_ok hsh0 hgood kv hkv
    exact keyOk_of h1 h2
  have hcont : contents T = applyOps ops (contents s) := by
    rw [hcontT, ht.keys, map_dropKey_zero, contents_eq hr,
      applyOps_dropNoops_opsOk cf ops (L s r0) hkeys hok]
  have hc12 : contractOk cf.params i s ops T = true := by
    simp only [contractOk, hTat, hsat, hinvT, hcont, Bool.true_and, beq_self_eq_true]
  -- clause 3
  have hD : o.D = W.map (·.1) := by simp [Out.D, hows]
  have hframe : Frame i s o.D T := by
    refine ⟨fun x ob hx => ?_, fun x nk hx hsx => ?_, ?_⟩
    · rcases hcases x with ⟨ob', hm, hx'⟩ | ⟨hnot, hx'⟩
      · obtain ⟨nk, rfl⟩ := hold (x, ob') hm ob hx
        obtain ⟨more, hmore⟩ := hWok.frame (x, ob') hm nk hx
        refine ⟨ob', hx', ?_, fun h => absurd (by rw [hD]; exact List.mem_map_of_mem hm) h⟩
        simp only at hmore
        rw [hmore]
        exact ⟨rfl, rfl, Or.inr ⟨more, rfl⟩⟩
      · refine ⟨ob, by rw [hx', hx], ?_, fun _ => rfl⟩
        cases ob with
        | val h => rfl
        | key nk => exact ⟨rfl, rfl, Or.inl rfl⟩
    · rcases hcases x with ⟨ob', hm, _⟩ | ⟨_, hx'⟩
      · rw [hD]; exact List.mem_map_of_mem hm
      · rw [hx', hsx] at hx; cases hx
    · rcases hroots with h | h
      · exact ⟨[], by rw [hTroots, h]; simp, by simp⟩
      · exact ⟨[(i, r')], by rw [hTroots, h], by simp⟩
  -- TREE at i
  obtain ⟨nr, hnr, hlev, _, _, hHt⟩ := shaped_obj ht.shaped
  have hRT : R T r' = reachAt T (cf.lev 0 hh + 1) r' := by simp [R, Tree.fuel, hnr, hlev]
  have hsub := ht.reach _ (le_refl _)
  rw [← hRT] at hsub
  have hfreshR : ∀ z ∈ R s r0, z < next := by
    intro z hz
    have hz' := reach_exists _ hgood z hz
    by_contra hc
    exact hz' (hI.fresh z (Nat.le_of_not_lt hc))
  have hndB : (R s r0 ++ List.range' next (acc2.next - next)).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnd, List.nodup_range', ?_⟩
    intro a ha b hb hab
    have h1 := hfreshR a ha
    rw [List.mem_range'] at hb
    subst hab
    tomega
  have htreeT : Contract.TreeOk T := by
    unfold Contract.TreeOk
    rw [hreachT]
    obtain ⟨l0, hperm, hsl⟩ := hsub
    exact hperm.nodup_iff.mp (hndB.sublist hsl)
  -- the top
  have htop : TopStep i tp o.top ∧ T.roots = rootsOf o.top ∧ TopInv o.top o.next i := by
    rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨Or.inl rfl, by rw [hTroots]; exact hI.roots,
        topInv_mono hI.top (by simpa using hWok.next) (by tomega)⟩
    · obtain ⟨h1, h2⟩ := topInv_new (r := r') hI.top (by simpa using hWok.next) (show i - 1 < i by tomega)
      refine ⟨h1, ?_, h2⟩
      rw [hTroots]
      show s.roots ++ [(i, r')] = rootsOf (tp ++ [(acc2.next, newTopNode tp i r')])
      rw [rootsOf_snoc, newTopNode_time, newTopNode_root, hI.roots]
  -- the state after
  have hshT : Shaped cf T 0 (htIn cf T r') r' := by
    have : htIn cf T r' = hh := by simp [htIn, hnr, hlev, htOf_lev cf hHt]
    rw [this]; exact ht.shaped
  have hsokT : SOk cf (i + 1) T := by
    intro x nk hx
    rcases hcases x with ⟨ob, hm, hx'⟩ | ⟨_, hx'⟩
    · rw [hx] at hx'
      have hob : ob = .key nk := (Option.some.inj hx').symm
      obtain ⟨h1, h2⟩ := hnok (x, ob) hm nk hob
      exact ⟨h1, h2, fun u hu => Nat.lt_succ_of_le (hWok.times (x, ob) hm nk hob u hu)⟩
    · rw [hx] at hx'
      obtain ⟨h1, h2, h3⟩ := hsok x nk hx'.symm
      exact ⟨nodeOk_transfer h1 hafter.exist, h2, fun u hu => Nat.lt_succ_of_lt (h3 u hu)⟩
  have hfreshT : ∀ x, o.next ≤ x → T.obj x = none := by
    intro x hx
    rcases hcases x with ⟨ob, hm, _⟩ | ⟨_, hx'⟩
    · exfalso
      have hwn : next ≤ acc2.next := by simpa using hWok.next
      rcases hWok.ids x (List.mem_map_of_mem (f := (·.1)) hm) with h | h
      · have h2 : x < acc2.next := h.2
        exact absurd (Nat.lt_of_lt_of_le h2 hnext) (Nat.not_lt.mpr hx)
      · have := hfreshR x h
        exact absurd (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le this hwn) hnext) (Nat.not_lt.mpr hx)
    · rw [hx']
      have hwn : next ≤ acc2.next := by simpa using hWok.next
      exact hI.fresh x (Nat.le_trans hwn (Nat.le_trans hnext hx))
  exact ⟨⟨hc12, hframe⟩, by rw [hTat]; exact htreeT, htop.1, htop.2.1,
    { inv := hinvT, tree := htreeT, shaped := ⟨r', hTroot, hshT⟩, sok := hsokT, fresh := hfreshT,
      top := htop.2.2, roots := htop.2.1 }⟩

/-- A state PE keeps at time 0 is the tree at time 0. -/
theorem inv_at_zero {s : Tree} {tp : Top} {nx : NodeId} (h : Inv cf 0 s tp nx) : s.at 0 = s := by
  apply tree_at_self
  · intro x n hx u hu
    exact Nat.le_of_lt_succ ((h.sok x n hx).2.2 u hu)
  · rw [h.roots]; exact roots_times h.top

/-- **Every history PE writes meets the contract with TREE and the top**
(`MeetsTop`, so the theorems on reads apply, TheoremsTop.lean), from any start
state that PE keeps (`Inv` at time 0) whose tree is a start tree of the
contract (`Start`) with a start top (`TopStart`); and PE keeps its state at
the end. -/
theorem pe_meetsTop (hcf : cf.Ok) {s0 : Tree} {tp0 : Top} {nx0 : NodeId}
    (h0 : Inv cf 0 s0 tp0 nx0) (hst : Start cf.params s0) (htop : TopStart tp0) :
    ∀ {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId}, PeHist cf s0 tp0 nx0 txs s tp nx →
      MeetsTop cf.params txs s tp ∧ Inv cf txs.length s tp nx
  | _, _, _, _, .start => by
    refine ⟨MeetsTop.start s0 tp0 hst ?_ htop h0.roots, h0⟩
    rw [inv_at_zero h0]; exact h0.tree
  | _, _, _, _, .step (txs := txs) (s := s) (tp := tp) (nx := nx) (ops := ops) (o := o) hh hw => by
    obtain ⟨hm, hI⟩ := pe_meetsTop hcf h0 hst htop hh
    have hI' : Inv cf (txs.length + 1 - 1) s tp nx := by simpa using hI
    obtain ⟨hc, ht, hts, hr, hI2⟩ := pe_step hcf (Nat.succ_pos _) hI' hw
    refine ⟨MeetsTop.step txs s tp ops o.D (o.tree s) o.top hm hc ht hts hr, ?_⟩
    simpa using hI2

/-- Every history PE writes meets the writer's contract (`Meets`, so the
theorems on gets and scans at every time apply, Theorems.lean). -/
theorem pe_meets (hcf : cf.Ok) {s0 : Tree} {tp0 : Top} {nx0 : NodeId}
    (h0 : Inv cf 0 s0 tp0 nx0) (hst : Start cf.params s0) (htop : TopStart tp0)
    {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId}
    (hh : PeHist cf s0 tp0 nx0 txs s tp nx) : Meets cf.params txs s :=
  (pe_meetsTop hcf h0 hst htop hh).1.meets

/-! ## The start: the empty tree -/

theorem startTree_root : (startTree cf).root = some 1 := rfl

theorem startTree_obj1 : (startTree cf).obj 1 = some (.key ⟨cf.lev 0 0, true, [.time 0]⟩) := rfl

theorem startTree_obj_ne {x : NodeId} (hx : x ≠ 1) : (startTree cf).obj x = none := by
  simp [startTree, hx]

theorem start_live : live [Klong.time 0] = [] := rfl

theorem start_wf : klongsWf [Klong.time 0] = true := by decide

theorem start_nodeOk (hcf : cf.Ok) :
    nodeOk cf.params (startTree cf) ⟨cf.lev 0 0, true, [.time 0]⟩ = true := by
  have hM : 1 ≤ cf.M := by have := hcf.h1; have := hcf.hM; omega
  simp [nodeOk, Cfg.params, start_wf, hM]

theorem start_invOk (hcf : cf.Ok) : invOk cf.params (startTree cf) = true := by
  simp only [invOk, startTree_root, startTree_obj1, Bool.true_or, Bool.true_and]
  simp only [walk, startTree_obj1, start_nodeOk hcf, start_live, kidsOk, Bool.and_true]

theorem start_reach : reach (startTree cf) = [1] := by
  simp [reach, startTree_root, Tree.fuel, startTree_obj1, reachAt, start_live]

/-- **The start**: the empty tree of PE (an empty segment leaf, the start top
node, the next id 3) is a state PE keeps, a start tree of the contract, and a
start top. -/
theorem start_inv (hcf : cf.Ok) :
    Inv cf 0 (startTree cf) startTop startNext ∧ Start cf.params (startTree cf) ∧ TopStart startTop := by
  have hat : (startTree cf).at 0 = startTree cf := by
    apply tree_at_self
    · intro x n hx u hu
      by_cases h1 : x = 1
      · subst h1
        rw [startTree_obj1] at hx
        cases hx
        simp at hu
        rw [hu]
      · rw [startTree_obj_ne h1] at hx; cases hx
    · intro r hr
      simp [startTree] at hr
      rw [hr]
  refine ⟨{ inv := start_invOk hcf, tree := ?_, shaped := ?_, sok := ?_, fresh := ?_,
            top := topInv_start.2, roots := rfl }, ⟨?_, ?_⟩, topInv_start.1⟩
  · unfold Contract.TreeOk; rw [start_reach]; simp
  · refine ⟨1, startTree_root, ?_⟩
    have : htIn cf (startTree cf) 1 = 0 := by
      simp [htIn, startTree_obj1, Cfg.htOf, Cfg.lev]
    rw [this]
    exact Shaped.leaf startTree_obj1 rfl rfl (Nat.zero_le _) (by simp [start_live])
  · intro x n hx
    by_cases h1 : x = 1
    · subst h1
      rw [startTree_obj1] at hx
      cases hx
      refine ⟨start_nodeOk hcf, by simp, ?_⟩
      intro u hu
      simp at hu
      rw [hu]; exact Nat.zero_lt_one
    · rw [startTree_obj_ne h1] at hx; cases hx
  · intro x hx
    apply startTree_obj_ne
    intro h; rw [h] at hx; simp [startNext] at hx
  · rw [hat]; exact start_invOk hcf
  · rw [hat]
    simp [contents, startTree_root, Tree.fuel, startTree_obj1]
    cases cf.lev 0 0 <;> simp [listAt, startTree_obj1, start_live]

/-- **Every history PE writes from the empty tree meets the contract with
TREE and the top** (`MeetsTop`), so every get and scan, through the top too,
is right at every time of it (TheoremsTop.lean). -/
theorem pe_meetsTop_start (hcf : cf.Ok) {txs : List (List Op)} {s : Tree} {tp : Top} {nx : NodeId}
    (hh : PeHist cf (startTree cf) startTop startNext txs s tp nx) : MeetsTop cf.params txs s tp :=
  let ⟨h0, hst, htop⟩ := start_inv hcf
  (pe_meetsTop hcf h0 hst htop hh).1

end Contract.PE
