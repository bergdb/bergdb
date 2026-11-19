/-
bergdb 030-21, part 2: PE's transaction meets the bridge's computed clauses
(Bridge.lean, sections 3.2 to 3.4) with its change in the model's words
(`peChange`, Contract/PeRecord.lean): `pe_bridge`.

For one transaction at time i that PE accepts, from a state PE keeps (`Inv`
at i - 1) whose tree also meets `InvB` (node 0 is no node of it; every key
node meets W5 and A4), and whose operations have distinct keys:

* N: the nodes made are the fresh ids written, with their levels and kinds,
  and the new top node, on the top nodes' level or above and no node of the
  tree; every node of the tree after that is no node of the tree before is
  made (`Made`).
* K: each node written gets, in order, the entries of the klongs it got
  (`newVals`); the root (node 0) and the new top node are no nodes of the
  tree.
* F4, W, A4 for the nodes written: the forms of the writes (`seg_space_form`,
  `WForm`: an appended base gets `emitKs`, more than the time klong; a fresh
  key node `newKs`), W5 kept by emit (`fullOk_emitKs`), A4 for the old klongs
  from `InvB` and for the live ones from the sound tree after
  (`rch_live_low`).
* A2, A3: every node written is reached from the new space root
  (`seg_space_rch`, which needs the distinct keys); A5: every node reached
  after was reached before or is a fresh id written (the reach bound of
  `seg_space`).
* `InvB` holds of the tree after (`invB_start`: of PE's empty tree).

For runs and histories: `pe_bridge_run` (every transaction of a run of PE,
`peRun`), `pe_bridge_hist` (every transaction of PE's history from the empty
tree, `peHist`), `pe_bridge_hist_full` (the same with the history's own top
nodes' level, `h.topLevel`, as `MeetsFull.step` asks: `bridgeOk_mono`,
`peHist_topLevel`).

The premise of distinct keys is needed: with two puts of one key, the first
put's value is written and never reached (A2 and A3 fail). Java's Dag keeps
one operation a key.
-/
import Contract.PeRecord
import Contract.Proof.PeTx
import Contract.Proof.PeBridgeKs

namespace Contract.PE

open PeProof PeProof.Abs PeProof.Keys
open SIS (Changes NewNode)
open SIS.Check (BVal)

variable {cf : Cfg}

/-! ## What PE keeps for the bridge -/

/-- What the tree before a transaction keeps for the bridge's clauses, beyond
`Inv`. -/
structure InvB (cf : Cfg) (s : Tree) : Prop where
  /-- Node 0 is no node of the tree: it is the model's root (`c0`), which gets
  the entry of every new top node. -/
  zero : s.obj 0 = none
  /-- W5 for every key node: a bitmap's new bit deletes every key klong before
  it of the same compare value (`fullOk`). -/
  full : ∀ x n, s.obj x = some (.key n) → fullOk n.ks = true
  /-- A4 for every key node: every key klong of it, live or dead, names a node
  on a lower level (`ptrsLow`). -/
  low : ∀ x n, s.obj x = some (.key n) → ptrsLow s n = true

theorem ptrsLow_iff {s : Tree} {n : KNode} : ptrsLow s n = true ↔
    ∀ c y, Klong.key c y ∈ n.ks → ∃ o, s.obj y = some o ∧ lvl o < n.level := by
  unfold ptrsLow
  rw [List.all_eq_true]
  constructor
  · intro h c y hk
    have h1 := h _ hk
    simp only at h1
    split at h1
    · rename_i o ho
      exact ⟨o, ho, by simpa using h1⟩
    · cases h1
  · intro h k hk
    cases k with
    | key c y =>
      obtain ⟨o, ho, hl⟩ := h c y hk
      simp [ho, hl]
    | time _ => rfl
    | del _ => rfl

/-- **The start**: PE's empty tree meets `InvB`. -/
theorem invB_start (_hcf : cf.Ok) : InvB cf (startTree cf) := by
  refine ⟨startTree_obj_ne (by decide), fun x n hx => ?_, fun x n hx => ?_⟩
  · by_cases h1 : x = 1
    · subst h1
      rw [startTree_obj1] at hx
      cases hx
      exact fullOk_start
    · rw [startTree_obj_ne h1] at hx; cases hx
  · by_cases h1 : x = 1
    · subst h1
      rw [startTree_obj1] at hx
      cases hx
      rfl
    · rw [startTree_obj_ne h1] at hx; cases hx

/-! ## Lists -/

theorem pairs_filter (f : NodeId → List BVal) (x : NodeId) :
    ∀ xs : List NodeId, ((xs.flatMap (fun y => (f y).map (fun v => (y, v)))).filter
      (fun a => a.1 == x)).map (·.2) = (xs.filter (· == x)).flatMap f
  | [] => rfl
  | y :: ys => by
    rw [List.flatMap_cons, List.filter_append, List.map_append, pairs_filter f x ys,
      List.filter_cons]
    by_cases h : y = x
    · subst h
      simp [List.filter_map, Function.comp_def]
    · have : (y == x) = false := by simpa using h
      simp [List.filter_map, Function.comp_def, this]

theorem filter_beq_single {xs : List NodeId} (hnd : xs.Nodup) {x : NodeId} (hx : x ∈ xs) :
    xs.filter (· == x) = [x] := by
  rw [List.filter_beq, List.count_eq_one_of_mem hnd hx]
  rfl

/-! ## PE's change, split -/

/-- The nodes made among the nodes written xs: the fresh ones. -/
def wNew (s T : Tree) (xs : List NodeId) : List NewNode :=
  (xs.filter (fun x => (s.obj x).isNone)).map (fun x => ⟨x, lvlOf T x, isDataOf T x⟩)

/-- The entries added to the nodes written xs. -/
def wAdds (s T : Tree) (xs : List NodeId) : List (NodeId × BVal) :=
  xs.flatMap (fun x => (newVals s T x).map (fun v => (x, v)))

theorem wNew_ids (s T : Tree) (xs : List NodeId) :
    (wNew s T xs).map (·.id) = xs.filter (fun x => (s.obj x).isNone) := by
  simp [wNew, Function.comp_def]

/-- PE's change: the nodes written, then the new top node if any (on the top
nodes' level or above, a key node), and the root's entry for it and its own. -/
theorem peChange_split (cf : Cfg) (s : Tree) (tp : Top) (o : Out) :
    ∃ N2 A2, (peChange cf s tp o).new = wNew s (o.tree s) (o.ws.map (·.1)).reverse ++ N2 ∧
      (peChange cf s tp o).adds = wAdds s (o.tree s) (o.ws.map (·.1)).reverse ++ A2 ∧
      N2.length ≤ 1 ∧
      (∀ nn ∈ N2, (∃ nd, newTopOf tp o = some (nn.id, nd)) ∧ cf.topBase ≤ nn.level ∧
        nn.isData = false) ∧
      (∀ a ∈ A2, a.1 = 0 ∨ a.1 ∈ N2.map (·.id)) := by
  unfold peChange
  rcases h : newTopOf tp o with _ | ⟨z, nd⟩
  · exact ⟨[], [], by simp [wNew], by simp [wAdds], by simp, by simp, by simp⟩
  · refine ⟨[⟨z, cf.topBase + tp.length, false⟩],
      (0, BVal.top z) :: (topVals nd).map (fun v => (z, v)), rfl, rfl, by simp, ?_, ?_⟩
    · intro nn hnn
      simp only [List.mem_singleton] at hnn
      subst hnn
      exact ⟨⟨nd, rfl⟩, Nat.le_add_right _ _, rfl⟩
    · intro a ha
      simp only [List.mem_cons, List.mem_map] at ha
      rcases ha with rfl | ⟨w, _, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (by simp)

/-! ## The transaction -/

/-- **PE's transaction meets the bridge's computed clauses** (N, K, F4, W,
A4, A2, A3, A5: `bridgeOk`, with the new top node on the start top node's
level or above) and N's rest (`Made`), with its change in the model's words
(`peChange`), and keeps `InvB`: from a state PE keeps at i - 1 (`Inv`) whose
tree meets `InvB`, for operations of distinct keys. -/
theorem pe_bridge (hcf : cf.Ok) {i : Time} (hi : 1 ≤ i) {s : Tree} {tp : Top} {next : NodeId}
    {ops : List Op} {o : Out} (hI : Inv cf (i - 1) s tp next) (hB : InvB cf s)
    (hkeys : (ops.map Op.key).Nodup) (hw : peTx cf i s tp next ops = some o) :
    bridgeOk cf.topBase i s (o.tree s) o.D (peChange cf s tp o) = true ∧
      Made s (o.tree s) (peChange cf s tp o) ∧ InvB cf (o.tree s) := by
  obtain ⟨hok, r, n, v, acc1, v', c0, r', acc2, hr, hn, hp, hsr, he, hout⟩ := peTx_spec hw
  have hi1 : i - 1 + 1 = i := by tomega
  have hsok : SOk cf i s := hi1 ▸ hI.sok
  have hgood : Good s r 0 none := good_of_invOk hr hI.inv
  have hnd : (R s r).Nodup := by
    have := hI.tree; unfold Contract.TreeOk at this; rwa [reach_eq_R hr] at this
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
  have hkeys' : ((dropNoops cf ops).map Op.key).Nodup :=
    hkeys.sublist ((List.filter_sublist).map _)
  obtain ⟨W, hWok, hold, hT⟩ := seg_space hcf hpre (hht ▸ hp) hsr he
  obtain ⟨W2, hW2, hform⟩ := seg_space_form hcf hpre (hht ▸ hp) hsr he
  obtain ⟨W3, hW3, hrch⟩ := seg_space_rch hcf hpre hkeys' (hht ▸ hp) hsr he
  have hws : acc2.ws = W := by simpa using hWok.ws
  have hW2W : W2 = W := by rw [← hws, hW2]; simp
  have hW3W : W3 = W := by rw [← hws, hW3]; simp
  rw [hW2W] at hform
  rw [hW3W] at hrch
  have hows : o.ws = W := by rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> exact hws
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
  have hTroot : T.root = some r' := by
    rcases hout with ⟨heq, rfl⟩ | ⟨_, rfl⟩
    · show s.root = some r'
      rw [hr, heq]
    · show (s.roots ++ [(i, r')]).getLast?.map (·.2) = some r'
      simp
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
  have hreachT : reach T = R T r' := reach_eq_R hTroot
  have hreachS : reach s = R s r0 := reach_eq_R hr
  obtain ⟨nr, hnr, hlev, _, _, _⟩ := shaped_obj ht.shaped
  have hRT : R T r' = reachAt T (cf.lev 0 hh + 1) r' := by simp [R, Tree.fuel, hnr, hlev]
  have hsub := ht.reach _ (le_refl _)
  rw [← hRT] at hsub
  -- the nodes written
  have hWnd : (W.map (·.1)).Nodup := hWok.nodup
  have hfreshR : ∀ z ∈ R s r0, z < next := by
    intro z hz
    have hz' := reach_exists _ hgood z hz
    by_contra hc
    exact hz' (hI.fresh z (Nat.le_of_not_lt hc))
  have hRex : ∀ z ∈ R s r0, s.obj z ≠ none := reach_exists _ hgood
  have hnext0 : 0 < next := Nat.lt_of_le_of_lt (Nat.zero_le _)
    (hfreshR r0 (mem_reachAt_self' _ _ _))
  have hwn : next ≤ acc2.next := by simpa using hWok.next
  have hWids : ∀ w ∈ W.map (·.1), (next ≤ w ∧ w < acc2.next) ∨ w ∈ R s r0 := by
    intro w hw'
    simpa using hWok.ids w hw'
  have hTW : ∀ x ob, (x, ob) ∈ W → T.obj x = some ob := by
    intro x ob hm
    rw [hTobj]
    exact applyWs_obj_of_mem hWok.nodup hm
  have hTN : ∀ x, x ∉ W.map (·.1) → T.obj x = s.obj x := by
    intro x hx
    rw [hTobj]
    exact applyWs_obj_of_not hx
  have hmemW : ∀ x, x ∈ W.map (·.1) → ∃ ob, (x, ob) ∈ W := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    exact ⟨p.2, hp⟩
  have hWT : ∀ x, x ∈ W.map (·.1) → T.obj x ≠ none := by
    intro x hx
    obtain ⟨ob, hm⟩ := hmemW x hx
    rw [hTW x ob hm]
    simp
  -- node 0 and the new top node's id are no nodes of T
  have h0W : (0 : NodeId) ∉ W.map (·.1) := by
    intro h0
    rcases hWids 0 h0 with ⟨h1, _⟩ | h1
    · tomega
    · exact hRex 0 h1 hB.zero
  have hT0 : T.obj 0 = none := by rw [hTN 0 h0W]; exact hB.zero
  have hzW : acc2.next ∉ W.map (·.1) := by
    intro hz
    rcases hWids _ hz with ⟨_, h2⟩ | h1
    · tomega
    · have := hfreshR _ h1; tomega
  have hsz : s.obj acc2.next = none := hI.fresh _ hwn
  have hTz : T.obj acc2.next = none := by rw [hTN _ hzW]; exact hsz
  have hztop : ∀ z nd, newTopOf tp o = some (z, nd) → z = acc2.next := by
    intro z nd hz
    unfold newTopOf at hz
    rcases hout with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · simp at hz
    · simp only [List.length_append, List.length_singleton, List.getLast?_append,
        List.getLast?_singleton, Option.some_or] at hz
      split at hz
      · omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at hz
        exact hz.1.symm
  -- every node written is reached
  have hreachW : ∀ x ∈ W.map (·.1), x ∈ reach T := by
    intro x hx
    rw [hreachT]
    exact rch_reachAt ht.good ht.shaped (hrch T hafter x hx) _ (le_refl _)
  -- levels are kept
  have hLP : ∀ y o', s.obj y = some o' → ∃ o'', T.obj y = some o'' ∧ lvl o'' = lvl o' := by
    intro y o' hy
    by_cases hyW : y ∈ W.map (·.1)
    · obtain ⟨ob, hm⟩ := hmemW y hyW
      refine ⟨ob, hTW y ob hm, ?_⟩
      rcases hform (y, ob) hm with ⟨hs0, _⟩ | ⟨n0, F, hs0, hob, _, _⟩
      · simp only at hs0; rw [hy] at hs0; cases hs0
      · simp only at hs0 hob
        rw [hy] at hs0
        cases hs0
        rw [hob]
        rfl
    · exact ⟨o', by rw [hTN y hyW, hy], rfl⟩
  have hlow_old : ∀ m : KNode, ptrsLow s m = true →
      ∀ c y, Klong.key c y ∈ m.ks → ∃ o', T.obj y = some o' ∧ lvl o' < m.level := by
    intro m hm c y hk
    obtain ⟨o1, ho1, hl1⟩ := ptrsLow_iff.mp hm c y hk
    obtain ⟨o2, ho2, hl2⟩ := hLP y o1 ho1
    exact ⟨o2, ho2, hl2 ▸ hl1⟩
  have hlow_live : ∀ x m, x ∈ W.map (·.1) → T.obj x = some (.key m) →
      ∀ c y, (c, y) ∈ live m.ks → ∃ o', T.obj y = some o' ∧ lvl o' < m.level :=
    fun x m hx hxm => rch_live_low ht.good ht.shaped (hrch T hafter x hx) hxm
  -- a key node written: F4, W5, A4
  have hWnode : ∀ x ob, (x, ob) ∈ W → ∀ m, ob = .key m →
      ((∃ n0, s.obj x = some (.key n0) ∧ extKs4 i n0.ks m.ks = true) ∨
        (s.obj x = none ∧ madeKs i m.ks = true)) ∧
      fullOk m.ks = true ∧ ptrsLow T m = true := by
    intro x ob hm m hob
    have hxW : x ∈ W.map (·.1) := List.mem_map.mpr ⟨_, hm, rfl⟩
    have hTx : T.obj x = some (.key m) := hob ▸ hTW x ob hm
    rcases hform (x, ob) hm with ⟨hs0, hv | ⟨l, b, F, hk, hlive⟩⟩ | ⟨n0, F, hs0, hk, hlive, hne⟩
    · obtain ⟨v0, hv0⟩ := hv
      simp only at hv0
      rw [hv0] at hob
      cases hob
    · simp only at hs0 hk
      rw [hk] at hob
      cases hob
      refine ⟨Or.inr ⟨hs0, madeKs_newKs i F⟩, fullOk_newKs i F, ptrsLow_iff.mpr ?_⟩
      intro c y hky
      have hcy : (c, y) ∈ F := by
        simp only [newKs, keysOf, List.mem_cons, List.mem_map] at hky
        rcases hky with h | ⟨e, he, h⟩
        · cases h
        · injection h with h1 h2
          subst h1 h2
          exact he
      exact hlow_live x _ hxW hTx c y (by rw [hlive]; exact hcy)
    · simp only at hs0 hk
      rw [hk] at hob
      cases hob
      obtain ⟨hok0, _, _⟩ := hsok x n0 hs0
      have hwf0 : klongsWf n0.ks = true := (nodeOk_iff.mp hok0).2.1
      refine ⟨Or.inl ⟨n0, hs0, extKs4_emitKs hne⟩, fullOk_emitKs hwf0 (hB.full x n0 hs0) i F,
        ptrsLow_iff.mpr ?_⟩
      intro c y hky
      rcases List.mem_append.mp hky with hky | hky
      · exact hlow_old n0 (hB.low x n0 hs0) c y hky
      · exact hlow_live x _ hxW hTx c y (by rw [hlive]; exact emitKs_ptrs hky)
  -- W5 and A4 for every key node of T
  have hfullT : ∀ x m, T.obj x = some (.key m) → fullOk m.ks = true ∧ ptrsLow T m = true := by
    intro x m hx
    by_cases hxW : x ∈ W.map (·.1)
    · obtain ⟨ob, hm⟩ := hmemW x hxW
      have hob : ob = .key m := by rw [hTW x ob hm] at hx; exact Option.some.inj hx
      exact (hWnode x ob hm m hob).2
    · rw [hTN x hxW] at hx
      exact ⟨hB.full x m hx, ptrsLow_iff.mpr (hlow_old m (hB.low x m hx))⟩
  -- the change
  obtain ⟨N2, A2, hnew, hadds, hN2len, hN2, hA2⟩ := peChange_split cf s tp o
  rw [hows] at hnew hadds
  set c := peChange cf s tp o with hc
  have hN2id : ∀ nn ∈ N2, nn.id = acc2.next := by
    intro nn hnn
    obtain ⟨⟨nd, h⟩, _, _⟩ := hN2 nn hnn
    exact hztop _ _ h
  have hN2ids : ∀ x ∈ N2.map (·.id), x = acc2.next := by
    intro x hx
    obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hx
    exact hN2id nn hnn
  have hnewids : c.new.map (·.id) =
      (W.map (·.1)).reverse.filter (fun x => (s.obj x).isNone) ++ N2.map (·.id) := by
    rw [hnew, List.map_append, wNew_ids]
  have hnewof : ∀ x, x ∈ W.map (·.1) → s.obj x = none → ∃ nn ∈ c.new, nn.id = x := by
    intro x hx hsx
    have : x ∈ c.new.map (·.id) := by
      rw [hnewids]
      exact List.mem_append_left _ (List.mem_filter.mpr ⟨List.mem_reverse.mpr hx, by simp [hsx]⟩)
    obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp this
    exact ⟨nn, hnn, rfl⟩
  have hnewz : ∀ nn ∈ c.new, (nn.id ∈ W.map (·.1) ∧ s.obj nn.id = none ∧
      nn = ⟨nn.id, lvlOf T nn.id, isDataOf T nn.id⟩) ∨ nn ∈ N2 := by
    intro nn hnn
    rw [hnew, List.mem_append] at hnn
    rcases hnn with hnn | hnn
    · left
      simp only [wNew, List.mem_map, List.mem_filter, List.mem_reverse] at hnn
      obtain ⟨x, ⟨hx, hsx⟩, rfl⟩ := hnn
      exact ⟨List.mem_map.mpr hx, by simpa using hsx, rfl⟩
    · exact Or.inr hnn
  have haddsz : ∀ a ∈ c.adds, a.1 ∈ W.map (·.1) ∨ a.1 = 0 ∨ a.1 = acc2.next := by
    intro a ha
    rw [hadds, List.mem_append] at ha
    rcases ha with ha | ha
    · left
      simp only [wAdds, List.mem_flatMap, List.mem_map, List.mem_reverse] at ha
      obtain ⟨x, hx, w, _, rfl⟩ := ha
      exact List.mem_map.mpr hx
    · right
      rcases hA2 a ha with h | h
      · exact Or.inl h
      · exact Or.inr (hN2ids _ h)
  -- clause K at a node written
  have hK : ∀ x ∈ W.map (·.1), (c.adds.filter (fun a => a.1 == x)).map (·.2) = newVals s T x := by
    intro x hx
    have hxs : x ∈ (W.map (·.1)).reverse := List.mem_reverse.mpr hx
    have hx0 : x ≠ 0 := fun h => h0W (h ▸ hx)
    have hxz : x ≠ acc2.next := fun h => hzW (h ▸ hx)
    rw [hadds, List.filter_append, List.map_append]
    have hA2nil : A2.filter (fun a => a.1 == x) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      rcases hA2 a ha with h | h
      · rw [h]; simpa using hx0.symm
      · rw [hN2ids _ h]; simpa using hxz.symm
    rw [hA2nil, List.map_nil, List.append_nil]
    unfold wAdds
    rw [pairs_filter, filter_beq_single (List.nodup_reverse.mpr hWnd) hxs]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  refine ⟨?_, ?_, ⟨hT0, fun x m hx => (hfullT x m hx).1, fun x m hx => (hfullT x m hx).2⟩⟩
  · simp only [bridgeOk, Bool.and_eq_true, hTat, hsat]
    refine ⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · -- N
      simp only [newsOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨?_, ?_⟩
      · rw [hnewids, List.nodup_append]
        refine ⟨(List.nodup_reverse.mpr hWnd).filter _, ?_, ?_⟩
        · match N2, hN2len with
          | [], _ => exact List.nodup_nil
          | [_], _ => exact List.nodup_singleton _
        · intro a ha b hb hab
          subst hab
          have := hN2ids _ hb
          subst this
          exact hzW (List.mem_reverse.mp (List.mem_filter.mp ha).1)
      · intro nn hnn
        rcases hnewz nn hnn with ⟨hx, hsx, heq⟩ | hn2
        · rw [heq]
          simp only [hsx, Option.isNone_none]
          obtain ⟨ob, hm⟩ := hmemW _ hx
          have hTx := hTW _ ob hm
          cases ob with
          | key m => simp [hTx, lvlOf, isDataOf, lvl]
          | val w => simp [hTx, lvlOf, isDataOf, lvl]
        · rw [hN2id nn hn2, hsz, hTz]
          obtain ⟨_, hl, hd⟩ := hN2 nn hn2
          simp [hl, hd]
    · -- K
      simp only [addsOk, List.all_eq_true]
      intro x hx
      by_cases hxT : T.obj x = none
      · simp [hxT]
      · have hxW : x ∈ W.map (·.1) := by
          rw [List.mem_append, List.mem_append] at hx
          rcases hx with (hx | hx) | hx
          · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
            rcases haddsz a ha with h | h | h
            · exact h
            · exact absurd (h ▸ hT0) hxT
            · exact absurd (h ▸ hTz) hxT
          · simpa [Out.D, hows] using hx
          · obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hx
            rcases hnewz nn hnn with ⟨h, _, _⟩ | h
            · exact h
            · exact absurd (hN2id nn h ▸ hTz) hxT
        rw [hK x hxW]
        simp
    · -- F4, W, A4
      simp only [localOk, List.all_eq_true]
      intro x hx
      have hxW : x ∈ W.map (·.1) := by simpa [Out.D, hows] using hx
      obtain ⟨ob, hm⟩ := hmemW x hxW
      have hTx := hTW x ob hm
      cases ob with
      | val w => simp [hTx]
      | key m =>
        obtain ⟨hf4, hfull, hlow⟩ := hWnode x _ hm m rfl
        have hwf : klongsWf m.ks = true := (nodeOk_iff.mp (hnok (x, .key m) hm m rfl).1).2.1
        rcases hf4 with ⟨n0, hs0, h4⟩ | ⟨hs0, h4⟩
        · simp [hTx, hs0, h4, hwf, hfull, hlow]
        · simp [hTx, hs0, h4, hwf, hfull, hlow]
    · -- A2
      simp only [currentOk, List.all_eq_true]
      intro a ha
      rcases haddsz a ha with h | h | h
      · obtain ⟨ob, hm⟩ := hmemW _ h
        rw [hTW _ ob hm]
        simpa using hreachW _ h
      · rw [h, hT0]
        simp
      · rw [h, hTz]
        have : ∃ nn ∈ N2, nn.id = acc2.next := by
          have ha' := ha
          rw [hadds, List.mem_append] at ha'
          rcases ha' with ha' | ha'
          · have : a.1 ∈ W.map (·.1) := by
              simp only [wAdds, List.mem_flatMap, List.mem_map, List.mem_reverse] at ha'
              obtain ⟨x, hx, w, _, rfl⟩ := ha'
              exact List.mem_map.mpr hx
            exact absurd (h ▸ this) hzW
          · rcases hA2 a ha' with h0 | h0
            · exfalso; rw [h] at h0; tomega
            · obtain ⟨nn, hnn, he⟩ := List.mem_map.mp h0
              exact ⟨nn, hnn, he.trans h⟩
        obtain ⟨nn, hnn, he⟩ := this
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
        right
        exact ⟨nn, by rw [hnew]; exact List.mem_append_right _ hnn, he⟩
    · -- A3
      simp only [madeOk, List.all_eq_true]
      intro nn hnn
      rcases hnewz nn hnn with ⟨hx, _, _⟩ | hn2
      · simpa using Or.inr (hreachW _ hx)
      · rw [hN2id nn hn2, hTz]
        simp
    · -- A5
      simp only [noResOk, List.all_eq_true]
      intro y hy
      rw [hreachT] at hy
      have hyT : T.obj y ≠ none := reach_exists _ ht.good y hy
      rcases List.mem_append.mp (hsub.subset hy) with hyS | hyF
      · simp [hreachS, hyS]
      · rw [List.mem_range'_1] at hyF
        have hsy : s.obj y = none := hI.fresh y hyF.1
        have hyW : y ∈ W.map (·.1) := by
          by_contra hn'
          exact hyT (by rw [hTN y hn', hsy])
        obtain ⟨nn, hnn, he⟩ := hnewof y hyW hsy
        simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
        right
        exact ⟨nn, hnn, he⟩
  · -- Made
    intro x hsx hTx
    have hxW : x ∈ W.map (·.1) := by
      by_contra hn'
      rw [hTN x hn', hsx] at hTx
      cases hTx
    obtain ⟨nn, hnn, he⟩ := hnewof x hxW hsx
    exact List.mem_map.mpr ⟨nn, hnn, he⟩

/-! ## Runs and histories -/

/-- The bridge's clauses with a lower top nodes' level: only N's level of a
top node depends on it. -/
theorem bridgeOk_mono {t t' : Nat} (htt : t ≤ t') {i : Nat} {s s' : Tree} {D : List NodeId}
    {c : Changes BVal} (hb : bridgeOk t' i s s' D c = true) : bridgeOk t i s s' D c = true := by
  simp only [bridgeOk, Bool.and_eq_true] at hb ⊢
  refine ⟨⟨⟨⟨⟨?_, hb.1.1.1.1.2⟩, hb.1.1.1.2⟩, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  have hn := hb.1.1.1.1.1
  simp only [newsOk, Bool.and_eq_true, List.all_eq_true] at hn ⊢
  refine ⟨hn.1, fun nn hnn => ?_⟩
  have h1 := hn.2 nn hnn
  refine ⟨h1.1, ?_⟩
  have h2 := h1.2
  revert h2
  cases s'.obj nn.id with
  | none =>
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact fun h => ⟨Nat.le_trans htt h.1, h.2⟩
  | some ob => cases ob <;> exact id

theorem bhist_tree_cons (s : Tree) (c : Changes BVal) (tx : BTx) (txs : List BTx) :
    ∀ j, j ≤ txs.length →
      (⟨s, c, tx :: txs⟩ : BHist).tree (j + 1) = (⟨tx.s, c, txs⟩ : BHist).tree j
  | 0, _ => rfl
  | j + 1, hj => by
    have hj' : j < txs.length := by omega
    simp only [BHist.tree, List.getElem?_cons_succ, List.getElem?_eq_getElem hj']

/-- **Every run of PE meets the bridge's computed clauses and N's rest**, at
every transaction, and keeps `InvB`: from a state PE keeps at time t whose
tree meets `InvB`, for transactions each of distinct keys, the run's
transactions at t + 1, t + 2, ... (`peRun`), as a history from s. -/
theorem pe_bridge_run (hcf : cf.Ok) (c0' : Changes BVal) :
    ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId) (t : Time)
      (L : List (BTx × Top)), Inv cf t s tp nx → InvB cf s →
      (∀ ops ∈ txs, (ops.map Op.key).Nodup) → peRun cf s tp nx t txs = some L →
      ∀ j (hj : j < L.length),
        bridgeOk cf.topBase (t + j + 1) ((⟨s, c0', L.map (·.1)⟩ : BHist).tree j)
          ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1.D L[j].1.c = true ∧
        Made ((⟨s, c0', L.map (·.1)⟩ : BHist).tree j)
          ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1)) L[j].1.c ∧
        InvB cf ((⟨s, c0', L.map (·.1)⟩ : BHist).tree (j + 1))
  | [], s, tp, nx, t, L, _, _, _, hr => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    intro j hj
    simp at hj
  | ops :: rest, s, tp, nx, t, L, hI, hB, hk, hr => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o hw
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      have hI' : Inv cf (t + 1 - 1) s tp nx := by simpa using hI
      have hko : (ops.map Op.key).Nodup := hk ops List.mem_cons_self
      obtain ⟨hb, hmade, hB'⟩ := pe_bridge hcf (Nat.succ_pos t) hI' hB hko hw
      obtain ⟨_, _, _, _, hI2⟩ := pe_step hcf (Nat.succ_pos t) hI' hw
      have ih := pe_bridge_run hcf c0' rest (o.tree s) o.top o.next (t + 1) L' (by simpa using hI2)
        hB' (fun ops' h' => hk ops' (List.mem_cons_of_mem _ h')) hrest
      intro j hj
      cases j with
      | zero => exact ⟨hb, hmade, hB'⟩
      | succ j =>
        have hj' : j < L'.length := by simpa using hj
        obtain ⟨h1, h2, h3⟩ := ih j hj'
        have e1 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1)) j
          (by simp; omega)
        have e2 := bhist_tree_cons s c0' ⟨ops, o.D, o.tree s, peChange cf s tp o⟩ (L'.map (·.1))
          (j + 1) (by simp; omega)
        simp only [List.map_cons] at e1 e2 ⊢
        rw [e1, e2]
        refine ⟨?_, h2, h3⟩
        rw [show t + (j + 1) + 1 = t + 1 + j + 1 by omega]
        exact h1

/-- **Every history PE writes from the empty tree meets the bridge's computed
clauses and N's rest** (`peHist`, the record of 030-21 part 2), for
transactions each of distinct keys, with the start top node's level, and
every tree of it meets `InvB`. -/
theorem pe_bridge_hist (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ∀ j (hj : j < h.txs.length),
      bridgeOk cf.topBase (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true ∧
      Made (h.tree j) (h.tree (j + 1)) h.txs[j].c ∧ InvB cf (h.tree (j + 1)) := by
  unfold peHist at hh
  cases hr : peRun cf (startTree cf) startTop startNext 0 txs with
  | none => rw [hr] at hh; cases hh
  | some L =>
    rw [hr, Option.map_some, Option.some.injEq] at hh
    have hh1 := congrArg Prod.fst hh
    simp only at hh1
    subst hh1
    obtain ⟨h0, _, _⟩ := start_inv hcf
    intro j hj
    have hj' : j < L.length := by simpa using hj
    obtain ⟨h1, h2, h3⟩ := pe_bridge_run hcf (c0 cf) txs _ _ _ 0 L h0 (invB_start hcf) hk hr j hj'
    simp only [List.getElem_map]
    rw [show 0 + j + 1 = j + 1 by omega] at h1
    exact ⟨h1, h2, h3⟩

/-- The model's top nodes' level of PE's history (`BHist.topLevel`, the
level of the primordial top node, at most 2^62) is at most the start top
node's level. -/
theorem start_topLevel (cf : Cfg) (L : List BTx) :
    (⟨startTree cf, c0 cf, L⟩ : BHist).topLevel ≤ cf.topBase := by
  simp [BHist.topLevel, BHist.spec, SIS.Check.bspec, BHist.p0, SIS.Check.topLevelOf,
    SIS.Struct.apply, c0, SIS.Struct.addEntry]

theorem peHist_topLevel {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hh : peHist cf txs = some (h, top)) : h.topLevel ≤ cf.topBase := by
  unfold peHist at hh
  cases hr : peRun cf (startTree cf) startTop startNext 0 txs with
  | none => rw [hr] at hh; cases hh
  | some L =>
    rw [hr, Option.map_some, Option.some.injEq] at hh
    have hh1 := congrArg Prod.fst hh
    simp only at hh1
    subst hh1
    exact start_topLevel cf _

/-- **The bridge's clauses of `MeetsFull.step` for PE's history**: with the
history's own top nodes' level (`h.topLevel`, as `MeetsFull` asks), every
transaction meets `bridgeOk` and `Made`, for transactions each of distinct
keys. -/
theorem pe_bridge_hist_full (hcf : cf.Ok) {txs : List (List Op)} {h : BHist} {top : Nat → Top}
    (hk : ∀ ops ∈ txs, (ops.map Op.key).Nodup) (hh : peHist cf txs = some (h, top)) :
    ∀ j (hj : j < h.txs.length),
      bridgeOk h.topLevel (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true ∧
      Made (h.tree j) (h.tree (j + 1)) h.txs[j].c := by
  intro j hj
  obtain ⟨h1, h2, _⟩ := pe_bridge_hist hcf hk hh j hj
  exact ⟨bridgeOk_mono (peHist_topLevel hh) h1, h2⟩

end Contract.PE
