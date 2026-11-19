/-
bergdb 030-24: PE's writer does not look at the values' hashes. Every read of
the tree before goes through `getKey` (key nodes only), and a value's hash is
only written (`applyGroups`, a put's value node). So:

* two trees with the same key nodes give the same run (`plan_congr` and the
  others: each function of the writer is the same on them);
* mapping the hashes of the operations by any σ maps the hashes of the
  values written by σ, and changes nothing else (`plan_mapH` and the others,
  `peTx_mapH`); in particular every value a transaction writes has the hash of
  one of its puts (`peTx_vals`);
* a history that PE writes is the image, under a map of the hashes, of the
  history it writes from operations with other hashes and the same keys
  (`peRun_mapH`): the same trees but for the values' hashes, the same nodes
  made, the same tops.
-/
import Contract.PeRecord

namespace Contract.PE

/-! ## Hashes mapped -/

/-- An operation with its hash mapped. -/
def opH (σ : Nat → Nat) : Op → Op
  | .put k v => .put k (σ v)
  | .del k => .del k

/-- A node with its hash mapped, if it is a value. -/
def objH (σ : Nat → Nat) : Obj → Obj
  | .val v => .val (σ v)
  | o => o

/-- The writes so far with the values' hashes mapped. -/
def accH (σ : Nat → Nat) (a : Acc) : Acc := ⟨a.ws.map (fun p => (p.1, objH σ p.2)), a.next⟩

/-- A tree with the values' hashes mapped. -/
def treeH (σ : Nat → Nat) (s : Tree) : Tree := ⟨fun x => (s.obj x).map (objH σ), s.roots⟩

/-- What a transaction gives, with the values' hashes mapped. -/
def outH (σ : Nat → Nat) (o : Out) : Out :=
  { o with ws := o.ws.map (fun p => (p.1, objH σ p.2)) }

@[simp] theorem opH_key (σ : Nat → Nat) (op : Op) : (opH σ op).key = op.key := by
  cases op <;> rfl

@[simp] theorem segAt_opH (σ : Nat → Nat) (g : Nat) (op : Op) :
    segAt g (opH σ op) = segAt g op := by
  simp [segAt]

@[simp] theorem endsAt_opH (σ : Nat → Nat) (g : Nat) (op : Op) :
    endsAt g (opH σ op) = endsAt g op := by
  simp [endsAt]

theorem getKey_treeH (σ : Nat → Nat) (s : Tree) : getKey (treeH σ s) = getKey s := by
  funext x
  simp only [getKey, treeH]
  cases s.obj x with
  | none => rfl
  | some o => cases o <;> rfl

/-! ## The same key nodes, the same run -/

section Congr

variable {cf : Cfg} {i : Time} {s s' : Tree} (hg : getKey s = getKey s')
include hg

theorem mkNode_congr : mkNode cf i s = mkNode cf i s' := by
  funext b g h join es0
  simp only [mkNode, hg]

theorem openEs_congr : openEs s = openEs s' := by
  funext v
  cases v <;> simp only [openEs, hg]

theorem cntOf_congr : cntOf s = cntOf s' := by
  funext v
  cases v <;> simp only [cntOf, hg]

theorem joinAt_congr : joinAt cf i s = joinAt cf i s' := by
  funext g h down es ix
  simp only [joinAt, openEs_congr hg, cntOf_congr hg, mkNode_congr hg]

theorem joinLoop_congr : joinLoop cf i s = joinLoop cf i s' := by
  funext g h down n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext es
    simp only [joinLoop, joinAt_congr hg, ih]

theorem rebalance_congr : ∀ f, rebalance cf i s f = rebalance cf i s' f := by
  intro f
  induction f with
  | zero => rfl
  | succ f ih =>
    funext g h es0
    simp only [rebalance, joinLoop_congr hg, ih]

theorem settleRoot_congr : ∀ f, settleRoot cf i s f = settleRoot cf i s' f := by
  intro f
  induction f with
  | zero => rfl
  | succ f ih =>
    funext g v space
    cases v <;> simp only [settleRoot, hg, mkNode_congr hg, ih]

omit hg in
mutual

theorem emit_congr' (hg : getKey s = getKey s') :
    ∀ (v : VN) (a : Acc), emit cf i s v a = emit cf i s' v a
  | .old _, _ => rfl
  | .node base g h join es F dec, a => by
    simp only [emit, emitKids_congr' hg es a, hg]

theorem emitKids_congr' (hg : getKey s = getKey s') : ∀ (es : List (Nat × VN)) (a : Acc),
    emitKids cf i s es a = emitKids cf i s' es a
  | [], _ => rfl
  | (c, v) :: rest, a => by
    simp only [emitKids, emit_congr' hg v a, emitKids_congr' hg rest]

end

theorem emit_congr : emit cf i s = emit cf i s' := by
  funext v a
  exact emit_congr' hg v a

/-- The mutual block of plan, by its fuel. -/
theorem plan_block_congr : ∀ f,
    plan cf i s f = plan cf i s' f ∧ planKids cf i s f = planKids cf i s' f ∧
    applyGroups cf i s f = applyGroups cf i s' f ∧ planTree cf i s f = planTree cf i s' f := by
  intro f
  induction f with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> funext <;> simp [plan, planKids, applyGroups, planTree]
  | succ f ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · funext x g h ops acc
      simp only [plan, hg, h2, h3, mkNode_congr hg, rebalance_congr hg]
    · funext g h es os acc
      cases es with
      | nil => simp [planKids]
      | cons e rest =>
        obtain ⟨c, y⟩ := e
        cases os with
        | nil => simp [planKids]
        | cons o os => simp only [planKids, h1, h2]
    · funext g es cvs ops acc
      cases cvs with
      | nil => simp [applyGroups]
      | cons cv cvs => simp only [applyGroups, h3, h4]
    · funext root g ops acc
      unfold planTree
      simp only [hg, h1, h3, mkNode_congr hg, settleRoot_congr hg, emit_congr hg]

end Congr

/-! ## The hashes of the operations mapped -/

section MapH

variable {cf : Cfg} {i : Time} {s : Tree} (σ : Nat → Nat)

theorem filter_map_opH (p : Op → Bool) (hp : ∀ op, p (opH σ op) = p op) (ops : List Op) :
    (ops.map (opH σ)).filter p = (ops.filter p).map (opH σ) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro op _
  simp [hp]

theorem route_map {α β : Type} (cv : α → Nat) (f : α → α) (hf : ∀ a, cv (f a) = cv a) :
    ∀ (lv : List (Nat × β)) (ops : List α),
      route cv lv (ops.map f) = (route cv lv ops).map (List.map f)
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: (c', y) :: r, ops => by
    simp only [route, List.map_cons]
    have h1 : (ops.map f).filter (fun o => decide (cv o < c')) =
        (ops.filter (fun o => decide (cv o < c'))).map f := by
      rw [List.filter_map]; congr 1; apply List.filter_congr; intro a _; simp [hf]
    have h2 : (ops.map f).filter (fun o => decide (c' ≤ cv o)) =
        (ops.filter (fun o => decide (c' ≤ cv o))).map f := by
      rw [List.filter_map]; congr 1; apply List.filter_congr; intro a _; simp [hf]
    rw [h1, h2, route_map cv f hf ((c', y) :: r)]

theorem fresh_accH (a : Acc) :
    (accH σ a).fresh = ((a.fresh).1, accH σ (a.fresh).2) := rfl

theorem write_accH (a : Acc) (x : NodeId) (o : Obj) :
    (accH σ a).write x (objH σ o) = accH σ (a.write x o) := rfl

theorem write_key_accH (a : Acc) (x : NodeId) (n : KNode) :
    (accH σ a).write x (.key n) = accH σ (a.write x (.key n)) := rfl

theorem newParts_mapH (g h : Nat) : ∀ (Ps : List (List (Nat × NodeId))) (a : Acc),
    newParts cf i g h Ps (accH σ a) =
      ((newParts cf i g h Ps a).1, accH σ (newParts cf i g h Ps a).2)
  | [], _ => rfl
  | P :: Ps, a => by
    simp only [newParts]
    rw [fresh_accH]
    simp only
    rw [write_key_accH, newParts_mapH g h Ps]

mutual

theorem emit_mapH' : ∀ (v : VN) (a : Acc),
    emit cf i s v (accH σ a) = (emit cf i s v a).map (fun r => (r.1, accH σ r.2))
  | .old _, _ => rfl
  | .node base g h join es F dec, a => by
    simp only [emit]
    rw [emitKids_mapH' es a]
    cases emitKids cf i s es a with
    | none => rfl
    | some r =>
      obtain ⟨F0, b⟩ := r
      simp only [Option.map_some]
      cases dec with
      | same => cases base <;> rfl
      | append =>
        cases base with
        | none => rfl
        | some b' =>
          simp only
          cases getKey s b' with
          | none => rfl
          | some n => simp only [Option.map_some, write_key_accH]
      | parts k => simp only [Option.map_some, newParts_mapH]

theorem emitKids_mapH' : ∀ (es : List (Nat × VN)) (a : Acc),
    emitKids cf i s es (accH σ a) = (emitKids cf i s es a).map (fun r => (r.1, accH σ r.2))
  | [], _ => rfl
  | (c, v) :: rest, a => by
    simp only [emitKids]
    rw [emit_mapH' v a]
    cases emit cf i s v a with
    | none => rfl
    | some r =>
      obtain ⟨E, b⟩ := r
      simp only [Option.map_some]
      rw [emitKids_mapH' rest b]
      cases emitKids cf i s rest b with
      | none => rfl
      | some r' => rfl

end

theorem foldl_mapH (F : List (Nat × NodeId) × Acc → Op → List (Nat × NodeId) × Acc)
    (hF : ∀ es a op, F (es, accH σ a) (opH σ op) = ((F (es, a) op).1, accH σ (F (es, a) op).2)) :
    ∀ (l : List Op) (es : List (Nat × NodeId)) (a : Acc),
      (l.map (opH σ)).foldl F (es, accH σ a) = ((l.foldl F (es, a)).1, accH σ (l.foldl F (es, a)).2)
  | [], _, _ => rfl
  | op :: l, es, a => by
    simp only [List.map_cons, List.foldl_cons]
    rw [hF]
    exact foldl_mapH F hF l _ _

/-- The writer's plan with the hashes of its operations mapped writes the
values with their hashes mapped, and is otherwise the same. -/
theorem plan_block_mapH : ∀ f,
    (∀ x g h ops a, plan cf i s f x g h (ops.map (opH σ)) (accH σ a) =
        (plan cf i s f x g h ops a).map (fun r => (r.1, accH σ r.2))) ∧
    (∀ g h es os a, planKids cf i s f g h es (os.map (List.map (opH σ))) (accH σ a) =
        (planKids cf i s f g h es os a).map (fun r => (r.1, accH σ r.2))) ∧
    (∀ g es cvs ops a, applyGroups cf i s f g es cvs (ops.map (opH σ)) (accH σ a) =
        (applyGroups cf i s f g es cvs ops a).map (fun r => (r.1, accH σ r.2))) ∧
    (∀ root g ops a, planTree cf i s f root g (ops.map (opH σ)) (accH σ a) =
        (planTree cf i s f root g ops a).map (fun r => (r.1, accH σ r.2))) := by
  intro f
  induction f with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp [plan, planKids, applyGroups, planTree]
  | succ f ih =>
    obtain ⟨IP, IK, IA, IT⟩ := ih
    have hseg : ∀ (g : Nat) (ops : List Op),
        (ops.map (opH σ)).map (segAt g) = ops.map (segAt g) := by
      intro g ops; simp [List.map_map, Function.comp_def]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x g h ops a
      simp only [plan]
      cases getKey s x with
      | none => rfl
      | some n =>
        simp only
        split
        · rw [hseg, IA]
          cases applyGroups cf i s f g (live n.ks) ((ops.map (segAt g)).eraseDups) ops a with
          | none => rfl
          | some r =>
            obtain ⟨es, b⟩ := r
            simp only [Option.map_some]
            split <;> rfl
        · rw [route_map (segAt g) (opH σ) (segAt_opH σ g), IK]
          cases planKids cf i s f g h (live n.ks) (route (segAt g) (live n.ks) ops) a with
          | none => rfl
          | some r =>
            obtain ⟨es, b⟩ := r
            simp only [Option.map_some]
            split
            · rfl
            · split <;> rfl
    · intro g h es os a
      cases es with
      | nil => simp [planKids]
      | cons e rest =>
        obtain ⟨c, y⟩ := e
        cases os with
        | nil => simp [planKids]
        | cons o os =>
          simp only [planKids, List.map_cons, List.isEmpty_map]
          split
          · rw [IK]
            cases planKids cf i s f g h rest os a <;> rfl
          · rw [IP]
            cases plan cf i s f y g (h - 1) o a with
            | none => rfl
            | some r =>
              obtain ⟨v, b⟩ := r
              simp only [Option.map_some]
              rw [IK]
              cases planKids cf i s f g h rest os b <;> rfl
    · intro g es cvs ops a
      cases cvs with
      | nil => simp [applyGroups]
      | cons cv cvs =>
        simp only [applyGroups]
        rw [filter_map_opH σ (fun op => segAt g op == cv) (fun op => by simp),
          filter_map_opH σ (endsAt g) (fun op => by simp),
          foldl_mapH σ _ (fun es a op => by cases op <;> rfl),
          filter_map_opH σ (fun op => !endsAt g op) (fun op => by simp), List.isEmpty_map]
        simp only
        split
        · rw [IA]
        · rw [IT]
          cases planTree cf i s f _ (g + 1) _ _ with
          | none => rfl
          | some r =>
            obtain ⟨res, b⟩ := r
            cases res with
            | none => simp only [Option.map_some]; rw [IA]
            | some y => simp only [Option.map_some]; rw [IA]
    · intro root g ops a
      unfold planTree
      cases root with
      | some r =>
        simp only
        cases getKey s r with
        | none => rfl
        | some n =>
          simp only
          rw [IP]
          cases plan cf i s f r g (cf.htOf n.level) ops a with
          | none => rfl
          | some p =>
            obtain ⟨v, b⟩ := p
            simp only [Option.map_some]
            cases settleRoot cf i s f g v false with
            | none => rfl
            | some o =>
              cases o with
              | none => rfl
              | some v' =>
                simp only
                rw [emit_mapH' σ v' b]
                cases emit cf i s v' b with
                | none => rfl
                | some q =>
                  obtain ⟨E, b2⟩ := q
                  simp only [Option.map_some]
                  rcases E with _ | ⟨⟨c0, y⟩, _ | ⟨_, _⟩⟩ <;> rfl
      | none =>
        simp only
        rw [hseg, IA]
        cases applyGroups cf i s f g [] ((ops.map (segAt g)).eraseDups) ops a with
        | none => rfl
        | some p =>
          obtain ⟨es, b⟩ := p
          simp only [Option.map_some]
          cases mkNode cf i s none g 0 false (es.map (fun e => (e.1, VN.old e.2))) with
          | none => rfl
          | some v =>
            simp only [Option.map_some]
            cases settleRoot cf i s f g v false with
            | none => rfl
            | some o =>
              cases o with
              | none => rfl
              | some v' =>
                simp only
                rw [emit_mapH' σ v' b]
                cases emit cf i s v' b with
                | none => rfl
                | some q =>
                  obtain ⟨E, b2⟩ := q
                  simp only [Option.map_some]
                  rcases E with _ | ⟨⟨c0, y⟩, _ | ⟨_, _⟩⟩ <;> rfl

theorem dropNoops_mapH (ops : List Op) :
    dropNoops cf (ops.map (opH σ)) = (dropNoops cf ops).map (opH σ) := by
  unfold dropNoops
  exact filter_map_opH σ _ (fun op => by cases op <;> rfl) ops

theorem opsOk_mapH (ops : List Op) : opsOk cf (ops.map (opH σ)) = opsOk cf ops := by
  unfold opsOk
  rw [List.all_map]
  congr 1
  funext op
  simp

/-- **The transaction with the hashes of its operations mapped** writes the
values with their hashes mapped, and is otherwise the same. -/
theorem peTx_mapH (tp : Top) (nx : NodeId) (ops : List Op) :
    peTx cf i s tp nx (ops.map (opH σ)) = (peTx cf i s tp nx ops).map (outH σ) := by
  unfold peTx
  simp only [dropNoops_mapH, opsOk_mapH]
  split
  · rfl
  · cases s.root with
    | none => rfl
    | some r =>
      simp only
      cases getKey s r with
      | none => rfl
      | some n =>
        simp only
        have hp : plan cf i s fuel r 0 (cf.htOf n.level) ((dropNoops cf ops).map (opH σ)) ⟨[], nx⟩ =
            (plan cf i s fuel r 0 (cf.htOf n.level) (dropNoops cf ops) ⟨[], nx⟩).map
              (fun r => (r.1, accH σ r.2)) :=
          (plan_block_mapH σ fuel).1 r 0 (cf.htOf n.level) (dropNoops cf ops) ⟨[], nx⟩
        rw [hp]
        cases plan cf i s fuel r 0 (cf.htOf n.level) (dropNoops cf ops) ⟨[], nx⟩ with
        | none => rfl
        | some p =>
          obtain ⟨v, b⟩ := p
          simp only [Option.map_some]
          cases settleRoot cf i s fuel 0 v true with
          | none => rfl
          | some o =>
            cases o with
            | none => rfl
            | some rv =>
              simp only
              rw [emit_mapH' σ rv b]
              cases emit cf i s rv b with
              | none => rfl
              | some q =>
                obtain ⟨E, b2⟩ := q
                simp only [Option.map_some]
                rcases E with _ | ⟨⟨c0, y⟩, _ | ⟨_, _⟩⟩
                · rfl
                · simp only
                  split <;> rfl
                · rfl

end MapH

theorem map_eq_self_mem {α : Type} {f : α → α} : ∀ {l : List α}, l.map f = l → ∀ x ∈ l, f x = x
  | [], _, _, hx => by simp at hx
  | a :: l, h, x, hx => by
    simp only [List.map_cons, List.cons.injEq] at h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact map_eq_self_mem h.2 x hx

/-- **Every value a transaction writes has the hash of one of its puts.** -/
theorem peTx_vals {cf : Cfg} {i : Time} {s : Tree} {tp : Top} {nx : NodeId} {ops : List Op}
    {o : Out} (ho : peTx cf i s tp nx ops = some o) {y : NodeId} {v : Nat}
    (hy : (y, Obj.val v) ∈ o.ws) : ∃ k, Op.put k v ∈ ops := by
  by_contra hno
  have hno' : ∀ k, Op.put k v ∉ ops := fun k hk => hno ⟨k, hk⟩
  let σ : Nat → Nat := fun u => if u = v then v + 1 else u
  have hops : ops.map (opH σ) = ops := by
    conv_rhs => rw [← List.map_id ops]
    apply List.map_congr_left
    intro op hop
    cases op with
    | put k u =>
      have : u ≠ v := fun h => hno' k (h ▸ hop)
      simp [opH, σ, this]
    | del k => rfl
  have h1 := peTx_mapH (cf := cf) (i := i) (s := s) σ tp nx ops
  rw [hops, ho, Option.map_some, Option.some.injEq] at h1
  have h2 : o.ws.map (fun p => (p.1, objH σ p.2)) = o.ws := by
    have := congrArg Out.ws h1
    simpa [outH] using this.symm
  have := map_eq_self_mem h2 _ hy
  simp [objH, σ] at this

/-! ## The trees -/

theorem treeH_getKey_roots (σ : Nat → Nat) (s : Tree) :
    getKey (treeH σ s) = getKey s ∧ (treeH σ s).roots = s.roots := ⟨getKey_treeH σ s, rfl⟩

/-- The transaction on two trees with the same key nodes and space roots. -/
theorem peTx_congr {cf : Cfg} {i : Time} {s s' : Tree} (hg : getKey s = getKey s')
    (hr : s.roots = s'.roots) (tp : Top) (nx : NodeId) (ops : List Op) :
    peTx cf i s tp nx ops = peTx cf i s' tp nx ops := by
  have hroot : s.root = s'.root := by simp [Tree.root, hr]
  unfold peTx
  simp only [hroot, hg, (plan_block_congr hg fuel).1, settleRoot_congr hg, emit_congr hg, hr]

theorem lookup_mapH (σ : Nat → Nat) (ws : List (NodeId × Obj)) (x : NodeId) :
    (ws.map (fun p => (p.1, objH σ p.2))).lookup x = (ws.lookup x).map (objH σ) := by
  induction ws with
  | nil => rfl
  | cons p ws ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.lookup]
    split <;> simp_all

theorem tree_outH (σ : Nat → Nat) (s : Tree) (o : Out) :
    (outH σ o).tree (treeH σ s) = treeH σ (o.tree s) := by
  simp only [Out.tree, applyWs, outH, treeH, Tree.mk.injEq, and_true]
  funext x
  rw [lookup_mapH]
  cases o.ws.lookup x <;> rfl

theorem lvlOf_treeH (σ : Nat → Nat) (T : Tree) (x : NodeId) : lvlOf (treeH σ T) x = lvlOf T x := by
  simp only [lvlOf, treeH]
  cases T.obj x with
  | none => rfl
  | some o => cases o <;> rfl

theorem isDataOf_treeH (σ : Nat → Nat) (T : Tree) (x : NodeId) :
    isDataOf (treeH σ T) x = isDataOf T x := by
  simp only [isDataOf, treeH]
  cases T.obj x with
  | none => rfl
  | some o => cases o <;> rfl

theorem peChange_new (σ : Nat → Nat) (cf : Cfg) (s : Tree) (tp : Top) (o : Out) :
    (peChange cf (treeH σ s) tp (outH σ o)).new = (peChange cf s tp o).new := by
  have hids : (outH σ o).ws.map (·.1) = o.ws.map (·.1) := by simp [outH]
  have htop : newTopOf tp (outH σ o) = newTopOf tp o := rfl
  simp only [peChange, hids, htop, tree_outH, lvlOf_treeH, isDataOf_treeH]
  congr 2
  apply List.filter_congr
  intro x _
  simp [treeH]

/-- **A run of PE on operations whose hashes are mapped by σ** is the image
of the run on the operations: the same steps, each tree the image of the
other's, the same nodes made, the same tops. -/
theorem peRun_mapH (cf : Cfg) (σ : Nat → Nat) : ∀ (txs : List (List Op)) (s : Tree) (tp : Top)
    (nx : NodeId) (t : Time) (L : List (BTx × Top)),
    peRun cf (treeH σ s) tp nx t (txs.map (List.map (opH σ))) = some L →
    ∃ L', peRun cf s tp nx t txs = some L' ∧ L.length = L'.length ∧
      ∀ j (hj : j < L.length) (hj' : j < L'.length), L[j].1.ops = L'[j].1.ops.map (opH σ) ∧
        L[j].1.s = treeH σ L'[j].1.s ∧ L[j].1.c.new = L'[j].1.c.new ∧ L[j].2 = L'[j].2
  | [], s, tp, nx, t, L, hr => by
    simp only [List.map_nil, peRun, Option.some.injEq] at hr
    subst hr
    exact ⟨[], rfl, rfl, fun j hj => by simp at hj⟩
  | ops :: rest, s, tp, nx, t, L, hr => by
    simp only [List.map_cons, peRun] at hr
    rw [peTx_congr (getKey_treeH σ s) rfl, peTx_mapH] at hr
    cases ho : peTx cf (t + 1) s tp nx ops with
    | none => rw [ho] at hr; cases hr
    | some o =>
      rw [ho, Option.map_some] at hr
      simp only at hr
      rw [tree_outH] at hr
      cases hrest : peRun cf (treeH σ (o.tree s)) (outH σ o).top (outH σ o).next (t + 1)
          (rest.map (List.map (opH σ))) with
      | none => rw [hrest] at hr; cases hr
      | some Lr =>
        rw [hrest, Option.map_some, Option.some.injEq] at hr
        subst hr
        obtain ⟨Lr', hr', hlen, hall⟩ :=
          peRun_mapH cf σ rest (o.tree s) o.top o.next (t + 1) Lr hrest
        refine ⟨(⟨ops, o.D, o.tree s, peChange cf s tp o⟩, o.top) :: Lr',
          by simp only [peRun, ho, hr', Option.map_some], by simp [hlen], ?_⟩
        intro j hj hj'
        cases j with
        | zero =>
          refine ⟨rfl, ?_, ?_, rfl⟩
          · simp
          · exact peChange_new σ cf s tp o
        | succ j =>
          simp only [List.getElem_cons_succ]
          exact hall j (by simpa using hj) (by simpa using hj')

/-- **In a run of PE, a value that a step makes has the hash of one of its
puts.** -/
theorem peRun_vals (cf : Cfg) : ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId)
    (t : Time) (L : List (BTx × Top)), peRun cf s tp nx t txs = some L →
    ∀ j (hj : j < L.length) y v, L[j].1.s.obj y = some (.val v) →
      ((s :: L.map (·.1.s))[j]?).bind (·.obj y) = none → ∃ k, Op.put k v ∈ L[j].1.ops
  | [], _, _, _, _, L, hr => by
    simp only [peRun, Option.some.injEq] at hr
    subst hr
    intro j hj; simp at hj
  | ops :: rest, s, tp, nx, t, L, hr => by
    simp only [peRun] at hr
    cases ho : peTx cf (t + 1) s tp nx ops with
    | none => rw [ho] at hr; cases hr
    | some o =>
      rw [ho] at hr
      simp only at hr
      cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
      | none => rw [hrest] at hr; cases hr
      | some Lr =>
        rw [hrest, Option.map_some, Option.some.injEq] at hr
        subst hr
        intro j hj y v hy hprev
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero, List.getElem?_cons_zero, Option.bind_some]
            at hy hprev ⊢
          simp only [Out.tree, applyWs] at hy
          cases hl : o.ws.lookup y with
          | none => rw [hl, hprev] at hy; cases hy
          | some ob =>
            rw [hl] at hy
            injection hy with hy
            subst hy
            obtain ⟨l₁, l₂, hl', -⟩ := List.lookup_eq_some_iff.mp hl
            exact peTx_vals (y := y) ho (by rw [hl']; simp)
        | succ j =>
          simp only [List.getElem_cons_succ, List.map_cons, List.getElem?_cons_succ] at hy hprev ⊢
          exact peRun_vals cf rest (o.tree s) o.top o.next (t + 1) Lr hrest j (by simpa using hj)
            y v hy
            (by
              cases j with
              | zero => simpa using hprev
              | succ j => simpa using hprev)

theorem peRun_ops (cf : Cfg) : ∀ (txs : List (List Op)) (s : Tree) (tp : Top) (nx : NodeId)
    (t : Time) (L : List (BTx × Top)), peRun cf s tp nx t txs = some L → L.map (·.1.ops) = txs
  | [], _, _, _, _, L, hr => by
    simp only [peRun, Option.some.injEq] at hr; subst hr; rfl
  | ops :: rest, s, tp, nx, t, L, hr => by
    simp only [peRun] at hr
    split at hr
    · cases hr
    rename_i o _
    cases hrest : peRun cf (o.tree s) o.top o.next (t + 1) rest with
    | none => rw [hrest] at hr; cases hr
    | some L' =>
      rw [hrest, Option.map_some, Option.some.injEq] at hr
      subst hr
      simp [peRun_ops cf rest _ _ _ _ L' hrest]

/-! ## Operations with labels -/

/-- The operations of transaction j with each put labelled by its place: the
put at index idx gets the hash `Nat.pair j idx`. -/
def relab (j : Nat) (ops : List Op) : List Op :=
  ops.mapIdx (fun idx op => match op with
    | .put k _ => .put k (Nat.pair j idx)
    | .del k => .del k)

/-- A history's operations with each put labelled by its place. -/
def labTxs (txs : List (List Op)) : List (List Op) := txs.mapIdx relab

/-- The label of a put mapped back to its hash. -/
def labσ (txs : List (List Op)) (v : Nat) : Nat :=
  match (txs[(Nat.unpair v).1]?).bind (fun ops => ops[(Nat.unpair v).2]?) with
  | some (.put _ h) => h
  | _ => 0

theorem labTxs_length (txs : List (List Op)) : (labTxs txs).length = txs.length := by
  simp [labTxs]

theorem labTxs_get (txs : List (List Op)) {j : Nat} (hj : j < (labTxs txs).length) :
    (labTxs txs)[j] = relab j (txs[j]'(by simpa [labTxs_length] using hj)) := by
  simp [labTxs]

theorem relab_keys (j : Nat) (ops : List Op) : (relab j ops).map Op.key = ops.map Op.key := by
  apply List.ext_getElem (by simp [relab])
  intro n h1 h2
  have hn : n < ops.length := by simpa using h2
  simp only [relab, List.getElem_map, List.getElem_mapIdx]
  cases ops[n] <;> rfl

/-- The labels mapped back give the operations. -/
theorem labTxs_map (txs : List (List Op)) :
    (labTxs txs).map (List.map (opH (labσ txs))) = txs := by
  apply List.ext_getElem (by simp [labTxs_length])
  intro j h1 h2
  simp only [List.getElem_map]
  rw [labTxs_get txs (by simpa using h1)]
  apply List.ext_getElem (by simp [relab])
  intro idx k1 k2
  simp only [relab, List.getElem_map, List.getElem_mapIdx]
  cases hop : txs[j][idx] with
  | put k v =>
    simp only [opH, labσ, Nat.unpair_pair, List.getElem?_eq_getElem h2, Option.bind_some,
      List.getElem?_eq_getElem k2, hop]
  | del k => rfl

theorem mem_relab {j : Nat} {ops : List Op} {k : Key} {v : Nat} (h : Op.put k v ∈ relab j ops) :
    ∃ idx, ∃ hi : idx < ops.length, v = Nat.pair j idx ∧ ∃ w, ops[idx] = Op.put k w := by
  simp only [relab, List.mem_iff_getElem, List.length_mapIdx, List.getElem_mapIdx] at h
  obtain ⟨idx, hi, he⟩ := h
  refine ⟨idx, hi, ?_⟩
  cases hop : ops[idx] with
  | put k' w =>
    rw [hop] at he
    simp only [Op.put.injEq] at he
    exact ⟨he.2.symm, w, by rw [he.1]⟩
  | del k' => rw [hop] at he; cases he

/-- Labels name one put: one transaction and one key. -/
theorem labTxs_unique (txs : List (List Op)) {j j' : Nat} (hj : j < (labTxs txs).length)
    (hj' : j' < (labTxs txs).length) {k k' : Key} {v : Nat}
    (h1 : Op.put k v ∈ (labTxs txs)[j]) (h2 : Op.put k' v ∈ (labTxs txs)[j']) :
    j = j' ∧ k = k' := by
  rw [labTxs_get] at h1 h2
  obtain ⟨i1, hi1, hv1, w1, hw1⟩ := mem_relab h1
  obtain ⟨i2, hi2, hv2, w2, hw2⟩ := mem_relab h2
  rw [hv1] at hv2
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.mp hv2
  refine ⟨rfl, ?_⟩
  rw [hw1] at hw2
  injection hw2

theorem startTree_treeH (σ : Nat → Nat) (cf : Cfg) : treeH σ (startTree cf) = startTree cf := by
  simp only [treeH, startTree, Tree.mk.injEq, and_true]
  funext x
  split <;> rfl

end Contract.PE
