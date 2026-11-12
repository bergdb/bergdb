import SIS.Tree.MergeKeptNode

namespace SIS.Tree

open SIS SIS.Check

/-- Updating the guarded id changes only the cached node in its guard. -/
theorem writerWP_putNode_guard_same (b : NodeGuard) (n : KNode) (c : Ctx) (w : W)
    (hw : GuardHeld b w) :
    WriterWP (putNode b.id n) c w (fun _ v => GuardHeld {b with node := n} v) := by
  simp only [putNode,writerWP_modify]
  exact ⟨upsert_lookup_same _ _ _,hw.2⟩

/-- Dead-klong compaction of a node made in this transaction keeps its
id, height tag and allocation status, at any depth. -/
theorem writerWP_handleFullWith_compact_new_same (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat) (last : KNode)
    (c : Ctx) (w : W) (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i) :
    WriterWP (handleFullWith up depth b.id [] last true) c w
      (fun _ v => GuardHeld {b with node := {last with leaf := b.node.leaf}} v) := by
  unfold handleFullWith
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  refine writerWP_mono (guard_ghOf b b.id c w hw) ?_
  intro gh v hv
  simp only [ht,BEq.rfl]
  unfold parentAt pathNode
  repeat' first
    | wpSimplify
    | simp only [note,replaceOrAdd,List.foldlM_nil,Bool.not_true,Bool.false_and,
        Bool.false_eq_true,↓reduceIte]
    | kgUse b using (guard_getNode b _)
    | (refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro _ _ hn
       exact hn)
    | exact writerWP_throw _ _ _ _
    | split

/-- Distinct live values below the delete compare value survive in the
normalized last version. -/
theorem KNode.delete_cnt_ge_earlier_prefix (n : KNode) (t : Time)
    (cut cv : Nat) (keys : List Nat) (hn : keys.Nodup)
    (hcut : ∀ a ∈ keys, a < cut) (hcv : cut ≤ cv)
    (hk : ∀ a ∈ keys, ∃ y i, (.key a y,i) ∈ n.ks.zipIdx ∧ i ∉ n.lastBitmap) :
    keys.length ≤ (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).cnt := by
  obtain ⟨pairs,hpairs,hs,hlen,_⟩ :=
    n.delete_lastVersion_earlier_prefix t cut cv keys hn hcut hcv hk
  have hnd : (pairs.map Prod.fst).Nodup := by
    apply List.pairwise_map.mpr
    exact hs.imp (by intro a b hab; omega)
  have hc := KNode.newKlongs_cnt n.leaf t pairs hnd
  have hnode : n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv)) =
      ⟨n.leaf,newKlongs t pairs⟩ := by
    have hf : (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).leaf = n.leaf := rfl
    generalize n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv)) = out at hpairs hf ⊢
    cases out
    simp_all
  have he : (n.lastVersionGivenDel t (bitsUnion n.lastBitmap (n.bitsOf cv))).cnt = pairs.length := by
    simpa only [hnode] using hc
  simp only [List.length_take] at hlen
  omega

/-- A delete with room in a node made in this transaction preserves its
guard and the earlier-key count, including either dead-compaction route. -/
theorem writerWP_appendDeleteKlong_new_room_earlier (b : NodeGuard)
    (depth cv cut : Nat) (keys : List Nat) (c : Ctx) (w : W)
    (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i) (hkeys : keys.Nodup)
    (hcut : ∀ a ∈ keys, a < cut) (hcv : cut ≤ cv)
    (hk : ∀ a ∈ keys, ∃ y i, (.key a y,i) ∈ b.node.ks.zipIdx ∧ i ∉ b.node.lastBitmap)
    (hroom : b.node.size+1 < c.p.M) :
    WriterWP (appendDeleteKlong b.id depth cv) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧ keys.length ≤ after.cnt) := by
  have hold := b.node.cnt_ge_protected_keys keys hkeys hk
  have hadd := b.node.add_delete_cnt_ge_earlier_prefix c.i cut cv keys hkeys hcut hcv hk
  have hset := b.node.setAt_delete_cnt_ge_earlier_prefix cut cv keys hkeys hcut hcv hk
  have hcompact := b.node.delete_cnt_ge_earlier_prefix c.i cut cv keys hkeys hcut hcv hk
  unfold appendDeleteKlong
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  repeat' first
    | wpSimplify
    | simp only [note,hroom,↓reduceIte]
    | (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ true) _ _ _
       unfold handleFull
       refine writerWP_mono (writerWP_handleFullWith_compact_new_same b _ _ _ _ _ (by kgState) ht) ?_
       intro _ _ hv)
    | (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _
       refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro _ _ hv)
    | (exact ⟨b.node,by kgState,hold⟩)
    | (exact ⟨_,by kgState,hadd⟩)
    | (exact ⟨_,by kgState,hset _ (by assumption)⟩)
    | (refine ⟨_,?_,hcompact⟩; simpa only [KNode.lastVersionGivenDel] using hv)
    | exact writerWP_throw _ _ _ _
    | split

/-- The sorted terminal-key premises give the earlier-value hypotheses of
the writer-level room/delete rule. Physical availability is still required. -/
theorem writerWP_appendDeleteKlong_new_room_sorted_terminal (b : NodeGuard)
    (depth g : Nat) (keys : List Key) (key : Key) (cv : Nat) (c : Ctx) (w : W)
    (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (hs : sortedKeys (keys ++ [key]) = true)
    (hwf : ∀ a ∈ keys, keyWf a = true) (hkey : keyWf key = true)
    (hlen : ∀ a ∈ keys, a.length = g+1)
    (hprefix : ∀ a ∈ keys, a.take g = key.take g) (hcv : key[g]? = some cv)
    (hk : ∀ a ∈ keys, ∃ y i,
      (.key a[g]! y,i) ∈ b.node.ks.zipIdx ∧ i ∉ b.node.lastBitmap)
    (hroom : b.node.size+1 < c.p.M) :
    WriterWP (appendDeleteKlong b.id depth cv) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧ keys.length ≤ after.cnt) := by
  obtain ⟨hnd,hbefore⟩ := terminal_prefix_values_before keys key g cv hs hwf hkey hlen hprefix hcv
  have he := writerWP_appendDeleteKlong_new_room_earlier b depth cv cv
    (keys.map (fun a => a[g]!)) c w hw ht hnd hbefore (Nat.le_refl _) (by
      intro a ha
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp ha
      exact hk old hold) hroom
  simpa only [List.length_map] using he

/-- A physical live key prevents the all-keys-deleted test. -/
theorem KNode.allKeysIn_false_of_live_key (n : KNode) (del : List Nat)
    (a : Nat) (y : NodeId) (i : Nat) (hm : (.key a y,i) ∈ n.ks.zipIdx)
    (hi : i ∉ del) : n.allKeysIn del = false := by
  cases he : n.allKeysIn del with
  | false => rfl
  | true =>
    have ha := List.all_eq_true.mp he (.key a y,i) hm
    have hd : i ∈ del := by simpa using ha
    exact False.elim (hi hd)

/-- Deleting a later compare value cannot empty a node with an earlier
physical live key. -/
theorem KNode.delete_nonempty_of_earlier (n : KNode) (a cv : Nat)
    (y : NodeId) (i : Nat) (hm : (.key a y,i) ∈ n.ks.zipIdx)
    (hi : i ∉ n.lastBitmap) (hlt : a < cv) :
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false := by
  exact n.allKeysIn_false_of_live_key _ a y i hm
    (n.delete_preserves_earlier_key a cv y i hm hi hlt)

/-- With an earlier live key, an effective cached-leaf delete follows the
nonempty route. No upward-empty-node cleanup is executed by deleteUpward. -/
theorem writerWP_deleteUpward_of_earlier (leaf : NodeId) (depth cv : Nat) (key : Key)
    (n : KNode) (a : Nat) (y : NodeId) (i : Nat) (c : Ctx) (w : W)
    (hn : w.nodes.lookup leaf = some n)
    (hm : (.key a y,i) ∈ n.ks.zipIdx) (hi : i ∉ n.lastBitmap) (hlt : a < cv)
    (hchange : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false)
    (post : Bool → W → Prop) :
    WriterWP (deleteUpward leaf depth cv key) c w post ↔
      WriterWP (do
        let (g,h) ← ghOf leaf
        let _ ← appendDeleteKlong leaf depth cv
        afterDelete key g h
        pure false) c w post := by
  have hne := n.delete_nonempty_of_earlier a cv y i hm hi hlt
  unfold deleteUpward
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known leaf n c w hn]
  simp only [hchange,hne,Bool.false_eq_true,Bool.not_false,↓reduceIte,
    writerWP_bind,writerWP_pure]

/-- An earlier live parent klong stops the empty-node climb at that parent.
If the split take-back check fails the action throws; every successful
result is the parent depth, with the cache and all other state unchanged. -/
theorem writerWP_climb_of_earlier_parent (d : Nat) (x q : NodeId)
    (parentCv : Option Nat) (cv a : Nat) (nx pn : KNode)
    (y : NodeId) (i : Nat) (c : Ctx) (w : W)
    (hpath : w.path[d+1]? = some (some cv,x))
    (hparent : w.path[d]? = some (parentCv,q))
    (hx : w.nodes.lookup x = some nx) (hq : w.nodes.lookup q = some pn)
    (hm : (.key a y,i) ∈ pn.ks.zipIdx) (hi : i ∉ pn.lastBitmap) (hlt : a < cv) :
    WriterWP (climb (d+1)) c w (fun r v => r = d ∧ v = w) := by
  have hne := pn.delete_nonempty_of_earlier a cv y i hm hi hlt
  unfold climb
  repeat' first
    | wpSimplify
    | simp only [pathNode,klongAt,canTakeBack,replacedBy,hpath,hparent,hne,
        Bool.false_eq_true,↓reduceIte]
    | rw [writerWP_getNode_known x nx c w hx]
    | rw [writerWP_getNode_known q pn c w hq]
    | exact writerWP_throw _ _ _ _
    | exact ⟨rfl,rfl⟩
    | trivial
    | wpSplit
    | split

/-- With the access path cached, the empty-node climb cannot pass a parent
that has an earlier live klong. Successful climbs only read the cached path. -/
theorem writerWP_climb_above_earlier_parent (barrier : Nat) (x q : NodeId)
    (parentCv : Option Nat) (cv a : Nat) (nx pn : KNode)
    (y : NodeId) (i : Nat) (c : Ctx) (w : W)
    (hpath : w.path[barrier+1]? = some (some cv,x))
    (hparent : w.path[barrier]? = some (parentCv,q))
    (hx : w.nodes.lookup x = some nx) (hq : w.nodes.lookup q = some pn)
    (hm : (.key a y,i) ∈ pn.ks.zipIdx) (hi : i ∉ pn.lastBitmap) (hlt : a < cv) :
    ∀ depth, barrier < depth →
      (∀ k, k ≤ depth → ∃ entry node,
        w.path[k]? = some entry ∧ w.nodes.lookup entry.2 = some node) →
      WriterWP (climb depth) c w (fun r v => barrier ≤ r ∧ v = w) := by
  intro depth
  induction depth with
  | zero => intro hlt; omega
  | succ d ih =>
    intro hdepth hcache
    by_cases hd : d = barrier
    · subst d
      refine writerWP_mono
        (writerWP_climb_of_earlier_parent barrier x q parentCv cv a nx pn y i c w
          hpath hparent hx hq hm hi hlt) ?_
      rintro r v ⟨rfl,rfl⟩
      exact ⟨Nat.le_refl _,rfl⟩
    · have hbd : barrier < d := by omega
      obtain ⟨⟨childCv,child⟩,childNode,hchild,hchildNode⟩ := hcache (d+1) (by omega)
      obtain ⟨⟨parCv,par⟩,parNode,hpar,hparNode⟩ := hcache d (by omega)
      have hrec := ih hbd (fun k hk => hcache k (by omega))
      unfold climb
      repeat' first
        | wpSimplify
        | simp only [pathNode,klongAt,canTakeBack,replacedBy,hchild,hpar]
        | rw [writerWP_getNode_known child childNode c w hchildNode]
        | rw [writerWP_getNode_known par parNode c w hparNode]
        | exact hrec
        | exact writerWP_throw _ _ _ _
        | exact ⟨Nat.le_of_lt hbd,rfl⟩
        | exact ⟨Nat.le_of_lt hbd,True.intro⟩
        | trivial
        | wpSplit
        | split

end SIS.Tree
