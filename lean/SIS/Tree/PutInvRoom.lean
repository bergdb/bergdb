import SIS.Tree.PutInvInit
import SIS.Tree.WriterTreeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! `PutInv` kept by a put into a segment leaf with room (bergdb 024-12, TP10;
the rule of `writerWP_put_room_seg`). The parts about the tree after any rule
(`PutInvT`: no reachable node taken back, the order at the leaves) and the
global parts together give `PutInv` (`writerWP_putInv_of_T`). For a put, the
order at the leaf that gets the key comes from the descent: its parent's klong
to it is the parent's `searchLte` of the key's compare value, and TREE makes it
the one link to the leaf (`parentBound_of_descent`). -/

/-- The parts of `PutInv` about the tree. -/
def PutInvT (c : Ctx) (base : View BVal) (w : W) : Prop :=
  (∀ x, ReachS (wNode c.p base w) c.i w.top.rootKey x → w.taken.contains x = false) ∧
  (∀ q qn L n k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
    wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
    n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n)

/-- A rule that keeps the parts about the tree keeps `PutInv`, the writer's
tree after it given: the global parts hold after every operation. -/
theorem writerWP_putInv_of_T (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (op : Op)
    (w : W) (hB : PutBase c base B) (hw : PutBook c B top0 w)
    (hT : WriterWP (putKv op) c w (fun _ w' => PutInvT c base w')) :
    WriterWP (putKv op) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  intro r w' h htree
  have hb := (putBook_putKv c base B top0 op hB w hw r w' h).1
  have hG := putInvG_of_book c base B top0 w' hB hb
  exact putInv_of_parts c base w' hG htree (hT r w' h).1 (hT r w' h).2

/-! ## The bound that the descent gives the leaf -/

/-- Below an inner segment root rk, the leaf L of a key's compare value cv has
one parent in the tree, and its klong to L is at most cv, below every larger
live klong of it. -/
theorem parentBound_of_descent (c : Ctx) (base : View BVal) (w : W) (hI : PutInv c base w)
    (cv : Nat) (rk L : NodeId)
    (hrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hLrk : L ≠ rk) :
    ∀ q qn k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → (k1, L) ∈ qn.live →
      k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'' := by
  intro q qn k1 hq hqn hk
  obtain ⟨q0, q0n, fd, hq0, hq0n, _, hs, hy⟩ :=
    eqVisits_parent_lte _ _ cv c.p.fuel rk L hL hLrk
  have hrq0 := eqVisits_reach _ _ _ cv c.p.fuel rk q0 cv hrk hq0
  have hm0 : (fd.c, L) ∈ q0n.liveAt c.i := by
    have := KNode.searchLte_mem q0n c.i cv fd hs
    rw [hy] at this; exact this
  have hk' : (k1, L) ∈ qn.liveAt c.i := by
    rw [KNode.liveAt_of_times qn c.i (hI.times q qn hqn)]; exact hk
  obtain ⟨he, hc⟩ := htree_of_treeOK _ _ _ hI.tree q qn k1 L hq hqn hk' q0 q0n fd.c hrq0 hq0n hm0
  subst he
  rw [hq0n] at hqn
  cases hqn
  subst hc
  obtain ⟨_, hallow, hmax⟩ := (KNode.searchLte_spec qn c.i cv).1 fd hs
  simp only [decide_eq_true_eq] at hallow
  refine ⟨by omega, ?_⟩
  intro c'' z' hz hlt
  have hz' : (c'', z') ∈ qn.liveAt c.i := by
    rw [KNode.liveAt_of_times qn c.i (hI.times _ qn hq0n)]; exact hz
  by_cases hle : (c'' : Int) ≤ cv
  · have := hmax (c'', z') hz' (by simpa using hle)
    simp only [decide_eq_true_eq] at this
    omega
  · omega

/-- A leaf that gets a key klong of compare value cv between its parent's
bounds keeps the order below the parent. -/
theorem leafOrderAt_add (qn n : KNode) (k1 cv : Nat) (v : NodeId) (t : Time)
    (hwf : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hold : LeafOrderAt qn k1 n)
    (hb : k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    LeafOrderAt qn k1 (n.add t (.key cv v)) := by
  intro c' z hz
  have ht' := KNode.add_times n t (.key cv v) (fun s h => by cases h) ht
  rw [← KNode.liveAt_of_times _ t ht'] at hz
  rcases KNode.add_key_liveAt_mem n t cv v hwf ht c' z hz with ⟨h1, _⟩ | ⟨_, h2⟩
  · subst h1; exact hb
  · rw [KNode.liveAt_of_times n t ht] at h2
    exact hold c' z h2

/-! ## The writer's put with room -/

/-- A put into a segment leaf with room: the leaf L of the key's descent gets
the klong of the new value, at the next id; nothing else the state reads
changes. -/
theorem writerWP_put_room_after (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hroom : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' => ∃ L n,
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk ∧
      wNode c.p base w L = some n ∧ n.leaf = true ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
      wNode c.p base w' L = some (n.add c.i (.key cv w.next)) ∧
      ∀ x, x ≠ L → wNode c.p base w' x = wNode c.p base w x) := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2) ?_
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hroom', hdead⟩ := hroom L n hvisL hn hnl
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known L n c _ (by simpa using hlk3)]
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  have hcond : (decide (n.size + 1 < c.p.M) && !deadOver c.p (n.add c.i (.key cv w3.next))) = true := by
    rw [hnext3, hdead]; simp [hroom']
  simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  refine ⟨L, n, hvisL, hn, hnl, hr03.2.2.1, hr03.2.1, ?_, ?_⟩
  · simp only [wNode, hr03.2.2.1, hLt, Bool.false_eq_true, ↓reduceIte, lookup_upsert, hnext3]
  · intro x hx
    rw [← hr03.1]
    simp only [wNode, lookup_upsert, hx, ↓reduceIte]

/-- The parts about the tree after a put with room. `hpar`: the order bound
of the leaf's parents (from the descent below an inner segment root,
`parentBound_of_descent`; none for the space root). -/
theorem putInvT_room (c : Ctx) (base : View BVal) (w w' : W) (hI : PutInv c base w)
    (cv : Nat) (L : NodeId) (n : KNode)
    (hn : wNode c.p base w L = some n) (hnl : n.leaf = true)
    (htk : w'.taken = w.taken) (htop : w'.top = w.top)
    (hL' : wNode c.p base w' L = some (n.add c.i (.key cv w.next)))
    (hother : ∀ x, x ≠ L → wNode c.p base w' x = wNode c.p base w x)
    (hpar : ∀ q qn k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (k1, L) ∈ qn.live →
      k1 ≤ cv ∧ ∀ c'' z', (c'', z') ∈ qn.live → k1 < c'' → cv < c'') :
    PutInvT c base w' := by
  have hLnext : L < w.next := by
    have := hI.ids
    rcases (wNode_cases _ _ _ _ _ hn).2 with hl | ⟨_, hk⟩
    · exact this.1 L (by rw [hl]; rfl)
    · cases Nat.lt_or_ge L w.next with
      | inl h => exact h
      | inr h => rw [(hI.fresh L h).1] at hk; cases hk
  have hvN : wNode c.p base w w.next = none := by
    unfold wNode
    split
    · rfl
    · have hl : w.nodes.lookup w.next = none := by
        cases h' : w.nodes.lookup w.next with
        | none => rfl
        | some _ => have := hI.ids.1 w.next (by rw [h']; rfl); omega
      rw [hl]
      exact (hI.fresh w.next (Nat.le_refl _)).1
  have hvN' : wNode c.p base w' w.next = none := by
    rw [hother w.next (by omega)]; exact hvN
  have hwf := hI.wf L n hn
  have hnt := hI.times L n hn
  -- reachable after: reachable before, or the new value
  have hsub : ∀ x, ReachS (wNode c.p base w') c.i w'.top.rootKey x →
      ReachS (wNode c.p base w) c.i w.top.rootKey x ∨ x = w.next := by
    rw [htop]
    apply reachS_sub _ _ _ _ _ _ (Or.inl ReachS.root)
    intro x xn cc z hx hxn hz
    rcases hx with hx | hx
    · by_cases hxL : x = L
      · subst hxL
        rw [hL'] at hxn
        cases hxn
        rcases KNode.add_key_liveAt_mem n c.i cv w.next hwf hnt cc z hz with ⟨_, h2⟩ | ⟨_, h2⟩
        · exact Or.inr h2
        · exact Or.inl (ReachS.step x n cc z hx hn h2)
      · rw [hother x hxL] at hxn
        exact Or.inl (ReachS.step x xn cc z hx hxn hz)
    · subst hx; rw [hvN'] at hxn; cases hxn
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [htk]
    rcases hsub x hx with hx | hx
    · exact hI.untaken x hx
    · subst hx
      cases h' : w.taken.contains w.next with
      | false => rfl
      | true => have := hI.ids.2.2.1 _ h'; omega
  · intro q qn L2 n2 k1 hq hqn hql hn2 hnl2 hk
    have hqL : q ≠ L := by
      intro he; subst he; rw [hL'] at hqn; cases hqn
      rw [KNode.add_leaf] at hql; rw [hnl] at hql; cases hql
    rw [hother q hqL] at hqn
    have hq' : ReachS (wNode c.p base w) c.i w.top.rootKey q := by
      rcases hsub q hq with h | h
      · exact h
      · subst h; rw [hvN] at hqn; cases hqn
    by_cases hL2 : L2 = L
    · subst hL2
      rw [hL'] at hn2
      cases hn2
      exact leafOrderAt_add qn n k1 cv w.next c.i hwf hnt
        (hI.order q qn L2 n k1 hq' hqn hql hn hnl hk) (hpar q qn k1 hq' hqn hql hk)
    · rw [hother L2 hL2] at hn2
      exact hI.order q qn L2 n2 k1 hq' hqn hql hn2 hnl2 hk

/-! ## The rule -/

/-- A put of a key whose prefix is there into a segment leaf with room, below
an inner segment root, keeps `PutInv` (the writer's tree after it given). -/
theorem putInv_put_room_below (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hinner : ∀ m, wNode c.p base w rk = some m → m.leaf = false)
    (hroom : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) pre _ rk ReachS.root hrk
  refine writerWP_mono (writerWP_put_room_after c base hB.coherent pre cv h rk w hrk
    (fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
      (pre ++ [cv]) _ q.1 q.2 ReachS.root hq)) hroom) ?_
  intro _ w' ⟨L, n, hL, hn, hnl, htk, htop, hL', hother⟩
  have hLrk : L ≠ rk := by
    intro he; subst he; rw [hinner n hn] at hnl; cases hnl
  exact putInvT_room c base w w' hI cv L n hn hnl htk htop hL' hother
    (fun q qn k1 hq hqn _ hk => parentBound_of_descent c base w hI cv rk L hrrk hL hLrk q qn k1
      hq hqn hk)

/-- A put of a key of one segment into the space root, a leaf with room, keeps
`PutInv` (the writer's tree after it given). -/
theorem putInv_put_room_root (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (cv h : Nat) (w : W) (n : KNode)
    (hI : PutInv c base w) (hw : PutBook c B top0 w)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey → PutInv c base w') := by
  apply writerWP_putInv_of_T c base B top0 _ w hB hw
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hev : eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hroot, hnl]
  have hput := writerWP_put_room_after c base hB.coherent [] cv h w.top.rootKey w rfl
    (by
      intro q hq
      simp only [List.nil_append, fromVisits] at hq
      rw [hev] at hq
      simp only [List.mem_singleton] at hq
      subst hq
      exact hI.untaken _ ReachS.root)
    (by
      intro L n' hL hn' _
      rw [hev] at hL
      simp only [List.mem_singleton, Prod.mk.injEq, and_true] at hL
      subst hL
      rw [hroot] at hn'
      cases hn'
      exact hroom)
  refine writerWP_mono hput ?_
  intro _ w' ⟨L, n', hL, hn', hnl', htk, htop, hL', hother⟩
  rw [hev] at hL
  simp only [List.mem_singleton, Prod.mk.injEq, and_true] at hL
  subst hL
  exact putInvT_room c base w w' hI cv _ n' hn' hnl' htk htop hL' hother
    (fun q qn k1 hq hqn _ hk => absurd ⟨qn, hqn, by
      rw [← KNode.liveAt_of_times qn c.i (hI.times q qn hqn)] at hk; exact hk⟩
      (hI.tree.rootFree q k1 (reachS_tReach _ _ _ q hq)))

end SIS.Tree
