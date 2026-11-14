import SIS.Tree.GetAssembly
import SIS.Tree.GetLeafBelow
import SIS.Tree.GetNewSegFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The operation cases of the assembly, proved (bergdb 024-12, TP10): each
writer-level rule takes premises on the writer's state (the klongs well formed,
no node on the key's path taken back, the next id free, the key's leaf named by
the key alone); `PutInv` gives them, and the case gives the leaf's room. With
them, a case's `OpGetCaseOK` follows from its rule: (1) a put into a leaf with
room (`opGetCaseOK_putLeafRoom`), (6) a delete whose bitmap changes nothing
(`opGetCaseOK_delNoop`), (8) a delete into a leaf with room for the bitmap
(`opGetCaseOK_delRoom`). -/

/-! ## The rules' premises from `PutInv` -/

/-- An operation of a transaction within reach has a well formed key. -/
theorem within_op_keyWf (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (pre : List Op) (op : Op) (post : List Op) (h : tx.ops = pre ++ op :: post) :
    keyWf op.key = true := by
  have h1 := (hw.1 tx (by simp)).2
  unfold Tx.wf at h1
  rw [List.all_eq_true] at h1
  exact h1 op (by rw [h]; simp)

theorem PutInv.pathUntaken {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (key : Key) : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key w.top.rootKey,
      w.taken.contains q.1 = false :=
  fun q hq => hI.untaken q.1 (fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn)
    key _ q.1 q.2 ReachS.root hq)

theorem PutInv.nextFree {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w) :
    w.taken.contains w.next = false ∧ w.vals.lookup w.next = none := by
  obtain ⟨_, _, hidt, hidvals, _⟩ := hI.ids
  refine ⟨?_, ?_⟩
  · cases h' : w.taken.contains w.next with
    | false => rfl
    | true => have := hidt _ h'; omega
  · apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega

theorem PutInv.leafFresh {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w) :
    ∀ key' x c' n' y, (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → (n'.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next := by
  intro key' x c' n' y hx hn' _ hs
  have hrx := fromVisits_reach _ _ _ _ (fun x xn _ hn => hI.wf x xn hn) key' _ x c' ReachS.root hx
  cases hfd : n'.searchEq c.i c' with
  | none => rw [hfd] at hs; cases hs
  | some fd =>
    rw [hfd] at hs
    simp only [Option.map_some, Option.some.injEq] at hs
    subst hs
    have := hI.links x n' c' fd.y hrx hn' (KNode.searchEq_mem n' c.i c' fd (hI.wf x n' hn') hfd)
    omega

theorem PutInv.keyUniq {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) :
    ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv] :=
  fun key' x _ hkey' h1 h2 _ _ =>
    visits_unique_seg_of_tree _ _ _ _ hI.tree hI.wf pre cv rk hkey hrk key' x hkey' h1 h2

/-- What holds of the key's leaf holds of every leaf of the descent. -/
theorem keyLeaf_all {c : Ctx} {base : View BVal} {w : W} {pre : List Nat} {cv : Nat}
    {L : NodeId} {n : KNode} {rk : NodeId} (hK : KeyLeaf c base w pre cv L n)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (P : KNode → Prop) (hP : P n) :
    ∀ L' n', (L', cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L' = some n' → n'.leaf = true → P n' := by
  obtain ⟨rk', hrk', hL, hn, hnl⟩ := hK
  rw [hrk] at hrk'
  cases hrk'
  intro L' n' hL' hn' hnl'
  have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
  subst he
  rw [hn] at hn'
  cases hn'
  exact hP

theorem keyLeaf_rk {c : Ctx} {base : View BVal} {w : W} {pre : List Nat} {cv : Nat}
    {L : NodeId} {n : KNode} (hK : KeyLeaf c base w pre cv L n) :
    ∃ rk, segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk ∧
      wNode c.p base w L = some n :=
  let ⟨rk, hrk, _, hn, _⟩ := hK
  ⟨rk, hrk, hn⟩

/-! ## A delete's bitmap with room, the room as the writer checks it -/

/-- `writerWP_del_bitmap_seg` with the room of `DelRoom`: the writer checks the
room of the branch it takes, the bitmap put in place of the leaf's last one or
added. -/
theorem writerWP_del_bitmap_segR (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (hfuel : 1 ≤ c.p.fuel)
    (hmerges : c.p.merges = false) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some m → m.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_putSegs_prefix c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
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
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, hget⟩
  rw [hr0.1] at hn hvisL hget
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := hleaf L n hvisL hn hnl
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  suffices hfin : ∀ (n2 : KNode) (w6 : W), n2.leaf = true → w6.top = w.top →
      w6.taken = w.taken → w6.vals = w.vals →
      (∀ x, w6.nodes.lookup x = if x = L then some n2 else w3.nodes.lookup x) →
      (∀ c', ((n2.searchEq c.i c').map (·.y)) =
        if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
      ∀ key', keyWf key' = true → wGet c.p c.i base w6 key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key' by
    unfold pathSize deleteUpward
    wpSimplify
    rw [writerWP_getNode_known L n c _ hlk3]
    have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
      simpa using hne
    simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
    wpSimplify
    refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
    unfold appendDeleteKlong
    wpSimplify
    rw [writerWP_getNode_known L n c _ hlk3]
    split
    · exact writerWP_throw _ _ _ _
    · simp only [hnb, Bool.not_false, ↓reduceIte]
      have hcont : ∀ (n2 : KNode), n2.leaf = true →
          (∀ c', ((n2.searchEq c.i c').map (·.y)) =
            if c' == cv then none else (n.searchEq c.i c').map (·.y)) →
          ∀ (s : String), WriterWP (do note s; putNode L n2; pure false) c w3 (fun _ w' =>
            WriterWP (afterDelete (pre ++ [cv]) gh.1 gh.2) c w' (fun _ w'' =>
              WriterWP (do let _ ← fresh; pure false) c w''
                (fun _ w''' => ∀ key', keyWf key' = true → wGet c.p c.i base w''' key' =
                  if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
                  else wGet c.p c.i base w key'))) := by
        intro n2 hl2 hs2 s
        unfold note putNode afterDelete
        wpSimplify
        simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
        unfold fresh
        wpSimplify
        refine hfin n2 _ hl2 ?_ ?_ ?_ ?_ hs2
        · exact hr03.2.1
        · exact hr03.2.2.1
        · exact hr03.2.2.2.1
        · intro x; exact lookup_upsert _ _ _ _
      have hsetAt : ∀ old, n.ks.getLast? = some (.del old) →
          ∀ c', (((n.setAt (n.size - 1) (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).searchEq
            c.i c').map (·.y)) = if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
        intro old hlast c'
        have hw' := KNode.setAt_delete_wf n cv old hwf hlast
        rw [KNode.searchEq_live _ c.i hw' (KNode.setAt_last_times n old _ c.i hlast htimes),
          KNode.setAt_delete_live_lookup n cv c' old hlast, KNode.searchEq_live n c.i hwf htimes]
      have hadd : ∀ c', (((n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).searchEq
            c.i c').map (·.y)) = if c' == cv then none else (n.searchEq c.i c').map (·.y) := by
        intro c'
        have hw' := KNode.add_delete_wf n c.i cv hwf hne
        rw [KNode.searchEq_live _ c.i hw' (KNode.add_times n c.i _ (fun s h => by cases h) htimes),
          KNode.add_delete_live_lookup n c.i cv c', KNode.searchEq_live n c.i hwf htimes]
      split
      · rename_i _ old hlast
        by_cases hlt : n.lastTime = some c.i
        · have hb : (n.lastTime == some c.i) = true := by simp [hlt]
          have hd1 : deadOver c.p (n.setAt (n.size - 1)
              (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
            rcases hroomD with ⟨_, _, h⟩ | ⟨hno, _, _⟩
            · exact h
            · exact absurd ⟨⟨old, hlast⟩, hlt⟩ hno
          simp only [hb, Bool.and_self, ↓reduceIte, hd1, Bool.false_eq_true]
          exact hcont _ (by rw [KNode.setAt_leaf]; exact hnl) (hsetAt old hlast) _
        · have hb : (n.lastTime == some c.i) = false := by simpa using hlt
          obtain ⟨hsize, hd2⟩ : n.size + 1 < c.p.M ∧
              deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
            rcases hroomD with ⟨_, h2, _⟩ | ⟨_, hs, hd⟩
            · exact absurd h2 hlt
            · exact ⟨hs, hd⟩
          simp only [hb, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hsize, hd2]
          exact hcont _ (by rw [KNode.add_leaf]; exact hnl) hadd _
      · rename_i _ hnot
        obtain ⟨hsize, hd2⟩ : n.size + 1 < c.p.M ∧
            deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
          rcases hroomD with ⟨⟨old, hl⟩, _, _⟩ | ⟨_, hs, hd⟩
          · exact absurd hl (hnot old)
          · exact ⟨hs, hd⟩
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, hsize, hd2]
        exact hcont _ (by rw [KNode.add_leaf]; exact hnl) hadd _
  intro n2 w6 hl2 h6top h6taken h6vals h6nodes hs2
  have hN : ∀ x, x ≠ L → wNode c.p base w x = wNode c.p base w6 x := by
    intro x hx
    rw [← hr03.1]
    simp only [wNode, h6taken, h6nodes, hx, ↓reduceIte, hr03.2.2.1]
  have hNL : wNode c.p base w6 L = some n2 := by
    simp only [wNode, h6taken, hLt, Bool.false_eq_true, ↓reduceIte, h6nodes]
  have hV : ∀ y, wValue base w y = wValue base w6 y := by
    intro y; simp only [wValue, h6taken, h6vals]
  obtain ⟨hown, hother⟩ := wGet_leaf_change_seg c.p base c.i w w6 L pre cv rk n n2 hfuel h6top hN
    hn hNL hnl hl2 (fun c' hc' => by
      rw [hs2 c']
      have hb : (c' == cv) = false := by simpa using hc'
      rw [hb]; rfl)
    hrk (keyWf_last_notin pre cv hkey) hvisL huniq (fun _ _ _ _ y _ _ _ _ _ => hV y)
  intro key' hkey'
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    rw [hown, hs2 cv]
    simp
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    exact hother key' hkey' (fun h => hk h.symm)

/-! ## The cases -/

theorem fuel_pos (p : Params) : 1 ≤ p.fuel := by unfold Params.fuel; omega

/-- (1) A put into a leaf with room. -/
theorem opGetCaseOK_putLeafRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpGetCaseOK p R PutLeafRoomCase := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI _ hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hroom⟩ := hP
  subst hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_put_room_seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h rk
    w (fuel_pos p) hkey hrk (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧ m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)
      ⟨hI.wf L n hn, hI.times L n hn, hroom.1, hroom.2⟩)
    hI.nextFree (hI.keyUniq pre cv rk hkey hrk) hI.leafFresh) ?_
  intro _ w' hpost _ key hk
  exact hpost key hk

/-- (6) A delete whose bitmap changes nothing. -/
theorem opGetCaseOK_delNoop (p : Params) (R : Struct BVal → Time → Prop) :
    OpGetCaseOK p R DelNoopCase := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ hP
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_del_noop_seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk
    w hrk (hI.pathUntaken _) (keyLeaf_all hK hrk (fun m => klongsWf m.ks = true ∧
      (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
      bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap)
      ⟨hI.wf L n hn, hI.times L n hn, hnoop⟩)) ?_
  intro _ w' hpost _ key hk
  exact hpost key hk

/-- (8) A delete into a leaf that keeps a live klong and has room for the
bitmap. -/
theorem opGetCaseOK_delRoom (p : Params) (R : Struct BVal → Time → Prop) :
    OpGetCaseOK p R DelRoomCase := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI _ hP
  obtain ⟨pre, cv, L, n, hop, hmerges, hK, hne, hkeep, hroom⟩ := hP
  subst hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn⟩ := keyLeaf_rk hK
  refine writerWP_mono (writerWP_del_bitmap_segR (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv
    rk w (fuel_pos p) hmerges hkey hrk (hI.pathUntaken _) (keyLeaf_all hK hrk
      (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
      ⟨hI.wf L n hn, hI.times L n hn, hne, hkeep, hroom⟩)
    (hI.keyUniq pre cv rk hkey hrk)) ?_
  intro _ w' hpost _ key hk
  exact hpost key hk

/-! ## A delete of a key with no leaf -/

/-- A search that finds a pointer ends at a leaf of its visits. -/
theorem getEqR_leafVisit (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x y : NodeId), getEqR N t cv f x = some y →
      ∃ L n, (L, cv) ∈ eqVisits N t cv f x ∧ N L = some n ∧ n.leaf = true := by
  intro f
  induction f with
  | zero => intro x y h; simp [getEqR] at h
  | succ f ih =>
    intro x y h
    simp only [getEqR] at h
    cases hx : N x with
    | none => rw [hx] at h; cases h
    | some n =>
      rw [hx] at h
      simp only at h
      by_cases hl : n.leaf = true
      · exact ⟨x, n, by simp [eqVisits], hx, hl⟩
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        cases hs : n.searchLte t cv with
        | none => rw [hs] at h; cases h
        | some fd =>
          rw [hs] at h
          obtain ⟨L, m, hL, hm, hml⟩ := ih fd.y y h
          refine ⟨L, m, ?_, hm, hml⟩
          simp only [eqVisits, hx, hl, Bool.false_eq_true, ↓reduceIte, hs, List.mem_cons]
          exact Or.inr hL

theorem getEqR_start_isSome (N : NodeId → Option KNode) (t : Time) (cv : Nat) (f : Nat)
    (x y : NodeId) (h : getEqR N t cv f x = some y) : (N x).isSome = true := by
  cases f with
  | zero => simp [getEqR] at h
  | succ f =>
    simp only [getEqR] at h
    cases hx : N x with
    | none => rw [hx] at h; cases h
    | some _ => rfl

theorem eqVisits_start_isSome (N : NodeId → Option KNode) (t : Time) (cv : Nat) (f : Nat)
    (x L : NodeId) (n : KNode) (hL : (L, cv) ∈ eqVisits N t cv f x) (hn : N L = some n) :
    (N x).isSome = true := by
  cases f with
  | zero => simp [eqVisits] at hL
  | succ f =>
    cases hx : N x with
    | some _ => rfl
    | none =>
      simp only [eqVisits, hx, List.mem_cons, Prod.mk.injEq, and_true, List.not_mem_nil,
        or_false] at hL
      subst hL
      rw [hx] at hn
      cases hn

theorem segRootR_start_isSome (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (cv : Nat)
    (pre : List Nat) (y rk L : NodeId) (n : KNode) (hrk : segRootR N t fuel pre y = some rk)
    (hL : (L, cv) ∈ eqVisits N t cv fuel rk) (hn : N L = some n) : (N y).isSome = true := by
  cases pre with
  | nil =>
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    exact eqVisits_start_isSome N t cv fuel _ L n hL hn
  | cons c0 rest =>
    simp only [segRootR] at hrk
    cases hg : getEqR N t c0 fuel y with
    | none => rw [hg] at hrk; cases hrk
    | some _ => exact getEqR_start_isSome N t c0 fuel y _ hg

/-- The key has no leaf from r: no prefix's segment root whose descent for the
last segment ends at a leaf. -/
def NoLeafFrom (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (key : List Nat)
    (r : NodeId) : Prop :=
  ¬ ∃ pre cv rk L n, key = pre ++ [cv] ∧ segRootR N t fuel pre r = some rk ∧
    (L, cv) ∈ eqVisits N t cv fuel rk ∧ N L = some n ∧ n.leaf = true

/-- A key with no leaf reads as no value. -/
theorem getFromR_noLeaf (N : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (key : List Nat) (r : NodeId) (hne : key ≠ []) (hno : NoLeafFrom N t fuel key r) :
    getFromR N V t fuel key r = none := by
  obtain ⟨pre, cv, hk⟩ : ∃ pre cv, key = pre ++ [cv] :=
    ⟨key.dropLast, key.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  subst hk
  rw [getFromR_append]
  cases hs : segRootR N t fuel pre r with
  | none => rfl
  | some rk =>
    simp only [Option.bind_some, getFromR]
    cases hg : getEqR N t cv fuel rk with
    | none => rfl
    | some y =>
      obtain ⟨L, n, hL, hn, hnl⟩ := getEqR_leafVisit N t cv fuel rk y hg
      exact absurd ⟨pre, cv, rk, L, n, rfl, hs, hL, hn, hnl⟩ hno

/-- The writer's delete of a key with no leaf reads only: the walk stops at the
first segment that is not there (or fails). -/
theorem writerWP_putSegs_del_noLeaf (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) :
    ∀ (sfx : List Nat) (r : NodeId) (w : W), sfx ≠ [] →
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel sfx r, w.taken.contains q.1 = false) →
      NoLeafFrom (wNode c.p base w) c.i c.p.fuel sfx r →
      WriterWP (putSegs key none sfx r) c w (fun _ w' => ReadsAs c.p base w w') := by
  intro sfx
  induction sfx with
  | nil => intro r w h; exact absurd rfl h
  | cons s rest ih =>
    intro r w _ ht hno
    cases rest with
    | nil =>
      rw [putSegs.eq_2]
      unfold setValue
      wpSimplify
      refine writerWP_mono (writerWP_descendLte_reads s c base hvc c.p.fuel r w
        (fun q hq => ht q (by simpa [fromVisits] using hq))) ?_
      intro L w3 ⟨_, n, hn, hnl, _, hvis, _⟩
      exact absurd ⟨[], s, r, L, n, rfl, rfl, hvis, hn, hnl⟩ hno
    | cons d rest' =>
      rw [putSegs.eq_3 key none r s (d :: rest') (by simp)]
      simp only [fromVisits] at ht
      have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
          w.taken.contains q.1 = false := fun q hq => ht q (List.mem_append_left _ hq)
      unfold setNode
      wpSimplify
      refine writerWP_mono (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1) ?_
      intro L w3 ⟨hr3, n, hn, hnl, hlk3, _, hget⟩
      rw [writerWP_getNode_known L n c _ hlk3]
      cases hfd : n.searchEq c.i s with
      | none =>
        simp only [Option.isSome_none, Bool.not_false, ↓reduceIte, writerWP_pure]
        exact hr3
      | some fd =>
        rw [hfd] at hget
        simp only [Option.map_some] at hget
        simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
        generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, fd.y)] } : W) = w4
        have hr04 : ReadsAs c.p base w w4 := by
          subst hw4
          exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
        refine writerWP_mono (ih fd.y w4 (by simp) ?_ ?_)
          (fun _ w' h => ReadsAs.trans _ _ _ _ _ hr04 h)
        · intro q hq
          rw [hr04.2.2.1]
          rw [hr04.1] at hq
          apply ht q
          apply List.mem_append_right
          rw [hget]
          exact hq
        · rintro ⟨pre, cv, rk, L', n', hsplit, hrk, hvis', hn', hnl'⟩
          rw [hr04.1] at hrk hvis' hn'
          apply hno
          refine ⟨s :: pre, cv, rk, L', n', by rw [hsplit]; rfl, ?_, hvis', hn', hnl'⟩
          have hy := segRootR_start_isSome _ _ _ cv pre fd.y rk L' n' hrk hvis' hn'
          simp only [segRootR, hget, hy, ↓reduceIte]
          exact hrk

/-- (5) A delete of a key that has no leaf. -/
theorem opGetCaseOK_delNoLeaf (p : Params) (R : Struct BVal → Time → Prop) :
    OpGetCaseOK p R DelNoLeafCase := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI _ hP
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  have hnone : runGet p ts w key = none := by
    unfold runGet wGet
    exact getFromR_noLeaf _ _ _ _ key _ hne hno'
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
    subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  refine writerWP_mono (writerWP_putSegs_del_noLeaf (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key
    key w.top.rootKey w2 hne ?_ ?_) ?_
  · intro q hq
    rw [hr02.2.2.1]
    rw [hr02.1] at hq
    exact hI.pathUntaken key q hq
  · rw [hr02.1]; exact hno'
  · intro _ w' hr' _ key' _
    have hr : ReadsAs p (viewOf (treeRun p ts)) w w' := ReadsAs.trans _ _ _ _ _ hr02 hr'
    have hsame : runGet p ts w' key' = runGet p ts w key' := by
      unfold runGet wGet
      rw [hr.1, hr.2.1, ReadsAs.value _ _ _ _ hr]
    rw [hsame]
    by_cases hk : key = key'
    · subst hk
      simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
      exact hnone
    · have hk' : (key == key') = false := by simpa using hk
      simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]

/-! ## The order premises from the walk's ranges -/

/-- `OrdG` from the walk's ranges. -/
theorem ordG_of_rangeOrder (c : Ctx) (N : NodeId → Option KNode) (r : NodeId)
    (hR : RangeOrder N c.i r) (htimes : ∀ x n, N x = some n → ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) :
    OrdG c N r := by
  intro q qn x xn K hq hqn hql hK hxn _ _ c' z hz
  obtain ⟨lo, hi, hqr⟩ := reachR_of_reachS N c.i r q (tReach_reachS N c.i r q hq)
  obtain ⟨b, hb⟩ := childBounds_exists (qn.liveAt c.i) hi (K, x) hK
  have hrange := hR x _ b xn (ReachR.inner q qn lo hi K x b hqr hqn hql hb) hxn
  have hz' : (c', z) ∈ xn.liveAt c.i := by
    rw [KNode.liveAt_of_times xn c.i (htimes x xn hxn)]; exact hz
  have hlow := (hrange (c', z) hz').1
  dsimp only at hlow
  by_cases h0 : K = 0
  · subst h0
    split <;> omega
  · have hb0 : (K == 0) = false := by simpa using h0
    simp only [hb0, Bool.false_eq_true, ↓reduceIte] at hlow
    exact hlow

/-- The order of the cascade's rules (`hrangeG`) from the walk's ranges. -/
theorem rangeG_of_rangeOrder (c : Ctx) (N : NodeId → Option KNode) (r : NodeId)
    (hR : RangeOrder N c.i r) (htimes : ∀ x n, N x = some n → ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) :
    ∀ q qn x xn K, TReach N c.i r q → N q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      N x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'' := by
  intro q qn x xn K hq hqn hql hK hxn _ c' z hz hpos
  obtain ⟨lo, hi, hqr⟩ := reachR_of_reachS N c.i r q (tReach_reachS N c.i r q hq)
  obtain ⟨b, hb⟩ := childBounds_exists (qn.liveAt c.i) hi (K, x) hK
  have hrange := hR x _ b xn (ReachR.inner q qn lo hi K x b hqr hqn hql hb) hxn
  have hz' : (c', z) ∈ xn.liveAt c.i := by
    rw [KNode.liveAt_of_times xn c.i (htimes x xn hxn)]; exact hz
  obtain ⟨hlow, hhigh⟩ := hrange (c', z) hz'
  dsimp only at hlow hhigh
  refine ⟨?_, ?_⟩
  · by_cases h0 : K = 0
    · omega
    · have hb0 : (K == 0) = false := by simpa using h0
      simp only [hb0, Bool.false_eq_true, ↓reduceIte] at hlow
      split at hlow <;> omega
  · intro c'' z' hz2 hlt
    have hz3 : (c'', z') ∈ qn.liveAt c.i := by
      rw [KNode.liveAt_of_times qn c.i (htimes q qn hqn)]; exact hz2
    obtain ⟨upper, hub, hle⟩ := childBounds_next_le (qn.liveAt c.i) hi (KNode.liveAt_order qn c.i)
      (K, x) b hb (c'', z') hz3 hlt
    rw [hub] at hhigh
    simp only [UpperBound] at hhigh
    simp only at hle
    omega

/-- Two live klongs in a node that space splits, when the split threshold is 2
or more. -/
theorem lenG_of_splitAbove (c : Ctx) (N : NodeId → Option KNode) (r : NodeId)
    (hsa : 2 ≤ c.p.splitAbove) :
    ∀ x xn, TReach N c.i r x → N x = some xn → ¬ ChainRoom c xn →
      c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length := by
  intro x xn _ _ _ hlt
  have := KNode.lastVersion_size xn c.i
  simp only [KNode.cnt] at this
  omega

/-- The global parts of `PutInv` at every state of a transaction within reach. -/
theorem putInvG_reached (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (z : NodeId) (top : Top)
    (htop : topOf p (ctxOf p ts).view z = .ok top) (pre : List Op) (r : List Bool) (w : W)
    (hpre : (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w)) :
    PutInvG (ctxOf p ts) (viewOf (treeRun p ts)) w :=
  putInvG_of_book _ _ _ _ _ (putBase_of_run p ts tx hw hR)
    (putBook_reached p ts tx hw hR z top htop pre r w hpre)

/-- (2) A put into a full leaf: the cascade of splits. -/
theorem opGetCaseOK_putLeafFull (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) (hsa : 2 ≤ p.splitAbove) :
    OpGetCaseOK p R PutLeafFullCase := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hP
  obtain ⟨pre, cv, h, L, n, hop, hK, hfull⟩ := hP
  subst hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hG := putInvG_reached p ts tx hw (hR _ _ hr) z top htop ops r w hpre
  have hOrd := ordG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times
  refine writerWP_mono (writerWP_put_accessPathR (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv h
    rk w hkey hrk (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
    (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hI.keyNoValue
    (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
    (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr hOrd)
    (keyLeaf_all hK hrk (fun m => ¬ (m.size + 1 < (ctxOf p ts).p.M ∧
      deadOver (ctxOf p ts).p (m.add (ctxOf p ts).i (.key cv w.next)) = false)) hfull)
    (hI.keyUniq pre cv rk hkey hrk)) ?_
  intro _ w' hpost hfit key hk
  exact hpost.2.2.2 (Or.inl hfit) key hk

/-! ## A put of a key with no leaf -/

/-- A point where a put makes new segments: the key's prefix pre is there, and
the leaf of its next segment c0 has no klong of c0. -/
def NewSegFrom (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (key : List Nat)
    (r : NodeId) : Prop :=
  ∃ pre c0 tail rk0 L n, key = pre ++ c0 :: tail ∧ tail ≠ [] ∧
    segRootR N t fuel pre r = some rk0 ∧ (L, c0) ∈ eqVisits N t c0 fuel rk0 ∧ N L = some n ∧
    n.leaf = true ∧ n.searchEq t c0 = none

/-- A put of a key with no leaf and no point to make new segments at fails: the
writer's walk ends below a missing node or a descent that finds no leaf. -/
theorem writerWP_putSegs_put_fail (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (h : Nat) :
    ∀ (sfx : List Nat) (r : NodeId) (w : W), sfx ≠ [] →
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel sfx r, w.taken.contains q.1 = false) →
      NoLeafFrom (wNode c.p base w) c.i c.p.fuel sfx r →
      ¬ NewSegFrom (wNode c.p base w) c.i c.p.fuel sfx r →
      WriterWP (putSegs key (some h) sfx r) c w (fun _ _ => False) := by
  intro sfx
  induction sfx with
  | nil => intro r w h; exact absurd rfl h
  | cons s rest ih =>
    intro r w _ ht hno hns
    cases rest with
    | nil =>
      rw [putSegs.eq_2]
      unfold setValue
      wpSimplify
      refine writerWP_mono (writerWP_descendLte_reads s c base hvc c.p.fuel r w
        (fun q hq => ht q (by simpa [fromVisits] using hq))) ?_
      intro L w3 ⟨_, n, hn, hnl, _, hvis, _⟩
      exact absurd ⟨[], s, r, L, n, rfl, rfl, hvis, hn, hnl⟩ hno
    | cons d rest' =>
      rw [putSegs.eq_3 key (some h) r s (d :: rest') (by simp)]
      simp only [fromVisits] at ht
      have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
          w.taken.contains q.1 = false := fun q hq => ht q (List.mem_append_left _ hq)
      unfold setNode
      wpSimplify
      refine writerWP_mono (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1) ?_
      intro L w3 ⟨hr3, n, hn, hnl, hlk3, hvis, hget⟩
      rw [writerWP_getNode_known L n c _ hlk3]
      cases hfd : n.searchEq c.i s with
      | none =>
        exact absurd ⟨[], s, d :: rest', r, L, n, rfl, by simp, rfl, hvis, hn, hnl, hfd⟩ hns
      | some fd =>
        rw [hfd] at hget
        simp only [Option.map_some] at hget
        simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
        generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, fd.y)] } : W) = w4
        have hr04 : ReadsAs c.p base w w4 := by
          subst hw4
          exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
        refine ih fd.y w4 (by simp) ?_ ?_ ?_
        · intro q hq
          rw [hr04.2.2.1]
          rw [hr04.1] at hq
          apply ht q
          apply List.mem_append_right
          rw [hget]
          exact hq
        · rintro ⟨pre, cv, rk, L', n', hsplit, hrk, hvis', hn', hnl'⟩
          rw [hr04.1] at hrk hvis' hn'
          apply hno
          refine ⟨s :: pre, cv, rk, L', n', by rw [hsplit]; rfl, ?_, hvis', hn', hnl'⟩
          have hy := segRootR_start_isSome _ _ _ cv pre fd.y rk L' n' hrk hvis' hn'
          simp only [segRootR, hget, hy, ↓reduceIte]
          exact hrk
        · rintro ⟨pre, c0, tail, rk0, L', n', hsplit, htail, hrk, hvis', hn', hnl', hnone⟩
          rw [hr04.1] at hrk hvis' hn'
          apply hns
          refine ⟨s :: pre, c0, tail, rk0, L', n', by rw [hsplit]; rfl, htail, ?_, hvis', hn', hnl',
            hnone⟩
          have hy := segRootR_start_isSome _ _ _ c0 pre fd.y rk0 L' n' hrk hvis' hn'
          simp only [segRootR, hget, hy, ↓reduceIte]
          exact hrk

/-- The leaf of a new segment's point is visited by the keys of its prefix and
segment alone. -/
theorem newSeg_leaf_keys {c : Ctx} {base : View BVal} {w : W} (hI : PutInv c base w)
    (pre : List Nat) (c0 : Nat) (rk0 L : NodeId)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hL : (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0) :
    (∀ key', keyWf key' = true →
      (L, c0) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      ∃ rest', key' = pre ++ c0 :: rest') ∧
    ∀ c', (L, c') ∉ fromVisits (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey := by
  have hrkp : TPathK (wNode c.p base w) c.i w.top.rootKey rk0 pre := by
    have := segRootR_tPathK _ _ _ _ hI.wf pre _ [] rk0 TPathK.root hrk
    simpa using this
  have hLp := (eqVisits_tPathK _ _ _ c0 _ rk0 pre hrkp L c0 hL).1
  refine ⟨?_, ?_⟩
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

/-- (3) A put of a key with no leaf: new segments, below a leaf with room or
with the cascade of splits. -/
theorem opGetCaseOK_putNewSeg (p : Params) (R : Struct BVal → Time → Prop)
    (hR : ∀ P t, R P t → RunLinksOK p P t) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove) :
    OpGetCaseOK p R PutNewSegCase := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hP
  obtain ⟨key, h, hop, hno⟩ := hP
  subst hop
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  have hno' : NoLeafFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey := by
    rintro ⟨pre, cv, rk, L, n, hsplit, hrk, hvis, hn, hnl⟩
    exact hno ⟨pre, cv, L, n, hsplit, rk, hrk, hvis, hn, hnl⟩
  by_cases hseg : NewSegFrom (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) p.fuel key
      w.top.rootKey
  · obtain ⟨pre, c0, tail, rk0, L, n, hk, htail, hrk0, hL, hn, hnl, hnone⟩ := hseg
    subst hk
    have hone : ∀ L' n', (L', c0) ∈ eqVisits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1)
        c0 p.fuel rk0 → wNode p (viewOf (treeRun p ts)) w L' = some n' → n'.leaf = true →
        L' = L ∧ n' = n := by
      intro L' n' hL' hn' hnl'
      have he := eqVisits_leaf_unique _ _ _ _ _ _ _ _ _ hL' hL hn' hnl' hn hnl
      subst he
      rw [hn] at hn'
      exact ⟨rfl, (Option.some.inj hn').symm⟩
    by_cases hroom : n.size + 1 < p.M
    · refine writerWP_mono (writerWP_put_newSegs_inv (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0
        h tail htail rk0 w hI hM hrk0 (fun L' n' hL' hn' hnl' => by
          obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
          subst he1 he2
          exact ⟨hnone, hroom⟩)) ?_
      intro _ w' hpost _ key' hk
      exact hpost key' hk
    · have hG := putInvG_reached p ts tx hw (hR _ _ hr) z top htop ops r w hpre
      have hOrd := ordG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times
      obtain ⟨hkeys, hnotpre⟩ := newSeg_leaf_keys hI pre c0 rk0 L hrk0 hL
      refine writerWP_mono (writerWP_put_newSegFullR (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre c0
        h tail htail rk0 w hM hrk0 (hI.pathUntaken _) hI.ids hI.fresh hI.wf hI.times hI.tree
        (fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl) hI.keyNoValue
        (rangeG_of_rangeOrder (ctxOf p ts) _ _ hRO hI.times)
        (lenG_of_splitAbove (ctxOf p ts) _ _ hsa)
        (fun _ _ _ _ _ _ _ _ _ _ _ _ => Or.inr hOrd)
        (fun L' n' hL' hn' hnl' => by
          obtain ⟨he1, he2⟩ := hone L' n' hL' hn' hnl'
          subst he1 he2
          exact ⟨hnone, hroom, hkeys, hnotpre⟩)) ?_
      intro _ w' hpost hfit key' hk
      exact hpost.2.2.2.1 (Or.inl hfit) key' hk
  · unfold putKv pathClear findRoot pathAdd
    wpSimplify
    generalize hw2 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
    have hr02 : ReadsAs (ctxOf p ts).p (viewOf (treeRun p ts)) w w2 := by
      subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    refine writerWP_mono (writerWP_putSegs_put_fail (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key h
      key w.top.rootKey w2 hne ?_ ?_ ?_) (fun _ _ hf => hf.elim)
    · intro q hq
      rw [hr02.2.2.1]
      rw [hr02.1] at hq
      exact hI.pathUntaken key q hq
    · rw [hr02.1]; exact hno'
    · rw [hr02.1]; exact hseg

/-! ## The delete's cases with the merges on -/

/-- (7) is void with the merges on: its case has them off. -/
theorem opGetCaseOK_delEmpty_merges (p : Params) (R : Struct BVal → Time → Prop)
    (hm : p.merges = true) : OpGetCaseOK p R DelEmptyCase := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨_, _, _, _, _, hmf, _⟩ := hP
  have h : p.merges = false := hmf
  rw [hm] at h
  cases h

/-- (9) is void with the merges on: its case has them off. -/
theorem opGetCaseOK_delFull_merges (p : Params) (R : Struct BVal → Time → Prop)
    (hm : p.merges = true) : OpGetCaseOK p R DelFullCase := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨_, _, _, _, _, hmf, _⟩ := hP
  have h : p.merges = false := hmf
  rw [hm] at h
  cases h

/-! ## The assembly with the cases proved -/

/-- `getOK_scanOK_of_open_runOK` with the cases (1), (2), (3), (5), (6) and (8)
proved, for a node size and a split threshold of 2 or more: left of the cases
are the delete's merges (4), the upward delete (7) and the split of the
delete's full leaf (9). -/
theorem getOK_scanOK_of_open_cases (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpTreeOK p) (hP : OpPutInvOK p (RunOK p)) (hO : OpRangeOK p (RunOK p))
    (hfit : TxSegFitsOK p (RunOK p))
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) (c7 : OpGetCaseOK p (RunOK p) DelEmptyCase)
    (c9 : OpGetCaseOK p (RunOK p) DelFullCase) :
    GetOK p ∧ ScanOK p :=
  getOK_scanOK_of_open_runOK p hinv hlinks htree ho hP hO hfit
    (opGetCaseOK_putLeafRoom p _) (opGetCaseOK_putLeafFull p _ (fun _ _ h => h.1) hsa)
    (opGetCaseOK_putNewSeg p _ (fun _ _ h => h.1) hM hsa) c4 (opGetCaseOK_delNoLeaf p _)
    (opGetCaseOK_delNoop p _) c7 (opGetCaseOK_delRoom p _) c9

/-- `getOK_scanOK_of_open_cases` for TP7's parameters with the merges
(`MergeParamsOK`): of the cases, only the delete's merges (4) is left; (7) and
(9) are void with the merges on. -/
theorem getOK_scanOK_of_open_merges (p : Params) (hp : MergeParamsOK p) (hinv : InvPreserved p)
    (hlinks : ∀ ts, Within p ts → RunLinksOK p (treeRun p ts) ts.length)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (ho : OpTreeOK p) (hP : OpPutInvOK p (RunOK p)) (hO : OpRangeOK p (RunOK p))
    (hfit : TxSegFitsOK p (RunOK p)) (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hm : p.merges = true := by
    unfold MergeParamsOK at hp; unfold Params.merges; simp only [decide_eq_true_eq]; omega
  unfold MergeParamsOK at hp
  exact getOK_scanOK_of_open_cases p (by omega) (by omega) hinv hlinks htree ho hP hO hfit c4
    (opGetCaseOK_delEmpty_merges p _ hm) (opGetCaseOK_delFull_merges p _ hm)

end SIS.Tree
