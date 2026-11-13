/-
The take-back's (B) and (C) together per operation case (bergdb 024-12, TP7;
`TakeJ2`), the cases of latest's assembly (`opCase_cover`, GetAssembly.lean):
the rule lemmas with the room of the branch the writer takes (`DelRoom`).
-/
import SIS.Tree.TakeDeadUpW
import SIS.Tree.GetCaseBridge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option linter.unusedSimpArgs false in
/-- `writerWP_appendDeleteKlong_room_exact` with the room of the branch the
writer takes (`DelRoom`). -/
theorem writerWP_appendDeleteKlong_room_exactD (x : NodeId) (depth cv : Nat) (n : KNode) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup x = some n) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hw : klongsWf n.ks = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hD : DelRoom c cv n) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' =>
      w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
      w'.next = w.next ∧ w'.madeFor = w.madeFor ∧
      ∃ n', w'.nodes = upsert w.nodes x n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
        (∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') ∧
        BitmapOf n n' c.i cv) := by
  have hR : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
      n.size + 1 < c.p.M ∧
      deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
    intro hn
    rcases hD with ⟨h1, h2, _⟩ | ⟨_, h3, h4⟩
    · exact absurd ⟨h1, h2⟩ hn
    · exact ⟨h3, h4⟩
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
      simpa using hne
    cases hgl : n.ks.getLast? with
    | none =>
      obtain ⟨hroom0, hdead2⟩ := hR (fun ⟨⟨old, h⟩, _⟩ => by rw [hgl] at h; cases h)
      have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom0
      simp only [hno, hroom', hroom0, hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure, hgl]
      exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
        KNode.add_times n c.i _ (fun s h => by cases h) hnt, fun c' => n.add_delete_live_lookup c.i cv c', Or.inl rfl⟩
    | some k =>
      cases k with
      | del old =>
        obtain ⟨pre, hpre⟩ := List.getLast?_eq_some_iff.mp hgl
        cases hlt : (n.lastTime == some c.i)
        · obtain ⟨hroom0, hdead2⟩ := hR (fun ⟨_, h⟩ => by rw [h] at hlt; simp at hlt)
          have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom0
          simp only [hno, hroom', hroom0, hdead2, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_false,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
            KNode.add_times n c.i _ (fun s h => by cases h) hnt,
            fun c' => n.add_delete_live_lookup c.i cv c', Or.inl rfl⟩
        · have hdead1 : deadOver c.p (n.setAt (n.size - 1)
              (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
            rcases hD with ⟨_, _, h⟩ | ⟨hn, _, _⟩
            · exact h
            · exact absurd ⟨⟨old, hgl⟩, by simpa using hlt⟩ hn
          simp only [hno, hdead1, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_true,
            Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
            writerWP_pure]
          exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.setAt_leaf _ _ _, KNode.setAt_delete_wf n cv old hw hgl,
            KNode.setAt_last_del_times n c.i old _ hgl hnt,
            fun c' => n.setAt_delete_live_lookup cv c' old hgl,
            Or.inr ⟨pre, old, hpre, by simpa using hlt, rfl⟩⟩
      | _ =>
        obtain ⟨hroom0, hdead2⟩ := hR (fun ⟨⟨old, h⟩, _⟩ => by rw [hgl] at h; cases h)
        have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom0
        simp only [hno, hroom', hroom0, hdead2, hgl, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, _, rfl, KNode.add_leaf _ _ _, KNode.add_delete_wf n c.i cv hw hne,
          KNode.add_times n c.i _ (fun s h => by cases h) hnt,
          fun c' => n.add_delete_live_lookup c.i cv c', Or.inl rfl⟩


/-- `writerWP_appendDeleteKlong_j2` with the room of the branch the writer takes
(`DelRoom`). -/
theorem writerWP_appendDeleteKlong_j2D (x : NodeId) (depth cv : Nat) (n : KNode) (c : Ctx)
    (base : View BVal) (B : NodeId) (w : W)
    (hlk : w.nodes.lookup x = some n) (htk : w.taken.contains x = false)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i) (hw : klongsWf n.ks = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hDR : DelRoom c cv n)
    (hpos : 0 < c.i) (hJ : TakeJ2 c base B w)
    (hxR : TReach (wNode c.p base w) c.i w.top.rootKey x)
    (hcvN : ∀ y, (cv, y) ∈ n.liveAt c.i → wNode c.p base w y = none)
    (hcvv : ∀ y, (cv, y) ∈ n.liveAt c.i → y < B ∨ y ∈ w.vals.map (·.1)) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' => TakeJ2 c base B w') := by
  refine writerWP_mono (writerWP_appendDeleteKlong_room_exactD x depth cv n c w hlk hnt hw hne hDR) ?_
  rintro _ w' ⟨ht, htop, hv, _, _, _, n', hnodes, _, _, ht', hlk', hbm⟩
  have hx : wNode c.p base w x = some n := by
    simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hlk]
  have hN' : wNode c.p base w' = updN (wNode c.p base w) x n' := by
    funext z
    by_cases hz : z = x
    · rw [hz, updN_self]
      simp only [wNode, ht, htk, Bool.false_eq_true, ↓reduceIte, hnodes, lookup_upsert]
    · simp only [updN, hz, ↓reduceIte, wNode, ht, hnodes, lookup_upsert]
  have hlive := liveAt_iff_of_delete_lookup n n' c.i cv hnt ht' hlk'
  have hreach := reach_updN_keep (wNode c.p base w) c.i w.top.rootKey x n n' hx (by
    intro cc u hm
    by_cases hc : cc = cv
    · rw [hc] at hm; exact Or.inr (hcvN u hm)
    · exact Or.inl ⟨cc, (hlive cc u).mpr ⟨hm, hc⟩⟩)
  unfold TakeJ2
  rw [htop, hv, hN']
  refine j2_change_one (wNode c.p base w) _ c.i w.top.rootKey w.top.rootKey B _ x n n' hJ hx
    (updN_self _ _ _) (fun z hz => by simp [updN, hz]) (bitmapOf_prefix n n' c.i cv hbm hpos)
    (bitmapOf_firstTime n n' c.i cv hbm)
    (deadLiveK_bitmap n n' c.i cv B _ hbm hnt (deadLiveK_of_N _ _ _ _ hJ.2.1 x n hx) hcvv hlive)
    hreach (fun _ => ?_)
  rcases hreach x hxR with h | h
  · exact h
  · rw [h] at hx; cases hx


/-! ## (8) A delete into a leaf that keeps a live klong and has room -/

/-- (8) with the take-back's (B) and (C): `writerWP_del_bitmap_segR`'s premises
with `TakeJ2` before, the leaf reached and its klong of cv naming no node, below B
or a value. -/
theorem writerWP_del_room_j2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk B : NodeId) (w : W) (hmerges : c.p.merges = false)
    (hpos : 0 < c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n)
    (hJ : TakeJ2 c base B w)
    (hLR : ∀ L, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      TReach (wNode c.p base w) c.i w.top.rootKey L)
    (hcvL : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none ∧ (y < B ∨ y ∈ w.vals.map (·.1))) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => TakeJ2 c base B w') := by
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
  intro L w3 ⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := hleaf L n hvisL hn hnl
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  have hJ3 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJ hr03
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  have hL3t : w3.taken.contains L = false := by rw [hr03.2.2.1]; exact hLt
  refine writerWP_mono (writerWP_appendDeleteKlong_j2D L _ cv n c base B w3 hlk3 hL3t htimes hwf hne
    hroomD hpos hJ3 (by rw [hr03.1, hr03.2.1]; exact hLR L hvisL)
    (fun y hy => by rw [hr03.1]; exact (hcvL L n hvisL hn hnl y hy).1)
    (fun y hy => by rw [hr03.2.2.2.1]; exact (hcvL L n hvisL hn hnl y hy).2)) ?_
  intro _ w4 hJ4
  unfold afterDelete
  wpSimplify
  simp only [hmerges, Bool.false_eq_true, ↓reduceIte]
  rw [writerWP_pure]
  simp only [Bool.not_false, ↓reduceIte]
  unfold fresh
  wpSimplify
  exact hJ4

end SIS.Tree
