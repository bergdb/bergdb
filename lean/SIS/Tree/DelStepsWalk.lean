/-
The walk of a key's segments with an invariant J that every read on it keeps
(bergdb 024-12, case (4)'s delete steps): `writerWP_putSegs_prefix` with J at
the last segment (`writerWP_putSegs_prefixJ`), and the books (`PutBook`) as
such a J (`putBook_descendLte`, `putBook_pathAdd`).
-/
import SIS.Tree.DelStepsMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_putSegs_prefixJ (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (cv : Nat) (post : Bool → W → Prop) (J : W → Prop)
    (hJd : ∀ (s f : Nat) (x : NodeId) (v : W), J v → WriterWP (descendLte s f x) c v (fun _ v' => J v'))
    (hJp : ∀ (s : Option Nat) (x : NodeId) (v : W), J v → J { v with path := v.path ++ [(s, x)] }) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W), J w →
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      (∀ w', ReadsAs c.p base w w' → J w' → WriterWP (setValue rk cv key value) c w' post) →
      WriterWP (putSegs key value (pre ++ [cv]) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w hJ _ hrk hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append, putSegs.eq_2]
    exact hcont w (ReadsAs.refl _ _ _) hJ
  | cons s rest ih =>
    intro r rk w hJ ht hrk hcont
    have hne : rest ++ [cv] ≠ [] := by simp
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ [cv]) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · rename_i hysome
        obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
          cases h' : rest ++ [cv] with
          | nil => exact absurd h' hne
          | cons d rest' => exact ⟨d, rest', rfl⟩
        have hvis : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (s :: d :: rest') r,
            w.taken.contains q.1 = false := by
          intro q hq; apply ht q; rw [List.cons_append, he]; exact hq
        simp only [fromVisits] at hvis
        have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
            w.taken.contains q.1 = false := fun q hq => hvis q (List.mem_append_left _ hq)
        unfold setNode
        wpSimplify
        refine writerWP_mono (writerWP_and (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
          (hJd s c.p.fuel r w hJ)) ?_
        intro L w3 ⟨⟨hr3, n, hn, hnl, hlk3, _, hget⟩, hJ3⟩
        rw [writerWP_getNode_known L n c _ hlk3]
        rw [hg] at hget
        cases hfd : n.searchEq c.i s with
        | none => rw [hfd] at hget; cases hget
        | some fd =>
          rw [hfd] at hget
          simp only [Option.map_some, Option.some.injEq] at hget
          simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
          rw [← hget]
          generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, y)] } : W) = w4
          have hr04 : ReadsAs c.p base w w4 := by
            subst hw4
            exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
          apply ih y rk w4 (by rw [← hw4]; exact hJp _ _ w3 hJ3)
          · intro q hq
            rw [hr04.2.2.1]
            rw [hr04.1] at hq
            apply hvis q
            apply List.mem_append_right
            rw [hg]
            simp only
            rw [← he]
            exact hq
          · rw [hr04.1]; exact hrk
          · intro w' hr' hJ'
            exact hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') hJ'
      · cases hrk

theorem putBook_descendLte (s f : Nat) (x : NodeId) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (descendLte s f x) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_descendLte s f x) (good_descendLte B s f x)
    (book_descendLte B s f x) (@state_descendLte (allocatedIdsInvariant B) s f x)
    (@state_descendLte (commitInvariant top0) s f x) (freshCache_descendLte s f x)
    (ptrs_descendLte _ s f x)

theorem putBook_pathAdd (s : Option Nat) (x : NodeId) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    PutBook c B top0 { w with path := w.path ++ [(s, x)] } := by
  have h := putBook_of_keeps (pathAdd s x) c base B top0 hB w hw (klongsWf_pathAdd s x) (good_pathAdd B s x)
    (book_pathAdd B s x) (@state_pathAdd (allocatedIdsInvariant B) s x)
    (@state_pathAdd (commitInvariant top0) s x) (freshCache_pathAdd s x) (ptrs_pathAdd _ s x)
  simp only [pathAdd, writerWP_modify] at h
  exact h

theorem putBook_pathClear (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    PutBook c B top0 { w with path := [] } := by
  have h := putBook_of_keeps pathClear c base B top0 hB w hw klongsWf_pathClear (good_pathClear B)
    (book_pathClear B) (@state_pathClear (allocatedIdsInvariant B))
    (@state_pathClear (commitInvariant top0)) freshCache_pathClear (ptrs_pathClear _)
  simp only [pathClear, writerWP_modify] at h
  exact h

theorem putBook_appendDeleteKlong (x : NodeId) (depth cv : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_appendDeleteKlong x depth cv)
    (good_appendDeleteKlong B x depth cv) (book_appendDeleteKlong B x depth cv)
    (@state_appendDeleteKlong (allocatedIdsInvariant B) x depth cv)
    (@state_appendDeleteKlong (commitInvariant top0) x depth cv) (freshCache_appendDeleteKlong x depth cv)
    (ptrs_appendDeleteKlong _ x depth cv)

/-- The delete of a key whose leaf keeps a live klong and has room for the
bitmap, the merges on, up to `afterDelete`: the continuation is given the leaf
L and its node n, the state w3 before the bitmap (read as w), the state v after
it with L's new node n' (`writerWP_appendDeleteKlong_room_exactD`) and the books
at v. After `afterDelete` comes `fresh`, which Post must survive. -/
theorem writerWP_del_roomM (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hleaf : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false ∧ DelRoom c cv n)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hcont : ∀ (L : NodeId) (n : KNode) (w3 v : W) (g h : Nat),
      (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w L = some n →
      n.leaf = true → ReadsAs c.p base w w3 → w3.nodes.lookup L = some n →
      w.taken.contains L = false →
      v.taken = w3.taken → v.top = w3.top → v.vals = w3.vals → v.path = w3.path →
      v.next = w3.next → v.madeFor = w3.madeFor →
      (∃ n', v.nodes = upsert w3.nodes L n' ∧ n'.leaf = n.leaf ∧ klongsWf n'.ks = true ∧
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) ∧
        (∀ c', n'.live.lookup c' = if c' == cv then none else n.live.lookup c') ∧
        BitmapOf n n' c.i cv) →
      PutBook c B top0 v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => Post v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hb2 : PutBook c B top0 w2 := by
    rw [← hw2]
    exact putBook_pathAdd none w.top.rootKey c base B top0 hB _ (putBook_pathClear c base B top0 hB w hbook)
  refine writerWP_putSegs_prefixJ c base hvc (pre ++ [cv]) none cv _ (PutBook c B top0)
    (fun s f x v hv => putBook_descendLte s f x c base B top0 hB v hv)
    (fun s x v hv => putBook_pathAdd s x c base B top0 hB v hv) pre w.top.rootKey rk w2 hb2
    (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk) ?_
  intro w2' hr2' hb2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (putBook_descendLte cv c.p.fuel rk c base B top0 hB w2' hb2')) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, hb3⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := hleaf L n hvisL hn hnl
  have hLt : w.taken.contains L = false :=
    ht (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hvisL)
  unfold pathSize deleteUpward
  wpSimplify
  rw [writerWP_getNode_known L n c _ hlk3]
  have hnb : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached L n c _ hlk3 _ (fun gh => ?_)
  refine writerWP_mono (writerWP_and (writerWP_appendDeleteKlong_room_exactD L _ cv n c _ hlk3 htimes hwf
    hne hroomD) (putBook_appendDeleteKlong L _ cv c base B top0 hB _ hb3)) ?_
  rintro _ v ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hbv⟩
  refine writerWP_mono (hcont L n w3 v gh.1 gh.2 hvisL hn hnl hr03 hlk3 hLt h1 h2 h3 h4 h5 h6 h7 hbv) ?_
  intro _ v' hv'
  simp only [Bool.not_false, ↓reduceIte]
  simp only [writerWP_bind]
  exact writerWP_mono (hfresh v' hv') (fun _ _ h => by simp only [writerWP_pure]; exact h)

end SIS.Tree
