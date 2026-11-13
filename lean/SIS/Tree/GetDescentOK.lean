import SIS.Tree.DelMergeCaseF
import SIS.Tree.MergePathCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The merges' descent inside a delete (bergdb 024-12, case (4); cost's
`DescentOKF` without `MergePathCond`, whose clauses are facts of the merge, not
of the state): `descendToHeight` reads only, keeps `DelInvF` and the books, and
leaves the key access path linked from the space root, every node of it cached
(`PathOK`). -/

/-- `DescentOKF` without `MergePathCond`: the descent keeps `DelInvF` and gives
the path down to the node it stops at. -/
def DescentOKF2 (c : Ctx) (base : View BVal) (f : Nat) : Prop :=
  ∀ (w0 : W) (k0 key : Key) (g h : Nat) (v : W), DelInvF c base w0 k0 f v →
    WriterWP (descendToHeight key g h) c v (fun d v' => DelInvF c base w0 k0 f v' ∧
      ∃ X K Nn, PathOK c v' d X K Nn)

theorem putBook_descendToHeight (key : Key) (g h : Nat) (c : Ctx) (base : View BVal) (B : NodeId)
    (top0 : Top) (hB : PutBase c base B) (w : W) (hw : PutBook c B top0 w) :
    WriterWP (descendToHeight key g h) c w (fun _ w' => PutBook c B top0 w') :=
  putBook_of_keeps _ c base B top0 hB w hw (klongsWf_descendToHeight key g h)
    (good_descendToHeight B key g h) (book_descendToHeight B key g h)
    (@state_descendToHeight (allocatedIdsInvariant B) key g h)
    (@state_descendToHeight (commitInvariant top0) key g h)
    (freshCache_descendToHeight key g h) (ptrs_descendToHeight _ key g h)

/-- The descent to height h: reads only, and every step it adds to the path is
linked from the node before it in the state the descent started from. -/
theorem writerWP_descendHeight_linked (cv h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w0 : W) (r : NodeId)
    (hRt : ∀ y, TReach (wNode c.p base w0) c.i r y → w0.taken.contains y = false) :
    ∀ (f : Nat) (x : NodeId) (w : W) (ps : List (Option Nat × NodeId)),
      ReadsAs c.p base w0 w → w.path = (none, r) :: ps →
      LinkedFrom (wNode c.p base w0) c.i r ps → pathEnd r ps = x →
      WriterWP (descendHeight cv h f x) c w (fun _ v => ReadsAs c.p base w0 v ∧
        ∃ ps', v.path = (none, r) :: ps' ∧ LinkedFrom (wNode c.p base w0) c.i r ps') := by
  intro f
  induction f with
  | zero => intro x w _ _ _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w ps hr0 hp hlf hend
    have hxR : TReach (wNode c.p base w0) c.i r x := by
      rw [← hend, ← nodeAt_last]
      exact (LinkedFrom.pathLen _ _ r ps hlf ps.length (Nat.le_refl _)).reach
    unfold descendHeight
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_ghOf_reads x c w base hvc)
      (writerWP_ghOf_frame x c w)) ?_
    rintro ⟨_, hx⟩ v ⟨hrv, ⟨htv, _, _, _, hpv, _, _⟩⟩
    split
    · simp only [writerWP_pure]
      exact ⟨ReadsAs.trans _ _ _ _ _ hr0 hrv, ps, by rw [hpv, hp], hlf⟩
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_and (writerWP_getNode_reads x c v base hvc)
        (writerWP_getNode_frame x c v)) ?_
      rintro n v1 ⟨⟨hr1, _, hwn⟩, ⟨_, _, _, _, hp1, _, _⟩⟩
      have hr01 := ReadsAs.trans _ _ _ _ _ (ReadsAs.trans _ _ _ _ _ hr0 hrv) hr1
      have hxn : wNode c.p base w0 x = some n := by
        have htx : v.taken.contains x = false := by
          rw [htv, hr0.2.2.1]; exact hRt x hxR
        rw [← (ReadsAs.trans _ _ _ _ _ hr0 hrv).1]
        exact hwn htx
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd hfd
          simp only [pathAdd, writerWP_bind, writerWP_modify]
          refine ih fd.y _ (ps ++ [(some fd.c, fd.y)]) ?_ ?_ ?_ ?_
          · exact ReadsAs.trans _ _ _ _ _ hr01 ⟨by funext y; rfl, rfl, rfl, rfl, rfl⟩
          · show v1.path ++ [(some fd.c, fd.y)] = _
            rw [hp1, hpv, hp]; rfl
          · refine LinkedFrom.append _ _ r ps _ hlf ?_
            rw [hend]
            exact LinkedFrom.cons x n fd.c fd.y [] hxn (KNode.searchLte_mem n c.i _ fd hfd)
              (LinkedFrom.nil _)
          · have := pathEnd_cons_append r fd.y (some fd.c) ps []
            simp [pathEnd] at this ⊢

/-- `descendToHeight`: reads only, and its path is the space root and steps
linked from it in the state before. -/
theorem writerWP_descendToHeight_linked (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hwf : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      klongsWf yn.ks = true) :
    WriterWP (descendToHeight key g h) c w (fun d v => ReadsAs c.p base w v ∧
      ∃ ps, v.path = (none, w.top.rootKey) :: ps ∧
        LinkedFrom (wNode c.p base w) c.i w.top.rootKey ps ∧ d = ps.length) := by
  unfold descendToHeight
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_descendToSegmentRoot_linked key g c base hvc w hRt hwf) ?_
  rintro root v1 ⟨hr1, _, _, ps, hp1, hlf, hend, _, _⟩
  split
  · exact writerWP_throw _ _ _ _
  · rename_i cv _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_descendHeight_linked cv h c base hvc w w.top.rootKey hRt c.p.fuel
      root v1 ps hr1 hp1 hlf hend) ?_
    rintro _ v2 ⟨hr2, ps', hp2, hlf2⟩
    unfold pathSize
    simp only [writerWP_bind, writerWP_get, writerWP_pure]
    exact ⟨hr2, ps', hp2, hlf2, by rw [hp2]; simp⟩

/-- The path of a descent, every node of it cached, in the form of `PathOK`. -/
theorem pathOK_of_linked (c : Ctx) (base : View BVal) (w0 v : W) (ps : List (Option Nat × NodeId))
    (hr : ReadsAs c.p base w0 v) (hp : v.path = (none, w0.top.rootKey) :: ps)
    (hlf : LinkedFrom (wNode c.p base w0) c.i w0.top.rootKey ps) (hc : PathCached v)
    (hRt : ∀ y, TReach (wNode c.p base w0) c.i w0.top.rootKey y → w0.taken.contains y = false) :
    PathOK c v ps.length (fun i => nodeAt w0.top.rootKey ps i)
      (fun i => ((ps[i - 1]?).bind (·.1)).getD 0)
      (fun i => (wNode c.p base w0 (nodeAt w0.top.rootKey ps i)).getD ⟨true, []⟩) := by
  have hgetP := LinkedFrom.get _ _ _ ps hlf
  have hPL := LinkedFrom.pathLen _ _ _ ps hlf
  have hpX : ∀ i, i ≤ ps.length →
      (v.path[i]?).map (·.2) = some (nodeAt w0.top.rootKey ps i) := by
    intro i hi
    have hl : i < (w0.top.rootKey :: ps.map (·.2)).length := by simp; omega
    rw [hp, ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  refine ⟨hpX, ?_, ?_, ?_, ?_⟩
  · intro i h1 h2
    obtain ⟨k, n', e1, _, _⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp, List.getElem?_cons_succ]
    simp only [Nat.add_sub_cancel] at e1 ⊢
    rw [e1]
    rfl
  · intro i hi
    have hR := (hPL i hi).reach
    have htk : v.taken.contains (nodeAt w0.top.rootKey ps i) = false := by
      rw [hr.2.2.1]; exact hRt _ hR
    have hmem : ∃ e ∈ v.path, e.2 = nodeAt w0.top.rootKey ps i := by
      have h := hpX i hi
      cases he : v.path[i]? with
      | none => rw [he] at h; cases h
      | some e =>
        rw [he] at h
        simp only [Option.map_some, Option.some.injEq] at h
        exact ⟨e, List.mem_of_getElem? he, h⟩
    obtain ⟨e, he, hee⟩ := hmem
    obtain ⟨m, hm⟩ := hc e he
    rw [hee] at hm
    refine ⟨?_, htk⟩
    have hwv : wNode c.p base v (nodeAt w0.top.rootKey ps i) = some m := by
      simp only [wNode, htk, Bool.false_eq_true, ↓reduceIte, hm]
    rw [hr.1] at hwv
    simp only [hwv, Option.getD_some]
    exact hm
  · intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    simp only [e1, e2, Option.bind_some, Option.getD_some]
    exact e3
  · simp only [nodeAt_zero]
    exact hr.2.1 ▸ rfl

/-- The merges' descent keeps `DelInvF` and gives the path down to the node it
stops at (cost's `DescentOKF` without `MergePathCond`). -/
theorem descentOKF2 (c : Ctx) (base : View BVal) (f : Nat) : DescentOKF2 c base f := by
  intro w0 k0 key g h v hD
  obtain ⟨hI, _, _, _, _, _, B, top0, hB, hbk⟩ := id hD
  have hvc := hB.coherent
  have hRt : ∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false :=
    fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hwf : ∀ y yn, TReach (wNode c.p base v) c.i v.top.rootKey y → wNode c.p base v y = some yn →
      klongsWf yn.ks = true := fun y yn _ hn => hI.wf y yn hn
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendToHeight_linked key g h c base hvc v hRt hwf)
    (writerWP_descendToHeight_path_cached key g h c v))
    (putBook_descendToHeight key g h c base B top0 hB v hbk)) ?_
  rintro d v' ⟨⟨⟨hr, ps, hp, hlf, hd⟩, hc⟩, hbk'⟩
  subst hd
  exact ⟨delInvF_of_readsAs c base w0 k0 f v v' hD hr ⟨B, top0, hB, hbk'⟩, _, _, _,
    pathOK_of_linked c base v v' ps hr hp hlf hc hRt⟩

end SIS.Tree
