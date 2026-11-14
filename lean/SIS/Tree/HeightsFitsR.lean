/-
The fuel after a delete's bitmap into a full leaf from the heights (bergdb
024-22, step 4; once a premise of putinv's, DelStepsFullGet.lean):
`DelFullFitsOKR`, proved (`delFullFitsOKR_of`).

The heights' state at the descent's end (`HtJ`: the books, the walk's state,
the path not taken back, the klongs' form, and every cached height of a node
not taken back below the fuel) comes with putinv's descent walk
(`writerWP_del_toLeafMK`'s invariant J) through three steps: `htJ_descendLte`,
`htJ_pathAdd` (the segment leaf's klong that `searchEq` finds) and
`htJ_start`; with the kinds' books, `kdhtJ_*`. At a reachable delete's start
the facts `htJ_start` asks come from the run (`htStart_reachedU`): the bound
below the fuel is the boundary fit's (the doomed transaction, with
`TakeBelowFuelDelOK`).

Then the bitmap's cascade is the delete's first write that adds heights: a
node it makes is at most one above the path's nodes, which are below the fuel
(`sbS_appendDeleteKlong` with S the nodes not taken back), so every node not
taken back stays at most at the fuel, and `SegFits` at the fuel follows
(`segFits_of_heightsU`).
-/
import SIS.Tree.HeightsUnder
import SIS.Tree.HeightsFuelPut
import SIS.Tree.DelStepsFullGet

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The heights' state in a delete's descent. -/
structure HtJ (c : Ctx) (H : NodeId → Nat → Prop) (B : NodeId) (v : W) : Prop where
  book : Book B c v
  inv : HtInv H B c v
  free : PathFreeTo v v.path.length
  wf : WriterKlongsWf v
  bound : UntakenBound (c.p.fuel - 1) v

section Walk

variable {H : NodeId → Nat → Prop} {B : NodeId} {c : Ctx}

theorem fuel_sub_one_ge_H (p : Params) : p.H ≤ p.fuel - 1 := by
  have := fuel_gt_H p; omega

/-- The descent keeps `HtJ`. -/
theorem htJ_descendLte (hvo : ViewHtOK H B c) (hkw : ViewKlongsWf c.p c.view)
    (s f : Nat) (x : NodeId) (v : W) (hJ : HtJ c H B v) (hx : KdPathLast v x) :
    WriterWP (descendLte s f x) c v (fun _ v' => HtJ c H B v') := by
  refine writerWP_mono (writerWP_and (writerWP_and
    (ht_descendLte B s f x c v hvo hJ.book hJ.inv hJ.free (Or.inl hx))
    (klongsWf_descendLte s f x c v hkw hJ.wf))
    (shbS_descendLte (c.p.fuel - 1) s (fun y => v.taken.contains y = false) f x c v
      (fuel_sub_one_ge_H c.p) (fun y g h hm hy => hJ.bound y g h hm hy))) ?_
  rintro _ v' ⟨⟨⟨hb', hi', hle', -, -, hpf'⟩, hwf'⟩, hs'⟩
  exact ⟨hb', hi', hpf', hwf', fun y g h hm hy => hs' y g h hm (by rw [← hle'.2]; exact hy)⟩

/-- The path's step from a segment leaf to the next segment's root, the klong
`searchEq` finds. -/
theorem htJ_pathAdd (hvo : ViewHtOK H B c) (s : Nat) (fd : Found) (L : NodeId) (n : KNode)
    (v : W) (hJ : HtJ c H B v) (hL : KdPathLast v L) (hlk : v.nodes.lookup L = some n)
    (hleaf : n.leaf = true) (hfd : n.searchEq c.i s = some fd) :
    HtJ c H B { v with path := v.path ++ [(some fd.c, fd.y)] } := by
  obtain ⟨a, ha⟩ := hL
  obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hJ.book hlk
  have h0 : h = 0 := kd_h0 hJ.book hlk hm hleaf
  subst h0
  have hLf : v.taken.contains L = false :=
    hJ.free _ a L (by have := (List.getElem?_eq_some_iff.mp ha).1; omega) ha
  have hN := ht_cache_at hlk hJ.inv hm hLf (HtLe.refl _)
  have hlive := ht_searchEq_live (writerKlongsWf_lookup v hJ.wf L n hlk) hN.3 hfd
  have hpa := ht_pathAdd B fd.c fd.y c v hvo hJ.book hJ.inv a L n (ht_getLast_of ha) hlk s hlive hLf
  simp only [pathAdd, writerWP_modify] at hpa
  obtain ⟨hb', hi', -, -, -, hyf⟩ := hpa
  exact ⟨hb', hi', PathFreeTo.append hJ.free _ rfl rfl hyf, hJ.wf, hJ.bound⟩

/-- The descent's first state: the path cleared and the space root. -/
theorem htJ_start (hvo : ViewHtOK H B c) (w : W) (hb : Book B c w) (hi : HtInv H B c w)
    (hwf : WriterKlongsWf w) (hub : UntakenBound (c.p.fuel - 1) w) :
    HtJ c H B ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) := by
  have h1 := ht_pathClear B c w hvo hb hi
  simp only [pathClear, writerWP_modify] at h1
  have h2 := ht_findRoot B c { w with path := [] } hvo h1.1 h1.2.1 rfl
  simp only [findRoot, pathAdd, writerWP_bind, writerWP_get, writerWP_modify, writerWP_pure] at h2
  obtain ⟨hb2, hi2, -, -, -, hpf2⟩ := h2
  exact ⟨hb2, hi2, hpf2, hwf, hub⟩

/-- The kinds' books and the heights' state in the descent: putinv's `KdJ` and
`HtJ`. -/
def KdHtJ (c : Ctx) (B : NodeId) (top0 : Top) (KO : KindOracle) (BK : NodeId)
    (H : NodeId → Nat → Prop) (v : W) : Prop :=
  KdJ c B top0 KO BK v ∧ HtJ c H BK v

theorem kdhtJ_descendLte (base : View BVal) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view)
    (s f : Nat) (x : NodeId) (v : W) (hJ : KdHtJ c B top0 KO BK H v) (hx : KdPathLast v x) :
    WriterWP (descendLte s f x) c v (fun _ v' => KdHtJ c B top0 KO BK H v') :=
  writerWP_and (kdJ_descendLte c base B top0 hB KO BK hv hk s f x v hJ.1 hx)
    (htJ_descendLte hvo hkw s f x v hJ.2 hx)

theorem kdhtJ_pathAdd (base : View BVal) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hvo : ViewHtOK H BK c)
    (s : Nat) (fd : Found) (L : NodeId) (n : KNode) (v : W) (hJ : KdHtJ c B top0 KO BK H v)
    (hL : KdPathLast v L) (hlk : v.nodes.lookup L = some n) (hleaf : n.leaf = true)
    (hfd : n.searchEq c.i s = some fd) :
    KdHtJ c B top0 KO BK H { v with path := v.path ++ [(some fd.c, fd.y)] } :=
  ⟨kdJ_pathAdd c base B top0 hB KO BK hv fd.c fd.y L n v hJ.1 hL hlk (kd_searchEq_mem n c.i s fd hfd),
    htJ_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩

theorem kdhtJ_start (base : View BVal) (top0 : Top) (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hv : ViewIdsBelow BK c.view) (hvo : ViewHtOK H BK c)
    (w : W) (hJ : KdJ c B top0 KO BK w) (hi : HtInv H BK c w) (hwf : WriterKlongsWf w)
    (hub : UntakenBound (c.p.fuel - 1) w) :
    KdHtJ c B top0 KO BK H ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) :=
  ⟨kdJ_start c base B top0 hB KO BK hv w hJ, htJ_start hvo w hJ.2.1 hi hwf hub⟩

end Walk

/-! ## The fuel after the bitmap into a full leaf -/

/-- After a delete's bitmap into a full leaf at the end of the key access path,
the state fits the writer's fuel (one level more than before at most), with the
heights' state at the descent's end (`HtJ`), the path ending at depth d. -/
def DelFullFitsOKR (c : Ctx) (base : View BVal) (H : NodeId → Nat → Prop) (B : NodeId) : Prop :=
  ∀ (w : W), PutInv c base w → SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey →
    ∀ (d : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode), PathOK c w d X K Nn →
    ∀ (cv : Nat), (Nn d).leaf = true → bitsUnion (Nn d).lastBitmap ((Nn d).bitsOf cv) ≠ (Nn d).lastBitmap →
      ¬ DelRoom c cv (Nn d) → HtJ c H B w → w.path.length = d + 1 →
      WriterWP (appendDeleteKlong (X d) d cv) c w
        (fun _ v => SegFits (wNode c.p base v) c.i c.p.fuel v.top.rootKey)

set_option maxHeartbeats 1600000 in
/-- `DelFullFitsOKR` from the heights: the bitmap's cascade adds at most one to
the heights of the nodes not taken back, which were below the fuel. -/
theorem delFullFitsOKR_of (c : Ctx) (base : View BVal) (H : NodeId → Nat → Prop) (B : NodeId)
    (hvo : ViewHtOK H B c) (hbase : BaseHeights c H base) (hHb : ∀ y h, H y h → h ≤ c.p.H)
    (hpos : 0 < c.i) : DelFullFitsOKR c base H B := by
  intro w _ _ d X K Nn hP cv _ _ _ hJ hlen
  obtain ⟨hpX, -, hlk, -, -⟩ := hP
  obtain ⟨hxl, hxf⟩ := hlk d (Nat.le_refl _)
  obtain ⟨a, hpx⟩ : ∃ a, w.path[d]? = some (a, X d) := by
    have := hpX d (Nat.le_refl _)
    cases he : w.path[d]? with
    | none => rw [he] at this; cases this
    | some e =>
      rw [he] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact ⟨e.1, by rw [← this]⟩
  obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hJ.book hxl
  have hfuel : c.p.H + 2 < c.p.fuel := fuel_gt_H c.p
  -- the path's nodes are cached, not taken back, so below the fuel
  have hpg := ht_pathGh_all hJ.book hJ.inv (x := X d) ⟨a, by rw [hlen]; exact hpx⟩ hxl
  have hpb : PathBelowSB c.p.fuel w := by
    intro d' a' q hq
    obtain ⟨⟨q', g', h'⟩, hm', he⟩ := List.mem_map.mp (hpg d' a' q hq)
    simp only at he
    subst he
    refine ⟨hJ.book.bound _ hm', fun g2 h2 hm2 => ?_⟩
    have hqf := hJ.free d' a' q' (List.getElem?_eq_some_iff.mp hq).1 hq
    have := hJ.bound q' g2 h2 hm2 hqf
    omega
  have hS0 : SBInvS c.p c.p.fuel (fun y => w.taken.contains y = false) w w :=
    ⟨fun y g' h' hm' hy => Nat.le_trans (hJ.bound y g' h' hm' hy) (Nat.sub_le _ _), Nat.le_refl _,
      rfl, fun _ _ _ hm' _ => Or.inl hm'⟩
  refine writerWP_mono (writerWP_and
    (ht_appendDeleteKlong B (X d) d cv c w hvo hpos hJ.book hJ.inv g h hm a hpx
      (hJ.free.mono (by omega)))
    (sbS_appendDeleteKlong c.p.fuel (X d) d cv c w w (by omega) hS0 hpb a hpx)) ?_
  rintro _ v ⟨⟨hbv, hiv, hlev, -⟩, hsv⟩
  refine segFits_of_heightsU hbv hiv.cache hvo.heights base hbase c.p.fuel _ ?_
  intro y n hn k hk
  rcases hk with ⟨g', hm'⟩ | hk
  · have hyv := (ht_wNode_cases hn).1
    exact hsv.1 y g' k hm' (by rw [← hlev.2]; exact hyv)
  · have := hHb y k hk; omega

/-- `DelFullFitsOKR` at a run's context, for the transaction after it. -/
theorem delFullFitsOKR_run (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hR : RunLinksOK p (treeRun p ts) ts.length) (hK : KindsAllOK p (treeRun p ts))
    (hA : HeightAllOK p (treeRun p ts) ts.length) :
    DelFullFitsOKR (ctxOf p ts) (viewOf (treeRun p ts)) (htOracleOf p (treeRun p ts)) tx.base := by
  have htimes : StructTimesLE (treeRun p ts) ts.length := treeRun_timesLE p ts
  refine delFullFitsOKR_of _ _ _ _ (viewHtOK_of_run p ts tx hw hR hK hA)
    (baseHeights_of p (treeRun p ts) ts.length (ctxOf p ts) rfl (by simp [ctxOf]) htimes hR.1 hK hA)
    ?_ (by simp [ctxOf])
  rintro y h ⟨ny, _, _, _, hny⟩
  exact hny ▸ heightOf_le p ny.level

end SIS.Tree
