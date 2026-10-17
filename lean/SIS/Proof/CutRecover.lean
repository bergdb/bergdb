/-
Proofs about reclaim, part 8 (bergdb item 001, WP R4): T8, startup from a
stream cut safely.
-/
import SIS.Proof.CutStart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The nodes that startup reads have their histories cut at s. -/
theorem baseStruct_times (sp : Spec V T) (S : Stream V T) (s : Nat) (x : NodeId) (n : Node V)
    (h : (baseStruct sp S s true).get? x = some n) : ∀ e ∈ n.hist, e.time ≤ s := by
  rw [baseStruct_eq, Struct.get?, lookup_filterMap_pair] at h
  split at h
  · obtain ⟨v, -, rfl⟩ := Option.map_eq_some_iff.mp h
    intro e he
    exact (mem_upTo.mp he).2
  · simp at h

/-- A cut at or before the startup pos keeps D: startup takes it from the
records after the startup pos. -/
theorem sectionD_cut {c : Nat} {S : Stream V T} (hcs : c ≤ lastSp S) :
    sectionD (cutStream c S) = sectionD S := by
  unfold sectionD
  rw [lastSp_cut]
  have hidx : sectionIdx (cutStream c S) (lastSp S) = sectionIdx S (lastSp S) := by
    simp [sectionIdx, cutStream_length]
  rw [hidx]
  apply flatMap_congr_mem
  intro j hj
  have : lastSp S + 1 ≤ j := by simp [sectionIdx] at hj; omega
  rw [cutStream_getElem?_ge (by omega)]

section Base

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The entries up to s of a version of a node of Ps (P after T(s)) are the
node's entries in Ps, so they point to nodes of Ps. -/
theorem Inv.version_ptrs (hinv : Inv sp db k) {Ps : Struct V} {s : Nat} (hg : Grow Ps s db.P)
    (hpt : PtrsOK sp Ps) (htimes : ∀ x n, Ps.get? x = some n → ∀ e ∈ n.hist, e.time ≤ s)
    {r : Nat} {y : NodeId} {w : Version V} (hw : db.S.versionAt r y = some w) (hy : (Ps.get? y).isSome) :
    ∀ e ∈ w.hist, e.time ≤ s → ∀ y' ∈ sp.ptrs e.val, (Ps.get? y').isSome := by
  intro e he hes y' hy'
  obtain ⟨-, -, m, hm, hmh, -, -⟩ := hinv.version_node hw
  obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hy
  obtain ⟨n', hn', -, -, hup⟩ := hg y ny hny
  rw [hm, Option.some.injEq] at hn'
  subst hn'
  have hen : e ∈ ny.hist := by
    rw [← upTo_of_forall ny.hist s (htimes y ny hny), ← hup]
    rw [hmh] at he
    exact mem_upTo.mpr ⟨(mem_upTo.mp he).1, hes⟩
  obtain ⟨m', hm', -⟩ := hpt y ny hny e hen y' hy'
  rw [hm']; rfl

/-- After a safe cut, startup's reads of the cut stream and of the whole stream
at a time from f to s give the same last version of every node but a virtual
root. -/
theorem Inv.readAt_cut_lookup (hinv : Inv sp db k) (hvl : VirtLiveOK sp) {c : Nat}
    (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) {t : Time} (hft : lastFa db.S ≤ t)
    (hts : t ≤ lastSp db.S) {x : NodeId} (hx : sp.virt = true → x ≠ root) :
    List.lookup x (readAt sp (cutStream c db.S) (lastSp db.S) true t).reverse =
      List.lookup x (readAt sp db.S (lastSp db.S) true t).reverse := by
  by_cases hv : sp.virt = true
  · obtain ⟨h1, h2⟩ := hinv.readAt_cut_v hv hvl hcut hfs hft hts
    generalize (readAt sp db.S (lastSp db.S) true t).tail = X at h1 h2
    rw [h1, h2, List.reverse_cons, List.reverse_cons, List.lookup_append, List.lookup_append]
    have hn : ∀ v : Version V, List.lookup x [(root, v)] = none := by
      intro v
      have : (x == root) = false := by simp [hx hv]
      simp [List.lookup_cons, this]
    rw [hn, hn]
  · rw [hinv.readAt_cut_nv (by simpa using hv) hcut hft hts]

/-- After a safe cut, startup's P up to s from the cut stream has the node of
the whole stream's for every node but a virtual root that is reachable at a
time from f to s. -/
theorem Inv.baseCut_get? (hinv : Inv sp db k) (hls : LiveSub sp) (hvl : VirtLiveOK sp) {c : Nat}
    (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) {x : NodeId}
    (hx : sp.virt = true → x ≠ root) {t' : Time} (h1 : lastFa db.S ≤ t') (h2 : t' ≤ lastSp db.S)
    (hr : reachable sp db.P t' x = true) :
    (baseStruct sp (cutStream c db.S) (lastSp db.S) true).get? x =
      (baseStruct sp db.S (lastSp db.S) true).get? x := by
  rw [baseStruct_eq, baseStruct_eq, Struct.get?, Struct.get?, lookup_filterMap_pair,
    lookup_filterMap_pair]
  have hin : x ∈ (readAt sp db.S (lastSp db.S) true t').map (·.1) := by
    rw [(hinv.readAt_spec hls h2).1]; simpa [reachable] using hr
  have hsome : (List.lookup x (readAt sp db.S (lastSp db.S) true t').reverse).isSome := by
    rw [List.lookup_isSome_iff]
    obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hin
    exact ⟨p, List.mem_reverse.mpr hp, by simp [hpx]⟩
  have hin' : x ∈ (readAt sp (cutStream c db.S) (lastSp db.S) true t').map (·.1) := by
    have h := hsome
    rw [← hinv.readAt_cut_lookup hvl hcut hfs h1 h2 hx, List.lookup_isSome_iff] at h
    obtain ⟨p, hp, hpx⟩ := h
    exact List.mem_map.mpr ⟨p, List.mem_reverse.mp hp, (beq_iff_eq.mp hpx).symm⟩
  have hmem : ∀ (S' : Stream V T), x ∈ (readAt sp S' (lastSp db.S) true t').map (·.1) →
      x ∈ (((List.range (lastSp db.S + 1)).flatMap
        (fun t => readAt sp S' (lastSp db.S) true t)).map (·.1)).eraseDups := by
    intro S' h
    rw [List.mem_eraseDups, List.map_flatMap]
    exact List.mem_flatMap.mpr ⟨t', List.mem_range.mpr (by omega), h⟩
  rw [ite_eq_left_iff.mpr (fun h => absurd (hmem _ hin') h),
    ite_eq_left_iff.mpr (fun h => absurd (hmem _ hin) h)]
  congr 1
  apply lookup_rev_flatMap_congr _ _ x (lastFa db.S) (lastSp db.S)
  · intro t ht1 ht2; exact hinv.readAt_cut_lookup hvl hcut hfs ht1 ht2 hx
  · exact ⟨t', h1, h2, hsome⟩

/-- With a virtual root: after a safe cut, startup's root from the cut stream is
the root it rebuilds from the root children read there, cut at s. -/
theorem Inv.baseCut_root (hinv : Inv sp db k) (hv : sp.virt = true) {c : Nat} (hcs : c ≤ lastSp db.S) :
    (baseStruct sp (cutStream c db.S) (lastSp db.S) true).get? root =
      some (cutNode (lastSp db.S)
        (rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true))) := by
  rw [baseStruct_eq, Struct.get?, lookup_filterMap_pair]
  have hread : ∀ t, readAt sp (cutStream c db.S) (lastSp db.S) true t =
      readFrom sp (cutStream c db.S) (lastSp db.S) true t
        (rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)) := by
    intro t; unfold readAt startVersion; simp only [hv, ↓reduceIte]
  have hp0 : (root, rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)) ∈
      (List.range (lastSp db.S + 1)).flatMap (fun t => readAt sp (cutStream c db.S) (lastSp db.S) true t) := by
    refine List.mem_flatMap.mpr ⟨0, List.mem_range.mpr (by omega), ?_⟩
    rw [hread, readFrom_eq]
    exact List.mem_cons_self
  have hmem : root ∈ (((List.range (lastSp db.S + 1)).flatMap
      (fun t => readAt sp (cutStream c db.S) (lastSp db.S) true t)).map (·.1)).eraseDups := by
    rw [List.mem_eraseDups]
    exact List.mem_map.mpr ⟨_, hp0, rfl⟩
  rw [ite_eq_left_iff.mpr (fun h => absurd hmem h)]
  cases hl : List.lookup root (((List.range (lastSp db.S + 1)).flatMap
      (fun t => readAt sp (cutStream c db.S) (lastSp db.S) true t))).reverse with
  | none =>
    exfalso
    rw [List.lookup_eq_none_iff] at hl
    have := hl _ (List.mem_reverse.mpr hp0)
    simp at this
  | some u =>
    obtain ⟨t, -, hmem', -⟩ := lookup_rev_flatMap_range _ _ root u hl
    rw [hread] at hmem'
    have := readFrom_root_pair sp (hinv.follow_cut_root hv hcs) _ _ (Nat.lt_succ_self _) _ hmem' rfl
    simp only [Prod.mk.injEq] at this
    rw [this.2]
    rfl

/-- After a safe cut, startup's P up to s from the cut stream has only nodes of
Ps, P after T(s). -/
theorem Inv.baseCut_ids (hinv : Inv sp db k) (hls : LiveSub sp) {Ps : Struct V}
    (hg : Grow Ps (lastSp db.S) db.P) (hpt : PtrsOK sp Ps)
    (htimes : ∀ x n, Ps.get? x = some n → ∀ e ∈ n.hist, e.time ≤ lastSp db.S)
    (hroot : (Ps.get? root).isSome) {c : Nat} (hcut : CutOK sp c db k) (hcs : c ≤ lastSp db.S)
    (x : NodeId) (hx : ((baseStruct sp (cutStream c db.S) (lastSp db.S) true).get? x).isSome) :
    (Ps.get? x).isSome := by
  rw [baseStruct_eq, Struct.get?, lookup_filterMap_pair] at hx
  split at hx
  · rename_i hmem
    rw [List.mem_eraseDups, List.map_flatMap] at hmem
    obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hmem
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hxt
    have hts : t ≤ lastSp db.S := by have := List.mem_range.mp ht; omega
    have hread := hinv.readFrom_cut_ids hls hg hpt htimes hcs hts
    unfold readAt startVersion at hp
    by_cases hv : sp.virt = true
    · simp only [hv, ↓reduceIte] at hp
      obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
      apply hread _ _ (Nat.lt_succ_self _) hroot _ p hp
      intro e he hes y hy
      rw [hinv.cutRoot_hist hv hcut hcs h0] at he
      have he1 := (mem_upTo.mp (List.mem_filter.mp he).1).1
      obtain ⟨n0s, hn0s⟩ := Option.isSome_iff_exists.mp hroot
      obtain ⟨n', hn', -, -, hup⟩ := hg root n0s hn0s
      rw [h0, Option.some.injEq] at hn'
      subst hn'
      have hen : e ∈ n0s.hist := by
        rw [← upTo_of_forall n0s.hist _ (htimes root n0s hn0s), ← hup]
        exact mem_upTo.mpr ⟨he1, hes⟩
      obtain ⟨m', hm', -⟩ := hpt root n0s hn0s e hen y hy
      rw [hm']; rfl
    · simp only [hv, Bool.false_eq_true, ↓reduceIte] at hp
      rw [topVersion_cut hcut hcs] at hp
      cases htv : topVersion db.S (lastSp db.S) true with
      | none => rw [htv] at hp; simp at hp
      | some v0 =>
        rw [htv] at hp
        simp only at hp
        -- top(k) names the root's latest version.
        have hv0 : ∃ r, db.S.versionAt r root = some v0 := by
          unfold topVersion at htv
          cases hR : db.S.getLast? with
          | none => rw [hR] at htv; simp at htv
          | some R =>
            rw [hR] at htv
            simp only [Option.bind_some] at htv
            rw [hinv.top R hR] at htv
            simp only [topOf, hv, Bool.false_eq_true, ↓reduceIte] at htv
            cases hu : db.S.lv root with
            | none => rw [hu] at htv; simp at htv
            | some u =>
              rw [hu] at htv
              simp only [Option.map_some] at htv
              obtain ⟨-, r, hr⟩ := follow_spec htv
              exact ⟨r, hr⟩
        obtain ⟨r, hr⟩ := hv0
        have hv0n : v0.node = root := (hinv.version_node hr).1
        apply hread _ _ (Nat.lt_succ_self _) (by rw [hv0n]; exact hroot)
          (hinv.version_ptrs hg hpt htimes hr hroot) p hp
  · simp at hx

end Base

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

/-- The first available time of the last record is at most its startup pos. -/
theorem st_fa_le {k : Nat} (hk : k ≤ ts.length) :
    lastFa (st sp al ts k).S ≤ lastSp (st sp al ts k).S := by
  cases k with
  | zero => rw [st_zero]; simp [init, lastFa, lastSp]
  | succ j =>
    rw [st_S_succ sp al ts (by omega)]
    simp only [lastFa, lastSp, List.getLast?_append, List.getLast?_singleton, Option.some_or,
      Option.map_some, Option.getD_some]
    rw [parts_R]
    simp only [parts_fa, firstAvail]
    exact Nat.min_le_left _ _

/-- After a safe cut, P up to the startup pos s, as startup reads it from the
cut stream, agrees with P after T(s) for lookups from f to s. -/
theorem base_cutAgree (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat} (hk : k ≤ ts.length)
    (hvl : VirtLiveOK sp) {c : Nat} (hcut : CutOK sp c (st sp al ts k) k) :
    CutAgree sp (lastFa (st sp al ts k).S) (lastSp (st sp al ts k).S)
      (st sp al ts (lastSp (st sp al ts k).S)).P
      (baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true) := by
  have hinv := inv_st sp al ts hok hst k hk
  have hls : LiveSub sp := hok.1.liveSub
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have hinvs := inv_st sp al ts hok hst _ (Nat.le_trans hsk hk)
  have hgrow := st_grow sp al ts hok hst hsk hk
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hreach : ∀ t ≤ lastSp (st sp al ts k).S, ∀ y,
      reachable sp (st sp al ts k).P t y = reachable sp (st sp al ts (lastSp (st sp al ts k).S)).P t y :=
    fun t ht y => reachable_grow hls hinvs.ptrs hinvs.rootIn hgrow ht y
  have hbase := base_sameNodes sp al ts hok hst hk
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  refine ⟨hinvs.rootIn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The root.
    by_cases hv : sp.virt = true
    · rw [hinv.baseCut_root hv hcs]; rfl
    · rw [hinv.baseCut_get? hls hvl hcut hfs (fun h => absurd h hv) (Nat.le_refl _) hfs
        (reachable_root h0 _), hbase root]
      exact hinvs.rootIn
  · -- A virtual root's live children.
    intro hv n n' hn hn'
    rw [hinv.baseCut_root hv hcs, Option.some.injEq] at hn'
    subst hn'
    obtain ⟨n1, hn1, hl1, -, hh1⟩ := hgrow root n hn
    rw [h0, Option.some.injEq] at hn1
    subst hn1
    refine ⟨?_, ?_⟩
    · show n.level = rootLevel sp
      rw [← hl1]; exact ((hinv.vr hv).rootIdx n0 h0).2
    · intro t' h1 h2
      have hn_hist : n.hist.upTo t' = n0.hist.upTo t' := by
        rw [← upTo_upTo n.hist h2, ← upTo_upTo n0.hist h2, hh1]
      show sp.live (n.hist.upTo t') = sp.live (History.upTo (History.upTo
        (rootVersion sp (lastSp (st sp al ts k).S)
          (topsRead sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true)).hist
        (lastSp (st sp al ts k).S)) t')
      rw [upTo_upTo _ h2, hn_hist, hinv.cutRoot_live hv hvl hcut hfs h0 h1 h2]
  · -- The nodes reachable from f on.
    intro x t' h1 h2 hx hr
    rw [← hreach t' h2 x] at hr
    rw [hinv.baseCut_get? hls hvl hcut hfs hx h1 h2 hr, hbase x]
  · -- No other nodes.
    exact hinv.baseCut_ids hls hgrow hinvs.ptrs hinvs.times hinvs.rootIn hcut hcs
  · -- Times.
    exact baseStruct_times sp _ _
  · -- A virtual root's entries.
    intro hv n hn e he
    rw [hinv.baseCut_root hv hcs, Option.some.injEq] at hn
    subst hn
    exact rootVersion_vals sp _ _ e (mem_upTo.mp he).1

/-- T8: after a safe cut, startup from the cut stream gives P at every time from
f to k, and D. -/
theorem recoverCut (hok : RunOK sp al ts) (hst : AlgOK sp al) {k : Nat} (hk : k ≤ ts.length)
    (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) {c : Nat} (hcut : CutOK sp c (st sp al ts k) k) :
    SameFrom sp (lastFa (st sp al ts k).S) k (startup sp (cutStream c (st sp al ts k).S)).P
        (st sp al ts k).P ∧
      (startup sp (cutStream c (st sp al ts k).S)).D = (st sp al ts k).D := by
  have hinv := inv_st sp al ts hok hst k hk
  have hls : LiveSub sp := hok.1.liveSub
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hagree := rerun_cutAgree sp al ts hok hst hk hex hvl hcs hfs
    (base_cutAgree sp al ts hok hst hk hvl hcut)
  refine ⟨?_, ?_⟩
  · have hP : (startup sp (cutStream c (st sp al ts k).S)).P =
        rerun sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S)
          (baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true) := by
      simp only [startup, startupWith, lastSp_cut]
    rw [hP]
    exact hagree.sameFrom hls hinv.ptrs
  · rw [startup, startup_D, hinv.inv1, sectionD_cut hcs]

end Run

end SIS
