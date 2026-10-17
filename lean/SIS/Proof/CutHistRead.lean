/-
Proofs about reclaim, part 11 (bergdb item 001, WP R5): after a safe cut,
startup from the cut stream reads the nodes of D that no lookup from f on
reaches (M33, M34). Such a node was reachable at a time t before f, and its
ancestors then, it included, are in D with versions in the startup section
(`DAnchor`). With Rule R startup reads it at t through them, at its newest
version, as it does from the whole stream. With a virtual root, the root
child at t is read from the cut stream: the root children after it are in D
(`TopsD`), so their latest versions are at the cut or later (`CutOK`'s part
3).
-/
import SIS.Proof.CutHist

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- Every pair that a read gives is a version with its node: the first
version, or one that a pointer to the node is followed to. -/
theorem readFrom_pairs (sp : Spec V T) {S : Stream V T} {s : Nat} {t : Time}
    (hnode : ∀ y ref w, follow S s true y ref = some w → w.node = y) :
    ∀ (b : Nat) (v : Version V), v.level < b → ∀ p ∈ readFrom sp S s true t v,
      p.1 = p.2.node ∧ (p.2 = v ∨ ∃ ref, follow S s true p.1 ref = some p.2) := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb p hp
    rw [readFrom_eq] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨rfl, Or.inl rfl⟩
    · obtain ⟨y, -, hp⟩ := List.mem_flatMap.mp hp
      cases hw : follow S s true y (v.ref? y) with
      | none => rw [hw] at hp; simp at hp
      | some w =>
        rw [hw] at hp
        simp only at hp
        split at hp
        · rename_i hlt
          obtain ⟨h1, h2⟩ := ih w (by omega) p hp
          refine ⟨h1, Or.inr ?_⟩
          rcases h2 with h2 | h2
          · rw [h1, h2, hnode y _ w hw]; exact ⟨_, hw⟩
          · exact h2
        · simp at hp

/-- The version that startup starts from: the root's, or one that a pointer
is followed to. -/
theorem startVersion_cases (sp : Spec V T) (S : Stream V T) (s : Nat) {v : Version V}
    (h : startVersion sp S s true = some v) :
    v.node = root ∨ ∃ y ref, follow S s true y ref = some v := by
  unfold startVersion at h
  split at h
  · left; rw [← Option.some.inj h]; rfl
  · right
    unfold topVersion at h
    cases hT : S.getLast?.bind (·.top) with
    | none => rw [hT] at h; cases h
    | some p =>
      rw [hT] at h
      obtain ⟨z, r⟩ := p
      exact ⟨z, some r, h⟩

/-- The lookup of x in a list where x has pairs, all with u: u. -/
theorem lookup_of_all {β : Type} {x : NodeId} {u : β} :
    ∀ {l : List (NodeId × β)}, (∃ b, (x, b) ∈ l) → (∀ b, (x, b) ∈ l → b = u) →
      List.lookup x l = some u
  | [], hin, _ => by obtain ⟨b, hb⟩ := hin; simp at hb
  | (a, b0) :: l, hin, hall => by
    by_cases hax : x = a
    · subst hax
      simp only [List.lookup, beq_self_eq_true]
      rw [hall b0 List.mem_cons_self]
    · have hne : (x == a) = false := by simp [hax]
      simp only [List.lookup, hne]
      apply lookup_of_all
      · obtain ⟨b, hb⟩ := hin
        rcases List.mem_cons.mp hb with h | h
        · simp only [Prod.mk.injEq] at h; exact absurd h.1 hax
        · exact ⟨b, h⟩
      · intro b hb; exact hall b (List.mem_cons_of_mem _ hb)

/-- Startup's P up to s has the node of version u for x when a read of x up to
s gives u, and every one does. -/
theorem baseStruct_get?_of (sp : Spec V T) (S : Stream V T) (s : Nat) (x : NodeId)
    (u : Version V) (hin : ∃ t ≤ s, ∃ w, (x, w) ∈ readAt sp S s true t)
    (hall : ∀ t ≤ s, ∀ w, (x, w) ∈ readAt sp S s true t → w = u) :
    (baseStruct sp S s true).get? x = some (cutNode s u) := by
  rw [baseStruct_eq, Struct.get?, lookup_filterMap_pair]
  obtain ⟨t0, ht0, w0, hw0⟩ := hin
  have hmem : (x, w0) ∈ (List.range (s + 1)).flatMap (fun t => readAt sp S s true t) :=
    List.mem_flatMap.mpr ⟨t0, List.mem_range.mpr (by omega), hw0⟩
  have hx : x ∈ (((List.range (s + 1)).flatMap (fun t => readAt sp S s true t)).map (·.1)).eraseDups := by
    rw [List.mem_eraseDups]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
  simp only [hx, ↓reduceIte]
  rw [lookup_of_all ⟨w0, List.mem_reverse.mpr hmem⟩ (fun b hb => by
    obtain ⟨t, ht, hb⟩ := List.mem_flatMap.mp (List.mem_reverse.mp hb)
    exact hall t (by have := List.mem_range.mp ht; omega) b hb)]
  rfl

section Hist

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- Reading at time t from a version of a node p reachable then, with p's
entries up to t: x below p is read when x's ancestors then have their newest
versions in the section, with their entries up to t (Rule R). -/
theorem Inv.readFrom_anc (hinv : Inv sp db k) (hls : LiveSub sp) {S : Stream V T} {s : Nat}
    {t : Time} (x : NodeId)
    (hnew : ∀ q nq, Anc sp db.P t x q → db.P.get? q = some nq →
      ∃ w, newest S s q = some w ∧ w.node = q ∧ w.level = nq.level ∧
        w.hist.upTo t = nq.hist.upTo t) :
    ∀ (b : Nat) (p : NodeId) (np : Node V) (v : Version V), np.level < b → db.P.get? p = some np →
      reachable sp db.P t p = true → v.node = p → v.level = np.level →
      v.hist.upTo t = np.hist.upTo t → x ∈ reachFrom sp db.P t p np →
      ∃ w, (x, w) ∈ readFrom sp S s true t v := by
  intro b
  induction b with
  | zero => intro p np v h; omega
  | succ b ih =>
    intro p np v hb hnp hr hvn hvl hvh hx
    rw [reachFrom_eq] at hx
    simp only [List.mem_cons, List.mem_flatMap] at hx
    rcases hx with hx | ⟨q, hq, hxq⟩
    · refine ⟨v, ?_⟩
      rw [readFrom_eq, hx, ← hvn]
      exact List.mem_cons_self
    · split at hxq
      · rename_i m hm
        split at hxq
        · rename_i hlt
          obtain ⟨e, he, hqe⟩ := hls _ _ hq
          have hqw : written sp q = true :=
            written_of_ne_root sp (hinv.ptr_ne_root hnp (mem_upTo.mp he).1 hqe)
          have hqr : reachable sp db.P t q = true :=
            (reachable_iff _ _ _ _).mpr (Reach.child ((reachable_iff _ _ _ _).mp hr) hnp hq hm hlt)
          obtain ⟨w, hw, hwn, hwl, hwh⟩ := hnew q m ⟨hqw, hqr, m, hm, hxq⟩ hm
          obtain ⟨w', hw'⟩ := ih q m w (by omega) hm hqr hwn hwl hwh hxq
          refine ⟨w', ?_⟩
          rw [readFrom_eq]
          apply List.mem_cons_of_mem
          apply List.mem_flatMap.mpr
          refine ⟨q, by rw [hvh]; exact hq, ?_⟩
          rw [follow_newest hw]
          have hlt' : w.level < v.level := by rw [hwl, hvl]; exact hlt
          simp only [hlt', ↓reduceIte]
          exact hw'
        · simp at hxq
      · simp at hxq

/-- With a virtual root: after a safe cut, startup's read of the root children
from the cut stream reads, at its latest version, every root child created up
to s at C0 or later, if the root children created then have their latest
versions at the cut or later. -/
theorem Inv.topsRead_cut_from (hinv : Inv sp db k) (hv : sp.virt = true) {c C0 : Nat}
    (hcut : CutOK sp c db k) (hcs : c ≤ lastSp db.S) {n0 : Node V} (h0 : db.P.get? root = some n0)
    (hC : ∀ y m cy u, TopAt sp db.P y m cy → C0 ≤ cy → cy ≤ lastSp db.S → db.S.lv y = some u →
      c ≤ u.recNo) :
    ∀ y my cy, TopAt sp db.P y my cy → C0 ≤ cy → cy ≤ lastSp db.S →
      ∃ w' ∈ topsRead sp (cutStream c db.S) (lastSp db.S) true, w'.node = y ∧ db.S.lv y = some w' := by
  have hvi := hinv.vr hv
  intro y my cy hyt hC0 hcy
  rcases hinv.topVersion_virt hv h0 with ⟨hnil, htv⟩ | ⟨zs, ms, cs, us, hzt, hcs', hmax, hus, htv⟩
  · exfalso
    have : (⟨cy, sp.rootVal y⟩ : Entry V) ∈ n0.hist.upTo (lastSp db.S) :=
      mem_upTo.mpr ⟨hvi.topEntry y my cy hyt n0 h0, hcy⟩
    rw [hnil] at this; simp at this
  · obtain ⟨husn, -⟩ := hinv.version_node (hinv.lv_at hus)
    have hws : topsRead sp (cutStream c db.S) (lastSp db.S) true =
        readTops sp (cutStream c db.S) (lastSp db.S) true us := by
      unfold topsRead; rw [topVersion_cut hcut hcs, htv]
    rw [hws]
    rcases Nat.lt_or_ge cy cs with hlt | hge
    · have hy := hvi.closed zs ms cs y my cy hzt hyt hlt
      rw [← husn] at hzt hy
      exact hinv.readTops_all_cut hv hcs hC (ms.level + 1) us ms cs (by omega) hzt hcs'
        (by rw [husn]; exact hus) y hy my cy hyt hC0
    · have hc' : cy = cs := Nat.le_antisymm (hmax y my cy hyt hcy) hge
      rw [← hc'] at hzt
      have := hinv.topAt_unique hv hyt hzt
      rw [this]
      exact ⟨us, by rw [readTops_eq]; exact List.mem_cons_self, husn, hus⟩

/-- After a safe cut, startup's P up to s from the cut stream has the node of
the whole stream's for every node of D that no lookup from f to k reaches. -/
theorem Inv.baseCut_get?_hist (hinv : Inv sp db k) (hls : LiveSub sp) (hvl : VirtLiveOK sp)
    {c : Nat} (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) (ha : DAnchor sp db k)
    (htd : sp.virt = true → TopsD sp db) {x : NodeId} (hx : inD db.D x = true)
    (hnr : ∀ t', lastFa db.S ≤ t' → t' ≤ k → reachable sp db.P t' x = false) :
    (baseStruct sp (cutStream c db.S) (lastSp db.S) true).get? x =
      (baseStruct sp db.S (lastSp db.S) true).get? x := by
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 hfs
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  obtain ⟨t, htk, hrt, hanc⟩ := ha x hx
  have htf : t < lastFa db.S := by
    rcases Nat.lt_or_ge t (lastFa db.S) with h | h
    · exact h
    · have := hnr t h htk
      rw [hrt] at this; cases this
  -- The ancestors of x at t have their newest versions in the section.
  have hsec : ∀ q nq, Anc sp db.P t x q → db.P.get? q = some nq →
      ∃ w, newest db.S (lastSp db.S) q = some w ∧ w.node = q ∧ w.level = nq.level ∧
        w.hist.upTo t = nq.hist.upTo t := by
    intro q nq hq hnq
    obtain ⟨d, hd, hd'⟩ := hanc q hq
    have hsd : lastSp db.S < d := by rw [hinv.inv1] at hd; exact (sectionD_mem hd).1
    rcases hd' with hd' | hd'
    · omega
    · obtain ⟨w0, hw0⟩ := Option.isSome_iff_exists.mp hd'
      cases hw : newest db.S (lastSp db.S) q with
      | none => exact absurd hw (newest_some_of_versionAt hw0 (by omega))
      | some w =>
        obtain ⟨r, hsr, hwr⟩ := newest_some hw
        obtain ⟨hwn, -, n', hn', hwh, hwl, -⟩ := hinv.version_node hwr
        rw [hnq, Option.some.injEq] at hn'
        subst hn'
        refine ⟨w, rfl, hwn, hwl, ?_⟩
        rw [hwh, upTo_upTo _ (by omega : t ≤ r)]
  have hsec' : ∀ q nq, Anc sp db.P t x q → db.P.get? q = some nq →
      ∃ w, newest (cutStream c db.S) (lastSp db.S) q = some w ∧ w.node = q ∧ w.level = nq.level ∧
        w.hist.upTo t = nq.hist.upTo t := by
    intro q nq hq hnq; rw [newest_cut hcs]; exact hsec q nq hq hnq
  -- x is not the root; its newest version u.
  have hxr : x ≠ root := by
    intro h; subst h
    have := hnr (lastFa db.S) (Nat.le_refl _) (by omega)
    rw [reachable_root h0] at this; cases this
  obtain ⟨nx, hnx⟩ := Option.isSome_iff_exists.mp ((reachable_iff _ _ _ _).mp hrt).isSome
  have hxa : Anc sp db.P t x x :=
    ⟨hinv.written_of_D hx, hrt, nx, hnx, self_mem_reachFrom sp _ _ _ _⟩
  obtain ⟨u, hu, -, -, -⟩ := hsec x nx hxa hnx
  -- Every read of x gives u, from either stream.
  have hnodeS : ∀ y ref w, follow db.S (lastSp db.S) true y ref = some w → w.node = y :=
    fun y ref w h => (follow_spec h).1
  have hnodeC : ∀ y ref w, follow (cutStream c db.S) (lastSp db.S) true y ref = some w →
      w.node = y := by
    intro y ref w h
    obtain ⟨r, w0, hw0, hw⟩ := follow_cut_spec hcs h
    have := (hinv.version_node hw0).1
    rcases hw with rfl | rfl
    · exact this
    · exact this
  have hall : ∀ S' : Stream V T, newest S' (lastSp db.S) x = some u →
      (∀ y ref w, follow S' (lastSp db.S) true y ref = some w → w.node = y) →
      ∀ t' ≤ lastSp db.S, ∀ w, (x, w) ∈ readAt sp S' (lastSp db.S) true t' → w = u := by
    intro S' hu' hnode t' _ w hw
    unfold readAt at hw
    cases hsv : startVersion sp S' (lastSp db.S) true with
    | none => rw [hsv] at hw; simp at hw
    | some v =>
      rw [hsv] at hw
      simp only at hw
      obtain ⟨h1, h2⟩ := readFrom_pairs sp hnode (v.level + 1) v (Nat.lt_succ_self _) _ hw
      simp only at h1 h2
      rcases h2 with h2 | ⟨ref, h2⟩
      · subst h2
        rcases startVersion_cases sp S' (lastSp db.S) hsv with h3 | ⟨y, ref, h3⟩
        · exact absurd (h1.trans h3) hxr
        · have hy := hnode y ref w h3
          rw [← hy, ← h1, follow_newest hu'] at h3
          exact (Option.some.inj h3).symm
      · rw [follow_newest hu'] at h2
        exact (Option.some.inj h2).symm
  -- x is read at t from the whole stream.
  have hinS : ∃ w, (x, w) ∈ readAt sp db.S (lastSp db.S) true t := by
    have h1 := (hinv.readAt_spec hls (by omega : t ≤ lastSp db.S)).1
    have h2 : x ∈ reachList sp db.P t := by
      simp only [reachable, List.contains_iff_mem] at hrt; exact hrt
    rw [← h1] at h2
    obtain ⟨⟨a, w⟩, hp, hpx⟩ := List.mem_map.mp h2
    simp only at hpx
    subst hpx
    exact ⟨w, hp⟩
  -- x is read at t from the cut stream, through its ancestors then.
  have hxroot : x ∈ reachFrom sp db.P t root n0 := by
    have := hrt
    simp only [reachable, reachList, List.contains_iff_mem, h0] at this
    exact this
  have hinC : ∃ w, (x, w) ∈ readAt sp (cutStream c db.S) (lastSp db.S) true t := by
    by_cases hv : sp.virt = true
    · have hvi := hinv.vr hv
      rw [reachFrom_eq] at hxroot
      simp only [List.mem_cons, List.mem_flatMap] at hxroot
      rcases hxroot with h | ⟨z1, hz1, hxz⟩
      · exact absurd h hxr
      · split at hxz
        · rename_i m1 hm1
          split at hxz
          · rename_i hlt1
            cases hl : (n0.hist.upTo t).getLast? with
            | none =>
              exfalso
              have hrootE : ∀ e ∈ n0.hist.upTo t, ∃ z, e.val = sp.rootVal z := fun e he => by
                obtain ⟨z', m', -, hval⟩ := hvi.rootEntry n0 h0 e (mem_upTo.mp he).1; exact ⟨z', hval⟩
              rw [hvl hv _ hrootE, hl] at hz1
              simp at hz1
            | some e1 =>
              obtain ⟨z1', m1', hzt1, hval1, -, het1, hlz, hr1⟩ := hinv.rootLast hv hvl h0 hl
              rw [hlz, List.mem_singleton] at hz1
              subst hz1
              have hm : m1' = m1 := by rw [hzt1.1] at hm1; exact Option.some.inj hm1
              subst hm
              -- The root child at t is an ancestor of x then, so in D.
              have hz1a : Anc sp db.P t x z1 := ⟨written_of_ne_root sp hzt1.2.1, hr1, m1', hzt1.1, hxz⟩
              obtain ⟨d1, hd1, -⟩ := hanc z1 hz1a
              have hz1D : inD db.D z1 = true := (inD_iff _ _).mpr ⟨d1, hd1⟩
              -- The root children from its creation on are in D, so their latest
              -- versions are at the cut or later.
              have hC : ∀ y m cy u, TopAt sp db.P y m cy → e1.time ≤ cy → cy ≤ lastSp db.S →
                  db.S.lv y = some u → c ≤ u.recNo := by
                intro y m cy u hyt hcy _ hlv
                have hyD : inD db.D y = true := by
                  rcases Nat.lt_or_ge e1.time cy with h | h
                  · exact htd hv z1 m1' e1.time y m cy hzt1 hyt h hz1D
                  · have hce : cy = e1.time := by omega
                    rw [hce] at hyt
                    rw [hinv.topAt_unique hv hyt hzt1]; exact hz1D
                exact (hcut.2.2.1 y hyD u hlv).1
              obtain ⟨w1, hw1, -, hw1lv⟩ := hinv.topsRead_cut_from hv hcut hcs h0 hC z1 m1' e1.time
                hzt1 (Nat.le_refl _) (by omega)
              -- So the root that startup rebuilds keeps the entry for it.
              have hkeep : cutKeep (topsRead sp (cutStream c db.S) (lastSp db.S) true) e1 = true := by
                unfold cutKeep
                obtain ⟨e', he', he't⟩ := hzt1.exists_entry
                have hwh := hvi.topVers z1 m1' e1.time hzt1 w1.recNo w1 (hinv.lv_at hw1lv)
                exact List.any_eq_true.mpr ⟨w1, hw1, List.any_eq_true.mpr
                  ⟨e', by rw [hwh]; exact he', by simp [he't]⟩⟩
              have hlast : ((rootVersion sp (lastSp db.S)
                  (topsRead sp (cutStream c db.S) (lastSp db.S) true)).hist.upTo t).getLast? = some e1 := by
                rw [hinv.cutRoot_hist hv hcut hcs h0]
                generalize topsRead sp (cutStream c db.S) (lastSp db.S) true = ws' at hkeep ⊢
                have hfilt : History.upTo ((n0.hist.upTo (lastSp db.S)).filter (cutKeep ws')) t =
                    (n0.hist.upTo t).filter (cutKeep ws') := by
                  simp only [History.upTo, List.filter_filter]
                  apply List.filter_congr
                  intro e _
                  by_cases h1 : e.time ≤ t
                  · have : e.time ≤ lastSp db.S := by omega
                    simp [h1, this]
                  · simp [h1]
                rw [hfilt]
                exact getLast?_filter_of hl hkeep
              have hlive : sp.live ((rootVersion sp (lastSp db.S)
                  (topsRead sp (cutStream c db.S) (lastSp db.S) true)).hist.upTo t) = [z1] := by
                rw [hvl hv _ (fun e he => rootVersion_vals sp _ _ e (mem_upTo.mp he).1), hlast]
                simp [hval1, hvi.rootPtrs]
              -- Read through the root child, at its newest version.
              obtain ⟨w1', hw1', hw1'n, hw1'l, hw1'h⟩ := hsec' z1 m1' hz1a hzt1.1
              obtain ⟨w, hw⟩ := hinv.readFrom_anc hls (S := cutStream c db.S) (s := lastSp db.S) x hsec'
                (m1'.level + 1) z1 m1' w1' (Nat.lt_succ_self _) hzt1.1 hr1 hw1'n hw1'l hw1'h hxz
              refine ⟨w, ?_⟩
              unfold readAt startVersion
              simp only [hv, ↓reduceIte]
              rw [readFrom_eq]
              apply List.mem_cons_of_mem
              apply List.mem_flatMap.mpr
              refine ⟨z1, by rw [hlive]; exact List.mem_singleton_self _, ?_⟩
              rw [follow_newest hw1']
              have hrl : n0.level = rootLevel sp := ((hinv.vr hv).rootIdx n0 h0).2
              have hlt' : w1'.level < (rootVersion sp (lastSp db.S)
                  (topsRead sp (cutStream c db.S) (lastSp db.S) true)).level := by
                show w1'.level < rootLevel sp
                rw [hw1'l, ← hrl]; exact hlt1
              simp only [hlt', ↓reduceIte]
              exact hw
          · simp at hxz
        · simp at hxz
    · have hv' : sp.virt = false := by simpa using hv
      have hroota : Anc sp db.P t x root :=
        ⟨by simp [written, hv'], reachable_root h0 t, n0, h0, hxroot⟩
      obtain ⟨u0, hu0, hu0n, hu0l, hu0h⟩ := hsec root n0 hroota h0
      have hstart : startVersion sp (cutStream c db.S) (lastSp db.S) true = some u0 := by
        unfold startVersion
        simp only [hv', Bool.false_eq_true, ↓reduceIte]
        rw [topVersion_cut hcut hcs]
        unfold topVersion
        cases hR : db.S.getLast? with
        | none =>
          exfalso
          rw [List.getLast?_eq_none_iff] at hR
          have := hinv.len
          rw [hR] at this; simp at this
        | some R =>
          simp only [Option.bind_some]
          rw [hinv.top R hR]
          simp only [topOf, hv', Bool.false_eq_true, ↓reduceIte]
          rw [newest_lv hu0]
          simp only [Option.map_some]
          exact follow_newest hu0
      obtain ⟨w, hw⟩ := hinv.readFrom_anc hls (S := cutStream c db.S) (s := lastSp db.S) x hsec'
        (n0.level + 1) root n0 u0 (Nat.lt_succ_self _) h0 (reachable_root h0 t) hu0n hu0l hu0h hxroot
      refine ⟨w, ?_⟩
      unfold readAt
      rw [hstart]
      exact hw
  -- So both give the node of u.
  rw [baseStruct_get?_of sp (cutStream c db.S) (lastSp db.S) x u ⟨t, by omega, hinC⟩
      (hall _ (by rw [newest_cut hcs]; exact hu) hnodeC),
    baseStruct_get?_of sp db.S (lastSp db.S) x u ⟨t, by omega, hinS⟩ (hall _ hu hnodeS)]

end Hist

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

/-- T8 with D's nodes (bergdb item 001, WP R5): after a safe cut, startup from
the cut stream agrees with the run for lookups from f to k, and gives every
node of D the run's node: those that a lookup from f on may reach by the
agreement, the others through their ancestors' versions in the section. -/
theorem recoverCut_dNodes (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) {k : Nat} (hk : k ≤ ts.length) (hex : ExecRootOK sp)
    (hvl : VirtLiveOK sp) {c : Nat} (hcut : CutOK sp c (st sp al ts k) k) :
    CutAgree sp (lastFa (st sp al ts k).S) k (st sp al ts k).P
        (startup sp (cutStream c (st sp al ts k).S)).P ∧
      ∀ x, inD (st sp al ts k).D x = true →
        (startup sp (cutStream c (st sp al ts k).S)).P.get? x = (st sp al ts k).P.get? x := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hls : LiveSub sp := hok.1.liveSub
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hP : (startup sp (cutStream c (st sp al ts k).S)).P =
      rerun sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S)
        (baseStruct sp (cutStream c (st sp al ts k).S) (lastSp (st sp al ts k).S) true) := by
    simp only [startup, startupWith, lastSp_cut]
  have hbase := base_sameNodes sp al ts hok hst hk
  obtain ⟨hag, hX⟩ := rerun_cutAgree_nodes sp al ts hok hst hk hex hvl hcs hfs
    (base_cutAgree sp al ts hok hst hk hvl hcut)
    (fun x => inD (st sp al ts k).D x = true ∧
      ∀ t', lastFa (st sp al ts k).S ≤ t' → t' ≤ k → reachable sp (st sp al ts k).P t' x = false)
    (fun x ⟨hx, hnr⟩ => by
      rw [hinv.baseCut_get?_hist hls hvl hcut hfs (dAnchor_st sp al ts hok hj hmk k hk)
        (fun hv => topsD_st sp al ts hok hj hmk hv hvl k hk) hx hnr, hbase x])
  rw [hP]
  refine ⟨hag, ?_⟩
  intro x hx
  by_cases hr : ∃ t', lastFa (st sp al ts k).S ≤ t' ∧ t' ≤ k ∧ reachable sp (st sp al ts k).P t' x = true
  · obtain ⟨t', h1, h2, h3⟩ := hr
    exact hag.nodes x t' h1 h2 (fun hv => ne_root_of_written hv (hinv.written_of_D hx)) h3
  · apply hX x ⟨hx, fun t' h1 h2 => ?_⟩
    cases h : reachable sp (st sp al ts k).P t' x
    · rfl
    · exact absurd ⟨t', h1, h2, h⟩ hr

end Run

end SIS
