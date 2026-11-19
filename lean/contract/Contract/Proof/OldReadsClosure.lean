/- From the local section certificate to physical read closure. -/
import Contract.Proof.OldReadsReach
namespace Contract.OldReads
open SIS
variable {V T : Type} [DecidableEq V]

section Helpers
variable {sp : Spec V T} {db : DB V T} {k : Nat}

theorem latest_old_good (hinv : Inv sp db k) (hls : LiveSub sp)
    {x : Nat} {w : Version V} (hlw : db.S.lv x = some w)
    (hws : w.recNo ≤ lastSp db.S) {q : Nat} (hqs : q ≤ lastSp db.S)
    (hr : reachable sp db.P q x = true) : good sp db.S db.P q w = true := by
  cases hxD : inD db.D x
  · have hqk : q ≤ k := by have := hinv.spLt; omega
    obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hxD (hinv.written_of_versionAt (hinv.lv_at hlw)) hqk hr
    rw [hlw] at hv
    cases hv
    exact hg
  · obtain ⟨d, hd⟩ := (inD_iff _ _).mp hxD
    have hsd := (sectionD_mem (hinv.inv1 ▸ hd)).1
    rcases hinv.inv3 x d w hd hlw with h | h
    · omega
    · exact h q (by omega) hr

theorem clamp_hist (hinv : Inv sp db k) {r x : Nat} {v : Version V}
    (hv : db.S.versionAt r x = some v) (hrs : r ≤ lastSp db.S) (t : Nat) :
    v.hist.upTo t = v.hist.upTo (min t (lastSp db.S)) := by
  by_cases hts : t ≤ lastSp db.S
  · rw [Nat.min_eq_left hts]
  · obtain ⟨_, _, n, _, hh, _⟩ := hinv.version_node hv
    rw [Nat.min_eq_right (by omega), hh, upTo_upTo' _ (by omega), upTo_upTo' _ hrs]

theorem data_no_live (hinv : Inv sp db k) (hls : LiveSub sp)
    {r x t y : Nat} {v : Version V} (hv : db.S.versionAt r x = some v)
    (hd : v.isData = true) (hy : y ∈ sp.live (v.hist.upTo t)) : False := by
  obtain ⟨_, _, n, hn, hh, _, hnd⟩ := hinv.version_node hv
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  have he' := (mem_upTo.mp he).1
  rw [hh] at he'
  have hne := (mem_upTo.mp he').1
  have hndata : n.isData = true := by rw [← hnd]; exact hd
  rw [hinv.data x n hn hndata e hne] at hye
  cases hye

/-- Any child version already before the parent's record is no newer than
    that parent's serialized reference. In particular, that ref is not a vpos. -/
theorem ref_ge_old_version (hinv : Inv sp db k)
    {r x a y : Nat} {v w : Version V} (hv : db.S.versionAt r x = some v)
    (hy : y ∈ pointees sp v.hist) (hw : db.S.versionAt a y = some w) (har : a < r) :
    ∃ b, v.ref? y = some b ∧ a ≤ b := by
  obtain ⟨pre, R, hR, hpre, href⟩ := hinv.ref_lv hv hy
  have hrlen : r < db.S.length := (List.getElem?_eq_some_iff.mp hR).1
  have hlen : (db.S.take r).length = r := by rw [List.length_take]; omega
  have hwb : (Stream.building (db.S.take r) pre).versionAt a y = some w := by
    rw [versionAt_building_lt (by omega), versionAt_take]
    simpa [har] using hw
  obtain ⟨b, z, hb, hlz, hab⟩ := lv_recNo_ge hwb
  have hbS := (sext_building_take hR hpre).versionAt hb
  have hzb : z.recNo = b := (hinv.version_node hbS).2.1
  exact ⟨b, by rw [href, hlz]; simp [hzb], hab⟩

theorem section_follow_latest (hinv : Inv sp db k)
    {r x y : Nat} {v w : Version V} (hv : db.S.versionAt r x = some v)
    (hsr : lastSp db.S < r) (hyp : y ∈ pointees sp v.hist)
    (hf : follow db.S (lastSp db.S) true y (v.ref? y) = some w) : db.S.lv y = some w := by
  cases hn : newest db.S (lastSp db.S) y with
  | some u =>
    rw [follow_newest hn] at hf
    have huw := Option.some.inj hf
    rw [← huw]
    exact newest_lv hn
  | none =>
    obtain ⟨_, a, hw⟩ := follow_spec hf
    obtain ⟨u, hu, _⟩ := hinv.le_lv hw
    have hus : u.recNo < lastSp db.S := by
      apply Nat.lt_of_not_ge
      intro hge
      have hnone := (newest_eq_none_iff _ _ _).mp hn u.recNo hge
      rw [hinv.lv_at hu] at hnone
      cases hnone
    obtain ⟨b, hb, hub⟩ := ref_ge_old_version hinv hv hyp (hinv.lv_at hu) (by omega)
    obtain ⟨u', hu'⟩ := hinv.ref_versionAt hv hb
    obtain ⟨u'', hu'', hbu⟩ := hinv.le_lv hu'
    rw [hu] at hu''
    cases hu''
    have hbeq : b = u.recNo := by omega
    rw [hbeq] at hb
    have hfu := hinv.follow_lv hu
    rw [hb, hfu] at hf
    have huw := Option.some.inj hf
    rw [← huw]
    exact hu

end Helpers

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The read-prefix invariant, now derived from the local certificate. It
    requires RunOK and Java's Rule A, not A6' or any reclaim hypothesis. -/
theorem oldReadsGood_st (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    {k : Nat} (hk : k ≤ ts.length) : OldReadsGood sp (st sp al ts k) k := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  let db := st sp al ts k
  let s := lastSp db.S
  have hinv : Inv sp db k := inv_st sp al ts hok hst k hk
  have hsk : s ≤ k := by have := hinv.spLt; omega
  have hsection : SectionRefsGood sp db := sectionRefsGood_st hok hj hk
  intro t htk
  let q := min t s
  have hqs : q ≤ s := Nat.min_le_right _ _
  have main : ∀ w, ReadsPhys sp db.S db.P db.D t w →
      (w.recNo ≤ s → good sp db.S db.P q w = true ∧ reachable sp db.P q w.node = true) ∧
      (w.isData = false → reachable sp db.P q w.node = true) := by
    intro w hread
    induction hread with
    | latest x w hr hlw =>
      have hwat := hinv.lv_at hlw
      have hwn : w.node = x := (hinv.version_node hwat).1
      have reachq (hne : w.recNo ≤ s ∨ w.isData = false) : reachable sp db.P q x = true := by
        by_cases hts : t ≤ s
        · have hq : q = t := Nat.min_eq_left hts
          rw [hq]; exact hr
        · have hq : q = s := Nat.min_eq_right (by omega)
          rw [hq]
          have hex : ((st sp al ts s).P.get? x).isSome := by
            rcases hne with h | h
            · exact old_version_exists hok hst hk hsk hwat h
            · exact index_exists_at_startup hok hst hk hwat h
          exact reach_back_in_final hok hst hk (by omega : s ≤ t) htk hr hex
      constructor
      · intro hws
        have hrq := reachq (Or.inl hws)
        exact ⟨latest_old_good hinv hok.1.liveSub hlw hws hqs hrq, by rw [hwn]; exact hrq⟩
      · intro hd
        rw [hwn]
        exact reachq (Or.inr hd)
    | child v y w hp hy hf ih =>
      obtain ⟨rp, hpv⟩ := hinv.readsPhys_version hp
      have hpr : v.recNo = rp := (hinv.version_node hpv).2.1
      have hvp : db.S.versionAt v.recNo v.node = some v := by simpa [hpr] using hpv
      have hreadw : ReadsPhys sp db.S db.P db.D t w := ReadsPhys.child v y w hp hy hf
      obtain ⟨rc, hcv⟩ := hinv.readsPhys_version hreadw
      have hcr : w.recNo = rc := (hinv.version_node hcv).2.1
      have hwv : db.S.versionAt w.recNo w.node = some w := by simpa [hcr] using hcv
      have hwn : w.node = y := by
        rcases hf with hf | ⟨_, r, hwr, _⟩
        · exact (follow_spec hf).1
        · exact (hinv.version_node hwr).1
      have hwy : db.S.versionAt w.recNo y = some w := by rw [← hwn]; exact hwv
      have hyp : y ∈ pointees sp v.hist := mem_pointees_of_live hok.1.liveSub hy
      have hvdata : v.isData = false := by
        cases hd : v.isData
        · rfl
        · exact False.elim (data_no_live hinv hok.1.liveSub hvp hd hy)
      have hparent := ih.2 hvdata
      have hchildReach (hne : w.recNo ≤ s ∨ w.isData = false) : reachable sp db.P q y = true := by
        by_cases hvs : v.recNo ≤ s
        · obtain ⟨hgood, _⟩ := ih.1 hvs
          have hyq : y ∈ sp.live (v.hist.upTo q) := by
            rw [← clamp_hist hinv hvp hvs t]; exact hy
          obtain ⟨⟨nx, hnx, hh⟩, _⟩ := (good_iff sp db.S db.P q v).mp hgood
          exact (hinv.reach_child hok.1.liveSub hnx hparent (by rw [← hh]; exact hyq)).1
        · obtain ⟨_, _, nx, hnx, hh, _⟩ := hinv.version_node hvp
          by_cases hts : t ≤ s
          · have hq : q = t := Nat.min_eq_left hts
            have hh' : v.hist.upTo t = nx.hist.upTo t := by
              rw [hh, upTo_upTo _ (by omega)]
            apply (hinv.reach_child hok.1.liveSub hnx hparent ?_).1
            rw [hq, ← hh']; exact hy
          · have hq : q = s := Nat.min_eq_right (by omega)
            have hex : ((st sp al ts s).P.get? y).isSome := by
              rcases hne with h | h
              · exact old_version_exists hok hst hk hsk hwy h
              · exact index_exists_at_startup hok hst hk hwy h
            have hh' : v.hist.upTo t = nx.hist.upTo (min t v.recNo) := by
              rw [hh]
              by_cases htr : t ≤ v.recNo
              · rw [Nat.min_eq_left htr, upTo_upTo _ htr]
              · rw [Nat.min_eq_right (by omega), upTo_upTo' _ (by omega)]
            have hrp : v.recNo ≤ k := by
              have := versionAt_lt_length hvp
              rw [hinv.len] at this; omega
            rw [hq]
            exact live_child_back hok hst hk hsk hnx (by simpa [hq] using hparent) hex
              (min t v.recNo) (by omega) (by omega) (by rw [← hh']; exact hy)
      constructor
      · intro hws
        have hrq := hchildReach (Or.inl hws)
        refine ⟨?_, by rw [hwn]; exact hrq⟩
        rcases hf with hfollow | ⟨hguard, r, hwr, hbound⟩
        · cases hn : newest db.S s y with
          | some u =>
            rw [follow_newest hn] at hfollow
            have huw := Option.some.inj hfollow
            have hlw : db.S.lv y = some w := by rw [← huw]; exact newest_lv hn
            exact latest_old_good hinv hok.1.liveSub hlw hws hqs hrq
          | none =>
            have hn' : newest db.S (lastSp db.S) y = none := hn
            cases href : v.ref? y with
            | none => simp [follow, hn', href] at hfollow
            | some a =>
              have haw : db.S.versionAt a y = some w := by simpa [follow, hn', href] using hfollow
              by_cases hvs : v.recNo ≤ s
              · obtain ⟨hgood, _⟩ := ih.1 hvs
                have hyq : y ∈ sp.live (v.hist.upTo q) := by
                  rw [← clamp_hist hinv hvp hvs t]; exact hy
                obtain ⟨_, kids⟩ := (good_iff sp db.S db.P q v).mp hgood
                obtain ⟨a', z, haz, hz, _, hgz⟩ := kids y hyq
                rw [href] at haz
                cases haz
                rw [haw] at hz
                cases hz
                exact hgz
              · by_cases hguard : (v.node, v.recNo) ∈ db.D
                · have hlw := section_follow_latest hinv hvp (by omega) hyp hfollow
                  exact latest_old_good hinv hok.1.liveSub hlw hws hqs hrq
                · have hwa : w.recNo = a := (hinv.version_node haw).2.1
                  exact hsection v.recNo v.node v hvp (by omega) hguard y a q href
                    (by omega) hqs hrq w haw
        · by_cases hvs : v.recNo ≤ s
          · obtain ⟨hgood, _⟩ := ih.1 hvs
            have hyq : y ∈ sp.live (v.hist.upTo q) := by
              rw [← clamp_hist hinv hvp hvs t]; exact hy
            obtain ⟨_, kids⟩ := (good_iff sp db.S db.P q v).mp hgood
            obtain ⟨a, z, haz, hz, _, hgz⟩ := kids y hyq
            exact hinv.newer hok.1.liveSub (z.level+1) a r y z w (by omega) hz hwr
              (hbound a haz) q hgz
          · obtain ⟨a, ha, hwa⟩ := ref_ge_old_version hinv hvp hyp hwy (by omega)
            have har := hbound a ha
            have hwrrec : w.recNo = r := (hinv.version_node hwr).2.1
            have hae : a = w.recNo := by omega
            rw [hae] at ha
            exact hsection v.recNo v.node v hvp (by omega) hguard y w.recNo q ha hws hqs hrq w hwy
      · intro hd
        rw [hwn]
        exact hchildReach (Or.inr hd)
  intro w hread hws
  exact (main w hread).1 hws

end Contract.OldReads
