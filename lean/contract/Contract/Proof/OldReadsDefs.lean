/- bergdb 030-24: the read invariant of the independent search made beside
   030-23, its definitions and the step from it to part 2 of `CutOK`
   (`reads_ge_cut`); with I0 (`SectionLatest`), I5 (`SectionRefsGood`) and I3
   (`PendingRefsFresh`), which hold in every reached state (OldReadsSection.lean,
   OldReadsClosure.lean, OldReadsDirty.lean), and I4 (`AfterVFrozen`), unused.
   It changes none of the model's definitions. -/
import SIS.Proof.CutCover

namespace Contract.OldReads
open SIS
variable {V T : Type} [DecidableEq V]
variable {sp : Spec V T} {db : DB V T} {k c v : Nat}

/-- I0. A version beyond the startup position is still its node's latest. -/
def SectionLatest (db : DB V T) : Prop :=
  ∀ r x w, db.S.versionAt r x = some w → lastSp db.S < r → db.S.lv x = some w

/-- I5. A section version that was not put back has good references for
    every earlier time at which an old target is reachable. No cut parameter. -/
def SectionRefsGood (sp : Spec V T) (db : DB V T) : Prop :=
  ∀ r x w, db.S.versionAt r x = some w → lastSp db.S < r → (x,r) ∉ db.D →
    ∀ y a u, w.ref? y = some a → a ≤ lastSp db.S → u ≤ lastSp db.S →
      reachable sp db.P u y = true →
      ∀ z, db.S.versionAt a y = some z → good sp db.S db.P u z = true

/-- I1 and I2. The historical prefix of a physical read is good at the
    clamped lookup time, and is reachable then. No reclaim hypotheses. -/
def OldReadsGood (sp : Spec V T) (db : DB V T) (k : Nat) : Prop :=
  ∀ t, t ≤ k → ∀ w, ReadsPhys sp db.S db.P db.D t w → w.recNo ≤ lastSp db.S →
    good sp db.S db.P (min t (lastSp db.S)) w = true ∧
      reachable sp db.P (min t (lastSp db.S)) w.node = true

/-- I3. A pending dirty node with a pre-section version has fresh references.
    The proposed preservation premise is A6', through EvLogic.clean. -/
def PendingRefsFresh (db : DB V T) : Prop :=
  ∀ x, inD db.D x = true → ∀ w, db.S.lv x = some w → w.recNo ≤ lastSp db.S →
    ∀ y a, w.ref? y = some a → (db.S.lv y).map (·.recNo) = some a

/-- I4. After the first wait, new versions reference below c only frozen
    targets. This form states the result at any later state. -/
def AfterVFrozen (c v : Nat) (db : DB V T) : Prop :=
  ∀ r x w, db.S.versionAt r x = some w → v < r →
    ∀ y a, w.ref? y = some a → a < c →
      (db.S.lv y).map (·.recNo) = some a ∧ inD db.D y = false

/-- A good version written no later than e, good at q >= e, is good at e.
    Every referenced version is earlier than its parent, so all histories
    on the exact reference chain have the same prefix at e and q. -/
theorem good_down (hinv : Inv sp db k) (_hls : LiveSub sp) :
    ∀ b r x w, w.level < b → db.S.versionAt r x = some w →
      ∀ e q, r ≤ e → e ≤ q → good sp db.S db.P q w = true →
        good sp db.S db.P e w = true := by
  intro b
  induction b with
  | zero => intro r x w h; omega
  | succ b ih =>
    intro r x w hb hw e q hre heq hg
    obtain ⟨hwx, hwr, n, hn, hwh, hwl, _⟩ := hinv.version_node hw
    have wh : w.hist.upTo e = w.hist := by rw [hwh, upTo_upTo' _ hre]
    have wq : w.hist.upTo q = w.hist := by rw [hwh, upTo_upTo' _ (by omega)]
    rw [good_iff] at hg ⊢
    obtain ⟨⟨n', hn', heqh⟩, kids⟩ := hg
    rw [hwx, hn] at hn'
    cases hn'
    have nh : n.hist.upTo e = w.hist := by
      have h := congrArg (fun h : History V => h.upTo e) heqh
      rw [wq, wh, upTo_upTo _ heq] at h
      exact h.symm
    refine ⟨⟨n, by rw [hwx]; exact hn, by rw [wh, nh]⟩, ?_⟩
    intro y hy
    have hyq : y ∈ sp.live (w.hist.upTo q) := by rw [wq, ← wh]; exact hy
    obtain ⟨a, z, ha, hz, hlev, hgood⟩ := kids y hyq
    have hae := hinv.ref_le_recNo hw ha
    refine ⟨a, z, ha, hz, hlev, ?_⟩
    exact ih a y z (by omega) hz e q (by omega) heq hgood

/-- The data-below argument applies to ANY good version, not just a latest
    version. At e it cannot lie below a cut that covers every live data node. -/
theorem good_at_end_ge_cut (hinv : Inv sp db k) (hdo : DataOnce db)
    (e c : Nat)
    (rw : ∀ d m, db.P.get? d = some m → m.isData = true →
      reachable sp db.P e d = true → ∃ z, db.S.lv d = some z ∧ c ≤ z.recNo)
    (lb : ∀ x n, db.P.get? x = some n → n.isData = false → written sp x = true →
      reachable sp db.P e x = true →
      ∃ d m, d ∈ reachFrom sp db.P e x n ∧ db.P.get? d = some m ∧ m.isData = true)
    {r x : Nat} {w : Version V} (hw : db.S.versionAt r x = some w)
    (hr : reachable sp db.P e x = true) (hg : good sp db.S db.P e w = true) : c ≤ r := by
  obtain ⟨_, hwr, n, hn, _, _, hdata⟩ := hinv.version_node hw
  cases hd : n.isData with
  | true =>
    have hl := hdo x n r w hn hd hw
    obtain ⟨z, hz, hcz⟩ := rw x n hn hd hr
    rw [hl] at hz
    cases hz
    omega
  | false =>
    obtain ⟨d, m, hbelow, hm, hmd⟩ := lb x n hn hd (hinv.written_of_versionAt hw) hr
    have hrd : reachable sp db.P e d = true :=
      (reachable_iff _ _ _ _).mpr
        (reach_of_mem_reachFrom sp _ e (n.level + 1) x n (by omega) hn
          ((reachable_iff _ _ _ _).mp hr) d hbelow)
    obtain ⟨r', z, hle, hz, _⟩ :=
      hinv.good_below (n.level + 1) r x w n (by omega) hw hn hg d hbelow
    have hl := hdo d m r' z hm hmd hz
    obtain ⟨z', hz', hcz⟩ := rw d m hm hmd hrd
    rw [hl] at hz'
    cases hz'
    have := (hinv.version_node hz).2.1
    omega

/-- Conditional read soundness: I1/I2 imply the open READ half, from the
    FIRST wait. RC2/RC3 are stated at time e in the final history here;
    their transport from state e uses the existing Grow/DataOnce lemmas.
    Invariant preservation is intentionally not a premise silently asserted
    as a theorem: hprefix is explicit. -/
theorem reads_ge_cut {al : Algo V T} {ts : List T}
    (hok : RunOK sp al ts) (hst : AlgOK sp al) (e k c : Nat)
    (hce : c ≤ e) (hek : e ≤ k) (hk : k ≤ ts.length)
    (hsp : e ≤ lastSp (st sp al ts k).S)
    (hprefix : OldReadsGood sp (st sp al ts k) k)
    (hrw : ∀ d m, (st sp al ts k).P.get? d = some m → m.isData = true →
      reachable sp (st sp al ts k).P e d = true →
        ∃ z, (st sp al ts k).S.lv d = some z ∧ c ≤ z.recNo)
    (hlb : ∀ x n, (st sp al ts k).P.get? x = some n → n.isData = false →
      written sp x = true → reachable sp (st sp al ts k).P e x = true →
      ∃ d m, d ∈ reachFrom sp (st sp al ts k).P e x n ∧
        (st sp al ts k).P.get? d = some m ∧ m.isData = true) :
    ∀ t w, e ≤ t → t ≤ k → ReadsPhys sp (st sp al ts k).S
      (st sp al ts k).P (st sp al ts k).D t w → c ≤ w.recNo := by
  intro t w het htk hread
  by_cases hc : c ≤ w.recNo
  · exact hc
  exfalso
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨r, hw⟩ := hinv.readsPhys_version hread
  have hwr : w.recNo = r := (hinv.version_node hw).2.1
  have hwe : r ≤ e := by omega
  obtain ⟨hg, hrq⟩ := hprefix t htk w hread (by omega)
  have hqk : min t (lastSp (st sp al ts k).S) ≤ k := by omega
  have heq : e ≤ min t (lastSp (st sp al ts k).S) := by omega
  have hex : ((st sp al ts e).P.get? w.node).isSome := by
    cases hx : (st sp al ts e).P.get? w.node with
    | some n => simp
    | none =>
      have := st_version_after hok hst hek hk hx hw
      omega
  have hre : reachable sp (st sp al ts k).P e w.node = true := by
    have h := reach_back_st hok hst (j1 := e) hk
      (min t (lastSp (st sp al ts k).S) - e)
      (min t (lastSp (st sp al ts k).S)) (by omega) hqk w.node hrq hex
    have hinve := inv_st sp al ts hok hst e (by omega)
    rw [reachable_grow hok.1.liveSub hinve.ptrs hinve.rootIn
      (st_grow sp al ts hok hst hek hk) (Nat.le_refl e)]
    exact h
  have hge := good_down hinv hok.1.liveSub (w.level + 1) r w.node w
    (by omega) hw e (min t (lastSp (st sp al ts k).S)) hwe heq hg
  have hcr := good_at_end_ge_cut hinv (dataOnce_st sp al ts hok hst k hk)
    e c hrw hlb hw hre hge
  omega

/-- The two D-reference invariants combine arithmetically after the second
    wait. No reachable-node premise is needed, so historical D is included. -/
theorem dirty_refs_of_fences (hinv : Inv sp db k) (hpend : PendingRefsFresh db)
    (hfrozen : AfterVFrozen c v db) (hwait : v < lastSp db.S) :
    ∀ x, inD db.D x = true → ∀ w, db.S.lv x = some w →
      ∀ y a, w.ref? y = some a → a < c → (db.S.lv y).map (·.recNo) = some a := by
  intro x hx w hw y a ha hac
  by_cases hr : w.recNo ≤ lastSp db.S
  · exact hpend x hx w hw hr y a ha
  · exact (hfrozen w.recNo x w (hinv.lv_at hw) (by omega) y a ha hac).1

end Contract.OldReads

