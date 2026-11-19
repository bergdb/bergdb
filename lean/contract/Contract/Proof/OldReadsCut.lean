/- bergdb 030-24: part 2 of `CutOK`, with RC2 and RC3 at the iteration's end
   e and the first wait (`rc_reads`). -/
import Contract.Proof.OldReadsClosure
namespace Contract.OldReads
open SIS
variable {V T : Type} [DecidableEq V]
variable {sp : Spec V T} {al : Algo V T} {ts : List T}

theorem rc_reads (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (e k c : Nat) (hce : c ≤ e) (hek : e ≤ k) (hk : k ≤ ts.length)
    (hrw : ∀ d m, (st sp al ts e).P.get? d = some m → m.isData = true →
      reachable sp (st sp al ts e).P e d = true →
        ∃ u, (st sp al ts e).S.lv d = some u ∧ c ≤ u.recNo)
    (hlb : ∀ x n, (st sp al ts e).P.get? x = some n → n.isData = false →
      written sp x = true → reachable sp (st sp al ts e).P e x = true →
      ∃ d m, d ∈ reachFrom sp (st sp al ts e).P e x n ∧
        (st sp al ts e).P.get? d = some m ∧ m.isData = true)
    (hsp : e ≤ lastSp (st sp al ts k).S) :
    ∀ t w, e ≤ t → t ≤ k → ReadsPhys sp (st sp al ts k).S
      (st sp al ts k).P (st sp al ts k).D t w → c ≤ w.recNo := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinve := inv_st sp al ts hok hst e (by omega)
  have hinvk := inv_st sp al ts hok hst k hk
  have hg := st_grow sp al ts hok hst hek hk
  have hpre := st_S_prefix sp al ts hek hk
  apply reads_ge_cut hok hst e k c hce hek hk hsp (oldReadsGood_st hok hj hk)
  · intro d m hm hd hr
    have hre : reachable sp (st sp al ts e).P e d = true := by
      rw [← reachable_grow hok.1.liveSub hinve.ptrs hinve.rootIn hg (Nat.le_refl e)]
      exact hr
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp
      (Reach.isSome ((reachable_iff _ _ _ _).mp hre))
    obtain ⟨m', hm', _, hkind, _⟩ := hg d n hn
    rw [hm] at hm'; cases hm'
    have hnd : n.isData = true := by rw [← hkind]; exact hd
    obtain ⟨u, hu, hcu⟩ := hrw d n hn hnd hre
    have huk := versionAt_prefix hpre (hinve.lv_at hu)
    have hlu := dataOnce_st sp al ts hok hst k hk d m u.recNo u hm hd huk
    exact ⟨u, hlu, hcu⟩
  · intro x n hn hd hxw hr
    have hre : reachable sp (st sp al ts e).P e x = true := by
      rw [← reachable_grow hok.1.liveSub hinve.ptrs hinve.rootIn hg (Nat.le_refl e)]
      exact hr
    obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp
      (Reach.isSome ((reachable_iff _ _ _ _).mp hre))
    obtain ⟨n', hn', _, hkind, _⟩ := hg x n0 hn0
    rw [hn] at hn'; cases hn'
    have hnd : n0.isData = false := by rw [← hkind]; exact hd
    obtain ⟨d, m, hd0, hm, hmd⟩ := hlb x n0 hn0 hnd hxw hre
    obtain ⟨m', hm', _, hmk, _⟩ := hg d m hm
    refine ⟨d, m', ?_, hm', by rw [hmk]; exact hmd⟩
    rw [reachFrom_grow hok.1.liveSub hinve.ptrs hg (Nat.le_refl e)
      (n0.level+1) x n0 n (by omega) hn0 hn]
    exact hd0

end Contract.OldReads
