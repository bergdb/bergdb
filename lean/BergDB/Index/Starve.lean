/-
The user indexes of BergDB 2026.4 in Lean: weak fairness does not suffice for
BuildEnds with several names (bergdb 020-29).

A run of the model with two names, A (0) and B (1), over one directory with no
data. A is created and its build reaches its check (`isLive`, under the lock).
Then, for ever, round after round: B is created (the lock taken), its maps
(released), its build reads its end key and its step (and waits at its check),
B is deleted (the lock taken), its maps (released), its cleanup finds no entry
and ends. Every thread is weakly fair: each is unable to step at some time of
every round (the builds while the lock is taken, the maps and the cleanups
when there is none, the writer always). The lock is free in every round, there
is no crash, retry or abort, and finitely many keys and writers: every
hypothesis of `build_ends` but strong fairness holds. Yet A stays building for
ever: so the run is not strongly fair for A's build, and weak fairness alone
does not give BuildEnds.
-/
import BergDB.Index.Liveness
import BergDB.Index.Example

namespace BergDB.Index

/-- The systems of the run. -/
abbrev SysX := Sys Nat Unit Nat Unit

/-- A build as it starts, and after it read its end key. -/
def bInit : BSt Nat Unit := BSt.init ()
def bRd : BSt Nat Unit := { bInit with E := some 0, pc := .read }
/-- A cleanup as it starts. -/
def cInit : CSt Nat := CSt.init

/-- A creation of the name n. -/
def rCreate (n : Nat) (s : SysX) : SysX :=
  s.commit
    { s.st with dfn := upd s.st.dfn n (some ⟨max 1 s.st.now, (), false⟩),
                wdef := upd s.st.wdef n (s.st.now + 1),
                wv := upd s.st.wv (exSpec.dirF ()) (s.st.now + 1), now := s.st.now + 1 }
    { s.m with lock := .mgr, admin := .create n (max 1 s.st.now) () }

/-- Its maps. -/
def rMap (n : Nat) (s : SysX) (g : Nat) : SysX :=
  { s with m :=
    { s.m with
      mem := upd s.m.mem n (s.st.dfn n), lock := .free, admin := .idle,
      bld := upd2 s.m.bld n g (some bInit) } }

/-- Its build reads its end key. -/
def rReadE (n : Nat) (s : SysX) (g : Nat) : SysX :=
  { s with m :=
    { s.m with bld := upd2 s.m.bld n g (some bRd) } }

/-- The build's checked step. -/
def bCk (s : SysX) : BSt Nat Unit :=
  { bRd with hi := 1, R := s.st.now, snap := s.st.data, ended := decide (1 = 0 + 1),
             pc := .check }

/-- Its build's step reads. -/
def rRead (n : Nat) (s : SysX) (g : Nat) : SysX :=
  { s with m := { s.m with bld := upd2 s.m.bld n g (some (bCk s)) } }

/-- B's deletion. -/
def rDelete (s : SysX) (g : Nat) : SysX :=
  s.commit
    { s.st with dfn := upd s.st.dfn 1 none, mark := upd2 s.st.mark 1 g true,
                wdef := upd s.st.wdef 1 (s.st.now + 1),
                wv := upd s.st.wv (exSpec.dirF ()) (s.st.now + 1), now := s.st.now + 1 }
    { s.m with lock := .mgr, admin := .delete 1 g }

/-- Its maps, and its cleanup. -/
def rDelMap (s : SysX) (g : Nat) : SysX :=
  { s with m :=
    { s.m with
      mem := upd s.m.mem 1 none, lock := .free, admin := .idle,
      cln := upd2 s.m.cln 1 g (some cInit) } }

/-- The cleanup's scan from the prefix finds none. -/
def rScanEnd (s : SysX) (g : Nat) : SysX :=
  { s with m := { s.m with cln := upd2 s.m.cln 1 g (some { cInit with pc := .done }) } }

/-- The marker deleted. -/
def rEnd (s : SysX) (g : Nat) : SysX :=
  s.commit { s.st with mark := upd2 s.st.mark 1 g false, now := s.st.now + 1 }
    { s.m with cln := upd2 s.m.cln 1 g none }

/-- The states of a round from its first, s, with B's generation g. -/
def rAt (s : SysX) (g : Nat) : Nat → SysX
  | 0 => s
  | 1 => rCreate 1 s
  | 2 => rMap 1 (rCreate 1 s) g
  | 3 => rReadE 1 (rMap 1 (rCreate 1 s) g) g
  | 4 => rRead 1 (rReadE 1 (rMap 1 (rCreate 1 s) g) g) g
  | 5 => rDelete (rRead 1 (rReadE 1 (rMap 1 (rCreate 1 s) g) g) g) g
  | 6 => rDelMap (rDelete (rRead 1 (rReadE 1 (rMap 1 (rCreate 1 s) g) g) g) g) g
  | 7 => rScanEnd (rDelMap (rDelete (rRead 1 (rReadE 1 (rMap 1 (rCreate 1 s) g) g) g) g) g) g
  | _ => rEnd (rScanEnd (rDelMap (rDelete (rRead 1 (rReadE 1 (rMap 1 (rCreate 1 s) g) g) g) g) g)
      g) g

/-- The threads of a round's steps. -/
def rLbl (g : Nat) : Nat → Lbl Unit
  | 0 => .achange
  | 1 => .amap
  | 2 => .bld 1 g
  | 3 => .bld 1 g
  | 4 => .achange
  | 5 => .amap
  | 6 => .cln 1 g
  | _ => .cln 1 g

/-- What holds at the first state of each round. -/
structure RoundOk (s : SysX) : Prop where
  admin : s.m.admin = .idle
  lock : s.m.lock = .free
  mem1 : s.m.mem 1 = none
  wr : ∀ w, s.m.wr w = .idle
  ent : ∀ n g k l, ¬ s.st.ent n g k l
  dfnA : s.st.dfn 0 = some ⟨1, (), false⟩
  bldCheck : ∀ n g b, s.m.bld n g = some b → b.pc = .check
  bldA : s.m.bld 0 1 ≠ none
  cln : ∀ n g, s.m.cln n g = none
  data : ∀ k, s.st.data k = none
  now1 : 1 ≤ s.st.now


/-- Each step of a round is a step of the model. -/
theorem round_step {s : SysX} (hs : RoundOk s) (p : Nat) (hp : p < 8) :
    Step exSpec (rAt s (max 1 s.st.now) p) (rLbl (max 1 s.st.now) p)
      (rAt s (max 1 s.st.now) (p + 1)) := by
  have h8 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
  rcases h8 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Step.aCreate s 1 () hs.admin hs.lock hs.mem1
  · exact Step.aCreateMap _ 1 (max 1 s.st.now) () rfl
  · refine Step.bReadE _ 1 (max 1 s.st.now) bInit 0 (upd2_same _ _ _ _) rfl ?_
    intro k _
    show s.st.data k = none
    exact hs.data k
  · exact Step.bRead _ 1 (max 1 s.st.now) bRd 0 1 (upd2_same _ _ _ _) rfl rfl (by decide)
      (Nat.le_refl _)
  · refine Step.aDelete _ 1 ⟨max 1 s.st.now, (), false⟩ rfl rfl ?_
    show upd s.m.mem 1 (upd s.st.dfn 1 (some ⟨max 1 s.st.now, (), false⟩) 1) 1 = _
    rw [upd_same, upd_same]
  · exact Step.aDeleteMap _ 1 (max 1 s.st.now) rfl
  · exact Step.cScanEnd _ 1 (max 1 s.st.now) cInit (upd2_same _ _ _ _) rfl (fun k l => hs.ent 1 _ k l)
  · exact Step.cEnd _ 1 (max 1 s.st.now) { cInit with pc := .done } (upd2_same _ _ _ _) rfl

/-- The first state of the next round. -/
theorem round_ok {s : SysX} (hs : RoundOk s) : RoundOk (rAt s (max 1 s.st.now) 8) := by
  refine ⟨rfl, rfl, ?_, hs.wr, hs.ent, ?_, ?_, ?_, ?_, hs.data, ?_⟩
  · show upd (upd s.m.mem 1 (upd s.st.dfn 1 (some ⟨max 1 s.st.now, (), false⟩) 1)) 1 none 1 = none
    rw [upd_same]
  · show upd (upd s.st.dfn 1 (some ⟨max 1 s.st.now, (), false⟩)) 1 none 0 = _
    rw [upd_ne _ _ (by decide), upd_ne _ _ (by decide)]; exact hs.dfnA
  · intro n g b hb
    change upd2 (upd2 (upd2 s.m.bld 1 (max 1 s.st.now) (some bInit)) 1 (max 1 s.st.now) (some bRd))
      1 (max 1 s.st.now) (some (bCk (rReadE 1 (rMap 1 (rCreate 1 s) (max 1 s.st.now)) (max 1 s.st.now)))) n g = some b at hb
    by_cases h : n = 1 ∧ g = max 1 s.st.now
    · rw [h.1, h.2, upd2_same] at hb; cases hb; rfl
    · rw [upd2_ne _ _ h, upd2_ne _ _ h, upd2_ne _ _ h] at hb; exact hs.bldCheck n g b hb
  · show upd2 (upd2 (upd2 s.m.bld 1 (max 1 s.st.now) (some bInit)) 1 (max 1 s.st.now) (some bRd))
      1 (max 1 s.st.now) (some (bCk (rReadE 1 (rMap 1 (rCreate 1 s) (max 1 s.st.now)) (max 1 s.st.now)))) 0 1 ≠ none
    have h : ¬ ((0 : Nat) = 1 ∧ (1 : Nat) = max 1 s.st.now) := fun h => by cases h.1
    rw [upd2_ne _ _ h, upd2_ne _ _ h, upd2_ne _ _ h]; exact hs.bldA
  · intro n g
    show upd2 (upd2 (upd2 s.m.cln 1 (max 1 s.st.now) (some cInit)) 1 (max 1 s.st.now)
      (some { cInit with pc := .done })) 1 (max 1 s.st.now) none n g = none
    by_cases h : n = 1 ∧ g = max 1 s.st.now
    · rw [h.1, h.2, upd2_same]
    · rw [upd2_ne _ _ h, upd2_ne _ _ h, upd2_ne _ _ h]; exact hs.cln n g
  · show 1 ≤ s.st.now + 1 + 1 + 1; omega


/-- The run's start: A created (G = 1), its maps, its build's end key and its
first step's read; the build waits at its check. -/
def S0 : SysX := rRead 0 (rReadE 0 (rMap 0 (rCreate 0 (Sys.init (fun _ => none))) 1) 1) 1

theorem s0_reach : Reach exSpec S0 := by
  have r0 : Reach exSpec (Sys.init (F := Unit) (L := Nat) (W := Unit) (fun _ => none)) :=
    Reach.init _
  have r1 := Reach.step r0 (Step.aCreate _ 0 () rfl rfl rfl)
  have r2 := Reach.step r1 (Step.aCreateMap _ 0 1 () rfl)
  have r3 := Reach.step r2 (Step.bReadE _ 0 1 bInit 0 rfl rfl (fun k _ => rfl))
  have r4 := Reach.step r3
    (Step.bRead _ 0 1 bRd 0 1 rfl rfl rfl (by decide) (Nat.le_refl _))
  exact r4

theorem s0_ok : RoundOk S0 := by
  refine ⟨rfl, rfl, ?_, fun _ => rfl, fun _ _ _ _ h => h, ?_, ?_, ?_, ?_, fun _ => rfl, Nat.le_refl _⟩
  · rfl
  · rfl
  · intro n g b hb
    have hS : S0.m.bld n g = upd2 (upd2 (upd2 (fun _ _ => none) 0 1 (some bInit)) 0 1 (some bRd))
        0 1 (some (bCk (rReadE 0 (rMap 0 (rCreate 0 (Sys.init (fun _ => none))) 1) 1))) n g := rfl
    rw [hS] at hb
    by_cases h : n = 0 ∧ g = 1
    · rw [h.1, h.2, upd2_same] at hb; cases hb; rfl
    · rw [upd2_ne _ _ h, upd2_ne _ _ h, upd2_ne _ _ h] at hb
      cases hb
  · intro h; cases h
  · intro n g; rfl

/-- The first states of the rounds. -/
def Cr : Nat → SysX
  | 0 => S0
  | r + 1 => rAt (Cr r) (max 1 (Cr r).st.now) 8

theorem cr_ok : ∀ r, RoundOk (Cr r)
  | 0 => s0_ok
  | r + 1 => round_ok (cr_ok r)

/-- The run: round r's position p at time 8 r + p. -/
def sysX (k : Nat) : SysX := rAt (Cr (k / 8)) (max 1 (Cr (k / 8)).st.now) (k % 8)
def lblX (k : Nat) : Lbl Unit := rLbl (max 1 (Cr (k / 8)).st.now) (k % 8)

theorem runX_step (k : Nat) : Step exSpec (sysX k) (lblX k) (sysX (k + 1)) := by
  have hok := cr_ok (k / 8)
  by_cases h7 : k % 8 < 7
  · have h1 : (k + 1) / 8 = k / 8 := by omega
    have h2 : (k + 1) % 8 = k % 8 + 1 := by omega
    unfold sysX lblX
    rw [h1, h2]
    exact round_step hok (k % 8) (by omega)
  · have h1 : (k + 1) / 8 = k / 8 + 1 := by omega
    have h2 : (k + 1) % 8 = 0 := by omega
    have h3 : k % 8 = 7 := by omega
    unfold sysX lblX
    rw [h1, h2, h3]
    exact round_step hok 7 (by omega)

/-- The run of the counterexample. -/
def runX : Run exSpec Unit where
  sys := sysX
  lbl := lblX
  start := s0_reach
  step := runX_step

theorem sysX_round (r : Nat) : sysX (8 * r) = Cr r := by
  unfold sysX
  rw [show 8 * r / 8 = r by omega, show 8 * r % 8 = 0 by omega]
  rfl

theorem sysX_one (r : Nat) : sysX (8 * r + 1) = rCreate 1 (Cr r) := by
  unfold sysX
  rw [show (8 * r + 1) / 8 = r by omega, show (8 * r + 1) % 8 = 1 by omega]
  rfl

theorem wf_of_off {ρ : Run exSpec Unit} {l : Lbl Unit}
    (h : ∀ i, ∃ j, i ≤ j ∧ ¬ Enabled exSpec (ρ.sys j) l) : WeakFair ρ l := by
  intro i hall
  obtain ⟨j, hj, hn⟩ := h i
  exact absurd (hall j hj) hn

/-- At a round's first state, no definition change ends, no cleanup and no
writer can step. -/
theorem off_start {s : SysX} (hs : RoundOk s) :
    ¬ Enabled exSpec s .amap ∧ (∀ n g, ¬ Enabled exSpec s (.cln n g)) ∧
      ∀ w, ¬ Enabled exSpec s (.wr w) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨s', hst⟩
    cases hst with
    | aCreateMap _ _ _ ha => rw [hs.admin] at ha; cases ha
    | aDeleteMap _ _ ha => rw [hs.admin] at ha; cases ha
  · rintro n g ⟨s', hst⟩
    cases hst with
    | cScan _ _ c _ hc _ _ _ => rw [hs.cln] at hc; cases hc
    | cScanEnd _ _ c hc _ _ => rw [hs.cln] at hc; cases hc
    | cDel _ _ c hc _ => rw [hs.cln] at hc; cases hc
    | cEnd _ _ c hc _ => rw [hs.cln] at hc; cases hc
  · rintro w ⟨s', hst⟩
    cases hst with
    | wReadS _ _ _ _ _ _ _ hw _ => rw [hs.wr] at hw; cases hw
    | wCommit _ _ _ _ _ _ hw _ => rw [hs.wr] at hw; cases hw
    | wDrop _ hw => exact hw (hs.wr _)

/-- While B's creation holds the lock, no build can step: each waits at its
check, which needs the lock. -/
theorem off_one {s : SysX} (hs : RoundOk s) (n g : Nat) :
    ¬ Enabled exSpec (rCreate 1 s) (.bld n g) := by
  rintro ⟨s', hst⟩
  have hck : ∀ b, (rCreate 1 s).m.bld n g = some b → b.pc = .check := hs.bldCheck n g
  cases hst with
  | bReadE _ _ b _ hb hpc _ => rw [hck b hb] at hpc; cases hpc
  | bRead _ _ b _ _ hb hpc _ _ _ => rw [hck b hb] at hpc; cases hpc
  | bCheck _ _ b _ _ _ hl _ _ => rcases hl with hl | hl <;> cases hl
  | bCheckFail _ _ b _ _ hl _ => rcases hl with hl | hl <;> cases hl
  | bCommit _ _ b hb hpc _ _ => rw [hck b hb] at hpc; cases hpc
  | bRefused _ _ b hb hpc _ => rw [hck b hb] at hpc; cases hpc
  | bLock _ _ b hb hpc _ => rw [hck b hb] at hpc; cases hpc
  | bActivate _ _ b _ hb hpc _ _ _ => rw [hck b hb] at hpc; cases hpc
  | bActivateFail _ _ b hb hpc _ _ => rw [hck b hb] at hpc; cases hpc

theorem rAt_dfn0 (s : SysX) (g : Nat) : ∀ p, (rAt s g p).st.dfn 0 = s.st.dfn 0 := by
  have h01 : (0 : Nat) ≠ 1 := by decide
  have h1 : upd s.st.dfn 1 (some ⟨max 1 s.st.now, (), false⟩) 0 = s.st.dfn 0 := upd_ne _ _ h01
  have h2 : upd (upd s.st.dfn 1 (some ⟨max 1 s.st.now, (), false⟩)) 1 none 0 = s.st.dfn 0 := by
    rw [upd_ne _ _ h01, upd_ne _ _ h01]
  intro p
  match p with
  | 0 => rfl
  | 1 => exact h1
  | 2 => exact h1
  | 3 => exact h1
  | 4 => exact h1
  | 5 => exact h2
  | 6 => exact h2
  | 7 => exact h2
  | _ + 8 => exact h2

theorem rLbl_ok (g p : Nat) :
    rLbl g p ≠ .crash ∧ rLbl g p ≠ .bretry 0 1 ∧ rLbl g p ≠ .babort 0 1 := by
  unfold rLbl
  split <;> exact ⟨(fun h => by cases h), (fun h => by cases h), (fun h => by cases h)⟩

/-- **Weak fairness is not enough** with several names: a run in which every
thread is weakly fair, the lock is free in every round, there is no crash,
retry or abort, and finitely many keys and writers, yet A stays building for
ever. By `build_ends`, the run is not strongly fair for A's build: its check is
possible in every round, while the lock is free, and never taken. -/
theorem weak_fairness_not_enough :
    ∃ ρ : Run exSpec Unit,
      (∀ w, WeakFair ρ (.wr w)) ∧ WeakFair ρ .amap ∧ (∀ n g, WeakFair ρ (.bld n g)) ∧
      (∀ n g, WeakFair ρ (.cln n g)) ∧
      (∀ j, ρ.lbl j ≠ .crash ∧ ρ.lbl j ≠ .bretry 0 1 ∧ ρ.lbl j ≠ .babort 0 1) ∧
      (∀ j, ∃ j', j ≤ j' ∧ (ρ.sys j').m.lock = .free) ∧
      (∀ j, ∃ e, ∀ k, e < k → (ρ.sys j).st.data k = none) ∧
      (ρ.sys 0).m.bld 0 1 ≠ none ∧ (ρ.sys 0).m.admin.name ≠ some 0 ∧
      (∀ j, Building (ρ.sys j) 0 1) ∧ ¬ StrongFair ρ (.bld 0 1) := by
  have hstart : ∀ i, ∃ r, i ≤ 8 * r := fun i => ⟨i, by omega⟩
  have hwr : ∀ w, WeakFair runX (.wr w) := by
    intro w
    apply wf_of_off
    intro i
    refine ⟨8 * (i + 1), by omega, ?_⟩
    show ¬ Enabled exSpec (sysX (8 * (i + 1))) _
    rw [sysX_round]; exact (off_start (cr_ok _)).2.2 w
  have hamap : WeakFair runX .amap := by
    apply wf_of_off
    intro i
    refine ⟨8 * (i + 1), by omega, ?_⟩
    show ¬ Enabled exSpec (sysX (8 * (i + 1))) _
    rw [sysX_round]; exact (off_start (cr_ok _)).1
  have hbld : ∀ n g, WeakFair runX (.bld n g) := by
    intro n g
    apply wf_of_off
    intro i
    refine ⟨8 * (i + 1) + 1, by omega, ?_⟩
    show ¬ Enabled exSpec (sysX (8 * (i + 1) + 1)) _
    rw [sysX_one]; exact off_one (cr_ok _) n g
  have hcln : ∀ n g, WeakFair runX (.cln n g) := by
    intro n g
    apply wf_of_off
    intro i
    refine ⟨8 * (i + 1), by omega, ?_⟩
    show ¬ Enabled exSpec (sysX (8 * (i + 1))) _
    rw [sysX_round]; exact (off_start (cr_ok _)).2.1 n g
  have hlbl : ∀ j, runX.lbl j ≠ .crash ∧ runX.lbl j ≠ .bretry 0 1 ∧ runX.lbl j ≠ .babort 0 1 :=
    fun j => rLbl_ok _ _
  have hfree : ∀ j, ∃ j', j ≤ j' ∧ (runX.sys j').m.lock = .free := by
    intro j
    refine ⟨8 * j, by omega, ?_⟩
    show (sysX (8 * j)).m.lock = .free
    rw [sysX_round]; exact (cr_ok j).lock
  have hdata : ∀ j, ∃ e, ∀ k, e < k → (runX.sys j).st.data k = none := by
    intro j
    refine ⟨0, fun k _ => ?_⟩
    show (rAt (Cr (j / 8)) _ (j % 8)).st.data k = none
    have h : (rAt (Cr (j / 8)) (max 1 (Cr (j / 8)).st.now) (j % 8)).st.data =
        (Cr (j / 8)).st.data := by
      unfold rAt; split <;> rfl
    rw [h]; exact (cr_ok _).data k
  have hb0 : (runX.sys 0).m.bld 0 1 ≠ none := (cr_ok 0).bldA
  have ha0 : (runX.sys 0).m.admin.name ≠ some 0 := by
    show (Cr 0).m.admin.name ≠ some 0
    rw [(cr_ok 0).admin]; intro h; cases h
  have hbuild : ∀ j, Building (runX.sys j) 0 1 := by
    intro j
    refine ⟨⟨1, (), false⟩, ?_, rfl, rfl⟩
    show (rAt (Cr (j / 8)) _ (j % 8)).st.dfn 0 = _
    rw [rAt_dfn0]; exact (cr_ok _).dfnA
  refine ⟨runX, hwr, hamap, hbld, hcln, hlbl, hfree, hdata, hb0, ha0, hbuild, ?_⟩
  intro hsf
  obtain ⟨j, _, hnb⟩ := build_ends runX ⟨0, fun j _ => ⟨(hlbl j).1, (hlbl j).2.1⟩⟩
    (fun j => (hlbl j).2.2) hsf (fun j => by
      obtain ⟨j', hj', hl⟩ := hfree j
      exact ⟨j', hj', Or.inl hl⟩) hdata ⟨[()], fun w => by cases w; simp⟩ hb0 ha0
  exact hnb (hbuild j)

end BergDB.Index
