/-
Proofs about reclaim, part 7 (bergdb item 001, WP R4): P up to the startup
pos, as startup reads it from a stream cut safely, agrees with the run's for
lookups from the first available time on.
-/
import SIS.Proof.CutTops

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Lists -/

/-- The lookup of y in the references to versions ws, when every version of y
in ws has record r. -/
theorem lookup_refs_rec {ws : List (Version V)} {y : NodeId} {r : Nat}
    (hex : ∃ w ∈ ws, w.node = y) (hall : ∀ w ∈ ws, w.node = y → w.recNo = r) :
    List.lookup y (ws.map (fun w => (w.node, w.recNo))) = some r := by
  induction ws with
  | nil => obtain ⟨w, hw, -⟩ := hex; simp at hw
  | cons a ws ih =>
    simp only [List.map_cons, List.lookup_cons]
    by_cases ha : a.node = y
    · have hb : (y == a.node) = true := by simp [ha]
      simp only [hb]
      rw [hall a List.mem_cons_self ha]
    · have hne : (y == a.node) = false := by simp; exact fun h => ha h.symm
      simp only [hne]
      apply ih
      · obtain ⟨w, hw, hwy⟩ := hex
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hwy ha
        · exact ⟨w, hw, hwy⟩
      · exact fun w hw hwy => hall w (List.mem_cons_of_mem a hw) hwy

/-- In a list sorted by time, the last entry is the latest. -/
theorem getLast_time_max {l : List (Entry V)} (hs : l.Pairwise (fun e e' => e.time < e'.time))
    {e : Entry V} (hl : l.getLast? = some e) {e' : Entry V} (he' : e' ∈ l) : e'.time ≤ e.time := by
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
  rw [hys] at hs he'
  rcases List.mem_append.mp he' with h | h
  · have := (List.pairwise_append.mp hs).2.2 _ h e (List.mem_singleton_self e)
    omega
  · rw [List.mem_singleton] at h; rw [h]; exact Nat.le_refl _

/-- In a list sorted by time, an entry at least as late as every entry is the
last. -/
theorem getLast_of_max {l : List (Entry V)} (hs : l.Pairwise (fun e e' => e.time < e'.time))
    {e : Entry V} (he : e ∈ l) (hmax : ∀ e' ∈ l, e'.time ≤ e.time) : l.getLast? = some e := by
  cases hl : l.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at he; simp at he
  | some e1 =>
    have h1 := getLast_time_max hs hl he
    have h2 := hmax e1 (List.mem_of_getLast? hl)
    exact congrArg some (sorted_time_eq hs (List.mem_of_getLast? hl) he (by omega))

/-- The last element of a list is the last of the filtered list, if the filter
keeps it. -/
theorem getLast?_filter_of {α : Type} {l : List α} {p : α → Bool} {a : α} (hl : l.getLast? = some a)
    (hp : p a = true) : (l.filter p).getLast? = some a := by
  obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp hl
  rw [List.filter_append]
  simp [hp]

/-- The last occurrence of x in the blocks B(0), ..., B(n) is the same for two
families of blocks that give the same last occurrence of x in every block from
m on, if x occurs in one of those. -/
theorem lookup_rev_flatMap_congr {β : Type} (Bc Bf : Nat → List (NodeId × β)) (x : NodeId) (m : Nat) :
    ∀ n, (∀ t, m ≤ t → t ≤ n → List.lookup x (Bc t).reverse = List.lookup x (Bf t).reverse) →
      (∃ t, m ≤ t ∧ t ≤ n ∧ (List.lookup x (Bf t).reverse).isSome) →
      List.lookup x (((List.range (n + 1)).flatMap Bc).reverse) =
        List.lookup x (((List.range (n + 1)).flatMap Bf).reverse) := by
  intro n
  induction n with
  | zero =>
    intro h hex
    obtain ⟨t, h1, h2, -⟩ := hex
    have ht : t = 0 := by omega
    subst ht
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact h 0 h1 (Nat.le_refl _)
  | succ n ih =>
    intro h hex
    rw [List.range_succ, List.flatMap_append, List.flatMap_append, List.reverse_append,
      List.reverse_append, List.lookup_append, List.lookup_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    obtain ⟨t, h1, h2, hsome⟩ := hex
    rw [h (n + 1) (by omega) (Nat.le_refl _)]
    cases hl : List.lookup x (Bf (n + 1)).reverse with
    | some u => rfl
    | none =>
      simp only [Option.none_or]
      have htn : t ≤ n := by
        rcases Nat.lt_or_ge t (n + 1) with ht | ht
        · omega
        · have : t = n + 1 := by omega
          subst this
          rw [hl] at hsome; simp at hsome
      exact ih (fun t' h1' h2' => h t' h1' (by omega)) ⟨t, h1, htn, hsome⟩

/-! ### Reading a cut stream -/

section CutRead

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- On a stream cut at or before s, a pointer leads to a version of its node in
the whole stream, or to the stub of one. -/
theorem follow_cut_spec {S : Stream V T} {c s : Nat} (hcs : c ≤ s) {y : NodeId} {ref : Option Nat}
    {w : Version V} (h : follow (cutStream c S) s true y ref = some w) :
    ∃ r w0, S.versionAt r y = some w0 ∧ (w = w0 ∨ w = w0.stub) := by
  unfold follow at h
  simp only [ite_true] at h
  rw [newest_cut hcs] at h
  cases hn : newest S s y with
  | some u =>
    rw [hn] at h
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨r, -, hr⟩ := newest_some hn
    exact ⟨r, u, hr, Or.inl rfl⟩
  | none =>
    rw [hn] at h
    simp only at h
    cases ref with
    | none => simp at h
    | some r =>
      simp only [Option.bind_some] at h
      rcases Nat.lt_or_ge r c with hr | hr
      · rw [versionAt_cut_lt hr] at h
        cases hw0 : S.versionAt r y with
        | none => rw [hw0] at h; simp at h
        | some w0 =>
          rw [hw0] at h
          simp only [Option.map_some, Option.some.injEq] at h
          exact ⟨r, w0, hw0, Or.inr h.symm⟩
      · rw [versionAt_cut_ge hr] at h
        exact ⟨r, w, h, Or.inl rfl⟩

/-- With a virtual root, no record has a version of the root. -/
theorem Inv.versionAt_root_none (hinv : Inv sp db k) (hv : sp.virt = true) (r : Nat) :
    db.S.versionAt r root = none := by
  cases h : db.S.versionAt r root with
  | none => rfl
  | some w =>
    exfalso
    have := hinv.written_of_versionAt h
    rw [written_root_false hv] at this
    simp at this

/-- With a virtual root, no pointer leads to a version of the root, before or
after a cut. -/
theorem Inv.follow_cut_root (hinv : Inv sp db k) (hv : sp.virt = true) {c s : Nat} (hcs : c ≤ s)
    (ref : Option Nat) : follow (cutStream c db.S) s true root ref = none := by
  cases h : follow (cutStream c db.S) s true root ref with
  | none => rfl
  | some w =>
    exfalso
    obtain ⟨r, w0, hr, -⟩ := follow_cut_spec hcs h
    rw [hinv.versionAt_root_none hv r] at hr
    simp at hr

/-- Reading a stream where no pointer leads to a version of the root: only the
first version's pair can have the root as its node. -/
theorem readFrom_root_pair (sp : Spec V T) {S : Stream V T} {s : Nat} {t : Time}
    (hS : ∀ ref, follow S s true root ref = none) :
    ∀ (b : Nat) (v : Version V), v.level < b →
      ∀ p ∈ readFrom sp S s true t v, p.1 = root → p = (v.node, v) := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb p hp hpr
    rw [readFrom_eq] at hp
    rcases List.mem_cons.mp hp with h | hp
    · exact h
    · exfalso
      obtain ⟨y, -, hp⟩ := List.mem_flatMap.mp hp
      cases hw : follow S s true y (v.ref? y) with
      | none => rw [hw] at hp; simp at hp
      | some w =>
        rw [hw] at hp
        simp only at hp
        split at hp
        · have hpw := ih w (by omega) p hp hpr
          obtain ⟨hwy, -⟩ := follow_spec hw
          have hy0 : y ≠ root := by
            intro hy0; subst hy0; rw [hS] at hw; simp at hw
          rw [hpw] at hpr
          exact hy0 (by rw [← hwy]; exact hpr)
        · simp at hp

/-- Reading the stream cut at or before s, at a time up to s, from a version
whose node is in Ps (P after T(s)) and whose entries up to s point to nodes of
Ps, gives only nodes of Ps. -/
theorem Inv.readFrom_cut_ids (hinv : Inv sp db k) (hls : LiveSub sp) {Ps : Struct V} {s : Nat}
    (hg : Grow Ps s db.P) (hpt : PtrsOK sp Ps)
    (htimes : ∀ x n, Ps.get? x = some n → ∀ e ∈ n.hist, e.time ≤ s)
    {c : Nat} (hcs : c ≤ s) {t : Time} (hts : t ≤ s) :
    ∀ (b : Nat) (v : Version V), v.level < b → (Ps.get? v.node).isSome →
      (∀ e ∈ v.hist, e.time ≤ s → ∀ y ∈ sp.ptrs e.val, (Ps.get? y).isSome) →
      ∀ p ∈ readFrom sp (cutStream c db.S) s true t v, (Ps.get? p.1).isSome := by
  intro b
  induction b with
  | zero => intro v h; omega
  | succ b ih =>
    intro v hb hvn hve p hp
    rw [readFrom_eq] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hvn
    · obtain ⟨y, hy, hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨e, he, hye⟩ := hls _ _ hy
      have hyP : (Ps.get? y).isSome :=
        hve e (mem_upTo.mp he).1 (Nat.le_trans (mem_upTo.mp he).2 hts) y hye
      cases hw : follow (cutStream c db.S) s true y (v.ref? y) with
      | none => rw [hw] at hp; simp at hp
      | some w =>
        rw [hw] at hp
        simp only at hp
        split at hp
        · obtain ⟨r, w0, hw0, hww⟩ := follow_cut_spec hcs hw
          obtain ⟨hw0y, -, m, hm, hmh, -, -⟩ := hinv.version_node hw0
          have hwn : w.node = y := by rcases hww with rfl | rfl <;> exact hw0y
          apply ih w (by omega) (by rw [hwn]; exact hyP) _ p hp
          intro e' he' he's y' hy'
          rcases hww with rfl | rfl
          · -- A version of y: its entries up to s are y's in Ps.
            obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp hyP
            obtain ⟨n', hn', -, -, hup⟩ := hg y ny hny
            rw [hm, Option.some.injEq] at hn'
            subst hn'
            have he'n : e' ∈ ny.hist := by
              rw [← upTo_of_forall ny.hist s (htimes y ny hny), ← hup]
              rw [hmh] at he'
              exact mem_upTo.mpr ⟨(mem_upTo.mp he').1, he's⟩
            obtain ⟨m', hm', -⟩ := hpt y ny hny e' he'n y' hy'
            rw [hm']; rfl
          · simp [Version.stub] at he'
        · simp at hp

/-- The version that top(k) names is the same after a safe cut. -/
theorem topVersion_cut {c : Nat} (hcut : CutOK sp c db k) (hcs : c ≤ lastSp db.S) :
    topVersion (cutStream c db.S) (lastSp db.S) true = topVersion db.S (lastSp db.S) true := by
  unfold topVersion
  have hlast : (cutStream c db.S).getLast?.bind (·.top) = db.S.getLast?.bind (·.top) := by
    rw [getLast?_cut]
    cases db.S.getLast? with
    | none => rfl
    | some R => simp only [Option.map_some, Option.bind_some]; split <;> rfl
  rw [hlast]
  cases hR : db.S.getLast? with
  | none => rfl
  | some R =>
    simp only [Option.bind_some]
    cases htop : R.top with
    | none => rfl
    | some p =>
      obtain ⟨z, r⟩ := p
      simp only
      exact follow_cut hcs z _ (fun _ r' hr' _ => by
        cases hr'; exact hcut.2.2.2 R z r hR htop)

/-- With a virtual root: the root children read at startup are latest versions
of root children created up to s, and include every such root child. -/
theorem Inv.topsRead_spec (hinv : Inv sp db k) (hv : sp.virt = true) :
    (∀ w ∈ topsRead sp db.S (lastSp db.S) true, TopRead sp db w) ∧
    (∀ y m c, TopAt sp db.P y m c → c ≤ lastSp db.S →
      ∃ w ∈ topsRead sp db.S (lastSp db.S) true, w.node = y) := by
  have hvi := hinv.vr hv
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  rcases hinv.topVersion_virt hv h0 with ⟨hnil, htv⟩ | ⟨zs, ms, cs, us, hzt, hcs, hmax, hus, htv⟩
  · have hws : topsRead sp db.S (lastSp db.S) true = [] := by unfold topsRead; rw [htv]
    rw [hws]
    refine ⟨by simp, ?_⟩
    intro y m c hyt hc
    have : (⟨c, sp.rootVal y⟩ : Entry V) ∈ n0.hist.upTo (lastSp db.S) :=
      mem_upTo.mpr ⟨hvi.topEntry y m c hyt n0 h0, hc⟩
    rw [hnil] at this; simp at this
  · obtain ⟨husn, -⟩ := hinv.version_node (hinv.lv_at hus)
    have hread : TopRead sp db us := ⟨ms, cs, by rw [husn]; exact hzt, hcs, by rw [husn]; exact hus⟩
    have hws : topsRead sp db.S (lastSp db.S) true = readTops sp db.S (lastSp db.S) true us := by
      unfold topsRead; rw [htv]
    rw [hws]
    refine ⟨hinv.readTops_read hv (us.level + 1) us (by omega) hread, ?_⟩
    intro y m c hyt hc
    rcases Nat.lt_or_ge c cs with hlt | hge
    · have hy := hvi.closed zs ms cs y m c hzt hyt hlt
      rw [← husn] at hzt hy
      exact hinv.readTops_all hv (ms.level + 1) us ms cs (by omega) hzt hcs (by rw [husn]; exact hus) y hy
    · have hc' : c = cs := Nat.le_antisymm (hmax y m c hyt hc) hge
      subst hc'
      have := hinv.topAt_unique hv hyt hzt
      subst this
      exact ⟨us, by rw [readTops_eq]; exact List.mem_cons_self, husn⟩

/-- With a virtual root: every root child read from a stream cut safely is read
from the whole stream too, or is the stub of one read there. -/
theorem topsRead_cut {c : Nat} (hcut : CutOK sp c db k) (hcs : c ≤ lastSp db.S) :
    ∀ w' ∈ topsRead sp (cutStream c db.S) (lastSp db.S) true,
      ∃ w ∈ topsRead sp db.S (lastSp db.S) true, w' = w ∨ w' = w.stub := by
  intro w' hw'
  unfold topsRead at hw' ⊢
  rw [topVersion_cut hcut hcs] at hw'
  cases htv : topVersion db.S (lastSp db.S) true with
  | none => rw [htv] at hw'; simp at hw'
  | some v =>
    rw [htv] at hw'
    simp only at hw' ⊢
    rcases readTops_cut_sub sp db.S hcs (v.level + 1) v (by omega) w' hw' with h | ⟨w, hw, rfl⟩
    · exact ⟨w', h, Or.inl rfl⟩
    · exact ⟨w, hw, Or.inr rfl⟩

end CutRead

/-! ### With a virtual root -/

/-- With a virtual root, at the first available time f: the creation time of
the root's live child at f, 0 if there is none. Root children created at it or
later are the root's live children at some time from f on. -/
def rootC0 (n0 : Node V) (f : Time) : Time :=
  ((n0.hist.upTo f).getLast?.map (·.time)).getD 0

/-- The entries that startup's root rebuilt from root children ws keeps: those
at the times of root children read with entries. -/
def cutKeep (ws : List (Version V)) (e : Entry V) : Bool :=
  ws.any (fun w => w.hist.any (fun e' => e'.time == e.time))

/-- The history of the root that startup rebuilds holds root entries. -/
theorem rootVersion_vals (sp : Spec V T) (s : Nat) (ws : List (Version V)) :
    ∀ e ∈ (rootVersion sp s ws).hist, ∃ z, e.val = sp.rootVal z := by
  intro e he
  simp only [rootVersion, List.mem_filterMap, List.mem_range] at he
  obtain ⟨t, -, hf⟩ := he
  obtain ⟨w, -, hw⟩ := Option.map_eq_some_iff.mp hf
  exact ⟨w.node, by rw [← hw]⟩

section VCut

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- With a virtual root: the root's live child at time t is the root child of
its last entry up to t, and it is reachable at t. -/
theorem Inv.rootLast (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp) {n0 : Node V}
    (h0 : db.P.get? root = some n0) {t : Time} {e : Entry V} (hl : (n0.hist.upTo t).getLast? = some e) :
    ∃ z m, TopAt sp db.P z m e.time ∧ e.val = sp.rootVal z ∧ e ∈ n0.hist ∧ e.time ≤ t ∧
      sp.live (n0.hist.upTo t) = [z] ∧ reachable sp db.P t z = true := by
  have hvi := hinv.vr hv
  have he := List.mem_of_getLast? hl
  obtain ⟨he1, he2⟩ := mem_upTo.mp he
  obtain ⟨z, m, hzt, hval⟩ := hvi.rootEntry n0 h0 e he1
  have hlive : sp.live (n0.hist.upTo t) = [z] := by
    rw [hvl hv _ (fun e' he' => by
      obtain ⟨z', m', -, hval'⟩ := hvi.rootEntry n0 h0 e' (mem_upTo.mp he').1
      exact ⟨z', hval'⟩), hl]
    simp [hval, hvi.rootPtrs]
  obtain ⟨my, hmy, hlt⟩ := hinv.ptrs root n0 h0 e he1 z (by rw [hval, hvi.rootPtrs]; simp)
  refine ⟨z, m, hzt, hval, he1, he2, hlive, ?_⟩
  exact (reachable_iff _ _ _ _).mpr (Reach.child (Reach.root n0 h0) h0 (by rw [hlive]; simp) hmy hlt)

/-- With a virtual root: up to the time a root child was created, the root's
last entry is that root child's. -/
theorem Inv.rootLast_at (hinv : Inv sp db k) (hv : sp.virt = true) {n0 : Node V}
    (h0 : db.P.get? root = some n0) {y : NodeId} {m : Node V} {cy : Time} (hyt : TopAt sp db.P y m cy) :
    (n0.hist.upTo cy).getLast? = some ⟨cy, sp.rootVal y⟩ := by
  have hvi := hinv.vr hv
  apply getLast_of_max ((hvi.rootSorted n0 h0).filter _)
  · exact mem_upTo.mpr ⟨hvi.topEntry y m cy hyt n0 h0, Nat.le_refl _⟩
  · intro e' he'; exact (mem_upTo.mp he').2

/-- With a virtual root: a root child created at `rootC0` or later is the root's
live child, so reachable, at f or at the time it was created. -/
theorem Inv.top_reach_from (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp)
    {n0 : Node V} (h0 : db.P.get? root = some n0) {f : Time} {y : NodeId} {m : Node V} {cy : Time}
    (hyt : TopAt sp db.P y m cy) (hC0 : rootC0 n0 f ≤ cy) :
    ∃ t, f ≤ t ∧ t ≤ max f cy ∧ reachable sp db.P t y = true := by
  have hvi := hinv.vr hv
  rcases Nat.lt_or_ge cy f with hlt | hge
  · have hmem : (⟨cy, sp.rootVal y⟩ : Entry V) ∈ n0.hist.upTo f :=
      mem_upTo.mpr ⟨hvi.topEntry y m cy hyt n0 h0, show cy ≤ f by omega⟩
    cases hl : (n0.hist.upTo f).getLast? with
    | none => rw [List.getLast?_eq_none_iff] at hl; rw [hl] at hmem; simp at hmem
    | some e =>
      have hle : cy ≤ e.time := getLast_time_max ((hvi.rootSorted n0 h0).filter _) hl hmem
      have hC : rootC0 n0 f = e.time := by simp [rootC0, hl]
      obtain ⟨z, mz, hzt, -, -, -, -, hr⟩ := hinv.rootLast hv hvl h0 hl
      have hcy : cy = e.time := by omega
      rw [hcy] at hyt
      have := hinv.topAt_unique hv hyt hzt
      rw [this]
      exact ⟨f, Nat.le_refl _, Nat.le_max_left _ _, hr⟩
  · obtain ⟨z, mz, hzt, -, -, -, -, hr⟩ := hinv.rootLast hv hvl h0 (hinv.rootLast_at hv h0 hyt)
    have := hinv.topAt_unique hv hyt hzt
    rw [this]
    exact ⟨cy, hge, Nat.le_max_right _ _, hr⟩

/-- With a virtual root: the root's live child at a time from f on was created at
`rootC0` or later. -/
theorem Inv.rootC0_le (hinv : Inv sp db k) (hv : sp.virt = true) {n0 : Node V}
    (h0 : db.P.get? root = some n0) {f t : Time} (hft : f ≤ t) {e : Entry V}
    (hl : (n0.hist.upTo t).getLast? = some e) : rootC0 n0 f ≤ e.time := by
  have hvi := hinv.vr hv
  cases hl0 : (n0.hist.upTo f).getLast? with
  | none => simp [rootC0, hl0]
  | some e0 =>
    have : rootC0 n0 f = e0.time := by simp [rootC0, hl0]
    rw [this]
    have he0 := List.mem_of_getLast? hl0
    exact getLast_time_max ((hvi.rootSorted n0 h0).filter _) hl
      (mem_upTo.mpr ⟨(mem_upTo.mp he0).1, Nat.le_trans (mem_upTo.mp he0).2 hft⟩)

/-- With a virtual root: after a safe cut, startup's read of the root children
from the cut stream reads, at its latest version, every root child created up
to s at `rootC0` or later. -/
theorem Inv.topsRead_cut_all (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp)
    {c : Nat} (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) {n0 : Node V}
    (h0 : db.P.get? root = some n0) :
    ∀ y my cy, TopAt sp db.P y my cy → rootC0 n0 (lastFa db.S) ≤ cy → cy ≤ lastSp db.S →
      ∃ w' ∈ topsRead sp (cutStream c db.S) (lastSp db.S) true, w'.node = y ∧ db.S.lv y = some w' := by
  have hvi := hinv.vr hv
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 hfs
  -- The root children from C0 on have their latest versions at the cut or later.
  have hC : ∀ y m cy u, TopAt sp db.P y m cy → rootC0 n0 (lastFa db.S) ≤ cy → cy ≤ lastSp db.S →
      db.S.lv y = some u → c ≤ u.recNo := by
    intro y m cy u hyt hC0 hcy hu
    obtain ⟨t, h1, h2, hr⟩ := hinv.top_reach_from hv hvl h0 hyt hC0
    have h3 : max (lastFa db.S) cy ≤ lastSp db.S := Nat.max_le.mpr ⟨hfs, hcy⟩
    exact hcut.2.1 t u h1 (by omega) (ReadsAt.latest y u hr hu)
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

/-- With a virtual root: the root that startup rebuilds from a stream cut safely
has the root's entries up to s at the times of the root children it reads with
entries. -/
theorem Inv.cutRoot_hist (hinv : Inv sp db k) (hv : sp.virt = true) {c : Nat} (hcut : CutOK sp c db k)
    (hcs : c ≤ lastSp db.S) {n0 : Node V} (h0 : db.P.get? root = some n0) :
    (rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)).hist =
      (n0.hist.upTo (lastSp db.S)).filter (cutKeep (topsRead sp (cutStream c db.S) (lastSp db.S) true)) := by
  have hvi := hinv.vr hv
  have hspec := hinv.topsRead_spec hv
  have hcut' := topsRead_cut hcut hcs
  generalize topsRead sp (cutStream c db.S) (lastSp db.S) true = ws' at hcut' ⊢
  -- A root child read with an entry at t was created at t.
  have hent : ∀ w ∈ ws', ∀ t, w.hist.any (fun e => e.time == t) = true →
      ∃ m, TopAt sp db.P w.node m t := by
    intro w hw t ht
    obtain ⟨w0, hw0, hww⟩ := hcut' w hw
    rcases hww with rfl | rfl
    · obtain ⟨m, c0, hzt, -, hlv⟩ := hspec.1 w hw0
      have hwh := hvi.topVers w.node m c0 hzt w.recNo w (hinv.lv_at hlv)
      obtain ⟨e, he, het⟩ := List.any_eq_true.mp ht
      rw [hwh] at he
      have : c0 = t := by rw [← hzt.time_of_mem he]; simpa using het
      rw [this] at hzt
      exact ⟨m, hzt⟩
    · simp [Version.stub] at ht
  rw [upTo_eq_filterMap (hvi.rootSorted n0 h0), List.filter_filterMap]
  unfold rootVersion
  simp only
  apply filterMap_congr_mem
  intro t _
  by_cases hex : ∃ z m, TopAt sp db.P z m t
  · obtain ⟨z, m, hzt⟩ := hex
    have hR : n0.hist.find? (fun e => e.time == t) = some ⟨t, sp.rootVal z⟩ :=
      (find?_time_eq_some (hvi.rootSorted n0 h0) t _).mpr ⟨hvi.topEntry z m t hzt n0 h0, rfl⟩
    rw [hR, Option.filter_some]
    cases hf : ws'.find? (fun w => w.hist.any (fun e => e.time == t)) with
    | none =>
      have hk : cutKeep ws' ⟨t, sp.rootVal z⟩ = false := by
        unfold cutKeep
        rw [List.any_eq_false]
        intro w hw hwt
        exact (List.find?_eq_none.mp hf) w hw hwt
      simp [hk]
    | some w0 =>
      have hw0 := List.mem_of_find?_eq_some hf
      have hw0t := List.find?_some hf
      obtain ⟨m0, hzt0⟩ := hent w0 hw0 t hw0t
      have := hinv.topAt_unique hv hzt0 hzt
      have hk : cutKeep ws' ⟨t, sp.rootVal z⟩ = true := List.any_eq_true.mpr ⟨w0, hw0, hw0t⟩
      simp [hk, this]
  · have hR : n0.hist.find? (fun e => e.time == t) = none := by
      rw [List.find?_eq_none]
      intro e he het
      obtain ⟨z, m, hzt, -⟩ := hvi.rootEntry n0 h0 e he
      have : e.time = t := by simpa using het
      rw [this] at hzt
      exact hex ⟨z, m, hzt⟩
    rw [hR]
    have hL : ws'.find? (fun w => w.hist.any (fun e => e.time == t)) = none := by
      rw [List.find?_eq_none]
      intro w hw hwt
      obtain ⟨m0, hzt0⟩ := hent w hw t hwt
      exact hex ⟨w.node, m0, hzt0⟩
    rw [hL]
    rfl

/-- With a virtual root: after a safe cut, the root that startup rebuilds from
the cut stream keeps every root entry from `rootC0` on, up to s. -/
theorem Inv.cutKeep_late (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp) {c : Nat}
    (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) {n0 : Node V}
    (h0 : db.P.get? root = some n0) {e : Entry V} (he : e ∈ n0.hist)
    (hC0 : rootC0 n0 (lastFa db.S) ≤ e.time) (hes : e.time ≤ lastSp db.S) :
    cutKeep (topsRead sp (cutStream c db.S) (lastSp db.S) true) e = true := by
  have hvi := hinv.vr hv
  obtain ⟨y, my, hyt, -⟩ := hvi.rootEntry n0 h0 e he
  obtain ⟨w', hw', -, hlv⟩ := hinv.topsRead_cut_all hv hvl hcut hfs h0 y my e.time hyt hC0 hes
  have hwh := hvi.topVers y my e.time hyt w'.recNo w' (hinv.lv_at hlv)
  obtain ⟨e', he', he't⟩ := hyt.exists_entry
  unfold cutKeep
  exact List.any_eq_true.mpr ⟨w', hw', List.any_eq_true.mpr ⟨e', by rw [hwh]; exact he', by simp [he't]⟩⟩

/-- With a virtual root: after a safe cut, the root that startup rebuilds from
the cut stream has the root's last entry at every time from f to s. -/
theorem Inv.cutRoot_last (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp) {c : Nat}
    (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) {n0 : Node V}
    (h0 : db.P.get? root = some n0) {t : Time} (hft : lastFa db.S ≤ t) (hts : t ≤ lastSp db.S) :
    ((rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)).hist.upTo t).getLast? =
      (n0.hist.upTo t).getLast? := by
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 hfs
  have hlate := fun (e : Entry V) (he : e ∈ n0.hist) hC0 hes => hinv.cutKeep_late hv hvl hcut hfs h0 he hC0 hes
  rw [hinv.cutRoot_hist hv hcut hcs h0]
  generalize topsRead sp (cutStream c db.S) (lastSp db.S) true = ws' at hlate ⊢
  have hfilt : History.upTo ((n0.hist.upTo (lastSp db.S)).filter (cutKeep ws')) t =
      (n0.hist.upTo t).filter (cutKeep ws') := by
    simp only [History.upTo, List.filter_filter]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.time ≤ t
    · have : e.time ≤ lastSp db.S := Nat.le_trans h1 hts
      simp [h1, this]
    · simp [h1]
  rw [hfilt]
  cases hl : (n0.hist.upTo t).getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl ⊢; rw [hl]; rfl
  | some e =>
    apply getLast?_filter_of hl
    have he := List.mem_of_getLast? hl
    exact hlate e (mem_upTo.mp he).1 (hinv.rootC0_le hv h0 hft hl) (Nat.le_trans (mem_upTo.mp he).2 hts)

/-- With a virtual root: after a safe cut, the root that startup rebuilds from
the cut stream has the root's live children at every time from f to s. -/
theorem Inv.cutRoot_live (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp) {c : Nat}
    (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S) {n0 : Node V}
    (h0 : db.P.get? root = some n0) {t : Time} (hft : lastFa db.S ≤ t) (hts : t ≤ lastSp db.S) :
    sp.live ((rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)).hist.upTo t) =
      sp.live (n0.hist.upTo t) := by
  have hvi := hinv.vr hv
  have hrootE : ∀ e ∈ n0.hist.upTo t, ∃ z, e.val = sp.rootVal z := fun e he => by
    obtain ⟨z, m, -, hval⟩ := hvi.rootEntry n0 h0 e (mem_upTo.mp he).1; exact ⟨z, hval⟩
  have hrootE' : ∀ e ∈ (rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)).hist.upTo t,
      ∃ z, e.val = sp.rootVal z := fun e he => rootVersion_vals sp _ _ e (mem_upTo.mp he).1
  rw [hvl hv _ hrootE', hvl hv _ hrootE, hinv.cutRoot_last hv hvl hcut hfs h0 hft hts]

/-- With a virtual root: after a safe cut, startup's read of the cut stream at
a time from f to s is its read of the whole stream, but for the root's version:
the root rebuilt from the root children read from the cut stream. -/
theorem Inv.readAt_cut_v (hinv : Inv sp db k) (hv : sp.virt = true) (hvl : VirtLiveOK sp)
    {c : Nat} (hcut : CutOK sp c db k) (hfs : lastFa db.S ≤ lastSp db.S)
    {t : Time} (hft : lastFa db.S ≤ t) (hts : t ≤ lastSp db.S) :
    readAt sp (cutStream c db.S) (lastSp db.S) true t =
        (root, rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)) ::
          (readAt sp db.S (lastSp db.S) true t).tail ∧
      readAt sp db.S (lastSp db.S) true t =
        (root, rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)) ::
          (readAt sp db.S (lastSp db.S) true t).tail := by
  have hvi := hinv.vr hv
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hcs : c ≤ lastSp db.S := Nat.le_trans hcut.1 hfs
  obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hspec := hinv.topsRead_spec hv
  have hvh : (rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)).hist =
      n0.hist.upTo (lastSp db.S) := hinv.rootHist_virt hv h0 _ hspec.1 hspec.2
  have hrootE : ∀ e ∈ n0.hist.upTo t, ∃ z, e.val = sp.rootVal z := fun e he => by
    obtain ⟨z, m, -, hval⟩ := hvi.rootEntry n0 h0 e (mem_upTo.mp he).1; exact ⟨z, hval⟩
  have hlive : sp.live ((rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)).hist.upTo t) =
      sp.live (n0.hist.upTo t) := by
    rw [hvh, upTo_upTo _ hts]
  have hlive' := hinv.cutRoot_live hv hvl hcut hfs h0 hft hts
  have hread : readAt sp db.S (lastSp db.S) true t =
      readFrom sp db.S (lastSp db.S) true t (rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)) := by
    unfold readAt startVersion; simp only [hv, ↓reduceIte]
  have hread' : readAt sp (cutStream c db.S) (lastSp db.S) true t =
      readFrom sp (cutStream c db.S) (lastSp db.S) true t
        (rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)) := by
    unfold readAt startVersion; simp only [hv, ↓reduceIte]
  rw [hread, hread', readFrom_eq, readFrom_eq]
  refine ⟨?_, rfl⟩
  simp only [List.tail_cons]
  congr 1
  rw [hlive', hlive]
  apply flatMap_congr_mem
  intro y hy
  cases hl : (n0.hist.upTo t).getLast? with
  | none =>
    exfalso
    rw [hvl hv _ hrootE, hl] at hy
    simp at hy
  | some e =>
    obtain ⟨z, m, hzt, -, -, het, hlz, hr⟩ := hinv.rootLast hv hvl h0 hl
    rw [hlz, List.mem_singleton] at hy
    rw [hy]
    obtain ⟨u, hu⟩ := hinv.topAt_lv hzt (by omega)
    have hcu : c ≤ u.recNo := hcut.2.1 t u hft (by omega) (ReadsAt.latest _ u hr hu)
    have href : (rootVersion sp (lastSp db.S) (topsRead sp db.S (lastSp db.S) true)).ref? z = some u.recNo := by
      unfold Version.ref?; simp only [rootVersion]
      apply lookup_refs (hspec.2 z m e.time hzt (by omega))
      intro w hw hwz
      obtain ⟨-, -, -, -, hlvw⟩ := hspec.1 w hw
      rw [hwz, hu] at hlvw
      exact (Option.some.inj hlvw).symm
    have href' : (rootVersion sp (lastSp db.S) (topsRead sp (cutStream c db.S) (lastSp db.S) true)).ref? z =
        some u.recNo := by
      unfold Version.ref?; simp only [rootVersion]
      obtain ⟨w', hw', hw'z, -⟩ := hinv.topsRead_cut_all hv hvl hcut hfs h0 z m e.time hzt
        (hinv.rootC0_le hv h0 hft hl) (by omega)
      apply lookup_refs_rec ⟨w', hw', hw'z⟩
      intro w hw hwz
      obtain ⟨w0, hw0, hww⟩ := topsRead_cut hcut hcs w hw
      obtain ⟨-, -, -, -, hlv0⟩ := hspec.1 w0 hw0
      have hw0z : w0.node = z := by rcases hww with rfl | rfl <;> exact hwz
      rw [hw0z, hu] at hlv0
      have hw0u : w0 = u := (Option.some.inj hlv0).symm
      rcases hww with rfl | rfl
      · rw [hw0u]
      · rw [stub_recNo, hw0u]
    have hfu := hinv.follow_lv hu
    have hfu' : follow (cutStream c db.S) (lastSp db.S) true z (some u.recNo) = some u := by
      rw [follow_cut hcs z _ (fun _ r hr _ => by cases hr; exact hcu), hfu]
    rw [href, href', hfu, hfu']
    simp only
    rw [hinv.readFrom_cut hcut hft hts (ReadsAt.latest z u hr hu)]
    rfl

end VCut

end SIS
