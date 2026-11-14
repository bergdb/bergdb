import SIS.Tree.GetFrame

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! OpGetOK's split rules (bergdb 024-12, TP10): the writer's steps of a time
split of a leaf that existed before the transaction, below an inner parent
with room, and the facts the reading needs of them: a key klong repointed by
an added klong, the descent's access path, the walk down a key's prefix with
its path. -/

theorem writerWP_and {α : Type} {f : M α} {c : Ctx} {w : W} {P Q : α → W → Prop}
    (hP : WriterWP f c w P) (hQ : WriterWP f c w Q) : WriterWP f c w (fun r v => P r v ∧ Q r v) :=
  fun r v h => ⟨hP r v h, hQ r v h⟩

/-! ## A key klong repointed by an added klong -/

theorem KNode.liveAt_of_times (n : KNode) (t : Time) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    n.liveAt t = n.live := by
  rw [KNode.liveAt_eq_live_prefix, prefixAt_of_times n.ks t (fun k hk s hs => by
    subst hs; exact ht s hk)]

theorem mem_iff_lookup (m : List (Nat × NodeId)) (hn : (m.map Prod.fst).Nodup) (c : Nat)
    (z : NodeId) : (c, z) ∈ m ↔ m.lookup c = some z :=
  ⟨fun h => lookup_some_of_mem hn h, fun h => lookup_some_mem h⟩

/-- A node with a key klong of an existing compare value k1 added: its search
at or below any target finds the same compare value, with the new pointer for
k1. -/
theorem KNode.add_key_searchLte (n : KNode) (t : Time) (k1 : Nat) (y : NodeId)
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hk1 : ∃ z, (k1, z) ∈ n.live) (c : Int) :
    ((n.add t (.key k1 y)).searchLte t c).map (fun f => (f.c, f.y)) =
      (n.searchLte t c).map (fun f => (f.c, if f.c = k1 then y else f.y)) := by
  have ht2 := KNode.add_times n t (.key k1 y) (fun s h => by cases h) ht
  have hL1 := KNode.liveAt_of_times n t ht
  have hL2 := KNode.liveAt_of_times _ t ht2
  have hlk : ∀ c', (n.add t (.key k1 y)).live.lookup c' =
      if k1 == c' then some y else n.live.lookup c' :=
    fun c' => KNode.add_key_live_lookup_of_wf n t k1 c' y hw
  have hnd1 := KNode.live_keys_nodup n
  have hnd2 := KNode.live_keys_nodup (n.add t (.key k1 y))
  have hmem2 : ∀ c' z, (c', z) ∈ (n.add t (.key k1 y)).live ↔
      if k1 = c' then z = y else (c', z) ∈ n.live := by
    intro c' z
    rw [mem_iff_lookup _ hnd2, hlk]
    by_cases h : k1 = c'
    · subst h; simp [eq_comm]
    · have : (k1 == c') = false := by simpa using h
      simp only [this, Bool.false_eq_true, ↓reduceIte, h]
      rw [mem_iff_lookup _ hnd1]
  -- the same compare values
  have hkeys : ∀ c', (∃ z, (c', z) ∈ (n.add t (.key k1 y)).live) ↔ ∃ z, (c', z) ∈ n.live := by
    intro c'
    by_cases h : k1 = c'
    · subst h
      constructor
      · intro _; exact hk1
      · intro _; exact ⟨y, (hmem2 k1 y).mpr (by simp)⟩
    · simp only [hmem2, h, ↓reduceIte]
  have hs1 := n.searchLte_spec t c
  have hs2 := (n.add t (.key k1 y)).searchLte_spec t c
  unfold NodeSearchSpec at hs1 hs2
  rw [hL1] at hs1
  rw [hL2] at hs2
  cases h1 : n.searchLte t c with
  | none =>
    have hall := hs1.2.mp h1
    have : (n.add t (.key k1 y)).searchLte t c = none := by
      apply hs2.2.mpr
      intro q hq
      obtain ⟨z, hz⟩ := (hkeys q.1).mp ⟨q.2, hq⟩
      exact hall (q.1, z) hz
    rw [this]; rfl
  | some f =>
    obtain ⟨hfm, hfa, hfmax⟩ := hs1.1 f h1
    cases h2 : (n.add t (.key k1 y)).searchLte t c with
    | none =>
      have hall := hs2.2.mp h2
      obtain ⟨z, hz⟩ := (hkeys f.c).mpr ⟨f.y, hfm⟩
      have := hall (f.c, z) hz
      rw [hfa] at this; cases this
    | some f' =>
      obtain ⟨hfm', hfa', hfmax'⟩ := hs2.1 f' h2
      obtain ⟨z, hz⟩ := (hkeys f.c).mpr ⟨f.y, hfm⟩
      have hle1 := hfmax' (f.c, z) hz hfa
      obtain ⟨z', hz'⟩ := (hkeys f'.c).mp ⟨f'.y, hfm'⟩
      have hle2 := hfmax (f'.c, z') hz' hfa'
      simp only [decide_eq_true_eq] at hle1 hle2
      have hc : f'.c = f.c := by omega
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      refine ⟨hc, ?_⟩
      have hy := (hmem2 f'.c f'.y).mp hfm'
      rw [hc] at hy
      by_cases hk : f.c = k1
      · subst hk; simp only [↓reduceIte] at hy ⊢; exact hy
      · have hk' : ¬ k1 = f.c := fun h => hk h.symm
        simp only [hk', ↓reduceIte] at hy
        simp only [hk, ↓reduceIte]
        exact Option.some.inj ((lookup_some_of_mem hnd1 hy).symm.trans (lookup_some_of_mem hnd1 hfm))

/-! ## A descent with its access path -/

/-- A klong added to a node with room: the node gets it, nothing else changes
but the cache of the node. -/
theorem writerWP_appendKlongs_room (d : Nat) (q : NodeId) (qn : KNode) (k1 y : Nat) (c : Ctx)
    (w : W) (hlk : w.nodes.lookup q = some qn) (hroom : qn.size + 1 + 1 ≤ c.p.M)
    (hdead : deadOver c.p (qn.add c.i (.key k1 y)) = false) :
    WriterWP (appendKlongs d q [(k1, y)]) c w (fun _ w' =>
      w' = { w with nodes := upsert w.nodes q (qn.add c.i (.key k1 y)) }) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  have h1 : ¬ (qn.size + [(k1, y)].length + 1 > c.p.M) := by simp; omega
  simp only [h1, decide_false, ↓reduceIte, List.foldl_cons, List.foldl_nil, hdead,
    Bool.false_eq_true]
  unfold addKeys
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known q qn c w hlk]
  simp only [putNode, List.foldl_cons, List.foldl_nil, writerWP_modify]

/-! ## The reading through generic readers, a leaf changed -/

theorem getFromR_leaf_change_seg (N1 N2 : NodeId → Option KNode) (V1 V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (L : NodeId) (pre : List Nat) (cv : Nat)
    (r rk : NodeId) (n n2 : KNode)
    (hN : ∀ x, x ≠ L → N1 x = N2 x)
    (hn : N1 L = some n) (hn2 : N2 L = some n2) (hl : n.leaf = true) (hl2 : n2.leaf = true)
    (hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (n2.searchEq i c').map (·.y))
    (hrk : segRootR N1 i fuel pre r = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N1 i cv fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true → (x, cv) ∈ fromVisits N1 i fuel key' r →
      (x, cv) ∈ eqVisits N1 i cv fuel rk → N1 x = some m → m.leaf = true → key' = pre ++ [cv])
    (hV : ∀ key' x c' m y, key' ≠ pre ++ [cv] → (x, c') ∈ fromVisits N1 i fuel key' r →
      N1 x = some m → m.leaf = true → (m.searchEq i c').map (·.y) = some y → V1 y = V2 y) :
    getFromR N2 V2 i fuel (pre ++ [cv]) r = ((n2.searchEq i cv).map (·.y)).bind V2 ∧
      ∀ key', keyWf key' = true → key' ≠ pre ++ [cv] →
        getFromR N2 V2 i fuel key' r = getFromR N1 V1 i fuel key' r := by
  have hsome : ∀ x, (N1 x).isSome = (N2 x).isSome := by
    intro x
    by_cases hx : x = L
    · subst hx; rw [hn, hn2]; rfl
    · rw [hN x hx]
  have hagree : ∀ (q : NodeId × Nat), q.2 ≠ cv → AgreeAt N1 N2 i q.1 q.2 := by
    intro q hq
    by_cases hx : q.1 = L
    · right
      exact ⟨n, n2, hx ▸ hn, hx ▸ hn2, hl, hl2, hs q.2 hq⟩
    · exact Or.inl (hN q.1 hx)
  constructor
  · rw [getFromR_append, ← segRootR_frame N1 N2 i fuel cv hsome pre r
      (fun q _ hq => hagree q hq) hcv, hrk]
    simp only [Option.bind_some, getFromR]
    rw [getEqR_change_leaf N1 N2 i cv L n2 hn2 hl2 fuel rk (fun q _ hq => hN q.1 hq) hvisL
      (fun n1 h1 => by rw [hn] at h1; cases h1; exact hl)]
  · intro key' hkey' hk
    symm
    apply getFromR_leaf_change N1 N2 V1 V2 i fuel hfuel L cv hN ⟨n, n2, hn, hn2, hl, hl2, hs⟩ key' r
    · intro hmem
      exact hk (huniq key' L n hkey' hmem hvisL hn hl)
    · intro x c' m y hx hm hml hsy
      exact hV key' x c' m y hk hx hm hml hsy

/-! ## Reachability through live klongs -/

/-- The nodes reachable from r at time t through klongs live then. -/
inductive ReachS (N : NodeId → Option KNode) (t : Time) (r : NodeId) : NodeId → Prop
  | root : ReachS N t r r
  | step (x : NodeId) (n : KNode) (c : Nat) (z : NodeId) :
      ReachS N t r x → N x = some n → (c, z) ∈ n.liveAt t → ReachS N t r z

theorem KNode.searchLte_mem (n : KNode) (t : Time) (c : Int) (fd : Found)
    (h : n.searchLte t c = some fd) : (fd.c, fd.y) ∈ n.liveAt t :=
  ((n.searchLte_spec t c).1 fd h).1

theorem KNode.searchEq_mem (n : KNode) (t : Time) (c : Nat) (fd : Found)
    (hw : klongsWf n.ks = true) (h : n.searchEq t c = some fd) : (c, fd.y) ∈ n.liveAt t := by
  have hs := searchEqSpec n t c hw
  rw [h] at hs
  exact lookup_some_mem hs.symm

/-! ## What a descent caches -/

theorem writerWP_getNode_cache2 (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun _ v => w.nodes.IsPrefix v.nodes ∧
      ∀ z, (v.nodes.lookup z).isSome = true →
        (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]
    exact ⟨List.prefix_refl _, fun z h => Or.inl h⟩
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hv
      split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨⟨_, rfl⟩, fun z hz => ?_⟩
        rw [List.lookup_append] at hz
        cases h : w.nodes.lookup z with
        | some _ => exact Or.inl rfl
        | none =>
          rw [h] at hz
          right
          by_cases hzx : z = x
          · subst hzx; rw [hv]; rfl
          · exfalso
            have : ([(x, ({ leaf := c.p.heightOf nd.level == 0, ks := klongsOf nd.hist } : KNode))].lookup z) = none := by
              show (match z == x with | true => _ | false => none) = none
              rw [show (z == x) = false by simpa using hzx]
            rw [this] at hz
            cases hz
    · exact writerWP_throw _ _ _ _

/-- A descent caches every node of the key's path that the state reads, and
caches only nodes it had or that the writer's view has. -/
theorem writerWP_descendLte_cache (cv : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (f : Nat) (x : NodeId) (w : W),
    (∀ q ∈ eqVisits (wNode c.p base w) c.i cv f x, w.taken.contains q.1 = false) →
    WriterWP (descendLte cv f x) c w (fun _ v =>
      (∀ q qn, (q, cv) ∈ eqVisits (wNode c.p base w) c.i cv f x →
        wNode c.p base w q = some qn → v.nodes.lookup q = some qn) ∧
      (∀ z, (v.nodes.lookup z).isSome = true →
        (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) ∧
      w.nodes.IsPrefix v.nodes) := by
  intro f
  induction f with
  | zero => intro x w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w ht
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_getNode_reads x c w base hvc)
      (writerWP_getNode_cache2 x c w)) ?_
    intro n v ⟨⟨hrv, hlk, hwn⟩, hpre, hsrc⟩
    have hx := hwn (ht (x, cv) (by simp [eqVisits]))
    split
    · rename_i hleaf
      simp only [writerWP_pure]
      refine ⟨?_, hsrc, hpre⟩
      intro q qn hq hqn
      simp only [eqVisits, hx, hleaf, ↓reduceIte, List.mem_cons, List.mem_nil_iff, or_false,
        Prod.mk.injEq] at hq
      rw [hq.1] at hqn ⊢
      rw [hx] at hqn
      cases hqn
      exact hlk
    · rename_i hleaf
      split
      · exact writerWP_throw _ _ _ _
      · rename_i fd hfd
        simp only [pathAdd, writerWP_bind, writerWP_modify]
        have hr01 : ReadsAs c.p base w { v with path := v.path ++ [(some fd.c, fd.y)] } :=
          ReadsAs.trans _ _ _ _ _ hrv ⟨by funext y; rfl, rfl, rfl, rfl, rfl⟩
        have hvis : ∀ q ∈ eqVisits (wNode c.p base { v with path := v.path ++ [(some fd.c, fd.y)] })
            c.i cv f fd.y,
            ({ v with path := v.path ++ [(some fd.c, fd.y)] } : W).taken.contains q.1 = false := by
          intro q hq
          rw [hr01.1] at hq
          rw [hr01.2.2.1]
          apply ht q
          simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
          exact Or.inr hq
        refine writerWP_mono (writerWP_and (ih fd.y _ hvis)
          (writerWP_descendLte_reads cv c base hvc f fd.y _ hvis)) ?_
        intro L v2 ⟨⟨hcache, hsrc2, hpre2⟩, ⟨hr2, _⟩⟩
        rw [hr01.1] at hcache
        refine ⟨?_, ?_, hpre.trans hpre2⟩
        · intro q qn hq hqn
          simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons,
            Prod.mk.injEq] at hq
          rcases hq with ⟨hqx, _⟩ | hq
          · subst hqx
            rw [hx] at hqn
            cases hqn
            exact hpre2.lookup_eq_some hlk
          · exact hcache q qn hq hqn
        · intro z hz
          rcases hsrc2 z hz with h | h
          · exact hsrc z h
          · exact Or.inr h

/-! ## Reachability of a key's path -/

theorem eqVisits_reach (N : NodeId → Option KNode) (t : Time) (r0 : NodeId) (cv : Nat) :
    ∀ (f : Nat) (x z : NodeId) (c : Nat), ReachS N t r0 x → (z, c) ∈ eqVisits N t cv f x →
      ReachS N t r0 z := by
  intro f
  induction f with
  | zero => intro x z c _ h; simp [eqVisits] at h
  | succ f ih =>
    intro x z c hx h
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, _⟩ | h
    · exact hx
    · cases hn : N x with
      | none => rw [hn] at h; cases h
      | some n =>
        rw [hn] at h
        simp only at h
        split at h
        · cases h
        · cases hf : n.searchLte t cv with
          | none => rw [hf] at h; cases h
          | some fd =>
            rw [hf] at h
            exact ih fd.y z c (ReachS.step x n fd.c fd.y hx hn (KNode.searchLte_mem n t cv fd hf)) h

theorem getEqR_reach (N : NodeId → Option KNode) (t : Time) (r0 : NodeId) (cv : Nat)
    (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true) :
    ∀ (f : Nat) (x y : NodeId), ReachS N t r0 x → getEqR N t cv f x = some y → ReachS N t r0 y := by
  intro f
  induction f with
  | zero => intro x y _ h; simp [getEqR] at h
  | succ f ih =>
    intro x y hx h
    simp only [getEqR] at h
    cases hn : N x with
    | none => rw [hn] at h; cases h
    | some n =>
      rw [hn] at h
      simp only at h
      split at h
      · cases hf : n.searchEq t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          exact ReachS.step x n cv fd.y hx hn (KNode.searchEq_mem n t cv fd (hwf x n hx hn) hf)
      · cases hf : n.searchLte t cv with
        | none => rw [hf] at h; cases h
        | some fd =>
          rw [hf] at h
          exact ih fd.y y (ReachS.step x n fd.c fd.y hx hn (KNode.searchLte_mem n t cv fd hf)) h

theorem segRootR_reach (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (r0 : NodeId)
    (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true) :
    ∀ (pre : List Nat) (r rk : NodeId), ReachS N t r0 r → segRootR N t fuel pre r = some rk →
      ReachS N t r0 rk := by
  intro pre
  induction pre with
  | nil => intro r rk hr h; simp only [segRootR, Option.some.injEq] at h; subst h; exact hr
  | cons c rest ih =>
    intro r rk hr h
    simp only [segRootR] at h
    cases hg : getEqR N t c fuel r with
    | none => rw [hg] at h; cases h
    | some y =>
      rw [hg] at h
      simp only at h
      split at h
      · exact ih y rk (getEqR_reach N t r0 c hwf fuel r y hr hg) h
      · cases h

/-! ## The reading after a time split -/

theorem fromVisits_reach (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (r0 : NodeId)
    (hwf : ∀ x xn, ReachS N t r0 x → N x = some xn → klongsWf xn.ks = true) :
    ∀ (key : List Nat) (r x : NodeId) (c : Nat), ReachS N t r0 r →
      (x, c) ∈ fromVisits N t fuel key r → ReachS N t r0 x := by
  intro key
  induction key with
  | nil => intro r x c _ h; simp [fromVisits] at h
  | cons cv rest ih =>
    intro r x c hr h
    cases rest with
    | nil => exact eqVisits_reach N t r0 cv fuel r x c hr (by simpa [fromVisits] using h)
    | cons d rest' =>
      simp only [fromVisits] at h
      rcases List.mem_append.mp h with h | h
      · exact eqVisits_reach N t r0 cv fuel r x c hr h
      · cases hg : getEqR N t cv fuel r with
        | none => rw [hg] at h; cases h
        | some y =>
          rw [hg] at h
          exact ih y x c (getEqR_reach N t r0 cv hwf fuel r y hr hg) h

end SIS.Tree
