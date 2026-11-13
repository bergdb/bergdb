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

/-- The descent's access path: unchanged when it starts at the leaf; else its
last entry names the leaf L by the klong k1 that the node q before it in the
path finds for cv. -/
def DescentPath (p : Params) (base : View BVal) (t : Time) (w : W) (cv : Nat) (x L : NodeId)
    (path : List (Option Nat × NodeId)) (fuel : Nat) : Prop :=
  (L = x ∧ path = w.path) ∨
  ∃ pre q k1 qn fd, path = w.path ++ pre ++ [(some k1, L)] ∧
    (w.path ++ pre).getLast?.map (·.2) = some q ∧ wNode p base w q = some qn ∧
    qn.leaf = false ∧ qn.searchLte t cv = some fd ∧ fd.c = k1 ∧ fd.y = L ∧
    (q, cv) ∈ eqVisits (wNode p base w) t cv fuel x

theorem writerWP_descendLte_path (cv : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (f : Nat) (x : NodeId) (w : W),
    (∀ q ∈ eqVisits (wNode c.p base w) c.i cv f x, w.taken.contains q.1 = false) →
    w.path.getLast?.map (·.2) = some x →
    WriterWP (descendLte cv f x) c w (fun L v => ReadsAs c.p base w v ∧
      ∃ n, wNode c.p base w L = some n ∧ n.leaf = true ∧ v.nodes.lookup L = some n ∧
        (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv f x ∧
        getEqR (wNode c.p base w) c.i cv f x = (n.searchEq c.i cv).map (·.y) ∧
        DescentPath c.p base c.i w cv x L v.path f) := by
  intro f
  induction f with
  | zero => intro x w _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w ht hpath
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_getNode_reads x c w base hvc)
      (writerWP_getNode_cache x c w)) ?_
    intro n v ⟨⟨hrv, hlk, hwn⟩, ⟨_, _, hvpath⟩⟩
    have hx := hwn (ht (x, cv) (by simp [eqVisits]))
    split
    · rename_i hleaf
      simp only [writerWP_pure]
      refine ⟨hrv, n, hx, hleaf, hlk, by simp [eqVisits], ?_, Or.inl ⟨rfl, hvpath⟩⟩
      simp [getEqR, hx, hleaf]
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
        refine writerWP_mono (ih fd.y _ hvis (by simp)) ?_
        intro L v2 ⟨hr2, m, hm, hml, hlk2, hvisL, hget, hdp⟩
        rw [hr01.1] at hm hvisL hget
        refine ⟨ReadsAs.trans _ _ _ _ _ hr01 hr2, m, hm, hml, hlk2, ?_, ?_, ?_⟩
        · simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
          exact Or.inr hvisL
        · simp only [getEqR, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd]
          exact hget
        · right
          rcases hdp with ⟨hL, hp2⟩ | ⟨pre, q, k1, qn, fd', hp2, hlast, hq, hql, hqs, hc, hy, hqv⟩
          · subst hL
            refine ⟨[], x, fd.c, n, fd, ?_, ?_, hx, by simpa using hleaf, hfd, rfl, rfl,
              by simp [eqVisits]⟩
            · rw [hp2, hvpath]; simp
            · simpa using hpath
          · rw [hr01.1] at hq hqv
            refine ⟨(some fd.c, fd.y) :: pre, q, k1, qn, fd', ?_, ?_, hq, hql, hqs, hc, hy, ?_⟩
            · rw [hp2, hvpath]; simp
            · rw [← hlast, hvpath]; simp
            · simp only [eqVisits, hx, hleaf, Bool.false_eq_true, ↓reduceIte, hfd, List.mem_cons]
              exact Or.inr hqv

theorem writerWP_putSegs_prefix_path (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (cv : Nat) (post : Bool → W → Prop) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W),
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      w.path.getLast?.map (·.2) = some r →
      (∀ w', ReadsAs c.p base w w' → w'.path.getLast?.map (·.2) = some rk →
        WriterWP (setValue rk cv key value) c w' post) →
      WriterWP (putSegs key value (pre ++ [cv]) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w _ hrk hp hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append, putSegs.eq_2]
    exact hcont w (ReadsAs.refl _ _ _) hp
  | cons s rest ih =>
    intro r rk w ht hrk hp hcont
    have hne : rest ++ [cv] ≠ [] := by simp
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ [cv]) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · rename_i hysome
        obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
          cases h' : rest ++ [cv] with
          | nil => exact absurd h' hne
          | cons d rest' => exact ⟨d, rest', rfl⟩
        have hvis : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (s :: d :: rest') r,
            w.taken.contains q.1 = false := by
          intro q hq; apply ht q; rw [List.cons_append, he]; exact hq
        simp only [fromVisits] at hvis
        have ht1 : ∀ q ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r,
            w.taken.contains q.1 = false := fun q hq => hvis q (List.mem_append_left _ hq)
        unfold setNode
        wpSimplify
        refine writerWP_mono (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1) ?_
        intro L w3 ⟨hr3, n, hn, hnl, hlk3, _, hget⟩
        rw [writerWP_getNode_known L n c _ hlk3]
        rw [hg] at hget
        cases hfd : n.searchEq c.i s with
        | none => rw [hfd] at hget; cases hget
        | some fd =>
          rw [hfd] at hget
          simp only [Option.map_some, Option.some.injEq] at hget
          simp only [pathAdd, writerWP_bind, writerWP_modify, writerWP_pure]
          rw [← hget]
          generalize hw4 : ({ w3 with path := w3.path ++ [(some fd.c, y)] } : W) = w4
          have hr04 : ReadsAs c.p base w w4 := by
            subst hw4
            exact ReadsAs.trans _ _ _ _ _ hr3 ⟨rfl, rfl, rfl, rfl, rfl⟩
          refine ih y rk w4 ?_ ?_ (by subst hw4; simp) ?_
          · intro q hq
            rw [hr04.2.2.1]
            rw [hr04.1] at hq
            apply hvis q
            apply List.mem_append_right
            rw [hg]
            simp only
            rw [← he]
            exact hq
          · rw [hr04.1]; exact hrk
          · intro w' hr' hp'
            exact hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') hp'
      · cases hrk

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

/-- The state after a time split of a leaf L below an inner parent q with
room: a new node y (the next id) holds the last version with the klong, q's
klong k1 names y, L keeps only its klongs before the transaction. -/
def TimeSplitAfter (c : Ctx) (w w' : W) (L q : NodeId) (n qn : KNode) (k1 cv v : Nat) : Prop :=
  ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
    (∀ q', l.live.lookup q' = if cv == q' then some v else n.live.lookup q') ∧
    w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧
    ∀ x, w'.nodes.lookup x =
      if x = L then some (n.toPrev (c.i - 1))
      else if x = q then some (qn.add c.i (.key k1 w.next))
      else if x = w.next then some ⟨n.leaf, l.ks⟩
      else w.nodes.lookup x

theorem writerWP_handleFullWith_timeSplit (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hsplit : (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) L [(cv, v)]
      (n.lastVersion c.i) compact) c w
      (fun _ w' => TimeSplitAfter c w w' L q n qn k1 cv v) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  refine writerWP_ghOf_cached L n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew]
  unfold parentAt pathNode
  simp only [writerWP_bind, writerWP_get]
  cases hp : w.path[d']? with
  | none => rw [hp] at hpq; cases hpq
  | some e =>
    rw [hp] at hpq
    simp only [Option.map_some, Option.some.injEq] at hpq
    simp only [writerWP_pure]
    rw [hpq]
    simp only [writerWP_bind]
    rw [writerWP_getNode_known q qn c w hlq]
    have hsz : decide ((n.lastVersion c.i).size > c.p.splitAbove) = false := by
      simp only [decide_eq_false_iff_not, gt_iff_lt, Nat.not_lt]; exact hsplit
    simp only [writerWP_pure, hql, hsz, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    have hfinal : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true →
        (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
        (∀ q', l.live.lookup q' = [(cv, v)].foldl (pairLookupStep q') (n.live.lookup q')) →
        ∀ w2 : W, w2.taken = w.taken → w2.top = w.top → w2.vals = w.vals →
        w2.nodes = upsert (w.nodes ++ [(w.next, { leaf := n.leaf, ks := l.ks })]) q
          (qn.add c.i (.key k1 w.next)) →
        WriterWP (do let n ← getNode L; putNode L (n.toPrev (c.i - 1))) c w2
          (fun _ w' => TimeSplitAfter c w w' L q n qn k1 cv v) := by
      intro l hl_leaf hl_wf hl_times hl_look w2 h2t h2top h2v h2n
      have hlk2 : w2.nodes.lookup L = some n := by
        rw [h2n, lookup_upsert, if_neg (fun h => hqL h.symm), List.lookup_append, hlk]
        rfl
      simp only [writerWP_bind]
      rw [writerWP_getNode_known L n c w2 hlk2]
      simp only [putNode, writerWP_modify]
      refine ⟨l, hl_leaf, hl_wf, hl_times, ?_, h2t, h2top, h2v, ?_⟩
      · intro q'
        rw [hl_look q']
        simp [pairLookupStep]
      · intro x
        simp only
        rw [lookup_upsert, h2n, lookup_upsert]
        by_cases hxL : x = L
        · simp [hxL]
        · simp only [hxL, ↓reduceIte]
          by_cases hxq : x = q
          · simp [hxq]
          · simp only [hxq, ↓reduceIte, List.lookup_append]
            by_cases hxy : x = w.next
            · subst hxy; rw [hny]; simp [List.lookup]
            · simp only [hxy, ↓reduceIte]
              cases h : w.nodes.lookup x with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup x) = none
                rw [lookup_cons_ne _ _ _ _ hxy]; rfl
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_last n [(cv, v)] c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          refine writerWP_mono (writerWP_appendKlongs_room d' q qn k1 w.next c _
            (by simp [List.lookup_append, hlq]) hroomq (hdeadq _)) ?_
          intro _ w2 hw2
          subst hw2
          exact hfinal l hl_leaf hl_wf hl_times hl_look _ rfl rfl rfl rfl

theorem writerWP_appendKlongs_timeSplit (d' : Nat) (L q : NodeId) (n qn : KNode)
    (k1 cv v : Nat) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup L = some n) (hlq : w.nodes.lookup q = some qn)
    (hqL : q ≠ L) (hql : qn.leaf = false) (hfirst : n.firstTime ≠ some c.i)
    (hfull : ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv v)) = false))
    (hsplit : (n.lastVersion c.i).size ≤ c.p.splitAbove)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, L))
    (hroomq : qn.size + 1 + 1 ≤ c.p.M) (hdeadq : ∀ y, deadOver c.p (qn.add c.i (.key k1 y)) = false)
    (hny : w.nodes.lookup w.next = none) :
    WriterWP (appendKlongs (d' + 1) L [(cv, v)]) c w
      (fun _ w' => TimeSplitAfter c w w' L q n qn k1 cv v) := by
  rw [appendKlongs_step_dead]
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known L n c w hlk]
  have hts := fun compact => writerWP_handleFullWith_timeSplit d' L q n qn k1 cv v compact c w hlk
    hlq hqL hql hfirst hsplit hpq hpk hroomq hdeadq hny
  split
  · exact hts false
  · rename_i hsize
    have hlt : n.size + 1 < c.p.M := by simp at hsize; omega
    have hd : deadOver c.p (n.add c.i (.key cv v)) = true := by
      cases h : deadOver c.p (n.add c.i (.key cv v)) with
      | true => rfl
      | false => exact absurd ⟨hlt, h⟩ hfull
    simp only [List.foldl_cons, List.foldl_nil, hd, ↓reduceIte]
    exact hts true

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

/-- The time split's move as a renaming: in the reader before it, with the
leaf L already holding its new content m, L is renamed to the new node y, and
q's klong k1, the one klong that names L, names y. -/
theorem renSim_timeSplit (N M2 : NodeId → Option KNode) (t : Time) (r L q y : NodeId)
    (qn m : KNode) (k1 : Nat)
    (hqL : q ≠ L) (hyL : y ≠ L) (hyq : y ≠ q)
    (hNL : N L = some m) (hNq : N q = some qn) (hql : qn.leaf = false)
    (hqwf : klongsWf qn.ks = true) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ t)
    (hk1 : (k1, L) ∈ qn.live) (honly : ∀ c z, (c, z) ∈ qn.liveAt t → z = L → c = k1)
    (hM2y : M2 y = some m) (hM2q : M2 q = some (qn.add t (.key k1 y)))
    (hM2 : ∀ x, x ≠ L → x ≠ q → x ≠ y → M2 x = N x)
    (hwf : ∀ x xn, ReachS N t r x → N x = some xn → klongsWf xn.ks = true)
    (hnotL : ∀ x xn, ReachS N t r x → x ≠ q → N x = some xn → ∀ c z, (c, z) ∈ xn.liveAt t → z ≠ L)
    (hnoty : ∀ x xn, ReachS N t r x → N x = some xn → ∀ c z, (c, z) ∈ xn.liveAt t → z ≠ y) :
    RenSim N M2 t (fun x => x ≠ y ∧ ReachS N t r x) L y := by
  -- the targets of a reachable node's searches, renamed
  have hclos : ∀ x xn, ReachS N t r x → N x = some xn → ∀ c z, (c, z) ∈ xn.liveAt t →
      z ≠ y ∧ ReachS N t r z :=
    fun x xn hx hn c z hz => ⟨hnoty x xn hx hn c z hz, ReachS.step x xn c z hx hn hz⟩
  have hsame : ∀ x xn, ReachS N t r x → x ≠ q → N x = some xn → ∀ c,
      (xn.leaf = true → ((xn.searchEq t c).map (·.y)).map (fun z => if z = L then y else z) =
          (xn.searchEq t c).map (·.y) ∧
          ∀ fd, xn.searchEq t c = some fd → fd.y ≠ y ∧ ReachS N t r fd.y) ∧
      (xn.leaf = false → ((xn.searchLte t c).map (·.y)).map (fun z => if z = L then y else z) =
          (xn.searchLte t c).map (·.y) ∧
          ∀ fd, xn.searchLte t c = some fd → fd.y ≠ y ∧ ReachS N t r fd.y) := by
    intro x xn hx hxq hn c
    have hw := hwf x xn hx hn
    constructor
    · intro _
      refine ⟨?_, fun fd hfd => hclos x xn hx hn c fd.y (KNode.searchEq_mem xn t c fd hw hfd)⟩
      cases hfd : xn.searchEq t c with
      | none => rfl
      | some fd =>
        have := hnotL x xn hx hxq hn c fd.y (KNode.searchEq_mem xn t c fd hw hfd)
        simp [this]
    · intro _
      refine ⟨?_, fun fd hfd => hclos x xn hx hn fd.c fd.y (KNode.searchLte_mem xn t c fd hfd)⟩
      cases hfd : xn.searchLte t c with
      | none => rfl
      | some fd =>
        have := hnotL x xn hx hxq hn fd.c fd.y (KNode.searchLte_mem xn t c fd hfd)
        simp [this]
  intro x ⟨hxy, hx⟩
  by_cases hxL : x = L
  · subst hxL
    simp only [↓reduceIte]
    rw [hNL, hM2y]
    refine ⟨rfl, ?_⟩
    intro n1 n2 h1 h2
    cases h1; cases h2
    refine ⟨rfl, fun c => ?_⟩
    have := hsame x m hx (fun h => hqL h.symm) hNL c
    exact ⟨fun hl => (this.1 hl), fun hl => (this.2 hl)⟩
  · simp only [hxL, ↓reduceIte]
    by_cases hxq : x = q
    · subst hxq
      rw [hNq, hM2q]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      have e1 : n1 = qn := (Option.some.inj h1).symm
      have e2 : n2 = qn.add t (.key k1 y) := (Option.some.inj h2).symm
      subst e1 e2
      have hleaf : (n1.add t (.key k1 y)).leaf = n1.leaf := KNode.add_leaf _ _ _
      refine ⟨hleaf.symm, fun c => ⟨fun hl => absurd (hql ▸ hl) (by simp), fun _ => ?_⟩⟩
      have hL1 := KNode.liveAt_of_times n1 t hqt
      have hadd := KNode.add_key_searchLte n1 t k1 y hqwf hqt ⟨L, hk1⟩ c
      refine ⟨?_, fun fd hfd => hclos x n1 hx hNq fd.c fd.y (KNode.searchLte_mem n1 t c fd hfd)⟩
      cases hfd : n1.searchLte t c with
      | none =>
        rw [hfd] at hadd
        cases h2 : (n1.add t (.key k1 y)).searchLte t c with
        | none => rfl
        | some f2 => rw [h2] at hadd; cases hadd
      | some fd =>
        rw [hfd] at hadd
        cases h2 : (n1.add t (.key k1 y)).searchLte t c with
        | none => rw [h2] at hadd; cases hadd
        | some f2 =>
          rw [h2] at hadd
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hadd
          simp only [Option.map_some, Option.some.injEq]
          rw [hadd.2]
          have hmem := KNode.searchLte_mem n1 t c fd hfd
          by_cases hc : fd.c = k1
          · have hy : fd.y = L := by
              rw [hL1] at hmem
              rw [hc] at hmem
              exact Option.some.inj ((lookup_some_of_mem (KNode.live_keys_nodup n1) hmem).symm.trans
                (lookup_some_of_mem (KNode.live_keys_nodup n1) hk1))
            simp [hc, hy]
          · have hy : fd.y ≠ L := fun h => hc (honly fd.c fd.y hmem h)
            simp [hc, hy]
    · rw [hM2 x hxL hxq hxy]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      rw [h1] at h2
      cases h2
      refine ⟨rfl, fun c => ?_⟩
      have := hsame x n1 hx hxq h1 c
      exact ⟨fun hl => this.1 hl, fun hl => this.2 hl⟩

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

/-- Reaching through a reader changed at one node L to a node m whose live
klongs are L's and one more, naming v: what is reached is reached before, or
is v. -/
theorem reach_change (N : NodeId → Option KNode) (t : Time) (r0 L v : NodeId) (n m : KNode)
    (hNL : N L = some n) (hm : ∀ c z, (c, z) ∈ m.liveAt t → (c, z) ∈ n.liveAt t ∨ z = v)
    (hv : N v = none) (hvL : v ≠ L) :
    ∀ x, ReachS (fun x => if x = L then some m else N x) t r0 x → ReachS N t r0 x ∨ x = v := by
  intro x hx
  induction hx with
  | root => exact Or.inl ReachS.root
  | step x xn c z _ hn hz ih =>
    rcases ih with ih | ih
    · by_cases hxL : x = L
      · subst hxL
        simp only [↓reduceIte, Option.some.injEq] at hn
        subst hn
        rcases hm c z hz with h | h
        · exact Or.inl (ReachS.step x n c z ih hNL h)
        · exact Or.inr h
      · simp only [hxL, ↓reduceIte] at hn
        exact Or.inl (ReachS.step x xn c z ih hn hz)
    · subst ih
      simp only [hvL, ↓reduceIte, hv] at hn
      cases hn

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

/-- After a time split of the leaf L of a key's last segment (its content m,
L's klongs and the put's klong to the new value v, at the new node y; q's klong
k1, the one klong that named L, now names y), every key reads what it read but
the key, which reads the put's value. -/
theorem getFromR_timeSplit (N N2 : NodeId → Option KNode) (V V2 : NodeId → Option Nat)
    (i : Time) (fuel : Nat) (hfuel : 1 ≤ fuel) (root L q y v : NodeId) (n qn m : KNode)
    (k1 : Nat) (pre : List Nat) (cv h : Nat) (rk : NodeId)
    (hNL : N L = some n) (hnl : n.leaf = true) (hnwf : klongsWf n.ks = true)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ i)
    (hNq : N q = some qn) (hql : qn.leaf = false) (hqwf : klongsWf qn.ks = true)
    (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ i) (hk1 : (k1, L) ∈ qn.live)
    (hml : m.leaf = true) (hmwf : klongsWf m.ks = true) (hmt : ∀ s, Klong.time s ∈ m.ks → s ≤ i)
    (hmlook : ∀ c, m.live.lookup c = if cv == c then some v else n.live.lookup c)
    (hN2y : N2 y = some m) (hN2q : N2 q = some (qn.add i (.key k1 y)))
    (hN2 : ∀ x, x ≠ L → x ≠ q → x ≠ y → N2 x = N x)
    (hV2v : V2 v = some h) (hV2 : ∀ a, a ≠ v → V2 a = V a) (hV2L : V2 L = none)
    (hV2y : V2 y = none)
    (hqL : q ≠ L) (hyL : y ≠ L) (hyq : y ≠ q) (hvL : v ≠ L) (hvy : v ≠ y) (hNv : N v = none)
    (hrootL : root ≠ L) (hrooty : root ≠ y) (hrq : ReachS N i root q)
    (hrk : segRootR N i fuel pre root = some rk) (hcv : cv ∉ pre)
    (hvisL : (L, cv) ∈ eqVisits N i cv fuel rk)
    (huniq : ∀ key' x m', keyWf key' = true → (x, cv) ∈ fromVisits N i fuel key' root →
      (x, cv) ∈ eqVisits N i cv fuel rk → N x = some m' → m'.leaf = true → key' = pre ++ [cv])
    (hwf : ∀ x xn, ReachS N i root x → N x = some xn → klongsWf xn.ks = true)
    (htree : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      ∀ x' xn' c', ReachS N i root x' → N x' = some xn' → (c', z) ∈ xn'.liveAt i →
        x = x' ∧ c = c')
    (hfr : ∀ x xn c z, ReachS N i root x → N x = some xn → (c, z) ∈ xn.liveAt i →
      z ≠ v ∧ z ≠ y) :
    ∀ key', keyWf key' = true → getFromR N2 V2 i fuel key' root =
      if pre ++ [cv] == key' then some h else getFromR N V i fuel key' root := by
  let Nm : NodeId → Option KNode := fun x => if x = L then some m else N x
  have hNmL : Nm L = some m := by simp [Nm]
  have hNmq : Nm q = some qn := by simp [Nm, hqL, hNq]
  have hNm : ∀ x, x ≠ L → Nm x = N x := fun x hx => by simp [Nm, hx]
  have hL1 := KNode.liveAt_of_times n i hnt
  have hLm := KNode.liveAt_of_times m i hmt
  have hmem : ∀ c z, (c, z) ∈ m.liveAt i → (c, z) ∈ n.liveAt i ∨ z = v := by
    intro c z hz
    rw [hLm] at hz
    have := lookup_some_of_mem (KNode.live_keys_nodup m) hz
    rw [hmlook] at this
    by_cases hc : cv = c
    · subst hc
      rw [beq_self_eq_true] at this
      simp only [↓reduceIte, Option.some.injEq] at this
      exact Or.inr this.symm
    · have hc' : (cv == c) = false := by simpa using hc
      rw [hc'] at this
      simp only [Bool.false_eq_true, ↓reduceIte] at this
      left; rw [hL1]; exact lookup_some_mem this
  have hreach := reach_change N i root L v n m hNL hmem hNv hvL
  have hrL : ReachS N i root L := ReachS.step q qn k1 L hrq hNq (by
    rw [KNode.liveAt_of_times qn i hqt]; exact hk1)
  -- the facts the renaming needs, through Nm
  have hwfm : ∀ x xn, ReachS Nm i root x → Nm x = some xn → klongsWf xn.ks = true := by
    intro x xn hx hn
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn; exact hmwf
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hwf x xn hx' hn
      · subst hxv; rw [hNv] at hn; cases hn
  have hnotL : ∀ x xn, ReachS Nm i root x → x ≠ q → Nm x = some xn →
      ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ L := by
    intro x xn hx hxq hn c z hz hzL
    subst hzL
    have hqk : (k1, z) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
    by_cases hxL : x = z
    · subst hxL
      rw [hNmL] at hn; cases hn
      rcases hmem c x hz with h1 | h1
      · exact hxq (htree x n c x hrL hNL h1 q qn k1 hrq hNq hqk).1
      · exact hvL h1.symm
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact hxq (htree x xn c z hx' hn hz q qn k1 hrq hNq hqk).1
      · subst hxv; rw [hNv] at hn; cases hn
  have hnoty : ∀ x xn, ReachS Nm i root x → Nm x = some xn → ∀ c z, (c, z) ∈ xn.liveAt i → z ≠ y := by
    intro x xn hx hn c z hz
    by_cases hxL : x = L
    · subst hxL; rw [hNmL] at hn; cases hn
      rcases hmem c z hz with h1 | h1
      · exact (hfr x n c z hrL hNL h1).2
      · rw [h1]; exact hvy
    · rw [hNm x hxL] at hn
      rcases hreach x hx with hx' | hxv
      · exact (hfr x xn c z hx' hn hz).2
      · subst hxv; rw [hNv] at hn; cases hn
  have honly : ∀ c z, (c, z) ∈ qn.liveAt i → z = L → c = k1 := by
    intro c z hz hzL
    subst hzL
    have hqk : (k1, z) ∈ qn.liveAt i := by rw [KNode.liveAt_of_times qn i hqt]; exact hk1
    exact (htree q qn c z hrq hNq hz q qn k1 hrq hNq hqk).2
  have hS := renSim_timeSplit Nm N2 i root L q y qn m k1 hqL hyL hyq hNmL hNmq hql hqwf hqt hk1
    honly hN2y hN2q (fun x h1 h2 h3 => by rw [hN2 x h1 h2 h3, hNm x h1]) hwfm hnotL hnoty
  have hren : ∀ key', getFromR Nm V2 i fuel key' root = getFromR N2 V2 i fuel key' root := by
    intro key'
    have := getFromR_ren Nm N2 V2 V2 i fuel _ L y hS (fun a => by
      by_cases ha : a = L
      · subst ha; simp [hV2L, hV2y]
      · simp [ha]) key' root ⟨hrooty, ReachS.root⟩
    rw [this]
    simp [hrootL]
  have hs : ∀ c', c' ≠ cv → (n.searchEq i c').map (·.y) = (m.searchEq i c').map (·.y) := by
    intro c' hc'
    rw [KNode.searchEq_live n i hnwf hnt, KNode.searchEq_live m i hmwf hmt, hmlook]
    have : (cv == c') = false := by
      cases hb : (cv == c') with
      | false => rfl
      | true => exact absurd (beq_iff_eq.mp hb).symm hc'
    rw [this]; rfl
  have hA := getFromR_leaf_change_seg N Nm V V2 i fuel hfuel L pre cv root rk n m
    (fun x hx => (hNm x hx).symm) hNL hNmL hnl hml hs hrk hcv hvisL huniq
    (fun key' x c' m' y' _ hx hm' hml' hs' => by
      have hrx : ReachS N i root x := fromVisits_reach N i fuel root hwf key' root x c' ReachS.root hx
      have hy' : y' ≠ v := by
        cases hfd : m'.searchEq i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact (hfr x m' c' fd.y hrx hm' (KNode.searchEq_mem m' i c' fd (hwf x m' hrx hm') hfd)).1
      exact (hV2 y' hy').symm)
  intro key' hkey'
  rw [← hren]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [hA.1, KNode.searchEq_live m i hmwf hmt, hmlook]
    simp [hV2v]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)

end SIS.Tree
