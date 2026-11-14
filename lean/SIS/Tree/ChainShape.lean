import SIS.Tree.WriterTreeChainSteps
import SIS.Tree.TimeSplitMap
import SIS.Tree.GetReachBack
import SIS.Tree.GetCascadeChain
import SIS.Tree.DeadCountBasic

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The klongs of the nodes that a cascade of splits makes or changes (bergdb
024-12, for prover putinv's take-back (C)). -/

/-- A node of time t's klongs: a time klong of t, then key klongs; a key klong
followed by one of its compare value (shadowed) names a node that P allows. -/
def ShadowOK (t : Time) (zn : KNode) (P : NodeId → Prop) : Prop :=
  (∃ ks', zn.ks = Klong.time t :: ks' ∧ ∀ k ∈ ks', ∃ cv y, k = Klong.key cv y) ∧
  ∀ (a b cv : Nat) (y y' : NodeId), a < b → zn.ks[a]? = some (Klong.key cv y) →
    zn.ks[b]? = some (Klong.key cv y') → P y

theorem ShadowOK.mono {t : Time} {zn : KNode} {P Q : NodeId → Prop} (h : ShadowOK t zn P)
    (hPQ : ∀ y, P y → Q y) : ShadowOK t zn Q :=
  ⟨h.1, fun a b cv y y' hab ha hb => hPQ y (h.2 a b cv y y' hab ha hb)⟩

/-- The key klongs of pairs. -/
def keyKs (l : List (Nat × NodeId)) : List Klong := l.map (fun q => .key q.1 q.2)

theorem nodup_fst_idx (l : List (Nat × NodeId)) (hl : (l.map Prod.fst).Nodup) (a b : Nat)
    (cv : Nat) (y y' : NodeId) (ha : l[a]? = some (cv, y)) (hb : l[b]? = some (cv, y')) : a = b := by
  have ha' : (l.map Prod.fst)[a]? = some cv := by rw [List.getElem?_map, ha]; rfl
  have hb' : (l.map Prod.fst)[b]? = some cv := by rw [List.getElem?_map, hb]; rfl
  have hla : a < (l.map Prod.fst).length := (List.getElem?_eq_some_iff.mp ha').1
  have hlb : b < (l.map Prod.fst).length := (List.getElem?_eq_some_iff.mp hb').1
  have e1 := (List.getElem?_eq_some_iff.mp ha').2
  have e2 := (List.getElem?_eq_some_iff.mp hb').2
  exact (List.Nodup.getElem_inj hl).mp (e1.trans e2.symm)

theorem keyKs_getElem? (l : List (Nat × NodeId)) (a : Nat) (cv : Nat) (y : NodeId)
    (h : (keyKs l)[a]? = some (.key cv y)) : l[a]? = some (cv, y) := by
  unfold keyKs at h
  rw [List.getElem?_map] at h
  cases hl : l[a]? with
  | none => rw [hl] at h; cases h
  | some q =>
    rw [hl] at h
    simp only [Option.map_some, Option.some.injEq, Klong.key.injEq] at h
    rw [← h.1, ← h.2]

/-- Two lists of pairs, each without repeated compare values: a klong shadowed
is one of the first list whose compare value the second has. -/
theorem shadowOK_append (t : Time) (leaf : Bool) (A B : List (Nat × NodeId))
    (hA : (A.map Prod.fst).Nodup) (hB : (B.map Prod.fst).Nodup) (P : NodeId → Prop)
    (hP : ∀ c y, (c, y) ∈ A → c ∈ B.map Prod.fst → P y) :
    ShadowOK t ⟨leaf, .time t :: keyKs (A ++ B)⟩ P := by
  refine ⟨⟨keyKs (A ++ B), rfl, ?_⟩, ?_⟩
  · intro k hk
    unfold keyKs at hk
    obtain ⟨q, _, hq⟩ := List.mem_map.mp hk
    exact ⟨q.1, q.2, hq.symm⟩
  · intro a b cv y y' hab ha hb
    cases a with
    | zero => simp at ha
    | succ a =>
      cases b with
      | zero => omega
      | succ b =>
        simp only [List.getElem?_cons_succ] at ha hb
        have ha' := keyKs_getElem? _ _ _ _ ha
        have hb' := keyKs_getElem? _ _ _ _ hb
        have hab' : a < b := by omega
        by_cases haA : a < A.length
        · by_cases hbA : b < A.length
          · rw [List.getElem?_append_left haA] at ha'
            rw [List.getElem?_append_left hbA] at hb'
            have := nodup_fst_idx A hA a b cv y y' ha' hb'
            omega
          · rw [List.getElem?_append_left haA] at ha'
            rw [List.getElem?_append_right (by omega)] at hb'
            apply hP cv y (List.mem_of_getElem? ha')
            exact List.mem_map.mpr ⟨(cv, y'), List.mem_of_getElem? hb', rfl⟩
        · rw [List.getElem?_append_right (by omega)] at ha'
          rw [List.getElem?_append_right (by omega)] at hb'
          have := nodup_fst_idx B hB (a - A.length) (b - A.length) cv y y' ha' hb'
          omega

/-- `halves` on a last version of pairs, cut into F and (c1, y1) :: rest. -/
theorem halves_pairs_eq (leaf : Bool) (t : Time) (F rest : List (Nat × NodeId)) (c1 : Nat)
    (y1 : NodeId) (ins : List (Nat × NodeId))
    (hk : F.length = (F.length + (rest.length + 1)) / 2) :
    halves leaf t ⟨leaf, Klong.time t :: keyKs (F ++ (c1, y1) :: rest)⟩ ins =
      (if (match ins.head? with | some (c, _) => decide (c1 ≤ c) | none => false) then
        (⟨leaf, Klong.time t :: keyKs F⟩,
         ⟨leaf, Klong.time t :: keyKs ((if leaf then (c1, y1) :: rest else (0, y1) :: rest) ++
           ins.map (fun q => (if !leaf && q.1 == c1 then 0 else q.1, q.2)))⟩, c1)
      else
        (⟨leaf, Klong.time t :: keyKs (F ++ ins)⟩,
         ⟨leaf, Klong.time t :: keyKs (if leaf then (c1, y1) :: rest else (0, y1) :: rest)⟩, c1)) := by
  have hlen : (F ++ (c1, y1) :: rest).length = F.length + (rest.length + 1) := by simp
  have hs1 : ((⟨leaf, Klong.time t :: keyKs (F ++ (c1, y1) :: rest)⟩ : KNode).size - 1) / 2 + 1 - 1 =
      F.length := by
    simp only [KNode.size, keyKs, List.length_cons, List.length_map, hlen]; omega
  unfold halves
  simp only [hs1, List.drop_succ_cons, List.drop_zero]
  have ht : (keyKs (F ++ (c1, y1) :: rest)).take F.length = keyKs F := by
    simp [keyKs, List.map_append, List.take_left']
  have hd : (keyKs (F ++ (c1, y1) :: rest)).drop F.length = Klong.key c1 y1 :: keyKs rest := by
    simp [keyKs, List.map_append, List.drop_left']
  rw [ht, hd]
  cases hh : ins.head? with
  | none =>
    cases ins with
    | nil => cases leaf <;> simp [keyKs]
    | cons _ _ => simp at hh
  | some q =>
    obtain ⟨c, y⟩ := q
    by_cases hc : c1 ≤ c
    · cases leaf
      · simp [keyKs, hc, List.map_append]
        intro a b _
        split <;> rfl
      · simp [keyKs, hc, List.map_append]
    · cases leaf <;> simp [keyKs, hc, List.map_append]

theorem nodup_fst_of_lt (l : List (Nat × NodeId)) (h : l.Pairwise (fun a b => a.1 < b.1)) :
    (l.map Prod.fst).Nodup :=
  List.pairwise_map.mpr (h.imp (by intro a b hab; omega))

/-- The shadowed klongs of the halves of a space split: a klong of the node
whose compare value a klong put has. -/
theorem halves_shadow (leaf : Bool) (t : Time) (pairs ins : List (Nat × NodeId))
    (hs : pairs.Pairwise (fun a b => a.1 < b.1)) (h2 : 2 ≤ pairs.length)
    (hins : ins.Pairwise (fun a b => a.1 < b.1)) :
    ShadowOK t (halves leaf t ⟨leaf, Klong.time t :: keyKs pairs⟩ ins).1
      (fun y => ∃ c0, (c0, y) ∈ pairs ∧ c0 ∈ ins.map Prod.fst) ∧
    ShadowOK t (halves leaf t ⟨leaf, Klong.time t :: keyKs pairs⟩ ins).2.1
      (fun y => ∃ c0, (c0, y) ∈ pairs ∧ c0 ∈ ins.map Prod.fst) ∧
    0 < (halves leaf t ⟨leaf, Klong.time t :: keyKs pairs⟩ ins).2.2 ∧
    (∃ y, ((halves leaf t ⟨leaf, Klong.time t :: keyKs pairs⟩ ins).2.2, y) ∈ pairs) ∧
    ∃ q ∈ pairs, q.1 < (halves leaf t ⟨leaf, Klong.time t :: keyKs pairs⟩ ins).2.2 := by
  obtain ⟨c1, y1, rest, hD⟩ : ∃ c1 y1 rest, pairs.drop (pairs.length / 2) = (c1, y1) :: rest := by
    cases h : pairs.drop (pairs.length / 2) with
    | nil =>
      have := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at this
      omega
    | cons q rest => exact ⟨q.1, q.2, rest, rfl⟩
  have hsplit : pairs = pairs.take (pairs.length / 2) ++ (c1, y1) :: rest := by
    rw [← hD, List.take_append_drop]
  generalize hF : pairs.take (pairs.length / 2) = F at hsplit
  have hFlen : F.length = pairs.length / 2 := by
    rw [← hF, List.length_take]; omega
  have hlen : pairs.length = F.length + (rest.length + 1) := by
    rw [hsplit]; simp
  have hk : F.length = (F.length + (rest.length + 1)) / 2 := by omega
  have hFpos : 0 < F.length := by omega
  have hs' := hs
  rw [hsplit] at hs'
  obtain ⟨hsF, hsD, hFD⟩ := List.pairwise_append.mp hs'
  have hsR := (List.pairwise_cons.mp hsD).2
  have hc1R : ∀ q ∈ rest, c1 < q.1 := (List.pairwise_cons.mp hsD).1
  have hFc1 : ∀ q ∈ F, q.1 < c1 := fun q hq => hFD q hq (c1, y1) (by simp)
  obtain ⟨f0, hf0⟩ : ∃ f0, f0 ∈ F := ⟨F[0], List.getElem_mem hFpos⟩
  have hc1pos : 0 < c1 := by have := hFc1 f0 hf0; omega
  have hmemF : ∀ q ∈ F, q ∈ F ++ (c1, y1) :: rest := fun q hq => List.mem_append_left _ hq
  have hmemD : ∀ q ∈ (c1, y1) :: rest, q ∈ F ++ (c1, y1) :: rest := fun q hq =>
    List.mem_append_right _ hq
  have hS'sorted : (if leaf then (c1, y1) :: rest else (0, y1) :: rest).Pairwise
      (fun a b => a.1 < b.1) := by
    cases leaf
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact List.pairwise_cons.mpr ⟨fun q hq => by have := hc1R q hq; simp only; omega, hsR⟩
    · simpa using hsD
  rw [hsplit, halves_pairs_eq leaf t F rest c1 y1 ins hk]
  have hP0 : ∀ (A : List (Nat × NodeId)), (A.map Prod.fst).Nodup →
      ShadowOK t ⟨leaf, Klong.time t :: keyKs A⟩
        (fun y => ∃ c0, (c0, y) ∈ F ++ (c1, y1) :: rest ∧ c0 ∈ ins.map Prod.fst) := by
    intro A hA
    have := shadowOK_append t leaf A [] hA List.nodup_nil
      (fun y => ∃ c0, (c0, y) ∈ F ++ (c1, y1) :: rest ∧ c0 ∈ ins.map Prod.fst)
      (fun _ _ _ h => by simp at h)
    simpa using this
  have hext : (∃ y, (c1, y) ∈ F ++ (c1, y1) :: rest) ∧ ∃ q ∈ F ++ (c1, y1) :: rest, q.1 < c1 :=
    ⟨⟨y1, hmemD _ (List.mem_cons_self ..)⟩, ⟨f0, hmemF _ hf0, hFc1 f0 hf0⟩⟩
  have hfalse : ShadowOK t ⟨leaf, Klong.time t :: keyKs (F ++ ins)⟩
        (fun y => ∃ c0, (c0, y) ∈ F ++ (c1, y1) :: rest ∧ c0 ∈ ins.map Prod.fst) ∧
      ShadowOK t ⟨leaf, Klong.time t :: keyKs (if leaf then (c1, y1) :: rest else (0, y1) :: rest)⟩
        (fun y => ∃ c0, (c0, y) ∈ F ++ (c1, y1) :: rest ∧ c0 ∈ ins.map Prod.fst) ∧ 0 < c1 ∧
      (∃ y, (c1, y) ∈ F ++ (c1, y1) :: rest) ∧ ∃ q ∈ F ++ (c1, y1) :: rest, q.1 < c1 := by
    refine ⟨?_, hP0 _ (nodup_fst_of_lt _ hS'sorted), hc1pos, hext⟩
    apply shadowOK_append t leaf F ins (nodup_fst_of_lt F hsF) (nodup_fst_of_lt ins hins)
    intro c' y' hmem hc'
    exact ⟨c', hmemF _ hmem, hc'⟩
  cases ins with
  | nil => simpa using hfalse
  | cons q rest' =>
    obtain ⟨c, y⟩ := q
    simp only [List.head?_cons]
    by_cases hc : c1 ≤ c
    · simp only [hc, decide_true, ↓reduceIte]
      have hinsPos : ∀ q ∈ (c, y) :: rest', c1 ≤ q.1 := by
        intro q hq
        rcases List.mem_cons.mp hq with h | h
        · rw [h]; exact hc
        · have := (List.pairwise_cons.mp hins).1 q h; simp only at this; omega
      refine ⟨hP0 F (nodup_fst_of_lt F hsF), ?_, hc1pos, hext⟩
      apply shadowOK_append t leaf _ _ (nodup_fst_of_lt _ hS'sorted)
      · cases leaf
        · simp only [Bool.not_false, Bool.true_and]
          rw [List.map_map]
          apply List.pairwise_map.mpr
          refine List.Pairwise.imp_of_mem ?_ hins
          intro a b ha hb hab
          have h1 := hinsPos a ha
          have h2 := hinsPos b hb
          simp only [Function.comp, beq_iff_eq]
          split <;> split <;> omega
        · simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
          exact nodup_fst_of_lt _ (by simpa using hins)
      · intro c' y' hmem hc'
        cases leaf
        · simp only [Bool.false_eq_true, ↓reduceIte] at hmem
          simp only [Bool.not_false, Bool.true_and, List.map_map, List.mem_map, Function.comp,
            beq_iff_eq] at hc'
          obtain ⟨q, hq, hqe⟩ := hc'
          have hq1 := hinsPos q hq
          rcases List.mem_cons.mp hmem with h | h
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨c1, hmemD (c1, _) (List.mem_cons_self ..), ?_⟩
            split at hqe
            · rename_i hq1c
              exact List.mem_map.mpr ⟨q, hq, hq1c⟩
            · omega
          · have hcr := hc1R _ h
            simp only at hcr
            refine ⟨c', hmemD _ (List.mem_cons_of_mem _ h), ?_⟩
            split at hqe
            · omega
            · exact List.mem_map.mpr ⟨q, hq, hqe⟩
        · simp only [↓reduceIte] at hmem
          simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte, List.map_map,
            List.mem_map, Function.comp] at hc'
          obtain ⟨q, hq, hqe⟩ := hc'
          exact ⟨c', hmemD _ hmem, List.mem_map.mpr ⟨q, hq, hqe⟩⟩
    · simp only [hc, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact hfalse

/-! ## The time split's last version: no compare value twice -/

theorem writerWP_replaceOrAdd_lastN (n : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd (n.lastVersion c.i) ins) c w (fun out v => v = w ∧
      out.leaf = n.leaf ∧ klongsWf out.ks = true ∧ (∀ s, Klong.time s ∈ out.ks → s ≤ c.i) ∧
      (∀ q, out.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q)) ∧
      ∃ more, out.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) := by
  have h2 := writerWP_replaceOrAdd_map n.leaf n.live ins (KNode.live_keys_nodup n) c w
  rw [← KNode.lastVersion_eq_newKlongs] at h2
  intro out v h
  obtain ⟨a1, a2, a3, a4, a5⟩ := writerWP_replaceOrAdd_last n ins c w out v h
  exact ⟨a1, a2, a3, a4, a5, (h2 out v h).2.1⟩

theorem shadowOK_newKlongs (t : Time) (leaf : Bool) (more : List (Nat × NodeId))
    (h : (more.map Prod.fst).Nodup) (P : NodeId → Prop) :
    ShadowOK t ⟨leaf, newKlongs t more⟩ P := by
  have := shadowOK_append t leaf more [] h List.nodup_nil P (fun _ _ _ hc => by simp at hc)
  simpa [keyKs, newKlongs] using this

/-- The writer's time split of a node that existed before the transaction, with
klongs ins and its last version, below a parent of either kind. -/
theorem writerWP_handleFullWith_time_upN (d' : Nat) (x q : NodeId) (n qn : KNode) (k1 : Nat)
    (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hpq : (w.path[d']?).map (·.2) = some q) (hpk : w.path[d' + 1]? = some (some k1, x))
    (Q : W → Prop)
    (hup : ∀ (l : KNode), l.leaf = n.leaf → klongsWf l.ks = true → (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) →
      (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) →
      (∃ more, l.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) →
      ∀ w1 : W, w1.nodes = w.nodes ++ [(w.next, ⟨n.leaf, l.ks⟩)] → w1.taken = w.taken →
        w1.top = w.top → w1.path = w.path → w1.next = w.next + 2 → w1.vals = w.vals →
        WriterWP (appendKlongs d' q [(k1, w.next)]) c w1 (fun _ w2 =>
          WriterWP (do let m ← getNode x; putNode x (m.toPrev (c.i - 1))) c w2 (fun _ w3 => Q w3))) :
    WriterWP (handleFullWith (fun q more => appendKlongs d' q more) (d' + 1) x ins
      (n.lastVersion c.i) compact) c w (fun _ w' => Q w') := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look hl_nd _ rfl rfl rfl rfl rfl rfl
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
      rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
      subst w1
      split <;>
      · simp only [newKey, fresh, setMadeFor, klongAt, note, writerWP_bind, writerWP_modify,
          writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, hpk]
          exact hup l hl_leaf hl_wf hl_times hl_look hl_nd _ rfl rfl rfl rfl rfl rfl

/-- The writer's time split in place of x, made by the transaction, below a
parent q that the writer has: x holds its last version with ins. -/
theorem writerWP_handleFullWith_timeInPlace_termN (up : NodeId → List (Nat × NodeId) → M Unit)
    (d' : Nat) (x q : NodeId) (n qn : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hlq : w.nodes.lookup q = some qn)
    (hpq : (w.path[d']?).map (·.2) = some q) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up (d' + 1) x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        (∃ more, l.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, l.ks⟩) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
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
    simp only [writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
    cases compact with
    | true =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
      refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
      rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
      subst hw3
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
    | false =>
      simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
      refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
      rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
      subst hw3
      split <;>
      · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
        refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

set_option linter.unusedSimpArgs false in
/-- The writer's time split of the space root x, which existed before the
transaction: the new node at the next id holds the last version with ins and
is the new space root; x keeps its klongs before the transaction. -/
theorem writerWP_handleFullWith_rootTime_termN (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime ≠ some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false)
    (hxn : x < w.next) (hny : w.nodes.lookup w.next = none) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        (∃ more, l.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) ∧
        w'.taken = w.taken ∧ w'.top.rootKey = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧
        w.next + 2 ≤ w'.next ∧
        ∀ z, w'.nodes.lookup z =
          if z = x then some (n.toPrev (c.i - 1))
          else if z = w.next then some ⟨n.leaf, l.ks⟩ else w.nodes.lookup z) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = false := by simpa using hfirst
  simp only [hnew, parentAt, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
  have hx1 : x ≠ w.next := by omega
  split <;>
  · simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w1 ⟨hw1, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
    subst w1
    split <;>
    · simp only [newKey, fresh, setMadeFor, note, newSuperRoot, writerWP_bind, writerWP_modify,
        writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
      split <;>
      · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
        split <;>
        · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_get, writerWP_set]
          refine (writerWP_getNode_known x n c _ ?_ _).mpr ?_
          · simp only [List.lookup_append, hlk]; rfl
          rw [putNode, writerWP_modify]
          refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
          all_goals first | rfl | trivial | (simp only []; omega) | omega | skip
          show (upsert _ x _).lookup z = _
          rw [lookup_upsert]
          by_cases hzx : z = x
          · simp [hzx]
          · simp only [hzx, ↓reduceIte, List.lookup_append]
            by_cases hzy : z = w.next
            · subst hzy; rw [hny]; simp [List.lookup]
            · simp only [hzy, ↓reduceIte]
              cases h : w.nodes.lookup z with
              | some m => rfl
              | none =>
                show (none : Option KNode).or ([(w.next, { leaf := n.leaf, ks := l.ks })].lookup z) = none
                rw [lookup_cons_ne _ _ _ _ hzy]; rfl

/-- The writer's time split in place of the space root x, made by the
transaction: x holds its last version with ins. -/
theorem writerWP_handleFullWith_timeInPlace_term0N (up : NodeId → List (Nat × NodeId) → M Unit)
    (x : NodeId) (n : KNode) (ins : List (Nat × NodeId)) (compact : Bool)
    (c : Ctx) (w : W) (hlk : w.nodes.lookup x = some n) (hfirst : n.firstTime = some c.i)
    (hcs : (!compact && decide ((n.lastVersion c.i).size > c.p.splitAbove)) = false) :
    WriterWP (handleFullWith up 0 x ins (n.lastVersion c.i) compact) c w (fun _ w' =>
      ∃ l : KNode, l.leaf = n.leaf ∧ klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
        (∀ q', l.live.lookup q' = ins.foldl (pairLookupStep q') (n.live.lookup q')) ∧
        (∃ more, l.ks = newKlongs c.i more ∧ (more.map Prod.fst).Nodup) ∧
        w'.taken = w.taken ∧ w'.top = w.top ∧ w'.vals = w.vals ∧ w'.next = w.next ∧
        w'.path = w.path ∧ w'.nodes = upsert w.nodes x ⟨n.leaf, l.ks⟩) := by
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  refine writerWP_ghOf_cached x n c w hlk _ (fun gh => ?_)
  have hnew : (n.firstTime == some c.i) = true := by simp [hfirst]
  simp only [hnew, parentAt, writerWP_bind, writerWP_pure, hcs, Bool.false_eq_true, ↓reduceIte,
    Bool.not_true]
  cases compact with
  | true =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
    subst hw3
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  | false =>
    simp only [↓reduceIte, note, writerWP_bind, writerWP_modify, Bool.false_eq_true]
    refine writerWP_mono (writerWP_replaceOrAdd_lastN n ins c _) ?_
    rintro l w3 ⟨hw3, hl_leaf, hl_wf, hl_times, hl_look, hl_nd⟩
    subst hw3
    split <;>
    · simp only [putNode, writerWP_bind, writerWP_modify, writerWP_pure]
      refine ⟨l, hl_leaf, hl_wf, hl_times, hl_look, hl_nd, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-! ## The shapes of a cascade's nodes -/

/-- What a shadowed klong of a node that the cascade made or changed names: the
old klong to a split child that was copied (not split in place), or a live
klong of the bottom node D for a compare value of the klongs put there. -/
def ChainShadow (c : Ctx) (X : Nat → NodeId) (Nn : Nat → KNode) (s D : Nat)
    (ins : List (Nat × NodeId)) (y : NodeId) : Prop :=
  (∃ i, s ≤ i ∧ i < D ∧ y = X (i + 1) ∧ (Nn (i + 1)).firstTime ≠ some c.i) ∨
  (∃ c0, (c0, y) ∈ (Nn D).liveAt c.i ∧ c0 ∈ ins.map Prod.fst)

/-- The node X j where the cascade from D ends: the klongs ins added at D; or
the klongs of the split below added, which shadow only the old klong to a split
child that was copied; or the klong to a child split in place repointed. -/
def CascadeTop (c : Ctx) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (D : Nat)
    (ins : List (Nat × NodeId)) (j : Nat) (zn : KNode) : Prop :=
  (j = D ∧ zn = ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn j)) ∨
  (j < D ∧ ∃ ins' : List (Nat × NodeId),
    zn = ins'.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn j) ∧
    (ins'.map Prod.fst).Nodup ∧ ∀ q ∈ ins', ∀ y, (q.1, y) ∈ (Nn j).liveAt c.i →
      q.1 = K (j + 1) ∧ y = X (j + 1) ∧ (Nn (j + 1)).firstTime ≠ some c.i) ∨
  (j < D ∧ ∃ k1 idx r, (Nn j).linkIndex (X (j + 1)) k1 = some idx ∧ zn = (Nn j).repoint idx r ∧
    (Nn (j + 1)).firstTime = some c.i ∧ (Nn j).leaf = true)

/-- A node z, zn after a cascade from D with ins: a chain node the cascade did
not reach, unchanged; a chain node left behind with its klongs before the
transaction; or a node of time c.i whose shadowed klongs
are as `ChainShadow` says, a chain node among them made by the transaction; or
the node where the cascade ends. -/
def CascadeNodeShape (c : Ctx) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (s D : Nat)
    (ins : List (Nat × NodeId)) (z : NodeId) (zn : KNode) : Prop :=
  (∃ i, s ≤ i ∧ i ≤ D ∧ z = X i ∧ zn = Nn i) ∨
  (∃ i, s ≤ i ∧ i ≤ D ∧ z = X i ∧ zn = (Nn i).toPrev (c.i - 1) ∧
    (Nn i).firstTime ≠ some c.i) ∨
  (ShadowOK c.i zn (ChainShadow c X Nn s D ins) ∧
    ∀ i, s ≤ i → i ≤ D → z = X i → (Nn i).firstTime = some c.i) ∨
  (∃ j, s ≤ j ∧ j ≤ D ∧ z = X j ∧ CascadeTop c X K Nn D ins j zn)

/-- The writer's state after a cascade from D with ins, from w: the next id
grows, nodes below w's next id off the chain are kept, ids from the next id on
are free, and every node the cascade made or changed has its shape. -/
def ShapePost (c : Ctx) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (s D : Nat)
    (ins : List (Nat × NodeId)) (w w' : W) : Prop :=
  w.next ≤ w'.next ∧
  (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
  (∀ z, w'.next ≤ z → w'.nodes.lookup z = none) ∧
  ∀ z zn, w'.nodes.lookup z = some zn → (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i) →
    CascadeNodeShape c X K Nn s D ins z zn

/-- A shape after the cascade from D + 1's parent step, from the klongs ins'
that the split of X (D + 1) puts into X D, is a shape of the cascade from
D + 1. -/
theorem cascadeShape_lift (c : Ctx) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (s D : Nat) (ins ins' : List (Nat × NodeId)) (z : NodeId) (zn : KNode)
    (hnd : (ins'.map Prod.fst).Nodup)
    (hpar : ∀ q ∈ ins', ∀ y, (q.1, y) ∈ (Nn D).liveAt c.i →
      q.1 = K (D + 1) ∧ y = X (D + 1) ∧ (Nn (D + 1)).firstTime ≠ some c.i)
    (hzx : z ≠ X (D + 1)) (hs : s ≤ D)
    (h : CascadeNodeShape c X K Nn s D ins' z zn) : CascadeNodeShape c X K Nn s (D + 1) ins z zn := by
  rcases h with ⟨i, h1, h2, h3, h4⟩ | ⟨i, h1, h2, h3, h4⟩ | ⟨hsh, hft⟩ | ⟨j, h1, h2, h3, htop⟩
  · exact Or.inl ⟨i, h1, by omega, h3, h4⟩
  · exact Or.inr (Or.inl ⟨i, h1, by omega, h3, h4⟩)
  · refine Or.inr (Or.inr (Or.inl ⟨hsh.mono ?_, fun i h1 h2 h3 => ?_⟩))
    · intro y hy
      rcases hy with ⟨i, a1, a2, a3, a4⟩ | ⟨c0, a1, a2⟩
      · exact Or.inl ⟨i, a1, by omega, a3, a4⟩
      · obtain ⟨q, hq, hq1⟩ := List.mem_map.mp a2
        obtain ⟨_, hy, hft⟩ := hpar q hq y (by rw [hq1]; exact a1)
        exact Or.inl ⟨D, hs, by omega, hy, hft⟩
    · rcases Nat.lt_or_ge i (D + 1) with hl | hl
      · exact hft i h1 (by omega) h3
      · have : i = D + 1 := by omega
        subst this; exact absurd h3 hzx
  · refine Or.inr (Or.inr (Or.inr ⟨j, h1, by omega, h3, ?_⟩))
    rcases htop with ⟨hj, hz⟩ | ⟨hj, hrest⟩ | ⟨hj, hrest⟩
    · subst hj
      exact Or.inr (Or.inl ⟨by omega, ins', hz, hnd, hpar⟩)
    · exact Or.inr (Or.inl ⟨by omega, hrest⟩)
    · exact Or.inr (Or.inr ⟨by omega, hrest⟩)

theorem shadowOK_root (t : Time) (a b : NodeId) (sc : Nat) (hsc : 0 < sc) (P : NodeId → Prop) :
    ShadowOK t ⟨false, [Klong.time t, .key 0 a, .key sc b]⟩ P := by
  have hnd : ([(0, a), (sc, b)].map Prod.fst).Nodup := by
    simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, or_false, not_false_eq_true, List.nodup_nil, and_true]
    omega
  exact shadowOK_newKlongs t false [(0, a), (sc, b)] hnd P

theorem newKlongs_keyKs (t : Time) (l : List (Nat × NodeId)) :
    newKlongs t l = Klong.time t :: keyKs l := rfl

/-- The halves of a node's space split: their shadowed klongs are live klongs of
the node for compare values of ins; the divider is a live compare value above
another one. -/
theorem halves_node (n : KNode) (t : Time) (ins : List (Nat × NodeId))
    (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (h2 : 2 ≤ n.live.length)
    (hins : ins.Pairwise (fun a b => a.1 < b.1)) :
    ShadowOK t (halves n.leaf t (n.lastVersion t) ins).1
      (fun y => ∃ c0, (c0, y) ∈ n.liveAt t ∧ c0 ∈ ins.map Prod.fst) ∧
    ShadowOK t (halves n.leaf t (n.lastVersion t) ins).2.1
      (fun y => ∃ c0, (c0, y) ∈ n.liveAt t ∧ c0 ∈ ins.map Prod.fst) ∧
    0 < (halves n.leaf t (n.lastVersion t) ins).2.2 ∧
    (∃ y, ((halves n.leaf t (n.lastVersion t) ins).2.2, y) ∈ n.live) ∧
    ∃ q ∈ n.live, q.1 < (halves n.leaf t (n.lastVersion t) ins).2.2 := by
  rw [KNode.lastVersion_eq_newKlongs, newKlongs_keyKs]
  obtain ⟨a1, a2, a3, a4, a5⟩ := halves_shadow n.leaf t n.live ins (KNode.live_order n) h2 hins
  have hl : ∀ y, (∃ c0, (c0, y) ∈ n.live ∧ c0 ∈ ins.map Prod.fst) →
      ∃ c0, (c0, y) ∈ n.liveAt t ∧ c0 ∈ ins.map Prod.fst := by
    rintro y ⟨c0, h1, h2⟩
    exact ⟨c0, by rw [KNode.liveAt_of_times n t ht]; exact h1, h2⟩
  exact ⟨a1.mono hl, a2.mono hl, a3, a4, a5⟩

/-! ## The targets of a cascade's nodes -/

theorem keyKs_target (A : List (Nat × NodeId)) (T : NodeId → Prop) (hA : ∀ q ∈ A, T q.2)
    (cv : Nat) (y : NodeId) (h : Klong.key cv y ∈ keyKs A) : T y := by
  unfold keyKs at h
  obtain ⟨q, hq, hqe⟩ := List.mem_map.mp h
  simp only [Klong.key.injEq] at hqe
  rw [← hqe.2]; exact hA q hq

/-- The key klongs of the halves of a node's split name what the node's live
klongs or the klongs put name. -/
theorem halves_targets (n : KNode) (t : Time) (ins : List (Nat × NodeId))
    (h2 : 2 ≤ n.live.length) :
    (∀ cv y, Klong.key cv y ∈ (halves n.leaf t (n.lastVersion t) ins).1.ks →
      (∃ c', (c', y) ∈ n.live) ∨ ∃ c', (c', y) ∈ ins) ∧
    (∀ cv y, Klong.key cv y ∈ (halves n.leaf t (n.lastVersion t) ins).2.1.ks →
      (∃ c', (c', y) ∈ n.live) ∨ ∃ c', (c', y) ∈ ins) := by
  rw [KNode.lastVersion_eq_newKlongs, newKlongs_keyKs]
  generalize hp : n.live = pairs at h2 ⊢
  obtain ⟨c1, y1, rest, hD⟩ : ∃ c1 y1 rest, pairs.drop (pairs.length / 2) = (c1, y1) :: rest := by
    cases h : pairs.drop (pairs.length / 2) with
    | nil =>
      have := congrArg List.length h
      simp only [List.length_drop, List.length_nil] at this
      omega
    | cons q rest => exact ⟨q.1, q.2, rest, rfl⟩
  have hsplit : pairs = pairs.take (pairs.length / 2) ++ (c1, y1) :: rest := by
    rw [← hD, List.take_append_drop]
  generalize hF : pairs.take (pairs.length / 2) = F at hsplit
  have hFlen : F.length = pairs.length / 2 := by
    rw [← hF, List.length_take]; omega
  have hlen : pairs.length = F.length + (rest.length + 1) := by rw [hsplit]; simp
  have hk : F.length = (F.length + (rest.length + 1)) / 2 := by omega
  let T : NodeId → Prop := fun y => (∃ c', (c', y) ∈ pairs) ∨ ∃ c', (c', y) ∈ ins
  have hTF : ∀ q ∈ F, T q.2 := fun q hq =>
    Or.inl ⟨q.1, by rw [hsplit]; exact List.mem_append_left _ hq⟩
  have hTD : ∀ q ∈ (if n.leaf then (c1, y1) :: rest else (0, y1) :: rest), T q.2 := by
    intro q hq
    have hmem : ∀ q ∈ (c1, y1) :: rest, q ∈ pairs := fun q hq => by
      rw [hsplit]; exact List.mem_append_right _ hq
    split at hq
    · exact Or.inl ⟨q.1, hmem q hq⟩
    · rcases List.mem_cons.mp hq with h | h
      · subst h; exact Or.inl ⟨c1, hmem _ (List.mem_cons_self ..)⟩
      · exact Or.inl ⟨q.1, hmem q (List.mem_cons_of_mem _ h)⟩
  have hTI : ∀ (g : Nat × NodeId → Nat), ∀ q ∈ ins.map (fun q => (g q, q.2)), T q.2 := by
    intro g q hq
    obtain ⟨q', hq', hqe⟩ := List.mem_map.mp hq
    rw [← hqe]; exact Or.inr ⟨q'.1, hq'⟩
  have hTI' : ∀ q ∈ ins, T q.2 := fun q hq => Or.inr ⟨q.1, hq⟩
  rw [hsplit, halves_pairs_eq n.leaf t F rest c1 y1 ins hk]
  rw [← hsplit]
  have happ : ∀ A B : List (Nat × NodeId), (∀ q ∈ A, T q.2) → (∀ q ∈ B, T q.2) → ∀ q ∈ A ++ B, T q.2 :=
    fun A B hA hB q hq => (List.mem_append.mp hq).elim (hA q) (hB q)
  generalize (match ins.head? with | some (c, _) => decide (c1 ≤ c) | none => false) = b
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun cv y h => ?_, fun cv y h => ?_⟩
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact keyKs_target _ T (happ _ _ hTF hTI') cv y h
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact keyKs_target _ T hTD cv y h
  · simp only [↓reduceIte]
    refine ⟨fun cv y h => ?_, fun cv y h => ?_⟩
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact keyKs_target F T hTF cv y h
    · simp only [List.mem_cons, reduceCtorEq, false_or] at h
      exact keyKs_target _ T (happ _ _ hTD (hTI _)) cv y h

theorem toPrev_key_mem (n : KNode) (t : Time) (cv : Nat) (y : NodeId)
    (h : Klong.key cv y ∈ (n.toPrev t).ks) : Klong.key cv y ∈ n.ks :=
  (prefixAt_prefix n.ks t).subset h

theorem repoint_key_mem (n : KNode) (j : Nat) (r : NodeId) (cv : Nat) (y : NodeId)
    (h : Klong.key cv y ∈ (n.repoint j r).ks) : (∃ cv', Klong.key cv' y ∈ n.ks) ∨ y = r := by
  unfold KNode.repoint at h
  split at h
  · rename_i c0 y0 hj
    simp only [KNode.setAt] at h
    rcases List.mem_or_eq_of_mem_set h with h' | h'
    · exact Or.inl ⟨cv, h'⟩
    · simp only [Klong.key.injEq] at h'; exact Or.inr h'.2
  · exact Or.inl ⟨cv, h⟩

theorem addKeys_key_mem (t : Time) (ins : List (Nat × NodeId)) :
    ∀ (n : KNode) (cv : Nat) (y : NodeId),
      Klong.key cv y ∈ (ins.foldl (fun n (cv, y) => n.add t (.key cv y)) n).ks →
      Klong.key cv y ∈ n.ks ∨ (cv, y) ∈ ins := by
  induction ins with
  | nil => intro n cv y h; exact Or.inl h
  | cons q rest ih =>
    intro n cv y h
    obtain ⟨a, b⟩ := q
    simp only [List.foldl_cons] at h
    rcases ih _ cv y h with h' | h'
    · have hk : Klong.key cv y ∈ n.ks ∨ Klong.key cv y = Klong.key a b := by
        unfold KNode.add at h'
        split at h'
        · split at h' <;> simp_all
        · simp_all
      rcases hk with hk | hk
      · exact Or.inl hk
      · simp only [Klong.key.injEq] at hk
        obtain ⟨rfl, rfl⟩ := hk
        exact Or.inr (List.mem_cons_self ..)
    · exact Or.inr (List.mem_cons_of_mem _ h')

/-- The klongs that a cascade's step puts at time t into its bottom node D: a
node whose key klongs name what D's klongs or the klongs put name, of D's leaf
flag, links y, which D's klongs do not name, only by a klong put. -/
def LeafTargets (c : Ctx) (X : Nat → NodeId) (Nn : Nat → KNode) (s D : Nat)
    (ins : List (Nat × NodeId)) (w w' : W) : Prop :=
  ∀ y, y < w.next → (∀ i, s ≤ i → i ≤ D → ∀ cv, Klong.key cv y ∉ (Nn i).ks) →
    (∀ i, s ≤ i → i ≤ D → y ≠ X i) →
    ∀ z zn cv, w'.nodes.lookup z = some zn → (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i) →
      (cv, y) ∈ zn.liveAt c.i → (∃ c', (c', y) ∈ ins) ∧ zn.leaf = (Nn D).leaf

theorem leafTarget_of_keys (t : Time) (n zn : KNode) (ins : List (Nat × NodeId)) (y : NodeId)
    (hy : ∀ cv, Klong.key cv y ∉ n.ks)
    (hks : ∀ cv y', Klong.key cv y' ∈ zn.ks → (∃ c', Klong.key c' y' ∈ n.ks) ∨ ∃ c', (c', y') ∈ ins)
    (hleaf : zn.leaf = n.leaf) (cv : Nat) (h : (cv, y) ∈ zn.liveAt t) :
    (∃ c', (c', y) ∈ ins) ∧ zn.leaf = n.leaf := by
  rcases hks cv y (KNode.liveAt_key_mem zn t cv y h) with ⟨c', h'⟩ | h'
  · exact absurd h' (hy c')
  · exact ⟨h', hleaf⟩

theorem leafTarget_none (t : Time) (zn : KNode) (y : NodeId) (hy : ∀ cv, Klong.key cv y ∉ zn.ks)
    (cv : Nat) (h : (cv, y) ∈ zn.liveAt t) : False :=
  hy cv (KNode.liveAt_key_mem zn t cv y h)

theorem leafTarget_time (t : Time) (n l : KNode) (leaf : Bool) (ins : List (Nat × NodeId))
    (y : NodeId) (hy : ∀ cv, Klong.key cv y ∉ n.ks) (htn : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (htl : ∀ s, Klong.time s ∈ l.ks → s ≤ t)
    (hlook : ∀ q, l.live.lookup q = ins.foldl (pairLookupStep q) (n.live.lookup q))
    (cv : Nat) (h : (cv, y) ∈ (⟨leaf, l.ks⟩ : KNode).liveAt t) : ∃ c', (c', y) ∈ ins := by
  have h1 : (cv, y) ∈ (⟨leaf, l.ks⟩ : KNode).live := by
    rw [← KNode.liveAt_of_times (⟨leaf, l.ks⟩ : KNode) t htl]; exact h
  have h2 : l.live.lookup cv = some y :=
    lookup_of_mem_nodup _ (KNode.live_keys_nodup (⟨leaf, l.ks⟩ : KNode)) _ _ h1
  rw [hlook] at h2
  rcases pairLookupFold_some_mem cv ins _ y h2 with h3 | h3
  · exact ⟨cv, h3⟩
  · have h4 := lookup_some_mem h3
    rw [← KNode.liveAt_of_times n t htn] at h4
    exact absurd (KNode.liveAt_key_mem n t cv y h4) (hy cv)

theorem halves_keys (n : KNode) (t : Time) (ins : List (Nat × NodeId))
    (htn : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (h2 : 2 ≤ n.live.length) :
    (∀ cv y, Klong.key cv y ∈ (halves n.leaf t (n.lastVersion t) ins).1.ks →
      (∃ c', Klong.key c' y ∈ n.ks) ∨ ∃ c', (c', y) ∈ ins) ∧
    (∀ cv y, Klong.key cv y ∈ (halves n.leaf t (n.lastVersion t) ins).2.1.ks →
      (∃ c', Klong.key c' y ∈ n.ks) ∨ ∃ c', (c', y) ∈ ins) := by
  obtain ⟨a, b⟩ := halves_targets n t ins h2
  have hc : ∀ y, (∃ c', (c', y) ∈ n.live) → ∃ c', Klong.key c' y ∈ n.ks := by
    rintro y ⟨c', h⟩
    rw [← KNode.liveAt_of_times n t htn] at h
    exact ⟨c', KNode.liveAt_key_mem n t c' y h⟩
  exact ⟨fun cv y h => (a cv y h).imp (hc y) id, fun cv y h => (b cv y h).imp (hc y) id⟩

theorem root_key_ne (t : Time) (a b y : NodeId) (sc : Nat) (ha : y ≠ a) (hb : y ≠ b) (cv : Nat) :
    Klong.key cv y ∉ ([Klong.time t, .key 0 a, .key sc b] : List Klong) := by
  intro h
  simp only [List.mem_cons, reduceCtorEq, Klong.key.injEq, List.not_mem_nil, or_false,
    false_or] at h
  rcases h with ⟨_, h⟩ | ⟨_, h⟩
  · exact ha h
  · exact hb h

/-! ## The cascade -/

/-- `ShapePost` with a property `Bnd` of every node the cascade made or
changed. -/
def ShapePostG (Bnd : KNode → Prop) (c : Ctx) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode)
    (s D : Nat) (ins : List (Nat × NodeId)) (w w' : W) : Prop :=
  w.next ≤ w'.next ∧
  (∀ z, z < w.next → (∀ i, s ≤ i → i ≤ D → z ≠ X i) → w'.nodes.lookup z = w.nodes.lookup z) ∧
  (∀ z, w'.next ≤ z → w'.nodes.lookup z = none) ∧
  ∀ z zn, w'.nodes.lookup z = some zn → (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D ∧ z = X i) →
    CascadeNodeShape c X K Nn s D ins z zn ∧ Bnd zn

set_option maxHeartbeats 3200000 in
/-- `writerWP_appendKlongs_chainShape` with a property `Bnd` of every node the
cascade makes or changes, which every kind of node the cascade can write has
(the dead klongs' bound, `writerWP_appendKlongs_chainDead`). The shapes of the
nodes that a cascade of splits makes or changes (bergdb
024-12; for prover putinv's take-back (C)), on the premises of
`writerWP_appendKlongs_chainGRV` that concern the writer's nodes, with
`ChainOrd` at every level and the klongs put ordered: after `appendKlongs (s + e)`
every node with an id from the next id on or on the chain is a chain node the
cascade did not reach, a chain node left behind, a node of time c.i whose
shadowed klongs name a split child that was copied or a live klong of X (s + e)
for a compare value put there (`ChainShadow`), or the node where the cascade
ends (`CascadeTop`). -/
theorem writerWP_appendKlongs_chainShapeG (c : Ctx)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (Bnd : KNode → Prop)
    (hBc : ∀ i, s ≤ i → i ≤ D → Bnd (Nn i))
    (hBt : ∀ n, deadOver c.p n = false → Bnd n)
    (hBn : ∀ (n : KNode) (more : List (Nat × NodeId)), n.ks = newKlongs c.i more →
      (more.map Prod.fst).Nodup → Bnd n)
    (hBh : ∀ i, s ≤ i → i ≤ D → ∀ ins : List (Nat × NodeId), ins.length ≤ 2 →
      Bnd (halves (Nn i).leaf c.i ((Nn i).lastVersion c.i) ins).1 ∧
        Bnd (halves (Nn i).leaf c.i ((Nn i).lastVersion c.i) ins).2.1)
    (hBr : ∀ (a b : NodeId) (sc : Nat), 0 < sc → Bnd ⟨false, [Klong.time c.i, .key 0 a, .key sc b]⟩)
    (hBp : ∀ i, s ≤ i → i ≤ D → Bnd ((Nn i).toPrev (c.i - 1)))
    (hBe : ∀ i, s ≤ i → i ≤ D → ∀ idx r, Bnd ((Nn i).repoint idx r)) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → ins.Pairwise (fun a b => a.1 < b.1) → w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        ShapePostG Bnd c X K Nn s (s + e) ins w w') := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next) →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        ShapePostG Bnd c X K Nn s (s + e) ins w w') := by
    intro e _ w ins hS2 hroom hdead hfr
    obtain ⟨hlk, hxn⟩ := hS2 (s + e) (by omega) (Nat.le_refl _)
    refine writerWP_mono (writerWP_appendKlongs_addKeys (s + e) (X (s + e)) (Nn (s + e)) ins c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
    · intro z _ hz
      show (upsert w.nodes _ _).lookup z = _
      rw [lookup_upsert]
      simp only [hz (s + e) (by omega) (Nat.le_refl _), ↓reduceIte]
    · intro z hz
      have hz' : w.next ≤ z := hz
      show (upsert w.nodes _ _).lookup z = _
      have hzx : z ≠ X (s + e) := by intro h; subst h; omega
      rw [lookup_upsert]
      simp only [hzx, ↓reduceIte]
      exact hfr z hz'
    · intro z zn h hz
      change (upsert w.nodes _ _).lookup z = some zn at h
      rw [lookup_upsert] at h
      by_cases hzx : z = X (s + e)
      · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
        subst h
        refine ⟨?_, hBt _ hdead⟩
        exact Or.inr (Or.inr (Or.inr ⟨s + e, by omega, Nat.le_refl _, hzx, Or.inl ⟨rfl, rfl⟩⟩))
      · simp only [hzx, ↓reduceIte] at h
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · have hz' : w.next ≤ z := hz
          rw [hfr z hz'] at h; cases h
        · rw [h3, (hS2 i h1 h2).1] at h
          cases h
          refine ⟨?_, hBc i h1 (by omega)⟩
          exact Or.inl ⟨i, h1, h2, h3, rfl⟩
  intro e
  induction e with
  | zero =>
    intro hD w ins hins hinsS hpath hS2 hfr
    by_cases hroom : (Nn (s + 0)).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + 0))) = false
    · exact hroomCase 0 hD w ins hS2 hroom.1 hroom.2 hfr
    · have hs0 : s = 0 := by
        rcases htop with h | h
        · exfalso
          exact hroom ⟨by have := h.1; have := hins.length; simp only [Nat.add_zero]; omega,
            by simpa using h.2 ins hins.length⟩
        · exact h
      subst hs0
      simp only [Nat.add_zero] at hroom hins hS2 ⊢
      obtain ⟨hlk, hxn⟩ := hS2 0 (Nat.le_refl _) (Nat.le_refl _)
      have hNR : ¬ ChainRoom c (Nn 0) := fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩
      have hxt := htimes 0 (Nat.le_refl _) (by omega)
      have hfree0 := hfr w.next (Nat.le_refl _)
      have hfree2 := hfr (w.next + 2) (by omega)
      have hTIME0 : ∀ (up : NodeId → List (Nat × NodeId) → M Unit) (compact : Bool),
          (!compact && decide (((Nn 0).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith up 0 (X 0) ins ((Nn 0).lastVersion c.i) compact) c w (fun _ w' =>
            ShapePostG Bnd c X K Nn 0 0 ins w w') := by
        intro up compact hcs
        by_cases hmade : (Nn 0).firstTime = some c.i
        · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term0N up (X 0) (Nn 0) ins compact
            c w hlk hmade hcs) ?_
          rintro _ w' ⟨l, _, _, _, _, ⟨more, hmore, hnd⟩, _, _, _, h'next, _, h'n⟩
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro z _ hz
            rw [h'n, lookup_upsert]
            simp only [hz 0 (Nat.le_refl _) (Nat.le_refl _), ↓reduceIte]
          · intro z hz
            rw [h'next] at hz
            have hzx : z ≠ X 0 := by intro h; subst h; omega
            rw [h'n, lookup_upsert]
            simp only [hzx, ↓reduceIte]
            exact hfr z hz
          · intro z zn h hz
            rw [h'n, lookup_upsert] at h
            by_cases hzx : z = X 0
            · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBn _ more hmore hnd⟩
              refine Or.inr (Or.inr (Or.inl ⟨?_, fun i h1 h2 _ => ?_⟩))
              · rw [hmore]; exact shadowOK_newKlongs c.i _ more hnd _
              · have : i = 0 := by omega
                subst this; exact hmade
            · simp only [hzx, ↓reduceIte] at h
              rcases hz with hz | ⟨i, h1, h2, h3⟩
              · rw [hfr z hz] at h; cases h
              · have : i = 0 := by omega
                subst this; exact absurd h3 hzx
        · refine writerWP_mono (writerWP_handleFullWith_rootTime_termN up (X 0) (Nn 0) ins compact c w
            hlk hmade hcs hxn hfree0) ?_
          rintro _ w' ⟨l, _, _, _, _, ⟨more, hmore, hnd⟩, _, _, _, _, h'next, h'n⟩
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro z hzl hz
            have h1 : z ≠ X 0 := hz 0 (Nat.le_refl _) (Nat.le_refl _)
            have h2 : z ≠ w.next := by omega
            rw [h'n]
            simp only [h1, h2, ↓reduceIte]
          · intro z hz
            have h1 : z ≠ X 0 := by omega
            have h2 : z ≠ w.next := by omega
            rw [h'n]
            simp only [h1, h2, ↓reduceIte]
            exact hfr z (by omega)
          · intro z zn h hz
            rw [h'n] at h
            by_cases h1 : z = X 0
            · simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBp 0 (by omega) (by omega)⟩
              exact Or.inr (Or.inl ⟨0, Nat.le_refl _, Nat.le_refl _, h1, rfl, hmade⟩)
            · by_cases h2 : z = w.next
              · subst h2
                simp only [h1, ↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, hBn _ more hmore hnd⟩
                refine Or.inr (Or.inr (Or.inl ⟨?_, fun i h1' h2' h3' => ?_⟩))
                · rw [hmore]; exact shadowOK_newKlongs c.i _ more hnd _
                · have : i = 0 := by omega
                  subst this
                  exact absurd h3' h1
              · simp only [h1, h2, ↓reduceIte] at h
                rcases hz with hz | ⟨i, h1', h2', h3'⟩
                · rw [hfr z hz] at h; cases h
                · have : i = 0 := by omega
                  subst this; exact absurd h3' h1
      have hSPACE0 : ∀ (up : NodeId → List (Nat × NodeId) → M Unit),
          c.p.splitAbove < ((Nn 0).lastVersion c.i).size →
          WriterWP (handleFullWith up 0 (X 0) ins ((Nn 0).lastVersion c.i) false) c w (fun _ w' =>
            ShapePostG Bnd c X K Nn 0 0 ins w w') := by
        intro up hsp
        have h2l := hlen 0 (Nat.le_refl _) (by omega) hNR hsp
        obtain ⟨hF, hS, hscpos, _, _⟩ := halves_node (Nn 0) c.i ins hxt h2l hinsS
        have hmono : ∀ zn, ShadowOK c.i zn
            (fun y => ∃ c0, (c0, y) ∈ (Nn 0).liveAt c.i ∧ c0 ∈ ins.map Prod.fst) →
            ShadowOK c.i zn (ChainShadow c X Nn 0 0 ins) :=
          fun zn h => h.mono (fun y hy => Or.inr hy)
        by_cases hmade : (Nn 0).firstTime = some c.i
        · refine writerWP_mono (writerWP_handleFullWith_rootSpaceInPlace_term up (X 0) (Nn 0) ins c w
            hlk hmade hsp hxn hfree2) ?_
          rintro _ w' ⟨_, _, _, _, h'next, h'n⟩
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro z hzl hz
            have h1 : z ≠ X 0 := hz 0 (Nat.le_refl _) (Nat.le_refl _)
            have h2 : z ≠ w.next := by omega
            have h3 : z ≠ w.next + 2 := by omega
            rw [h'n]
            simp only [h1, h2, h3, ↓reduceIte]
          · intro z hz
            have h1 : z ≠ X 0 := by omega
            have h2 : z ≠ w.next := by omega
            have h3 : z ≠ w.next + 2 := by omega
            rw [h'n]
            simp only [h1, h2, h3, ↓reduceIte]
            exact hfr z (by omega)
          · intro z zn h hz
            rw [h'n] at h
            by_cases h1 : z = X 0
            · simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, (hBh 0 (by omega) (by omega) ins hins.length).1⟩
              refine Or.inr (Or.inr (Or.inl ⟨hmono _ hF, fun i _ h2' _ => ?_⟩))
              have : i = 0 := by omega
              subst this; exact hmade
            · by_cases h2 : z = w.next
              · subst h2
                simp only [h1, ↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, (hBh 0 (by omega) (by omega) ins hins.length).2⟩
                refine Or.inr (Or.inr (Or.inl ⟨hmono _ hS, fun i _ h2' h3' => ?_⟩))
                have : i = 0 := by omega
                subst this
                exact absurd h3' h1
              · by_cases h3 : z = w.next + 2
                · subst h3
                  simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  refine ⟨?_, hBr _ _ _ hscpos⟩
                  refine Or.inr (Or.inr (Or.inl ⟨shadowOK_root c.i _ _ _ hscpos _, fun i _ h2' h3' => ?_⟩))
                  have : i = 0 := by omega
                  subst this
                  exact absurd h3' h1
                · simp only [h1, h2, h3, ↓reduceIte] at h
                  rcases hz with hz | ⟨i, h1', h2', h3'⟩
                  · rw [hfr z hz] at h; cases h
                  · have : i = 0 := by omega
                    subst this; exact absurd h3' h1
        · refine writerWP_mono (writerWP_handleFullWith_rootSpace_term up (X 0) (Nn 0) ins c w hlk hmade
            hsp hxn) ?_
          rintro _ w' ⟨_, _, _, _, h'next, h'n⟩
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro z hzl hz
            have h1 : z ≠ X 0 := hz 0 (Nat.le_refl _) (Nat.le_refl _)
            have h2 : z ≠ w.next := by omega
            have h3 : z ≠ w.next + 2 := by omega
            have h4 : z ≠ w.next + 2 + 2 := by omega
            rw [h'n]
            simp only [h1, h2, h3, h4, ↓reduceIte]
          · intro z hz
            have h1 : z ≠ X 0 := by omega
            have h2 : z ≠ w.next := by omega
            have h3 : z ≠ w.next + 2 := by omega
            have h4 : z ≠ w.next + 2 + 2 := by omega
            rw [h'n]
            simp only [h1, h2, h3, h4, ↓reduceIte]
            exact hfr z (by omega)
          · intro z zn h hz
            rw [h'n] at h
            by_cases h1 : z = X 0
            · simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBp 0 (by omega) (by omega)⟩
              exact Or.inr (Or.inl ⟨0, Nat.le_refl _, Nat.le_refl _, h1, rfl, hmade⟩)
            · have hnot : ∀ i, 0 ≤ i → i ≤ 0 → z = X i → False := fun i _ h2' h3' => by
                have : i = 0 := by omega
                subst this; exact h1 h3'
              by_cases h2 : z = w.next
              · subst h2
                simp only [h1, ↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, (hBh 0 (by omega) (by omega) ins hins.length).1⟩
                exact Or.inr (Or.inr (Or.inl ⟨hmono _ hF, fun i h1' h2' h3' =>
                  absurd (hnot i h1' h2' h3') id⟩))
              · by_cases h3 : z = w.next + 2
                · subst h3
                  simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  refine ⟨?_, (hBh 0 (by omega) (by omega) ins hins.length).2⟩
                  exact Or.inr (Or.inr (Or.inl ⟨hmono _ hS, fun i h1' h2' h3' =>
                    absurd (hnot i h1' h2' h3') id⟩))
                · by_cases h4 : z = w.next + 2 + 2
                  · subst h4
                    simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h
                    subst h
                    refine ⟨?_, hBr _ _ _ hscpos⟩
                    exact Or.inr (Or.inr (Or.inl ⟨shadowOK_root c.i _ _ _ hscpos _, fun i h1' h2' h3' =>
                      absurd (hnot i h1' h2' h3') id⟩))
                  · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                    rcases hz with hz | ⟨i, h1', h2', h3'⟩
                    · rw [hfr z hz] at h; cases h
                    · exact absurd (hnot i h1' h2' h3') id
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn 0).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn 0).lastVersion c.i).size
        · exact hSPACE0 _ hsp
        · exact hTIME0 _ false (by
            simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
            exact hsp)
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hTIME0 _ true (by simp)
  | succ e ih =>
    intro hD w ins hins hinsS hpath hS2 hfr
    obtain ⟨hlk, hxn⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, hqn⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) = false
    · exact hroomCase (e + 1) hD w ins hS2 hroom.1 hroom.2 hfr
    · have hNR : ¬ ChainRoom c (Nn (s + (e + 1))) := fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩
      have hj : s < s + (e + 1) := by omega
      have hpq : (w.path[s + e]?).map (·.2) = some (X (s + e)) := by
        rw [hpath]; exact hX (s + e) (by omega) (by omega)
      have hpk : w.path[s + e + 1]? = some (some (K (s + (e + 1))), X (s + (e + 1))) := by
        rw [hpath]; exact hK (s + (e + 1)) hj hD
      have hkl : (K (s + (e + 1)), X (s + (e + 1))) ∈ (Nn (s + e)).liveAt c.i := by
        have := hlinkK (s + (e + 1)) hj hD; simpa using this
      have hqx : X (s + e) ≠ X (s + (e + 1)) := by
        intro h; have := hdist _ _ (by omega) (by omega) (by omega) hD h; omega
      have hxt := htimes (s + (e + 1)) (by omega) hD
      have hqt := htimes (s + e) (by omega) (by omega)
      have hKuniq : ∀ y, (K (s + (e + 1)), y) ∈ (Nn (s + e)).liveAt c.i → y = X (s + (e + 1)) :=
        fun y hy => liveAt_cv_unique _ c.i hqt _ _ _ hy hkl
      have hXne : ∀ i, s ≤ i → i ≤ s + e → X i ≠ X (s + (e + 1)) := by
        intro i h1 h2 he; have := hdist _ _ h1 (by omega) (by omega) hD he; omega
      -- after the parent's step: the cascade's post
      have hfin : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (w2 w3 : W),
          (ins'.map Prod.fst).Nodup →
          (∀ q ∈ ins', ∀ y, (q.1, y) ∈ (Nn (s + e)).liveAt c.i →
            q.1 = K (s + (e + 1)) ∧ y = X (s + (e + 1)) ∧ (Nn (s + (e + 1))).firstTime ≠ some c.i) →
          w.next ≤ w1.next →
          (∀ z, z < w.next → z ≠ X (s + (e + 1)) → w1.nodes.lookup z = w.nodes.lookup z) →
          (∀ z zn, w.next ≤ z → z < w1.next → w1.nodes.lookup z = some zn →
            ShadowOK c.i zn (ChainShadow c X Nn s (s + (e + 1)) ins) ∧ Bnd zn) →
          ShapePostG Bnd c X K Nn s (s + e) ins' w1 w2 →
          w3.next = w2.next →
          (∀ z, z ≠ X (s + (e + 1)) → w3.nodes.lookup z = w2.nodes.lookup z) →
          (∀ zn, w3.nodes.lookup (X (s + (e + 1))) = some zn →
            CascadeNodeShape c X K Nn s (s + (e + 1)) ins (X (s + (e + 1))) zn ∧ Bnd zn) →
          ShapePostG Bnd c X K Nn s (s + (e + 1)) ins w w3 := by
        intro w1 ins' w2 w3 hnd hpar h1next h1low h1new ⟨h2next, h2frame, h2fr, h2sh⟩ h3next h3n h3x
        refine ⟨by omega, ?_, ?_, ?_⟩
        · intro z hz hzX
          have hzx := hzX (s + (e + 1)) (by omega) (Nat.le_refl _)
          rw [h3n z hzx, h2frame z (by omega) (fun i h1 h2 => hzX i h1 (by omega)), h1low z hz hzx]
        · intro z hz
          have hzx : z ≠ X (s + (e + 1)) := by intro h; subst h; omega
          rw [h3n z hzx]; exact h2fr z (by omega)
        · intro z zn h hz
          by_cases hzx : z = X (s + (e + 1))
          · subst hzx; exact h3x zn h
          · rw [h3n z hzx] at h
            by_cases hin : w1.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i
            · exact ⟨cascadeShape_lift c X K Nn s (s + e) ins ins' z zn hnd hpar hzx (by omega)
                (h2sh z zn h hin).1, (h2sh z zn h hin).2⟩
            · have hzw : w.next ≤ z ∧ z < w1.next := by
                rcases hz with hz | ⟨i, h1, h2, h3⟩
                · refine ⟨hz, ?_⟩
                  rcases Nat.lt_or_ge z w1.next with h' | h'
                  · exact h'
                  · exact absurd (Or.inl h') hin
                · exfalso
                  rcases Nat.lt_or_ge i (s + (e + 1)) with h' | h'
                  · exact hin (Or.inr ⟨i, h1, by omega, h3⟩)
                  · have : i = s + (e + 1) := by omega
                    subst this; exact hzx h3
              have hz1 : w1.nodes.lookup z = some zn := by
                rw [← h2frame z hzw.2 (fun i h1 h2 he => by
                  have := (hS2 i h1 (by omega)).2; rw [← he] at this; omega)]
                exact h
              refine ⟨?_, (h1new z zn hzw.1 hzw.2 hz1).2⟩
              refine Or.inr (Or.inr (Or.inl ⟨(h1new z zn hzw.1 hzw.2 hz1).1, fun i h1 h2 h3 => ?_⟩))
              exfalso
              have := (hS2 i h1 h2).2; rw [← h3] at this; omega
      -- the time split
      have hTIME : ∀ compact : Bool,
          (!compact && decide (((Nn (s + (e + 1))).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) compact) c w (fun _ w' =>
            ShapePostG Bnd c X K Nn s (s + (e + 1)) ins w w') := by
        intro compact hcs
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termN _ (s + e) (X (s + (e + 1)))
            (X (s + e)) (Nn (s + (e + 1))) (Nn (s + e)) ins compact c w hlk hlq hpq hmade hcs) ?_
          rintro _ w' ⟨l, _, _, _, _, ⟨more, hmore, hnd⟩, _, _, _, h'next, _, h'n⟩
          refine ⟨by omega, ?_, ?_, ?_⟩
          · intro z _ hz
            rw [h'n, lookup_upsert]
            simp only [hz (s + (e + 1)) (by omega) (Nat.le_refl _), ↓reduceIte]
          · intro z hz
            rw [h'next] at hz
            have hzx : z ≠ X (s + (e + 1)) := by intro h; subst h; omega
            rw [h'n, lookup_upsert]
            simp only [hzx, ↓reduceIte]
            exact hfr z hz
          · intro z zn h hz
            rw [h'n, lookup_upsert] at h
            by_cases hzx : z = X (s + (e + 1))
            · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBn _ more hmore hnd⟩
              refine Or.inr (Or.inr (Or.inl ⟨by rw [hmore]; exact shadowOK_newKlongs c.i _ more hnd _,
                fun i h1 h2 h3 => ?_⟩))
              have := hdist _ _ h1 (by omega) (by omega) hD (h3.symm.trans hzx)
              subst this; exact hmade
            · simp only [hzx, ↓reduceIte] at h
              rcases hz with hz | ⟨i, h1, h2, h3⟩
              · rw [hfr z hz] at h; cases h
              · rw [h3, (hS2 i h1 h2).1] at h
                cases h
                refine ⟨?_, hBc i h1 (by omega)⟩
                exact Or.inl ⟨i, h1, h2, h3, rfl⟩
        · apply writerWP_handleFullWith_time_upN (s + e) (X (s + (e + 1))) (X (s + e))
            (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins compact c w hlk hlq hmade hcs hpq hpk
          intro l _ _ _ _ ⟨more, hmore, hnd⟩ w1 h1n _ _ h1path h1next _
          have hfree0 := hfr w.next (Nat.le_refl _)
          have h1lk : ∀ z, z ≠ w.next → w1.nodes.lookup z = w.nodes.lookup z := fun z hz => by
            rw [h1n]; exact lookup_append_single_ne _ _ _ _ hz
          refine writerWP_mono (ih (by omega) w1 [(K (s + (e + 1)), w.next)] (Or.inl ⟨_, _, rfl⟩)
            (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
          · intro i h1 h2
            have hlt := (hS2 i h1 (by omega)).2
            exact ⟨by rw [h1lk _ (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
          · intro z hz
            rw [h1next] at hz
            rw [h1lk z (by omega)]; exact hfr z (by omega)
          · intro _ w2 hpost
            have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
              rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
                h1lk _ (by omega), hlk]
            simp only [writerWP_bind]
            rw [writerWP_getNode_known _ _ c w2 hlk2]
            simp only [putNode, writerWP_modify]
            refine hfin w1 [(K (s + (e + 1)), w.next)] w2 _ (by simp) ?_ (by omega) ?_ ?_ hpost rfl ?_ ?_
            · intro q hq y hy
              simp only [List.mem_singleton] at hq
              subst hq
              exact ⟨rfl, hKuniq y hy, hmade⟩
            · intro z hz _; exact h1lk z (by omega)
            · intro z zn h1 h2 h3
              rw [h1next] at h2
              have hzn : z = w.next := by
                refine Classical.byContradiction (fun hne => ?_)
                rw [h1lk z hne, hfr z h1] at h3; cases h3
              subst hzn
              rw [h1n, lookup_append_single_self _ _ _ hfree0] at h3
              cases h3
              refine ⟨?_, hBn _ more hmore hnd⟩
              rw [hmore]; exact shadowOK_newKlongs c.i _ more hnd _
            · intro z hz
              show (upsert w2.nodes _ _).lookup z = _
              rw [lookup_upsert]; simp only [hz, ↓reduceIte]
            · intro zn h
              change (upsert w2.nodes _ _).lookup _ = some zn at h
              rw [lookup_upsert] at h
              simp only [↓reduceIte, Option.some.injEq] at h
              subst h
              refine ⟨?_, hBp (s + (e + 1)) (by omega) hD⟩
              exact Or.inr (Or.inl ⟨s + (e + 1), by omega, Nat.le_refl _, rfl, rfl, hmade⟩)
      -- the space split
      have hSPACE : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) false) c w (fun _ w' =>
            ShapePostG Bnd c X K Nn s (s + (e + 1)) ins w w') := by
        intro hsp
        have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
        obtain ⟨hF, hS, hscpos, ⟨ysc, hscmem⟩, ⟨q0, hq0, hq0lt⟩⟩ :=
          halves_node (Nn (s + (e + 1))) c.i ins hxt h2l hinsS
        have hmono : ∀ zn, ShadowOK c.i zn
            (fun y => ∃ c0, (c0, y) ∈ (Nn (s + (e + 1))).liveAt c.i ∧ c0 ∈ ins.map Prod.fst) →
            ShadowOK c.i zn (ChainShadow c X Nn s (s + (e + 1)) ins) :=
          fun zn h => h.mono (fun y hy => Or.inr hy)
        have hord1 := hord (s + (e + 1)) hj hD hNR
        have hKsc : (Nn (s + e)).leaf = false → K (s + (e + 1)) <
            (halves (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins).2.2 := by
          intro hql
          have h := hord1 (by simpa using hql) hsp
          by_cases hl : (Nn (s + (e + 1))).leaf = true
          · have h' := h q0.1 q0.2 hq0
            rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h'
            omega
          · have h' := h _ _ hscmem
            rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h'
            omega
        have hscpar : (Nn (s + e)).leaf = false → ∀ y,
            ((halves (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins).2.2, y) ∉
              (Nn (s + e)).liveAt c.i := by
          intro hql y hy
          have hr := (hrange (s + (e + 1)) hj hD hNR (by simpa using hql) _ _ hscmem hscpos).2
          rw [KNode.liveAt_of_times _ c.i hqt] at hy
          have := hr _ _ (by simpa using hy) (hKsc hql)
          omega
        have hfree0 := hfr w.next (Nat.le_refl _)
        have hfree2 := hfr (w.next + 2) (by omega)
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · cases hqlf : (Nn (s + e)).leaf with
          | false =>
            apply writerWP_handleFullWith_spaceInPlace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) ins c w hlk hlq hqlf hmade hsp hpq hxn
            intro w1 h1n _ _ h1path h1next _
            have h1lk : ∀ z, z ≠ X (s + (e + 1)) → z ≠ w.next → w1.nodes.lookup z = w.nodes.lookup z :=
              fun z h1 h2 => by rw [h1n]; simp only [h1, h2, ↓reduceIte]
            refine writerWP_mono (ih (by omega) w1 [((halves (Nn (s + (e + 1))).leaf c.i
              ((Nn (s + (e + 1))).lastVersion c.i) ins).2.2, w.next)] (Or.inl ⟨_, _, rfl⟩)
              (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
            · intro i h1 h2
              have hlt := (hS2 i h1 (by omega)).2
              exact ⟨by rw [h1lk _ (hXne i h1 h2) (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
            · intro z hz
              rw [h1next] at hz
              rw [h1lk z (by omega) (by omega)]; exact hfr z (by omega)
            · intro _ w2 hpost
              refine hfin w1 _ w2 w2 (by simp) ?_ (by omega) ?_ ?_ hpost rfl (fun _ _ => rfl) ?_
              · intro q hq y hy
                simp only [List.mem_singleton] at hq
                subst hq
                exact absurd hy (hscpar hqlf y)
              · intro z hz hzx; exact h1lk z hzx (by omega)
              · intro z zn h1 h2 h3
                rw [h1next] at h2
                have hzx : z ≠ X (s + (e + 1)) := by omega
                by_cases hzn : z = w.next
                · subst hzn
                  rw [h1n] at h3
                  simp only [hzx, ↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).2⟩
                  exact hmono _ hS
                · rw [h1lk z hzx hzn, hfr z h1] at h3; cases h3
              · intro zn h
                rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm), h1n] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).1⟩
                refine Or.inr (Or.inr (Or.inl ⟨hmono _ hF, fun i h1 h2 h3 => ?_⟩))
                have := hdist _ _ h1 (by omega) (by omega) hD h3.symm
                subst this; exact hmade
          | true =>
            refine writerWP_mono (writerWP_handleFullWith_segSpaceInPlace_term (s + e) (X (s + (e + 1)))
              (X (s + e)) (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqx hqlf
              hmade hsp hpq hpk hxn hqn hfree2) ?_
            rintro _ w' ⟨idx, hidx, _, _, _, _, h'next, h'n⟩
            refine ⟨by omega, ?_, ?_, ?_⟩
            · intro z hzl hz
              have h1 : z ≠ X (s + (e + 1)) := hz _ (by omega) (Nat.le_refl _)
              have h2 : z ≠ X (s + e) := hz _ (by omega) (by omega)
              have h3 : z ≠ w.next := by omega
              have h4 : z ≠ w.next + 2 := by omega
              rw [h'n]
              simp only [h1, h2, h3, h4, ↓reduceIte]
            · intro z hz
              have h1 : z ≠ X (s + (e + 1)) := by omega
              have h2 : z ≠ X (s + e) := by omega
              have h3 : z ≠ w.next := by omega
              have h4 : z ≠ w.next + 2 := by omega
              rw [h'n]
              simp only [h1, h2, h3, h4, ↓reduceIte]
              exact hfr z (by omega)
            · intro z zn h hz
              rw [h'n] at h
              by_cases h1 : z = X (s + (e + 1))
              · subst h1
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).1⟩
                refine Or.inr (Or.inr (Or.inl ⟨hmono _ hF, fun i h1 h2 h3 => ?_⟩))
                have := hdist _ _ h1 (by omega) (by omega) hD h3.symm
                subst this; exact hmade
              · by_cases h2 : z = X (s + e)
                · subst h2
                  simp only [h1, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  refine ⟨?_, hBe (s + e) (by omega) (by omega) _ _⟩
                  exact Or.inr (Or.inr (Or.inr ⟨s + e, by omega, by omega, rfl, Or.inr (Or.inr
                    ⟨by omega, K (s + (e + 1)), idx, w.next + 2, hidx, rfl, hmade, hqlf⟩)⟩))
                · have hnot : ∀ i, s ≤ i → i ≤ s + (e + 1) → z = X i → z = X i ∧ i ≤ s + e := by
                    intro i h1' h2' h3'
                    refine ⟨h3', ?_⟩
                    rcases Nat.lt_or_ge i (s + (e + 1)) with h' | h'
                    · omega
                    · have : i = s + (e + 1) := by omega
                      subst this; exact absurd h3' h1
                  by_cases h3 : z = w.next
                  · subst h3
                    simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                    subst h
                    refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).2⟩
                    refine Or.inr (Or.inr (Or.inl ⟨hmono _ hS, fun i h1' h2' h3' => ?_⟩))
                    exfalso
                    have := (hS2 i h1' h2').2; rw [← h3'] at this; omega
                  · by_cases h4 : z = w.next + 2
                    · subst h4
                      simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h
                      subst h
                      refine ⟨?_, hBr _ _ _ hscpos⟩
                      refine Or.inr (Or.inr (Or.inl ⟨shadowOK_root c.i _ _ _ hscpos _,
                        fun i h1' h2' h3' => ?_⟩))
                      exfalso
                      have := (hS2 i h1' h2').2; rw [← h3'] at this; omega
                    · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                      rcases hz with hz | ⟨i, h1', h2', h3'⟩
                      · rw [hfr z hz] at h; cases h
                      · rw [h3', (hS2 i h1' h2').1] at h
                        cases h
                        refine ⟨?_, hBc i h1' (by omega)⟩
                        exact Or.inl ⟨i, h1', h2', h3', rfl⟩
        · cases hqlf : (Nn (s + e)).leaf with
          | false =>
            apply writerWP_handleFullWith_space_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqlf hmade hsp hpq hpk
            intro w1 h1n _ _ h1path h1next _
            have h1lk : ∀ z, z ≠ w.next → z ≠ w.next + 2 → w1.nodes.lookup z = w.nodes.lookup z :=
              fun z h1 h2 => by rw [h1n]; simp only [h1, h2, ↓reduceIte]
            have hKsc' := hKsc hqlf
            refine writerWP_mono (ih (by omega) w1 _ (Or.inr ⟨_, _, _, _, rfl, Nat.le_of_lt hKsc',
              fun c'' z'' hm hlt => (hrange (s + (e + 1)) hj hD hNR (by simpa using hqlf) _ _ hscmem
                hscpos).2 c'' z'' (by simpa using hm) hlt⟩)
              (List.pairwise_cons.mpr ⟨fun a' ha' => by
                simp only [List.mem_singleton] at ha'; subst ha'; exact hKsc',
                List.pairwise_singleton _ _⟩)
              (by rw [h1path, hpath]) ?_ ?_) ?_
            · intro i h1 h2
              have hlt := (hS2 i h1 (by omega)).2
              exact ⟨by rw [h1lk _ (by omega) (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
            · intro z hz
              rw [h1next] at hz
              rw [h1lk z (by omega) (by omega)]; exact hfr z (by omega)
            · intro _ w2 hpost
              have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
                rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
                  h1lk _ (by omega) (by omega), hlk]
              simp only [writerWP_bind]
              rw [writerWP_getNode_known _ _ c w2 hlk2]
              simp only [putNode, writerWP_modify]
              refine hfin w1 _ w2 _ ?_ ?_ (by omega) ?_ ?_ hpost rfl ?_ ?_
              · simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                  List.not_mem_nil, or_false, not_false_eq_true, List.nodup_nil, and_true]
                omega
              · intro q hq y hy
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with hq | hq
                · subst hq; exact ⟨rfl, hKuniq y hy, hmade⟩
                · subst hq; exact absurd hy (hscpar hqlf y)
              · intro z hz _; exact h1lk z (by omega) (by omega)
              · intro z zn h1 h2 h3
                rw [h1next] at h2
                by_cases hz0 : z = w.next
                · subst hz0
                  rw [h1n] at h3
                  simp only [↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).1⟩
                  exact hmono _ hF
                · by_cases hz2 : z = w.next + 2
                  · subst hz2
                    rw [h1n] at h3
                    simp only [hz0, ↓reduceIte, Option.some.injEq] at h3
                    subst h3
                    refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).2⟩
                    exact hmono _ hS
                  · rw [h1lk z hz0 hz2, hfr z h1] at h3; cases h3
              · intro z hz
                show (upsert w2.nodes _ _).lookup z = _
                rw [lookup_upsert]; simp only [hz, ↓reduceIte]
              · intro zn h
                change (upsert w2.nodes _ _).lookup _ = some zn at h
                rw [lookup_upsert] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, hBp (s + (e + 1)) (by omega) hD⟩
                exact Or.inr (Or.inl ⟨s + (e + 1), by omega, Nat.le_refl _, rfl, rfl, hmade⟩)
          | true =>
            apply writerWP_handleFullWith_segSpace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqlf hmade hsp hpq hpk
            intro w1 h1n _ _ h1path h1next _
            have h1lk : ∀ z, z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
                w1.nodes.lookup z = w.nodes.lookup z :=
              fun z h1 h2 h3 => by rw [h1n]; simp only [h1, h2, h3, ↓reduceIte]
            refine writerWP_mono (ih (by omega) w1 [(K (s + (e + 1)), w.next + 2 + 2)]
              (Or.inl ⟨_, _, rfl⟩) (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
            · intro i h1 h2
              have hlt := (hS2 i h1 (by omega)).2
              exact ⟨by rw [h1lk _ (by omega) (by omega) (by omega)]; exact (hS2 i h1 (by omega)).1,
                by omega⟩
            · intro z hz
              rw [h1next] at hz
              rw [h1lk z (by omega) (by omega) (by omega)]; exact hfr z (by omega)
            · intro _ w2 hpost
              have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
                rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
                  h1lk _ (by omega) (by omega) (by omega), hlk]
              simp only [writerWP_bind]
              rw [writerWP_getNode_known _ _ c w2 hlk2]
              simp only [putNode, writerWP_modify]
              refine hfin w1 _ w2 _ (by simp) ?_ (by omega) ?_ ?_ hpost rfl ?_ ?_
              · intro q hq y hy
                simp only [List.mem_singleton] at hq
                subst hq
                exact ⟨rfl, hKuniq y hy, hmade⟩
              · intro z hz _; exact h1lk z (by omega) (by omega) (by omega)
              · intro z zn h1 h2 h3
                rw [h1next] at h2
                by_cases hz0 : z = w.next
                · subst hz0
                  rw [h1n] at h3
                  simp only [↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).1⟩
                  exact hmono _ hF
                · by_cases hz2 : z = w.next + 2
                  · subst hz2
                    rw [h1n] at h3
                    simp only [hz0, ↓reduceIte, Option.some.injEq] at h3
                    subst h3
                    refine ⟨?_, (hBh (s + (e + 1)) (by omega) hD ins hins.length).2⟩
                    exact hmono _ hS
                  · by_cases hz4 : z = w.next + 2 + 2
                    · subst hz4
                      rw [h1n] at h3
                      simp only [hz0, hz2, ↓reduceIte, Option.some.injEq] at h3
                      subst h3
                      refine ⟨?_, hBr _ _ _ hscpos⟩
                      exact shadowOK_root c.i _ _ _ hscpos _
                    · rw [h1lk z hz0 hz2 hz4, hfr z h1] at h3; cases h3
              · intro z hz
                show (upsert w2.nodes _ _).lookup z = _
                rw [lookup_upsert]; simp only [hz, ↓reduceIte]
              · intro zn h
                change (upsert w2.nodes _ _).lookup _ = some zn at h
                rw [lookup_upsert] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                refine ⟨?_, hBp (s + (e + 1)) (by omega) hD⟩
                exact Or.inr (Or.inl ⟨s + (e + 1), by omega, Nat.le_refl _, rfl, rfl, hmade⟩)
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn (s + (e + 1))).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size
        · exact hSPACE hsp
        · apply hTIME false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
          exact hsp
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hTIME true (by simp)

set_option maxHeartbeats 3200000 in
/-- The shapes of the nodes that a cascade of splits makes or changes (bergdb
024-12; for prover putinv's take-back (C)), on the premises of
`writerWP_appendKlongs_chainGRV` that concern the writer's nodes, with
`ChainOrd` at every level and the klongs put ordered: after `appendKlongs (s + e)`
every node with an id from the next id on or on the chain is a chain node the
cascade did not reach, a chain node left behind, a node of time c.i whose
shadowed klongs name a split child that was copied or a live klong of X (s + e)
for a compare value put there (`ChainShadow`), or the node where the cascade
ends (`CascadeTop`). -/
theorem writerWP_appendKlongs_chainShape (c : Ctx)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i') :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → ins.Pairwise (fun a b => a.1 < b.1) → w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        ShapePost c X K Nn s (s + e) ins w w') := by
  intro e hD w ins h1 h2 h3 h4 h5
  refine writerWP_mono (writerWP_appendKlongs_chainShapeG c path0 s D X K Nn hX hK hlinkK hrange hlen
    hord htimes htop hdist (fun _ => True) (fun _ _ _ => trivial) (fun _ _ => trivial)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ => ⟨trivial, trivial⟩) (fun _ _ _ _ => trivial)
    (fun _ _ _ => trivial) (fun _ _ _ _ _ => trivial) e hD w ins h1 h2 h3 h4 h5) ?_
  intro _ _ ⟨a, b, d, f⟩
  exact ⟨a, b, d, fun z zn h hz => (f z zn h hz).1⟩
/-- The cascade's dead klongs (bergdb 024-12, `QDead` of (2) and (3c)): with
theta 0 or at least 2, every node the cascade makes or changes holds at most
theta dead klongs when the chain's nodes do. A half holds at most as many as the
klongs put into it, at most 2; a copy of a last version and a new root none; a
chain node left behind no more than the node; the cascade's top takes klongs
only when `deadOver` lets them through, or points one in place. -/
theorem writerWP_appendKlongs_chainDead (c : Ctx)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0)
    (hdc : ∀ i, s ≤ i → i ≤ D → c.p.theta ≠ 0 → (Nn i).deadCount ≤ c.p.theta)
    (hwf : ∀ i, s ≤ i → i ≤ D → klongsWf (Nn i).ks = true) :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → ins.Pairwise (fun a b => a.1 < b.1) → w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        ShapePostG (fun n => c.p.theta ≠ 0 → n.deadCount ≤ c.p.theta) c X K Nn s (s + e) ins w w') :=
  writerWP_appendKlongs_chainShapeG c path0 s D X K Nn hX hK hlinkK hrange hlen hord htimes htop hdist
    (fun n => c.p.theta ≠ 0 → n.deadCount ≤ c.p.theta) hdc
    (fun n hd h0 => deadOver_false c.p n hd h0)
    (fun n more h hnd _ => by
      have h1 := KNode.newKlongs_deadCount n.leaf c.i more hnd
      rw [← h] at h1
      have h2 : n.deadCount = 0 := h1
      omega)
    (fun i h1 h2 ins hl => by
      have hh := halves_normalized_deadCount_le (Nn i) c.i (Nn i).lastBitmap ins
      exact ⟨fun h0 => by
          have := hh.1
          have : (halves (Nn i).leaf c.i ((Nn i).lastVersion c.i) ins).1.deadCount ≤ ins.length := hh.1
          rcases hth with h | h <;> omega,
        fun h0 => by
          have : (halves (Nn i).leaf c.i ((Nn i).lastVersion c.i) ins).2.1.deadCount ≤ ins.length := hh.2
          rcases hth with h | h <;> omega⟩)
    (fun a b sc hsc _ => by rw [KNode.deadCount_newRoot c.i a b sc hsc]; exact Nat.zero_le _)
    (fun i h1 h2 h0 => Nat.le_trans (KNode.deadCount_toPrev_le (Nn i) _ (hwf i h1 h2)) (hdc i h1 h2 h0))
    (fun i h1 h2 idx r h0 => by rw [KNode.deadCount_repoint]; exact hdc i h1 h2 h0)

set_option maxHeartbeats 3200000 in
/-- The nodes that a cascade makes or changes link a node y that no chain node's
klong names and that is not on the chain only by a klong put into the bottom
node, and then have the bottom node's leaf flag (`LeafTargets`); on the
premises of `writerWP_appendKlongs_chainShape`. -/
theorem writerWP_appendKlongs_chainLeafTargets (c : Ctx)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode)
    (hX : ∀ i, s ≤ i → i ≤ D → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → 2 ≤ (Nn i).live.length)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (htimes : ∀ i, s ≤ i → i ≤ D → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i') :
    ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      InsOK (Nn (s + e)) ins → ins.Pairwise (fun a b => a.1 < b.1) → w.path = path0 →
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next) →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        LeafTargets c X Nn s (s + e) ins w w') := by
  -- the room case at any level
  have hroomCase : ∀ e, s + e ≤ D → ∀ (w : W) (ins : List (Nat × NodeId)),
      (∀ i, s ≤ i → i ≤ s + e → w.nodes.lookup (X i) = some (Nn i) ∧ X i < w.next) →
      (Nn (s + e)).size + ins.length + 1 ≤ c.p.M →
      deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + e))) = false →
      (∀ z, w.next ≤ z → w.nodes.lookup z = none) →
      WriterWP (appendKlongs (s + e) (X (s + e)) ins) c w (fun _ w' =>
        LeafTargets c X Nn s (s + e) ins w w') := by
    intro e _ w ins hS2 hroom hdead hfr
    obtain ⟨hlk, hxn⟩ := hS2 (s + e) (by omega) (Nat.le_refl _)
    refine writerWP_mono (writerWP_appendKlongs_addKeys (s + e) (X (s + e)) (Nn (s + e)) ins c w hlk
      hroom hdead) ?_
    intro _ w' hw'
    subst hw'
    intro y _ hNy _ z zn cv h hz hcv
    change (upsert w.nodes _ _).lookup z = some zn at h
    rw [lookup_upsert] at h
    by_cases hzx : z = X (s + e)
    · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact leafTarget_of_keys c.i (Nn (s + e)) _ ins y (hNy (s + e) (by omega) (Nat.le_refl _))
        (fun cv' y' hk => (addKeys_key_mem c.i ins _ cv' y' hk).imp (fun h => ⟨cv', h⟩)
          (fun h => ⟨cv', h⟩)) (KNode.addKeys_leaf c.i ins _) cv hcv
    · simp only [hzx, ↓reduceIte] at h
      exfalso
      rcases hz with hz | ⟨i, h1, h2, h3⟩
      · have hz' : w.next ≤ z := hz
        rw [hfr z hz'] at h; cases h
      · rw [h3, (hS2 i h1 h2).1] at h
        cases h
        exact leafTarget_none c.i _ y (fun cv' hk => hNy i h1 h2 cv' hk) cv hcv
  intro e
  induction e with
  | zero =>
    intro hD w ins hins hinsS hpath hS2 hfr
    by_cases hroom : (Nn (s + 0)).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + 0))) = false
    · exact hroomCase 0 hD w ins hS2 hroom.1 hroom.2 hfr
    · have hs0 : s = 0 := by
        rcases htop with h | h
        · exfalso
          exact hroom ⟨by have := h.1; have := hins.length; simp only [Nat.add_zero]; omega,
            by simpa using h.2 ins hins.length⟩
        · exact h
      subst hs0
      simp only [Nat.add_zero] at hroom hins hS2 ⊢
      obtain ⟨hlk, hxn⟩ := hS2 0 (Nat.le_refl _) (Nat.le_refl _)
      have hNR : ¬ ChainRoom c (Nn 0) := fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩
      have hxt := htimes 0 (Nat.le_refl _) (by omega)
      have hfree0 := hfr w.next (Nat.le_refl _)
      have hfree2 := hfr (w.next + 2) (by omega)
      have hTIME0 : ∀ (up : NodeId → List (Nat × NodeId) → M Unit) (compact : Bool),
          (!compact && decide (((Nn 0).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith up 0 (X 0) ins ((Nn 0).lastVersion c.i) compact) c w (fun _ w' =>
            LeafTargets c X Nn 0 0 ins w w') := by
        intro up compact hcs
        by_cases hmade : (Nn 0).firstTime = some c.i
        · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_term0N up (X 0) (Nn 0) ins compact
            c w hlk hmade hcs) ?_
          rintro _ w' ⟨l, _, _, hl_times, hl_look, _, _, _, _, _, _, h'n⟩
          intro y _ hNy _ z zn cv h hz hcv
          rw [h'n, lookup_upsert] at h
          by_cases hzx : z = X 0
          · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
            subst h
            exact ⟨leafTarget_time c.i (Nn 0) l _ ins y (hNy 0 (Nat.le_refl _) (Nat.le_refl _)) hxt
              hl_times hl_look cv hcv, rfl⟩
          · simp only [hzx, ↓reduceIte] at h
            exfalso
            rcases hz with hz | ⟨i, h1, h2, h3⟩
            · rw [hfr z hz] at h; cases h
            · have : i = 0 := by omega
              subst this; exact hzx h3
        · refine writerWP_mono (writerWP_handleFullWith_rootTime_termN up (X 0) (Nn 0) ins compact c w
            hlk hmade hcs hxn hfree0) ?_
          rintro _ w' ⟨l, _, _, hl_times, hl_look, _, _, _, _, _, _, h'n⟩
          intro y hy hNy _ z zn cv h hz hcv
          rw [h'n] at h
          by_cases h1 : z = X 0
          · subst h1
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
              hNy 0 (Nat.le_refl _) (Nat.le_refl _) cv' (toPrev_key_mem _ _ _ _ hk)) cv hc)
          · by_cases h2 : z = w.next
            · subst h2
              simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact ⟨leafTarget_time c.i (Nn 0) l _ ins y (hNy 0 (Nat.le_refl _) (Nat.le_refl _)) hxt
                hl_times hl_look cv hcv, rfl⟩
            · simp only [h1, h2, ↓reduceIte] at h
              exfalso
              rcases hz with hz | ⟨i, h1', h2', h3'⟩
              · rw [hfr z hz] at h; cases h
              · have : i = 0 := by omega
                subst this; exact h1 h3'
      have hSPACE0 : ∀ (up : NodeId → List (Nat × NodeId) → M Unit),
          c.p.splitAbove < ((Nn 0).lastVersion c.i).size →
          WriterWP (handleFullWith up 0 (X 0) ins ((Nn 0).lastVersion c.i) false) c w (fun _ w' =>
            LeafTargets c X Nn 0 0 ins w w') := by
        intro up hsp
        have h2l := hlen 0 (Nat.le_refl _) (by omega) hNR hsp
        obtain ⟨hkF, hkS⟩ := halves_keys (Nn 0) c.i ins hxt h2l
        obtain ⟨hlF, hlS⟩ := halves_leaf_flags (Nn 0).leaf c.i ((Nn 0).lastVersion c.i) ins
        by_cases hmade : (Nn 0).firstTime = some c.i
        · refine writerWP_mono (writerWP_handleFullWith_rootSpaceInPlace_term up (X 0) (Nn 0) ins c w
            hlk hmade hsp hxn hfree2) ?_
          rintro _ w' ⟨_, _, _, _, _, h'n⟩
          intro y hy hNy hyX z zn cv h hz hcv
          have hNy0 := hNy 0 (Nat.le_refl _) (Nat.le_refl _)
          rw [h'n] at h
          by_cases h1 : z = X 0
          · subst h1
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            exact leafTarget_of_keys c.i (Nn 0) _ ins y hNy0 hkF hlF cv hcv
          · by_cases h2 : z = w.next
            · subst h2
              simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact leafTarget_of_keys c.i (Nn 0) _ ins y hNy0 hkS hlS cv hcv
            · by_cases h3 : z = w.next + 2
              · subst h3
                simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                subst h
                exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                  root_key_ne c.i _ _ y _ (hyX 0 (Nat.le_refl _) (Nat.le_refl _)) (by omega) cv' hk) cv hc)
              · simp only [h1, h2, h3, ↓reduceIte] at h
                exfalso
                rcases hz with hz | ⟨i, h1', h2', h3'⟩
                · rw [hfr z hz] at h; cases h
                · have : i = 0 := by omega
                  subst this; exact h1 h3'
        · refine writerWP_mono (writerWP_handleFullWith_rootSpace_term up (X 0) (Nn 0) ins c w hlk hmade
            hsp hxn) ?_
          rintro _ w' ⟨_, _, _, _, _, h'n⟩
          intro y hy hNy _ z zn cv h hz hcv
          have hNy0 := hNy 0 (Nat.le_refl _) (Nat.le_refl _)
          rw [h'n] at h
          by_cases h1 : z = X 0
          · subst h1
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
              hNy0 cv' (toPrev_key_mem _ _ _ _ hk)) cv hc)
          · by_cases h2 : z = w.next
            · subst h2
              simp only [h1, ↓reduceIte, Option.some.injEq] at h
              subst h
              exact leafTarget_of_keys c.i (Nn 0) _ ins y hNy0 hkF hlF cv hcv
            · by_cases h3 : z = w.next + 2
              · subst h3
                simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                subst h
                exact leafTarget_of_keys c.i (Nn 0) _ ins y hNy0 hkS hlS cv hcv
              · by_cases h4 : z = w.next + 2 + 2
                · subst h4
                  simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                    root_key_ne c.i _ _ y _ (by omega) (by omega) cv' hk) cv hc)
                · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                  exfalso
                  rcases hz with hz | ⟨i, h1', h2', h3'⟩
                  · rw [hfr z hz] at h; cases h
                  · have : i = 0 := by omega
                    subst this; exact h1 h3'
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn 0).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn 0).lastVersion c.i).size
        · exact hSPACE0 _ hsp
        · exact hTIME0 _ false (by
            simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
            exact hsp)
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn 0)) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hTIME0 _ true (by simp)
  | succ e ih =>
    intro hD w ins hins hinsS hpath hS2 hfr
    obtain ⟨hlk, hxn⟩ := hS2 (s + (e + 1)) (by omega) (Nat.le_refl _)
    obtain ⟨hlq, hqn⟩ := hS2 (s + e) (by omega) (by omega)
    by_cases hroom : (Nn (s + (e + 1))).size + ins.length + 1 ≤ c.p.M ∧
        deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) (Nn (s + (e + 1)))) = false
    · exact hroomCase (e + 1) hD w ins hS2 hroom.1 hroom.2 hfr
    · have hNR : ¬ ChainRoom c (Nn (s + (e + 1))) := fun ⟨h1, h2⟩ =>
        hroom ⟨by have := hins.length; omega, h2 ins hins.length⟩
      have hj : s < s + (e + 1) := by omega
      have hpq : (w.path[s + e]?).map (·.2) = some (X (s + e)) := by
        rw [hpath]; exact hX (s + e) (by omega) (by omega)
      have hpk : w.path[s + e + 1]? = some (some (K (s + (e + 1))), X (s + (e + 1))) := by
        rw [hpath]; exact hK (s + (e + 1)) hj hD
      have hqx : X (s + e) ≠ X (s + (e + 1)) := by
        intro h; have := hdist _ _ (by omega) (by omega) (by omega) hD h; omega
      have hxt := htimes (s + (e + 1)) (by omega) hD
      have hqt := htimes (s + e) (by omega) (by omega)
      have hXne : ∀ i, s ≤ i → i ≤ s + e → X i ≠ X (s + (e + 1)) := by
        intro i h1 h2 he; have := hdist _ _ h1 (by omega) (by omega) hD he; omega
      -- the inner call: its leaf targets and its frame
      have hin : ∀ (w1 : W) (ins' : List (Nat × NodeId)), InsOK (Nn (s + e)) ins' →
          ins'.Pairwise (fun a b => a.1 < b.1) → w1.path = path0 →
          (∀ i, s ≤ i → i ≤ s + e → w1.nodes.lookup (X i) = some (Nn i) ∧ X i < w1.next) →
          (∀ z, w1.next ≤ z → w1.nodes.lookup z = none) →
          WriterWP (appendKlongs (s + e) (X (s + e)) ins') c w1 (fun _ w2 =>
            LeafTargets c X Nn s (s + e) ins' w1 w2 ∧ ShapePost c X K Nn s (s + e) ins' w1 w2) :=
        fun w1 ins' a1 a2 a3 a4 a5 => writerWP_and (ih (by omega) w1 ins' a1 a2 a3 a4 a5)
          (writerWP_appendKlongs_chainShape c path0 s D X K Nn hX hK hlinkK hrange hlen hord htimes
            htop hdist e (by omega) w1 ins' a1 a2 a3 a4 a5)
      have hfinL : ∀ (w1 : W) (ins' : List (Nat × NodeId)) (w2 w3 : W),
          (∀ q ∈ ins', w.next ≤ q.2) → w.next ≤ w1.next →
          (∀ y, y < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → ∀ cv, Klong.key cv y ∉ (Nn i).ks) →
            (∀ i, s ≤ i → i ≤ s + (e + 1) → y ≠ X i) →
            ∀ z zn cv, w.next ≤ z → z < w1.next → w1.nodes.lookup z = some zn →
            (cv, y) ∈ zn.liveAt c.i → (∃ c', (c', y) ∈ ins) ∧ zn.leaf = (Nn (s + (e + 1))).leaf) →
          LeafTargets c X Nn s (s + e) ins' w1 w2 → ShapePost c X K Nn s (s + e) ins' w1 w2 →
          (∀ z, z ≠ X (s + (e + 1)) → w3.nodes.lookup z = w2.nodes.lookup z) →
          (∀ y, y < w.next → (∀ i, s ≤ i → i ≤ s + (e + 1) → ∀ cv, Klong.key cv y ∉ (Nn i).ks) →
            (∀ i, s ≤ i → i ≤ s + (e + 1) → y ≠ X i) →
            ∀ zn cv, w3.nodes.lookup (X (s + (e + 1))) = some zn → (cv, y) ∈ zn.liveAt c.i →
            (∃ c', (c', y) ∈ ins) ∧ zn.leaf = (Nn (s + (e + 1))).leaf) →
          LeafTargets c X Nn s (s + (e + 1)) ins w w3 := by
        intro w1 ins' w2 w3 hins' h1next h1newL h2L ⟨_, h2frame, _, _⟩ h3n h3xL
        intro y hy hNy hyX z zn cv h hz hcv
        by_cases hzx : z = X (s + (e + 1))
        · subst hzx; exact h3xL y hy hNy hyX zn cv h hcv
        · rw [h3n z hzx] at h
          by_cases hin : w1.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ s + e ∧ z = X i
          · obtain ⟨⟨c', hc'⟩, _⟩ := h2L y (by omega) (fun i h1 h2 => hNy i h1 (by omega))
              (fun i h1 h2 => hyX i h1 (by omega)) z zn cv h hin hcv
            have := hins' _ hc'
            simp only at this
            omega
          · have hzw : w.next ≤ z ∧ z < w1.next := by
              rcases hz with hz | ⟨i, h1, h2, h3⟩
              · refine ⟨hz, ?_⟩
                rcases Nat.lt_or_ge z w1.next with h' | h'
                · exact h'
                · exact absurd (Or.inl h') hin
              · exfalso
                rcases Nat.lt_or_ge i (s + (e + 1)) with h' | h'
                · exact hin (Or.inr ⟨i, h1, by omega, h3⟩)
                · have : i = s + (e + 1) := by omega
                  subst this; exact hzx h3
            have hz1 : w1.nodes.lookup z = some zn := by
              rw [← h2frame z hzw.2 (fun i h1 h2 he => by
                have := (hS2 i h1 (by omega)).2; rw [← he] at this; omega)]
              exact h
            exact h1newL y hy hNy hyX z zn cv hzw.1 hzw.2 hz1 hcv
      -- the time split
      have hTIME : ∀ compact : Bool,
          (!compact && decide (((Nn (s + (e + 1))).lastVersion c.i).size > c.p.splitAbove)) = false →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) compact) c w (fun _ w' =>
            LeafTargets c X Nn s (s + (e + 1)) ins w w') := by
        intro compact hcs
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · refine writerWP_mono (writerWP_handleFullWith_timeInPlace_termN _ (s + e) (X (s + (e + 1)))
            (X (s + e)) (Nn (s + (e + 1))) (Nn (s + e)) ins compact c w hlk hlq hpq hmade hcs) ?_
          rintro _ w' ⟨l, _, _, hl_times, hl_look, _, _, _, _, _, _, h'n⟩
          intro y _ hNy _ z zn cv h hz hcv
          rw [h'n, lookup_upsert] at h
          by_cases hzx : z = X (s + (e + 1))
          · simp only [hzx, ↓reduceIte, Option.some.injEq] at h
            subst h
            exact ⟨leafTarget_time c.i (Nn (s + (e + 1))) l _ ins y (hNy _ (by omega) (Nat.le_refl _))
              hxt hl_times hl_look cv hcv, rfl⟩
          · simp only [hzx, ↓reduceIte] at h
            exfalso
            rcases hz with hz | ⟨i, h1, h2, h3⟩
            · rw [hfr z hz] at h; cases h
            · rw [h3, (hS2 i h1 h2).1] at h
              cases h
              exact leafTarget_none c.i _ y (fun cv' hk => hNy i h1 h2 cv' hk) cv hcv
        · apply writerWP_handleFullWith_time_upN (s + e) (X (s + (e + 1))) (X (s + e))
            (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins compact c w hlk hlq hmade hcs hpq hpk
          intro l _ _ hl_times hl_look _ w1 h1n _ _ h1path h1next _
          have hfree0 := hfr w.next (Nat.le_refl _)
          have h1lk : ∀ z, z ≠ w.next → w1.nodes.lookup z = w.nodes.lookup z := fun z hz => by
            rw [h1n]; exact lookup_append_single_ne _ _ _ _ hz
          refine writerWP_mono (hin w1 [(K (s + (e + 1)), w.next)] (Or.inl ⟨_, _, rfl⟩)
            (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
          · intro i h1 h2
            have hlt := (hS2 i h1 (by omega)).2
            exact ⟨by rw [h1lk _ (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
          · intro z hz
            rw [h1next] at hz
            rw [h1lk z (by omega)]; exact hfr z (by omega)
          · intro _ w2 ⟨hL2, hpost⟩
            have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
              rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
                h1lk _ (by omega), hlk]
            simp only [writerWP_bind]
            rw [writerWP_getNode_known _ _ c w2 hlk2]
            simp only [putNode, writerWP_modify]
            refine hfinL w1 [(K (s + (e + 1)), w.next)] w2 _ (by simp) (by omega) ?_ hL2 hpost ?_ ?_
            · intro y _ hNy _ z zn cv h1 h2 h3 hcv
              rw [h1next] at h2
              have hzn : z = w.next := by
                refine Classical.byContradiction (fun hne => ?_)
                rw [h1lk z hne, hfr z h1] at h3; cases h3
              subst hzn
              rw [h1n, lookup_append_single_self _ _ _ hfree0] at h3
              cases h3
              exact ⟨leafTarget_time c.i (Nn (s + (e + 1))) l _ ins y (hNy _ (by omega) (Nat.le_refl _))
                hxt hl_times hl_look cv hcv, rfl⟩
            · intro z hz
              show (upsert w2.nodes _ _).lookup z = _
              rw [lookup_upsert]; simp only [hz, ↓reduceIte]
            · intro y _ hNy _ zn cv h hcv
              change (upsert w2.nodes _ _).lookup _ = some zn at h
              rw [lookup_upsert] at h
              simp only [↓reduceIte, Option.some.injEq] at h
              subst h
              exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                hNy _ (by omega) (Nat.le_refl _) cv' (toPrev_key_mem _ _ _ _ hk)) cv hc)
      -- the space split
      have hSPACE : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size →
          WriterWP (handleFullWith (fun q more => appendKlongs (s + e) q more) (s + e + 1)
            (X (s + (e + 1))) ins ((Nn (s + (e + 1))).lastVersion c.i) false) c w (fun _ w' =>
            LeafTargets c X Nn s (s + (e + 1)) ins w w') := by
        intro hsp
        have h2l := hlen (s + (e + 1)) (by omega) hD hNR hsp
        obtain ⟨_, _, hscpos, ⟨ysc, hscmem⟩, ⟨q0, hq0, hq0lt⟩⟩ :=
          halves_node (Nn (s + (e + 1))) c.i ins hxt h2l hinsS
        obtain ⟨hkF, hkS⟩ := halves_keys (Nn (s + (e + 1))) c.i ins hxt h2l
        obtain ⟨hlF, hlS⟩ := halves_leaf_flags (Nn (s + (e + 1))).leaf c.i
          ((Nn (s + (e + 1))).lastVersion c.i) ins
        have hord1 := hord (s + (e + 1)) hj hD hNR
        have hKsc : (Nn (s + e)).leaf = false → K (s + (e + 1)) <
            (halves (Nn (s + (e + 1))).leaf c.i ((Nn (s + (e + 1))).lastVersion c.i) ins).2.2 := by
          intro hql
          have h := hord1 (by simpa using hql) hsp
          by_cases hl : (Nn (s + (e + 1))).leaf = true
          · have h' := h q0.1 q0.2 hq0
            rw [ite_eq_left_of_eq_true _ _ (eq_true hl)] at h'
            omega
          · have h' := h _ _ hscmem
            rw [ite_eq_right_of_eq_false _ _ (eq_false hl)] at h'
            omega
        have hfree0 := hfr w.next (Nat.le_refl _)
        have hfree2 := hfr (w.next + 2) (by omega)
        by_cases hmade : (Nn (s + (e + 1))).firstTime = some c.i
        · cases hqlf : (Nn (s + e)).leaf with
          | false =>
            apply writerWP_handleFullWith_spaceInPlace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) ins c w hlk hlq hqlf hmade hsp hpq hxn
            intro w1 h1n _ _ h1path h1next _
            have h1lk : ∀ z, z ≠ X (s + (e + 1)) → z ≠ w.next → w1.nodes.lookup z = w.nodes.lookup z :=
              fun z h1 h2 => by rw [h1n]; simp only [h1, h2, ↓reduceIte]
            refine writerWP_mono (hin w1 [((halves (Nn (s + (e + 1))).leaf c.i
              ((Nn (s + (e + 1))).lastVersion c.i) ins).2.2, w.next)] (Or.inl ⟨_, _, rfl⟩)
              (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
            · intro i h1 h2
              have hlt := (hS2 i h1 (by omega)).2
              exact ⟨by rw [h1lk _ (hXne i h1 h2) (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
            · intro z hz
              rw [h1next] at hz
              rw [h1lk z (by omega) (by omega)]; exact hfr z (by omega)
            · intro _ w2 ⟨hL2, hpost⟩
              refine hfinL w1 _ w2 w2 (by simp) (by omega) ?_ hL2 hpost (fun _ _ => rfl) ?_
              · intro y _ hNy _ z zn cv h1 h2 h3 hcv
                rw [h1next] at h2
                have hzx : z ≠ X (s + (e + 1)) := by omega
                by_cases hzn : z = w.next
                · subst hzn
                  rw [h1n] at h3
                  simp only [hzx, ↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkS hlS cv hcv
                · rw [h1lk z hzx hzn, hfr z h1] at h3; cases h3
              · intro y _ hNy _ zn cv h hcv
                rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm), h1n] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkF hlF cv hcv
          | true =>
            refine writerWP_mono (writerWP_handleFullWith_segSpaceInPlace_term (s + e) (X (s + (e + 1)))
              (X (s + e)) (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqx hqlf
              hmade hsp hpq hpk hxn hqn hfree2) ?_
            rintro _ w' ⟨idx, _, _, _, _, _, _, h'n⟩
            intro y hy hNy hyX z zn cv h hz hcv
            rw [h'n] at h
            by_cases h1 : z = X (s + (e + 1))
            · subst h1
              simp only [↓reduceIte, Option.some.injEq] at h
              subst h
              exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkF hlF cv hcv
            · by_cases h2 : z = X (s + e)
              · subst h2
                simp only [h1, ↓reduceIte, Option.some.injEq] at h
                subst h
                exfalso
                rcases repoint_key_mem _ _ _ cv y (KNode.liveAt_key_mem _ c.i cv y hcv) with
                  ⟨cv', hk⟩ | hk
                · exact hNy (s + e) (by omega) (by omega) cv' hk
                · omega
              · by_cases h3 : z = w.next
                · subst h3
                  simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h
                  subst h
                  exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkS hlS cv hcv
                · by_cases h4 : z = w.next + 2
                  · subst h4
                    simp only [h1, h2, h3, ↓reduceIte, Option.some.injEq] at h
                    subst h
                    exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                      root_key_ne c.i _ _ y _ (hyX _ (by omega) (Nat.le_refl _)) (by omega) cv' hk) cv hc)
                  · simp only [h1, h2, h3, h4, ↓reduceIte] at h
                    exfalso
                    rcases hz with hz | ⟨i, h1', h2', h3'⟩
                    · rw [hfr z hz] at h; cases h
                    · rw [h3', (hS2 i h1' h2').1] at h
                      cases h
                      exact leafTarget_none c.i _ y (fun cv' hk => hNy i h1' h2' cv' hk) cv hcv
        · cases hqlf : (Nn (s + e)).leaf with
          | false =>
            apply writerWP_handleFullWith_space_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqlf hmade hsp hpq hpk
            intro w1 h1n _ _ h1path h1next _
            have h1lk : ∀ z, z ≠ w.next → z ≠ w.next + 2 → w1.nodes.lookup z = w.nodes.lookup z :=
              fun z h1 h2 => by rw [h1n]; simp only [h1, h2, ↓reduceIte]
            have hKsc' := hKsc hqlf
            refine writerWP_mono (hin w1 _ (Or.inr ⟨_, _, _, _, rfl, Nat.le_of_lt hKsc',
              fun c'' z'' hm hlt => (hrange (s + (e + 1)) hj hD hNR (by simpa using hqlf) _ _ hscmem
                hscpos).2 c'' z'' (by simpa using hm) hlt⟩)
              (List.pairwise_cons.mpr ⟨fun a' ha' => by
                simp only [List.mem_singleton] at ha'; subst ha'; exact hKsc',
                List.pairwise_singleton _ _⟩)
              (by rw [h1path, hpath]) ?_ ?_) ?_
            · intro i h1 h2
              have hlt := (hS2 i h1 (by omega)).2
              exact ⟨by rw [h1lk _ (by omega) (by omega)]; exact (hS2 i h1 (by omega)).1, by omega⟩
            · intro z hz
              rw [h1next] at hz
              rw [h1lk z (by omega) (by omega)]; exact hfr z (by omega)
            · intro _ w2 ⟨hL2, hpost⟩
              have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
                rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
                  h1lk _ (by omega) (by omega), hlk]
              simp only [writerWP_bind]
              rw [writerWP_getNode_known _ _ c w2 hlk2]
              simp only [putNode, writerWP_modify]
              refine hfinL w1 _ w2 _ ?_ (by omega) ?_ hL2 hpost ?_ ?_
              · intro q hq
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
                rcases hq with hq | hq <;> (subst hq; simp only; omega)
              · intro y _ hNy _ z zn cv h1 h2 h3 hcv
                rw [h1next] at h2
                by_cases hz0 : z = w.next
                · subst hz0
                  rw [h1n] at h3
                  simp only [↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkF hlF cv hcv
                · by_cases hz2 : z = w.next + 2
                  · subst hz2
                    rw [h1n] at h3
                    simp only [hz0, ↓reduceIte, Option.some.injEq] at h3
                    subst h3
                    exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkS hlS cv hcv
                  · rw [h1lk z hz0 hz2, hfr z h1] at h3; cases h3
              · intro z hz
                show (upsert w2.nodes _ _).lookup z = _
                rw [lookup_upsert]; simp only [hz, ↓reduceIte]
              · intro y _ hNy _ zn cv h hcv
                change (upsert w2.nodes _ _).lookup _ = some zn at h
                rw [lookup_upsert] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                  hNy _ (by omega) (Nat.le_refl _) cv' (toPrev_key_mem _ _ _ _ hk)) cv hc)
          | true =>
            apply writerWP_handleFullWith_segSpace_up (s + e) (X (s + (e + 1))) (X (s + e))
              (Nn (s + (e + 1))) (Nn (s + e)) (K (s + (e + 1))) ins c w hlk hlq hqlf hmade hsp hpq hpk
            intro w1 h1n _ _ h1path h1next _
            have h1lk : ∀ z, z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 2 + 2 →
                w1.nodes.lookup z = w.nodes.lookup z :=
              fun z h1 h2 h3 => by rw [h1n]; simp only [h1, h2, h3, ↓reduceIte]
            refine writerWP_mono (hin w1 [(K (s + (e + 1)), w.next + 2 + 2)]
              (Or.inl ⟨_, _, rfl⟩) (List.pairwise_singleton _ _) (by rw [h1path, hpath]) ?_ ?_) ?_
            · intro i h1 h2
              have hlt := (hS2 i h1 (by omega)).2
              exact ⟨by rw [h1lk _ (by omega) (by omega) (by omega)]; exact (hS2 i h1 (by omega)).1,
                by omega⟩
            · intro z hz
              rw [h1next] at hz
              rw [h1lk z (by omega) (by omega) (by omega)]; exact hfr z (by omega)
            · intro _ w2 ⟨hL2, hpost⟩
              have hlk2 : w2.nodes.lookup (X (s + (e + 1))) = some (Nn (s + (e + 1))) := by
                rw [hpost.2.1 _ (by omega) (fun i h1 h2 he => hXne i h1 h2 he.symm),
                  h1lk _ (by omega) (by omega) (by omega), hlk]
              simp only [writerWP_bind]
              rw [writerWP_getNode_known _ _ c w2 hlk2]
              simp only [putNode, writerWP_modify]
              refine hfinL w1 _ w2 _ (by simp; omega) (by omega) ?_ hL2 hpost ?_ ?_
              · intro y _ hNy _ z zn cv h1 h2 h3 hcv
                rw [h1next] at h2
                by_cases hz0 : z = w.next
                · subst hz0
                  rw [h1n] at h3
                  simp only [↓reduceIte, Option.some.injEq] at h3
                  subst h3
                  exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkF hlF cv hcv
                · by_cases hz2 : z = w.next + 2
                  · subst hz2
                    rw [h1n] at h3
                    simp only [hz0, ↓reduceIte, Option.some.injEq] at h3
                    subst h3
                    exact leafTarget_of_keys c.i _ _ ins y (hNy _ (by omega) (Nat.le_refl _)) hkS hlS cv hcv
                  · by_cases hz4 : z = w.next + 2 + 2
                    · subst hz4
                      rw [h1n] at h3
                      simp only [hz0, hz2, ↓reduceIte, Option.some.injEq] at h3
                      subst h3
                      exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                        root_key_ne c.i _ _ y _ (by omega) (by omega) cv' hk) cv hc)
                    · rw [h1lk z hz0 hz2 hz4, hfr z h1] at h3; cases h3
              · intro z hz
                show (upsert w2.nodes _ _).lookup z = _
                rw [lookup_upsert]; simp only [hz, ↓reduceIte]
              · intro y _ hNy _ zn cv h hcv
                change (upsert w2.nodes _ _).lookup _ = some zn at h
                rw [lookup_upsert] at h
                simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                exact absurd hcv (fun hc => leafTarget_none c.i _ y (fun cv' hk =>
                  hNy _ (by omega) (Nat.le_refl _) cv' (toPrev_key_mem _ _ _ _ hk)) cv hc)
      rw [appendKlongs_step_dead]
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known _ _ c w hlk]
      by_cases hsz : (Nn (s + (e + 1))).size + ins.length + 1 > c.p.M
      · simp only [hsz, ↓reduceIte]
        by_cases hsp : c.p.splitAbove < ((Nn (s + (e + 1))).lastVersion c.i).size
        · exact hSPACE hsp
        · apply hTIME false
          simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not, gt_iff_lt]
          exact hsp
      · have hd : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) = true := by
          cases h : deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y))
            (Nn (s + (e + 1)))) with
          | true => rfl
          | false => exact absurd ⟨by omega, h⟩ hroom
        simp only [hsz, hd, ↓reduceIte]
        exact hTIME true (by simp)

end SIS.Tree
