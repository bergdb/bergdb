import SIS.Tree.GetCascadePut
import SIS.Tree.GetDelVirtual
import SIS.Tree.WriterTreeDelChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The writer's access path through every segment of a key (bergdb 024-12,
TP10): each entry after the first names a node by a live klong of the node
before it, inner or a segment leaf. A cascade of any kind runs along it. -/

/-- Steps from x, each a live klong of the node before it. -/
inductive LinkedFrom (N : NodeId → Option KNode) (t : Time) : NodeId → List (Option Nat × NodeId) → Prop
  | nil (x : NodeId) : LinkedFrom N t x []
  | cons (x : NodeId) (n : KNode) (k : Nat) (y : NodeId) (rest : List (Option Nat × NodeId)) :
      N x = some n → (k, y) ∈ n.liveAt t → LinkedFrom N t y rest →
      LinkedFrom N t x ((some k, y) :: rest)

theorem LinkedFrom.append (N : NodeId → Option KNode) (t : Time) :
    ∀ (x : NodeId) (a b : List (Option Nat × NodeId)), LinkedFrom N t x a →
      LinkedFrom N t (pathEnd x a) b → LinkedFrom N t x (a ++ b) := by
  intro x a
  induction a generalizing x with
  | nil => intro b _ hb; simpa [pathEnd] using hb
  | cons e rest ih =>
    intro b ha hb
    cases ha with
    | cons _ n k y _ hn hl hr =>
      refine LinkedFrom.cons x n k y (rest ++ b) hn hl (ih y b hr ?_)
      have : pathEnd x ((some k, y) :: rest) = pathEnd y rest := by
        cases rest with
        | nil => simp [pathEnd]
        | cons e' r' =>
          simp only [pathEnd, List.getLast?_cons_cons]
          cases h : (e' :: r').getLast? with
          | none => simp at h
          | some v => rfl
      rw [this] at hb
      exact hb

theorem LinkedFrom.of_pathFrom (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (x : NodeId) (steps : List (Option Nat × NodeId)), PathFrom N t cv x steps →
      LinkedFrom N t x steps := by
  intro x steps h
  induction h with
  | nil x => exact LinkedFrom.nil x
  | cons x n fd rest hn _ hs _ ih =>
    exact LinkedFrom.cons x n fd.c fd.y rest hn (KNode.searchLte_mem n t cv fd hs) ih

theorem pathEnd_cons_append (x y : NodeId) (k : Option Nat) (a b : List (Option Nat × NodeId)) :
    pathEnd x (a ++ (k, y) :: b) = pathEnd y b := by
  simp only [pathEnd]
  rw [List.getLast?_append]
  cases b with
  | nil => simp
  | cons e rest =>
    rw [List.getLast?_cons_cons]
    cases h : (e :: rest).getLast? with
    | none => simp at h
    | some v => rfl

theorem lookup_of_isPrefix {β : Type} (l1 l2 : List (NodeId × β)) (h : l1.IsPrefix l2) (z : NodeId)
    (v : β) (hz : l1.lookup z = some v) : l2.lookup z = some v := by
  obtain ⟨t, rfl⟩ := h
  rw [List.lookup_append, hz]
  rfl

/-- `writerWP_putSegs_prefix_src` with the writer's path: the walk down the prefix
adds steps linked from r, ending at rk, whose nodes but the last are in the
writer's nodes. -/
theorem writerWP_putSegs_prefix_linked (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (cv : Nat) (post : Bool → W → Prop) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W),
      (∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true) →
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      w.path.getLast?.map (·.2) = some r →
      (∀ w', ReadsAs c.p base w w' → w.nodes.IsPrefix w'.nodes →
        (∀ z, (w'.nodes.lookup z).isSome = true →
          (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) →
        (∃ ps, w'.path = w.path ++ ps ∧ LinkedFrom (wNode c.p base w) c.i r ps ∧ pathEnd r ps = rk ∧
          ∀ z ∈ (r :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base w z = some zn →
            w'.nodes.lookup z = some zn) →
        WriterWP (setValue rk cv key value) c w' post) →
      WriterWP (putSegs key value (pre ++ [cv]) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w _ _ hrk _ hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append, putSegs.eq_2]
    exact hcont w (ReadsAs.refl _ _ _) (List.prefix_refl _) (fun z hz => Or.inl hz)
      ⟨[], by simp, LinkedFrom.nil r, rfl, by simp⟩
  | cons s rest ih =>
    intro r rk w hwf ht hrk hp hcont
    have hne : rest ++ [cv] ≠ [] := by simp
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ [cv]) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ [cv] = d :: rest' := by
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
        refine writerWP_mono (writerWP_and (writerWP_and
          (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
          (writerWP_descendLte_steps s c base hvc c.p.fuel r w ht1))
          (writerWP_descendLte_cache s c base hvc c.p.fuel r w ht1)) ?_
        intro L w3 ⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, hget⟩, ⟨steps1, hpf, hp3, hLe⟩⟩,
          ⟨hcache3, hsrc3, hpre3⟩⟩
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
          have h4n : w4.nodes = w3.nodes := by rw [← hw4]
          have h4p : w4.path = w.path ++ steps1 ++ [(some fd.c, y)] := by rw [← hw4]; simp [hp3]
          have hvisAll := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps1 hpf
            (fun m hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
          have hlink : (fd.c, y) ∈ n.liveAt c.i := by
            have hm := KNode.searchEq_mem n c.i s fd (hwf L n hn) hfd
            rw [KNode.searchEq_c n c.i s fd hfd, hget]
            exact hm
          refine ih y rk w4 (by rw [hr04.1]; exact hwf) ?_ ?_ (by rw [h4p]; simp) ?_
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
          · intro w' hr' hpre' hsrc' ⟨ps', hp', hl', he', hc'⟩
            rw [hr04.1] at hl' hc'
            refine hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') ?_ (fun z hz => ?_) ?_
            · rw [h4n] at hpre'; exact hpre3.trans hpre'
            · rcases hsrc' z hz with h1 | h1
              · rw [h4n] at h1
                exact hsrc3 z h1
              · exact Or.inr h1
            · refine ⟨steps1 ++ (some fd.c, y) :: ps', by rw [hp', h4p]; simp, ?_, ?_, ?_⟩
              · refine LinkedFrom.append _ _ r steps1 _ (LinkedFrom.of_pathFrom _ _ s r steps1 hpf) ?_
                rw [← hLe]
                exact LinkedFrom.cons L n fd.c y ps' hn hlink hl'
              · rw [pathEnd_cons_append]; exact he'
              · intro z hz zn hzn
                have hsplit : (r :: (steps1 ++ (some fd.c, y) :: ps').map (·.2)) =
                    (r :: steps1.map (·.2)) ++ (y :: ps'.map (·.2)) := by simp
                rw [hsplit, List.dropLast_append_of_ne_nil (by simp)] at hz
                rcases List.mem_append.mp hz with hz | hz
                · have hzv : (z, s) ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r := by
                    rcases List.mem_cons.mp hz with hz | hz
                    · rw [hz]; exact hvisAll.1
                    · obtain ⟨e, he1, he2⟩ := List.mem_map.mp hz
                      rw [← he2]; exact hvisAll.2 e he1
                  have h3 := hcache3 z zn hzv hzn
                  rw [← h4n] at h3
                  exact lookup_of_isPrefix _ _ hpre' z zn h3
                · exact hc' z hz zn hzn
      · cases hrk

/-- `writerWP_putSegs_prefix_linked` for a key's segments after the prefix
of any length: the walk down the prefix, then the rest from its segment root. -/
theorem writerWP_putSegs_prefix_linkedS (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (sfx : List Nat) (hsfx : sfx ≠ []) (post : Bool → W → Prop) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W),
      (∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true) →
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ sfx) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      w.path.getLast?.map (·.2) = some r →
      (∀ w', ReadsAs c.p base w w' → w.nodes.IsPrefix w'.nodes →
        (∀ z, (w'.nodes.lookup z).isSome = true →
          (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) →
        (∃ ps, w'.path = w.path ++ ps ∧ LinkedFrom (wNode c.p base w) c.i r ps ∧ pathEnd r ps = rk ∧
          ∀ z ∈ (r :: ps.map (·.2)).dropLast, ∀ zn, wNode c.p base w z = some zn →
            w'.nodes.lookup z = some zn) →
        WriterWP (putSegs key value sfx rk) c w' post) →
      WriterWP (putSegs key value (pre ++ sfx) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w _ _ hrk _ hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append]
    exact hcont w (ReadsAs.refl _ _ _) (List.prefix_refl _) (fun z hz => Or.inl hz)
      ⟨[], by simp, LinkedFrom.nil r, rfl, by simp⟩
  | cons s rest ih =>
    intro r rk w hwf ht hrk hp hcont
    have hne : rest ++ sfx ≠ [] := by simp [hsfx]
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ sfx) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ sfx = d :: rest' := by
          cases h' : rest ++ sfx with
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
        refine writerWP_mono (writerWP_and (writerWP_and
          (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
          (writerWP_descendLte_steps s c base hvc c.p.fuel r w ht1))
          (writerWP_descendLte_cache s c base hvc c.p.fuel r w ht1)) ?_
        intro L w3 ⟨⟨⟨hr3, n, hn, hnl, hlk3, hvisL, hget⟩, ⟨steps1, hpf, hp3, hLe⟩⟩,
          ⟨hcache3, hsrc3, hpre3⟩⟩
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
          have h4n : w4.nodes = w3.nodes := by rw [← hw4]
          have h4p : w4.path = w.path ++ steps1 ++ [(some fd.c, y)] := by rw [← hw4]; simp [hp3]
          have hvisAll := PathFrom.mem_eqVisits _ _ _ c.p.fuel r steps1 hpf
            (fun m hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
          have hlink : (fd.c, y) ∈ n.liveAt c.i := by
            have hm := KNode.searchEq_mem n c.i s fd (hwf L n hn) hfd
            rw [KNode.searchEq_c n c.i s fd hfd, hget]
            exact hm
          refine ih y rk w4 (by rw [hr04.1]; exact hwf) ?_ ?_ (by rw [h4p]; simp) ?_
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
          · intro w' hr' hpre' hsrc' ⟨ps', hp', hl', he', hc'⟩
            rw [hr04.1] at hl' hc'
            refine hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') ?_ (fun z hz => ?_) ?_
            · rw [h4n] at hpre'; exact hpre3.trans hpre'
            · rcases hsrc' z hz with h1 | h1
              · rw [h4n] at h1
                exact hsrc3 z h1
              · exact Or.inr h1
            · refine ⟨steps1 ++ (some fd.c, y) :: ps', by rw [hp', h4p]; simp, ?_, ?_, ?_⟩
              · refine LinkedFrom.append _ _ r steps1 _ (LinkedFrom.of_pathFrom _ _ s r steps1 hpf) ?_
                rw [← hLe]
                exact LinkedFrom.cons L n fd.c y ps' hn hlink hl'
              · rw [pathEnd_cons_append]; exact he'
              · intro z hz zn hzn
                have hsplit : (r :: (steps1 ++ (some fd.c, y) :: ps').map (·.2)) =
                    (r :: steps1.map (·.2)) ++ (y :: ps'.map (·.2)) := by simp
                rw [hsplit, List.dropLast_append_of_ne_nil (by simp)] at hz
                rcases List.mem_append.mp hz with hz | hz
                · have hzv : (z, s) ∈ eqVisits (wNode c.p base w) c.i s c.p.fuel r := by
                    rcases List.mem_cons.mp hz with hz | hz
                    · rw [hz]; exact hvisAll.1
                    · obtain ⟨e, he1, he2⟩ := List.mem_map.mp hz
                      rw [← he2]; exact hvisAll.2 e he1
                  have h3 := hcache3 z zn hzv hzn
                  rw [← h4n] at h3
                  exact lookup_of_isPrefix _ _ hpre' z zn h3
                · exact hc' z hz zn hzn
      · cases hrk

/-- The node at position i of the path from x: x, then the steps' nodes. -/
def nodeAt (x : NodeId) (steps : List (Option Nat × NodeId)) (i : Nat) : NodeId :=
  ((x :: steps.map (·.2))[i]?).getD 0

theorem LinkedFrom.get (N : NodeId → Option KNode) (t : Time) :
    ∀ (x : NodeId) (steps : List (Option Nat × NodeId)), LinkedFrom N t x steps →
      ∀ i, i < steps.length → ∃ k n, steps[i]? = some (some k, nodeAt x steps (i + 1)) ∧
        N (nodeAt x steps i) = some n ∧ (k, nodeAt x steps (i + 1)) ∈ n.liveAt t := by
  intro x steps h
  induction h with
  | nil x => intro i hi; simp at hi
  | cons x n k y rest hn hl _ ih =>
    intro i hi
    cases i with
    | zero => exact ⟨k, n, by simp [nodeAt], by simpa [nodeAt] using hn, by simpa [nodeAt] using hl⟩
    | succ i =>
      obtain ⟨k', n', h1, h2, h3⟩ := ih i (by simpa using hi)
      refine ⟨k', n', ?_, ?_, ?_⟩
      · simp only [List.getElem?_cons_succ]
        rw [h1]
        simp [nodeAt]
      · simpa [nodeAt] using h2
      · simpa [nodeAt] using h3

theorem LinkedFrom.pathLen (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (steps : List (Option Nat × NodeId)) (h : LinkedFrom N t r steps) :
    ∀ i, i ≤ steps.length → PathLen N t r (nodeAt r steps i) i := by
  intro i
  induction i with
  | zero => intro _; simpa [nodeAt] using PathLen.root
  | succ i ih =>
    intro hi
    obtain ⟨k, n, _, h2, h3⟩ := LinkedFrom.get N t r steps h i (by omega)
    exact PathLen.link (ih (by omega)) ⟨n, h2, h3⟩

theorem nodeAt_last (x : NodeId) (steps : List (Option Nat × NodeId)) :
    nodeAt x steps steps.length = pathEnd x steps := by
  induction steps generalizing x with
  | nil => simp [nodeAt, pathEnd]
  | cons e rest ih =>
    obtain ⟨k, y⟩ := e
    have h1 : nodeAt x ((k, y) :: rest) ((k, y) :: rest).length = nodeAt y rest rest.length := by
      simp [nodeAt]
    rw [h1, ih y]
    have := pathEnd_cons_append x y k [] rest
    simpa using this.symm

theorem nodeAt_zero (x : NodeId) (steps : List (Option Nat × NodeId)) : nodeAt x steps 0 = x := by
  simp [nodeAt]

theorem nodeAt_append_left (x : NodeId) (a b : List (Option Nat × NodeId)) (i : Nat)
    (hi : i ≤ a.length) : nodeAt x (a ++ b) i = nodeAt x a i := by
  unfold nodeAt
  cases i with
  | zero => simp
  | succ i =>
    simp only [List.map_append, List.getElem?_cons_succ]
    rw [List.getElem?_append_left (by simp; omega)]

theorem nodeAt_append_right (x : NodeId) (a b : List (Option Nat × NodeId)) (j : Nat) :
    nodeAt x (a ++ b) (a.length + j) = nodeAt (pathEnd x a) b j := by
  induction a generalizing x with
  | nil => simp [pathEnd]
  | cons e rest ih =>
    obtain ⟨k, y⟩ := e
    have h1 : nodeAt x ((k, y) :: rest ++ b) (((k, y) :: rest).length + j) =
        nodeAt y (rest ++ b) (rest.length + j) := by
      simp only [nodeAt, List.cons_append, List.map_cons, List.length_cons]
      rw [show rest.length + 1 + j = (rest.length + j) + 1 by omega, List.getElem?_cons_succ]
    rw [h1, ih y]
    have := pathEnd_cons_append x y k [] rest
    simp only [List.nil_append] at this
    rw [this]

theorem nodeAt_mem_dropLast (x : NodeId) (a : List (Option Nat × NodeId)) (i : Nat)
    (hi : i < a.length) : nodeAt x a i ∈ (x :: a.map (·.2)).dropLast := by
  unfold nodeAt
  have hlen : i < (x :: a.map (·.2)).dropLast.length := by simp; omega
  have he : (x :: a.map (·.2))[i]? = some ((x :: a.map (·.2)).dropLast[i]) := by
    rw [← List.getElem?_eq_getElem hlen, List.getElem?_dropLast]
    simp only [List.length_cons, List.length_map, show i < a.length + 1 - 1 by omega, ↓reduceIte]
  rw [he]
  exact List.getElem_mem hlen

theorem nodeAt_mem_steps (y : NodeId) (b : List (Option Nat × NodeId)) (j : Nat)
    (h1 : 0 < j) (h2 : j ≤ b.length) : ∃ e ∈ b, e.2 = nodeAt y b j := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hj : j' < b.length := by omega
  refine ⟨b[j'], List.getElem_mem hj, ?_⟩
  simp [nodeAt, List.getElem?_eq_getElem hj]

theorem pathEnd_append_gen (x : NodeId) (a b : List (Option Nat × NodeId)) :
    pathEnd x (a ++ b) = pathEnd (pathEnd x a) b := by
  cases b with
  | nil => simp [pathEnd]
  | cons e rest =>
    obtain ⟨k, y⟩ := e
    rw [pathEnd_cons_append x y k a rest]
    have := pathEnd_cons_append (pathEnd x a) y k [] rest
    simp only [List.nil_append] at this
    rw [this]

/-- The space root r of N does not space split: when a cascade reaches it
without room (`ChainRoom`), its last version is within the split size. With it,
the reading after a cascade needs no premise on the fuel
(`writerWP_appendKlongs_chainGRV`). -/
def RootStays (c : Ctx) (N : NodeId → Option KNode) (r : NodeId) : Prop :=
  ∀ rn, N r = some rn → ¬ ChainRoom c rn → (rn.lastVersion c.i).size ≤ c.p.splitAbove

set_option maxHeartbeats 1600000 in
/-- A put of a key into a full leaf, with the cascade along the whole access path
from the space root, across segments (`writerWP_appendKlongs_chainGRV` from 0):
each node splits as its sizes say, in place if the transaction made it, or
keeps its room and ends the cascade. The premises on the nodes reached: the
order of a full node's compare values below its inner parent's klong
(`hrangeG`), two live klongs in a node that space splits (`hlenG`), and an inner
parent for a node that space splits (`hspaceG`: the space root may space split
and get a new root, a segment root below a segment leaf may not). The splits
change the reading by the put alone, when every path inside one segment tree of
the writer's state after them is shorter than the fuel (`SegFits`), or when the
space root does not space split (`RootStays`). -/
theorem writerWP_put_accessPathR (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i → qn.leaf = false)
    (hfullL : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
        RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  have htkN : ∀ z zn, wNode c.p base w z = some zn → w.taken.contains z = false := by
    intro z zn hz
    cases hc : w.taken.contains z with
    | false => rfl
    | true => unfold wNode at hz; rw [hc] at hz; simp at hz
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hw2p : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  refine writerWP_putSegs_prefix_linked c base hvc (pre ++ [cv]) (some h) cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1]; exact hwfG) (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by rw [hw2p]; simp) ?_
  intro w2' hr2' _ hsrc2' ⟨ps, hp2', hps, hpse, hpsc⟩
  rw [hr02.1] at hps hpsc
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel rk w2' ht2))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, hpre3⟩⟩
  rw [hr0.1] at hn hvisL hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  -- the whole path from the space root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w.top.rootKey) :: P := by rw [hp3, hp2', hw2p, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hps (by rw [hpse]; exact LinkedFrom.of_pathFrom _ _ cv rk steps hpf)
  have hXD : nodeAt w.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, hpse, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk steps hpf
    (fun mm hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL)
  -- the chain's nodes, klongs and contents
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hreachX : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w) c.i w.top.rootKey (nodeAt w.top.rootKey P i) :=
    fun i hi => (hPL i hi).reach
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hm : nodeAt w.top.rootKey P i ∈ (w.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hpsc _ hm _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w.top.rootKey P i = nodeAt rk steps j := by
        rw [hP, hj, nodeAt_append_right, hpse]
      have hvj : (nodeAt rk steps j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps rk steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  -- ids
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
    intro z hz
    apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega
  have hXlt : ∀ i, i ≤ P.length → nodeAt w.top.rootKey P i < w.next :=
    fun i hi => hsrcw3 _ (by rw [hlkX i hi]; rfl)
  -- the writer's path
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  have hLlt : L < w.next := by rw [← hXD]; exact hXlt _ (Nat.le_refl _)
  have hLreach : TReach (wNode c.p base w) c.i w.top.rootKey L := by
    rw [← hXD]; exact hreachX _ (Nat.le_refl _)
  -- the leaf is full: the put goes to appendKlongs
  unfold newValue fresh
  wpSimplify
  rw [writerWP_getNode_known _ _ c _ (by simpa using hlk3)]
  have hcond : (decide (n.size + 1 < c.p.M) &&
      !deadOver c.p (n.add c.i (.key cv w3.next))) = false := by
    rw [hnext3]
    have hf := hfullL L n hvisL hn hnl
    cases hd' : deadOver c.p (n.add c.i (.key cv w.next)) with
    | true => simp
    | false =>
      have : ¬ n.size + 1 < c.p.M := fun hlt => hf ⟨hlt, hd'⟩
      simp [this]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, pathSize, writerWP_bind, writerWP_get,
    writerWP_pure]
  have hlen3 : w3.path.length - 1 = P.length := by rw [hp3']; simp
  rw [hlen3]
  -- the state before appendKlongs: w3 with the new value
  generalize hws : ({ w3 with
    made := w3.made ++ [⟨w3.next, 0, true⟩]
    vals := w3.vals ++ [(w3.next, h)]
    next := w3.next + 2 } : W) = ws
  have hwsn : ws.nodes = w3.nodes := by rw [← hws]
  have hwst : ws.taken = w.taken := by rw [← hws]; exact hr03.2.2.1
  have hwsv : ws.vals = w.vals ++ [(w.next, h)] := by rw [← hws]; simp only; rw [hr03.2.2.2.1, hnext3]
  have hwsx : ws.next = w.next + 2 := by rw [← hws]; simp only; rw [hnext3]
  have hwsp : ws.path = w3.path := by rw [← hws]
  have hwstop : ws.top = w.top := by rw [← hws]; exact hr03.2.1
  have hwsN : wNode c.p base ws = wNode c.p base w := by
    rw [← hr03.1]
    funext z
    simp only [wNode, hwsn, hwst, hr03.2.2.1]
  have hchain := writerWP_appendKlongs_chainGRV c base w3.path 0 P.length
    (fun i => nodeAt w.top.rootKey P i) (fun i => ((P[i - 1]?).bind (·.1)).getD 0)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i _ h2 => hpX i h2)
    (fun i h1 h2 => hpK i h1 h2)
    (fun i h1 h2 => (hKP i h1 h2).2)
    (fun i h1 h2 hnr hql c' z hz hc => hrangeG _ _ _ _ _ (hreachX (i - 1) (by omega))
      (hXN (i - 1) (by omega)) hql (hKP i h1 h2).2 (hXN i h2) hnr c' z hz hc)
    (fun i _ h2 hnr hsp => hlenG _ _ (hreachX i h2) (hXN i h2) hnr hsp)
    (fun i _ h2 => hwfG _ _ (hXN i h2))
    (fun i _ h2 => htimesG _ _ (hXN i h2))
    (Or.inr rfl)
    (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
    (fun i _ h2 hnr hsp => by
      rcases Nat.eq_zero_or_pos i with h0 | hi
      · exact Or.inl h0
      · exact Or.inr ⟨hi, hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _ (hreachX (i - 1) (by omega))
          (hXN (i - 1) (by omega)) (hKP i hi h2).2⟩)
    P.length (by omega) ws [(cv, w3.next)] (Or.inl ⟨cv, w3.next, rfl⟩)
    (by intro q hq; simp at hq; rw [hq, hwsx, hnext3]; simp)
    hwsp
    (fun i _ h2 => ⟨by rw [hwsn]; exact hlkX i (by omega),
      by rw [hwst]; exact htkN _ _ (hXN i (by omega))⟩)
    (by rw [hwsN, hwstop]; exact hT)
    (fun i _ h2 => by rw [hwsN, hwstop]; exact hreachX i (by omega))
    (by
      intro z hz
      rw [hwsx] at hz
      refine ⟨?_, ?_, (hbase z (by omega)).1⟩
      · rw [hwsn]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega
      · rw [hwst]; exact hntake z (by omega))
    (by
      intro u c' z hl
      rw [hwsN] at hl
      have := hlinksAll u c' z hl
      rw [hwsx]; omega)
    (fun _ _ => by show ws.top.rootKey = nodeAt w.top.rootKey P 0; rw [hwstop, nodeAt_zero])
    (by
      intro z zn hz
      rw [hwsN] at hz
      exact hwfG z zn hz)
    (by
      rw [hwsN, hwstop]
      simp only [Nat.zero_add, hXD, hn, Option.getD_some, hnext3]
      exact treeOK_addKey (wNode c.p base w) _ c.i w.top.rootKey L w.next n cv hT hLreach hn
        (hwfG _ _ hn) (htimesG _ _ hn) (updN_self _ _ _) (fun x hx => updN_ne _ _ _ _ hx)
        (by
          simp only [wNode, hntake w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
            (hbase w.next (Nat.le_refl _)).1]
          cases h' : w.nodes.lookup w.next with
          | none => rfl
          | some _ => have := hidn w.next (by rw [h']; rfl); omega)
        (fun u c' _ hl => by have := hlinksAll u c' w.next hl; omega))
  simp only [Nat.zero_add, hXD, hn, Option.getD_some] at hchain
  refine writerWP_mono hchain ?_
  intro _ wf ⟨_, ⟨hftop, hft, _, _, hfv⟩, _, _, _, hR, _⟩
  have hadm : ∀ z, (w.next + 2 ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ P.length ∧ z = nodeAt w.top.rootKey P i) →
      wValue base ws z = none := by
    intro z hz
    have hzn : z ≠ w.next := by
      rcases hz with hz | ⟨i, h1, h2, h3⟩
      · omega
      · rw [h3]; have := hXlt i h2; omega
    have hval : wValue base ws z = wValue base w z := by
      simp only [wValue, hwst, hwsv, lookup_append_single_ne _ _ _ _ hzn]
    rw [hval]
    rcases hz with hz | ⟨i, h1, h2, h3⟩
    · simp only [wValue, hntake z (by omega), Bool.false_eq_true, ↓reduceIte,
        hvalnone z (by omega), (hbase z (by omega)).2]
    · rw [h3]; exact hnoval _ _ (hXN i h2)
  have hvf : wValue base wf = wValue base ws := by
    funext a; simp only [wValue, hft, hfv]
  have hn2l : (n.add c.i (.key cv w.next)).leaf = true := by rw [KNode.add_leaf]; exact hnl
  have hmwf := hwfG _ _ hn
  have hmt := htimesG _ _ hn
  have hsearch := KNode.add_key_searchEq n c.i cv w.next hmwf hmt
  have hwsnext : ws.taken.contains w.next = false := by rw [hwst]; exact hntake _ (Nat.le_refl _)
  have hVv : wValue base ws w.next = some h := by
    simp only [wValue, hwsnext, Bool.false_eq_true, ↓reduceIte, hwsv,
      lookup_append_single_self _ _ _ (hvalnone _ (Nat.le_refl _))]
  have hA := getFromR_leaf_change_seg (wNode c.p base w)
    (updN (wNode c.p base w) L (n.add c.i (.key cv w.next))) (wValue base w)
    (wValue base ws) c.i c.p.fuel hfuel L pre cv w.top.rootKey rk n
    (n.add c.i (.key cv w.next)) (fun x hx => (updN_ne _ _ _ _ hx).symm)
    hn (updN_self _ _ _) hnl hn2l
    (fun c' hc' => by
      rw [hsearch c']
      have hb : (cv == c') = false := by
        cases hcb : (cv == c') with
        | false => rfl
        | true => exact absurd (beq_iff_eq.mp hcb).symm hc'
      rw [hb]; rfl)
    hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    (fun key' x c' m' y _ hx hm' _ hs' => by
      have hrx : ReachS (wNode c.p base w) c.i w.top.rootKey x :=
        fromVisits_reach _ _ _ _ hwfR key' _ x c' ReachS.root hx
      have hy : y < w.next := by
        cases hfd : m'.searchEq c.i c' with
        | none => rw [hfd] at hs'; cases hs'
        | some fd =>
          rw [hfd] at hs'
          simp only [Option.map_some, Option.some.injEq] at hs'
          subst hs'
          exact hlinksAll x c' fd.y ⟨m', hm', KNode.searchEq_mem m' c.i c' fd (hwfG x m' hm') hfd⟩
      simp only [wValue, hwst, hwsv, lookup_append_single_ne _ _ _ _ (by omega : y ≠ w.next)])
  intro hq key' hkey'
  unfold wGet
  rw [hvf, hR (wValue base ws) (fun z hz => hadm z (by rw [hwsx] at hz; exact hz))
    (hq.imp id (fun hs => ⟨fun ⟨_, hnr, hsp⟩ => Nat.not_le.mpr hsp (hs _ (by
      dsimp only
      have h0 := hXN 0 (Nat.zero_le _)
      rw [nodeAt_zero] at h0 ⊢
      exact h0) hnr), fun i hi h2 hnr hsp => hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _
        (hreachX (i - 1) (by omega)) (hXN (i - 1) (by omega)) (hKP i hi h2).2⟩)) key', hwsN, hwstop, hnext3]
  simp only [List.foldl_cons, List.foldl_nil]
  by_cases hk : pre ++ [cv] = key'
  · subst hk
    simp only [Op.key, beq_self_eq_true, ↓reduceIte, Op.value]
    rw [hA.1, hsearch cv]
    simp [hVv]
  · have hk' : (pre ++ [cv] == key') = false := by simpa using hk
    simp only [Op.key, hk', Bool.false_eq_true, ↓reduceIte]
    exact hA.2 key' hkey' (fun h' => hk h'.symm)


/-- `writerWP_put_accessPathR` when no node that space splits is the space root
(`hspaceG`): the reading needs no premise on the fuel. -/
theorem writerWP_put_accessPath (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv h : Nat) (rk : NodeId) (w : W)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      x ≠ w.top.rootKey ∧ ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i → qn.leaf = false)
    (hfullL : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key') :=
  writerWP_mono (writerWP_put_accessPathR c base hvc pre cv h rk w hkey hrk ht hids hbase hwfG htimesG
    hT hlinksAll hnoval hrangeG hlenG (fun x xn hx hxn hnr hsp => (hspaceG x xn hx hxn hnr hsp).2)
    hfullL huniq)
    (fun _ _ hp => hp (Or.inr (fun rn hrn hnr => Nat.le_of_not_lt (fun hsp =>
      (hspaceG _ _ TReach.root hrn hnr hsp).1 rfl))))

set_option maxHeartbeats 1600000 in
/-- A delete, the merges off, from a leaf whose bitmap changes and keeps a live
klong, with the cascade along the whole access path from the space root, across
segments (`writerWP_appendKlongs_chainGRQ` from 0): the leaf's bitmap, its time
or space split (in place for a leaf the transaction made), and the splits above
it as their sizes say, the space root's space split too. The leaf is not the
space root and its parent is inner with the leaf's compare values in the range
of its klong (`hleafG`); the other premises are on the nodes reached, as in
`writerWP_put_accessPathR`. The reading changes by the delete alone when every
path inside one segment tree of the writer's state after it is shorter than the
fuel (`SegFits`) or the space root does not space split (`RootStays`). -/
theorem writerWP_del_accessPathR (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hmerges : c.p.merges = false) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i → qn.leaf = false)
    (hleafG : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      L ≠ w.top.rootKey ∧ (∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, L) ∈ qn.liveAt c.i →
        (qn.leaf = false ∧ LeafOrderAt qn K n) ∨
        (qn.leaf = true ∧ (¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
          c.p.M ≤ n.size + 1 →
          (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf cv))).size ≤ c.p.splitAbove))) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
        RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hwfR : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true := fun x xn _ hn => hwfG x xn hn
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk :=
    segRootR_reach _ _ _ _ hwfR pre _ rk ReachS.root hrk
  have htkN : ∀ z zn, wNode c.p base w z = some zn → w.taken.contains z = false := by
    intro z zn hz
    cases hc : w.taken.contains z with
    | false => rfl
    | true => unfold wNode at hz; rw [hc] at hz; simp at hz
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  have hw2p : w2.path = [(none, w.top.rootKey)] := by subst hw2; rfl
  refine writerWP_putSegs_prefix_linked c base hvc (pre ++ [cv]) none cv _ pre w.top.rootKey rk w2
    (by rw [hr02.1]; exact hwfG) (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by rw [hw2p]; simp) ?_
  intro w2' hr2' _ hsrc2' ⟨ps, hp2', hps, hpse, hpsc⟩
  rw [hr02.1] at hps hpsc
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  unfold setValue
  wpSimplify
  have ht2 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i cv c.p.fuel rk,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (fromVisits_append _ _ _ pre cv _ rk hrk q hq)
  refine writerWP_mono (writerWP_and (writerWP_and
    (writerWP_descendLte_reads cv c base hvc c.p.fuel rk w2' ht2)
    (writerWP_descendLte_steps cv c base hvc c.p.fuel rk w2' ht2))
    (writerWP_descendLte_cache cv c base hvc c.p.fuel rk w2' ht2)) ?_
  intro L w3 ⟨⟨⟨hr23, n, hn, hnl, hlk3, hvisL0, _⟩, ⟨steps, hpf, hp3, hLe⟩⟩, ⟨hcache3, hsrc3, hpre3⟩⟩
  rw [hr0.1] at hn hvisL0 hpf hcache3
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  -- the whole path from the space root
  obtain ⟨P, hP⟩ : ∃ P, P = ps ++ steps := ⟨_, rfl⟩
  have hp3' : w3.path = (none, w.top.rootKey) :: P := by rw [hp3, hp2', hw2p, hP]; simp
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P := by
    rw [hP]
    exact LinkedFrom.append _ _ _ ps steps hps (by rw [hpse]; exact LinkedFrom.of_pathFrom _ _ cv rk steps hpf)
  have hXD : nodeAt w.top.rootKey P P.length = L := by
    rw [nodeAt_last, hP, pathEnd_append_gen, hpse, hLe]
  have hvis := PathFrom.mem_eqVisits _ _ _ c.p.fuel rk steps hpf
    (fun mm hm => by rw [← hLe, hn] at hm; cases hm; exact hnl) (by rw [← hLe]; exact hvisL0)
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have hlkXP : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    have hw := hXN i hi
    rcases Nat.lt_or_ge i ps.length with hlt | hge
    · have hm : nodeAt w.top.rootKey P i ∈ (w.top.rootKey :: ps.map (·.2)).dropLast := by
        rw [hP, nodeAt_append_left _ _ _ _ (by omega)]
        exact nodeAt_mem_dropLast _ _ _ hlt
      exact lookup_of_isPrefix _ _ hpre3 _ _ (hpsc _ hm _ hw)
    · obtain ⟨j, hj⟩ : ∃ j, i = ps.length + j := ⟨i - ps.length, by omega⟩
      have hXj : nodeAt w.top.rootKey P i = nodeAt rk steps j := by
        rw [hP, hj, nodeAt_append_right, hpse]
      have hvj : (nodeAt rk steps j, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
        rcases Nat.eq_zero_or_pos j with h0 | h0
        · rw [h0, nodeAt_zero]; exact hvis.1
        · have hjl : j ≤ steps.length := by
            have : P.length = ps.length + steps.length := by rw [hP]; simp
            omega
          obtain ⟨e, he1, he2⟩ := nodeAt_mem_steps rk steps j h0 hjl
          rw [← he2]; exact hvis.2 e he1
      rw [hXj] at hw ⊢
      exact hcache3 _ _ hvj hw
  -- the chain's data: the whole path
  obtain ⟨m, hm_def⟩ : ∃ m, m = P.length := ⟨_, rfl⟩
  obtain ⟨d, hd0⟩ : ∃ d, d = 0 := ⟨0, rfl⟩
  obtain ⟨XX, hXX⟩ : ∃ f : Nat → NodeId, f = fun i => nodeAt w.top.rootKey P i := ⟨_, rfl⟩
  obtain ⟨KK, hKK⟩ : ∃ f : Nat → Nat, f = fun i => ((P[i - 1]?).bind (·.1)).getD 0 := ⟨_, rfl⟩
  obtain ⟨NN, hNNd⟩ : ∃ f : Nat → KNode,
      f = fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n := ⟨_, rfl⟩
  have hXm : XX m = L := by rw [hXX, hm_def]; exact hXD
  have hX0 : XX 0 = w.top.rootKey := by rw [hXX]; exact nodeAt_zero _ _
  have hNN : ∀ j, j ≤ m → wNode c.p base w (XX j) = some (NN j) := by
    intro j hj; rw [hXX, hNNd]; exact hXN j (by omega)
  have hNm : NN m = n := by
    have := hNN m (Nat.le_refl _); rw [hXm, hn] at this; cases this; rfl
  have hstay : RootStays c (wNode c.p base w) w.top.rootKey →
      ¬ (d = 0 ∧ ¬ ChainRoom c (NN (0 - d)) ∧ c.p.splitAbove < ((NN (0 - d)).lastVersion c.i).size) := by
    intro hs ⟨_, hnr, hsp⟩
    rw [hd0, Nat.zero_sub] at hnr hsp
    exact Nat.not_le.mpr hsp (hs _ (by rw [← hX0]; exact hNN 0 (Nat.zero_le _)) hnr)
  obtain ⟨hLroot', hLpar, hne, hkeep⟩ := hleafG L n hvisL0 hn hnl
  rw [← hNm] at hne hkeep
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · exfalso; apply hLroot'; rw [← hXm, h0, hX0]
    · exact h0
  have hleafm : (NN m).leaf = true := by rw [hNm]; exact hnl
  have hlinksK : ∀ j, j < m → (KK (j + 1), XX (j + 1)) ∈ (NN j).liveAt c.i := by
    intro j hj
    have := (hKP (j + 1) (by omega) (by omega)).2
    rw [hKK, hXX, hNNd]
    simpa using this
  have hTR : ∀ j, j ≤ m → TReach (wNode c.p base w) c.i w.top.rootKey (XX j) := by
    intro j hj; rw [hXX]; exact (hPL j (by omega)).reach
  have hreachX : ∀ j, j ≤ m → ReachS (wNode c.p base w) c.i w.top.rootKey (XX j) :=
    fun j hj => tReach_reachS _ _ _ _ (hTR j hj)
  have hparL := hLpar (XX (m - 1)) (NN (m - 1)) (KK m) (hTR (m - 1) (by omega)) (hNN (m - 1) (by omega))
    (by
      have := hlinksK (m - 1) (by omega)
      have he : m - 1 + 1 = m := by omega
      rw [he, hXm] at this; exact this)
  have hrangeL : (NN (m - 1)).leaf = false → ∀ c' z, (c', z) ∈ (NN m).live →
      KK m ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (NN (m - 1)).live → KK m < c'' → c' < c'' := by
    intro hql
    rcases hparL with h | h
    · rw [hNm]; exact h.2
    · rw [hql] at h; cases h.1
  have hstayL : (NN (m - 1)).leaf = true →
      ¬ ((∃ old, (NN m).ks.getLast? = some (.del old)) ∧ (NN m).lastTime = some c.i) →
      c.p.M ≤ (NN m).size + 1 →
      ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size ≤
        c.p.splitAbove := by
    intro hqlt
    rcases hparL with h | h
    · rw [hqlt] at h; cases h.1
    · rw [hNm]; exact h.2
  have hdist : ∀ j j', j ≤ m → j' ≤ m → XX j = XX j' → j = j' := by
    intro j j' h1 h2 he; rw [hXX] at he; exact hdistP j j' (by omega) (by omega) he
  have hvisL : (XX m, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by rw [hXm]; exact hvisL0
  have hlkX : ∀ j, j ≤ m → w3.nodes.lookup (XX j) = some (NN j) := by
    intro j hj; rw [hXX, hNNd]; exact hlkXP j (by omega)
  have htkX : ∀ j, j ≤ m → w.taken.contains (XX j) = false :=
    fun j hj => htkN _ _ (hNN j hj)
  -- ids
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hvalnone : ∀ z, w.next ≤ z → w.vals.lookup z = none := by
    intro z hz
    apply List.lookup_eq_none_iff.mpr
    intro q' hq'
    have := hidvals q' hq'
    simp only [bne_iff_ne, ne_eq]
    omega
  have hXlt : ∀ j, j ≤ m → XX j < w.next := fun j hj => hsrcw3 _ (by rw [hlkX j hj]; rfl)
  -- the writer's path
  have hlen3 : w3.path.length - 1 = d + m := by rw [hp3', hd0, hm_def]; simp
  have hpX : ∀ i, d ≤ i → i ≤ d + m → (w3.path[i]?).map (·.2) = some (XX (i - d)) := by
    intro i _ h2
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hd0, Nat.sub_zero, hXX, hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, d < i → i ≤ d + m → w3.path[i]? = some (some (KK (i - d)), XX (i - d)) := by
    intro i h1 h2
    rw [hd0, Nat.sub_zero, hKK, hXX]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) (by omega) (by omega)).1
  have hR0gen : ∀ ws : W, ws.top = w.top → d = 0 → ¬ ChainRoom c (NN (0 - d)) →
      ws.top.rootKey = XX (0 - d) := by
    intro ws hws _ _
    rw [hws, Nat.zero_sub, hX0]
  rw [← hXm]
  -- the delete in the leaf
  simp only [pathSize, writerWP_bind, writerWP_get, writerWP_pure]
  rw [hlen3]
  have hlkL := hlkX m (Nat.le_refl _)
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c _ hlkL]
  have hnb : (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv) == (NN m).lastBitmap) = false := by
    simpa using hne
  simp only [hnb, Bool.false_eq_true, ↓reduceIte, hkeep, Bool.not_false]
  wpSimplify
  refine writerWP_ghOf_cached _ _ c _ hlkL _ (fun gh => ?_)
  -- facts of the leaf, its parent and the delete's last version
  have hLt := htkX m (Nat.le_refl _)
  have hnL := hNN m (Nat.le_refl _)
  have hqn := hNN (m - 1) (by omega)
  have hnwf := hwfG _ _ hnL
  have hnt := htimesG _ _ hnL
  have hqwf := hwfG _ _ hqn
  have hqt := htimesG _ _ hqn
  have hmm : m - 1 + 1 = m := by omega
  have hkl : (KK m, XX m) ∈ (NN (m - 1)).liveAt c.i := by
    have := hlinksK (m - 1) (by omega); rw [hmm] at this; exact this
  have hkl' : (KK m, XX m) ∈ (NN (m - 1)).live := by
    rw [← KNode.liveAt_of_times _ c.i hqt]; exact hkl
  have hqL : XX (m - 1) ≠ XX m := fun h => by have := hdist _ _ (by omega) (Nat.le_refl _) h; omega
  have hrq := hreachX (m - 1) (by omega)
  have hrL := hreachX m (Nat.le_refl _)
  have honlyL : ∀ x xn c', ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (c', XX m) ∈ xn.liveAt c.i → x = XX (m - 1) ∧ c' = KK m :=
    fun x xn c' hx hxn hz => hT.oneLink x c' (XX (m - 1)) (KK m) (XX m)
      (reachS_tReach _ _ _ _ hx) (reachS_tReach _ _ _ _ hrq) ⟨xn, hxn, hz⟩ ⟨_, hqn, hkl⟩
  have hLroot : w.top.rootKey ≠ XX m := fun h =>
    hT.rootFree (XX (m - 1)) (KK m) (reachS_tReach _ _ _ _ hrq) ⟨_, hqn, by rw [h]; exact hkl⟩
  obtain ⟨hleq, hlt, hlsub⟩ := delLast_facts (NN m) c.i cv
  have hlook0 := KNode.delete_live_lookup (NN m) c.i cv
  have hwf0 := KNode.lastVersionGivenDel_wf (NN m) c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))
  have hfreshN : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have hnone : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, hntake z hz, Bool.false_eq_true, ↓reduceIte, hnone, (hbase z hz).1]
  have hfreshV : ∀ z, w.next ≤ z → wValue base w z = none := by
    intro z hz
    simp only [wValue, hntake z hz, Bool.false_eq_true, ↓reduceIte, hvalnone z hz, (hbase z hz).2]
  have hnoLinkW : ∀ z, w.next ≤ z → ∀ u c', ¬ TLink (wNode c.p base w) c.i u c' z := by
    intro z hz u c' hl; have := hlinksAll u c' z hl; omega
  have hyRW : ∀ z, w.next ≤ z → ¬ TReach (wNode c.p base w) c.i w.top.rootKey z :=
    fun z hz => not_reach_fresh _ c.i _ z hT (hfreshN z hz) (fun u c' _ => hnoLinkW z hz u c')
  have hw3N : ∀ w' : W, w'.nodes = w3.nodes → w'.taken = w3.taken →
      wNode c.p base w' = wNode c.p base w := by
    intro w' h1 h2
    rw [← hr03.1]
    funext z
    simp only [wNode, h1, h2]
  -- the chain at the parent, from a state that is w3's with the leaf's new nodes
  have hpq' : (w3.path[d + (m - 1)]?).map (·.2) = some (XX (m - 1)) := by
    have := hpX (d + (m - 1)) (by omega) (by omega)
    have he : d + (m - 1) - d = m - 1 := by omega
    rw [he] at this; exact this
  have hpk' : w3.path[d + (m - 1) + 1]? = some (some (KK m), XX m) := by
    have := hpK (d + (m - 1) + 1) (by omega) (by omega)
    have he : d + (m - 1) + 1 - d = m := by omega
    rw [he] at this; exact this
  have hdm : d + m = d + (m - 1) + 1 := by omega
  rw [hdm]
  have hstayC : RootStays c (wNode c.p base w) w.top.rootKey →
      ChainNoNewRoot c (fun i => NN (i - d)) d (d + (m - 1)) := by
    intro hs
    refine ⟨hstay hs, fun i h1 h2 hnr hsp => ?_⟩
    have hpar := hspaceG _ _ (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega)))
      (hNN (i - d) (by omega)) hnr hsp
    show (NN (i - 1 - d)).leaf = false
    have hlk : (KK (i - 1 - d + 1), XX (i - 1 - d + 1)) ∈ (NN (i - 1 - d)).liveAt c.i :=
      hlinksK (i - 1 - d) (by omega)
    have he2 : i - 1 - d + 1 = i - d := by omega
    rw [he2] at hlk
    exact hpar _ _ _ (reachS_tReach _ _ _ _ (hreachX (i - 1 - d) (by omega)))
      (hNN (i - 1 - d) (by omega)) hlk
  -- the chain's premises above the leaf
  have hchainPre := fun (w1 : W) (ins : List (Nat × NodeId)) =>
    writerWP_appendKlongs_chainGRQ c base w3.path d (d + (m - 1)) (fun i => XX (i - d))
    (fun i => KK (i - d)) (fun i => NN (i - d))
    (fun i h1 h2 => hpX i h1 (by omega))
    (fun i h1 h2 => hpK i h1 (by omega))
    (fun i h1 h2 => by
      show (KK (i - d), XX (i - d)) ∈ (NN (i - 1 - d)).liveAt c.i
      have := hlinksK (i - 1 - d) (by omega)
      have he : i - 1 - d + 1 = i - d := by omega
      rw [he] at this
      exact this)
    (fun i h1 h2 hnr hpl c' z hz hc => by
      have he : i - d - 1 = i - 1 - d := by omega
      have hpl' : (NN (i - d - 1)).leaf = false := by rw [he]; exact hpl
      have hlk : (KK (i - d), XX (i - d)) ∈ (NN (i - d - 1)).liveAt c.i := by
        have := hlinksK (i - d - 1) (by omega)
        have he2 : i - d - 1 + 1 = i - d := by omega
        rw [he2] at this; exact this
      have := hrangeG _ _ _ _ _ (reachS_tReach _ _ _ _ (hreachX (i - d - 1) (by omega)))
        (hNN (i - d - 1) (by omega)) hpl' hlk (hNN (i - d) (by omega)) hnr c' z hz hc
      rw [he] at this
      exact this)
    (fun i h1 h2 hnr hsp => hlenG _ _ (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega)))
      (hNN (i - d) (by omega)) hnr hsp)
    (fun i h1 h2 => hwfG _ _ (hNN (i - d) (by omega)))
    (fun i h1 h2 => htimesG _ _ (hNN (i - d) (by omega)))
    (Or.inr hd0)
    (fun i i' h1 h2 h3 h4 he => by
      have := hdist (i - d) (i' - d) (by omega) (by omega) he
      omega)
    (fun i h1 h2 hnr hsp => by
      have hpar := hspaceG _ _ (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega)))
        (hNN (i - d) (by omega)) hnr hsp
      rcases Nat.lt_or_ge d i with hi | hi
      · refine Or.inr ⟨hi, ?_⟩
        show (NN (i - 1 - d)).leaf = false
        have hlk : (KK (i - 1 - d + 1), XX (i - 1 - d + 1)) ∈ (NN (i - 1 - d)).liveAt c.i :=
          hlinksK (i - 1 - d) (by omega)
        have he2 : i - 1 - d + 1 = i - d := by omega
        rw [he2] at hlk
        exact hpar _ _ _ (reachS_tReach _ _ _ _ (hreachX (i - 1 - d) (by omega)))
          (hNN (i - 1 - d) (by omega)) hlk
      · exact Or.inl (by omega))
    (m - 1) (Nat.le_refl _) w1 ins
  have hdm1 : d + (m - 1) - d = m - 1 := by omega
  -- the post of the delete
  have hlast : ∀ s : String, ({ w3 with trail := s :: w3.trail } : W).nodes = w3.nodes ∧
      ({ w3 with trail := s :: w3.trail } : W).taken = w3.taken ∧
      ({ w3 with trail := s :: w3.trail } : W).path = w3.path ∧
      ({ w3 with trail := s :: w3.trail } : W).next = w3.next ∧
      ({ w3 with trail := s :: w3.trail } : W).top = w3.top ∧
      ({ w3 with trail := s :: w3.trail } : W).vals = w3.vals := fun _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- a time split of the leaf, not in place
  have hcascadeT : ∀ (compact : Bool) (s : String),
      (!compact && decide (((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size > c.p.splitAbove)) = false →
      (NN m).firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        compact) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 =>
          (SegFits (wNode c.p base w4) c.i (c.p.fuel - 1) w4.top.rootKey ∨
            RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro compact s hcs hfirst
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    generalize hLv : ((⟨(NN m).leaf, ((NN m).lastVersionGivenDel c.i
      (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).ks⟩ : KNode)) = Lv
    have hrqV : ReachS (updN (wNode c.p base w) (XX m) Lv) c.i w.top.rootKey (XX (m - 1)) := by
      have hq1 : PathLen (wNode c.p base w) c.i w.top.rootKey (XX (m - 1)) (m - 1) := by
        rw [hXX]; exact hPL (m - 1) (by omega)
      have hq2 : PathLen (wNode c.p base w) c.i w.top.rootKey (XX m) m := by
        rw [hXX]; exact hPL m (by omega)
      exact tReach_reachS _ _ _ _ (tReach_updN_of_short _ c.i _ _ _ (m - 1) _ hq1
        (fun k hk => by have := PathLen.depth_unique hT _ _ _ hk hq2; omega))
    apply writerWP_handleFullWith_time_up_last' (d + (m - 1)) (XX m) (XX (m - 1)) (NN m) (NN (m - 1))
      (KK m) _ compact c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hfirst hcs (by rw [hs3]; exact hpq') (by rw [hs3]; exact hpk')
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hs4] at h1n h1next
    rw [hs1] at h1n
    rw [hLv] at h1n
    have hfree0 : w3.nodes.lookup w3.next = none := by
      cases h' : w3.nodes.lookup w3.next with
      | none => rfl
      | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next Lv := by
      rw [wNode_append_updN c.p base w3 w1 Lv h1n h1t' hfree0
        (by rw [hr03.2.2.1, hnext3]; exact hntake _ (Nat.le_refl _))]
      rw [hw3N w3 rfl rfl, hnext3]
    rw [hnext3] at h1n h1next
    have hLvwf : klongsWf Lv.ks = true := by rw [← hLv]; exact hwf0
    have hLvt : ∀ s, Klong.time s ∈ Lv.ks → s ≤ c.i := by rw [← hLv]; exact hlt
    have hLvsub : ∀ c' z, (c', z) ∈ Lv.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hLvt] at h
      rw [KNode.liveAt_of_times _ c.i hnt]
      rw [← hLv, hleq] at h
      exact hlsub c' z h
    have hLvlook : ∀ c', Lv.live.lookup c' = if c' == cv then none else (NN m).live.lookup c' := by
      intro c'; rw [← hLv, hleq]; exact hlook0 c'
    -- the tree with the parent's klong put
    obtain ⟨hTA, hRA⟩ := treeOK_timeSplit_gen (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1))
        ([(KK m, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (NN (m - 1)) (NN m) Lv
      ((NN (m - 1)).add c.i (.key (KK m) w.next)) (KK m) hT (reachS_tReach _ _ _ _ hrq) hqn hkl hnL
      (updN_self _ _ _)
      (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h)
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (m - 1) (by omega); omega), hN1]
        exact updN_self _ _ _)
      hLvsub
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3])
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
    have hchain := hchainPre w1 [(KK m, w.next)] (Or.inl ⟨_, _, rfl⟩)
      (by intro q hq; simp at hq; rw [hq, h1next]; simp)
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n, List.lookup_append, hlkX (i - d) (by omega)]; rfl
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [hN1, h1top, hs5, hr03.2.1]
        exact treeOK_updN_unreach _ c.i _ _ _ hT (hyRW _ (Nat.le_refl _)))
      (by
        intro i h1 h2
        rw [hN1, h1top, hs5, hr03.2.1]
        obtain ⟨a, ha⟩ := (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))).pathLen
        exact tReach_updN_of_short _ c.i _ _ _ a _ ha
          (fun b hb => absurd hb.reach (hyRW _ (Nat.le_refl _))))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        rw [h1n, List.lookup_append]
        have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
        cases h' : w3.nodes.lookup z with
        | none => simp [List.lookup, hb]
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu : u = w.next
        · rw [hu, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hlinksAll _ _ _ ⟨_, hnL, hLvsub c' z hc⟩; omega
        · rw [updN_ne _ _ _ _ hu] at hm
          have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (fun h0 hnr => hR0gen _ (by rw [h1top, hs5, hr03.2.1]) h0 hnr)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hzy : z = w.next
        · rw [hzy, updN_self] at hz; cases hz; exact hLvwf
        · rw [updN_ne _ _ _ _ hzy] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        have hv1 : wValue base w1 = wValue base w := by
          funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    rw [hs4, hnext3]
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, ⟨h2top, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, _⟩
    have hlkL2 : w2.nodes.lookup (XX m) = some (NN m) := by
      rw [h2frame _ (by rw [h1next]; have := hXlt m (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist m (i - d) (Nat.le_refl _) (by omega) he; omega),
        h1n, List.lookup_append, hlkL]
      rfl
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlkL2]
    simp only [putNode, writerWP_modify]
    have htk2 : w2.taken.contains (XX m) = false := by rw [h2t, h1t', hr03.2.2.1]; exact hLt
    have hN4 := wNode_upsert_updN c.p base w2
      { w2 with nodes := upsert w2.nodes (XX m) ((NN m).toPrev (c.i - 1)) } (XX m) _ rfl rfl htk2
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (XX m) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top, hs5, hr03.2.1] at h'
        exact (hRA _ h').2 rfl
      · rw [h1next] at h'; have := hXlt m (Nat.le_refl _); omega
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hres := getFromR_timeSplit_delAny (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1))
        ([(KK m, w.next)].foldl (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (NN m)
      (NN (m - 1)) Lv (KK m) pre cv rk hT hwfR hnL hleafm hnwf hnt hqn hqwf hqt hkl hrqV
      (by rw [← hLv]; exact hleafm) hLvwf hLvt hLvlook
      (by
        rw [updN_ne _ _ _ _ (fun h => by have := hXlt (m - 1) (by omega); omega), hN1]
        exact updN_self _ _ _)
      (updN_self _ _ _)
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3])
      (hnoval _ _ hnL) (hfreshV _ (Nat.le_refl _)) hqL
      (fun h => by have := hXlt m (Nat.le_refl _); omega)
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
      hLroot (fun h => by omega) hrk (keyWf_last_notin pre cv hkey) hvisL huniq
    intro hq key' hkey'
    have hq2 := hq.imp (fun hf => SegFits.of_agree (wNode c.p base w2) _ c.i (c.p.fuel - 1) w2.top.rootKey
      (fun x hx => by rw [hN4]; exact updN_ne _ _ _ _ (fun he => hxR2 (he ▸ hx))) hf) hstayC
    unfold wGet
    rw [hN4]
    show getFromR (updN (wNode c.p base w2) (XX m) ((NN m).toPrev (c.i - 1))) (wValue base w2) c.i
      c.p.fuel key' w2.top.rootKey = _
    rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
      (XX m) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
    rw [h2R hq2 key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- the delete's last version as pairs
  obtain ⟨pairs, hpks, hps⟩ :=
    KNode.lastVersionGivenDel_order (NN m) c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))
  have hlastE : (NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)) =
      ⟨true, newKlongs c.i pairs⟩ := by
    rw [← hleq, hleafm, hpks]; rfl
  have hpn : (pairs.map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hps.imp (by intro a b hab; omega))
  have hpl : ∀ c', pairs.lookup c' = if c' == cv then none else (NN m).live.lookup c' := by
    intro c'
    rw [← hlook0 c', hlastE, KNode.newKlongs_live_lookup_fold, pairLookupFold_eq_lookup pairs c' hpn]
  have hpairsN : ∀ c' z, (c', z) ∈ pairs → (c', z) ∈ (NN m).live := by
    intro c' z hm
    have hl := lookup_some_of_mem hpn hm
    rw [hpl] at hl
    by_cases hc : c' = cv
    · rw [hc] at hl; simp at hl
    · have hc' : (c' == cv) = false := by simpa using hc
      rw [hc'] at hl
      simp only [Bool.false_eq_true, ↓reduceIte] at hl
      exact lookup_some_mem hl
  -- a space split of the leaf, which existed before
  have hcascadeS : (NN (m - 1)).leaf = false → ∀ (s : String),
      c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size →
      (NN m).firstTime ≠ some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        false) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 =>
          (SegFits (wNode c.p base w4) c.i (c.p.fuel - 1) w4.top.rootKey ∨
            RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro hql s hbig hfirst
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
      cases hd : (pairs.drop (pairs.length / 2)) with
      | nil =>
        have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
        have : pairs.length = 0 := by omega
        exact absurd (List.eq_nil_of_length_eq_zero this) hpne
      | cons a _ => exact ⟨a, rfl⟩
    obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links c.i pairs hps r hr
    have hHt := halves_nil_times c.i pairs
    have hHwf := halves_newKlongs_wf true c.i pairs []
    have hrmemN : r ∈ (NN m).live := hpairsN r.1 r.2 (List.mem_of_mem_drop (List.mem_of_head? hr))
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    apply writerWP_handleFullWith_space_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m) (NN (m - 1))
      (KK m) _ c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hbig (by rw [hs3]; exact hpq') (by rw [hs3]; exact hpk')
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hleafm, hlastE] at h1n ⊢
    generalize hH : halves true c.i ⟨true, newKlongs c.i pairs⟩ [] = H at h1n hscr hfh hsh hHt hHwf ⊢
    have h12 : w3'.next ≠ w3'.next + 2 := by omega
    have h12' : w.next ≠ w.next + 2 := by omega
    have hnx : w3'.next = w.next := by rw [hs4, hnext3]
    have htk0 : w3'.taken.contains w3'.next = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (Nat.le_refl _)
    have htk2 : w3'.taken.contains (w3'.next + 2) = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (by omega)
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) w.next H.1) (w.next + 2) H.2.1 := by
      rw [wNode_two_updN c.p base w3' w1 _ _ _ _ h1n h1t h12 htk0 htk2, hw3N w3' hs1 hs2, hnx]
    rw [hnx] at h1n h1next
    rw [hnx]
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hf : ∀ c' z, (c', z) ∈ H.1.liveAt c.i → c' < H.2.2 ∧ (c', z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.1] at h
      obtain ⟨h1, h2⟩ := hfh c' z h
      rw [hscr]
      exact ⟨h1, by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2⟩
    have hs : ∀ c' z, (c', z) ∈ H.2.1.liveAt c.i →
        ∃ c0, H.2.2 ≤ c0 ∧ c' = (fun c0 => c0) c0 ∧ (c0, z) ∈ (NN m).liveAt c.i := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.2] at h
      obtain ⟨h1, h2⟩ := hsh c' z h
      rw [hscr]
      exact ⟨c', h1, rfl, by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2⟩
    have hqwf1 := KNode.add_key_wf (NN (m - 1)) c.i (KK m) w.next hqwf
    have hqt1 := KNode.add_times (NN (m - 1)) c.i (.key (KK m) w.next) (fun _ h => by cases h) hqt
    have hqlinks : ∀ c' z, (c', z) ∈ ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))).liveAt c.i →
        (c' = H.2.2 ∧ z = w.next + 2) ∨ (c' ≠ H.2.2 ∧ c' = KK m ∧ z = w.next) ∨
        (c' ≠ H.2.2 ∧ c' ≠ KK m ∧ (c', z) ∈ (NN (m - 1)).liveAt c.i) := by
      intro c' z h
      simp only [List.foldl_cons, List.foldl_nil] at h
      rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf1 hqt1 c' z h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2⟩
      · rcases KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · exact Or.inr (Or.inl ⟨h1, h3, h4⟩)
        · exact Or.inr (Or.inr ⟨h1, h3, h4⟩)
    have hXq1 : XX (m - 1) ≠ w.next := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXq2 : XX (m - 1) ≠ w.next + 2 := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXL1 : XX m ≠ w.next := fun h => by have := hXlt m (Nat.le_refl _); omega
    have hXL2 : XX m ≠ w.next + 2 := fun h => by have := hXlt m (Nat.le_refl _); omega
    obtain ⟨hTA, hRA⟩ := treeOK_spaceSplit_gen (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (w.next + 2) (NN (m - 1)) (NN m) H.1 H.2.1
      ([(KK m, w.next), (H.2.2, w.next + 2)].foldl (fun n (cv, y) => n.add c.i (.key cv y))
        (NN (m - 1)))
      (KK m) H.2.2 (fun c0 => c0) hT (reachS_tReach _ _ _ _ hrq) hqn hkl hnL (updN_self _ _ _) hqlinks
      (by rw [updN_ne _ _ _ _ hXq1.symm, hN1, updN_ne _ _ _ _ h12']; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hXq2.symm, hN1]; exact updN_self _ _ _)
      hf hs
      (by
        intro z hz1 hz2 hz3 hz4
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz4, updN_ne _ _ _ _ hz3])
      (hfreshN _ (Nat.le_refl _)) (hfreshN _ (by omega)) h12'
      (fun z hz u c' _ hl => by
        rcases hz with hz | hz <;> (subst hz; exact hnoLinkW _ (by omega) u c' hl))
    have hagree : ∀ x, TReach (wNode c.p base w) c.i w.top.rootKey x →
        wNode c.p base w1 x = wNode c.p base w x := by
      intro x hx
      have h1 : x ≠ w.next := fun h => by subst h; exact hyRW _ (Nat.le_refl _) hx
      have h2 : x ≠ w.next + 2 := fun h => by subst h; exact hyRW _ (by omega) hx
      rw [hN1, updN_ne _ _ _ _ h2, updN_ne _ _ _ _ h1]
    have hins : InsOK (NN (m - 1)) [(KK m, w.next), (H.2.2, w.next + 2)] :=
      Or.inr ⟨KK m, w.next, H.2.2, w.next + 2, rfl, by rw [hscr]; exact (hrangeL hql r.1 r.2 hrmemN).1,
        fun c'' z'' hz hlt => by rw [hscr]; exact (hrangeL hql r.1 r.2 hrmemN).2 c'' z'' hz hlt⟩
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hchain := hchainPre w1 [(KK m, w.next), (H.2.2, w.next + 2)] (by simp only [hdm1]; exact hins)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rw [h1next]
        rcases hq with hq | hq <;> (subst hq; dsimp only; omega))
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        have hx := hXlt (i - d) (by omega)
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n]
          simp only [show XX (i - d) ≠ w.next by omega, show XX (i - d) ≠ w.next + 2 by omega,
            ↓reduceIte, hs1]
          exact hlkX (i - d) (by omega)
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [h1top, hs5, hr03.2.1]
        exact treeOK_of_agree _ _ _ _ hT hagree)
      (by
        intro i h1 h2
        rw [h1top, hs5, hr03.2.1]
        exact tReach_to_agree _ _ _ _ hagree _ (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        rw [h1n]
        simp only [show z ≠ w.next by omega, show z ≠ w.next + 2 by omega, ↓reduceIte, hs1]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu2 : u = w.next + 2
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          rw [KNode.liveAt_of_times _ c.i hHt.2] at hc
          have := hlinksAll _ _ _ ⟨_, hnL, by
            rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ (hsh c' z hc).2⟩
          omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          by_cases hu1 : u = w.next
          · rw [hu1, updN_self] at hm
            simp only [Option.some.injEq] at hm
            subst hm
            rw [KNode.liveAt_of_times _ c.i hHt.1] at hc
            have := hlinksAll _ _ _ ⟨_, hnL, by
              rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ (hfh c' z hc).2⟩
            omega
          · rw [updN_ne _ _ _ _ hu1] at hm
            have := hlinksAll u c' z ⟨mm, hm, hc⟩; omega)
      (fun h0 hnr => hR0gen _ (by rw [h1top, hs5, hr03.2.1]) h0 hnr)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hz2 : z = w.next + 2
        · rw [hz2, updN_self] at hz; cases hz; exact hHwf.2
        · rw [updN_ne _ _ _ _ hz2] at hz
          by_cases hz1 : z = w.next
          · rw [hz1, updN_self] at hz; cases hz; exact hHwf.1
          · rw [updN_ne _ _ _ _ hz1] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, ⟨h2top, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, _⟩
    have hlkL2 : w2.nodes.lookup (XX m) = some (NN m) := by
      rw [h2frame _ (by rw [h1next]; have := hXlt m (Nat.le_refl _); omega)
        (fun i h1 h2 he => by have := hdist m (i - d) (Nat.le_refl _) (by omega) he; omega), h1n]
      simp only [hXL1, hXL2, ↓reduceIte, hs1]
      exact hlkL
    simp only [writerWP_bind]
    rw [writerWP_getNode_known _ _ c w2 hlkL2]
    simp only [putNode, writerWP_modify]
    have htk2' : w2.taken.contains (XX m) = false := by rw [h2t, h1t', hr03.2.2.1]; exact hLt
    have hN4 := wNode_upsert_updN c.p base w2
      { w2 with nodes := upsert w2.nodes (XX m) ((NN m).toPrev (c.i - 1)) } (XX m) _ rfl rfl htk2'
    have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (XX m) := by
      intro h
      rcases h2reach _ h with h' | h'
      · rw [h1top, hs5, hr03.2.1] at h'
        exact (hRA _ h').2 rfl
      · rw [h1next] at h'; have := hXlt m (Nat.le_refl _); omega
    have hres := getFromR_spaceSplit_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(KK m, w.next), (H.2.2, w.next + 2)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (w.next + 2) (NN m)
      (NN (m - 1)) (KK m) pre cv rk pairs hps hpne hpl hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      (hrangeL hql)
      (by rw [hH]; exact updN_self _ _ _)
      (by rw [hH, updN_ne _ _ _ _ hXq1.symm, hN1, updN_ne _ _ _ _ h12', updN_self])
      (by rw [hH, updN_ne _ _ _ _ hXq2.symm, hN1, updN_self])
      (by
        intro x hx1 hx2 hx3 hx4
        rw [updN_ne _ _ _ _ hx2, hN1, updN_ne _ _ _ _ hx4, updN_ne _ _ _ _ hx3])
      hqL hXL1.symm (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by
        have := hlinksAll x c' z ⟨xn, hxn, hz⟩; exact ⟨by omega, by omega⟩)
    intro hq key' hkey'
    have hq2 := hq.imp (fun hf => SegFits.of_agree (wNode c.p base w2) _ c.i (c.p.fuel - 1) w2.top.rootKey
      (fun x hx => by rw [hN4]; exact updN_ne _ _ _ _ (fun he => hxR2 (he ▸ hx))) hf) hstayC
    unfold wGet
    rw [hN4]
    show getFromR (updN (wNode c.p base w2) (XX m) ((NN m).toPrev (c.i - 1))) (wValue base w2) c.i
      c.p.fuel key' w2.top.rootKey = _
    rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
      (XX m) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
    rw [h2R hq2 key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- a space split in place of the leaf, which the transaction made
  have hcascadeSIP : (NN (m - 1)).leaf = false → ∀ (s : String),
      c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
        (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size →
      (NN m).firstTime = some c.i →
      WriterWP (handleFullWith (fun q more => appendKlongs (d + (m - 1)) q more) (d + (m - 1) + 1)
        (XX m) [] ((NN m).lastVersionGivenDel c.i (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv)))
        false) c ({ w3 with trail := s :: w3.trail } : W) (fun _ w4 =>
          (SegFits (wNode c.p base w4) c.i (c.p.fuel - 1) w4.top.rootKey ∨
            RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
          wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') := by
    intro hql s hbig hfirst
    have hpne : pairs ≠ [] := by
      intro he
      rw [hlastE, he] at hbig
      simp [KNode.size, newKlongs] at hbig
      omega
    obtain ⟨r, hr⟩ : ∃ r, (pairs.drop (pairs.length / 2)).head? = some r := by
      cases hd : (pairs.drop (pairs.length / 2)) with
      | nil =>
        have : pairs.length ≤ pairs.length / 2 := List.drop_eq_nil_iff.mp hd
        have : pairs.length = 0 := by omega
        exact absurd (List.eq_nil_of_length_eq_zero this) hpne
      | cons a _ => exact ⟨a, rfl⟩
    obtain ⟨hscr, hfh, hsh⟩ := halves_nil_links c.i pairs hps r hr
    have hHt := halves_nil_times c.i pairs
    have hHwf := halves_newKlongs_wf true c.i pairs []
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := hlast s
    generalize hw3' : ({ w3 with trail := s :: w3.trail } : W) = w3' at hs1 hs2 hs3 hs4 hs5 hs6
    have hnx : w3'.next = w.next := by rw [hs4, hnext3]
    apply writerWP_handleFullWith_spaceInPlace_up_last (d + (m - 1)) (XX m) (XX (m - 1)) (NN m)
      (NN (m - 1)) _ c w3' (by rw [hs1]; exact hlkL) (by rw [hs1]; exact hlkX (m - 1) (by omega))
      hql hfirst hbig (by rw [hs3]; exact hpq') (by rw [hnx]; exact hXlt m (Nat.le_refl _))
    intro w1 h1n h1t h1top h1path h1next h1vals
    rw [hleafm, hlastE] at h1n ⊢
    generalize hH : halves true c.i ⟨true, newKlongs c.i pairs⟩ [] = H at h1n hscr hfh hsh hHt hHwf ⊢
    have hXq1 : XX (m - 1) ≠ w.next := fun h => by have := hXlt (m - 1) (by omega); omega
    have hXL1 : XX m ≠ w.next := fun h => by have := hXlt m (Nat.le_refl _); omega
    have htkL : w3'.taken.contains (XX m) = false := by rw [hs2, hr03.2.2.1]; exact hLt
    have htk0 : w3'.taken.contains w3'.next = false := by
      rw [hs2, hr03.2.2.1, hnx]; exact hntake _ (Nat.le_refl _)
    have hN1 : wNode c.p base w1 = updN (updN (wNode c.p base w) (XX m) H.1) w.next H.2.1 := by
      rw [wNode_two_updN c.p base w3' w1 _ _ _ _ h1n h1t (by rw [hnx]; exact hXL1) htkL htk0,
        hw3N w3' hs1 hs2, hnx]
    rw [hnx] at h1n h1next
    rw [hnx]
    have h1t' : w1.taken = w3.taken := by rw [h1t, hs2]
    have hf' : ∀ c' z, (c', z) ∈ H.1.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i ∧ c' < H.2.2 := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.1] at h
      obtain ⟨h1, h2⟩ := hfh c' z h
      rw [hscr]
      exact ⟨by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2, h1⟩
    have hs' : ∀ c' z, (c', z) ∈ H.2.1.liveAt c.i → (c', z) ∈ (NN m).liveAt c.i ∧ H.2.2 ≤ c' := by
      intro c' z h
      rw [KNode.liveAt_of_times _ c.i hHt.2] at h
      obtain ⟨h1, h2⟩ := hsh c' z h
      rw [hscr]
      exact ⟨by rw [KNode.liveAt_of_times _ c.i hnt]; exact hpairsN _ _ h2, h1⟩
    -- the leaf with its first half: links among the leaf's
    have hsubf : ∀ x c' y, TLink (updN (wNode c.p base w) (XX m) H.1) c.i x c' y →
        TLink (wNode c.p base w) c.i x c' y := by
      intro x c' y hl
      obtain ⟨mm, hm, hc⟩ := hl
      by_cases hx : x = XX m
      · subst hx
        rw [updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        exact ⟨_, hnL, (hf' c' y hc).1⟩
      · rw [updN_ne _ _ _ _ hx] at hm; exact ⟨mm, hm, hc⟩
    have hreachf := tReach_of_sublinks _ _ c.i w.top.rootKey hsubf
    have hTf : TreeOK (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey :=
      treeOK_of_node_shrink _ _ c.i _ (XX m) (NN m) H.1 hT hnL (updN_self _ _ _)
        (fun y hy => updN_ne _ _ _ _ hy) (fun c' z h => (hf' c' z h).1)
    have hnf : ¬ TReach (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey w.next :=
      fun h => hyRW _ (Nat.le_refl _) (hreachf _ h)
    have hagree : ∀ x, TReach (updN (wNode c.p base w) (XX m) H.1) c.i w.top.rootKey x →
        wNode c.p base w1 x = updN (wNode c.p base w) (XX m) H.1 x := by
      intro x hx
      have hxn : x ≠ w.next := fun h => by subst h; exact hnf hx
      rw [hN1, updN_ne _ _ _ _ hxn]
    have hlinkT : ∀ j, j < m → TLink (wNode c.p base w) c.i (XX j) (KK (j + 1)) (XX (j + 1)) :=
      fun j hj => ⟨NN j, hNN j (by omega), hlinksK j hj⟩
    have hTA := treeOK_spaceSplitInPlace_sub (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(H.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      c.i w.top.rootKey (XX (m - 1)) (XX m) w.next (NN (m - 1)) (NN m) H.1 H.2.1 (KK m) H.2.2
      hT (reachS_tReach _ _ _ _ hrq) hqn hkl hqwf hqt hnL (updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hqL.symm, hN1, updN_ne _ _ _ _ hXL1]; exact updN_self _ _ _)
      (by rw [updN_ne _ _ _ _ hXq1.symm, hN1]; exact updN_self _ _ _)
      hf' hs'
      (by
        intro z hz1 hz2 hz3
        rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1])
      (hfreshN _ (Nat.le_refl _))
      (fun u c' _ hl => hnoLinkW _ (Nat.le_refl _) u c' hl)
    have hv1 : wValue base w1 = wValue base w := by
      funext a; simp only [wValue, h1t', h1vals, hs6, hr03.2.2.1, hr03.2.2.2.1]
    have hchain := hchainPre w1 [(H.2.2, w.next)] (Or.inl ⟨_, _, rfl⟩)
      (by
        intro q hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        subst hq
        rw [h1next]; dsimp only; omega)
      (by rw [h1path, hs3])
      (by
        intro i h1 h2
        have hx := hXlt (i - d) (by omega)
        have hxL : XX (i - d) ≠ XX m := fun he => by
          have := hdist (i - d) m (by omega) (Nat.le_refl _) he; omega
        constructor
        · show w1.nodes.lookup (XX (i - d)) = some (NN (i - d))
          rw [h1n]
          simp only [hxL, show XX (i - d) ≠ w.next by omega, ↓reduceIte, hs1]
          exact hlkX (i - d) (by omega)
        · show w1.taken.contains (XX (i - d)) = false
          rw [h1t', hr03.2.2.1]; exact htkX (i - d) (by omega))
      (by
        rw [h1top, hs5, hr03.2.1, hN1]
        exact treeOK_updN_unreach _ c.i _ _ _ hTf hnf)
      (by
        intro i h1 h2
        rw [h1top, hs5, hr03.2.1]
        exact tReach_to_agree _ _ _ _ hagree _ (tReach_chain_updN _ c.i _ hT m XX KK hlinkT (i - d)
          (by omega) (reachS_tReach _ _ _ _ (hreachX (i - d) (by omega))) H.1))
      (by
        intro z hz
        rw [h1next] at hz
        refine ⟨?_, by rw [h1t', hr03.2.2.1]; exact hntake z (by omega), (hbase z (by omega)).1⟩
        have hzL : z ≠ XX m := fun h => by have := hXlt m (Nat.le_refl _); omega
        rw [h1n]
        simp only [hzL, show z ≠ w.next by omega, ↓reduceIte, hs1]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hsrcw3 z (by rw [h']; rfl); omega)
      (by
        intro u c' z hl
        rw [hN1] at hl
        rw [h1next]
        obtain ⟨mm, hm, hc⟩ := hl
        by_cases hu2 : u = w.next
        · rw [hu2, updN_self] at hm
          simp only [Option.some.injEq] at hm
          subst hm
          have := hlinksAll _ _ _ ⟨_, hnL, (hs' c' z hc).1⟩
          omega
        · rw [updN_ne _ _ _ _ hu2] at hm
          have := hlinksAll u c' z (hsubf u c' z ⟨mm, hm, hc⟩); omega)
      (fun h0 hnr => hR0gen _ (by rw [h1top, hs5, hr03.2.1]) h0 hnr)
      (by
        intro z zn hz
        rw [hN1] at hz
        by_cases hz2 : z = w.next
        · rw [hz2, updN_self] at hz; cases hz; exact hHwf.2
        · rw [updN_ne _ _ _ _ hz2] at hz
          by_cases hz1 : z = XX m
          · rw [hz1, updN_self] at hz; cases hz; exact hHwf.1
          · rw [updN_ne _ _ _ _ hz1] at hz; exact hwfG z zn hz)
      (by
        intro z hz
        rw [hv1]
        rcases hz with hz | ⟨i, h1, h2, h3⟩
        · rw [h1next] at hz; exact hfreshV z (by omega)
        · rw [h3]; exact hnoval _ _ (hNN (i - d) (by omega)))
      (by rw [h1top, hs5, hr03.2.1]; simp only [hdm1]; exact hTA)
    simp only [hdm1] at hchain
    refine writerWP_mono hchain ?_
    rintro _ w2 ⟨_, _, _, _, _, h2R, _⟩
    have hres := getFromR_spaceSplitInPlace_del (wNode c.p base w)
      (updN (wNode c.p base w1) (XX (m - 1)) ([(H.2.2, w.next)].foldl
        (fun n (cv, y) => n.add c.i (.key cv y)) (NN (m - 1))))
      (wValue base w) c.i c.p.fuel hfuel w.top.rootKey (XX m) (XX (m - 1)) w.next (NN m)
      (NN (m - 1)) (KK m) pre cv rk pairs hps hpne hpl hnL hleafm hnwf hnt hqn hql hqwf hqt hkl'
      (hrangeL hql)
      (by rw [hH]; exact updN_self _ _ _)
      (by rw [hH, updN_ne _ _ _ _ hqL.symm, hN1, updN_ne _ _ _ _ hXL1, updN_self])
      (by rw [hH, updN_ne _ _ _ _ hXq1.symm, hN1, updN_self])
      (by
        intro x hx1 hx2 hx3
        rw [updN_ne _ _ _ _ hx2, hN1, updN_ne _ _ _ _ hx3, updN_ne _ _ _ _ hx1])
      hqL hXL1.symm (hfreshN _ (Nat.le_refl _)) hLroot (fun h => by omega) hrq hrk
      (keyWf_last_notin pre cv hkey) hvisL huniq hwfR honlyL
      (fun x xn c' z hx hxn hz => by have := hlinksAll x c' z ⟨xn, hxn, hz⟩; omega)
    intro hq key' hkey'
    unfold wGet
    rw [h2R (hq.imp id hstayC) key', hv1, h1top, hs5, hr03.2.1, hres key' hkey']
  -- the leaf's bitmap, its time split or its space split
  refine writerWP_mono (post := fun _ w4 =>
      (SegFits (wNode c.p base w4) c.i (c.p.fuel - 1) w4.top.rootKey ∨
        RootStays c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
      wGet c.p c.i base w4 key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key')
    ?_ ?_
  · by_cases hsp : ¬ ((∃ old, (NN m).ks.getLast? = some (.del old)) ∧ (NN m).lastTime = some c.i) ∧
        c.p.M ≤ (NN m).size + 1 ∧ c.p.splitAbove < ((NN m).lastVersionGivenDel c.i
          (bitsUnion (NN m).lastBitmap ((NN m).bitsOf cv))).size
    · obtain ⟨hnotTD, hfull, hbig⟩ := hsp
      cases hqlb : (NN (m - 1)).leaf with
      | true => exact absurd hbig (Nat.not_lt.mpr (hstayL hqlb hnotTD hfull))
      | false =>
        exact writerWP_appendDeleteKlong_spaceGen c (XX m) (NN m) cv (d + (m - 1)) w3 _ hlkL hne hnotTD
          hfull (fun s => by
            by_cases hf : (NN m).firstTime = some c.i
            · exact hcascadeSIP hqlb s hbig hf
            · exact hcascadeS hqlb s hbig hf)
    · exact writerWP_appendDeleteKlong_timeGenQ c base hvc pre cv (d + (m - 1)) rk (XX m) (NN m) w w3
        (fun w4 => SegFits (wNode c.p base w4) c.i (c.p.fuel - 1) w4.top.rootKey ∨
          RootStays c (wNode c.p base w) w.top.rootKey) hfuel hkey hrk hvisL huniq hwfG hnL hleafm hnt hLt hr03 hlkL hne
        (fun h1 h2 => Nat.le_of_not_lt (fun h3 => hsp ⟨h1, h2, h3⟩)) hcascadeT
  · intro _ w4 hT4
    unfold afterDelete fresh
    wpSimplify
    simp only [hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    simp only [Bool.not_false, ↓reduceIte, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
    exact hT4

/-- `writerWP_del_accessPathR` when no node that space splits is the space root
(`hspaceG`): the reading needs no premise on the fuel. -/
theorem writerWP_del_accessPath (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W)
    (hmerges : c.p.merges = false) (hsa : 1 ≤ c.p.splitAbove)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : ∀ z, w.next ≤ z → knodeOf c.p base z = none ∧ valueOf base z = none)
    (hwfG : ∀ x xn, wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (htimesG : ∀ x xn, wNode c.p base w x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ c.i)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hnoval : ∀ x xn, wNode c.p base w x = some xn → wValue base w x = none)
    (hrangeG : ∀ q qn x xn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
      wNode c.p base w q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
      wNode c.p base w x = some xn → ¬ ChainRoom c xn → ∀ c' z, (c', z) ∈ xn.live → 0 < c' →
      K ≤ c' ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → c' < c'')
    (hlenG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size → 2 ≤ xn.live.length)
    (hspaceG : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
      x ≠ w.top.rootKey ∧ ∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i → qn.leaf = false)
    (hleafG : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      L ≠ w.top.rootKey ∧ (∀ q qn K, TReach (wNode c.p base w) c.i w.top.rootKey q →
        wNode c.p base w q = some qn → (K, L) ∈ qn.liveAt c.i → qn.leaf = false ∧ LeafOrderAt qn K n) ∧
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.del (pre ++ [cv])) == key' then Op.value (.del (pre ++ [cv]))
        else wGet c.p c.i base w key') :=
  writerWP_mono (writerWP_del_accessPathR c base hvc pre cv rk w hmerges hsa hkey hrk ht hids hbase hwfG
    htimesG hT hlinksAll hnoval hrangeG hlenG (fun x xn hx hxn hnr hsp => (hspaceG x xn hx hxn hnr hsp).2)
    (fun L n h1 h2 h3 => let ⟨a, b, e, f⟩ := hleafG L n h1 h2 h3
      ⟨a, fun q qn K x y z => Or.inl (b q qn K x y z), e, f⟩) huniq)
    (fun _ _ hp => hp (Or.inr (fun rn hrn hnr => Nat.le_of_not_lt (fun hsp =>
      (hspaceG _ _ TReach.root hrn hnr hsp).1 rfl))))

end SIS.Tree
