import SIS.Tree.GetCascadePut
import SIS.Tree.GetCascadeChainG
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

/-- The walk down a key's prefix, with what it caches and the writer's path: it
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

/-- The order every node that space splits below an inner parent needs for the
reach after a cascade (`ChainOrd` at every node): a leaf's compare values from
the parent's klong on, an inner node's but its first above it. `RangeOrder`
gives it. -/
def OrdG (c : Ctx) (N : NodeId → Option KNode) (r : NodeId) : Prop :=
  ∀ q qn x xn K, TReach N c.i r q → N q = some qn → qn.leaf = false → (K, x) ∈ qn.liveAt c.i →
    N x = some xn → ¬ ChainRoom c xn → c.p.splitAbove < (xn.lastVersion c.i).size →
    ∀ c' z, (c', z) ∈ xn.live → if xn.leaf = true then K ≤ c' else (c' = 0 ∨ K < c')

/-- No new root: the space root does not space split, and every node that
space splits has an inner parent. -/
def NoNewRootG (c : Ctx) (N : NodeId → Option KNode) (r : NodeId) : Prop :=
  RootStays c N r ∧ ∀ x xn, TReach N c.i r x → N x = some xn → ¬ ChainRoom c xn →
    c.p.splitAbove < (xn.lastVersion c.i).size → ∀ q qn K, TReach N c.i r q → N q = some qn →
      (K, x) ∈ qn.liveAt c.i → qn.leaf = false

/-- The nodes reached after a leaf L gets a klong to a fresh id y: those reached
before, and y. -/
theorem tReach_updN_addKey (N : NodeId → Option KNode) (t : Time) (r L y : NodeId) (n : KNode)
    (cv : Nat) (hn : N L = some n) (hwf : klongsWf n.ks = true)
    (htimes : ∀ s, Klong.time s ∈ n.ks → s ≤ t) (hy : N y = none) :
    ∀ z, TReach (updN N L (n.add t (.key cv y))) t r z → TReach N t r z ∨ z = y := by
  have hLy : L ≠ y := fun he => by rw [he, hy] at hn; cases hn
  intro z hz
  induction hz with
  | root => exact Or.inl TReach.root
  | @link u c z _ hl ih =>
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hu : u = L
    · subst hu
      rw [updN_self] at hm
      cases hm
      rcases KNode.add_key_liveAt_mem n t cv y hwf htimes c z hc with ⟨_, hzy⟩ | ⟨_, hc'⟩
      · exact Or.inr hzy
      · rcases ih with h | h
        · exact Or.inl (TReach.link h ⟨n, hn, hc'⟩)
        · exact absurd h hLy
    · rw [updN_ne _ _ _ _ hu] at hm
      rcases ih with h | h
      · exact Or.inl (TReach.link h ⟨m, hm, hc⟩)
      · subst h; rw [hy] at hm; cases hm

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
        wNode c.p base w q = some qn → (K, x) ∈ qn.liveAt c.i →
        qn.leaf = false ∨ OrdG c (wNode c.p base w) w.top.rootKey)
    (hfullL : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      ¬ (n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false))
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w x = some n' → n'.leaf = true → key' = pre ++ [cv]) :
    WriterWP (putKv (.put (pre ++ [cv]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey ∧ w'.taken = w.taken ∧
      (∀ x, TReach (wNode c.p base w') c.i w'.top.rootKey x →
        TReach (wNode c.p base w) c.i w.top.rootKey x ∨ w.next ≤ x) ∧
      ((SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
        NoNewRootG c (wNode c.p base w) w.top.rootKey) → ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put (pre ++ [cv]) h) == key' then Op.value (.put (pre ++ [cv]) h)
        else wGet c.p c.i base w key')) := by
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
      · refine Or.inr ⟨hi, ?_⟩
        rcases hspaceG _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _ (hreachX (i - 1) (by omega))
          (hXN (i - 1) (by omega)) (hKP i hi h2).2 with h | hord
        · exact Or.inl h
        · refine Or.inr (fun _ i' h1' h2' hnr' hql' hsp' c' z hz => ?_)
          exact hord _ _ _ _ _ (hreachX (i' - 1) (by omega)) (hXN (i' - 1) (by omega)) hql'
            (hKP i' (by omega) (by omega)).2 (hXN i' (by omega)) hnr' hsp' c' z hz)
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
  intro _ wf ⟨hTf, ⟨hftop, hft, _, _, hfv⟩, _, hreachf, _, hR, _⟩
  have hwnext : wNode c.p base w w.next = none := by
    simp only [wNode, hntake w.next (Nat.le_refl _), Bool.false_eq_true, ↓reduceIte,
      (hbase w.next (Nat.le_refl _)).1]
    cases h' : w.nodes.lookup w.next with
    | none => rfl
    | some _ => have := hidn w.next (by rw [h']; rfl); omega
  refine ⟨hTf, by rw [hft, hwst], ?_, ?_⟩
  · intro x hx
    rcases hreachf x hx with h1 | ⟨h1, _⟩
    · rw [hwsN, hwstop, hnext3] at h1
      simp only [List.foldl_cons, List.foldl_nil] at h1
      rcases tReach_updN_addKey (wNode c.p base w) c.i w.top.rootKey L w.next n cv hn (hwfG _ _ hn)
        (htimesG _ _ hn) hwnext x h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (by omega)
    · rw [hwsx] at h1
      exact Or.inr (by omega)
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
    (hq.imp id (fun hs => ⟨fun ⟨_, hnr, hsp⟩ => Nat.not_le.mpr hsp (hs.1 _ (by
      dsimp only
      have h0 := hXN 0 (Nat.zero_le _)
      rw [nodeAt_zero] at h0 ⊢
      exact h0) hnr), fun i hi h2 hnr hsp => hs.2 _ _ (hreachX i h2) (hXN i h2) hnr hsp _ _ _
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

end SIS.Tree
