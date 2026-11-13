import SIS.Tree.GetCascadePut

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

end SIS.Tree
