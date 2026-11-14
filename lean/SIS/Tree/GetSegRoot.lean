import SIS.Tree.GetPutInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put into the root of a key's last segment when it is a full leaf below a
segment leaf q (bergdb 024-12, TP10; `OpGetOK`'s rules): the split replaces the
segment's tree by one from a new root R, and q's klong k1 to the old root L
names R. Reading through q: what the new tree reads from R for the rest of a
key is what L's tree with the put read (`getFromR_graft`). -/

/-! ## A link moved to a new tree -/

/-- Reader N2 is reader N1 but q's klong k1 to L names R (q a leaf in both)
and the nodes of D: the descents from the nodes outside D that N1 reaches find
what N1's find, L renamed R. -/
theorem getEqR_graft (N1 N2 : NodeId → Option KNode) (t : Time) (r0 q L R : NodeId)
    (D : NodeId → Prop) (qn1 qn2 : KNode)
    (hq1 : N1 q = some qn1) (hq2 : N2 q = some qn2) (hql1 : qn1.leaf = true) (hql2 : qn2.leaf = true)
    (hqs : ∀ c, (qn2.searchEq t c).map (·.y) =
      ((qn1.searchEq t c).map (·.y)).map (fun z => if z = L then R else z))
    (hLD : D L) (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS N1 t r0 x → ¬ D x → x ≠ q → N2 x = N1 x)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → ¬ D x → x ≠ q → N1 x = some xn →
      (c, z) ∈ xn.liveAt t → ¬ D z)
    (c : Nat) :
    ∀ (f : Nat) (x : NodeId), ReachS N1 t r0 x → ¬ D x →
      getEqR N2 t c f x = (getEqR N1 t c f x).map (fun z => if z = L then R else z) := by
  intro f
  induction f with
  | zero => intro x _ _; rfl
  | succ f ih =>
    intro x hx hD
    by_cases hxq : x = q
    · subst hxq
      simp only [getEqR, hq1, hq2, hql1, hql2, ↓reduceIte]
      exact hqs c
    · simp only [getEqR, hsame x hx hD hxq]
      cases hn : N1 x with
      | none => rfl
      | some xn =>
        simp only
        by_cases hl : xn.leaf = true
        · simp only [hl, ↓reduceIte]
          cases hs : xn.searchEq t c with
          | none => rfl
          | some fd =>
            simp only [Option.map_some, Option.some.injEq]
            have hm : (c, fd.y) ∈ xn.liveAt t := KNode.searchEq_mem xn t c fd (hwf x xn hx hn) hs
            have hzL : fd.y ≠ L := fun he => hlinks x xn c fd.y hx hD hxq hn hm (he ▸ hLD)
            simp [hzL]
        · simp only [hl, Bool.false_eq_true, ↓reduceIte]
          cases hs : xn.searchLte t c with
          | none => rfl
          | some fd =>
            simp only
            have hmem := KNode.searchLte_mem xn t c fd hs
            exact ih fd.y (ReachS.step x xn fd.c fd.y hx hn hmem) (hlinks x xn fd.c fd.y hx hD hxq hn hmem)

/-- What a descent from a node outside D finds is L or outside D. -/
theorem getEqR_res_notD (N1 : NodeId → Option KNode) (t : Time) (r0 q L : NodeId)
    (D : NodeId → Prop) (qn1 : KNode) (hq1 : N1 q = some qn1) (hql1 : qn1.leaf = true)
    (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → ¬ D x → x ≠ q → N1 x = some xn →
      (c, z) ∈ xn.liveAt t → ¬ D z)
    (hqlinks : ∀ c z, (c, z) ∈ qn1.liveAt t → D z → z = L) (c : Nat) :
    ∀ (f : Nat) (x z : NodeId), ReachS N1 t r0 x → ¬ D x → getEqR N1 t c f x = some z →
      z = L ∨ ¬ D z := by
  intro f
  induction f with
  | zero => intro x z _ _ h; simp [getEqR] at h
  | succ f ih =>
    intro x z hx hD h
    simp only [getEqR] at h
    cases hn : N1 x with
    | none => rw [hn] at h; cases h
    | some xn =>
      rw [hn] at h
      simp only at h
      by_cases hl : xn.leaf = true
      · simp only [hl, ↓reduceIte] at h
        cases hs : xn.searchEq t c with
        | none => rw [hs] at h; cases h
        | some fd =>
          rw [hs] at h
          simp only [Option.map_some, Option.some.injEq] at h
          subst h
          have hm := KNode.searchEq_mem xn t c fd (hwf x xn hx hn) hs
          by_cases hxq : x = q
          · subst hxq
            rw [hq1] at hn; cases hn
            by_cases hz : D fd.y
            · exact Or.inl (hqlinks c fd.y hm hz)
            · exact Or.inr hz
          · exact Or.inr (hlinks x xn c fd.y hx hD hxq hn hm)
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
        cases hs : xn.searchLte t c with
        | none => rw [hs] at h; cases h
        | some fd =>
          rw [hs] at h
          have hmem := KNode.searchLte_mem xn t c fd hs
          have hxq : x ≠ q := by
            intro he; subst he; rw [hq1] at hn; cases hn; exact hl hql1
          exact ih fd.y z (ReachS.step x xn fd.c fd.y hx hn hmem)
            (hlinks x xn fd.c fd.y hx hD hxq hn hmem) h

/-- The reading from the nodes outside D that N1 reaches is N2's, when the tree
from R reads in N2 as the tree from L in N1. -/
theorem getFromR_graft (N1 N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (r0 q L R : NodeId) (D : NodeId → Prop) (qn1 qn2 : KNode)
    (hq1 : N1 q = some qn1) (hq2 : N2 q = some qn2) (hql1 : qn1.leaf = true) (hql2 : qn2.leaf = true)
    (hqs : ∀ c, (qn2.searchEq t c).map (·.y) =
      ((qn1.searchEq t c).map (·.y)).map (fun z => if z = L then R else z))
    (hLD : D L)
    (hwf : ∀ x xn, ReachS N1 t r0 x → N1 x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS N1 t r0 x → ¬ D x → x ≠ q → N2 x = N1 x)
    (hlinks : ∀ x xn c z, ReachS N1 t r0 x → ¬ D x → x ≠ q → N1 x = some xn →
      (c, z) ∈ xn.liveAt t → ¬ D z)
    (hqlinks : ∀ c z, (c, z) ∈ qn1.liveAt t → D z → z = L)
    (hsub : ∀ key, key ≠ [] → getFromR N2 V t fuel key R = getFromR N1 V t fuel key L)
    (hRL : (N2 R).isSome = (N1 L).isSome) (hVL : V R = V L) :
    ∀ (key : List Nat) (x : NodeId), ReachS N1 t r0 x → ¬ D x →
      getFromR N2 V t fuel key x = getFromR N1 V t fuel key x := by
  intro key
  induction key with
  | nil => intro x _ _; rfl
  | cons c rest ih =>
    intro x hx hD
    have he := getEqR_graft N1 N2 t r0 q L R D qn1 qn2 hq1 hq2 hql1 hql2 hqs hLD hwf hsame hlinks
      c fuel x hx hD
    cases rest with
    | nil =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N1 t c fuel x with
      | none => rfl
      | some z =>
        simp only [Option.map_some, Option.bind_some]
        by_cases hz : z = L
        · simp [hz, hVL]
        · simp [hz]
    | cons d rest' =>
      simp only [getFromR]
      rw [he]
      cases hg : getEqR N1 t c fuel x with
      | none => rfl
      | some z =>
        simp only [Option.map_some]
        by_cases hz : z = L
        · simp only [hz, ↓reduceIte]
          rw [hRL]
          split
          · exact hsub (d :: rest') (by simp)
          · rfl
        · simp only [hz, ↓reduceIte]
          have hzr : ReachS N1 t r0 z := getEqR_reach N1 t r0 c hwf fuel x z hx hg
          have hzD : ¬ D z := by
            rcases getEqR_res_notD N1 t r0 q L D qn1 hq1 hql1 hwf hlinks hqlinks c fuel x z hx hD hg with
              h | h
            · exact absurd h hz
            · exact h
          have hsome : (N2 z).isSome = (N1 z).isSome := by
            by_cases hzq : z = q
            · rw [hzq, hq1, hq2]; rfl
            · rw [hsame z hzr hzD hzq]
          rw [hsome]
          split
          · exact ih z hzr hzD
          · rfl

/-- A tree from a new root R reads in N2 as the tree from L in Nm, if their
first descents find alike and they agree below on what Nm reaches from L
outside D. -/
theorem getFromR_newRoot_sim (Nm N2 : NodeId → Option KNode) (V : NodeId → Option Nat)
    (t : Time) (fuel : Nat) (L R : NodeId) (D : NodeId → Prop)
    (hfirst : ∀ c, getEqR N2 t c fuel R = getEqR Nm t c fuel L)
    (hwf : ∀ x xn, ReachS Nm t L x → Nm x = some xn → klongsWf xn.ks = true)
    (hsame : ∀ x, ReachS Nm t L x → ¬ D x → N2 x = Nm x)
    (hlinks : ∀ x xn c z, ReachS Nm t L x → Nm x = some xn → (c, z) ∈ xn.liveAt t → ¬ D z) :
    ∀ key, getFromR N2 V t fuel key R = getFromR Nm V t fuel key L := by
  intro key
  cases key with
  | nil => rfl
  | cons c rest =>
    cases rest with
    | nil => simp only [getFromR]; rw [hfirst c]
    | cons d rest' =>
      simp only [getFromR]
      rw [hfirst c]
      cases hg : getEqR Nm t c fuel L with
      | none => rfl
      | some z =>
        simp only
        have hz : ReachS Nm t L z := getEqR_reach Nm t L c hwf fuel L z ReachS.root hg
        obtain ⟨x, xn, cz, hx, hxn, _, hzm⟩ := getEqR_leaf_link Nm t L c hwf fuel L z ReachS.root hg
        have hzD := hlinks x xn cz z hx hxn hzm
        rw [hsame z hz hzD]
        split
        · exact getFromR_avoid Nm N2 V t fuel L D hwf hsame hlinks _ z hz hzD
        · rfl

theorem reachS_trans (N : NodeId → Option KNode) (t : Time) (r a : NodeId) (ha : ReachS N t r a) :
    ∀ b, ReachS N t a b → ReachS N t r b := by
  intro b hb
  induction hb with
  | root => exact ha
  | step x n c z _ hn hz ih => exact ReachS.step x n c z ih hn hz

/-! ## The writer: the walk down a key's prefix to any suffix -/

/-- `writerWP_putSegs_prefix_src` to any nonempty suffix of segments. -/
theorem writerWP_putSegs_walk_src (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (key : Key) (value : Option Nat) (sfx : List Nat) (hsfx : sfx ≠ []) (post : Bool → W → Prop) :
    ∀ (pre : List Nat) (r rk : NodeId) (w : W),
      (∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ sfx) r,
        w.taken.contains q.1 = false) →
      segRootR (wNode c.p base w) c.i c.p.fuel pre r = some rk →
      w.path.getLast?.map (·.2) = some r →
      (∀ w', ReadsAs c.p base w w' → w'.path.getLast?.map (·.2) = some rk →
        (∀ z, (w'.nodes.lookup z).isSome = true →
          (w.nodes.lookup z).isSome = true ∨ (c.view z).isSome = true) →
        WriterWP (putSegs key value sfx rk) c w' post) →
      WriterWP (putSegs key value (pre ++ sfx) r) c w post := by
  intro pre
  induction pre with
  | nil =>
    intro r rk w _ hrk hp hcont
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    rw [List.nil_append]
    exact hcont w (ReadsAs.refl _ _ _) hp (fun z hz => Or.inl hz)
  | cons s rest ih =>
    intro r rk w ht hrk hp hcont
    have hne : rest ++ sfx ≠ [] := by simp [hsfx]
    rw [List.cons_append, putSegs.eq_3 key value r s (rest ++ sfx) hne]
    simp only [segRootR] at hrk
    cases hg : getEqR (wNode c.p base w) c.i s c.p.fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk
      split at hrk
      · rename_i hysome
        obtain ⟨d, rest', he⟩ : ∃ d rest', rest ++ sfx = d :: rest' := by
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
        refine writerWP_mono (writerWP_and (writerWP_descendLte_reads s c base hvc c.p.fuel r w ht1)
          (writerWP_descendLte_cache s c base hvc c.p.fuel r w ht1)) ?_
        intro L w3 ⟨⟨hr3, n, hn, hnl, hlk3, _, hget⟩, ⟨_, hsrc3, _⟩⟩
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
          · intro w' hr' hp' hsrc'
            refine hcont w' (ReadsAs.trans _ _ _ _ _ hr04 hr') hp' (fun z hz => ?_)
            rcases hsrc' z hz with h1 | h1
            · subst hw4
              exact hsrc3 z h1
            · exact Or.inr h1
      · cases hrk

/-! ## The writer: a time split below a segment leaf -/

/-- A search for compare value c finds a klong of c. -/
theorem KNode.searchEq_c (n : KNode) (t : Time) (c : Nat) (fd : Found)
    (h : n.searchEq t c = some fd) : fd.c = c := by
  unfold KNode.searchEq at h
  generalize (prefixAt n.ks t).zipIdx = l at h
  suffices hs : ∀ (l : List (Klong × Nat)) (acc : Option Time × List Nat × Option Found),
      (∀ f, acc.2.2 = some f → f.c = c) → ∀ f, (l.foldl (fun (acc : Option Time × List Nat × Option Found) (k, i) =>
      if acc.2.1.contains i then acc else
        match k with
        | .time x => (some x, acc.2.1, acc.2.2)
        | .key c' y => if c' == c then (acc.1, acc.2.1, some ⟨c, i, acc.1.getD 0, y⟩) else acc
        | .del b => (acc.1, b, match acc.2.2 with
          | some f => if b.contains f.idx then none else some f
          | none => none)) acc).2.2 = some f → f.c = c from
    hs l _ (fun f hf => by simp at hf) fd h
  intro l
  induction l with
  | nil => intro acc hacc f hf; exact hacc f hf
  | cons e rest ih =>
    intro acc hacc f hf
    rw [List.foldl_cons] at hf
    apply ih _ _ f hf
    intro f' hf'
    rcases e with ⟨k, i⟩
    simp only at hf'
    split at hf'
    · exact hacc f' hf'
    · split at hf'
      · exact hacc f' hf'
      · split at hf'
        · simp only [Option.some.injEq] at hf'; rw [← hf']
        · exact hacc f' hf'
      · simp only at hf'
        split at hf'
        · rename_i f0 hf0
          split at hf'
          · cases hf'
          · simp only [Option.some.injEq] at hf'; rw [← hf']; exact hacc f0 hf0
        · cases hf'

theorem fromVisits_append_gen (N : NodeId → Option KNode) (t : Time) (fuel : Nat)
    (k : Nat) (rest : List Nat) :
    ∀ (pre : List Nat) (r rk : NodeId), segRootR N t fuel pre r = some rk →
      ∀ q ∈ eqVisits N t k fuel rk, q ∈ fromVisits N t fuel (pre ++ k :: rest) r := by
  intro pre
  induction pre with
  | nil =>
    intro r rk hrk q hq
    simp only [segRootR, Option.some.injEq] at hrk
    subst hrk
    cases rest with
    | nil => exact hq
    | cons d rest' => simp only [List.nil_append, fromVisits]; exact List.mem_append_left _ hq
  | cons c pre ih =>
    intro r rk hrk q hq
    have hne : pre ++ k :: rest ≠ [] := by simp
    obtain ⟨d, rest', he⟩ : ∃ d rest', pre ++ k :: rest = d :: rest' := by
      cases h : pre ++ k :: rest with
      | nil => exact absurd h hne
      | cons d rest' => exact ⟨d, rest', rfl⟩
    simp only [segRootR] at hrk
    simp only [List.cons_append]
    rw [he]
    simp only [fromVisits]
    apply List.mem_append_right
    cases hg : getEqR N t c fuel r with
    | none => rw [hg] at hrk; cases hrk
    | some y =>
      rw [hg] at hrk
      simp only at hrk ⊢
      split at hrk
      · rw [← he]; exact ih y rk hrk q hq
      · cases hrk

theorem segRootR_snoc (N : NodeId → Option KNode) (t : Time) (fuel : Nat) (k : Nat) :
    ∀ (pre : List Nat) (r : NodeId), segRootR N t fuel (pre ++ [k]) r =
      (segRootR N t fuel pre r).bind (fun rk => match getEqR N t k fuel rk with
        | some y => if (N y).isSome then some y else none
        | none => none) := by
  intro pre
  induction pre with
  | nil =>
    intro r
    simp only [List.nil_append, segRootR, Option.bind_some]
    cases getEqR N t k fuel r <;> rfl
  | cons c pre ih =>
    intro r
    simp only [List.cons_append, segRootR]
    cases getEqR N t c fuel r with
    | none => rfl
    | some y =>
      simp only
      split
      · exact ih y
      · rfl

/-! ## The rule: a time split of a segment root below a segment leaf -/

/-! ## The writer: a space split of a segment root below a segment leaf -/

/-! ## The rule: a space split of a segment root below a segment leaf -/

end SIS.Tree
