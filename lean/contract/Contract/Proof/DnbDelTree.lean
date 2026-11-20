/-
bergdb 030-36: PE's plan of a transaction of puts and deletes against Java's
count for a segment's tree from its root (`tree_stepD`) and for the space
root (`space_stepD`), given plan at a lower fuel (`PlanPD`).

A planned root is settled alone (`settleRoot`). Besides the settles of a
transaction of puts (the root kept, or cut into parts with new roots above),
deletes can empty the root or leave an inner root with one entry, which then
collapses into its child, maybe repeatedly.

* An emptied root: a delete passes it, since a root that no delete passes
  keeps its live entries (`PlanSpecD.shape`) and a segment tree's root has
  one at least. The tree is gone; nothing more is written.
* A collapse: a delete passes the root, since an inner root that no delete
  passes keeps its two live entries at least (RootsOK). Then Java gives the
  leaf above a klong for the tree (`PlanSpecD.ci`, `up`). What is written is
  at most what emit writes for the planned root: a collapse follows children
  that give their parent one entry each, none cut into parts, so no new root
  is made (`settle_one`).
* The space root, emptied: a new empty segment leaf, one key node, paid for
  by the old root's own write (it changed, so its decision writes one node at
  least).
-/
import Contract.Proof.DnbDelLeaf

namespace Contract.PE

open DNB PeProof

variable {cf : Cfg} {i : Time} {s : Tree}

/-- Java's parameters meet `Cfg.Ok` from node size 8. -/
theorem cfgOk_java8 {b G H : Nat} (hb : 8 ≤ b) : Cfg.Ok (Cfg.java b G H) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Cfg.java, splitAbove, cutSize, mergeCap] <;> omega

/-- **A collapse writes no more.** A root that is an untouched node, or a
planned node that is not empty, and is not cut into two parts or more,
settles into a node whose emit writes at most its own key nodes. -/
theorem settle_one {g : Nat} {space : Bool} : ∀ (f h : Nat) (v v'' : VN),
    ((∃ y, v = .old y) ∨ (VOk cf s g h v ∧ v.isEmpty = false)) → One v →
    settleRoot cf i s f g v space = some (some v'') → vcost v'' ≤ vcost v
  | 0, _, _, _, _, _, hs => by simp [settleRoot] at hs
  | f + 1, h, v, v'', hv, hk, hs => by
    unfold settleRoot at hs
    cases v with
    | old y =>
      simp only at hs
      cases hgk : getKey s y with
      | none => rw [hgk] at hs; cases hs
      | some m =>
        rw [hgk] at hs
        simp only at hs
        split at hs
        · rename_i c z _
          split at hs
          · simp only [Option.some.injEq] at hs; subst hs; exact le_refl _
          · have := settle_one f h (.old z) v'' (Or.inl ⟨z, rfl⟩) trivial hs
            simpa [vcost] using this
        · simp only [Option.some.injEq] at hs; subst hs; exact le_refl _
    | node base g' h' j es F dec =>
      obtain ⟨hvok, hne⟩ : VOk cf s g h (.node base g' h' j es F dec) ∧
          (VN.node base g' h' j es F dec).isEmpty = false := by
        rcases hv with ⟨y, hy⟩ | hv
        · cases hy
        · exact hv
      obtain ⟨hh1, hh2⟩ := hvok.ht
      subst hh1 hh2
      simp only [VN.isEmpty] at hne
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hs
      split at hs
      · -- one entry: the child
        rename_i hone
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hone
        obtain ⟨hh, hF1⟩ := hone
        obtain ⟨h'', rfl⟩ : ∃ h'', h' = h'' + 1 := ⟨h' - 1, by omega⟩
        split at hs
        · rename_i c ch
          cases hvok with
          | inner hk' hne' _ hF _ =>
            have hch := hk' (c, ch) (by simp)
            have hchne := hne' (c, ch) (by simp)
            have hlen : (ents c ch).length = 1 := by
              rw [hF, renameHead_length] at hF1; simpa using hF1
            have hone : One ch := by
              cases ch with
              | old _ => trivial
              | node b2 g2 h2 j2 es2 F2 dec2 =>
                intro k hk2
                subst hk2
                by_contra hk3
                rw [ents_parts_length (by omega)] at hlen
                omega
            have ih := settle_one f h'' ch v'' (Or.inr ⟨hch, hchne⟩) hone hs
            simp only [vcost, vcostL]
            omega
        · cases hs
      · split at hs
        · rename_i k
          split at hs
          · rename_i hk2
            exact absurd (hk k rfl) (by omega)
          · simp only [Option.some.injEq] at hs; subst hs; exact le_refl _
        · simp only [Option.some.injEq] at hs; subst hs; exact le_refl _

/-- A planned node whose final list has at most one entry is one node. -/
theorem one_of_dec {g h : Nat} {base : Option NodeId} {j : Bool} {es : List (Nat × VN)}
    {F : List (Nat × Option NodeId)} {dec : Dec} (hv : VOk cf s g h (.node base g h j es F dec))
    (hF : F.length ≤ 1) : One (.node base g h j es F dec) := by
  intro k hk
  have hd : DecOk dec F := by cases hv <;> assumption
  by_contra h2
  have := hd k hk (by omega)
  omega

/-- What settle adds above a root, against Java's new roots above it. -/
theorem raOf_le_rootT {b : Nat} (hb : 8 ≤ b) {dec : Dec} {r : SR}
    (hdec : ∀ k, dec = .parts k → 0 < r.ov ∧ k ≤ r.parts) : raOf b dec ≤ rootT b r true := by
  cases dec with
  | parts k =>
    obtain ⟨hov, hkp⟩ := hdec k rfl
    simp only [raOf, rootT, true_and, Nat.pos_iff_ne_zero.mp hov, ne_eq, not_false_eq_true,
      ↓reduceIte]
    split
    · exact le_max_of_le_right (rootsAbove_mono hb hkp)
    · exact Nat.zero_le _
  | same => simp [raOf]
  | append => simp [raOf]

/-- **A segment's tree from its root, puts and deletes**, given plan at a
lower fuel. -/
theorem tree_stepD {b G H F : Nat} (hb : 8 ≤ b) (IH : PlanPD b (Cfg.java b G H) i s F) :
    TreePPD b (Cfg.java b G H) i s (F + 1) := by
  intro y g ops acc res acc' fs hsh hgood hfill hlive hops hne hfs hNo hpt
  obtain ⟨n, hobj, hgk, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  have hgkD : DNB.getKey s y = some n := hgk
  rw [planTree.eq_def] at hpt
  simp only at hpt
  rw [hgk] at hpt
  simp only at hpt
  rw [show (Cfg.java b G H).htOf n.level = htIn (Cfg.java b G H) s y by simp [htIn, hobj]] at hpt
  cases hpl : plan (Cfg.java b G H) i s F y g (htIn (Cfg.java b G H) s y) ops acc with
  | none => rw [hpl] at hpt; cases hpt
  | some q =>
    obtain ⟨v, acc1⟩ := q
    rw [hpl] at hpt
    simp only at hpt
    have hp := IH y g _ ops acc v acc1 true fs hsh hgood hfill hops hne hfs hNo hpl
    obtain ⟨lo, hi, hg⟩ := hgood
    obtain ⟨_, _, _, hvok⟩ := plan_inst (cfgOk_java8 hb) hpl hsh hg
    obtain ⟨n', es, Fl, dec, hgk', rfl, hdec, hlen, _⟩ := hp.shape
    rw [hgkD] at hgk'
    obtain rfl : n = n' := by injection hgk'
    obtain ⟨T, hTn, hkw⟩ := hp.kw
    have hlne := hlive n hgkD
    have hlne' : 1 ≤ (live n.ks).length := by
      cases h0 : live n.ks with
      | nil => exact absurd h0 hlne
      | cons _ _ => simp
    by_cases hFe : Fl = []
    · -- the root emptied: a delete passes it
      subst hFe
      obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := by
        cases F with
        | zero => simp [settleRoot] at hpt
        | succ F' => exact ⟨F', rfl⟩
      rw [settleRoot.eq_def] at hpt
      simp at hpt
      obtain ⟨rfl, rfl⟩ := hpt
      refine ⟨by omega, fun _ => ?_, fun _ h => by cases h⟩
      by_contra h0
      simp only [List.length_nil] at hlen
      omega
    · by_cases hcol : htIn (Cfg.java b G H) s y ≠ 0 ∧ Fl.length = 1
      · -- a collapse: a delete passes the root, and the leaf above gets a klong
        have hleaf' : n.leaf = false := by rw [hleaf]; simpa using hcol.1
        have h2 := (filled_key hfill hobj).1 hleaf' rfl
        have hnd : (sbPlan b s fs y g ops true).nd ≠ 0 := fun h0 => by
          rw [h0] at hlen; omega
        have hci := hp.ci hnd hcol.1
        have hup : 1 ≤ (sbPlan b s fs y g ops true).up := by
          rw [hp.up]
          simp only [true_and]
          rw [ite_eq_left (by omega)]
          omega
        split at hpt
        · cases hpt
        · simp only [Option.some.injEq, Prod.mk.injEq] at hpt
          obtain ⟨rfl, rfl⟩ := hpt
          exact ⟨by omega, fun _ => by omega, fun _ h => by cases h⟩
        · rename_i v1 hset
          have hv1 := settle_one F _ _ v1 (Or.inr ⟨hvok, by simpa [VN.isEmpty] using hFe⟩)
            (one_of_dec hvok (by omega)) hset
          split at hpt
          · rename_i c y' acc2 hem
            simp only [Option.some.injEq, Prod.mk.injEq] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            have hkw2 := emit_kw v1 acc1 _ acc2 hem
            exact ⟨by omega, fun h => (by cases h), fun _ _ => Or.inr hup⟩
          · cases hpt
      · -- settled as for puts
        have hF1 : htIn (Cfg.java b G H) s y ≠ 0 → Fl.length ≠ 1 := fun h0 h1 => hcol ⟨h0, h1⟩
        split at hpt
        · cases hpt
        · rename_i hset
          obtain ⟨v', hv, _⟩ := settle_chain (i := i) (s := s) hb F (some y) _ false es Fl dec _ hFe
            hF1 hset
          cases hv
        · rename_i v1 hset
          obtain ⟨v', hv, hv', hsame⟩ := settle_chain (i := i) (s := s) hb F (some y) _ false es Fl dec _
            hFe hF1 hset
          cases hv
          split at hpt
          · rename_i c y' acc2 hem
            simp only [Option.some.injEq, Prod.mk.injEq] at hpt
            obtain ⟨rfl, rfl⟩ := hpt
            have hkw2 := emit_kw v1 acc1 _ acc2 hem
            have hra := raOf_le_rootT hb hdec
            refine ⟨by omega, fun h => (by cases h), fun y'' hy'' => ?_⟩
            cases hy''
            by_cases hov : (sbPlan b s fs y g ops true).ov = 0
            · left
              have hnp : ∀ k, dec ≠ .parts k := by
                intro k hk'; have := (hdec k hk').1; omega
              rw [hsame (fun k _ => hnp k)] at hem
              have := emit_base hnp hem
              simp only [List.cons.injEq, Prod.mk.injEq, and_true] at this
              exact this.2
            · right
              rw [hp.up]
              simp only [hov, ↓reduceIte]
              omega
          · cases hpt

/-! ## The space root -/

theorem mkNode_some_dec {x : NodeId} {g h : Nat} {j : Bool} {es0 : List (Nat × VN)} {v : VN}
    (hm : mkNode cf i s (some x) g h j es0 = some v) :
    ∃ n es F, getKey s x = some n ∧ v = .node (some x) g h j es F (decideNode cf i (some n) j F) := by
  unfold mkNode at hm
  simp only at hm
  split at hm
  · rename_i n hn
    simp only [Option.some.injEq] at hm
    exact ⟨n, _, _, hn, hm.symm⟩
  · cases hm

/-- The plan of x is decided against x by `decideNode`. -/
theorem plan_decD {f : Nat} {x : NodeId} {g h : Nat} {ops : List Op} {acc acc' : Acc} {v : VN}
    (hp : plan cf i s f x g h ops acc = some (v, acc')) :
    ∃ n es F, getKey s x = some n ∧
      v = .node (some x) g h false es F (decideNode cf i (some n) false F) := by
  cases f with
  | zero => simp [plan] at hp
  | succ f =>
    unfold plan at hp
    split at hp
    · cases hp
    · split at hp
      · rename_i hh
        split at hp
        · cases hp
        · split at hp
          · rename_i w hm
            simp only [Option.some.injEq, Prod.mk.injEq] at hp
            obtain ⟨rfl, _⟩ := hp
            have h0 : h = 0 := by simpa using hh
            subst h0
            exact mkNode_some_dec hm
          · cases hp
      · dsimp only at hp
        split at hp
        · cases hp
        · split at hp
          · cases hp
          · split at hp
            · rename_i w hm
              simp only [Option.some.injEq, Prod.mk.injEq] at hp
              obtain ⟨rfl, _⟩ := hp
              exact mkNode_some_dec hm
            · cases hp

/-- A node of the tree before that changes writes one key node at least. -/
theorem dcost_decide_pos {n : KNode} {j : Bool} {F : List (Nat × Option NodeId)}
    (hne : (live n.ks).map (fun q => (q.1, some q.2)) ≠ F) :
    1 ≤ dcost (decideNode cf i (some n) j F) := by
  have hc : ∀ m, 1 ≤ cutParts cf m := by
    intro m; unfold cutParts; split <;> omega
  unfold decideNode
  simp only
  split
  · rename_i h; exact absurd (by simpa using h) hne
  · split
    · split
      · split
        · simp [dcost]
        · simp only [dcost]; exact hc _
      · simp [dcost]
    · simp only [dcost]; exact hc _

/-- **The space root, puts and deletes**: PE's key writes from the space
root's plan to its emit are at most Java's count of it. -/
theorem space_stepD {b G H : Nat} (hb : 8 ≤ b) {r : NodeId} {h f f' fs : Nat} {ops : List Op}
    {acc acc1 acc2 : Acc} {v rv : VN} {E : List (Nat × NodeId)} {lo : Nat} {hi : Option Nat}
    (hsh : Shaped (Cfg.java b G H) s 0 h r) (hg : Good s r lo hi)
    (hfill : Filled (Cfg.java b G H) s true r)
    (hpl : plan (Cfg.java b G H) i s f r 0 h ops acc = some (v, acc1))
    (hp : PlanSpecD b s 0 h r true v acc acc1 (sbPlan b s fs r 0 ops true))
    (hset : settleRoot (Cfg.java b G H) i s f' 0 v true = some (some rv))
    (hem : emit (Cfg.java b G H) i s rv acc1 = some (E, acc2)) :
    kw acc2 ≤ kw acc + (sbPlan b s fs r 0 ops true).cnt := by
  obtain ⟨_, _, _, hvok⟩ := plan_inst (cfgOk_java8 hb) hpl hsh hg
  obtain ⟨n0, es0, F0, hgk0, hv0⟩ := plan_decD hpl
  obtain ⟨n, es, Fl, dec, hgk, rfl, hdec, hlen, _⟩ := hp.shape
  obtain ⟨T, hTn, hkw⟩ := hp.kw
  have hkw2 := emit_kw rv acc1 E acc2 hem
  suffices hsuf : vcost rv ≤ vcost (.node (some r) 0 h false es Fl dec) +
      rootT b (sbPlan b s fs r 0 ops true) true by omega
  obtain ⟨n1, hobj, hgk1, hlev, hleaf, _, _⟩ := shaped_getKey hsh
  by_cases hFe : Fl = []
  · -- emptied: a new empty segment leaf, paid for by the old root's write
    subst hFe
    obtain ⟨f'', rfl⟩ : ∃ f'', f' = f'' + 1 := by
      cases f' with
      | zero => simp [settleRoot] at hset
      | succ f'' => exact ⟨f'', rfl⟩
    rw [settleRoot.eq_def] at hset
    by_cases hh : h = 0
    · subst hh
      simp at hset
      subst hset
      omega
    · simp only [List.isEmpty_nil, ↓reduceIte, Bool.not_true, Bool.false_eq_true, beq_iff_eq, hh]
        at hset
      unfold mkNode at hset
      simp only [beq_self_eq_true, ↓reduceIte, List.flatMap_nil] at hset
      simp only [Option.map_eq_some_iff] at hset
      obtain ⟨w, hw, hwrv⟩ := hset
      have hGH : ¬ ((Cfg.java b G H).G < 0 || (Cfg.java b G H).H < 0) = true := by simp
      rw [ite_eq_right hGH] at hw
      simp only [Option.some.injEq] at hw hwrv
      subst hw; subst hwrv
      have hdec0 : decideNode (Cfg.java b G H) i none false [] = .parts 1 := by
        simp only [decideNode, Bool.false_eq_true, ↓reduceIte, List.length_nil, cutParts_java]
        simp [cutPartsBound]
      rw [hdec0, show vcost (VN.node none 0 0 false [] [] (.parts 1)) = 1 from rfl]
      -- the old root changed: one key node at least
      have hleaf' : n1.leaf = false := by rw [hleaf]; simpa using hh
      have h2 := (filled_key hfill hobj).1 hleaf' rfl
      injection hv0 with _ _ _ _ _ hF0 hd0
      rw [hgk1] at hgk0
      obtain rfl : n1 = n0 := by injection hgk0
      subst hF0
      rw [hd0]
      simp only [vcost]
      have : (live n1.ks).map (fun q => (q.1, some q.2)) ≠ [] := by
        intro h0
        have := congrArg List.length h0
        simp only [List.length_map, List.length_nil] at this
        omega
      have := dcost_decide_pos (cf := Cfg.java b G H) (i := i) (j := false) this
      omega
  · by_cases hcol : h ≠ 0 ∧ Fl.length = 1
    · have := settle_one f' h _ rv (Or.inr ⟨hvok, by simpa [VN.isEmpty] using hFe⟩)
        (one_of_dec hvok (by omega)) hset
      omega
    · have hF1 : h ≠ 0 → Fl.length ≠ 1 := fun h0 h1 => hcol ⟨h0, h1⟩
      obtain ⟨v', hv, hv', _⟩ := settle_chain (i := i) (s := s) hb f' (some r) h false es Fl dec _
        hFe hF1 hset
      cases hv
      have hra := raOf_le_rootT hb hdec
      omega

end Contract.PE
