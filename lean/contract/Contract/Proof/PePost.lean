/-
bergdb 030-21: from what emit writes to the contract's clauses 1 and 2. PeEmitSpec.lean
(`emit_spec`) proves that the written nodes hold the planned abstract tree
(`Holds`), and 026-24's theory (PeAbsOrder.lean) that the plan is in order
(`WF`). This file turns that into the contract's terms, through every segment:

* the tree after: a node that holds an abstract node in order, whose leaves'
  payloads are sound (`PayGood`), is sound (`good_of_holds`), holds the
  abstract node's contents with each payload's keys (`L_of_holds`), and is
  shaped as PE's trees are (`shaped_of_holds`);
* the tree before, the converse: a sound node shaped as PE's trees, read as an
  abstract node (`view`), is in order (`view_wfe`), its payloads are sound and
  shaped (`view_pay`), it holds the view's contents with each payload's keys
  (`view_L_pays`), in strictly increasing compare order (`view_sorted`);
* an unchanged subtree keeps all of it (`good_transfer`, `L_transfer`,
  `shaped_transfer`, `payGood_transfer`);
* a tree whose times are at most t is itself at t (`tree_at_self`);
* clauses 1 and 2: a sound root whose reached nodes meet `nodeOk` passes the
  contract's walk (`walk_of_good`, the converse of `walk_good`), so `invOk`
  (`invOk_of_good`), and the contents are what the root holds (`contents_eq`).

Segments: a segment leaf's payload of a long compare value is the root of the
next segment's tree; `PayGood` asks that root to be sound (`Good`), which is
`good_of_holds` for segment g + 1 (`payGood_of_holds`, `shaped_pay_of_holds`),
or `good_transfer` for an old root kept as it was. So the segments are put
together by the caller, from the last segment up; so are the rules of one node
over the nodes reached (`NOk`: `nok_of_holds`, `nok_transfer`), the premise of
`clauses_of_holds`, clauses 1 and 2 from what the space root holds.

Against the statement asked for (030-21): `L_transfer` needs no `Good`; the
clauses need no premise on the tree before (`s.root`); the walk's premise is
`nodeOk` of the key nodes the walk reaches. Each result with `WF` (the plan in
order and nonempty) has a form with `WFE` (an empty root) where it holds.
-/
import Contract.Proof.PeEmitSpec

namespace Contract.PE

open PeProof PeProof.Abs

variable {cf : Cfg}

/-- What a segment leaf of segment g needs of its payload (c, y) in T: a value
for a short c; for a long c a key node of a lower level than the leaf's, with a
live klong, sound as the root of a segment tree. -/
def PayGood (cf : Cfg) (T : Tree) (g : Nat) (c : Nat) (y : NodeId) : Prop :=
  (isLong c = false → ∃ v, T.obj y = some (.val v)) ∧
  (isLong c = true → ∃ m, T.obj y = some (.key m) ∧ m.level < cf.lev g 0 ∧ live m.ks ≠ [] ∧
    Good T y 0 none)

/-! ## Lists -/

theorem belowHi_of_below {c : Nat} {hi : Option Nat} (h : Below c hi) : belowHi c hi = true := by
  cases hi with
  | none => rfl
  | some b => simpa [belowHi, Below] using h

theorem below_of_belowHi' {c : Nat} {hi : Option Nat} (h : belowHi c hi = true) : Below c hi := by
  cases hi with
  | none => trivial
  | some b => simpa [belowHi, Below] using h

/-- The child at a position of a list of children in order. -/
theorem kidsWF_split {β : Type} {W : Nat → Option Nat → β → Prop} {lo : Nat} {hi : Option Nat} :
    ∀ (pre : List (Nat × β)) (c : Nat) (x : β) (post : List (Nat × β)),
      KidsWF W lo hi (pre ++ (c, x) :: post) → W (max lo c) (nxt post hi) x
  | [], _, _, _, h => h.1
  | (_, _) :: pre, c, x, post, h => kidsWF_split pre c x post h.2

theorem forall₂_split {α β : Type} {R : α → β → Prop} :
    ∀ (pre : List α) (a : α) (post : List α) {l : List α} {l' : List β},
      List.Forall₂ R l l' → l = pre ++ a :: post →
      ∃ pre' b post', l' = pre' ++ b :: post' ∧ R a b ∧ List.Forall₂ R post post'
  | [], a, post, l, l', hf, he => by
    subst he
    cases hf with
    | cons hab hrest => exact ⟨[], _, _, rfl, hab, hrest⟩
  | x :: pre, a, post, l, l', hf, he => by
    subst he
    cases hf with
    | cons hab hrest =>
      obtain ⟨pre', b, post', h1, h2, h3⟩ := forall₂_split pre a post hrest rfl
      exact ⟨_ :: pre', b, post', by rw [h1]; rfl, h2, h3⟩

theorem forall₂_flatMap_congr {α β γ : Type} {R : α → β → Prop} {f : α → List γ} {g : β → List γ} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      (∀ a ∈ l, ∀ b ∈ l', R a b → f a = g b) → l.flatMap f = l'.flatMap g
  | [], [], List.Forall₂.nil, _ => rfl
  | a :: l, b :: l', List.Forall₂.cons hab hr, h => by
    simp only [List.flatMap_cons]
    rw [h a List.mem_cons_self b List.mem_cons_self hab,
      forall₂_flatMap_congr hr (fun a' ha' b' hb' hr' =>
        h a' (List.mem_cons_of_mem _ ha') b' (List.mem_cons_of_mem _ hb') hr')]

theorem nextHi_nxt {β : Type} {R : Nat × NodeId → Nat × β → Prop}
    (hR : ∀ a b, R a b → a.1 = b.1) {post : List (Nat × NodeId)} {post' : List (Nat × β)}
    (h : List.Forall₂ R post post') (hi : Option Nat) : nextHi post hi = nxt post' hi := by
  cases h with
  | nil => rfl
  | cons hab _ => simp [nextHi, nxt, hR _ _ hab]

/-! ## The tree after: what holds an abstract node in order is sound -/

/-- The live klongs of an inner node that holds A, with A's children. -/
theorem holdsE_of {T : Tree} {g h : Nat} {L : List (Nat × NodeId)} {K : List (Nat × Node h)}
    (h1 : L.map (·.1) = K.map (·.1)) (h2 : ∀ p ∈ L.zip K, Holds cf T g h p.1.2 p.2.2) :
    List.Forall₂ (fun e a => e.1 = a.1 ∧ Holds cf T g h e.2 a.2) L K := by
  have hf := forall₂_of_cvs h1
  rw [List.forall₂_iff_zip] at hf ⊢
  exact ⟨hf.1, fun hab => ⟨hf.2 hab, h2 _ hab⟩⟩

/-- A node that holds a nonempty abstract node has a live klong. -/
theorem Holds.live_ne {T : Tree} {g : Nat} : ∀ {h : Nat} {x : NodeId} {A : Node h},
    Holds cf T g h x A → A ≠ [] →
      ∃ m, T.obj x = some (.key m) ∧ m.level = cf.lev g h ∧ live m.ks ≠ []
  | 0, _, _, hx, hne => by
    cases hx with
    | leaf hobj _ hlev _ _ hlive => exact ⟨_, hobj, hlev, by rw [hlive]; exact hne⟩
  | _ + 1, _, _, hx, hne => by
    cases hx with
    | inner hobj _ hlev _ _ _ hcv _ =>
      refine ⟨_, hobj, hlev, fun h0 => hne ?_⟩
      rw [h0] at hcv
      exact List.map_eq_nil_iff.mp hcv.symm

theorem mem_content_succ {h : Nat} {A : Node (h + 1)} {a : Nat × Node h} (ha : a ∈ kids A)
    {p : Nat × Nat} (hp : p ∈ content h a.2) : p ∈ content (h + 1) A := by
  show p ∈ (kids A).flatMap (fun e => content h e.2)
  exact List.mem_flatMap.mpr ⟨a, ha, hp⟩

/-- **The tree after is sound**: a node of segment g at height h that holds the
abstract node A, in order with the range [lo, hi), whose leaves' payloads are
sound, is sound with that range (`Good`, what the contract's walk finds). -/
theorem good_of_holds : ∀ (h : Nat) {T : Tree} {g : Nat} {x : NodeId} {A : Node h} {lo : Nat}
    {hi : Option Nat}, Holds cf T g h x A → WF h lo hi A →
      (∀ p ∈ content h A, PayGood cf T g p.1 p.2) → Good T x lo hi
  | 0, T, g, x, A, lo, hi, hx, hw, hp => by
    cases hx with
    | @leaf _ n _ hobj hleaf hlev _ hok hlive =>
      have hok' := nodeOk_iff.mp hok
      obtain ⟨_, _, w3⟩ := hw
      have hp' : ∀ c y, (c, y) ∈ live n.ks → PayGood cf T g c y := by
        intro c y hm; rw [hlive] at hm; exact hp _ hm
      have hb : ∀ c y, (c, y) ∈ live n.ks → lo ≤ c ∧ Below c hi := by
        intro c y hm; rw [hlive] at hm; exact w3 _ hm
      refine Good.mk x lo hi n hobj hok'.2.1 ?_ ?_ ?_ ?_ ?_ ?_
      · intro c y hm; exact belowHi_of_below (hb c y hm).2
      · intro _ c y hm; exact (hb c y hm).1
      · intro _ c y hm hs; exact (hp' c y hm).1 hs
      · intro c y hm hk
        obtain ⟨m, h1, h2, h3, _⟩ := (hp' c y hm).2 (hk hleaf)
        exact ⟨m, h1, hlev ▸ h2, h3⟩
      · intro _ c y hm hs
        obtain ⟨m, _, _, _, h4⟩ := (hp' c y hm).2 hs
        exact h4
      · intro hl; simp [hleaf] at hl
  | h + 1, T, g, x, A, lo, hi, hx, hw, hp => by
    cases hx with
    | @inner _ _ n _ hobj hleaf hlev _ _ hok hcv hkids =>
      have hok' := nodeOk_iff.mp hok
      have hE := holdsE_of hcv hkids
      obtain ⟨_, _, w3, w4⟩ := hw
      have hpos : ∀ pre c y post, live n.ks = pre ++ (c, y) :: post →
          ∃ a : Node h, Holds cf T g h y a ∧ WF h (max lo c) (nextHi post hi) a ∧
            (∀ p ∈ content h a, PayGood cf T g p.1 p.2) := by
        intro pre c y post he
        obtain ⟨pre', b, post', hK, ⟨hb1, hb2⟩, hpost⟩ := forall₂_split pre (c, y) post hE he
        refine ⟨b.2, hb2, ?_, ?_⟩
        · rw [hK] at w4
          have := kidsWF_split pre' b.1 b.2 post' w4
          rw [nextHi_nxt (fun a b h => h.1) hpost hi]
          simp only at hb1
          rw [hb1]
          exact this
        · intro p hp'
          exact hp p (mem_content_succ (by rw [hK]; simp) hp')
      have hkey : ∀ c y, (c, y) ∈ live n.ks →
          ∃ m, T.obj y = some (.key m) ∧ m.level < n.level ∧ live m.ks ≠ [] := by
        intro c y hm
        obtain ⟨pre, post, he⟩ := List.append_of_mem hm
        obtain ⟨a, ha, hwa, _⟩ := hpos pre c y post he
        obtain ⟨m, h1, h2, h3⟩ := ha.live_ne (WF_ne_nil h _ _ a hwa)
        refine ⟨m, h1, ?_, h3⟩
        rw [h2, hlev, Cfg.lev_succ]; omega
      refine Good.mk x lo hi n hobj hok'.2.1 ?_ (fun hl => by simp [hleaf] at hl)
        (fun hl => by simp [hleaf] at hl) (fun c y hm _ => hkey c y hm)
        (fun hl => by simp [hleaf] at hl) ?_
      · intro c y hm
        have hc : c ∈ (kids A).map (·.1) := by
          rw [← hcv]; exact List.mem_map.mpr ⟨(c, y), hm, rfl⟩
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
        exact belowHi_of_below (w3 b hb)
      · intro _ pre c y post he
        obtain ⟨a, ha, hwa, hpa⟩ := hpos pre c y post he
        exact good_of_holds h ha hwa hpa

/-- A node that holds the empty abstract node: no live klong. -/
theorem Holds.empty {T : Tree} {g : Nat} : ∀ {h : Nat} {x : NodeId}, Holds cf T g h x [] →
    ∃ n, T.obj x = some (.key n) ∧ nodeOk cf.params T n = true ∧ live n.ks = []
  | 0, _, hx => by
    cases hx with
    | leaf hobj _ _ _ hok hlive => exact ⟨_, hobj, hok, hlive⟩
  | _ + 1, _, hx => by
    cases hx with
    | inner hobj _ _ _ _ hok hcv _ =>
      exact ⟨_, hobj, hok, List.map_eq_nil_iff.mp hcv⟩

theorem good_of_live_nil {T : Tree} {x : NodeId} {n : KNode} (hobj : T.obj x = some (.key n))
    (hok : nodeOk cf.params T n = true) (hl : live n.ks = []) (lo : Nat) (hi : Option Nat) :
    Good T x lo hi :=
  Good.mk x lo hi n hobj (nodeOk_iff.mp hok).2.1 (by simp [hl]) (by simp [hl]) (by simp [hl])
    (by simp [hl]) (by simp [hl]) (by simp [hl])

theorem content_nil : ∀ (h : Nat), content h ([] : Node h) = []
  | 0 => rfl
  | _ + 1 => rfl

/-- `good_of_holds` with the abstract node in order or empty (an empty root). -/
theorem good_of_holds_wfe {h : Nat} {T : Tree} {g : Nat} {x : NodeId} {A : Node h} {lo : Nat}
    {hi : Option Nat} (hx : Holds cf T g h x A) (hw : WFE h lo hi A)
    (hp : ∀ p ∈ content h A, PayGood cf T g p.1 p.2) : Good T x lo hi := by
  rcases hw with rfl | hw
  · obtain ⟨n, hobj, hok, hl⟩ := hx.empty
    exact good_of_live_nil hobj hok hl lo hi
  · exact good_of_holds h hx hw hp

/-- **What the tree after holds**: a node that holds the abstract node A, in
order, whose leaves' payloads are sound, holds A's payloads in their order, each
payload what its klong holds (a short compare value: the key of one segment and
its value; a long one: the next segment's keys with the compare value in front). -/
theorem L_of_holds : ∀ (h : Nat) {T : Tree} {g : Nat} {x : NodeId} {A : Node h} {lo : Nat}
    {hi : Option Nat}, Holds cf T g h x A → WF h lo hi A →
      (∀ p ∈ content h A, PayGood cf T g p.1 p.2) →
      L T x = (content h A).flatMap (fun p => klongList T true (L T) p.1 p.2)
  | 0, T, g, x, A, lo, hi, hx, hw, hp => by
    have hg := good_of_holds 0 hx hw hp
    cases hx with
    | @leaf _ n _ hobj hleaf _ _ _ hlive =>
      rw [hg.L_eq hobj, hleaf, hlive]
      rfl
  | h + 1, T, g, x, A, lo, hi, hx, hw, hp => by
    have hg := good_of_holds (h + 1) hx hw hp
    cases hx with
    | @inner _ _ n _ hobj hleaf _ _ _ _ hcv hkids =>
      have hE := holdsE_of hcv hkids
      rw [hg.L_eq hobj, hleaf]
      show _ = ((kids A).flatMap (fun e => content h e.2)).flatMap _
      rw [List.flatMap_assoc]
      apply forall₂_flatMap_congr hE
      intro e _ a ha hea
      obtain ⟨lo', hi', hwa⟩ := kidsWF_each hw.2.2.2 a ha
      simp only [klongList, Bool.false_eq_true, ite_false]
      exact L_of_holds h hea.2 hwa (fun p hp' => hp p (mem_content_succ ha hp'))

/-- `L_of_holds` with the abstract node in order or empty. -/
theorem L_of_holds_wfe {h : Nat} {T : Tree} {g : Nat} {x : NodeId} {A : Node h} {lo : Nat}
    {hi : Option Nat} (hx : Holds cf T g h x A) (hw : WFE h lo hi A)
    (hp : ∀ p ∈ content h A, PayGood cf T g p.1 p.2) :
    L T x = (content h A).flatMap (fun p => klongList T true (L T) p.1 p.2) := by
  rcases hw with rfl | hw
  · obtain ⟨n, hobj, hok, hl⟩ := hx.empty
    rw [(good_of_live_nil hobj hok hl 0 none).L_eq hobj, hl, content_nil]
    rfl
  · exact L_of_holds h hx hw hp

/-- **The tree after is shaped as PE's trees**: a node that holds the abstract
node A, in order, whose leaves' long payloads are shaped roots of segment
g + 1, is shaped at segment g and height h. -/
theorem shaped_of_holds : ∀ (h : Nat) {T : Tree} {g : Nat} {x : NodeId} {A : Node h} {lo : Nat}
    {hi : Option Nat}, Holds cf T g h x A → WF h lo hi A →
      (∀ p ∈ content h A, isLong p.1 = true → Shaped cf T (g + 1) (htIn cf T p.2) p.2) →
      Shaped cf T g h x
  | 0, T, g, x, A, lo, hi, hx, _, hp => by
    cases hx with
    | @leaf _ n _ hobj hleaf hlev hG _ hlive =>
      exact Shaped.leaf hobj hleaf hlev hG (fun c y hm hl => by rw [hlive] at hm; exact hp _ hm hl)
  | h + 1, T, g, x, A, lo, hi, hx, hw, hp => by
    cases hx with
    | @inner _ _ n _ hobj hleaf hlev hG hH _ hcv hkids =>
      have hE := holdsE_of hcv hkids
      refine Shaped.inner hobj hleaf hlev hG hH ?_ ?_
      · rw [← List.head?_map, hcv, List.head?_map]
        exact hw.1
      · intro c y hm
        obtain ⟨a, ha, hea⟩ := forall₂_exists hE (c, y) hm
        obtain ⟨lo', hi', hwa⟩ := kidsWF_each hw.2.2.2 a ha
        exact shaped_of_holds h hea.2 hwa (fun p hp' => hp p (mem_content_succ ha hp'))

/-! ## The tree before: a sound node shaped as PE's trees, read as an abstract node -/

theorem nextHi_eq_nxt' {β : Type} (f : NodeId → β) (post : List (Nat × NodeId)) (hi : Option Nat) :
    nextHi post hi = nxt (post.map (fun cy => (cy.1, f cy.2))) hi := by
  cases post with
  | nil => rfl
  | cons a r => rfl

/-- Children given by the positions of a list of live klongs, each with its range. -/
theorem kidsWF_of_pos_map {β : Type} {W : Nat → Option Nat → β → Prop} {lo : Nat} {hi : Option Nat}
    (f : NodeId → β) : ∀ (l : List (Nat × NodeId)),
    (∀ c y pre post, l = pre ++ (c, y) :: post → W (max lo c) (nextHi post hi) (f y)) →
    KidsWF W lo hi (l.map (fun cy => (cy.1, f cy.2)))
  | [], _ => trivial
  | (c, y) :: rest, h => by
    refine ⟨?_, kidsWF_of_pos_map f rest (fun c' y' pre post hp => ?_)⟩
    · have := h c y [] rest rfl
      rw [nextHi_eq_nxt' f] at this
      exact this
    · exact h c' y' ((c, y) :: pre) post (by rw [hp]; rfl)

theorem Shaped.inv_leaf {s : Tree} {g : Nat} {x : NodeId} (hsh : Shaped cf s g 0 x) :
    ∃ n, s.obj x = some (.key n) ∧ n.leaf = true ∧ n.level = cf.lev g 0 ∧ g ≤ cf.G ∧
      ∀ c y, (c, y) ∈ live n.ks → isLong c = true → Shaped cf s (g + 1) (htIn cf s y) y := by
  cases hsh with
  | leaf hobj hleaf hlev hG hk => exact ⟨_, hobj, hleaf, hlev, hG, hk⟩

theorem Shaped.inv_inner {s : Tree} {g h : Nat} {x : NodeId} (hsh : Shaped cf s g (h + 1) x) :
    ∃ n, s.obj x = some (.key n) ∧ n.leaf = false ∧ n.level = cf.lev g (h + 1) ∧ g ≤ cf.G ∧
      h + 1 ≤ cf.H ∧ (live n.ks).head?.map (·.1) = some 0 ∧
      ∀ c y, (c, y) ∈ live n.ks → Shaped cf s g h y := by
  cases hsh with
  | inner hobj hleaf hlev hG hH hhead hk => exact ⟨_, hobj, hleaf, hlev, hG, hH, hhead, hk⟩

/-- **The tree before is in order** (4 (a)): a sound node shaped as PE's trees,
read as an abstract node, is in order with its range, or empty; and nonempty
if it has a live klong. -/
theorem view_wfe : ∀ (h : Nat) {s : Tree} {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Good s x lo hi → Shaped cf s g h x → WFE h lo hi (view h s x) ∧
      (∀ n, s.obj x = some (.key n) → live n.ks ≠ [] → view h s x ≠ [])
  | 0, s, g, x, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, hleaf, _, _, _⟩ := hsh.inv_leaf
    cases hg with
    | mk _ _ _ n' hobj' _ hhi hlo _ _ _ _ =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      rw [view_zero hobj]
      refine ⟨?_, fun n0 h0 hne => ?_⟩
      · by_cases he : live n.ks = []
        · left; exact he
        · right
          exact ⟨he, live_sorted n.ks, fun e he' =>
            ⟨hlo hleaf e.1 e.2 he', below_of_belowHi' (hhi e.1 e.2 he')⟩⟩
      · rw [hobj] at h0
        obtain rfl : n = n0 := by injection h0 with h1; injection h1
        exact hne
  | h + 1, s, g, x, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, hleaf, _, _, _, hhead, hkids⟩ := hsh.inv_inner
    cases hg with
    | mk _ _ _ n' hobj' _ hhi _ _ hkey _ hkid =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      have hv := view_succ (h := h) hobj
      refine ⟨?_, fun n0 h0 hne => ?_⟩
      · by_cases he : live n.ks = []
        · left
          show kids (view (h + 1) s x) = []
          rw [hv, he]; rfl
        · right
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [hv, List.head?_map, Option.map_map]
            exact hhead
          · rw [hv]
            exact List.Pairwise.map _ (fun a b h => h) (live_sorted n.ks)
          · rw [hv]
            intro e he'
            obtain ⟨⟨c, y⟩, hm, rfl⟩ := List.mem_map.mp he'
            exact below_of_belowHi' (hhi c y hm)
          · rw [hv]
            refine kidsWF_of_pos_map (fun y => view h s y) (live n.ks) (fun c y pre post he2 => ?_)
            have hm : (c, y) ∈ live n.ks := by rw [he2]; simp
            have hgy := hkid hleaf pre c y post he2
            obtain ⟨m, hm1, _, hm3⟩ := hkey c y hm (by simp [hleaf])
            obtain ⟨w1, w2⟩ := view_wfe h hgy (hkids c y hm)
            rcases w1 with w1 | w1
            · exact absurd w1 (w2 m hm1 hm3)
            · exact w1
      · rw [hobj] at h0
        obtain rfl : n = n0 := by injection h0 with h1; injection h1
        intro hv0
        have : kids (view (h + 1) s x) = [] := by rw [hv0]; rfl
        rw [hv] at this
        exact hne (List.map_eq_nil_iff.mp this)

/-- **The tree before's payloads** (4 (b)): every payload of a sound node
shaped as PE's trees is sound, and a long one is a shaped root of the next
segment. -/
theorem view_pay : ∀ (h : Nat) {s : Tree} {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Good s x lo hi → Shaped cf s g h x → ∀ p ∈ content h (view h s x),
      PayGood cf s g p.1 p.2 ∧ (isLong p.1 = true → Shaped cf s (g + 1) (htIn cf s p.2) p.2)
  | 0, s, g, x, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, hleaf, hlev, _, hk⟩ := hsh.inv_leaf
    intro p hp
    have hp' : p ∈ live n.ks := by
      have : p ∈ view 0 s x := hp
      rwa [view_zero hobj] at this
    cases hg with
    | mk _ _ _ n' hobj' _ _ _ hval hkey hseg _ =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      refine ⟨⟨fun hs => hval hleaf p.1 p.2 hp' hs, fun hs => ?_⟩, fun hs => hk p.1 p.2 hp' hs⟩
      obtain ⟨m, h1, h2, h3⟩ := hkey p.1 p.2 hp' (fun _ => hs)
      exact ⟨m, h1, hlev ▸ h2, h3, hseg hleaf p.1 p.2 hp' hs⟩
  | h + 1, s, g, x, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, hleaf, _, _, _, _, hkids⟩ := hsh.inv_inner
    intro p hp
    have hp' : p ∈ (kids (view (h + 1) s x)).flatMap (fun e => content h e.2) := hp
    rw [view_succ hobj] at hp'
    simp only [List.mem_flatMap, List.mem_map] at hp'
    obtain ⟨_, ⟨⟨c, y⟩, hm, rfl⟩, hpy⟩ := hp'
    obtain ⟨m, lo', hi', _, _, _, hgy⟩ := hg.child hobj hm (by simp [hleaf])
    exact view_pay h hgy (hkids c y hm) p hpy

/-- **What the tree before holds** (4 (c)): a sound node shaped as PE's trees
holds its view's payloads in their order, each what its klong holds. -/
theorem view_L_pays : ∀ (h : Nat) {s : Tree} {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat},
    Good s x lo hi → Shaped cf s g h x →
      L s x = (content h (view h s x)).flatMap (fun p => klongList s true (L s) p.1 p.2)
  | 0, s, g, x, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, hleaf, _, _, _⟩ := hsh.inv_leaf
    rw [hg.L_eq hobj, hleaf]
    show _ = (view 0 s x).flatMap _
    rw [view_zero hobj]
    rfl
  | h + 1, s, g, x, lo, hi, hg, hsh => by
    obtain ⟨n, hobj, hleaf, _, _, _, _, hkids⟩ := hsh.inv_inner
    rw [hg.L_eq hobj, hleaf]
    show _ = ((kids (view (h + 1) s x)).flatMap (fun e => content h e.2)).flatMap _
    rw [view_succ hobj, List.flatMap_map, List.flatMap_assoc]
    apply List.flatMap_congr
    rintro ⟨c, y⟩ hm
    obtain ⟨m, lo', hi', _, _, _, hgy⟩ := hg.child hobj hm (by simp [hleaf])
    simp only [klongList, Bool.false_eq_true, ite_false]
    exact view_L_pays h hgy (hkids c y hm)

/-- A child of a list of children in order is in order from max(lo, c). -/
theorem kidsWF_lo_le {β : Type} {W : Nat → Option Nat → β → Prop} :
    ∀ {lo : Nat} {hi : Option Nat} {l : List (Nat × β)}, KidsWF W lo hi l →
      ∀ e ∈ l, ∃ hi', W (max lo e.1) hi' e.2
  | _, _, [], _, _, he => by simp at he
  | lo, hi, (c, x) :: rest, hk, e, he => by
    obtain ⟨h1, h2⟩ := hk
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, h1⟩
    · exact kidsWF_lo_le h2 e he

theorem kids_sorted (h : Nat) (IH : ∀ lo hi (x : Node h), WF h lo hi x → (content h x).Pairwise CvLtA) :
    ∀ (l : List (Nat × Node h)) (lo : Nat) (hi : Option Nat), KidsWF (WF h) lo hi l →
      l.Pairwise CvLtA → (l.flatMap (fun e => content h e.2)).Pairwise CvLtA
  | [], _, _, _, _ => List.Pairwise.nil
  | (c, a) :: rest, lo, hi, hk, hp => by
    obtain ⟨h1, h2⟩ := hk
    rw [List.flatMap_cons, List.pairwise_append]
    refine ⟨IH _ _ a h1, kids_sorted h IH rest lo hi h2 hp.of_cons, ?_⟩
    intro e he e' he'
    have hb := (WF_bounds h _ _ a h1 e he).2
    obtain ⟨⟨c', a'⟩, hm', he''⟩ := List.mem_flatMap.mp he'
    obtain ⟨hi', hw'⟩ := kidsWF_lo_le h2 _ hm'
    have hb' := (WF_bounds h _ _ a' hw' e' he'').1
    cases rest with
    | nil => simp at hm'
    | cons r rr =>
      obtain ⟨c1, a1⟩ := r
      simp only [nxt, Below] at hb
      have hc : c1 ≤ c' := by
        rcases List.mem_cons.mp hm' with h0 | h0
        · simp only [Prod.mk.injEq] at h0; omega
        · exact le_of_lt (List.rel_of_pairwise_cons hp.of_cons h0)
      show e.1 < e'.1
      simp only at hb'
      omega

/-- The contents of a node in order are in strictly increasing compare order. -/
theorem content_sorted : ∀ (h : Nat) {lo : Nat} {hi : Option Nat} {x : Node h}, WF h lo hi x →
    (content h x).Pairwise CvLtA
  | 0, _, _, _, hw => hw.2.1
  | h + 1, lo, hi, x, hw => by
    show ((kids x).flatMap (fun e => content h e.2)).Pairwise CvLtA
    exact kids_sorted h (fun lo hi x hx => content_sorted h hx) (kids x) lo hi hw.2.2.2 hw.2.1

/-- **The tree before's payloads in order** (4 (d)). -/
theorem view_sorted (h : Nat) {s : Tree} {g : Nat} {x : NodeId} {lo : Nat} {hi : Option Nat}
    (hg : Good s x lo hi) (hsh : Shaped cf s g h x) :
    (content h (view h s x)).Pairwise (fun a b => a.1 < b.1) := by
  rcases (view_wfe h hg hsh).1 with he | hw
  · rw [he, content_nil]; exact List.Pairwise.nil
  · exact content_sorted h hw

/-! ## An unchanged subtree -/

theorem mem_R_self (s : Tree) (y : NodeId) : y ∈ R s y := mem_reachAt_self' _ _ _

/-- More fuel reaches more. -/
theorem reachAt_mono {s : Tree} : ∀ (f f' : Nat) (y : NodeId), f ≤ f' →
    ∀ z ∈ reachAt s f y, z ∈ reachAt s f' y
  | 0, f', y, _, z, hz => by
    simp only [reachAt, List.mem_singleton] at hz
    subst hz
    exact mem_reachAt_self' s f' z
  | _ + 1, 0, _, hle, _, _ => by omega
  | f + 1, f' + 1, y, hle, z, hz => by
    cases ho : s.obj y with
    | none =>
      simp only [reachAt, ho, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      exact hz
    | some o =>
      cases o with
      | val v =>
        rw [reachAt_val ho] at hz ⊢
        exact hz
      | key n =>
        rw [reachAt_key ho, List.mem_cons, List.mem_flatMap] at hz ⊢
        rcases hz with rfl | ⟨cy, hcy, hz⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨cy, hcy, reachAt_mono f f' cy.2 (by omega) z hz⟩

/-- What a child reaches, its parent reaches, if the child's fuel is at most
the parent's level. -/
theorem R_child {s : Tree} {x : NodeId} {n : KNode} (hobj : s.obj x = some (.key n)) {c : Nat}
    {y : NodeId} (hm : (c, y) ∈ live n.ks) (hf : s.fuel y ≤ n.level) : ∀ z ∈ R s y, z ∈ R s x := by
  intro z hz
  have hR : R s x = reachAt s (n.level + 1) x := by simp [R, Tree.fuel, hobj]
  rw [hR, reachAt_key hobj, List.mem_cons, List.mem_flatMap]
  exact Or.inr ⟨(c, y), hm, reachAt_mono _ _ y hf z hz⟩

/-- A sound node's children have their fuel at most its level. -/
theorem good_child_fuel {s : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s x lo hi)
    {n : KNode} (hobj : s.obj x = some (.key n)) {c : Nat} {y : NodeId} (hm : (c, y) ∈ live n.ks) :
    s.fuel y ≤ n.level := by
  rcases good_kids hg hobj c y hm with ⟨m, hm1, hm2, _⟩ | ⟨v, hv⟩
  · simp [Tree.fuel, hm1]; omega
  · simp [Tree.fuel, hv]

/-- What a node holds, read with any fuel, is the same in T if T has every node
the walk with that fuel reaches as s has it. -/
theorem listAt_same {s T : Tree} : ∀ (f : Nat) (y : NodeId),
    (∀ z ∈ reachAt s f y, T.obj z = s.obj z) → listAt T f y = listAt s f y
  | 0, _, _ => rfl
  | f + 1, y, h => by
    have hy : T.obj y = s.obj y := h y (mem_reachAt_self' _ _ _)
    cases ho : s.obj y with
    | none => simp only [listAt, hy, ho]
    | some o =>
      cases o with
      | val v => simp only [listAt, hy, ho]
      | key n =>
        simp only [listAt, hy, ho]
        apply List.flatMap_congr
        rintro ⟨c, w⟩ hcw
        have hsub : ∀ z ∈ reachAt s f w, T.obj z = s.obj z := by
          intro z hz
          apply h z
          rw [reachAt_key ho, List.mem_cons, List.mem_flatMap]
          exact Or.inr ⟨(c, w), hcw, hz⟩
        have hw : T.obj w = s.obj w := hsub w (mem_reachAt_self' _ _ _)
        have hl := listAt_same f w hsub
        unfold klongList
        simp only [hw, hl]

/-- **An unchanged subtree holds what it held** (5): if T has every node that
y reaches in s as s has it, y holds in T what it holds in s. -/
theorem L_transfer {s T : Tree} {y : NodeId} (hag : ∀ z ∈ R s y, T.obj z = s.obj z) :
    L T y = L s y := by
  have hy : T.obj y = s.obj y := hag y (mem_R_self s y)
  have hf : T.fuel y = s.fuel y := by simp [Tree.fuel, hy]
  unfold L
  rw [hf]
  exact listAt_same _ y hag

/-- **An unchanged subtree is sound** (5). -/
theorem good_transfer {s T : Tree} {y : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good s y lo hi) :
    (∀ z ∈ R s y, T.obj z = s.obj z) → Good T y lo hi := by
  induction hg with
  | mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid ihseg ihkid =>
    intro hag
    have hG : Good s x lo hi := Good.mk x lo hi n hobj hwf hhi hlo hval hkey hseg hkid
    have hsub : ∀ c w, (c, w) ∈ live n.ks → ∀ z ∈ R s w, T.obj z = s.obj z :=
      fun c w hm z hz => hag z (R_child hobj hm (good_child_fuel hG hobj hm) z hz)
    have hT : ∀ c w, (c, w) ∈ live n.ks → T.obj w = s.obj w :=
      fun c w hm => hsub c w hm w (mem_R_self s w)
    have hTx : T.obj x = some (.key n) := by rw [hag x (mem_R_self s x), hobj]
    refine Good.mk x lo hi n hTx hwf hhi hlo ?_ ?_ ?_ ?_
    · intro hl c w hm hs
      rw [hT c w hm]
      exact hval hl c w hm hs
    · intro c w hm hk
      rw [hT c w hm]
      exact hkey c w hm hk
    · intro hl c w hm hs
      exact ihseg hl c w hm hs (hsub c w hm)
    · intro hl pre c w post he
      have hm : (c, w) ∈ live n.ks := by rw [he]; simp
      exact ihkid hl pre c w post he (hsub c w hm)

/-- **An unchanged subtree is shaped as it was** (5). -/
theorem shaped_transfer {s T : Tree} {g h : Nat} {y : NodeId} (hsh : Shaped cf s g h y) :
    (∀ z ∈ R s y, T.obj z = s.obj z) → Shaped cf T g h y := by
  induction hsh with
  | @leaf g x n hobj hleaf hlev hG hk ih =>
    intro hag
    have hTx : T.obj x = some (.key n) := by rw [hag x (mem_R_self s x), hobj]
    refine Shaped.leaf hTx hleaf hlev hG (fun c w hm hl => ?_)
    obtain ⟨m, hmo, hmlev, _, hG', hH'⟩ := shaped_obj (hk c w hm hl)
    have hf : s.fuel w ≤ n.level := by
      simp only [Tree.fuel, hmo, hmlev, hlev]
      exact lev_next cf hG' hH'
    have hsub : ∀ z ∈ R s w, T.obj z = s.obj z := fun z hz => hag z (R_child hobj hm hf z hz)
    have hw : T.obj w = s.obj w := hsub w (mem_R_self s w)
    have hht : htIn cf T w = htIn cf s w := by simp [htIn, hw]
    rw [hht]
    exact ih c w hm hl hsub
  | @inner g h x n hobj hleaf hlev hG hH hhead hk ih =>
    intro hag
    have hTx : T.obj x = some (.key n) := by rw [hag x (mem_R_self s x), hobj]
    refine Shaped.inner hTx hleaf hlev hG hH hhead (fun c w hm => ?_)
    obtain ⟨m, hmo, hmlev, _, _, _⟩ := shaped_obj (hk c w hm)
    have hf : s.fuel w ≤ n.level := by
      simp only [Tree.fuel, hmo, hmlev, hlev, Cfg.lev_succ]
      exact le_refl _
    exact ih c w hm (fun z hz => hag z (R_child hobj hm hf z hz))

/-- **An unchanged payload stays sound** (5). -/
theorem payGood_transfer {s T : Tree} {g c : Nat} {y : NodeId} (hp : PayGood cf s g c y)
    (hag : ∀ z ∈ R s y, T.obj z = s.obj z) : PayGood cf T g c y := by
  have hy : T.obj y = s.obj y := hag y (mem_R_self s y)
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · rw [hy]; exact hp.1 hs
  · obtain ⟨m, h1, h2, h3, h4⟩ := hp.2 hs
    exact ⟨m, by rw [hy]; exact h1, h2, h3, good_transfer h4 hag⟩

/-! ## The times -/

theorem takeWhile_self {α : Type} {p : α → Bool} : ∀ {l : List α}, (∀ a ∈ l, p a = true) →
    l.takeWhile p = l
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.takeWhile, h a List.mem_cons_self]
    rw [takeWhile_self (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem prefixAt_of_le {ks : List Klong} {t : Time} (h : ∀ u, Klong.time u ∈ ks → u ≤ t) :
    prefixAt ks t = ks := by
  unfold prefixAt
  apply takeWhile_self
  intro k hk
  cases k with
  | time u => simpa using h u hk
  | key _ _ => rfl
  | del _ => rfl

/-- **A tree whose times are at most t is itself at t** (6): every klong time of
every key node and every root time at most t. (For the tree after at the
transaction's time i, and for the tree before at i - 1.) -/
theorem tree_at_self {s : Tree} {t : Time}
    (hk : ∀ x n, s.obj x = some (.key n) → ∀ u, Klong.time u ∈ n.ks → u ≤ t)
    (hr : ∀ r ∈ s.roots, r.1 ≤ t) : s.at t = s := by
  obtain ⟨obj, roots⟩ := s
  simp only [Tree.at]
  congr 1
  · funext x
    cases ho : obj x with
    | none => rfl
    | some o =>
      cases o with
      | key n => simp [Obj.at, prefixAt_of_le (hk x n ho)]
      | val v => rfl
  · rw [List.filter_eq_self]
    intro r hr'
    simpa using hr r hr'

/-- The tree before at i - 1: its times are before i (`SOk`), and so are its
space roots' times. -/
theorem sok_at {i : Time} {s : Tree} (hs : SOk cf i s) (hr : ∀ r ∈ s.roots, r.1 < i) :
    s.at (i - 1) = s :=
  tree_at_self (fun x n hn u hu => Nat.le_sub_one_of_lt ((hs x n hn).2.2 u hu))
    (fun r hr' => Nat.le_sub_one_of_lt (hr r hr'))

/-! ## The contract's clauses 1 and 2 -/

theorem kidsOk_of {s : Tree} {n : KNode} {lo : Nat} {hi : Option Nat}
    {sub : NodeId → Nat → Option Nat → Bool} : ∀ (l : List (Nat × NodeId)),
    (∀ pre c y post, l = pre ++ (c, y) :: post → kidOk s n lo hi sub c y post = true) →
    kidsOk s n lo hi sub l = true
  | [], _ => rfl
  | (c, y) :: rest, h => by
    simp only [kidsOk, Bool.and_eq_true]
    exact ⟨h [] c y rest rfl, kidsOk_of rest (fun pre c' y' post hp =>
      h ((c, y) :: pre) c' y' post (by rw [hp]; rfl))⟩

theorem isEmpty_false {α : Type} {l : List α} (h : l ≠ []) : l.isEmpty = false := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- **A sound tree passes the walk** (the converse of `walk_good`): a sound
node, with fuel at least its own, every key node of whose walk meets the
rules of one node. -/
theorem walk_of_good {p : Params} {T : Tree} : ∀ (f : Nat) (x : NodeId) (lo : Nat) (hi : Option Nat),
    Good T x lo hi → T.fuel x ≤ f →
    (∀ z ∈ reachAt T f x, ∀ n, T.obj z = some (.key n) → nodeOk p T n = true) →
    walk p T f x lo hi = true
  | 0, x, lo, hi, hg, hf, _ => by
    obtain ⟨n, hn⟩ := good_obj hg
    simp [Tree.fuel, hn] at hf
  | f + 1, x, lo, hi, hg, hf, hok => by
    obtain ⟨n, hobj⟩ := good_obj hg
    have hfx : T.fuel x = n.level + 1 := by simp [Tree.fuel, hobj]
    have hok' : ∀ c w, (c, w) ∈ live n.ks →
        ∀ z ∈ reachAt T f w, ∀ m, T.obj z = some (.key m) → nodeOk p T m = true := by
      intro c w hm z hz
      apply hok z
      rw [reachAt_key hobj, List.mem_cons, List.mem_flatMap]
      exact Or.inr ⟨(c, w), hm, hz⟩
    unfold walk
    rw [hobj]
    simp only [Bool.and_eq_true]
    refine ⟨hok x (mem_reachAt_self' _ _ _) n hobj, ?_⟩
    apply kidsOk_of
    intro pre c w post he
    have hm : (c, w) ∈ live n.ks := by rw [he]; simp
    cases hg with
    | mk _ _ _ n' hobj' hwf hhi hlo hval hkey hseg hkid =>
      rw [hobj] at hobj'
      obtain rfl : n = n' := by injection hobj' with h1; injection h1
      unfold kidOk
      rw [hhi c w hm, Bool.true_and]
      cases hl : n.leaf with
      | true =>
        cases hlong : isLong c with
        | true =>
          obtain ⟨m, hm1, hm2, hm3⟩ := hkey c w hm (fun _ => hlong)
          have hgw := hseg hl c w hm hlong
          have hfw : T.fuel w = m.level + 1 := by simp [Tree.fuel, hm1]
          have := walk_of_good f w 0 none hgw (by omega) (hok' c w hm)
          simp [hlo hl c w hm, hm1, hm2, isEmpty_false hm3, this]
        | false =>
          obtain ⟨v, hv⟩ := hval hl c w hm hlong
          simp [hlo hl c w hm, hv]
      | false =>
        obtain ⟨m, hm1, hm2, hm3⟩ := hkey c w hm (by simp [hl])
        have hgw := hkid hl pre c w post he
        have hfw : T.fuel w = m.level + 1 := by simp [Tree.fuel, hm1]
        have := walk_of_good f w _ _ hgw (by omega) (hok' c w hm)
        simp [hm1, hm2, isEmpty_false hm3, this]

/-- **Clause 1 from a sound root** (7): a tree whose space root is sound with
the range [0, none), every key node it reaches meeting the rules of one node,
and whose root has a live klong or is a segment leaf, meets the invariants. -/
theorem invOk_of_good {p : Params} {T : Tree} {r : NodeId} (hr : T.root = some r)
    (hg : Good T r 0 none)
    (hok : ∀ z ∈ reach T, ∀ n, T.obj z = some (.key n) → nodeOk p T n = true)
    (hne : ∀ n, T.obj r = some (.key n) → n.leaf = true ∨ live n.ks ≠ []) :
    invOk p T = true := by
  obtain ⟨n, hobj⟩ := good_obj hg
  have hreach : reach T = reachAt T (n.level + 1) r := by simp [reach, hr, Tree.fuel, hobj]
  unfold invOk
  rw [hr]
  simp only [hobj, Bool.and_eq_true]
  refine ⟨?_, walk_of_good _ r 0 none hg (by simp [Tree.fuel, hobj]) (hreach ▸ hok)⟩
  rcases hne n hobj with h | h
  · simp [h]
  · simp [isEmpty_false h]

/-- **Clause 2's left side** (7): the contents of a tree are what its space root
holds. -/
theorem contents_eq {T : Tree} {r : NodeId} (hr : T.root = some r) : contents T = L T r := by
  simp [contents, hr, L]

/-- **The contract's clauses 1 and 2 from a sound root** (7). -/
theorem clauses_of_good {T : Tree} {r : NodeId} (hr : T.root = some r) (hg : Good T r 0 none)
    (hok : ∀ z ∈ reach T, ∀ n, T.obj z = some (.key n) → nodeOk cf.params T n = true)
    (hne : ∀ n, T.obj r = some (.key n) → n.leaf = true ∨ live n.ks ≠ []) :
    invOk cf.params T = true ∧ contents T = L T r :=
  ⟨invOk_of_good hr hg hok hne, contents_eq hr⟩

/-- `clauses_of_good` with every key node of T meeting the rules of one node. -/
theorem clauses_of_good' {T : Tree} {r : NodeId} (hr : T.root = some r) (hg : Good T r 0 none)
    (hok : ∀ z n, T.obj z = some (.key n) → nodeOk cf.params T n = true)
    (hne : ∀ n, T.obj r = some (.key n) → n.leaf = true ∨ live n.ks ≠ []) :
    invOk cf.params T = true ∧ contents T = L T r :=
  clauses_of_good hr hg (fun z _ n hn => hok z n hn) hne

/-! ## Putting the segments together -/

/-- The level bounds of a node that holds an abstract node. -/
theorem Holds.bounds {T : Tree} {g : Nat} : ∀ {h : Nat} {x : NodeId} {A : Node h},
    Holds cf T g h x A →
      ∃ n, T.obj x = some (.key n) ∧ n.level = cf.lev g h ∧ g ≤ cf.G ∧ h ≤ cf.H
  | 0, _, _, hx => by
    cases hx with
    | leaf hobj _ hlev hG _ _ => exact ⟨_, hobj, hlev, hG, Nat.zero_le _⟩
  | _ + 1, _, _, hx => by
    cases hx with
    | inner hobj _ hlev hG hH _ _ _ => exact ⟨_, hobj, hlev, hG, hH⟩

theorem htOf_lev (cf : Cfg) {g h : Nat} (hh : h ≤ cf.H) : cf.htOf (cf.lev g h) = h := by
  simp only [Cfg.htOf, Cfg.lev]
  rw [show 1 + (cf.G - g) * (cf.H + 1) + h - 1 = h + (cf.H + 1) * (cf.G - g) by
    rw [Nat.mul_comm]; omega]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- The height a node that holds an abstract node of height h has by its level. -/
theorem htIn_of_holds {T : Tree} {g h : Nat} {x : NodeId} {A : Node h} (hx : Holds cf T g h x A) :
    htIn cf T x = h := by
  obtain ⟨n, hobj, hlev, _, hH⟩ := hx.bounds
  simp only [htIn, hobj, hlev]
  exact htOf_lev cf hH

theorem htIn_transfer {s T : Tree} {y : NodeId} (hy : T.obj y = s.obj y) :
    htIn cf T y = htIn cf s y := by
  simp [htIn, hy]

/-- A value as a short payload. -/
theorem payGood_val {T : Tree} {g c : Nat} {y : NodeId} {v : Nat} (hl : isLong c = false)
    (hy : T.obj y = some (.val v)) : PayGood cf T g c y :=
  ⟨fun _ => ⟨v, hy⟩, fun h => by rw [hl] at h; cases h⟩

/-- **A next segment's root as a long payload**: a node of segment g + 1 that
holds an abstract node in order with the range [0, none), whose payloads are
sound, is a sound payload of segment g. -/
theorem payGood_of_holds {T : Tree} {g c h' : Nat} {y : NodeId} {A' : Node h'}
    (hl : isLong c = true) (hx : Holds cf T (g + 1) h' y A') (hw : WF h' 0 none A')
    (hp : ∀ p ∈ content h' A', PayGood cf T (g + 1) p.1 p.2) : PayGood cf T g c y := by
  obtain ⟨m, hobj, hlev, hG, hH⟩ := hx.bounds
  obtain ⟨m', hobj', _, hne⟩ := hx.live_ne (WF_ne_nil h' _ _ A' hw)
  rw [hobj] at hobj'
  obtain rfl : m = m' := by injection hobj' with h1; injection h1
  refine ⟨fun hs => ?_, fun _ => ⟨m, hobj, ?_, hne, good_of_holds h' hx hw hp⟩⟩
  · rw [hl] at hs; cases hs
  · have := lev_next cf hG hH
    omega

/-- **A next segment's root as a long payload, shaped**. -/
theorem shaped_pay_of_holds {T : Tree} {g h' : Nat} {y : NodeId} {A' : Node h'} {lo : Nat}
    {hi : Option Nat} (hx : Holds cf T (g + 1) h' y A') (hw : WF h' lo hi A')
    (hp : ∀ p ∈ content h' A', isLong p.1 = true → Shaped cf T (g + 2) (htIn cf T p.2) p.2) :
    Shaped cf T (g + 1) (htIn cf T y) y := by
  rw [htIn_of_holds hx]
  exact shaped_of_holds h' hx hw hp

/-- The key nodes reached from x meet the rules of one node. -/
def NOk (p : Params) (T : Tree) (x : NodeId) : Prop :=
  ∀ z ∈ R T x, ∀ n, T.obj z = some (.key n) → nodeOk p T n = true

/-- What a sound node reaches: itself, and what its children reach. -/
theorem R_good_kids {T : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat} (hg : Good T x lo hi)
    {n : KNode} (hobj : T.obj x = some (.key n)) {z : NodeId} (hz : z ∈ R T x) :
    z = x ∨ ∃ c y, (c, y) ∈ live n.ks ∧ z ∈ R T y := by
  have hR : R T x = reachAt T (n.level + 1) x := by simp [R, Tree.fuel, hobj]
  rw [hR, reachAt_key hobj, List.mem_cons, List.mem_flatMap] at hz
  rcases hz with rfl | ⟨⟨c, y⟩, hm, hz⟩
  · exact Or.inl rfl
  · right
    refine ⟨c, y, hm, ?_⟩
    rcases good_kids hg hobj c y hm with ⟨m, hm1, hm2, lo', hi', hgy⟩ | ⟨v, hv⟩
    · have := reach_stable n.level hgy (by simp [Tree.fuel, hm1]; omega)
      rw [this] at hz
      exact hz
    · rw [reachAt_val hv] at hz
      show z ∈ reachAt T (T.fuel y) y
      rw [reachAt_val hv]
      exact hz

/-- **The rules of one node through the tree after**: a node that holds an
abstract node in order, whose payloads are sound, and whose long payloads'
reached key nodes meet the rules of one node, has all its reached key nodes
meeting them. -/
theorem nok_of_holds {p : Params} (hp0 : p = cf.params) : ∀ (h : Nat) {T : Tree} {g : Nat}
    {x : NodeId} {A : Node h} {lo : Nat} {hi : Option Nat}, Holds cf T g h x A → WF h lo hi A →
      (∀ q ∈ content h A, PayGood cf T g q.1 q.2 ∧ (isLong q.1 = true → NOk p T q.2)) → NOk p T x
  | 0, T, g, x, A, lo, hi, hx, hw, hq => by
    have hg := good_of_holds 0 hx hw (fun q hq' => (hq q hq').1)
    cases hx with
    | @leaf _ n _ hobj _ _ _ hok hlive =>
      intro z hz m hm
      rcases R_good_kids hg hobj hz with rfl | ⟨c, y, hcy, hz⟩
      · rw [hobj] at hm
        obtain rfl : n = m := by injection hm with h1; injection h1
        subst hp0; exact hok
      · rw [hlive] at hcy
        cases hl : isLong c with
        | true => exact (hq _ hcy).2 hl z hz m hm
        | false =>
          obtain ⟨v, hv⟩ := (hq _ hcy).1.1 hl
          have : z ∈ R T y := hz
          simp only [R, Tree.fuel, hv, reachAt, List.mem_singleton] at this
          subst this
          rw [hv] at hm; cases hm
  | h + 1, T, g, x, A, lo, hi, hx, hw, hq => by
    have hg := good_of_holds (h + 1) hx hw (fun q hq' => (hq q hq').1)
    cases hx with
    | @inner _ _ n _ hobj _ _ _ _ hok hcv hkids =>
      have hE := holdsE_of hcv hkids
      intro z hz m hm
      rcases R_good_kids hg hobj hz with rfl | ⟨c, y, hcy, hz⟩
      · rw [hobj] at hm
        obtain rfl : n = m := by injection hm with h1; injection h1
        subst hp0; exact hok
      · obtain ⟨a, ha, hea⟩ := forall₂_exists hE (c, y) hcy
        obtain ⟨lo', hi', hwa⟩ := kidsWF_each hw.2.2.2 a ha
        exact nok_of_holds hp0 h hea.2 hwa (fun q hq' => hq q (mem_content_succ ha hq')) z hz m hm

/-- **The rules of one node through an unchanged subtree**: if every key node
of s meets them in s, T has every node of s, and T has every node y reaches
as s has it, y's reached key nodes meet them in T. -/
theorem nok_transfer {p : Params} {s T : Tree} {y : NodeId}
    (hs : ∀ x n, s.obj x = some (.key n) → nodeOk p s n = true)
    (hex : ∀ z, s.obj z ≠ none → T.obj z ≠ none) (hag : ∀ z ∈ R s y, T.obj z = s.obj z) :
    NOk p T y := by
  intro z hz n hn
  have hy : T.obj y = s.obj y := hag y (mem_R_self s y)
  have hf : T.fuel y = s.fuel y := by simp [Tree.fuel, hy]
  have hRe : R T y = R s y := by
    unfold R
    rw [hf]
    exact reachAt_agree _ y hag
  rw [hRe] at hz
  rw [hag z hz] at hn
  exact nodeOk_transfer (hs z n hn) hex

/-- **The contract's clauses 1 and 2 from what the root holds**: a tree whose
space root r holds the abstract node A of segment 0 at height h, in order with
the range [0, none) or empty (then a leaf), whose payloads are sound and whose
reached key nodes meet the rules of one node, meets the invariants, and its
contents are A's payloads' keys in order. -/
theorem clauses_of_holds {T : Tree} {r : NodeId} {h : Nat} {A : Node h} (hr : T.root = some r)
    (hx : Holds cf T 0 h r A) (hw : WFE h 0 none A) (h0 : h = 0 ∨ A ≠ [])
    (hp : ∀ q ∈ content h A, PayGood cf T 0 q.1 q.2)
    (hok : ∀ z ∈ reach T, ∀ n, T.obj z = some (.key n) → nodeOk cf.params T n = true) :
    invOk cf.params T = true ∧
      contents T = (content h A).flatMap (fun q => klongList T true (L T) q.1 q.2) := by
  have hg := good_of_holds_wfe hx hw hp
  refine ⟨invOk_of_good hr hg hok (fun n hn => ?_), by rw [contents_eq hr, L_of_holds_wfe hx hw hp]⟩
  rcases h0 with rfl | hne
  · left
    cases hx with
    | leaf hobj hleaf _ _ _ _ =>
      rw [hobj] at hn
      obtain rfl : _ = n := by injection hn with h1; injection h1
      exact hleaf
  · right
    obtain ⟨m, hm, _, hl⟩ := hx.live_ne hne
    rw [hm] at hn
    obtain rfl : m = n := by injection hn with h1; injection h1
    exact hl

theorem reach_eq_R {T : Tree} {r : NodeId} (hr : T.root = some r) : reach T = R T r := by
  simp [reach, hr, R]

/-- The tree before: a tree that meets the invariants has a sound space root
(`walk_good`). -/
theorem good_of_invOk {p : Params} {s : Tree} {r : NodeId} (hr : s.root = some r)
    (hinv : invOk p s = true) : Good s r 0 none := by
  unfold invOk at hinv
  rw [hr] at hinv
  simp only at hinv
  cases ho : s.obj r with
  | none => rw [ho] at hinv; cases hinv
  | some o =>
    cases o with
    | val v => rw [ho] at hinv; cases hinv
    | key n =>
      rw [ho] at hinv
      simp only [Bool.and_eq_true] at hinv
      exact walk_good _ r 0 none hinv.2

/-- **The contents of the tree before, by its view**: the contents of a tree
whose sound space root is shaped as PE's trees at segment 0 are its view's
payloads' keys in order. -/
theorem contents_view {s : Tree} {r : NodeId} {h : Nat} (hr : s.root = some r)
    (hg : Good s r 0 none) (hsh : Shaped cf s 0 h r) :
    contents s = (content h (view h s r)).flatMap (fun q => klongList s true (L s) q.1 q.2) := by
  rw [contents_eq hr, view_L_pays h hg hsh]

end Contract.PE
