/-
bergdb 030-37: the virtual fill conditions imply fill of emit's final
abstract nodes and every cut part. A root's own size is explicit here;
root settling and the next-segment payloads remain separate obligations.
-/
import Contract.Proof.DnbFillAbstract

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

theorem VFill.node_decision {g g' h h' : Nat} {root : Bool} {base : Option NodeId}
    {j : Bool} {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {d : Dec}
    (hv : VFill cf i s g root h (.node base g' h' j es F d)) :
    d = decideNode cf i (base.bind (getKey s)) j F := by
  cases hv <;> assumption

theorem vfill_children_full {b G H g h : Nat} (hb : 8 ≤ b) {es : List (Nat × VN)}
    (hv : ∀ e ∈ es, VFill (Cfg.java b G H) i s g false h e.2)
    (he : es.length < 2 ∨ findSmall (Cfg.java b G H) es = none)
    (hlen : 2 ≤ (entries es).length) : ∀ e ∈ es, (Cfg.java b G H).m ≤ cntOf s e.2 := by
  intro e hem
  have hm2 := (java_params (G := G) (H := H) hb).1
  by_contra hn
  have hs := (hv e hem).small hm2 |>.mpr (show cntOf s e.2 < (Cfg.java b G H).m from by omega)
  rcases he with he | he
  · have hpos := List.length_pos_of_mem hem
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show es.length = 1 by omega)
    subst ha
    have hea : e = a := List.mem_singleton.mp hem
    subst hea
    have hsmall := (hv e List.mem_cons_self).small_ents hb hs (cv := e.1)
    simp only [entries, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hlen
    omega
  · simp only [smallLeaf, Bool.and_eq_true, decide_eq_true_eq] at hs
    have hh := findSmall_none he e hem hs.1
    omega

theorem nodeFill_cutEnts {h : Nat} {root : Bool} {Ps : List (Node h)}
    (hf : ∀ Q ∈ Ps, NodeFill cf h root Q) (inner : Bool) (cv : Nat) :
    ∀ p ∈ cutEnts inner cv Ps, NodeFill cf h root p.2 := by
  cases Ps with
  | nil => simp [cutEnts]
  | cons Q Qs =>
    intro p hp
    simp only [cutEnts, List.mem_cons, List.mem_map] at hp
    rcases hp with rfl | ⟨P, hP, rfl⟩
    · exact hf Q List.mem_cons_self
    · have hh := hf P (List.mem_cons_of_mem _ hP)
      split
      · exact hh.renameHead
      · exact hh

def FinalFill (cf : Cfg) (i : Time) (s : Tree) (h : Nat) : Prop :=
  ∀ (g : Nat) (root : Bool) (v : VN), VFill cf i s g root h v → VOk cf s g h v →
    OwnFill cf root h (cntOf s v) → NodeFill cf h root (fin s h v)

def PiecesFill (cf : Cfg) (i : Time) (s : Tree) (h : Nat) : Prop :=
  ∀ (g cv : Nat) (v : VN), VFill cf i s g false h v → VOk cf s g h v → cf.m ≤ cntOf s v →
    ∀ p ∈ finEnts cv v (fin s h v), NodeFill cf h false p.2

theorem vfill_final_pieces {b G H : Nat} (hb : 8 ≤ b) :
    ∀ h, FinalFill (Cfg.java b G H) i s h ∧ PiecesFill (Cfg.java b G H) i s h := by
  have hm2 := (java_params (G := G) (H := H) hb).1
  intro ht
  induction ht using Nat.strong_induction_on with
  | _ ht IH =>
    have hfinal : FinalFill (Cfg.java b G H) i s ht := by
      intro g root v hv hok hown
      cases ht with
      | zero =>
        cases hv with
        | old hs hf =>
          rw [fin_old']
          exact nodeFill_view hm2 0 hs hf
        | @leaf root base j es F d hp hF hd hfull =>
          change OwnFill (Cfg.java b G H) root 0 (fin s 0 _).length
          rw [fin_length hok]
          exact hown
      | succ h =>
        cases hv with
        | old hs hf =>
          rw [fin_old']
          exact nodeFill_view hm2 (h + 1) hs hf
        | @inner root h base j es F d hc hn he hF hd hfull =>
          have hfinlen := fin_length hok
          have hF2 : 2 ≤ F.length := by
            cases root
            · have hm := hown.2 rfl; change (Cfg.java b G H).m ≤ F.length at hm; omega
            · exact hown.1 rfl (by omega)
          have hlen : 2 ≤ (entries es).length := by rw [hF, renameHead_length] at hF2; exact hF2
          have hfull := vfill_children_full hb hc he hlen
          have hkc : ∀ e ∈ es, VOk (Cfg.java b G H) s g h e.2 := by
            cases hok with
            | inner hh _ _ _ _ => exact hh
          change OwnFill (Cfg.java b G H) root (h + 1) (fin s (h + 1) _).length ∧
            ∀ p ∈ renameHead 0 (es.flatMap (fun e => finEnts e.1 e.2 (fin s h e.2))),
              NodeFill (Cfg.java b G H) h false p.2
          refine ⟨by rw [hfinlen]; exact hown, ?_⟩
          intro p hp
          obtain ⟨p', hp', h2⟩ := renameHead_mem hp
          rw [← h2]
          obtain ⟨e, hem, hp⟩ := List.mem_flatMap.mp hp'
          exact (IH h (by omega)).2 g e.1 e.2 (hc e hem) (hkc e hem) (hfull e hem) p' hp
    refine ⟨hfinal, ?_⟩
    intro g cv v hv hok hmin p hp
    have hnf := hfinal g false v hv hok (by simpa [OwnFill] using hmin)
    cases v with
    | old y =>
      simp only [finEnts, List.mem_singleton] at hp
      subst hp
      exact hnf
    | node base g' h' j es F d =>
      have hd := hv.node_decision
      cases d with
      | same =>
        simp only [finEnts, List.mem_singleton] at hp
        subst hp
        exact hnf
      | append =>
        simp only [finEnts, List.mem_singleton] at hp
        subst hp
        exact hnf
      | parts k =>
        by_cases hk : 2 ≤ k
        · rw [finEnts_cut cv hk] at hp
          have hflen := fin_length hok
          have hsmall : (Cfg.java b G H).m ≤ F.length := hmin
          have hsz := java_dec_parts_minFill hb hsmall hd.symm j
          have hsum : (partSizes (fin s ht (.node base g' h' j es F (.parts k))).length k j).sum =
              (fin s ht (.node base g' h' j es F (.parts k))).length := partSizes_sum (by omega) j
          apply nodeFill_cutEnts (inner := ht != 0) (cv := cv) ?_ p hp
          intro Q hQ
          have hQmin := cutList_min_length (le_of_eq hsum) (by simpa only [hflen] using hsz) Q hQ
          exact nodeFill_cut_piece (cutList_sublist _ _ Q hQ) hnf hQmin
        · simp only [finEnts, hk, ↓reduceIte, List.mem_singleton] at hp
          subst hp
          exact hnf

end Contract.PE
