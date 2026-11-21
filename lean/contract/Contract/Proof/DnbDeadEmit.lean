/-
bergdb 030-37: every key node emitted by a successful plan meets DeadOK.
New nodes have no dead klongs; appends use the decision's checked count.
-/
import Contract.Proof.DnbDeadBasics

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {i : Time} {s : Tree}

def WritesDeadSafe (cf : Cfg) (W : List (NodeId × Obj)) : Prop :=
  ∀ p ∈ W, ∀ n, p.2 = .key n → DeadSafe cf n.ks

theorem wform_fresh_dead {p : NodeId × Obj} {n : KNode}
    (hf : WForm i s p) (hn : s.obj p.1 = none) (hp : p.2 = .key n) : DeadSafe cf n.ks := by
  rcases hf with ⟨_, hv | ⟨l, b, F, he, hlive⟩⟩ | ⟨n0, F, hobj, _⟩
  · obtain ⟨v, hv⟩ := hv
    rw [hp] at hv; cases hv
  · rw [hp] at he
    have heq : n = ⟨l, b, newKs i F⟩ := Obj.key.inj he
    subst n
    right
    have hsort : F.Pairwise CvLtA := by rw [← hlive]; exact live_sorted _
    rw [deadCount_newKs hsort]
    exact Nat.zero_le _
  · rw [hn] at hobj; cases hobj

theorem node_emit_dead (hcf : cf.Ok) (hs : SOk cf i s) {g h : Nat} {b : Option NodeId}
    {join : Bool} {es : List (Nat × VN)} {F : List (Nat × Option NodeId)} {dec : Dec}
    {U : List NodeId} {acc acc1 acc' : Acc} {W0 : List (NodeId × Obj)} {F' E : List (Nat × NodeId)}
    (hn : NH cf i s g h b join es F dec U acc)
    (hc : CRes cf i s g h (.node b g h join es F dec) U acc acc1 W0 F' F)
    (hsafe : WritesDeadSafe cf acc1.ws)
    (he : emitAfter cf i s g h join dec b F' acc1 = some (E, acc')) :
    WritesDeadSafe cf acc'.ws := by
  cases dec with
  | same =>
    cases b with
    | none => simp [emitAfter] at he
    | some x =>
      simp only [emitAfter, Option.some.injEq, Prod.mk.injEq] at he
      exact he.2 ▸ hsafe
  | append =>
    cases b with
    | none => simp [emitAfter] at he
    | some x =>
      cases hgk : getKey s x with
      | none => simp [emitAfter, hgk] at he
      | some n =>
        simp only [emitAfter, hgk, Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        intro p hp n' hpn
        rcases List.mem_cons.mp hp with rfl | hp
        · have hd : Dec.append = decideNode cf i (some n) join F := by
            cases hn.e with
            | node hd _ _ _ => simpa only [Option.bind_some, hgk] using hd
          have hn' : n' = {n with ks := n.ks ++ emitKs i n.ks F'} := (Obj.key.inj hpn).symm
          subst n'
          have hlive : ∀ c y, (c, y) ∈ live n.ks → s.obj y ≠ none := by
            intro c y hy
            exact (nodeOk_iff.mp (hs x n (getKey_obj hgk)).1).2.2 c y (live_mem_key' hy)
          have hdead := dec_append_dead hd.symm
          unfold DeadSafe at hdead ⊢
          rw [emitKs_dead_eq hc.m hlive]
          exact hdead
        · exact hsafe p hp n' hpn
  | parts k =>
    have hspec := step_parts hcf hn hc
    obtain ⟨W, hW, _, _, _, _⟩ := hspec
    simp only [emitAfter, Option.some.injEq] at he
    have hacc' : acc' = (newParts cf i g h (cutList F' (partSizes F'.length k join)) acc1).2 := by
      exact (congrArg Prod.snd he).symm
    rw [hacc']
    obtain ⟨_, hw, _⟩ := newParts_eq (cf := cf) (i := i) (g := g) (h := h)
      (cutList F' (partSizes F'.length k join)) acc1
    intro p hp n hpn
    by_cases hp1 : p ∈ acc1.ws
    · exact hsafe p hp1 n hpn
    · have hpm : p ∈ npW cf i g h acc1.next (cutList F' (partSizes F'.length k join)) := by
        rw [hw, List.mem_append, List.mem_reverse] at hp
        exact hp.resolve_right hp1
      have hpW : p ∈ W := by
        rw [hW.ws, List.mem_append] at hp
        refine hp.resolve_right ?_
        intro hm
        exact hp1 (by rw [hc.w.ws]; exact List.mem_append_right _ hm)
      have hfresh : s.obj p.1 = none := hn.fresh p.1 (by
        have hlo := (mem_npW hpm).1
        have hnext := hc.w.next
        nomega)
      exact wform_fresh_dead (hW.form p hpW) hfresh hpn

end Contract.PE
