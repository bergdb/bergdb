/-
bergdb 030-37: transfer fill on an unchanged old walk, and the fill
premises of the long payloads of one old segment.
-/
import Contract.Proof.DnbFillRoot

namespace Contract.PE

open DNB PeProof PeProof.Abs

variable {cf : Cfg} {s T : Tree}

theorem good_key_child {x c y : Nat} {lo : Nat} {hi : Option Nat} {n : KNode}
    (hg : Good s x lo hi) (ho : s.obj x = some (.key n)) (hm : (c, y) ∈ live n.ks)
    (hkey : n.leaf = true → isLong c = true) : ∃ lo' hi', Good s y lo' hi' := by
  obtain ⟨m, hmo, _, _⟩ := (good_key hg ho).2 c y hm hkey
  rcases good_kids hg ho c y hm with ⟨m', hmo', _, lo', hi', hg'⟩ | ⟨v, hv⟩
  · exact ⟨lo', hi', hg'⟩
  · rw [hmo] at hv; cases hv

theorem Filled.transfer {x : Nat} {root : Bool} {lo : Nat} {hi : Option Nat}
    (hf : Filled cf s root x) (hg : Good s x lo hi)
    (hag : ∀ z ∈ R s x, T.obj z = s.obj z) : Filled cf T root x := by
  induction hf generalizing T lo hi with
  | @key root x n ho hR hF hlong hinner ihlong ihinner =>
    have hsub : ∀ c y, (c, y) ∈ live n.ks → ∀ z ∈ R s y, T.obj z = s.obj z :=
      fun c y hm z hz => hag z (R_child ho hm (good_child_fuel hg ho hm) z hz)
    have hTx : T.obj x = some (.key n) := by rw [hag x (mem_R_self s x), ho]
    refine Filled.key hTx hR hF ?_ ?_
    · intro c y hm hl hc
      obtain ⟨lo', hi', hgood⟩ := good_key_child hg ho hm (fun _ => hc)
      exact ihlong c y hm hl hc hgood (hsub c y hm)
    · intro c y hm hl
      obtain ⟨lo', hi', hgood⟩ := good_key_child hg ho hm (fun he => by rw [hl] at he; cases he)
      exact ihinner c y hm hl hgood (hsub c y hm)
  | other hn =>
    obtain ⟨n, ho⟩ := good_obj hg
    exact False.elim (hn n ho)

theorem filled_view_payloads : ∀ (h : Nat) {g x : Nat} {root : Bool},
    Shaped cf s g h x → Filled cf s root x →
    ∀ p ∈ content h (view h s x), isLong p.1 = true → Filled cf s true p.2
  | 0, g, x, root, hs, hf, p, hp, hl => by
    obtain ⟨n, ho, _, _, hleaf, _, _⟩ := shaped_getKey hs
    have hp' : p ∈ live n.ks := by simpa only [content, view, ho] using hp
    exact (filled_key hf ho).2.2.1 p.1 p.2 hp' (by simpa using hleaf) hl
  | h + 1, g, x, root, hs, hf, p, hp, hl => by
    obtain ⟨n, ho, _, _, hleaf, _, _⟩ := shaped_getKey hs
    have hnleaf : n.leaf = false := by simpa using hleaf
    have hkids := (shaped_inner hs ho).2
    simp only [content, view, ho, kids, ofKids, List.flatMap_map] at hp
    obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
    exact filled_view_payloads h (hkids q.1 q.2 hq)
      ((filled_key hf ho).2.2.2 q.1 q.2 hq hnleaf) p hp hl

end Contract.PE
