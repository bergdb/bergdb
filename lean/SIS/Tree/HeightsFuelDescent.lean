/-
Step 4 (C), part 1 (bergdb 024-22; 024-12's (4)): a descent's fuel bounds the
height it starts from. With the heights' walk, a key node of height h has a
segment tree of depth h (`segDepthEq_of_hasHt`), and the writer's descent
through it succeeds only with fuel above h (`writerWP_descendLte_depth`). So a
descent that succeeds from a node of height h has h below the fuel
(`ht_descendLte_height`): no operation reaches below a node of height fuel or
more, the first step of the doomed transaction.
-/
import SIS.Tree.HeightsFuel
import SIS.Tree.SegBalance
import SIS.Tree.WriterHeightsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

section C1

variable {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop}

/-- The nodes a descent visits from an untaken node are untaken: an overlay
node's live children are (`NodeHt`), a base node's are ids of the view. -/
theorem ht_eqVisits_free (base : View BVal) (w : W) (hb : Book B c w) (hi : HtInv H B c w)
    (hvo : ViewHtOK H B c) (hbase : BaseHeights c H base) (cv : Nat) :
    ∀ (f : Nat) (x : NodeId), w.taken.contains x = false →
      ∀ q ∈ eqVisits (wNode c.p base w) c.i cv f x, w.taken.contains q.1 = false := by
  intro f
  induction f with
  | zero => intro x _ q hq; simp [eqVisits] at hq
  | succ f ih =>
    intro x hx q hq
    simp only [eqVisits, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact hx
    · split at hq
      · simp at hq
      · rename_i n hn
        split at hq
        · simp at hq
        · rename_i hleaf
          split at hq
          · simp at hq
          · rename_i fd hfd
            have hm := KNode.searchLte_mem n c.i cv fd hfd
            have hyf : w.taken.contains fd.y = false := by
              obtain ⟨_, hl | ⟨_, hk⟩⟩ := ht_wNode_cases hn
              · obtain ⟨g, h, hgh⟩ := kd_tag_of_lookup hb hl
                have hN := hi.cache x n g h (bk_mem_of_lookup _ _ _ hl) hgh hx
                rw [KNode.liveAt_of_times n c.i hN.3] at hm
                exact (hN.1 fd.c fd.y hm).1
              · obtain ⟨h, _, hlf, htm, hlive⟩ := hbase x n hk
                have h0 : h ≠ 0 := by
                  intro h0; subst h0; simp at hlf; rw [hlf] at hleaf; exact hleaf rfl
                rw [KNode.liveAt_of_times n c.i htm] at hm
                have hy := hvo.heights.old _ _ (hlive h0 fd.c fd.y hm)
                cases ht : w.taken.contains fd.y with
                | false => rfl
                | true => have := hi.takenAbove _ ht; omega
            exact ih fd.y hyf q hq

/-- A descent that succeeds from an untaken key node of height h had fuel
above h. -/
theorem ht_descendLte_height (base : View BVal) (hvc : ViewCoherent c base) (w : W)
    (hb : Book B c w) (hi : HtInv H B c w) (hvo : ViewHtOK H B c)
    (hbase : BaseHeights c H base) (x : NodeId) (h : Nat) (hx : HasHt H w x h)
    (hxf : w.taken.contains x = false) (cv f : Nat) :
    WriterWP (descendLte cv f x) c w (fun _ _ => h < f) :=
  writerWP_descendLte_depth cv c base hvc f h x w
    (segDepthEq_of_hasHt hb hi.cache hvo.heights base hbase h x hx)
    (ht_eqVisits_free base w hb hi hvo hbase cv f x hxf)

end C1

end SIS.Tree
