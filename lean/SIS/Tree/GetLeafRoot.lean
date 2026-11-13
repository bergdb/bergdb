import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Every put of a key of one segment when the space root is a leaf (bergdb
024-12, TP10; `OpGetOK`'s rules together): with room, or by a time split or a
space split, in place for a root the transaction made, the reading changes by
the put alone (`writerWP_put_leafRoot`). The premises are those of the five
rules, in one form: the ids below the next one, the root not taken back, the
reachable nodes' klongs well formed, their klongs naming ids below the next one
and not the root, and the uniqueness of the key's search at the root. -/

theorem writerWP_put_leafRoot (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (cv h : Nat) (w : W) (n : KNode) (hsa : 1 ≤ c.p.splitAbove) (hkey : keyWf [cv] = true)
    (hroot : wNode c.p base w w.top.rootKey = some n) (hnl : n.leaf = true)
    (hrt : w.taken.contains w.top.rootKey = false)
    (hnwf : klongsWf n.ks = true) (htimes : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next) ∧
      (∀ q ∈ w.vals, q.1 < w.next) ∧ w.top.rootKey < w.next)
    (hbase : knodeOf c.p base w.next = none)
    (huniq : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → key' = [cv])
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hlinks : ∀ x xn cc z, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → (cc, z) ∈ xn.liveAt c.i →
        z < w.next ∧ z ≠ w.top.rootKey) :
    WriterWP (putKv (.put [cv] h)) c w (fun _ w' => ∀ key', keyWf key' = true →
      wGet c.p c.i base w' key' =
        if Op.key (.put [cv] h) == key' then Op.value (.put [cv] h)
        else wGet c.p c.i base w key') := by
  obtain ⟨hidn, hidv, hidt, hidvals, hidr⟩ := hids
  have hfuel : 2 ≤ c.p.fuel := by unfold Params.fuel; omega
  -- the key's descent at the root: the root alone
  have hev : eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey = [(w.top.rootKey, cv)] := by
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    rw [hf2]
    simp [eqVisits, hroot, hnl]
  have hleafAt : ∀ L n', (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w L = some n' → L = w.top.rootKey ∧ n' = n := by
    intro L n' hL hn'
    rw [hev] at hL
    have hL' : L = w.top.rootKey := by simpa using hL
    subst hL'
    rw [hroot] at hn'
    exact ⟨rfl, (Option.some.inj hn').symm⟩
  have ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel ([] ++ [cv]) w.top.rootKey,
      w.taken.contains q.1 = false := by
    intro q hq
    simp only [List.nil_append, fromVisits] at hq
    rw [hev] at hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact hrt
  have hnext : w.taken.contains w.next = false ∧ w.vals.lookup w.next = none := by
    refine ⟨?_, ?_⟩
    · cases h' : w.taken.contains w.next with
      | false => rfl
      | true => have := hidt _ h'; omega
    · apply List.lookup_eq_none_iff.mpr
      intro q' hq'
      have := hidvals q' hq'
      simp only [bne_iff_ne, ne_eq]
      omega
  have hfresh : ∀ key' x c' n' y,
      (x, c') ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → (n'.searchEq c.i c').map (·.y) = some y →
      y ≠ w.next := by
    intro key' x c' n' y hx hn' _ hs
    have hrx := fromVisits_reach _ _ _ _ hwf key' _ x c' ReachS.root hx
    cases hfd : n'.searchEq c.i c' with
    | none => rw [hfd] at hs; cases hs
    | some fd =>
      rw [hfd] at hs
      simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      have := hlinks x n' c' fd.y hrx hn' (KNode.searchEq_mem n' c.i c' fd (hwf x n' hrx hn') hfd)
      omega
  have huniq' : ∀ key' x n', keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel w.top.rootKey →
      wNode c.p base w x = some n' → n'.leaf = true → key' = [] ++ [cv] := huniq
  by_cases hroom : n.size + 1 < c.p.M ∧ deadOver c.p (n.add c.i (.key cv w.next)) = false
  · exact writerWP_put_room_seg c base hvc [] cv h w.top.rootKey w (by omega) (by simpa using hkey)
      rfl ht
      (fun L n' hL hn' _ => by
        obtain ⟨_, he⟩ := hleafAt L n' hL hn'
        subst he
        exact ⟨hnwf, htimes, hroom.1, hroom.2⟩)
      hnext huniq' hfresh
  · have hlive : c.p.splitAbove < (n.lastVersion c.i).size → n.live ≠ [] := by
      intro hlt he
      have := KNode.lastVersion_size n c.i
      simp only [KNode.cnt, he, List.length_nil] at this
      omega
    by_cases hnew : n.firstTime = some c.i
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_rootSpaceSplitInPlace c base hvc cv h w n hroot hnl hrt
          ⟨hnwf, htimes, hsp.1, hnew, hsp.2, hlive hsp.2⟩ ⟨hidn, hidv, hidt, hidvals, hidr⟩ hbase
          huniq hwf (fun x xn cc z hx hn hz => by
            have := hlinks x xn cc z hx hn hz
            exact ⟨by omega, by omega, by omega, this.2⟩)
      · exact writerWP_put_timeInPlace_seg c base hvc [] cv h w.top.rootKey w (by omega)
          (by simpa using hkey) rfl ht
          (fun L n' hL hn' _ => by
            obtain ⟨_, he⟩ := hleafAt L n' hL hn'
            subst he
            exact ⟨hnwf, htimes, hroom, hnew,
              fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩)
          hnext huniq' hfresh
    · by_cases hsp : c.p.M ≤ n.size + 1 ∧ c.p.splitAbove < (n.lastVersion c.i).size
      · exact writerWP_put_rootSpaceSplit c base hvc cv h w n hroot hnl hrt
          ⟨hnwf, htimes, hsp.1, hnew, hsp.2, hlive hsp.2⟩ ⟨hidn, hidv, hidt, hidvals, hidr⟩ hbase
          huniq hwf (fun x xn cc z hx hn hz => by
            have := hlinks x xn cc z hx hn hz
            exact ⟨by omega, by omega, by omega, by omega, this.2⟩)
      · exact writerWP_put_rootTimeSplit c base hvc cv h w n hroot hnl hrt
          ⟨hnwf, htimes, hroom, hnew, fun hM => Nat.le_of_not_lt (fun hlt => hsp ⟨hM, hlt⟩)⟩
          ⟨hidn, hidv, hidt, hidvals, hidr⟩ hbase huniq hwf (fun x xn cc z hx hn hz => by
            have := hlinks x xn cc z hx hn hz
            exact ⟨by omega, by omega, this.2⟩)

end SIS.Tree
