import SIS.Tree.SortedKeys

namespace SIS.Tree

/-- A well-formed segment is long exactly when the key continues after it. -/
theorem keyWf_segment_length (key : Key) (g cv : Nat)
    (hw : keyWf key = true) (hc : key[g]? = some cv) :
    (segLen cv = 7 ↔ g+1 < key.length) ∧
      (segLen cv ≠ 7 ↔ key.length = g+1) := by
  induction g generalizing key with
  | zero =>
    cases key with
    | nil => simp at hc
    | cons x rest =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hc
      subst cv
      cases rest with
      | nil =>
        have hs : segLen x ≠ 7 := by simpa only [keyWf,bne_iff_ne] using hw
        simp [hs]
      | cons y rest =>
        change (segLen x == 7 && keyWf (y :: rest)) = true at hw
        have hs : segLen x = 7 := by
          have hh : (segLen x == 7) = true ∧ keyWf (y :: rest) = true := by
            simpa only [Bool.and_eq_true] using hw
          simpa only [beq_iff_eq] using hh.1
        simp [hs]
  | succ g ih =>
    cases key with
    | nil => simp at hc
    | cons x rest =>
      cases rest with
      | nil => simp at hc
      | cons y rest =>
        change (segLen x == 7 && keyWf (y :: rest)) = true at hw
        have htail : keyWf (y :: rest) = true := by
          have hh : (segLen x == 7) = true ∧ keyWf (y :: rest) = true := by
            simpa only [Bool.and_eq_true] using hw
          exact hh.2
        have hh := ih (y :: rest) htail hc
        simpa only [List.length_cons,Nat.add_lt_add_iff_right,Nat.add_left_inj] using hh

/-- Well-formed segment lists cannot be proper prefixes of one another. -/
theorem keyWf_prefix_eq (a b : Key) (ha : keyWf a = true) (hb : keyWf b = true)
    (hp : a.IsPrefix b) : a = b := by
  have hne : a ≠ [] := by intro he; subst a; cases ha
  have hpos : 0 < a.length := by cases a <;> simp_all
  let g := a.length-1
  have hg : g < a.length := by omega
  let cv := a[g]
  have hca : a[g]? = some cv := List.getElem?_eq_getElem hg
  obtain ⟨suffix,hsuffix⟩ := hp
  have hcb : b[g]? = some cv := by
    rw [← hsuffix,List.getElem?_append_left hg]
    exact hca
  have hshort : segLen cv ≠ 7 := (keyWf_segment_length a g cv ha hca).2.mpr (by omega)
  have hlen := (keyWf_segment_length b g cv hb hcb).2.mp hshort
  have hlength := congrArg List.length hsuffix
  simp only [List.length_append] at hlength
  have hnil : suffix = [] := List.length_eq_zero_iff.mp (by omega)
  simpa only [hnil,List.append_nil] using hsuffix

/-- At a terminal segment, its prefix and compare value identify the whole
well-formed key. The same compare value cannot instead continue into a child. -/
theorem keyWf_terminal_segment_unique (g cv : Nat) (a b : Key)
    (ha : keyWf a = true) (hb : keyWf b = true)
    (hp : a.take g = b.take g) (hca : a[g]? = some cv) (hcb : b[g]? = some cv)
    (hlena : a.length = g+1) : a = b := by
  have hshort := (keyWf_segment_length a g cv ha hca).2.mpr hlena
  have hlenb := (keyWf_segment_length b g cv hb hcb).2.mp hshort
  have hta : a.take (g+1) = a := List.take_of_length_le (by omega)
  have htb : b.take (g+1) = b := List.take_of_length_le (by omega)
  calc
    a = a.take (g+1) := hta.symm
    _ = a.take g ++ [cv] := by rw [List.take_add_one,hca]; rfl
    _ = b.take g ++ [cv] := by rw [hp]
    _ = b.take (g+1) := by rw [List.take_add_one,hcb]; rfl
    _ = b := htb

/-- After an operation at a terminal compare value, every later key in the
same segment-prefix group has a strictly larger compare value there. -/
theorem keyLt_terminal_segment_strict (g : Nat) (a b : Key) (ca cb : Nat)
    (ha : keyWf a = true) (hb : keyWf b = true) (hs : keyLt a b = true)
    (hp : a.take g = b.take g) (hca : a[g]? = some ca) (hcb : b[g]? = some cb)
    (hlena : a.length = g+1) : ca < cb := by
  have hle := keyLt_segment_mono g a b ca cb hs hp hca hcb
  have hne : ca ≠ cb := by
    intro he
    subst cb
    have hab := keyWf_terminal_segment_unique g ca a b ha hb hp hca hcb hlena
    subst b
    rw [keyLt_irrefl] at hs
    cases hs
  omega

theorem terminal_segment_get (key : Key) (g : Nat) (hlen : key.length = g+1) :
    key[g]? = some key[g]! := by
  have hg : g < key.length := by omega
  simp only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hg,Option.getD_some]

/-- Full-key order becomes strict compare-value order for terminal writes
in one segment-prefix group. -/
theorem terminal_segment_values_pairwise (keys : List Key) (g : Nat) (pre : Key)
    (horder : keys.Pairwise (fun a b => keyLt a b = true))
    (hw : ∀ key ∈ keys, keyWf key = true)
    (hlen : ∀ key ∈ keys, key.length = g+1)
    (hp : ∀ key ∈ keys, key.take g = pre) :
    (keys.map (fun key => key[g]!)).Pairwise (fun a b => a < b) := by
  apply List.pairwise_map.mpr
  refine horder.imp_of_mem ?_
  intro a b ha hb hab
  exact keyLt_terminal_segment_strict g a b a[g]! b[g]! (hw a ha) (hw b hb) hab
    ((hp a ha).trans (hp b hb).symm)
    (terminal_segment_get a g (hlen a ha)) (terminal_segment_get b g (hlen b hb)) (hlen a ha)

theorem terminal_prefix_values_before (keys : List Key) (key : Key) (g cv : Nat)
    (hs : sortedKeys (keys ++ [key]) = true)
    (hw : ∀ a ∈ keys, keyWf a = true) (hkey : keyWf key = true)
    (hlen : ∀ a ∈ keys, a.length = g+1)
    (hp : ∀ a ∈ keys, a.take g = key.take g) (hcv : key[g]? = some cv) :
    (keys.map (fun a => a[g]!)).Nodup ∧
      ∀ c ∈ keys.map (fun a => a[g]!), c < cv := by
  have hpair := List.pairwise_append.mp (sortedKeys_pairwise (keys ++ [key]) hs)
  have hvalues := terminal_segment_values_pairwise keys g (key.take g) hpair.1 hw hlen hp
  refine ⟨hvalues.imp (by intro a b hab; omega),?_⟩
  intro c hc
  obtain ⟨old,hold,he⟩ := List.mem_map.mp hc
  subst c
  exact keyLt_terminal_segment_strict g old key old[g]! cv
    (hw old hold) hkey (hpair.2.2 old hold key List.mem_cons_self) (hp old hold)
    (terminal_segment_get old g (hlen old hold)) hcv (hlen old hold)

end SIS.Tree
