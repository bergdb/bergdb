import SIS.Tree.WriterKinds
import SIS.Tree.KlongRoundTrip
import SIS.Tree.InvConsequences
import SIS.Proof.Basic

namespace SIS.Tree

open SIS SIS.Check

/-- Values which can occur in a key node's encoded history. -/
def KlongValue : BVal → Prop
  | .key _ _ => True
  | .del _ => True
  | _ => False

def KlongValues (es : History BVal) : Prop := ∀ e ∈ es, KlongValue e.val

theorem klongValues_append (es fs : History BVal)
    (he : KlongValues es) (hf : KlongValues fs) : KlongValues (es++fs) := by
  intro e hm
  rcases List.mem_append.mp hm with hm | hm
  · exact he e hm
  · exact hf e hm

theorem encodeKlong_values (ks : List Klong) (a : KlongEntryState) (k : Klong)
    (ha : KlongValues a.1) : KlongValues (encodeKlong ks a k).1 := by
  cases k with
  | time t =>
    unfold encodeKlong
    dsimp only
    split
    · exact ha
    · exact klongValues_append _ _ ha (by simp [KlongValues,KlongValue,marker])
  | key c y =>
    exact klongValues_append _ _ ha (by simp [KlongValues,KlongValue])
  | del bits =>
    exact klongValues_append _ _ ha (by simp [KlongValues,KlongValue])

theorem entriesOf_values (ks : List Klong) : KlongValues (entriesOf ks) := by
  have hfold : ∀ (qs : List Klong) (a : KlongEntryState), KlongValues a.1 →
      KlongValues (qs.foldl (encodeKlong ks) a).1 := by
    intro qs
    induction qs with
    | nil => intro a ha; exact ha
    | cons q qs ih =>
      intro a ha
      exact ih _ (encodeKlong_values ks a q ha)
  rw [entriesOf_eq_encode]
  unfold finishKlongEntries
  have hf := hfold ks ([],0,[],true) (by simp [KlongValues])
  split
  · exact hf
  · exact klongValues_append _ _ hf (by simp [KlongValues,KlongValue,marker])

/-- High nondata nodes retain an entry distinguishing them from key nodes. -/
def HighKindsOK (p : Params) (P : Struct BVal) : Prop :=
  ∀ x n, P.get? x = some n → n.isData = false → p.keyMax < n.level →
    ∃ e ∈ n.hist, ¬ KlongValue e.val

theorem execW_high_new_marker (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w))
    (n : NewNode) (hn : n ∈ (changesOf i w).new)
    (hd : n.isData = false) (hl : p.keyMax < n.level) :
    ∃ e ∈ addsFor (changesOf i w) i n.id, ¬ KlongValue e.val := by
  obtain ⟨hid,htop,_⟩ := execW_high_new_is_top p tx i v bs w he n hn hd hl
  refine ⟨⟨i,.rootKey w.top.rootKey⟩,mem_addsFor.mpr ⟨rfl,?_⟩,by simp [KlongValue]⟩
  rw [hid]
  unfold changesOf
  apply (List.mergeSort_perm _ _).mem_iff.mpr
  simp [htop]

theorem highKindsOK_apply (p : Params) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (hP : HighKindsOK p P)
    (hc : ∀ nn ∈ c.new, nn.isData = false → p.keyMax < nn.level →
      ∃ e ∈ addsFor c i nn.id, ¬ KlongValue e.val) : HighKindsOK p (P.apply i c) := by
  intro x n hn hd hl
  rw [get?_apply] at hn
  cases hx : P.get? x with
  | some old =>
    simp only [hx,Option.some_or,Option.map_some,Option.some.injEq] at hn
    subst n
    obtain ⟨e,he,hbad⟩ := hP x old hx hd hl
    exact ⟨e,List.mem_append_left _ he,hbad⟩
  | none =>
    simp only [hx,Option.none_or] at hn
    cases hh : newNodeOf c x with
    | none => simp [hh] at hn
    | some nd =>
      simp only [hh,Option.map_some,Option.some.injEq] at hn
      subst n
      have hm := mem_of_get? hh
      obtain ⟨nn,hnn,heq⟩ := List.mem_map.mp hm
      have hid : nn.id = x := congrArg Prod.fst heq
      have hnd : ({level := nn.level,isData := nn.isData,hist := []} : Node BVal) = nd :=
        congrArg Prod.snd heq
      subst nd
      obtain ⟨e,he,hbad⟩ := hc nn hnn hd hl
      rw [hid] at he
      exact ⟨e,List.mem_append_right _ he,hbad⟩

theorem highKindsOK_exec (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (P : Struct BVal) (hP : HighKindsOK p P) :
    HighKindsOK p (P.apply i (exec p tx i v)) := by
  apply highKindsOK_apply p P i _ hP
  unfold exec exec?
  cases he : runOps p tx.base tx.ops i v with
  | error e => simp [Except.map]
  | ok result =>
    rcases result with ⟨bs,w⟩
    simp only [Except.map]
    intro nn hn hd hl
    exact execW_high_new_marker p tx i v bs w he nn hn hd hl

theorem highKindsOK_init (p : Params) : HighKindsOK p (initStruct p) := by
  intro x n hn hd hl
  simp only [initStruct,get?_cons,get?_nil] at hn
  split at hn
  · simp only [Option.some.injEq] at hn
    subst n
    exact ⟨⟨0,.top 2⟩,by simp,by simp [KlongValue]⟩
  · split at hn
    · simp only [Option.some.injEq] at hn
      subst n
      have hk := keyLevel_le_keyMax p 0 0 (Nat.zero_le _)
      dsimp only at hl
      omega
    · split at hn
      · simp only [Option.some.injEq] at hn
        subst n
        exact ⟨⟨0,.rootKey 1⟩,by simp,by simp [KlongValue]⟩
      · cases hn

/-- Top/root histories remain distinguishable from key-node histories after
every run, including runs whose writer errors are ignored by exec. -/
theorem treeRun_highKindsOK (p : Params) (ts : List Tx) : HighKindsOK p (treeRun p ts) := by
  have hf : ∀ qs : List (Tx × Nat), ∀ P, HighKindsOK p P →
      HighKindsOK p (qs.foldl (fun P (q : Tx × Nat) =>
        P.apply (q.2+1) (exec p q.1 (q.2+1) (view (treeSpec p) P q.2))) P) := by
    intro qs
    induction qs with
    | nil => intro P hP; exact hP
    | cons q qs ih =>
      intro P hP
      exact ih _ (highKindsOK_exec p q.1 (q.2+1) _ P hP)
  exact hf _ _ (highKindsOK_init p)

theorem walk_current_history (p : Params) (v : View BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hv : v x = some nd) (hd : nd.isData = false)
    (hw : walk p v t (f+1) x lo hi isRoot space = []) :
    entriesOf (klongsOf nd.hist) = nd.hist := by
  by_cases he : entriesOf (klongsOf nd.hist) = nd.hist
  · exact he
  · have hm : s!"key node {x}: its klongs do not give its history" ∈
        walk p v t (f+1) x lo hi isRoot space := by
      rw [walk]
      simp only [hv,hd,Bool.false_eq_true,↓reduceIte]
      simp [he]
    simp [hw] at hm

theorem highKindsOK_walk_level (p : Params) (P : Struct BVal) (t f : Nat)
    (x lo : Nat) (hi : Option Nat) (isRoot space : Bool) (nd : Node BVal)
    (hP : HighKindsOK p P) (hv : P.get? x = some nd) (hd : nd.isData = false)
    (hw : walk p (viewOf P) t (f+1) x lo hi isRoot space = []) : nd.level ≤ p.keyMax := by
  by_cases hl : nd.level ≤ p.keyMax
  · exact hl
  · obtain ⟨e,he,hbad⟩ := hP x nd hv hd (by omega)
    have hh := walk_current_history p (viewOf P) t f x lo hi isRoot space nd hv hd hw
    rw [← hh] at he
    exact (hbad (entriesOf_values _ e he)).elim

end SIS.Tree
