import SIS.Tree.WriterKinds
import SIS.Proof.Basic

namespace SIS.Tree

open SIS SIS.Check

def MadeData (w : W) : Prop :=
  ∀ n ∈ w.made, n.isData = true → ∃ h, (n.id,h) ∈ w.vals

@[instance_reducible]
def madeDataInvariant : WriterStateInvariant where
  pred := fun _ w => MadeData w
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind,writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind,writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind,writerWP_set,writerWP_pure]; exact hw
      · exact writerWP_throw _ _ _ _
  store := by
    intro x n c w hw
    simp only [putNode,writerWP_modify]
    exact hw
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify <;>
      (intro n hn hd
       simp only [List.mem_append,List.mem_singleton] at hn
       rcases hn with hn | rfl
       · exact hw n hn hd
       · cases hd)
  value := by
    intro h c w hw
    unfold newValue fresh
    wpSimplify
    intro n hn hd
    simp only [List.mem_append,List.mem_singleton] at hn
    rcases hn with hn | rfl
    · obtain ⟨v,hv⟩ := hw n hn hd
      exact ⟨v,List.mem_append_left _ hv⟩
    · exact ⟨h,by simp⟩
  allocate := by
    intro c w hw
    unfold fresh
    wpSimplify
    exact hw
  trace := by intro s c w hw; simp only [note,writerWP_modify]; exact hw
  provenance := by
    intro x old c w hw
    unfold setMadeFor
    split
    · simp only [writerWP_modify]; exact hw
    · simpa only [writerWP_pure] using hw
  take := by intro x c w hw; simp only [takenBack,writerWP_modify]; exact hw
  clear := by intro c w hw; simp only [pathClear,writerWP_modify]; exact hw
  path := by intro cv x c w hw; simp only [pathAdd,writerWP_modify]; exact hw
  top := by
    intro x c w hw
    unfold newSuperRoot note fresh
    wpSimplify
    split
    · wpSimplify; exact hw
    · wpSimplify
      intro n hn hd
      simp only [List.mem_append,List.mem_singleton] at hn
      rcases hn with hn | rfl
      · exact hw n hn hd
      · cases hd
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

theorem execW_madeData (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w)) : MadeData w := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      letI := madeDataInvariant
      exact state_ops tx.ops {p := p,i := i,view := rootless v}
        {next := tx.base,top := top} (by change MadeData _; simp [MadeData]) bs w hr

/-- Every data node contains an actual data entry. -/
def DataEntriesOK (P : Struct BVal) : Prop :=
  ∀ x n, P.get? x = some n → n.isData = true →
    ∃ e ∈ n.hist, ∃ h, e.val = .data h

theorem execW_new_data_entry (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (he : execW p tx i v = .ok (bs,w))
    (n : NewNode) (hn : n ∈ (changesOf i w).new) (hd : n.isData = true) :
    ∃ e ∈ addsFor (changesOf i w) i n.id, ∃ h, e.val = .data h := by
  obtain ⟨hm,_⟩ := changesOf_new_mem i w n hn
  obtain ⟨h,hval⟩ := execW_madeData p tx i v bs w he n hm hd
  refine ⟨⟨i,.data h⟩,mem_addsFor.mpr ⟨rfl,?_⟩,h,rfl⟩
  unfold changesOf
  apply (List.mergeSort_perm _ _).mem_iff.mpr
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨(n.id,h),hval,rfl⟩

theorem dataEntriesOK_apply (P : Struct BVal) (i : Time) (c : Changes BVal)
    (hP : DataEntriesOK P)
    (hc : ∀ nn ∈ c.new, nn.isData = true →
      ∃ e ∈ addsFor c i nn.id, ∃ h, e.val = .data h) : DataEntriesOK (P.apply i c) := by
  intro x n hn hd
  rw [get?_apply] at hn
  cases hx : P.get? x with
  | some old =>
    simp only [hx,Option.some_or,Option.map_some,Option.some.injEq] at hn
    subst n
    obtain ⟨e,he,h,hval⟩ := hP x old hx hd
    exact ⟨e,List.mem_append_left _ he,h,hval⟩
  | none =>
    simp only [hx,Option.none_or] at hn
    cases hh : newNodeOf c x with
    | none => simp [hh] at hn
    | some nd =>
      simp only [hh,Option.map_some,Option.some.injEq] at hn
      subst n
      obtain ⟨nn,hnn,heq⟩ := List.mem_map.mp (mem_of_get? hh)
      have hid : nn.id = x := congrArg Prod.fst heq
      have hnd : ({level := nn.level,isData := nn.isData,hist := []} : Node BVal) = nd :=
        congrArg Prod.snd heq
      subst nd
      obtain ⟨e,he,h,hval⟩ := hc nn hnn hd
      rw [hid] at he
      exact ⟨e,List.mem_append_right _ he,h,hval⟩

theorem dataEntriesOK_exec (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (P : Struct BVal) (hP : DataEntriesOK P) :
    DataEntriesOK (P.apply i (exec p tx i v)) := by
  apply dataEntriesOK_apply P i _ hP
  unfold exec exec?
  cases he : runOps p tx.base tx.ops i v with
  | error e => simp [Except.map]
  | ok result =>
    rcases result with ⟨bs,w⟩
    simp only [Except.map]
    intro nn hn hd
    exact execW_new_data_entry p tx i v bs w he nn hn hd

theorem dataEntriesOK_init (p : Params) : DataEntriesOK (initStruct p) := by
  intro x n hn hd
  simp only [initStruct,get?_cons,get?_nil] at hn
  split at hn
  · cases Option.some.inj hn
    cases hd
  · split at hn
    · cases Option.some.inj hn
      cases hd
    · split at hn
      · cases Option.some.inj hn
        cases hd
      · cases hn

theorem treeRun_dataEntriesOK (p : Params) (ts : List Tx) : DataEntriesOK (treeRun p ts) := by
  have hf : ∀ qs : List (Tx × Nat), ∀ P, DataEntriesOK P →
      DataEntriesOK (qs.foldl (fun P (q : Tx × Nat) =>
        P.apply (q.2+1) (exec p q.1 (q.2+1) (view (treeSpec p) P q.2))) P) := by
    intro qs
    induction qs with
    | nil => intro P hP; exact hP
    | cons q qs ih =>
      intro P hP
      exact ih _ (dataEntriesOK_exec p q.1 (q.2+1) _ P hP)
  exact hf _ _ (dataEntriesOK_init p)

theorem valueOf_some_of_dataEntriesOK (P : Struct BVal) (x : NodeId) (n : Node BVal)
    (hP : DataEntriesOK P) (hx : P.get? x = some n) (hd : n.isData = true) :
    ∃ h, valueOf (viewOf P) x = some h := by
  obtain ⟨e,he,val,hval⟩ := hP x n hx hd
  unfold valueOf viewOf
  simp only [hx,hd,↓reduceIte]
  cases hh : n.hist.findSome? (fun e => match e.val with | .data h => some h | _ => none) with
  | some h => exact ⟨h,rfl⟩
  | none =>
    have hn := List.findSome?_eq_none_iff.mp hh e he
    simp [hval] at hn

end SIS.Tree
