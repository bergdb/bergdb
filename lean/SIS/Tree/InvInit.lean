import SIS.Tree.InvConsequences
import SIS.Proof.TreeInit

namespace SIS.Tree

open SIS SIS.Check

theorem heightOf_initial_key (p : Params) : p.heightOf (p.keyLevel 0 0) = 0 := by
  simp [Params.heightOf,Params.keyLevel]

theorem initial_key_level_le (p : Params) : p.keyLevel 0 0 ≤ p.keyMax := by
  simp only [Params.keyLevel,Params.keyMax,Nat.sub_zero]
  omega

theorem rootAt_init (p : Params) (t : Time) : rootAt (viewOf (initStruct p)) t = some 1 := by
  simp [rootAt,topAt,rootKeyOf,viewOf,initStruct,Struct.get?,root,History.upTo,
    List.lookup_cons]

theorem knodeOf_init (p : Params) :
    knodeOf p (viewOf (initStruct p)) 1 = some ⟨true,[.time 0]⟩ := by
  simp [knodeOf,viewOf,init_get_key,heightOf_initial_key,
    Nat.not_lt_of_ge (initial_key_level_le p),klongsOf,marker]

theorem pointersOK_init (p : Params) : PointersOK (initStruct p) := by
  intro q hq e he y hy
  rcases mem_init p q hq with rfl | rfl | rfl
  · simp only [List.mem_singleton] at he
    subst e
    have hy' : y = 2 := by simpa [bptrs] using hy
    subst y
    rw [init_get_top]
    rfl
  · simp only [List.mem_singleton] at he
    subst e
    simp [bptrs,marker] at hy
  · simp only [List.mem_singleton] at he
    subst e
    have hy' : y = 1 := by simpa [bptrs] using hy
    subst y
    rw [init_get_key]
    rfl

theorem invOK_init (p : Params) (hM : 1 ≤ p.M) (t : Time) : InvOK p (initStruct p) t := by
  unfold InvOK faultsAt
  rw [rootAt_init]
  dsimp only
  have hf : p.fuel = (p.G+1)*(p.H+2)+1+1 := by unfold Params.fuel; omega
  rw [hf]
  rw [walk.eq_def]
  simp [viewOf,init_get_key,heightOf_initial_key,KNode.size,KNode.liveAt,
    KNode.lastVersionGivenDel,KNode.delAt,lastBitmapOf,klongsOf,entriesOf,marker,
    prefixAt,klongsWf,KNode.deadCount]
  omega

theorem within_nil (p : Params) : Within p [] := by simp [Within]

theorem getEq_init (p : Params) (t : Time) (c : Nat) :
    getEq p (viewOf (initStruct p)) t c p.fuel 1 = none := by
  have hf : p.fuel = (p.G+1)*(p.H+2)+1+1 := by unfold Params.fuel; omega
  rw [hf,getEq]
  simp [knodeOf_init,KNode.searchEq,prefixAt]

theorem get_init (p : Params) (t : Time) (key : Key) :
    get p (viewOf (initStruct p)) t key = none := by
  unfold get
  rw [rootAt_init]
  cases key with
  | nil => rfl
  | cons c rest =>
    cases rest with
    | nil => simp [getFrom,getEq_init]
    | cons d rest => simp [getFrom,getEq_init]

/-- TP7 needs a size premise even before the first transaction: the
primordial key node contains its time klong. -/
theorem not_invPreserved_zero_size : ¬ InvPreserved ({M := 0,G := 0,H := 0} : Params) := by
  intro h
  have hi := (h [] (within_nil _) 0 (by decide)).1
  unfold InvOK at hi
  have hn : faultsAt ({M := 0,G := 0,H := 0} : Params)
      (viewOf (treeRun ({M := 0,G := 0,H := 0} : Params) [])) 0 ≠ [] := by decide +kernel
  exact hn hi

end SIS.Tree
