import SIS.Proof.Util

set_option autoImplicit false

namespace SIS.Tree

theorem filterMap_congr_mem {α β : Type} (xs : List α) (f g : α → Option β)
    (he : ∀ a ∈ xs, f a = g a) : xs.filterMap f = xs.filterMap g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.filterMap_cons, he a List.mem_cons_self,
      ih (fun q hq => he q (List.mem_cons_of_mem a hq))]

theorem foldl_congr_mem {α β : Type} (xs : List α) (f g : β → α → β) (init : β)
    (he : ∀ acc a, a ∈ xs → f acc a = g acc a) : xs.foldl f init = xs.foldl g init := by
  induction xs generalizing init with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.foldl_cons, he init a List.mem_cons_self]
    exact ih _ (fun acc q hq => he acc q (List.mem_cons_of_mem a hq))

theorem all_congr_mem {α : Type} (xs : List α) (f g : α → Bool)
    (he : ∀ a ∈ xs, f a = g a) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.all_cons, he a List.mem_cons_self,
      ih (fun q hq => he q (List.mem_cons_of_mem a hq))]

end SIS.Tree
