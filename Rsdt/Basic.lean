import Mathlib.Order.Lattice

universe u v w
variable {α : Type u} {β : Type v}

/-- An abstract data type. -/
class DataType (α : Type u) where
  /-- The set of mutations. -/
  μ : Type v
  /-- The function which applies a mutation to the data. -/
  apply : μ → α → α

namespace DataType

variable [DataType α] [DataType β]

/-- The relation of reachability: `a ≤ b` iff `b` can be obtained from `a`. -/
protected inductive le : α → α → Prop
  | refl : (a : α) → DataType.le a a
  | step : {a b : α} → (f : _) → DataType.le a b → DataType.le a (apply f b)

/-- The notation `a ≤ b`. -/
instance : LE α where
  le := DataType.le

/-- By definition, `≤` is reflexive. -/
protected theorem le_refl (a : α) : a ≤ a :=
  le.refl _

/-- By definition, `≤` is transitive. -/
protected theorem le_trans {a b c : α} : a ≤ b → b ≤ c → a ≤ c := by
  intros h₁ h₂
  induction h₂ with
  | refl        => exact h₁
  | step f _ ih => exact DataType.le.step f ih

instance : Preorder α where
  le_refl := DataType.le_refl
  le_trans := @DataType.le_trans _ _

end DataType

/-- A semilattice data type.
It is an abstract data type with reachability relation `≤` forming a
join-semilattice (i.e. least upper bounds uniquely exist). -/
class SemilatticeDataType (α : Type u) extends DataType α, SemilatticeSup α where
  /-- The function which automatically merges two states. -/
  merge : α → α → α
  /-- The merge function correctly gives the least upper bound. -/
  merge_eq_join : ∀ a b : α, merge a b = a ⊔ b
