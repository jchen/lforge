import Mathlib.Tactic
import Mathlib.Logic.Relation
set_option autoImplicit false

namespace SigQuantifier
  def abstract (a : Type) :=
    IsEmpty a

  def one (a : Type) :=
    Singleton a

  def lone (a : Type) :=
    Subsingleton a

end SigQuantifier

namespace ExprQuantifier
  def one {a : Type} (f : a → Prop) :=
    ∃! x : a, f = Set.singleton x

  def no {a : Type} (f : a → Prop) :=
    (∅ : Set a) = f

  def lone {a : Type} (f : a → Prop) :=
    one f ∨ no f

  def some {a : Type} (f : a → Prop) :=
    ∃ t : a, f t

end ExprQuantifier

namespace ExprCmp
  def subset {a : Type} (f g : Set a) :=
    ∀ t : a, t ∈ f → t ∈ g

  def eq {a : Type} (f g : a → Prop) :=
    ∀ t : a, f t ↔ g t

end ExprCmp

namespace FieldQuantifier
  def one {α β : Type} (f : α → β → Prop) :=
    ∀ a : α, ExprQuantifier.one (f a ·)

  def no {α β : Type} (f : α → β → Prop) :=
    ∀ a : α, ExprQuantifier.no (f a ·)

  def lone {α β : Type} (f : α → β → Prop) :=
    ∀ a : α, ExprQuantifier.lone (f a ·)

  def pfunc {α β γ : Type} (f : α → (β × γ) → Prop) :=
    ∀ a : α, ∀ b : β, ExprQuantifier.lone (f a <| Prod.mk b ·)

  def func {α β γ : Type} (f : α → (β × γ) → Prop) :=
    ∀ a : α, ∀ b : β, ExprQuantifier.one (f a <| Prod.mk b ·)

end FieldQuantifier

def reachable {α : Type} (a1 a2 : α) (r : α → α → Prop) : Prop :=
  Relation.TransGen r a1 a2

@[mk_iff transpose_iff]
inductive Relation.Transpose {α β : Type} (r : α → β → Prop) : β → α → Prop
  | mk {a} {b} : r a b → Relation.Transpose r b a

def hm : Lean.HashMap Nat Nat := .empty
def hm2 := hm.insert 1 2
