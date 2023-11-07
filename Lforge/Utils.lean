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

  def subset {a : Type} (f g : Set a) :=
    ∀ x : a, f x

  def eq {a : Type} (f g : a → Prop) :=
    ∀ t : a, f t ↔ g t

end ExprQuantifier

namespace FieldQuantifier
  def one {α : Type} {β : Type} (f : α → β → Prop) :=
    ∀ a : α, ExprQuantifier.one (f a ·)

  def no {α : Type} {β : Type} (f : α → β → Prop) :=
    ∀ a : α, ExprQuantifier.no (f a ·)

  def lone {α : Type} {β : Type} (f : α → β → Prop) :=
    ∀ a : α, ExprQuantifier.lone (f a ·)

end FieldQuantifier

def reachable {α : Type} (a1 a2 : α) (r : α → α → Prop) : Prop :=
  Relation.TransGen r a1 a2

def if_else (a b c : Prop) : Prop :=
  (a → b) ∧ (¬ a → c)
