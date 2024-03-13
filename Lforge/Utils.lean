import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card
set_option autoImplicit false

def univ {α : Type} : Set α := fun _ ↦ True
def none {α : Type} : Set α := fun _ ↦ False
def iden {α : Type} : α → α := fun a ↦ a

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

def transpose {α β : Type} : (α × β) → (β × α) := Prod.swap

set_option autoImplicit true

/- Coercions -/
-- We do all these first because we use these coercions later below
/- Singletons -/
instance : Coe α (α → Prop) where
  coe := Eq

instance : Coe α (Set α) where
  coe := Eq

instance : Coe (α × β) (α → β → Prop) where
  coe := fun s ↦ fun a b ↦ s = (a, b)

instance : Coe (α × β × γ) (α → β → γ → Prop) where
  coe := fun s ↦ fun a b c ↦ s = (a, b, c)

/- Sets -/
instance : Coe (Set (α × β)) (α → β → Prop) where
  coe := fun s ↦ fun a b ↦ (a, b) ∈ s

instance : Coe (α → β → Prop) (Set (α × β)) where
  coe := fun r ↦ {p : α × β | r p.1 p.2}

instance : Coe (Set (α × β × γ)) (α → β → γ → Prop) where
  coe := fun s ↦ fun a b c ↦ (a, b, c) ∈ s

instance : Coe (α → β → γ → Prop) (Set (α × β × γ)) where
  coe := fun r ↦ {p : α × β × γ | r p.1 p.2.1 p.2.2}

instance : Coe (Set (α × β × γ × δ)) (α → β → γ → δ → Prop) where
  coe := fun s ↦ fun a b c d ↦ (a, b, c, d) ∈ s

instance : Coe (α → β → γ → δ → Prop) (Set (α × β × γ × δ)) where
  coe := fun r ↦ {p : α × β × γ × δ | r p.1 p.2.1 p.2.2.1 p.2.2.2}

/- (α → Set)s -/
instance : Coe (α → Set (β × γ)) (α → β → γ → Prop) where
  coe := fun r ↦ fun a b c ↦ (b, c) ∈ r a

instance : Coe (α → Set (β × γ × δ)) (α → β → γ → δ → Prop) where
  coe := fun r ↦ fun a b c d ↦ (b, c, d) ∈ r a

namespace Forge

/- In -/
class HIn (α : Type) (β : Type) :=
  (subset : α → β → Prop)

/--
`A ⊂ᶠ B` when `A` is a subset of `B`. If `A` is a singleton, then this is set membership operator.
-/
infix:60 " ⊂ᶠ " => HIn.subset

instance : HIn α (Set α) where
  subset := fun elt s ↦ s elt

instance : HIn α (α → Prop) where
  subset := fun elt s ↦ s elt

instance [HasSubset α] : HIn (Set α) (Set α) where
  subset := HasSubset.Subset

instance {α β : Type} : HIn (α → β → Prop) (α → β → Prop) where
  subset := fun f g ↦ ∀ a b, f a b → g a b

/- Eq -/

class HEq (α : Type) (β : Type) :=
  (eq : α → β → Prop)

/--
`A =ᶠ B` when `A` is equal to `B`. This works implicitly to compare expressions of mixed types, such as singletons and sets.
-/
infix:60 " =ᶠ " => HEq.eq

@[reducible] instance [HEq α β] : HEq β α where
  eq := fun s1 s2 ↦ HEq.eq s2 s1

@[reducible] instance : HEq α α where
  eq := Eq

@[reducible] instance : HEq α (Set α) where
  eq := fun s1 s2 ↦ s2 = Set.singleton s1

@[reducible] instance : HEq α (α → Prop) where
  eq := fun s1 s2 ↦ s2 = Set.singleton s1

@[reducible] instance : HEq (Set α) (Set α) where
  eq := Eq

@[reducible] instance {α : Type} : HEq (α → Prop) (α → Prop) where
  eq := Eq

/- Transpose -/
class HTranspose (α : Type) (γ : outParam Type) :=
  (transpose : α → γ)

/--
Returns the transpose of an arity-2 expression.
-/
notation:80 lhs:81 "ᵀ" => HTranspose.transpose lhs

instance : HTranspose (α × β) (β × α) where
  transpose := Prod.swap

instance {α β : Type} : HTranspose (α → β → Prop) (β → α → Prop) where
  transpose := Relation.Transpose

/- Join -/

class HJoin (α : Type) (β : Type) (γ : outParam Type) :=
  (join : α → β → γ)

/--
`A ⋈ B` returns the relational join of the two exprs. It combines two relations by seeking out rows with common values in their rightmost and leftmost columns. Type as `\bowtie`.
-/
infix:50 " ⋈ " => HJoin.join

instance {α β : Type} : HJoin (α) (α → β → Prop) (β → Prop) where
  join := fun a g ↦ g a

instance {α β : Type} : HJoin (α → Prop) (α → β → Prop) (β → Prop) where
  join := fun f g b ↦ ∃ a : α, f a ∧ g a b

/- Cross -/

class HCross (α : Type) (β : Type) (γ : outParam Type) :=
  (cross : α → β → γ)

infix:50 " ×ᶠ " => HCross.cross

instance {α β : Type} : HCross α β (α → β → Prop) where
  cross := fun a b ↦ (a, b)

instance {α β : Type} : HCross (α → Prop) (β → Prop) (α → β → Prop) where
  cross := fun f g a b ↦ f a ∧ g b

-- TODO: Cross with other arities?

-- Binops

instance {α β : Type} : Union (α → β → Prop) where
  union := fun f g ↦ fun a b ↦ f a b ∨ g a b

instance {α β : Type} : Inter (α → β → Prop) where
  inter := fun f g ↦ fun a b ↦ f a b ∧ g a b

prefix:60 "^" => Relation.TransGen
prefix:60 "*" => Relation.ReflTransGen

end Forge
