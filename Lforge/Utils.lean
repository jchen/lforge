import Mathlib.Tactic
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card
set_option autoImplicit true

@[reducible, simp] def univ {α : Type} : Set α := fun _ ↦ True
@[reducible, simp] def none {α : Type} : Set α := fun _ ↦ False
@[reducible, simp] def iden {α : Type} : α → α → Prop := Eq

namespace SigQuantifier
  class One (α : Type) :=
    one : α
    allEq : ∀ x : α, x = one
end SigQuantifier

@[reducible, simp] instance [o: SigQuantifier.One α] : CoeDep Type (α : Type) α where
  coe := o.one

namespace ExprQuantifier
@[reducible, simp] def one {a : Type} (f : a → Prop) :=
  ∃! x : a, f = Set.singleton x

@[reducible, simp] def no {a : Type} (f : a → Prop) :=
  (∅ : Set a) = f

@[reducible, simp] def lone {a : Type} (f : a → Prop) :=
  one f ∨ no f

@[reducible, simp] def some {a : Type} (f : a → Prop) :=
  ∃ t : a, f t
end ExprQuantifier

namespace ExprCmp
@[reducible, simp] def subset {a : Type} (f g : Set a) :=
  ∀ t : a, t ∈ f → t ∈ g

@[reducible, simp] def eq {a : Type} (f g : a → Prop) :=
  ∀ t : a, f t ↔ g t
end ExprCmp

namespace FieldQuantifier
@[reducible, simp] def one {α β : Type} (f : α → β → Prop) :=
  ∀ a : α, ExprQuantifier.one (f a ·)

@[reducible, simp] def no {α β : Type} (f : α → β → Prop) :=
  ∀ a : α, ExprQuantifier.no (f a ·)

@[reducible, simp] def lone {α β : Type} (f : α → β → Prop) :=
  ∀ a : α, ExprQuantifier.lone (f a ·)

@[reducible, simp] def pfunc {α β γ : Type} (f : α → β → γ → Prop) :=
  ∀ a : α, ∀ b : β, ExprQuantifier.lone (f a b ·)

@[reducible, simp] def func {α β γ : Type} (f : α → β → γ → Prop) :=
  ∀ a : α, ∀ b : β, ExprQuantifier.one (f a b ·)
end FieldQuantifier

@[reducible, simp] def reachable {α : Type} (a1 a2 : α) (r : α → α → Prop) : Prop :=
  Relation.TransGen r a1 a2

@[mk_iff transpose_iff]
inductive Relation.Transpose {α β : Type} (r : α → β → Prop) : β → α → Prop
  | mk {a} {b} : r a b → Relation.Transpose r b a

@[reducible, simp] def transpose {α β : Type} : (α × β) → (β × α) := Prod.swap

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

@[reducible, simp] instance [Coe α β] : HIn α (Set β) where
  subset := fun elt s ↦ s elt

@[reducible, simp] instance : HIn α (α → Prop) where
  subset := fun elt s ↦ s elt

@[reducible, simp] instance [HasSubset α] : HIn (Set α) (Set α) where
  subset := HasSubset.Subset

@[reducible, simp] instance {α β : Type} : HIn (α → β → Prop) (α → β → Prop) where
  subset := fun f g ↦ ∀ a b, f a b → g a b

/- Eq -/

class HEq (α : Type) (β : Type) :=
  (eq : α → β → Prop)

/--
`A =ᶠ B` when `A` is equal to `B`. This works implicitly to compare expressions of mixed types, such as singletons and sets.
-/
infix:60 " =ᶠ " => HEq.eq

@[reducible, simp] instance [HEq α β] : HEq β α where
  eq := fun s1 s2 ↦ HEq.eq s2 s1

@[reducible, simp] instance : HEq α α where
  eq := Eq

@[reducible, simp] instance : HEq α (Set α) where
  eq := fun s1 s2 ↦ s2 = Set.singleton s1

@[reducible, simp] instance : HEq α (α → Prop) where
  eq := fun s1 s2 ↦ s2 = Set.singleton s1

@[reducible, simp] instance : HEq (Set α) (Set α) where
  eq := Eq

@[reducible, simp] instance {α : Type} : HEq (α → Prop) (α → Prop) where
  eq := Eq

@[reducible, simp] instance {α : Type} : HEq (α → Prop) (Set α) where
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
  join : α → β → γ

/--
`A ⋈ B` returns the relational join of the two exprs. It combines two relations by seeking out rows with common values in their rightmost and leftmost columns. Type as `\bowtie`.
-/
infix:50 " ⋈ " => HJoin.join

-- TODO: Add more, join is broken with new one field

@[reducible, simp] instance {α β : Type} : HJoin (α) (α → β) (β) where
  join := fun a g ↦ g a

@[reducible, simp] instance {α β γ : Type} : HJoin (α) (α → β → γ) (β → γ) where
  join := fun a g ↦ g a

@[reducible, simp] instance {α β γ : Type} : HJoin (α) (α → β → γ → Prop) (β → γ → Prop) where
  join := fun a g ↦ g a

@[reducible, simp] instance {α β γ δ : Type} : HJoin (α) (α → β → γ → δ → Prop) (β → γ → δ → Prop) where
  join := fun a g ↦ g a

@[reducible, simp] instance {α β γ δ ε : Type} : HJoin (α) (α → β → γ → δ → ε → Prop) (β → γ → δ → ε → Prop) where
  join := fun a g ↦ g a

@[reducible, simp] instance {α β γ: Type} : HJoin (γ → α) (α → β) (γ → β) where
  join := fun l r g ↦ r (l g)

@[reducible, simp] instance {α β γ δ: Type} : HJoin (γ → α) (α → β → δ) (γ → β → δ) where
  join := fun l r g b ↦ r (l g) b

@[reducible, simp] instance {α β : Type} : HJoin (α → Prop) (α → β) (β → Prop) where
  join := fun l r b ↦ ∃ a : α, l a ∧ r a = b

@[reducible, simp] instance {α β : Type} : HJoin (Set α) (α → β) (β → Prop) where
  join := fun l r b ↦ ∃ a : α, l a ∧ r a = b

@[reducible, simp] instance {α β : Type} : HJoin (α → Prop) (α → β → Prop) (β → Prop) where
  join := fun l r b ↦ ∃ a : α, l a ∧ r a b

@[reducible, simp] instance {α β : Type} : HJoin (Set α) (α → β → Prop) (β → Prop) where
  join := fun l r b ↦ ∃ a : α, l a ∧ r a b

@[reducible, simp] instance {α β γ : Type} : HJoin (α → Prop) (α → β → γ → Prop) (β → γ → Prop) where
  join := fun l r b g ↦ ∃ a : α, l a ∧ r a b g

@[reducible, simp] instance {α β γ δ : Type} : HJoin (α → Prop) (α → β → γ → δ → Prop) (β → γ → δ → Prop) where
  join := fun l r b g d ↦ ∃ a : α, l a ∧ r a b g d

@[reducible, simp] instance {α β γ δ ε : Type} : HJoin (α → Prop) (α → β → γ → δ → ε → Prop) (β → γ → δ → ε → Prop) where
  join := fun l r b g d e ↦ ∃ a : α, l a ∧ r a b g d e

/- Cross -/

class HCross (α : Type) (β : Type) (γ : outParam Type) :=
  (cross : α → β → γ)

infix:50 " ×ᶠ " => HCross.cross

instance {α β : Type} : HCross α β (α → β → Prop) where
  cross := fun a b ↦ (a, b)

instance {α β : Type} : HCross α (β → Prop) (α → β → Prop) where
  cross := fun a f a' b ↦ a = a' ∧ f b

instance {α β : Type} : HCross (α → Prop) (β → Prop) (α → β → Prop) where
  cross := fun f g a b ↦ f a ∧ g b

-- TODO: Cross with other arities?

-- Binops

instance {α β : Type} : Union (α → β → Prop) where
  union := fun f g ↦ fun a b ↦ f a b ∨ g a b

instance {α : Type} [u : Union (Set α)] : Union (α → Prop) where
  union := u.union

instance {α β : Type} : Inter (α → β → Prop) where
  inter := fun f g ↦ fun a b ↦ f a b ∧ g a b

  instance {α : Type} [i : Inter (Set α)] : Inter (α → Prop) where
  inter := i.inter

prefix:60 "^" => Relation.TransGen
prefix:60 "*" => Relation.ReflTransGen

class Card (α : Type) :=
  (card : α → ℤ)

prefix:60 "#" => Card.card

noncomputable instance : Card (Set α) where
  card := (Set.ncard .)

noncomputable instance {α : Type} : Card (α → Prop) where
  card := (Set.ncard .)

noncomputable instance : Card (α) where
  card := fun _ ↦ 1

instance [f: Fintype α] : CoeDep Type (α : Type) (Set α) where
  coe := (f.elems : Set α)

instance [f: Fintype α] : CoeDep Type (α : Type) (α → Prop) where
  coe := (f.elems : Set α)

instance [f: Fintype α] : CoeDep Type (α : Type) (Finset α) where
  coe := f.elems

instance : Coe α α where
  coe := (.)

end Forge
