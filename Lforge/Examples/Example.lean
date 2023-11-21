import Mathlib.Data.Set.Basic
import Mathlib.Tactic
set_option autoImplicit false

opaque Pet : Type

opaque Person : Type
instance instSingletonPerson : Singleton Person (Set Person) := ⟨Set.singleton⟩

opaque owner : Pet → Person → Prop
axiom one_owner : ∀ pet : Pet, ∃! person : Person, owner pet person

opaque pets : Person → Pet → Prop

opaque friends : Person → Person → Prop

def owner_owns_pet : Prop :=
  ∀ p : Person, ∀ pet : Pet, pets p pet ↔ owner pet p

#check ∀ p : Person, ∀ pet : Pet, Set.union (Set.singleton p) (owner pet)
#check ∀ p : Person, ∀ pet : Pet, Set.union (Set.singleton p) (owner pet)

#check ({1, 2, 3} : Set ℕ) = {1, 2, 3}

def one_friend_owns_one_pet (p : Person) : Prop :=
  ∃! fs : Person, friends p fs ∧ ∃! pet : Pet, pets fs pet

def some_friend_owns_a_pet (p : Person) : Prop :=
  ∃ fs : Person, friends p fs ∧ ∃ pet : Pet, pets fs pet

def friends_pets (p : Person) : Pet → Prop :=
  { pet | ∃ fs : Person, friends p fs ∧ pets fs pet }

def check : ∀ p : Person, one_friend_owns_one_pet p → some_friend_owns_a_pet p :=
  by
    intro p hofoop
    rw [one_friend_owns_one_pet] at hofoop
    rw [some_friend_owns_a_pet]
    rcases ExistsUnique.exists hofoop
      with ⟨p1, left, right⟩
    apply Exists.intro p1
    exact And.intro left (ExistsUnique.exists right)

set_option pp.all true

#check ∃ p : Person, ∀ pet : Pet, owner pet p
#reduce ∃ p : Person, ∃ pet : Pet, owner pet p

#print Lean.toExpr

#check Int
