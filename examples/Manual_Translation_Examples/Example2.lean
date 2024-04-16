import Mathlib.Tactic
set_option autoImplicit false

----- HELPERS -----

def abstract_sig (a : Type) := IsEmpty a

def one_sig (a : Type) := Singleton a

def lone_sig (a : Type) := Subsingleton a

def one_set {a : Type} (f : a → Prop) :=
  ∃! x : a, f = Set.singleton x

def no_set {a : Type} (f : a → Prop) :=
  (∅ : Set a) = f

def lone_set {a : Type} (f : a → Prop) :=
  one_set f ∨ no_set f

def one_field {α : Type} {β : Type} (f : α → β → Prop) :=
  ∀ a : α, one_set (f a ·)

def no_field {α : Type} {β : Type} (f : α → β → Prop) :=
  ∀ a : α, no_set (f a ·)

def lone_field {α : Type} {β : Type} (f : α → β → Prop) :=
  ∀ a : α, lone_set (f a ·)

----- SIGS -----


opaque Student : Type
-- @[instance] axiom inhabited_student : Inhabited Student

opaque Undergrad : Type

-- Coercion method

@[instance] axiom cus : Coe Undergrad Student

def IsUndergrad (s : Student) : Prop := ∃ x : Undergrad, x = s

-- Subtype method

opaque IsGrad : Student → Prop
@[reducible] def Grad : Type :=
  { s : Student // IsGrad s }

@[instance] axiom inhabited_grad : Inhabited Grad

opaque IsSpecialGrad : Grad → Prop
@[reducible] def SpecialGrad : Type :=
  { s : Grad // IsSpecialGrad s }

@[instance] axiom inhabited_special_grad : Inhabited SpecialGrad

noncomputable opaque a : SpecialGrad
#check (a : Student)

noncomputable def test : Student := a

axiom abstract_student : ∀ s : Student, IsUndergrad s ∨ IsGrad s

-- instance Coe Undergrad Student :=

-- axiom special_grad_of_grad : Grad → SpecialGrad

-- axiom one_specialgrad : one_sig SpecialGrad

-- def Student : Type := Undergrad ⊕ Grad

theorem t : Coe Grad SpecialGrad := by
  done

-- opaque Student : Type

-- opaque IsUndergrad : Student → Prop
-- def Undergrad : Type :=
--   { s : Student // IsUndergrad s }

-- opaque Student : Type

-- -- Base student, only the root node of the tree, is abstract
-- opaque Base_Student : Type
-- axiom abstract_base_student : abstract_sig Base_Student
-- axiom student_of_base_student : Base_Student → Student

-- opaque Undergrad : Type
-- axiom student_of_undergrad : Undergrad → Student
-- -- TODO: Is this casting correct?

-- opaque Grad : Type
-- axiom student_of_grad : Grad → Student

-- opaque SpecialGrad : Type
-- axiom grad_of_specialgrad : SpecialGrad → Grad

opaque Mascot : Type

opaque Year : Type

opaque Class : Type

----- FIELDS -----
opaque mascot : Year → Mascot → Prop
axiom one_mascot : one_field mascot

opaque next : Year → Year → Prop
axiom lone_next : lone_field next

opaque students : Class → Student → Prop

opaque pairs : Class → Student → Student → Prop
axiom one_image_student : ∀ c : Class, one_field (pairs c · ·)
axiom one_preimage_student : ∀ c : Class, ∀ s2 : Student, one_set (pairs c · s2)

opaque buddies : Class → (Student → (Student → Prop))
opaque buddies' : Class → Student × Student → Prop
axiom func_buddies : ∀ c : Class, one_field (buddies c · ·)

opaque best_friend : Class → Student → Student → Prop
axiom pfunc_best_friend : ∀ c : Class, lone_field (best_friend c · ·)

----- PREDS -----

def buddies_no_cycles : Prop :=
  ∀ c : Class, ¬∃ x : Student, Relation.TransGen (buddies c) x x

def no_self_buddies : Prop :=
  ∀ c : Class, ¬∃ x : Student, buddies c x x

def some_student : Prop :=
  ∃ _ : Student, true

def some_class : Prop :=
  ∃ _ : Class, true

theorem test_expect_1 : some_class ∧ some_student ∧ buddies_no_cycles ∧ no_self_buddies → False :=
  by
    intro h
    rcases h
      with ⟨hsc, hss, hbnc, hnsb⟩
    cases' hsc
      with c _
    have h_class_no_cycle := hbnc c
    sorry
    -- I believe this is unprovable unless we have axioms that state finiteness??

#check Function.curry
#check Function.uncurry
