import Mathlib.Tactic
import Lforge

instance [f: Fintype α] : CoeDep Type (α : Type) (Finset α) where
  coe := f.elems

sig S {
  a: one Int
}

@[instance] axiom inhabited_s : Inhabited S
@[instance] axiom finset_s : Fintype S

#check (S : Finset S)
#reduce (S : Finset S)

def summation {α : Type} (s : Finset α) : Int := Finset.sum s (fun _ => 0)

noncomputable opaque n1 : S
noncomputable opaque n2 : S

def set_s := ({n1, n2} : Set S)

#check (S : Finset S)

#synth AddCommMonoid ℤ

#check @Finset.sum ℤ S Int.instAddCommMonoidInt S (fun _ => 0)

-- #synth CoeDep Type S (Finset S)

noncomputable instance : Coe S (Finset S) where
  coe := λ _ ↦ finset_s.elems

-- #check Finset.sum S (fun _ => 1)

-- structure Adder where
--   howMuch : Nat

-- def add5 : Adder := ⟨5⟩

-- instance : CoeFun Adder (fun _ => Nat → Nat) where
--   coe a := (· + a.howMuch)

-- noncomputable instance : Coe Adder ℕ where
--   coe _ := 0

-- #check add5 add5
