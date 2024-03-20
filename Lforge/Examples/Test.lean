import Mathlib.Tactic
-- import Mathlib.Logic.Relation
-- import Mathlib.Data.Set.Card
set_option autoImplicit false


#check ({1, 2, 3} : Set ℤ)
#check Finset.sum {1, 2, 3} (λ x ↦ x)
