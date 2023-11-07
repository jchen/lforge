import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Lforge.Utils
set_option autoImplicit false

opaque Node : Type
@[instance]
axiom finite_node : Fintype Node

opaque next : Node → Node → Prop
axiom one_next : FieldQuantifier.one next

def no_cycle : Prop :=
  ∀ n : Node, ¬ Relation.TransGen next n n

def some_node : Prop :=
  ∃ _ : Node, True

noncomputable def next_fn : Node → Node :=
  by
    intro n
    exact Classical.choose (one_next n)

theorem next_fn_next : ∀ n₁ n₂ : Node, next n₁ n₂ ↔ next_fn n₁ = n₂ :=
  sorry

theorem test_expect_1 : some_node ∧ no_cycle → False :=
  by
    intro hsnanc
    cases' hsnanc
      with hsn hnc
    cases' hsn
      with n ht
    let c := Fintype.card Node
    let nodes_idx := Finset.range (c + 1)
    have hlc : finite_node.elems.card < nodes_idx.card :=
      by
        rw [Finset.card_range]
        exact Nat.lt_succ_self c
    have h_next_in_node :
      ∀ k : ℕ, k ∈ nodes_idx → next_fn^[k] n ∈ finite_node.elems :=
      by
        intro k _
        exact Fintype.complete (next_fn^[k] n)
    have h_some_repeat_node :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlc h_next_in_node
    rcases h_some_repeat_node
      with ⟨k, _, k', _, hknekp, hnkenk'⟩
    wlog kltkp : k < k'
    sorry
    have hnknc := hnc (next_fn^[k] n)
    have h_n_reachable_n : Relation.TransGen next (next_fn^[k] n) (next_fn^[k] n) :=
      by
        nth_rewrite 2 [hnkenk']
        induction k with
        | zero =>
          rw [Function.iterate_zero]
          rw [id]
          rw [←Iff.mp (next_fn_next (next_fn^[k'-1] n) n)]
          sorry
          sorry
        | succ k' ih => sorry
    contradiction
