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

#check ExistsUnique
#check Exists.choose

noncomputable def ExistsUnique.choose {α} (P : α → Prop) (h : ∃! x, P x) : α :=
h.exists.choose

theorem ExistsUnique.choose_spec {α} (P : α → Prop) (h : ∃! x, P x) :
  P h.choose :=
h.exists.choose_spec

theorem ExistsUnique.choose_unique {α} (P : α → Prop) (h : ∃! x, P x) :
  ∀ y, P y → y = h.choose :=
fun _ hy => ExistsUnique.unique h hy h.choose_spec

noncomputable def next_fn : Node → Node :=
λ n => ExistsUnique.choose _ (one_next n)


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
      with ⟨k, left, k', left', hknekp, hnkenk'⟩
    wlog kltkp : k < k'
    { apply this hnc n ht hlc h_next_in_node k' ‹k' ∈ nodes_idx› k ‹k ∈ nodes_idx›  hknekp.symm hnkenk'.symm
      apply lt_of_le_of_ne (le_of_not_gt kltkp) hknekp.symm }
    have hnknc := hnc (next_fn^[k] n)
    have h_n_reachable_n : Relation.TransGen next (next_fn^[k] n) (next_fn^[k] n) :=
      by
        nth_rewrite 2 [hnkenk']
        have : ∃ i, k' = k + i + 1 := Nat.exists_eq_add_of_lt (by linarith)
        cases' this with i hi
        rw [add_assoc] at hi
        subst hi
        clear left' hknekp hnkenk'
        induction i with
        | zero =>
          simp
          constructor
          rw [next_fn_next]
          exact (Function.iterate_succ_apply' next_fn k n).symm

        | succ i' ih =>
          apply Relation.TransGen.trans
          { apply ih
            linarith }
          constructor
          rw [next_fn_next]
          simp [Nat.succ_eq_add_one]
          exact (Function.iterate_succ_apply' next_fn (Nat.add k (Nat.add (i' + 1) 0)) n).symm
    contradiction
