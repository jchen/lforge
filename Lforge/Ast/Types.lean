import Lean
open Lean Elab Meta Command Term System
set_option autoImplicit false

/-
This file contains all the types and structs that represent a Forge program.
-/

namespace ForgeSyntax

/-- A `Symbol` is a Lean name representing sigs, predicates, and functions in Forge. -/
def Symbol := Name deriving Repr, Inhabited, ToMessageData, DecidableEq

/--
A `Sig.Multiplicity` corresponds to the annotation of the multiplicity of a sig. For example, in
```
abstract sig Ingredient {}
one sig Carrot extends Ingredient {}
sig TimeStep {}
```
`abstract` and `one` correspond to multiplicities on `Ingredient` and `Carrot` respectively, and `TimeStep` is unquantified.
-/
inductive Sig.Multiplicity where
  /--
  `one` states that there is always exactly one object of that sig.
  `tok` points to the concrete syntax object that represents this multiplicity annotation.
  -/
  | one (tok : Syntax)
  /-- `lone` there is never more than one object of this sig. That is, that there are zero or one. -/
  | lone (tok : Syntax)
  /-- `abstract` states that any object of this sig must also be a member of some child sig. -/
  | abstract (tok : Syntax)
  /--
  `unquantified` means that there are no restrictions on the cardinality of this sig.
  A Forge sig without a multiplicity annotation is unquantified by default.
  -/
  | unquantified
  deriving Repr, Inhabited

/--
A `Field.Multiplicity` corresponds to the annotation of the multiplicity of a field. For example, in
```
sig Recipe {
  ingredients: set Ingredient,
  main_ingredient: one Ingredient
}
```
`set` and `one` correspond to multiplicities on fields `ingredients` and `main_ingredient` respectively.
-/
inductive Field.Multiplicity where
  /--
  There is a single object of this field. On an arrow type `A → B`,
  this means that this relation contains exactly one pair of `A × B`.
  -/
  | one (tok : Syntax)
  /--
  There is at most one object of this field.
  -/
  | lone (tok : Syntax)
  /--
  The relation **must** have arity 2. On relations from `A → B`, `pfunc` states that the relation is a partial function.
  -/
  | pfunc (tok : Syntax)
  /--
  The relation **must** have arity 2. On relations from `A → B`, `func` states that the relation is a total function.
  -/
  | func (tok : Syntax)
  /--
  `set` states that the relation is a set, this does not produce any additional quantifications or restraints.
  -/
  | set (tok : Syntax)
  deriving Repr, Inhabited

/--
A `Field` corresponds to a field in a sig.
-/
structure Field where
  name : Symbol
  /--
  The token that represents the name of the field. This is used for hinting and error reporting.
  -/
  name_tok : Syntax
  multiplicity : Field.Multiplicity
  /--
  The type of the field. If the type is of arity-1, such as `A`, then the type is `[A]`.
  Otherwise, if the type is of arity-n, such as `A → B → C`, then the type is `[A, B, C]` in order.
  -/
  type : List Symbol
  deriving Repr, Inhabited

/--
A `Sig` corresponds to a sig in Forge. In a contiguous block of Forge declarations, `Sig`s are lifted
such that they are defined for all fields that require them.
-/
structure Sig where
  quantifier : Sig.Multiplicity
  name : Symbol
  /--
  The token that represents the name of the sig. This is used for hinting and error reporting.
  -/
  name_tok : Syntax
  ancestor : Option Symbol := none
  fields : List Field
  deriving Repr, Inhabited

inductive Formula.UnOp where
  /-- Logical negation on a formula. Produces `¬ <fmla>`. -/
  | not
  deriving Repr, Inhabited

inductive Formula.BinOp where
  /-- Logical conjunction. Produces `<fmla-a> ∧ <fmla-b>`. -/
  | and
  /-- Logical disjunction. Produces `<fmla-a> ∨ <fmla-b>`. -/
  | or
  /-- Logical implication. Produces `<fmla-a> → <fmla-b>`. -/
  | implies
  /-- Logical bijection. Produces `<fmla-a> ↔ <fmla-b>`. -/
  | iff
  deriving Repr, Inhabited

/--
Unary operators on Expressions that produce Formulas.

These quantify over expressions and count them.
-/
inductive Formula.ExprUnOp where
  /-- The expression is not empty. Produces `ExprQuantifier.one <expr>`. -/
  | some
  /-- The expression is empty. Produces `ExprQuantifier.no <expr>`. -/
  | no
  /-- The expression has at most one element. Produces `ExprQuantifier.lone <expr>`. -/
  | lone
  /-- The expression has exactly one element. Produces `ExprQuantifier.one <expr>`. -/
  | one
  deriving Repr, Inhabited

/--
Binary operators on Expressions that produce Formulas.

These compare two expressions.
-/
inductive Formula.ExprBinOp where
  /-- The first expression is a subset of the second. Produces `ExprCmp.subset <expr-a> <expr-b>`. -/
  | in
  /-- The two expressions are equal. Produces `ExprCmp.eq <expr-a> <expr-b>`. -/
  | eq
  /-- The two expressions are not equal. Produces `¬ ExprCmp.eq <expr-a> <expr-b>`. -/
  | neq
  /- Integer binops -/
  | lt
  | leq
  | gt
  | geq
  deriving Repr, Inhabited

/--
A quantification of the form
```
<quantifier> x : <expr> | <fmla>
```
where `x` is bound in `<fmla>`. If the type of `<expr>` is a direct type, then the quantification is like
```lean
∀ x : <expr>, <fmla>
∃ x : <expr>, <fmla>
∃! x : <expr>, <fmla>
...
```
otherwise will desugar into
```lean
∀ x : <type-of-expr>, x ∈ <expr> → <fmla>
∃ x : <type-of-expr>, x ∈ <expr> ∧ <fmla>
∃! x : <type-of-expr>, x ∈ <expr> ∧ <fmla>
...
```
-/
inductive Formula.Quantifier where
  | no
  | lone
  | one
  | some
  | all
  deriving Repr, Inhabited

inductive Expression.UnOp where
  | transpose
  | transitive_closure
  | reflexive_transitive_closure
  deriving Repr, Inhabited

inductive Expression.BinOp where
  | union
  | set_difference
  | intersection
  | join
  | cross
  deriving Repr, Inhabited

inductive Expression.Integer.Aggregator where
  | sing
  | sum
  | max
  | min
  deriving Repr, Inhabited

inductive Expression.Integer.UnOp where
  | abs
  | sgn
  deriving Repr, Inhabited

inductive Expression.Integer.BinOp where
  | mod
  deriving Repr, Inhabited

inductive Expression.Integer.MulOp where
  | add
  | sub
  | mul
  | div
  deriving Repr, Inhabited

mutual
  /-
  All formulas evaluate to boolean values
  -/
  inductive Formula where
    /- Operators -/
    | unop (op : Formula.UnOp) (fmla : Formula) (tok : Syntax)
    | binop (op : Formula.BinOp) (fmla_a fmla_b : Formula) (tok : Syntax)
    -- if [fmla_a], then [fmla_b], otherwise [fmla_c]
    | implies_else (fmla_a fmla_b fmla_c : Formula) (tok : Syntax)
    /- Cardinality and membership -/
    | expr_unop (op : Formula.ExprUnOp) (expr : Expression) (tok : Syntax)
    | expr_binop (op : Formula.ExprBinOp) (expr_a expr_b : Expression) (tok : Syntax)
    /-- Quantifies `var` over `expr` and binds `var` in `fmla` -/
    | quantifier (quantification : Formula.Quantifier) (vars : List (Symbol × Expression)) (fmla : Formula) (tok : Syntax)
    /-- Predicate applications -/
    | app (pred_name : Symbol) (args : List Expression) (tok : Syntax)
    | let (id : Symbol) (expression : Expression) (body : Formula) (tok : Syntax)
    | true (tok : Syntax)
    | false (tok : Syntax)
    -- /-- integer comparison -/
    -- | cmp (op : Integer.Comparison) (expr_a expr_b : Expression) (tok : Syntax)
    deriving Repr, Inhabited

  inductive Expression where
    | unop (op : Expression.UnOp) (expr : Expression) (tok : Syntax)
    | binop (op : Expression.BinOp) (expr_a expr_b : Expression) (tok : Syntax)
    /-- if `fmla`, then `expr_a`, otherwise `expr_b` -/
    | if_then_else (fmla : Formula) (expr_a expr_b : Expression) (tok : Syntax)
    /-- { [var] | [fmla] }, binds [var] in fmla and includes in set if true -/
    | set_comprehension (vars : List (Symbol × Expression)) (fmla : Formula) (tok : Syntax)
    /-- Function application, also includes sugar for join. -/
    | app (function : Expression) (args : List Expression) (tok : Syntax)
    /-- a literal value, can be sig, relation, or top-level expr (univ, none, iden, etc.) -/
    | literal (value : Symbol) (tok : Syntax)
    | let (id : Symbol) (expression : Expression) (body : Expression) (tok : Syntax)
    /- Integer expressions -/
    /-- Integer literal -/
    | int (val : Int) (tok : Syntax)
    /-- Count of a set -/
    | int.count (expr : Expression) (tok : Syntax)
    /-- Aggregation of a set -/
    | int.agg (agg : Expression.Integer.Aggregator) (expr : Expression) (tok : Syntax)
    /-- Braced sum expression, like `sum <x>: <set> | { ... }`, ensure body is int -/
    | int.sum (binder : Symbol) (expr : Expression) (body : Expression) (tok : Syntax)
    /-- Integer unary operator, like op[a], ensure expr is int -/
    | int.unop (op : Expression.Integer.UnOp) (expr : Expression) (tok : Syntax)
    /-- Integer biinary operator, like op[a, b], ensure exprs are int -/
    | int.binop (op : Expression.Integer.BinOp) (expr_a expr_b : Expression) (tok : Syntax)
    /-- Integer multiple-ary operator, like op[a, b, c, ...], ensure exprs are int -/
    | int.mulop (op : Expression.Integer.MulOp) (exprs : List Expression) (tok : Syntax)
    deriving Repr, Inhabited
end

structure Predicate where
  name : Symbol
  name_tok : Syntax
  args : List (Symbol × Expression) -- (name, type) pairs
  body : Formula -- with args bound
  deriving Repr, Inhabited

structure Function where
  name : Symbol
  name_tok : Syntax
  args : List (Symbol × Expression) -- (name, type) pairs
  result_type : Expression -- ignored in Forge but we'll check
  body : Expression -- with args bound
  deriving Repr, Inhabited

structure ForgeModel where
  -- All in reverse order!
  sigs : List Sig
  predicates : List Predicate
  functions : List Function
  deriving Repr, Inhabited

end ForgeSyntax
