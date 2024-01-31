import Lean
open Lean Elab Meta Command Term System
set_option autoImplicit false

/-
The Forge CST that gives us objects that represent all syntactically
valid Forge programs. A program is a list of sigs, predicates, and functions.
Sigs contain fields, predicates contain formulas, and functions contain expressions.
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

declare_syntax_cat f_sig_multiplicity
syntax "one" : f_sig_multiplicity
syntax "lone" : f_sig_multiplicity
syntax "abstract" : f_sig_multiplicity

def Sig.Multiplicity.of_syntax (stx : TSyntax `f_sig_multiplicity) : MetaM Sig.Multiplicity :=
  match stx with
  | `(f_sig_multiplicity| one) => return .one stx
  | `(f_sig_multiplicity| lone) => return .lone stx
  | `(f_sig_multiplicity| abstract) => return .abstract stx
  | _ => throwUnsupportedSyntax

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

declare_syntax_cat f_field_multiplicity
syntax "one" : f_field_multiplicity
syntax "lone" : f_field_multiplicity
syntax "pfunc" : f_field_multiplicity
syntax "func" : f_field_multiplicity
syntax "set" : f_field_multiplicity

def Field.Multiplicity.of_syntax (stx : TSyntax `f_field_multiplicity) : MetaM Field.Multiplicity :=
  match stx with
  | `(f_field_multiplicity| one) => return .one stx
  | `(f_field_multiplicity| lone) => return .lone stx
  | `(f_field_multiplicity| pfunc) => return .pfunc stx
  | `(f_field_multiplicity| func) => return .func stx
  | `(f_field_multiplicity| set) => return .set stx
  | _ => throwUnsupportedSyntax

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

declare_syntax_cat f_field
syntax ident ":" f_field_multiplicity sepBy1(ident, " -> ") : f_field

def Field.of_syntax : TSyntax `f_field → MetaM Field
  | `(f_field| $name:ident : $multiplicity:f_field_multiplicity $type:ident->*) => do
    let multiplicity ← Field.Multiplicity.of_syntax multiplicity
    pure { name := name.getId, name_tok := name, multiplicity := multiplicity, type := type.getElems.toList.map (λ i ↦ i.getId) }
  | _ => throwUnsupportedSyntax

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

declare_syntax_cat f_sig
syntax f_sig_multiplicity ? "sig" ident "{" f_field,* "}" : f_sig
syntax f_sig_multiplicity ? "sig" ident "extends" ident "{" f_field,* "}" : f_sig

def Sig.of_syntax : TSyntax `f_sig → MetaM Sig
  | `(f_sig| $quantifier:f_sig_multiplicity ? sig $name:ident { $fields:f_field,* }) => do
    let quantifier ← match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => pure .unquantified
    let fields ← fields.getElems.toList.mapM Field.of_syntax
    pure { quantifier := quantifier, name := name.getId, name_tok := name, ancestor := none, fields := fields }
  | `(f_sig| $quantifier:f_sig_multiplicity ? sig $name:ident extends $ancestor:ident { $fields:f_field,* }) => do
    let quantifier ← match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => pure .unquantified
    let fields ← fields.getElems.toList.mapM Field.of_syntax
    pure { quantifier := quantifier, name := name.getId, name_tok := name, ancestor := some ancestor.getId, fields := fields }
  | _ => throwUnsupportedSyntax

-- We need to define both here because of mutually-recursive definitions
declare_syntax_cat f_fmla
declare_syntax_cat f_expr

declare_syntax_cat f_args
declare_syntax_cat f_arg

-- argument
syntax ident,+ ":" f_expr : f_arg
-- arguments
syntax f_arg,* : f_args

namespace Formula

inductive UnOp where
  /-- Logical negation on a formula. Produces `¬ <fmla>`. -/
  | not
  deriving Repr, Inhabited

declare_syntax_cat f_fmla_unop
syntax "!" : f_fmla_unop
syntax "not " : f_fmla_unop

def UnOp.of_syntax : TSyntax `f_fmla_unop → MetaM UnOp
  | `(f_fmla_unop| !)
  | `(f_fmla_unop| not) => return .not
  | _ => throwUnsupportedSyntax

syntax f_fmla_unop f_fmla : f_fmla

inductive BinOp where
  /-- Logical conjunction. Produces `<fmla-a> ∧ <fmla-b>`. -/
  | and
  /-- Logical disjunction. Produces `<fmla-a> ∨ <fmla-b>`. -/
  | or
  /-- Logical implication. Produces `<fmla-a> → <fmla-b>`. -/
  | implies
  /-- Logical bijection. Produces `<fmla-a> ↔ <fmla-b>`. -/
  | iff
  deriving Repr, Inhabited

declare_syntax_cat f_fmla_binop
syntax "&&" : f_fmla_binop
syntax "and" : f_fmla_binop
syntax "||" : f_fmla_binop
syntax "or" : f_fmla_binop
syntax "=>" : f_fmla_binop
syntax "implies" : f_fmla_binop
syntax "<=>" : f_fmla_binop
syntax "iff" : f_fmla_binop

def BinOp.of_syntax : TSyntax `f_fmla_binop → MetaM BinOp
  | `(f_fmla_binop| &&)
  | `(f_fmla_binop| and) => return .and
  | `(f_fmla_binop| ||)
  | `(f_fmla_binop| or) => return .or
  | `(f_fmla_binop| =>)
  | `(f_fmla_binop| implies) => return .implies
  | `(f_fmla_binop| <=>)
  | `(f_fmla_binop| iff) => return .iff
  | _ => throwUnsupportedSyntax

syntax f_fmla f_fmla_binop f_fmla : f_fmla

/--
Unary operators on Expressions that produce Formulas.

These quantify over expressions and count them.
-/
inductive ExprUnOp where
  /-- The expression is not empty. Produces `ExprQuantifier.one <expr>`. -/
  | some
  /-- The expression is empty. Produces `ExprQuantifier.no <expr>`. -/
  | no
  /-- The expression has at most one element. Produces `ExprQuantifier.lone <expr>`. -/
  | lone
  /-- The expression has exactly one element. Produces `ExprQuantifier.one <expr>`. -/
  | one
  deriving Repr, Inhabited

declare_syntax_cat f_fmla_of_expr_unop
syntax "some" : f_fmla_of_expr_unop
syntax "no" : f_fmla_of_expr_unop
syntax "lone" : f_fmla_of_expr_unop
syntax "one" : f_fmla_of_expr_unop

def ExprUnOp.of_syntax : TSyntax `f_fmla_of_expr_unop → MetaM ExprUnOp
  | `(f_fmla_of_expr_unop| some) => return .some
  | `(f_fmla_of_expr_unop| no) => return .no
  | `(f_fmla_of_expr_unop| lone) => return .lone
  | `(f_fmla_of_expr_unop| one) => return .one
  | _ => throwUnsupportedSyntax

syntax f_fmla_of_expr_unop f_expr : f_fmla

/--
Binary operators on Expressions that produce Formulas.

These compare two expressions.
-/
inductive ExprBinOp where
  /-- The first expression is a subset of the second. Produces `ExprCmp.subset <expr-a> <expr-b>`. -/
  | in
  /-- The two expressions are equal. Produces `ExprCmp.eq <expr-a> <expr-b>`. -/
  | eq
  /-- The two expressions are not equal. Produces `¬ ExprCmp.eq <expr-a> <expr-b>`. -/
  | neq
  deriving Repr, Inhabited

declare_syntax_cat f_fmla_of_expr_binop
syntax "in" : f_fmla_of_expr_binop
syntax "=" : f_fmla_of_expr_binop
syntax "!=" : f_fmla_of_expr_binop

def ExprBinOp.of_syntax : TSyntax `f_fmla_of_expr_binop → MetaM ExprBinOp
  | `(f_fmla_of_expr_binop| in) => return .in
  | `(f_fmla_of_expr_binop| =) => return .eq
  | `(f_fmla_of_expr_binop| !=) => return .neq
  | _ => throwUnsupportedSyntax

syntax f_expr f_fmla_of_expr_binop f_expr : f_fmla

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
inductive Quantifier where
  | no
  | lone
  | one
  | some
  | all
  deriving Repr, Inhabited

declare_syntax_cat f_fmla_quantifier
syntax "no" : f_fmla_quantifier
syntax "lone" : f_fmla_quantifier
syntax "one" : f_fmla_quantifier
syntax "some" : f_fmla_quantifier
syntax "all" : f_fmla_quantifier

def Quantifier.of_syntax : TSyntax `f_fmla_quantifier → MetaM Quantifier
  | `(f_fmla_quantifier| no) => return .no
  | `(f_fmla_quantifier| lone) => return .lone
  | `(f_fmla_quantifier| one) => return .one
  | `(f_fmla_quantifier| some) => return .some
  | `(f_fmla_quantifier| all) => return .all
  | _ => throwUnsupportedSyntax

syntax f_fmla_quantifier f_args "|" "{" f_fmla "}" : f_fmla
syntax f_fmla_quantifier f_args "|" f_fmla : f_fmla

/-
Everything else
-/

-- implies-else
syntax f_fmla "=>" f_fmla "else" f_fmla : f_fmla
syntax f_fmla "implies" f_fmla "else" f_fmla : f_fmla

-- boolean literals
syntax "true" : f_fmla
syntax "false" : f_fmla

-- predicate application
syntax ident "[" f_expr,* "]" : f_fmla
syntax ident : f_fmla

-- parens
syntax "(" f_fmla ")" : f_fmla
syntax "{" f_fmla "}" : f_fmla

end Formula

namespace Expression

inductive UnOp where
  | transpose
  | transitive_closure
  | reflexive_transitive_closure
  deriving Repr, Inhabited

declare_syntax_cat f_expr_unop
syntax "~" : f_expr_unop
syntax "^" : f_expr_unop
syntax "*" : f_expr_unop

def UnOp.of_syntax : TSyntax `f_expr_unop → MetaM UnOp
  | `(f_expr_unop| ~) => return .transpose
  | `(f_expr_unop| ^) => return .transitive_closure
  | `(f_expr_unop| *) => return .reflexive_transitive_closure
  | _ => throwUnsupportedSyntax

syntax f_expr_unop f_expr : f_expr

inductive BinOp where
  | union
  | set_difference
  | intersection
  | join
  | cross
  deriving Repr, Inhabited

declare_syntax_cat f_expr_binop
syntax "+" : f_expr_binop
syntax "-" : f_expr_binop
syntax "&" : f_expr_binop
syntax "." : f_expr_binop
syntax "->" : f_expr_binop

def BinOp.of_syntax : TSyntax `f_expr_binop → MetaM BinOp
  | `(f_expr_binop| +) => return .union
  | `(f_expr_binop| -) => return .set_difference
  | `(f_expr_binop| &) => return .intersection
  | `(f_expr_binop| .) => return .join
  | `(f_expr_binop| ->) => return .cross
  | _ => throwUnsupportedSyntax

syntax f_expr f_expr_binop f_expr : f_expr

/-
Everything else
-/
-- if-then-else
syntax "if" f_fmla "then" f_expr "else" f_expr : f_expr
-- set comprehension
syntax "{" f_args "|" f_fmla "}" : f_expr
-- app
syntax f_expr "[" f_expr,* "]" : f_expr
-- literal
syntax ident : f_expr
-- let
syntax "let" ident "=" f_expr "|" f_expr : f_expr
-- parens
syntax "(" f_expr ")" : f_expr

end Expression

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

    /-- Quantifiers
       Quantifies `var` over `expr` and binds `var` in `fmla` -/
    -- Exists and satisfies property <fmla>
    | quantifier (quantification : Formula.Quantifier) (vars : List (Symbol × Expression)) (fmla : Formula) (tok : Syntax)

    /-- Predicate applications -/
    | app (pred_name : Symbol) (args : List Expression) (tok : Syntax)
    | true
    | false
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
    deriving Repr, Inhabited
end

mutual
  partial def Arguments.one_of_syntax : TSyntax `f_arg → MetaM (List (Symbol × Expression))
    | `(f_arg| $names:ident,* : $expr:f_expr) =>
      names.getElems.toList.mapM (λ name ↦ do pure (name.getId, ← Expression.of_syntax expr))
    | _ => throwUnsupportedSyntax

  partial def Arguments.of_syntax : TSyntax `f_args → MetaM (List (Symbol × Expression))
    | `(f_args| $args:f_arg,* ) => do
      let lists ← args.getElems.toList.mapM Arguments.one_of_syntax
      return lists.join
    | _ => throwUnsupportedSyntax

  partial def Formula.of_syntax (stx : TSyntax `f_fmla) : MetaM Formula :=
    match stx with
    | `(f_fmla| $unop:f_fmla_unop $fmla:f_fmla) =>
      return Formula.unop (← Formula.UnOp.of_syntax unop) (← Formula.of_syntax fmla) stx
    | `(f_fmla| $fmla_a:f_fmla $binop:f_fmla_binop $fmla_b:f_fmla) =>
      return Formula.binop (← Formula.BinOp.of_syntax binop) (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
    | `(f_fmla| $fmla_a:f_fmla => $fmla_b:f_fmla else $fmla_c:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla implies $fmla_b:f_fmla else $fmla_c:f_fmla) =>
      return Formula.implies_else (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) (← Formula.of_syntax fmla_c) stx
    | `(f_fmla| $unop:f_fmla_of_expr_unop $expr_b:f_expr) =>
      return Formula.expr_unop (← Formula.ExprUnOp.of_syntax unop) (← Expression.of_syntax expr_b) stx
    | `(f_fmla| $expr_a:f_expr $binop:f_fmla_of_expr_binop $expr_b:f_expr) =>
      return Formula.expr_binop (← Formula.ExprBinOp.of_syntax binop) (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | { $fmla:f_fmla })
    | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | $fmla:f_fmla ) => do
      let quantification ← Formula.Quantifier.of_syntax quantifier
      return Formula.quantifier quantification (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
    -- single predicate
    | `(f_fmla| $name:ident ) => do
      return Formula.app name.getId [] stx
    | `(f_fmla| $name:ident [ $expr,* ]) => do
      return Formula.app name.getId (← expr.getElems.toList.mapM Expression.of_syntax) stx
    | `(f_fmla| ( $fmla:f_fmla )) => return (← Formula.of_syntax fmla)
    | `(f_fmla| { $fmla:f_fmla }) => return (← Formula.of_syntax fmla)
    | `(f_fmla| true) => return Formula.true
    | `(f_fmla| false) => return Formula.false
    | _ => throwUnsupportedSyntax

  partial def Expression.of_syntax (stx : TSyntax `f_expr) : MetaM Expression :=
    match stx with
    | `(f_expr| $unop:f_expr_unop $expr:f_expr) =>
      return Expression.unop (← Expression.UnOp.of_syntax unop) (← Expression.of_syntax expr) stx
    | `(f_expr| $expr_a:f_expr $binop:f_expr_binop $expr_b:f_expr) =>
      return Expression.binop (← Expression.BinOp.of_syntax binop) (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_expr| if $fmla:f_fmla then $expr_a:f_expr else $expr_b:f_expr) =>
      return Expression.if_then_else (← Formula.of_syntax fmla) (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_expr| { $args:f_args | $fmla:f_fmla }) =>
      return Expression.set_comprehension (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
    | `(f_expr| $expr_a:f_expr [ $expr,* ]) =>
      return Expression.app (← Expression.of_syntax expr_a) (← expr.getElems.toList.mapM Expression.of_syntax) stx
    | `(f_expr| $name:ident) => return Expression.literal name.getId stx
    | `(f_expr| let $id:ident = $expr_a:f_expr | $expr_b:f_expr) =>
      return Expression.let id.getId (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_expr| ( $expr:f_expr )) => return (← Expression.of_syntax expr)
    | _ => throwUnsupportedSyntax
end

structure Predicate where
  name : Symbol
  name_tok : Syntax
  args : List (Symbol × Expression) -- (name, type) pairs
  body : Formula -- with args bound
  deriving Repr, Inhabited

declare_syntax_cat f_pred
declare_syntax_cat f_pred_args
syntax "[" f_args "]" : f_pred_args
syntax "pred" ident f_pred_args ? "{" f_fmla* "}" : f_pred

def Predicate.of_syntax (stx : TSyntax `f_pred) : MetaM Predicate :=
  match stx with
  | `(f_pred| pred $name:ident { $fmla:f_fmla* }) => do
    let args := []
    -- Join fmla list with `ands`. No base case, if empty, then true. Else one element.
    let body ← ( match fmla.toList with
    | [] => return Formula.true
    | fmla => do
      let fmlas_rev := fmla.reverse
      let init ← Formula.of_syntax fmlas_rev.head!
      fmlas_rev.tail!.foldlM (λ acc elt ↦ do
        return .binop .and (← Formula.of_syntax elt) acc stx) init )
    return { name := name.getId, name_tok := name, args := args, body := body }
  | `(f_pred| pred $name:ident [ $args:f_args ] { $fmla:f_fmla* }) => do
    let args ← Arguments.of_syntax args
    -- Join fmla list with `ands`. No base case, if empty, then true. Else one element.
    let body ← ( match fmla.toList with
    | [] => return Formula.true
    | fmla => do
      let fmlas_rev := fmla.reverse
      let init ← Formula.of_syntax fmlas_rev.head!
      fmlas_rev.tail!.foldlM (λ acc elt ↦ do
        return .binop .and (← Formula.of_syntax elt) acc stx) init )
    return { name := name.getId, name_tok := name, args := args, body := body }
  | _ => throwUnsupportedSyntax

structure Function where
  name : Symbol
  name_tok : Syntax
  args : List (Symbol × Expression) -- (name, type) pairs
  result_type : Expression -- ignored in Forge but we'll check
  body : Expression -- with args bound
  deriving Repr, Inhabited

declare_syntax_cat f_fun

syntax "fun" ident "[" f_args "]" ":" (f_field_multiplicity)? f_expr "{" f_expr "}" : f_fun

-- TODO: Functions are not working
def Function.of_syntax : TSyntax `f_fun → MetaM Function
  | `(f_fun| fun $name:ident [ $args:f_args ] : $_? $result_type:f_expr { $expr:f_expr }) => do
    let args ← Arguments.of_syntax args
    let result_type ← Expression.of_syntax result_type
    let body ← Expression.of_syntax expr
    return { name := name.getId, name_tok := name, args := args, result_type := result_type, body := body }
  | _ => throwUnsupportedSyntax

structure ForgeModel where
  -- All in reverse order!
  sigs : List Sig
  predicates : List Predicate
  functions : List Function
  deriving Repr, Inhabited

declare_syntax_cat f_command
syntax f_sig : f_command
syntax f_pred : f_command
syntax f_fun : f_command

declare_syntax_cat f_program
syntax f_command* : f_program

def ForgeModel.of_syntax : TSyntax `f_program → MetaM ForgeModel
  | `(f_program| $terms:f_command* ) => do
    terms.foldlM (λ acc term ↦
        match term with
        | `(f_command| $s:f_sig) => do
          pure { acc with sigs := (← Sig.of_syntax s) :: acc.sigs}
        | `(f_command| $p:f_pred) => do
          pure { acc with predicates := (← Predicate.of_syntax p) :: acc.predicates }
        | `(f_command| $f:f_fun) => do
          pure { acc with functions := (← Function.of_syntax f) :: acc.functions }
        | _ => throwUnsupportedSyntax
      ) { sigs := [], predicates := [], functions := [] : ForgeModel}
  | _ => throwUnsupportedSyntax

end ForgeSyntax
