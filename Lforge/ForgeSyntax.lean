/-
Structures that represent the syntax of Forge.
-/
import Lean
open Lean Elab Meta
set_option autoImplicit false

/-
**ForgeSyntax** gives us objects that represent all syntactically valid Forge programs.
A program is a list of sigs, predicates, and functions. Sigs contain fields,
predicates contain formulas, and functions contain expressions.
-/
namespace ForgeSyntax

def Symbol := Name deriving Repr
instance : Inhabited Symbol := inferInstanceAs (Inhabited Name)

inductive Sig.Multiplicity where
  -- there is always exactly one object of that sig
  | one
  -- there is never more than one object of this sig
  | lone
  -- any object of this sig must also be a member of some child sig
  | abstract
  -- unquantified, no restrictions
  | unquantified
  deriving Repr

instance : Inhabited Sig.Multiplicity := ⟨Sig.Multiplicity.unquantified⟩

declare_syntax_cat f_sig_multiplicity
syntax "one" : f_sig_multiplicity
syntax "lone" : f_sig_multiplicity
syntax "abstract" : f_sig_multiplicity

def Sig.Multiplicity.of_syntax : TSyntax `f_sig_multiplicity → Sig.Multiplicity
  | `(f_sig_multiplicity| one) => .one
  | `(f_sig_multiplicity| lone) => .lone
  | `(f_sig_multiplicity| abstract) => .abstract
  | _ => unreachable!

inductive Field.Multiplicity where
  -- only one of
  | one
  -- one or zero of
  | lone
  -- is a -> relation and is a partial function
  | pfunc
  -- is a -> relation and is a total function
  | func
  -- is any set (no constraints on field)
  | set
  deriving Repr

instance : Inhabited Field.Multiplicity := ⟨Field.Multiplicity.set⟩

declare_syntax_cat f_field_multiplicity
syntax "one" : f_field_multiplicity
syntax "lone" : f_field_multiplicity
syntax "pfunc" : f_field_multiplicity
syntax "func" : f_field_multiplicity
syntax "set" : f_field_multiplicity

def Field.Multiplicity.of_syntax : TSyntax `f_field_multiplicity → Field.Multiplicity
  | `(f_field_multiplicity| one) => .one
  | `(f_field_multiplicity| lone) => .lone
  | `(f_field_multiplicity| pfunc) => .pfunc
  | `(f_field_multiplicity| func) => .func
  | `(f_field_multiplicity| set) => .set
  | _ => unreachable!

structure Field where
  name : Symbol
  multiplicity : Field.Multiplicity
  type : List Symbol
  deriving Repr

instance : Inhabited Field := ⟨{ name := default, multiplicity := default, type := default }⟩

declare_syntax_cat f_field
syntax ident ":" f_field_multiplicity sepBy1(ident, "->") : f_field

def Field.of_syntax : TSyntax `f_field → Field
  | `(f_field| $name:ident : $multiplicity:f_field_multiplicity $type:ident->*) =>
    let multiplicity := Field.Multiplicity.of_syntax multiplicity
    { name := name.getId, multiplicity := multiplicity, type := type.getElems.toList.map (λ i ↦ i.getId) }
  | _ => unreachable!

structure Sig where
  quantifier : Sig.Multiplicity
  name : Symbol
  ancestor : Option Symbol := none
  fields : List Field
  deriving Repr

instance : Inhabited Sig := ⟨{ quantifier := default, name := default, ancestor := default, fields := default }⟩

declare_syntax_cat f_sig
syntax f_sig_multiplicity ? "sig" ident "{" f_field,+ "}" : f_sig
syntax f_sig_multiplicity ? "sig" ident "extends" ident "{" f_field,+ "}" : f_sig

def Sig.of_syntax : TSyntax `f_sig → Sig
  | `(f_sig| $quantifier:f_sig_multiplicity ? sig $name:ident { $fields:f_field,* }) =>
    let quantifier := match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => .unquantified
    let fields := fields.getElems.toList.map .of_syntax
    { quantifier := quantifier, name := name.getId, ancestor := none, fields := fields }
  | `(f_sig| $quantifier:f_sig_multiplicity ? sig $name:ident extends $ancestor:ident { $fields:f_field,* }) =>
    let quantifier := match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => .unquantified
    let fields := fields.getElems.toList.map .of_syntax
    { quantifier := quantifier, name := name.getId, ancestor := some ancestor.getId, fields := fields }
  | _ => unreachable!

-- We need to define both here because of mutually-recursive definitions
declare_syntax_cat f_fmla
declare_syntax_cat f_expr

/-
**Standardized arguments** in both formula app and predicate app.
-/
namespace Arguments
declare_syntax_cat f_args
declare_syntax_cat f_arg

-- argument
syntax ident ":" f_expr : f_arg
-- arguments
syntax f_arg,* : f_args

end Arguments

namespace Formula

inductive UnOp where
  | not
  deriving Repr
instance : Inhabited UnOp := ⟨UnOp.not⟩

declare_syntax_cat f_fmla_unop
syntax "!" : f_fmla_unop
syntax "not " : f_fmla_unop

def UnOp.of_syntax : TSyntax `f_fmla_unop → UnOp
  | `(f_fmla_unop| !)
  | `(f_fmla_unop| not) => .not
  | _ => unreachable!

syntax f_fmla_unop f_fmla : f_fmla

inductive BinOp where
  | and
  | or
  | implies
  | iff
  deriving Repr

instance : Inhabited BinOp := ⟨BinOp.and⟩

declare_syntax_cat f_fmla_binop
syntax "&&" : f_fmla_binop
syntax "and" : f_fmla_binop
syntax "||" : f_fmla_binop
syntax "or" : f_fmla_binop
syntax "=>" : f_fmla_binop
syntax "implies" : f_fmla_binop
syntax "<=>" : f_fmla_binop
syntax "iff" : f_fmla_binop

def BinOp.of_syntax : TSyntax `f_fmla_binop → BinOp
  | `(f_fmla_binop| &&)
  | `(f_fmla_binop| and) => .and
  | `(f_fmla_binop| ||)
  | `(f_fmla_binop| or) => .or
  | `(f_fmla_binop| =>)
  | `(f_fmla_binop| implies) => .implies
  | `(f_fmla_binop| <=>)
  | `(f_fmla_binop| iff) => .iff
  | _ => unreachable!

syntax f_fmla f_fmla_binop f_fmla : f_fmla

inductive ExprUnOp where
  | some
  | all
  | no
  | lone
  | one
  deriving Repr

instance : Inhabited ExprUnOp := ⟨ExprUnOp.some⟩

declare_syntax_cat f_fmla_of_expr_unop
syntax "some" : f_fmla_of_expr_unop
syntax "all" : f_fmla_of_expr_unop
syntax "no" : f_fmla_of_expr_unop
syntax "lone" : f_fmla_of_expr_unop
syntax "one" : f_fmla_of_expr_unop

def ExprUnOp.of_syntax : TSyntax `f_fmla_of_expr_unop → ExprUnOp
  | `(f_fmla_of_expr_unop| some) => .some
  | `(f_fmla_of_expr_unop| all) => .all
  | `(f_fmla_of_expr_unop| no) => .no
  | `(f_fmla_of_expr_unop| lone) => .lone
  | `(f_fmla_of_expr_unop| one) => .one
  | _ => unreachable!

syntax f_fmla_of_expr_unop f_expr : f_fmla

inductive ExprBinOp where
  | in
  | eq
  | neq
  deriving Repr

instance : Inhabited ExprBinOp := ⟨ExprBinOp.in⟩

declare_syntax_cat f_fmla_of_expr_binop
syntax "in" : f_fmla_of_expr_binop
syntax "=" : f_fmla_of_expr_binop
syntax "!=" : f_fmla_of_expr_binop

def ExprBinOp.of_syntax : TSyntax `f_fmla_of_expr_binop → ExprBinOp
  | `(f_fmla_of_expr_binop| in) => .in
  | `(f_fmla_of_expr_binop| =) => .eq
  | `(f_fmla_of_expr_binop| !=) => .neq
  | _ => unreachable!

syntax f_expr f_fmla_of_expr_binop f_expr : f_fmla

inductive ExprQuantifier where
  | no
  | lone
  | one
  | some
  | all
  deriving Repr

instance : Inhabited ExprQuantifier := ⟨ExprQuantifier.no⟩

declare_syntax_cat f_fmla_quantifier
syntax "no" : f_fmla_quantifier
syntax "lone" : f_fmla_quantifier
syntax "one" : f_fmla_quantifier
syntax "some" : f_fmla_quantifier
syntax "all" : f_fmla_quantifier

def ExprQuantifier.of_syntax : TSyntax `f_fmla_quantifier → ExprQuantifier
  | `(f_fmla_quantifier| no) => .no
  | `(f_fmla_quantifier| lone) => .lone
  | `(f_fmla_quantifier| one) => .one
  | `(f_fmla_quantifier| some) => .some
  | `(f_fmla_quantifier| all) => .all
  | _ => unreachable!

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

end Formula

namespace Expression

inductive UnOp where
  | transpose
  | transitive_closure
  | reflexive_transitive_closure
  deriving Repr

instance : Inhabited UnOp := ⟨UnOp.transpose⟩

declare_syntax_cat f_expr_unop
syntax "~" : f_expr_unop
syntax "^" : f_expr_unop
syntax "*" : f_expr_unop

def UnOp.of_syntax : TSyntax `f_expr_unop → UnOp
  | `(f_expr_unop| ~) => .transpose
  | `(f_expr_unop| ^) => .transitive_closure
  | `(f_expr_unop| *) => .reflexive_transitive_closure
  | _ => unreachable!

syntax f_expr_unop f_expr : f_expr

inductive BinOp where
  | union
  | set_difference
  | intersection
  | join
  | cross
  deriving Repr

instance : Inhabited BinOp := ⟨BinOp.union⟩

declare_syntax_cat f_expr_binop
syntax "+" : f_expr_binop
syntax "-" : f_expr_binop
syntax "&" : f_expr_binop
syntax "." : f_expr_binop
syntax "->" : f_expr_binop

def BinOp.of_syntax : TSyntax `f_expr_binop → BinOp
  | `(f_expr_binop| +) => .union
  | `(f_expr_binop| -) => .set_difference
  | `(f_expr_binop| &) => .intersection
  | `(f_expr_binop| .) => .join
  | `(f_expr_binop| ->) => .cross
  | _ => unreachable!

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

end Expression

mutual
  /-
  All formulas evaluate to boolean values
  -/
  inductive Formula where
    /- Operators -/
    | unop (op : Formula.UnOp) (fmla : Formula)
    | binop (op : Formula.BinOp) (fmla_a fmla_b : Formula)
    -- if [fmla_a], then [fmla_b], otherwise [fmla_c]
    | implies_else (fmla_a fmla_b fmla_c : Formula)

    /- Cardinality and membership -/
    | expr_unop (op : Formula.ExprUnOp) (expr : Expression)
    | expr_binop (op : Formula.ExprBinOp) (expr_a expr_b : Expression)

    /- Quantifiers
       Quantifies [var](s) over [expr](s) and binds [var](s) in [fmla] -/
    -- Exists and satisfies property <fmla>
    | quantifier (quantification : Formula.ExprQuantifier) (vars : List (Symbol × Expression)) (fmla : Formula)

    /- Predicate Applications -/
    | app (pref_name : Symbol) (args : List Expression)
    | true
    | false
    deriving Repr

  inductive Expression where
    | unop (op : Expression.UnOp) (expr : Expression)
    | binop (op : Expression.BinOp) (expr_a expr_b : Expression)
    -- if [fmla], then [expr_a], otherwise [expr_b]
    | if_then_else (fmla : Formula) (expr_a expr_b : Expression)

    -- { [var] | [fmla] }, binds [var](s) in fmla and includes in set if true
    | set_comprehension (vars : List (Symbol × Expression)) (fmla : Formula)

    -- Function application, also includes sugar for join.
    | app (function : Expression) (args : List Expression)
    -- a literal value, can be sig, relation, or top-level expr (univ, none, iden, etc.)
    | literal (value : Symbol)

    | let (id : Symbol) (expression : Expression) (body : Expression)
    deriving Repr
end

instance : Inhabited Formula := ⟨Formula.true⟩
instance : Inhabited Expression := ⟨Expression.literal Name.anonymous⟩

mutual
  def Arguments.one_of_syntax : TSyntax `f_arg → Symbol × Expression
    | `(f_arg| $name:ident : $expr:f_expr) => (name.getId, Expression.of_syntax expr)
    | _ => unreachable!

  def Arguments.of_syntax : TSyntax `f_args → List (Symbol × Expression)
    | `(f_args| $args:f_arg,* ) => args.getElems.toList.map Arguments.one_of_syntax
    | _ => unreachable!

  def Formula.of_syntax : TSyntax `f_fmla → Formula
    | `(f_fmla| $unop:f_fmla_unop $fmla:f_fmla) =>
      Formula.unop (Formula.UnOp.of_syntax unop) (Formula.of_syntax fmla)
    | `(f_fmla| $fmla_a:f_fmla $binop:f_fmla_binop $fmla_b:f_fmla) =>
      Formula.binop (Formula.BinOp.of_syntax binop) (Formula.of_syntax fmla_a) (Formula.of_syntax fmla_b)
    | `(f_fmla| $fmla_a:f_fmla => $fmla_b:f_fmla else $fmla_c:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla implies $fmla_b:f_fmla else $fmla_c:f_fmla) =>
      Formula.implies_else (Formula.of_syntax fmla_a) (Formula.of_syntax fmla_b) (Formula.of_syntax fmla_c)
    | `(f_fmla| $unop:f_fmla_of_expr_unop $expr_b:f_expr) =>
      Formula.expr_unop (Formula.ExprUnOp.of_syntax unop) (Expression.of_syntax expr_b)
    | `(f_fmla| $expr_a:f_expr $binop:f_fmla_of_expr_binop $expr_b:f_expr) =>
      Formula.expr_binop (Formula.ExprBinOp.of_syntax binop) (Expression.of_syntax expr_a) (Expression.of_syntax expr_b)
    | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | { $fmla:f_fmla })
    | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | $fmla:f_fmla ) =>
      let quantification := Formula.ExprQuantifier.of_syntax quantifier
      Formula.quantifier quantification (Arguments.of_syntax args) (Formula.of_syntax fmla)
    -- single predicate
    | `(f_fmla| $name:ident )
      => Formula.app name.getId []
    | `(f_fmla| $name:ident [ $expr,* ])
      => Formula.app name.getId (expr.getElems.toList.map Expression.of_syntax)
    | `(f_fmla| true) => Formula.true
    | `(f_fmla| false) => Formula.false
    | _ => unreachable!

  def Expression.of_syntax : TSyntax `f_expr → Expression
    | `(f_expr| $unop:f_expr_unop $expr:f_expr) =>
      Expression.unop (Expression.UnOp.of_syntax unop) (Expression.of_syntax expr)
    | `(f_expr| $expr_a:f_expr $binop:f_expr_binop $expr_b:f_expr) =>
      Expression.binop (Expression.BinOp.of_syntax binop) (Expression.of_syntax expr_a) (Expression.of_syntax expr_b)
    | `(f_expr| if $fmla:f_fmla then $expr_a:f_expr else $expr_b:f_expr) =>
      Expression.if_then_else (Formula.of_syntax fmla) (Expression.of_syntax expr_a) (Expression.of_syntax expr_b)
    | `(f_expr| { $args:f_args | $fmla:f_fmla }) =>
      Expression.set_comprehension (Arguments.of_syntax args) (Formula.of_syntax fmla)
    | `(f_expr| $expr_a:f_expr [ $expr,* ]) =>
      Expression.app (Expression.of_syntax expr_a) (expr.getElems.toList.map Expression.of_syntax)
    | `(f_expr| $name:ident) => Expression.literal name.getId
    | `(f_expr| let $id:ident = $expr_a:f_expr | $expr_b:f_expr) =>
      Expression.let id.getId (Expression.of_syntax expr_a) (Expression.of_syntax expr_b)
    | _ => unreachable!
end
termination_by
  _ s => s.raw

structure Predicate where
  name : Symbol
  args : List (Symbol × Expression) -- (name, type) pairs
  body : Formula -- with args bound
  deriving Repr

instance : Inhabited Predicate := ⟨{ name := default, args := default, body := default }⟩

declare_syntax_cat f_pred
declare_syntax_cat f_pred_args
syntax "[" f_args "]" : f_pred_args
syntax "pred" ident f_pred_args ? "{" f_fmla+ "}" : f_pred

def Predicate.of_syntax : TSyntax `f_pred → Predicate
  | `(f_pred| pred $name:ident { $fmla:f_fmla* }) =>
    let args := []
    let body := fmla |> Array.toList |> List.foldr (λ elt acc ↦ .binop .and (.of_syntax elt) acc) Formula.true
    { name := name.getId, args := args, body := body }
  | `(f_pred| pred $name:ident [ $args:f_args ] { $fmla:f_fmla* }) =>
    let args := Arguments.of_syntax args
    let body := fmla |> Array.toList |> List.foldr (λ elt acc ↦ .binop .and (.of_syntax elt) acc)  Formula.true
    { name := name.getId, args := args, body := body }
  | _ => unreachable!

structure Function where
  name : Symbol
  args : List (Symbol × Expression) -- (name, type) pairs
  result_type : Expression -- ignored in Forge but we'll check
  body : Expression -- with args bound
  deriving Repr

instance : Inhabited Function := ⟨{ name := default, args := default, result_type := default, body := default }⟩

declare_syntax_cat f_fun

syntax "fun" ident "[" f_args "]" ":" (f_field_multiplicity)? f_expr "{" f_expr "}" : f_fun

def Function.of_syntax : TSyntax `f_fun → Function
  | `(f_fun| fun $name:ident [ $args:f_args ] : $_? $result_type:f_expr { $expr:f_expr }) =>
    let args := Arguments.of_syntax args
    let result_type := Expression.of_syntax result_type
    let body := Expression.of_syntax expr
    { name := name.getId, args := args, result_type := result_type, body := body }
  | _ => unreachable!

structure ForgeModel where
  sigs : List Sig
  predicates : List Predicate
  functions : List Function
  deriving Repr

instance : Inhabited ForgeModel := ⟨{ sigs := default, predicates := default, functions := default }⟩

declare_syntax_cat f_term
syntax f_sig : f_term
syntax f_pred : f_term
syntax f_fun : f_term

declare_syntax_cat f_program
syntax f_term* : f_program

def term_of_syntax : TSyntax `f_term → ForgeModel
  | `(f_term| $s:f_sig) => { sigs := [Sig.of_syntax s], predicates := [], functions := [] }
  | `(f_term| $p:f_pred) => { sigs := [], predicates := [Predicate.of_syntax p], functions := [] }
  | `(f_term| $f:f_fun) => { sigs := [], predicates := [], functions := [Function.of_syntax f] }
  | _ => unreachable!

def of_syntax : TSyntax `f_program → ForgeModel
  | `(f_program| $terms:f_term* ) =>
    terms.foldl
    (λ acc term ↦
      match term with
      | `(f_term| $s:f_sig) => { acc with sigs := Sig.of_syntax s :: acc.sigs }
      | `(f_term| $p:f_pred) => { acc with predicates := Predicate.of_syntax p :: acc.predicates }
      | `(f_term| $f:f_fun) => { acc with functions := Function.of_syntax f :: acc.functions }
      | _ => unreachable!
    ) { sigs := [], predicates := [], functions := [] }
  | _ => unreachable!

end ForgeSyntax

def test : TermElabM ForgeSyntax.ForgeModel := do
  let stx ← `(f_program|
sig TreeNode {
    parent: lone TreeNode,
    children: set TreeNode
}

pred treeRoot[t: TreeNode] {
    no t.parent
}

pred treeChild[t: TreeNode] {
    some t.parent
}

pred notOwnParent[t: TreeNode] {
    t.parent = t
}

pred allNotOwnParent {
    all t : TreeNode | { notOwnParent[t] }
}

pred oneRoot {
    one t : TreeNode | { treeRoot[t] }
}

pred parentOfChildren {
    all t1 : TreeNode | all t2 : TreeNode | { t1.parent = t2 <=> t1 in t2.children }
}

pred allReachable {
    all t1 : TreeNode | all t2 : TreeNode | { t1 = t2 }
}

-- this breaks!
pred wellFormed {
    allNotOwnParent
    oneRoot
    parentOfChildren
}
)
  pure (ForgeSyntax.of_syntax stx)

#eval test

syntax "⟪" f_program "⟫" : term

#check ⟪
sig TreeNode {
    parent: lone TreeNode,
    children: set TreeNode
}

pred treeRoot[t: TreeNode] {
    no t.parent
}

pred treeChild[t: TreeNode] {
    some t.parent
}

pred notOwnParent[t: TreeNode] {
    t.parent != t
}

pred allNotOwnParent {
    all t : TreeNode | { notOwnParent[t] }
}

pred oneRoot {
    one t : TreeNode | { treeRoot[t] }
}

pred parentOfChildren {
    all t1 : TreeNode | all t2 : TreeNode | { t1.parent = t2 <=> t1 in t2.children }
}

pred wellFormed {
    allNotOwnParent
    oneRoot
    parentOfChildren
}

pred allReachable {
    all t1 : TreeNode | all t2 : TreeNode | { t1 != t2 }
}
⟫
