/-
Structures that represent the syntax of Forge.
-/
import Lean
open Lean Elab Meta

set_option autoImplicit false

def Symbol := String

inductive SigMultiplicity where
  -- there is always exactly one object of that sig
  | one
  -- there is never more than one object of this sig
  | lone
  -- any object of this sig must also be a member of some child sig
  | abstract
  -- unquantified, no restrictions
  | unquantified

inductive FieldMultiplicity where
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

structure Field where
  name : Symbol
  multiplicity : FieldMultiplicity
  type : List Symbol

structure Sig where
  quantifier : SigMultiplicity
  name : Symbol
  ancestor : Option Symbol := none
  fields : List Field

inductive ExprQuantification where
  | some
  | all
  | no
  | lone
  | one

mutual
  /-
  All formulas evaluate to boolean values
  -/
  inductive Formula where
    /- Operators -/
    | not (fmla : Formula)
    | and (fmla_a fmla_b : Formula)
    | or (fmla_a fmla_b : Formula)
    | implies (fmla_a fmla_b : Formula)
    -- if [fmla_a], then [fmla_b], otherwise [fmla_c]
    | implies_else (fmla_a fmla_b fmla_c : Formula)
    | iff (fmla_a fmla_b : Formula)

    /- Cardinality and membership -/
    | no (expr : Expression)
    | lone (expr : Expression)
    | one (expr : Expression)
    | some (expr : Expression)
    -- expr_a in expr_b
    | subset (expr_a expr_b : Expression)
    -- expr_a = expr_b
    | eq (expr_a expr_b : Expression)

    /- Quantifiers
       Quantifies [var](s) over [expr](s) and binds [var](s) in [fmla] -/
    | quantifier (quantification : ExprQuantification) (vars : List (Symbol × Expression)) (fmla : Formula)

    /- Predicate Applications -/
    | app (pref_name : Symbol) (args : List Expression)

  inductive Expression where
    | union (expr_a expr_b : Expression)
    | set_difference (expr_a expr_b : Expression)
    | intersection (expr_a expr_b : Expression)
    -- relational join
    | join (expr_a expr_b : Expression)
    -- cartesian product
    | cross (expr_a expr_b : Expression)
    -- transpose of a relation of arity-2
    | transpose (expr : Expression)
    -- transitive closure of a relation of arity-2
    | transitive_closure (expr : Expression)
    | reflexive_transitive_closure (expr : Expression)
    -- if [fmla], then [expr_a], otherwise [expr_b]
    | if_then_else (fmla expr_a expr_b : Expression)
    -- { [var] | [fmla] }, binds [var](s) in fmla and includes in set if true
    | set_comprehension (vars : List (Symbol × Expression)) (fmla : Formula)

    -- Function application, also includes sugar for join.
    | app (fun_name : Symbol) (args : List Expression)
    -- a literal value, can be sig, relation, or top-level expr (univ, none, iden, etc.)
    | literal (value : Symbol)

    | let (id : Symbol) (expression : Expression) (body : Expression)
end

structure Predicate where
  name : Symbol
  args : List (Symbol × Expression) -- (name, type) pairs
  body : Formula -- with args bound

structure Function where
  name : Symbol
  args : List (Symbol × Expression) -- (name, type) pairs
  result_type : Expression -- ignored in Forge but we'll check
  body : Expression -- with args bound

structure ForgeModel where
  sigs : List Sig
  predicates : List Predicate
  functions : List Function

declare_syntax_cat forge_sig
declare_syntax_cat forge_field

declare_syntax_cat forge_sig_multiplicity
syntax "one" : forge_sig_multiplicity
syntax "lone" : forge_sig_multiplicity
syntax "abstract" : forge_sig_multiplicity

-- TODO: inheritance here
syntax (forge_sig_multiplicity)? "sig" ident "{" forge_field,+ "}"  : forge_sig

declare_syntax_cat forge_field_multiplicity
syntax "one" : forge_field_multiplicity
syntax "lone" : forge_field_multiplicity
syntax "pfunc" : forge_field_multiplicity
syntax "func" : forge_field_multiplicity
syntax "set" : forge_field_multiplicity

declare_syntax_cat forge_field_type
syntax sepBy1(ident, " -> ") : forge_field_type

syntax ident ": " forge_field_multiplicity forge_field_type : forge_field

declare_syntax_cat forge_fmla
declare_syntax_cat forge_expr
declare_syntax_cat forge_args
declare_syntax_cat forge_arg
-- argument
syntax ident ": " forge_expr : forge_arg
-- arguments
syntax forge_arg,* : forge_args

declare_syntax_cat forge_fmla_unop
syntax "!" : forge_fmla_unop
syntax "not " : forge_fmla_unop

syntax forge_fmla_unop forge_fmla : forge_fmla

declare_syntax_cat forge_fmla_binop
syntax " && " : forge_fmla_binop
syntax " an d" : forge_fmla_binop
syntax " || " : forge_fmla_binop
syntax " or " : forge_fmla_binop
syntax " => " : forge_fmla_binop
syntax " implies " : forge_fmla_binop
syntax " <=> " : forge_fmla_binop
syntax " iff " : forge_fmla_binop

syntax forge_fmla forge_fmla_binop forge_fmla : forge_fmla

-- implies-else
syntax forge_fmla " => " forge_fmla " else " forge_fmla : forge_fmla
syntax forge_fmla " implies " forge_fmla " else " forge_fmla : forge_fmla

-- boolean literals
syntax "true" : forge_fmla
syntax "false" : forge_fmla

declare_syntax_cat forge_fmla_quantifier
syntax "no " : forge_fmla_quantifier
syntax "lone " : forge_fmla_quantifier
syntax "one " : forge_fmla_quantifier
syntax "some " : forge_fmla_quantifier

-- quantification over expr
syntax forge_fmla_quantifier forge_expr : forge_fmla

declare_syntax_cat forge_fmla_of_expr_binop
syntax " in " : forge_fmla_of_expr_binop
syntax " = " : forge_fmla_of_expr_binop
syntax " != " : forge_fmla_of_expr_binop

syntax forge_expr forge_fmla_of_expr_binop forge_expr : forge_fmla

declare_syntax_cat forge_fmla_of_expr_quantifier
syntax "no " : forge_fmla_of_expr_quantifier
syntax "lone " : forge_fmla_of_expr_quantifier
syntax "one " : forge_fmla_of_expr_quantifier
syntax "some " : forge_fmla_of_expr_quantifier
syntax "all " : forge_fmla_of_expr_quantifier

-- quantifications
syntax forge_fmla_of_expr_quantifier forge_args " | " "{" forge_fmla "}" : forge_fmla
syntax forge_fmla_of_expr_quantifier forge_args " | " forge_fmla : forge_fmla


-- predicate application
syntax ident "[" forge_expr,* "]" : forge_fmla

-- anonymous predicate
syntax ident : forge_fmla

declare_syntax_cat forge_expr_unop
syntax " ~ " : forge_expr_unop
syntax " ^ " : forge_expr_unop
syntax " * " : forge_expr_unop

syntax forge_expr_unop forge_expr : forge_expr

declare_syntax_cat forge_expr_binop
syntax " + " : forge_expr_binop
syntax " - " : forge_expr_binop
syntax " & " : forge_expr_binop
syntax " . " : forge_expr_binop
syntax " -> " : forge_expr_binop

syntax forge_expr forge_expr_binop forge_expr : forge_expr

-- if-then
syntax "if" forge_fmla "then" forge_expr : forge_expr
-- if-then-else
syntax "if" forge_fmla "then" forge_expr "else" forge_expr : forge_expr
-- set comprehension
syntax "{" forge_args " | " forge_fmla "}" : forge_expr
-- app
syntax forge_expr "[" forge_expr,* "]" : forge_expr
-- literal
syntax ident : forge_expr

-- let
syntax "let" ident "=" forge_expr "|" forge_expr : forge_expr

declare_syntax_cat forge_pred
declare_syntax_cat forge_pred_args
syntax "[" forge_args "]" : forge_pred_args

syntax "pred" ident (forge_pred_args)? "{" forge_fmla+ "}" : forge_pred

declare_syntax_cat forge_fun
declare_syntax_cat forge_fun_args
syntax "[" forge_args "]" : forge_fun_args

syntax "fun" ident forge_fun_args ":" (forge_field_multiplicity)? ident "{" forge_expr "}" : forge_fun

declare_syntax_cat forge_term
syntax forge_sig : forge_term
syntax forge_pred : forge_term
syntax forge_fun : forge_term

declare_syntax_cat forge_program
syntax "#lang" "forge" forge_term* : forge_program

syntax "⟪" forge_program "⟫" : term

#eval ⟪
#lang forge

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
