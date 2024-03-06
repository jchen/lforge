import Lean
open Lean Elab Meta Command Term System
set_option autoImplicit false

/-
The Forge CST that gives us objects that represent all syntactically
valid Forge programs. A program is a list of sigs, predicates, and functions.
Sigs contain fields, predicates contain formulas, and functions contain expressions.
-/
namespace ForgeSyntax



namespace Formula


def UnOp.of_syntax : TSyntax `f_fmla_unop → MetaM UnOp
  | `(f_fmla_unop| !)
  | `(f_fmla_unop| not) => return .not
  | _ => throwUnsupportedSyntax




def Quantifier.of_syntax : TSyntax `f_fmla_quantifier → MetaM Quantifier
  | `(f_fmla_quantifier| no) => return .no
  | `(f_fmla_quantifier| lone) => return .lone
  | `(f_fmla_quantifier| one) => return .one
  | `(f_fmla_quantifier| some) => return .some
  | `(f_fmla_quantifier| all) => return .all
  | _ => throwUnsupportedSyntax


/-
Everything else
-/

-- implies-else


end Formula

namespace Expression


def UnOp.of_syntax : TSyntax `f_expr_unop → MetaM UnOp
  | `(f_expr_unop| ~) => return .transpose
  | `(f_expr_unop| ^) => return .transitive_closure
  | `(f_expr_unop| *) => return .reflexive_transitive_closure
  | _ => throwUnsupportedSyntax

-- TODO: make UnOps bind more than BinOps



def BinOp.of_syntax : TSyntax `f_expr_binop → MetaM BinOp
  | `(f_expr_binop| +) => return .union
  | `(f_expr_binop| -) => return .set_difference
  | `(f_expr_binop| &) => return .intersection
  | `(f_expr_binop| .) => return .join
  | `(f_expr_binop| ->) => return .cross
  | _ => throwUnsupportedSyntax

/-
Everything else
-/

end Expression

mutual
  /-
  All formulas evaluate to boolean values
  -/
end


mutual


  partial def Formula.of_syntax (stx : TSyntax `f_fmla) : MetaM Formula :=
    match stx with
    -- Unary Operators
    | `(f_fmla| $unop:f_fmla_unop $fmla:f_fmla) =>
      return Formula.unop (← Formula.UnOp.of_syntax unop) (← Formula.of_syntax fmla) stx
    -- Binary Operators
    | `(f_fmla| $fmla_a:f_fmla && $fmla_b:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla and $fmla_b:f_fmla) =>
      return Formula.binop .and (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
    | `(f_fmla| $fmla_a:f_fmla || $fmla_b:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla or $fmla_b:f_fmla) =>
      return Formula.binop .or (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
    | `(f_fmla| $fmla_a:f_fmla => $fmla_b:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla implies $fmla_b:f_fmla) =>
      return Formula.binop .implies (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
    | `(f_fmla| $fmla_a:f_fmla <=> $fmla_b:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla iff $fmla_b:f_fmla) =>
      return Formula.binop .iff (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
    -- Ternary Operators
    | `(f_fmla| $fmla_a:f_fmla => $fmla_b:f_fmla else $fmla_c:f_fmla)
    | `(f_fmla| $fmla_a:f_fmla implies $fmla_b:f_fmla else $fmla_c:f_fmla) =>
      return Formula.implies_else (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) (← Formula.of_syntax fmla_c) stx
    -- Unary operators on expressions (quantifiers)
    | `(f_fmla| some $expr_b:f_expr) =>
      return Formula.expr_unop .some (← Expression.of_syntax expr_b) stx
    | `(f_fmla| no $expr_b:f_expr) =>
      return Formula.expr_unop .no (← Expression.of_syntax expr_b) stx
    | `(f_fmla| lone $expr_b:f_expr) =>
      return Formula.expr_unop .lone (← Expression.of_syntax expr_b) stx
    | `(f_fmla| one $expr_b:f_expr) =>
      return Formula.expr_unop .one (← Expression.of_syntax expr_b) stx
    -- Binary operators on expressions
    | `(f_fmla| $expr_a:f_expr in $expr_b:f_expr) =>
      return Formula.expr_binop .in (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_fmla| $expr_a:f_expr = $expr_b:f_expr) =>
      return Formula.expr_binop .eq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_fmla| $expr_a:f_expr != $expr_b:f_expr) =>
      return Formula.expr_binop .neq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
    | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | { $fmla:f_fmla })
    | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | $fmla:f_fmla ) => do
      let quantification ← Formula.Quantifier.of_syntax quantifier
      return Formula.quantifier quantification (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
    -- single predicate
    | `(f_fmla| $name:ident ) => do
      return Formula.app name.getId [] stx
    | `(f_fmla| $name:ident [ $expr,* ]) => do
      return Formula.app name.getId (← expr.getElems.toList.mapM Expression.of_syntax) name
    | `(f_fmla| let $id:ident = $expr_a:f_expr | $fmla:f_fmla) =>
      return Formula.let id.getId (← Expression.of_syntax expr_a) (← Formula.of_syntax fmla) stx
    | `(f_fmla| ( $fmla:f_fmla )) => return (← Formula.of_syntax fmla)
    | `(f_fmla| { $fmla:f_fmla }) => return (← Formula.of_syntax fmla)
    | `(f_fmla| true) => return Formula.true stx
    | `(f_fmla| false) => return Formula.false stx
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


-- TODO: Functions are not working
def Function.of_syntax : TSyntax `f_fun → MetaM Function
  | `(f_fun| fun $name:ident [ $args:f_args ] : $_? $result_type:f_expr { $expr:f_expr }) => do
    let args ← Arguments.of_syntax args
    let result_type ← Expression.of_syntax result_type
    let body ← Expression.of_syntax expr
    return { name := name.getId, name_tok := name, args := args, result_type := result_type, body := body }
  | _ => throwUnsupportedSyntax


declare_syntax_cat f_command
syntax f_sig : f_command
syntax f_pred : f_command
syntax f_fun : f_command

declare_syntax_cat f_program
syntax f_command* : f_program


end ForgeSyntax

/-
Big TODO:
 - At some point in time, this entire code will probably need a large rehaul
-/
