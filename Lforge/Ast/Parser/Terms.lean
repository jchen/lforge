import Lforge.Ast.Types
import Lforge.Ast.Syntax.Common
import Lforge.Ast.Syntax.Expr
import Lforge.Ast.Syntax.Fmla

open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

mutual

partial def Arguments.one_of_syntax : TSyntax `forge_arg → MetaM (List (Symbol × Expression))
  | `(forge_arg| $names:ident,* : $expr:forge_expr) =>
    names.getElems.toList.mapM (λ name ↦ do pure (name.getId, ← Expression.of_syntax expr))
  | _ => throwUnsupportedSyntax

partial def Arguments.of_syntax : TSyntax `forge_args → MetaM (List (Symbol × Expression))
  | `(forge_args| $args:forge_arg,* ) => do
    let lists ← args.getElems.toList.mapM Arguments.one_of_syntax
    return lists.join
  | _ => throwUnsupportedSyntax

partial def Formula.of_syntax (stx : TSyntax `forge_fmla) : MetaM Formula :=
  match stx with
  -- Unary Operators
  | `(forge_fmla| ! $fmla:forge_fmla)
  | `(forge_fmla| not $fmla:forge_fmla) =>
    return Formula.unop .not (← Formula.of_syntax fmla) stx
  -- Binary Operators
  | `(forge_fmla| $fmla_a:forge_fmla && $fmla_b:forge_fmla)
  | `(forge_fmla| $fmla_a:forge_fmla and $fmla_b:forge_fmla) =>
    return Formula.binop .and (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
  | `(forge_fmla| $fmla_a:forge_fmla || $fmla_b:forge_fmla)
  | `(forge_fmla| $fmla_a:forge_fmla or $fmla_b:forge_fmla) =>
    return Formula.binop .or (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
  | `(forge_fmla| $fmla_a:forge_fmla => $fmla_b:forge_fmla)
  | `(forge_fmla| $fmla_a:forge_fmla implies $fmla_b:forge_fmla) =>
    return Formula.binop .implies (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
  | `(forge_fmla| $fmla_a:forge_fmla <=> $fmla_b:forge_fmla)
  | `(forge_fmla| $fmla_a:forge_fmla iff $fmla_b:forge_fmla) =>
    return Formula.binop .iff (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) stx
  -- Ternary Operators
  | `(forge_fmla| $fmla_a:forge_fmla => $fmla_b:forge_fmla else $fmla_c:forge_fmla)
  | `(forge_fmla| $fmla_a:forge_fmla implies $fmla_b:forge_fmla else $fmla_c:forge_fmla) =>
    return Formula.implies_else (← Formula.of_syntax fmla_a) (← Formula.of_syntax fmla_b) (← Formula.of_syntax fmla_c) stx
  -- Unary operators on expressions (quantifiers)
  | `(forge_fmla| some $expr_b:forge_expr) =>
    return Formula.expr_unop .some (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| no $expr_b:forge_expr) =>
    return Formula.expr_unop .no (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| lone $expr_b:forge_expr) =>
    return Formula.expr_unop .lone (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| one $expr_b:forge_expr) =>
    return Formula.expr_unop .one (← Expression.of_syntax expr_b) stx
  -- Binary operators on expressions
  | `(forge_fmla| $expr_a:forge_expr in $expr_b:forge_expr) =>
    return Formula.expr_binop .in (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| $expr_a:forge_expr !in $expr_b:forge_expr)
  | `(forge_fmla| $expr_a:forge_expr not in $expr_b:forge_expr) =>
    return Formula.unop .not (Formula.expr_binop .in (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx) stx
  | `(forge_fmla| $expr_a:forge_expr = $expr_b:forge_expr) =>
    return Formula.expr_binop .eq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| $expr_a:forge_expr != $expr_b:forge_expr) =>
    return Formula.expr_binop .neq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  -- Binary operators on numbers
  | `(forge_fmla| $expr_a:forge_expr < $expr_b:forge_expr) =>
    return Formula.expr_binop .lt (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| $expr_a:forge_expr <= $expr_b:forge_expr) =>
    return Formula.expr_binop .leq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| $expr_a:forge_expr > $expr_b:forge_expr) =>
    return Formula.expr_binop .gt (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| $expr_a:forge_expr >= $expr_b:forge_expr) =>
    return Formula.expr_binop .geq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_fmla| $quantifier:forge_fmla_quantifier $args:forge_args | { $fmla:forge_fmla })
  | `(forge_fmla| $quantifier:forge_fmla_quantifier $args:forge_args | $fmla:forge_fmla ) => do
    let quantification ← (
      match quantifier with
      | `(forge_fmla_quantifier| no) => return .no
      | `(forge_fmla_quantifier| lone) => return .lone
      | `(forge_fmla_quantifier| one) => return .one
      | `(forge_fmla_quantifier| some) => return .some
      | `(forge_fmla_quantifier| all) => return .all
      | _ => throwUnsupportedSyntax
    )
    return Formula.quantifier quantification (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
  -- single predicate
  | `(forge_fmla| $name:ident ) => do
    return Formula.app name.getId [] stx
  | `(forge_fmla| $name:ident [ $expr,* ]) => do
    return Formula.app name.getId (← expr.getElems.toList.mapM Expression.of_syntax) name
  -- let
  | `(forge_fmla| let $id:ident = $expr_a:forge_expr | $fmla:forge_fmla) =>
    return Formula.let id.getId (← Expression.of_syntax expr_a) (← Formula.of_syntax fmla) stx
  -- parens
  | `(forge_fmla| ( $fmla:forge_fmla )) => return (← Formula.of_syntax fmla)
  | `(forge_fmla| { $fmlas:forge_fmla* }) => do
    match fmlas.toList with
    | [] => return Formula.true stx
    | fmla => do
      let fmlas_rev := fmla.reverse
      let init ← Formula.of_syntax fmlas_rev.head!
      fmlas_rev.tail!.foldlM (λ acc elt ↦ do
        return .binop .and (← Formula.of_syntax elt) acc stx) init
  -- boolean literals
  | `(forge_fmla| true) => return Formula.true stx
  | `(forge_fmla| false) => return Formula.false stx
  | _ => throwUnsupportedSyntax

partial def Expression.of_syntax (stx : TSyntax `forge_expr) : MetaM Expression :=
  match stx with
  -- Unary operators
  | `(forge_expr| ~ $expr:forge_expr) =>
    return Expression.unop .transpose (← Expression.of_syntax expr) stx
  | `(forge_expr| ^ $expr:forge_expr) =>
    return Expression.unop .transitive_closure (← Expression.of_syntax expr) stx
  | `(forge_expr| * $expr:forge_expr) =>
    return Expression.unop .reflexive_transitive_closure (← Expression.of_syntax expr) stx
  -- Binary operators
  | `(forge_expr| $expr:forge_expr + $expr':forge_expr) =>
    return Expression.binop .union (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(forge_expr| $expr:forge_expr - $expr':forge_expr) =>
    return Expression.binop .set_difference (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(forge_expr| $expr:forge_expr & $expr':forge_expr) =>
    return Expression.binop .intersection (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(forge_expr| $expr:forge_expr . $expr':forge_expr) =>
    return Expression.binop .join (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(forge_expr| $expr:forge_expr -> $expr':forge_expr) =>
    return Expression.binop .cross (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  -- if-then-else
  | `(forge_expr| if $fmla:forge_fmla then $expr_a:forge_expr else $expr_b:forge_expr) =>
    return Expression.if_then_else (← Formula.of_syntax fmla) (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  -- set comprehension
  | `(forge_expr| { $args:forge_args | $fmla:forge_fmla }) =>
    return Expression.set_comprehension (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
  -- app
  | `(forge_expr| $expr_a:forge_expr [ $expr,* ]) =>
    return Expression.app (← Expression.of_syntax expr_a) (← expr.getElems.toList.mapM Expression.of_syntax) stx
  -- literal
  | `(forge_expr| $name:ident) => return Expression.literal name.getId stx
  -- let
  | `(forge_expr| let $id:ident = $expr_a:forge_expr | $expr_b:forge_expr) =>
    return Expression.let id.getId (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(forge_expr| $expr:forge_expr /* as $types:term,* */) => return Expression.cast (← Expression.of_syntax expr) types.getElems.toList stx
  -- parens
  | `(forge_expr| ( $expr:forge_expr )) => return (← Expression.of_syntax expr)
  -- int literal (and negative):
  | `(forge_expr| $n:num) => return Expression.int n.getNat stx
  | `(forge_expr| -$n:num) => return Expression.int (-n.getNat) stx
  | `(forge_expr| #$expr:forge_expr) => return Expression.int.count (← Expression.of_syntax expr) stx
  | `(forge_expr| sing[$expr:forge_expr]) => Expression.of_syntax expr
  | `(forge_expr| sum[$expr:forge_expr]) => return Expression.int.agg .sum (← Expression.of_syntax expr) stx
  | `(forge_expr| max[$expr:forge_expr]) => return Expression.int.agg .max (← Expression.of_syntax expr) stx
  | `(forge_expr| min[$expr:forge_expr]) => return Expression.int.agg .min (← Expression.of_syntax expr) stx
  | `(forge_expr| sum $id:ident : $expr:forge_expr | $body:forge_expr)
  | `(forge_expr| sum $id:ident : $expr:forge_expr | { $body:forge_expr }) =>
    return Expression.int.sum id.getId (← Expression.of_syntax expr) (← Expression.of_syntax body) stx
  | `(forge_expr| abs[$expr:forge_expr]) => return Expression.int.unop .abs (← Expression.of_syntax expr) stx
  | `(forge_expr| sign[$expr:forge_expr]) => return Expression.int.unop .sgn (← Expression.of_syntax expr) stx
  | `(forge_expr| add[$expr:forge_expr,*]) =>
    return Expression.int.mulop .add (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(forge_expr| subtract[$expr:forge_expr,*]) =>
    return Expression.int.mulop .sub (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(forge_expr| multiply[$expr:forge_expr,*]) =>
    return Expression.int.mulop .mul (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(forge_expr| divide[$expr:forge_expr,*]) =>
    return Expression.int.mulop .div (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(forge_expr| remainder[$expr_a:forge_expr, $expr_b:forge_expr]) =>
    return Expression.int.binop .mod (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | _ => throwUnsupportedSyntax
end

end ForgeSyntax
