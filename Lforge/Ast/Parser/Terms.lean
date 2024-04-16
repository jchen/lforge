import Lforge.Ast.Types
import Lforge.Ast.Syntax.Common
import Lforge.Ast.Syntax.Expr
import Lforge.Ast.Syntax.Fmla

open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

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
  -- Unary Operators
  | `(f_fmla| ! $fmla:f_fmla)
  | `(f_fmla| not $fmla:f_fmla) =>
    return Formula.unop .not (← Formula.of_syntax fmla) stx
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
  | `(f_fmla| $expr_a:f_expr !in $expr_b:f_expr)
  | `(f_fmla| $expr_a:f_expr not in $expr_b:f_expr) =>
    return Formula.unop .not (Formula.expr_binop .in (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx) stx
  | `(f_fmla| $expr_a:f_expr = $expr_b:f_expr) =>
    return Formula.expr_binop .eq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(f_fmla| $expr_a:f_expr != $expr_b:f_expr) =>
    return Formula.expr_binop .neq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  -- Binary operators on numbers
  | `(f_fmla| $expr_a:f_expr < $expr_b:f_expr) =>
    return Formula.expr_binop .lt (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(f_fmla| $expr_a:f_expr <= $expr_b:f_expr) =>
    return Formula.expr_binop .leq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(f_fmla| $expr_a:f_expr > $expr_b:f_expr) =>
    return Formula.expr_binop .gt (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(f_fmla| $expr_a:f_expr >= $expr_b:f_expr) =>
    return Formula.expr_binop .geq (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | { $fmla:f_fmla })
  | `(f_fmla| $quantifier:f_fmla_quantifier $args:f_args | $fmla:f_fmla ) => do
    let quantification ← (
      match quantifier with
      | `(f_fmla_quantifier| no) => return .no
      | `(f_fmla_quantifier| lone) => return .lone
      | `(f_fmla_quantifier| one) => return .one
      | `(f_fmla_quantifier| some) => return .some
      | `(f_fmla_quantifier| all) => return .all
      | _ => throwUnsupportedSyntax
    )
    return Formula.quantifier quantification (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
  -- single predicate
  | `(f_fmla| $name:ident ) => do
    return Formula.app name.getId [] stx
  | `(f_fmla| $name:ident [ $expr,* ]) => do
    return Formula.app name.getId (← expr.getElems.toList.mapM Expression.of_syntax) name
  -- let
  | `(f_fmla| let $id:ident = $expr_a:f_expr | $fmla:f_fmla) =>
    return Formula.let id.getId (← Expression.of_syntax expr_a) (← Formula.of_syntax fmla) stx
  -- parens
  | `(f_fmla| ( $fmla:f_fmla )) => return (← Formula.of_syntax fmla)
  | `(f_fmla| { $fmlas:f_fmla* }) => do
    match fmlas.toList with
    | [] => return Formula.true stx
    | fmla => do
      let fmlas_rev := fmla.reverse
      let init ← Formula.of_syntax fmlas_rev.head!
      fmlas_rev.tail!.foldlM (λ acc elt ↦ do
        return .binop .and (← Formula.of_syntax elt) acc stx) init
  -- boolean literals
  | `(f_fmla| true) => return Formula.true stx
  | `(f_fmla| false) => return Formula.false stx
  | _ => throwUnsupportedSyntax

partial def Expression.of_syntax (stx : TSyntax `f_expr) : MetaM Expression :=
  match stx with
  -- Unary operators
  | `(f_expr| ~ $expr:f_expr) =>
    return Expression.unop .transpose (← Expression.of_syntax expr) stx
  | `(f_expr| ^ $expr:f_expr) =>
    return Expression.unop .transitive_closure (← Expression.of_syntax expr) stx
  | `(f_expr| * $expr:f_expr) =>
    return Expression.unop .reflexive_transitive_closure (← Expression.of_syntax expr) stx
  -- Binary operators
  | `(f_expr| $expr:f_expr + $expr':f_expr) =>
    return Expression.binop .union (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(f_expr| $expr:f_expr - $expr':f_expr) =>
    return Expression.binop .set_difference (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(f_expr| $expr:f_expr & $expr':f_expr) =>
    return Expression.binop .intersection (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(f_expr| $expr:f_expr . $expr':f_expr) =>
    return Expression.binop .join (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  | `(f_expr| $expr:f_expr -> $expr':f_expr) =>
    return Expression.binop .cross (← Expression.of_syntax expr) (← Expression.of_syntax expr') stx
  -- if-then-else
  | `(f_expr| if $fmla:f_fmla then $expr_a:f_expr else $expr_b:f_expr) =>
    return Expression.if_then_else (← Formula.of_syntax fmla) (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  -- set comprehension
  | `(f_expr| { $args:f_args | $fmla:f_fmla }) =>
    return Expression.set_comprehension (← Arguments.of_syntax args) (← Formula.of_syntax fmla) stx
  -- app
  | `(f_expr| $expr_a:f_expr [ $expr,* ]) =>
    return Expression.app (← Expression.of_syntax expr_a) (← expr.getElems.toList.mapM Expression.of_syntax) stx
  -- literal
  | `(f_expr| $name:ident) => return Expression.literal name.getId stx
  -- let
  | `(f_expr| let $id:ident = $expr_a:f_expr | $expr_b:f_expr) =>
    return Expression.let id.getId (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | `(f_expr| $expr:f_expr /* as $types:term,* */) => return Expression.cast (← Expression.of_syntax expr) types.getElems.toList stx
  -- parens
  | `(f_expr| ( $expr:f_expr )) => return (← Expression.of_syntax expr)
  -- int literal (and negative):
  | `(f_expr| $n:num) => return Expression.int n.getNat stx
  | `(f_expr| -$n:num) => return Expression.int (-n.getNat) stx
  | `(f_expr| #$expr:f_expr) => return Expression.int.count (← Expression.of_syntax expr) stx
  | `(f_expr| sing[$expr:f_expr]) => Expression.of_syntax expr
  | `(f_expr| sum[$expr:f_expr]) => return Expression.int.agg .sum (← Expression.of_syntax expr) stx
  | `(f_expr| max[$expr:f_expr]) => return Expression.int.agg .max (← Expression.of_syntax expr) stx
  | `(f_expr| min[$expr:f_expr]) => return Expression.int.agg .min (← Expression.of_syntax expr) stx
  | `(f_expr| sum $id:ident : $expr:f_expr | $body:f_expr)
  | `(f_expr| sum $id:ident : $expr:f_expr | { $body:f_expr }) =>
    return Expression.int.sum id.getId (← Expression.of_syntax expr) (← Expression.of_syntax body) stx
  | `(f_expr| abs[$expr:f_expr]) => return Expression.int.unop .abs (← Expression.of_syntax expr) stx
  | `(f_expr| sign[$expr:f_expr]) => return Expression.int.unop .sgn (← Expression.of_syntax expr) stx
  | `(f_expr| add[$expr:f_expr,*]) =>
    return Expression.int.mulop .add (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(f_expr| subtract[$expr:f_expr,*]) =>
    return Expression.int.mulop .sub (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(f_expr| multiply[$expr:f_expr,*]) =>
    return Expression.int.mulop .mul (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(f_expr| divide[$expr:f_expr,*]) =>
    return Expression.int.mulop .div (← expr.getElems.toList.mapM Expression.of_syntax) stx
  | `(f_expr| remainder[$expr_a:f_expr, $expr_b:f_expr]) =>
    return Expression.int.binop .mod (← Expression.of_syntax expr_a) (← Expression.of_syntax expr_b) stx
  | _ => throwUnsupportedSyntax
end

end ForgeSyntax
