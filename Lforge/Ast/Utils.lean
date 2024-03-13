import Lforge.Ast.Types
import Lforge.Ast.Syntax.Command
open Lean Elab

namespace ForgeSyntax

def Formula.tok : Formula → Syntax
  | Formula.unop _ _ tok => tok
  | Formula.binop _ _ _ tok => tok
  | Formula.implies_else _ _ _ tok => tok
  | Formula.expr_unop _ _ tok => tok
  | Formula.expr_binop _ _ _ tok => tok
  | Formula.quantifier _ _ _ tok => tok
  | Formula.app _ _ tok => tok
  | Formula.let _ _ _ tok => tok
  | Formula.true tok => tok
  | Formula.false tok => tok

def Expression.tok : Expression → Syntax
  | Expression.unop _ _ tok => tok
  | Expression.binop _ _ _ tok => tok
  | Expression.if_then_else _ _ _ tok => tok
  | Expression.set_comprehension _ _ tok => tok
  | Expression.app _ _ tok => tok
  | Expression.literal _ tok => tok
  | Expression.let _ _ _ tok => tok
  | Expression.int _ tok => tok
  | Expression.int.count _ tok => tok
  | Expression.int.agg _ _ tok => tok
  | Expression.int.sum _ _ _ tok => tok
  | Expression.int.unop _ _ tok => tok
  | Expression.int.binop _ _ _ tok => tok
  | Expression.int.mulop _ _ tok => tok
end ForgeSyntax
