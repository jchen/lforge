import Lforge.Ast.Types
import Lforge.Ast.Syntax.Command
import Lforge.Ast.Parser.Sig
import Lforge.Ast.Parser.Pred
import Lforge.Ast.Parser.Fun

open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

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
