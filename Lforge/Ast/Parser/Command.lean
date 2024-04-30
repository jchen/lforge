import Lforge.Ast.Types
import Lforge.Ast.Syntax.Command
import Lforge.Ast.Parser.Sig
import Lforge.Ast.Parser.Pred
import Lforge.Ast.Parser.Fun
import Lforge.Elab.Terms

open Lean Elab Command
set_option autoImplicit false

namespace ForgeSyntax

def ForgeModel.of_syntax : TSyntax `forge_program → MetaM ForgeModel
  | `(forge_program| $terms:forge_command* ) => do
    terms.foldlM (λ acc term ↦
        match term with
        | `(forge_command| $s:forge_sig) => do
          pure { acc with sigs := (← Sig.of_syntax s) ++ acc.sigs}
        | `(forge_command| $p:forge_pred) => do
          pure { acc with decls :=
            (.p (← Predicate.of_syntax p)) :: acc.decls }
        | `(forge_command| $f:forge_fun) => do
          pure { acc with decls :=
            (.f (← Function.of_syntax f)) :: acc.decls }
        | `(forge_command| $s:forge_check) => do
          logInfoAt s m!"This `check` block is not being executed."
          pure acc
        | _ => throwUnsupportedSyntax
      ) { sigs := [], decls := [] : ForgeModel}
  | _ => throwUnsupportedSyntax

end ForgeSyntax
