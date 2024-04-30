import Lforge.Ast.Types
import Lforge.Ast.Syntax.Fun
import Lforge.Ast.Parser.Terms
open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

def Function.of_syntax : TSyntax `forge_fun → MetaM Function
  | `(forge_fun| fun $name:ident [ $args:forge_args ] : $result_type:forge_expr { $expr:forge_expr }) => do
    let args ← Arguments.of_syntax args
    let result_type ← Expression.of_syntax result_type
    let body ← Expression.of_syntax expr
    return { name := name.getId, name_tok := name, args := args, result_type := result_type, body := body }
  | `(forge_fun| fun $name:ident [ $args:forge_args ] : $qt_tok $result_type:forge_expr { $expr:forge_expr }) => do
    let args ← Arguments.of_syntax args
    let result_type ← Expression.of_syntax result_type
    let body ← Expression.of_syntax expr
    logInfoAt qt_tok m!"This quantifier condition will not be enforced."
    return { name := name.getId, name_tok := name, args := args, result_type := result_type, body := body }
  | _ => throwUnsupportedSyntax

end ForgeSyntax
