import Lforge.Ast.Types
import Lforge.Ast.Syntax.Fun
import Lforge.Ast.Parser.Terms
open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

def Function.of_syntax : TSyntax `f_fun → MetaM Function
  | `(f_fun| fun $name:ident [ $args:f_args ] : $_? $result_type:f_expr { $expr:f_expr }) => do
    let args ← Arguments.of_syntax args
    let result_type ← Expression.of_syntax result_type
    let body ← Expression.of_syntax expr
    return { name := name.getId, name_tok := name, args := args, result_type := result_type, body := body }
  | _ => throwUnsupportedSyntax

end ForgeSyntax
