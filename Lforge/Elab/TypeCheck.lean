import Lean
import Lforge.Ast.Types
import Lforge.Elab.Options
open Lean Elab Meta Command Term System

set_option autoImplicit false

namespace ForgeSyntax
/--
  If `expectedType?` is `some t`, then ensure `t` and `eType` are definitionally equal.
  If they are not, then try coercions.

  Argument `f?` is used only for generating error messages. -/
def forgeEnsureHasType (expectedType? : Option Expr) (e : Expr)
    (errorMsgHeader? : Option String := "Forge Type Error")
    (f? : Option Expr := none) : TermElabM Expr := do
  let some expectedType := expectedType? | return e
  if (← isDefEq (← inferType e) expectedType) then
    return e
  else
    mkCoe expectedType e f? errorMsgHeader?

end ForgeSyntax
