import Lean
import Lforge.Ast.Types
import Lforge.Elab.Options
import Lforge.Elab.Utils
import Lforge.Elab.Terms
open Lean Elab Meta Command Term

namespace ForgeSyntax

-- TODO: do function code
def Function.elab (f : Function) : CommandElabM Unit := do
  let env ← getEnv
  let val ← liftTermElabM $ f.body.elab .empty
  let funDecl := Declaration.defnDecl {
    name := f.name,
    levelParams := [],
    type := mkSort levelZero,
    hints := ReducibilityHints.opaque,
    value := val,
    safety := .safe,
  }
  match env.addDecl funDecl with
  | Except.ok env => setEnv env
  | Except.error ex =>
    throwErrorAt f.name_tok ex.toMessageData (← getOptions)

end ForgeSyntax
