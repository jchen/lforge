import Lean
import Lforge.Utils
import Lforge.Ast
import Lforge.Elab.Options
import Lforge.Elab.Sig
import Lforge.Elab.Pred
import Lforge.Elab.Fun

open Lean Elab Meta Command Term System

set_option autoImplicit false

namespace ForgeSyntax

-- This allows us to use forge_commands as honest-to-goodness Lean syntax
syntax (name := forge_program) f_program : command

@[command_elab forge_program]
def forgeImpl : CommandElab
  | `(command| $s:f_program) => do
    let model ← liftTermElabM $ ForgeModel.of_syntax s
    -- Elaborate all sigs first, this is so sig Types are defined (and lifted) before we try to define any fields, functions or predicates
    Sig.lift_and_elab_multiple model.sigs
    model.decls.reverse.forM (
      λ decl ↦
      match decl with
      | .p p => p.elab
      | .f f => f.elab
    )
  | _ => throwUnsupportedSyntax

end ForgeSyntax
