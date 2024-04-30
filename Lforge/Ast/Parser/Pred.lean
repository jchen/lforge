import Lforge.Ast.Types
import Lforge.Ast.Syntax.Pred
import Lforge.Ast.Parser.Terms
open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

def Predicate.of_syntax (stx : TSyntax `forge_pred) : MetaM Predicate :=
  match stx with
  | `(forge_pred| pred $name:ident { $fmla:forge_fmla* }) => do
    let args := []
    -- Join fmla list with `ands`. No base case, if empty, then true. Else one element.
    let body ← ( match fmla.toList with
    | [] => return Formula.true stx
    | fmla => do
      let fmlas_rev := fmla.reverse
      let init ← Formula.of_syntax fmlas_rev.head!
      fmlas_rev.tail!.foldlM (λ acc elt ↦ do
        return .binop .and (← Formula.of_syntax elt) acc stx) init )
    return { name := name.getId, name_tok := name, args := args, body := body }
  -- Predicate definition _with_ arguments/bindings
  | `(forge_pred| pred $name:ident [ $args:forge_args ] { $fmla:forge_fmla* }) => do
    let args ← Arguments.of_syntax args
    -- Join fmla list with `ands`. No base case, if empty, then true. Else one element.
    let body ← ( match fmla.toList with
    | [] => return Formula.true stx
    | fmla => do
      let fmlas_rev := fmla.reverse
      let init ← Formula.of_syntax fmlas_rev.head!
      fmlas_rev.tail!.foldlM (λ acc elt ↦ do
        return .binop .and (← Formula.of_syntax elt) acc stx) init )
    return { name := name.getId, name_tok := name, args := args, body := body }
  | _ => throwUnsupportedSyntax

end ForgeSyntax
