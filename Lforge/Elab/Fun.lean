import Lean
import Lforge.Ast.Types
import Lforge.Elab.Options
import Lforge.Elab.Utils
import Lforge.Elab.Terms
open Lean Elab Meta Command Term

namespace ForgeSyntax

-- This is a copy of Predicate code except output type is -> instead of
def Function.elab (f : Function) : CommandElabM Unit := do
  let env ← getEnv
  let vars ← liftTermElabM $ f.args.mapM (λ v ↦ do
    let (name, type) := v
    let v ← type.elab .empty
    pure (name, v))
  -- Ignored for now
  let output_type ← liftTermElabM $ f.result_type.elab .empty
  let val ← liftTermElabM $ (
    withLocalDeclsD
      (vars.toArray.map λ ⟨name, type⟩ ↦ ⟨name, λ _ ↦ pure type⟩)
      (λ fvars ↦ do
        let freed_vars := List.zipWith (λ ⟨name, _⟩ fvar ↦ (name, fvar)) vars fvars.toList
        let new_env := freed_vars.foldr (λ (v : Name × Expr) (acc : HashMap Name Expr) ↦
          let (name, fvar_type) := v
          acc.insert name fvar_type) .empty
        let body ← f.body.elab new_env
        fvars.foldrM (λ (fvar : Expr) (acc : Expr) ↦ do
          mkLambdaFVars #[fvar] acc) body)
    )
  let type_name_symbol_list : List (Symbol × Symbol) ← f.args.mapM (λ v ↦ match v.2 with
    | .literal l _tok => return (v.1, l)
    | _ => throwError "Expected types in predicate definition, got expressions instead." )
  let type_symbol_list : List Symbol := type_name_symbol_list.map (λ v ↦ v.2)
  -- If output type is int, keep as int, otherwise is an α → Prop
  let type ← liftTermElabM $ match output_type with
    | Expr.const `Int [] => namedArrowTypeOfList output_type type_name_symbol_list
    | _ => do namedArrowTypeOfList (← mkArrow output_type (mkSort levelZero)) type_name_symbol_list
  let val' ← liftTermElabM $ ensureHasType type val
  let funDecl := Declaration.defnDecl {
    name := f.name,
    levelParams := [],
    type := type,
    hints := ReducibilityHints.opaque,
    value := val',
    safety := .safe,
  }
  match env.addDecl funDecl with
  | Except.ok env => do
    setEnv env
    liftTermElabM $ addTermInfo' f.name_tok (mkConst f.name)
    if (← getOptions).getBool `forge.hints .false then
      let type_string := type_symbol_list.foldr (λ (s : Symbol) (acc : String) ↦ s.toString ++ " → " ++ acc) "Prop"
      logInfoAt f.name_tok m!"def {f.name} : {type_string}"
  | Except.error ex =>
    throwErrorAt f.name_tok ex.toMessageData (← getOptions)

end ForgeSyntax
