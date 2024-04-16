import Lean
import Lforge.Ast.Types
import Lforge.Elab.Options
import Lforge.Elab.Utils
import Lforge.Elab.Terms
open Lean Elab Meta Command Term

namespace ForgeSyntax

def Predicate.elab (p : Predicate) : CommandElabM Unit := withRef p.name_tok do
  let env ← getEnv
  let vars ← liftTermElabM $ p.args.mapM (λ v ↦ do
    let (name, type) := v
    let v ← type.elab .empty
    pure (name, v))
  let val ← liftTermElabM $ (
    withLocalDeclsD
      (vars.toArray.map λ ⟨name, type⟩ ↦ ⟨name, λ _ ↦ pure type⟩)
      (λ fvars ↦ do
        let freed_vars := List.zipWith (λ ⟨name, _⟩ fvar ↦ (name, fvar)) vars fvars.toList
        let new_env := freed_vars.foldr (λ (v : Name × Expr) (acc : HashMap Name Expr) ↦
          let (name, fvar_type) := v
          acc.insert name fvar_type) .empty
        let body ← p.body.elab new_env
        fvars.foldrM (λ (fvar : Expr) (acc : Expr) ↦ do
          mkLambdaFVars #[fvar] acc) body)
    )
  let type_name_symbol_list : List (Symbol × Symbol) ← p.args.mapM (λ v ↦ match v.2 with
    | .literal l _tok => return (v.1, l)
    | _ => throwError "Expected types in predicate definition, got expressions instead." )
  let type_symbol_list : List Symbol := type_name_symbol_list.map (λ v ↦ v.2)
  let type ← liftTermElabM $ namedPropArrowTypeOfList type_name_symbol_list
  let val' ← liftTermElabM $ ensureHasType type val
  let predDecl := Declaration.defnDecl {
    name := p.name,
    levelParams := [],
    type := type,
    hints := ReducibilityHints.opaque,
    value := val',
    safety := .safe,
  }
  match env.addDecl predDecl with
  | Except.ok env => do
    setEnv env
    liftTermElabM $ addTermInfo' p.name_tok (mkConst p.name)
    if (← getOptions).getBool `forge.hints .false then
      let type_string := type_symbol_list.foldr (λ (s : Symbol) (acc : String) ↦ s.toString ++ " → " ++ acc) "Prop"
      logInfoAt p.name_tok m!"def {p.name} : {type_string}"
  | Except.error ex =>
    throwErrorAt p.name_tok ex.toMessageData (← getOptions)

end ForgeSyntax
