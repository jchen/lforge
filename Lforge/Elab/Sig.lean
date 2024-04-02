import Lean
import Lforge.Utils
import Lforge.Elab.Options
import Lforge.Elab.Utils
import Lforge.Ast.Types

open Lean Elab Meta Command Term

private def space_case (s : String) : String :=
  s.foldl
    (λ acc c ↦
      if c.isUpper then
        acc ++ " ".push c.toLower
      else
        acc.push c)
    ""

/--
Converts LeadingCamelCase name to underscore_case name.
-/
private def Lean.Name.underscored : Name → Name
  | .str p s => .str p (String.replace (space_case s).trim " " "_")
  | n        => n

private inductive SigInheritanceTree where
  | sigtree (s : Sig) (children : List SigInheritanceTree) (parent : Option Sig)

namespace ForgeSyntax
def Field.Multiplicity.elab (_ : Sig) (f : Field) (m : Field.Multiplicity) : CommandElabM Unit := do
  let env ← getEnv
  /-
  The helper will create a declaration corresponding to the quantification of a field, for example:
  lone_parent, one_teacher, pfunc_owner, etc.
  -/
  let helper (pre : String) (quantifier_predicate : Name) (tok : Syntax) : CommandElabM Unit := (do
    let statement ← liftTermElabM $ mkAppM quantifier_predicate #[mkConst f.name]
    let name := f.name.appendBefore pre
    let decl := Declaration.axiomDecl {
      name := name,
      levelParams := [],
      type := statement,
      isUnsafe := False,
    }
    match env.addDecl decl with
    | Except.ok env => do
      if (← getOptions).getBool `forge.hints .false then
        logInfoAt tok m!"axiom {pre}{f.name} : {statement}"
      setEnv env
      liftTermElabM $ addTermInfo' tok (mkConst name)
    | Except.error ex =>
      throwErrorAt tok ex.toMessageData $ ← getOptions)
  match m with
  | .one tok => helper "one_" ``FieldQuantifier.one tok
  | .lone tok => helper "lone_" ``FieldQuantifier.lone tok
  | .pfunc tok => do
    match f.type with
    | _ :: _ :: [] => helper "pfunc_" ``FieldQuantifier.pfunc tok
    -- todo: fix for a -> b -> c, can they be pfunc too?
    | _ => throwErrorAt tok m!"Failed to add axiom 'pfunc_{f.name}'. '{f.name}' does not have arity 2."
  | .func tok => do
    match f.type with
    | _ :: _ :: [] => helper "func_" ``FieldQuantifier.func tok
    | _ => throwErrorAt tok m!"Failed to add axiom 'func_{f.name}'. '{f.name}' does not have arity 2."
  | .set _ => return

def Field.elab (s : Sig) (f : Field) : CommandElabM Unit := do
  let fieldType ← liftTermElabM $ arrowTypeOfList ([s.name] ++ f.type)
  -- We need a value to create the opaque declaration since the field ought to be inhabited.
  let fieldVal ← liftTermElabM $ arrowValueOfList ([s.name] ++ f.type)
  let fieldDecl := Declaration.opaqueDecl {
    name := f.name,
    value := fieldVal,
    levelParams := [],
    type := fieldType,
    isUnsafe := False,
  }
  let env ← getEnv
  match env.addDecl fieldDecl with
  | Except.ok env =>
    if (← getOptions).getBool `forge.hints .false then
      logInfoAt f.name_tok m!"opaque {f.name} : {fieldType}"
    setEnv env
    liftTermElabM $ addTermInfo' f.name_tok (mkConst f.name)
  | Except.error ex =>
    throwErrorAt s.name_tok ex.toMessageData (← getOptions)
  f.multiplicity.elab s f

def Sig.Multiplicity.elab (s : Sig) (m : Sig.Multiplicity) : CommandElabM Unit := do
  /-
  TODO: Resolve with children sigs
   - If abstract, will add an axiom that it is inhabited only by its children
   - If one and is a leaf node, is the single Child : Parent instead of Child extends Parent.
   - Issues a warning for user to manually constrain their sigs otherwise.
  -/
  -- Every type ought to be inhabited
  elabCommand (← `(@[instance] axiom $(mkIdent $ s.name.underscored.appendBefore "inhabited_") : Inhabited $(mkIdent s.name)))
  -- Every type is finitely inhabited
  elabCommand (← `(@[instance] axiom $(mkIdent $ s.name.underscored.appendBefore "fintype_") : Fintype $(mkIdent s.name)))

def Sig.elab (s : Sig): CommandElabM Unit := do
  let env ← getEnv
  match s.ancestor with
  | .none =>
    let sigDecl := Declaration.opaqueDecl {
      name := s.name,
      value := mkSort levelZero,
      levelParams := [],
      type := mkSort levelOne,
      isUnsafe := False,
    }
    match env.addDecl sigDecl with
    | Except.ok env =>
      if (← getOptions).getBool `forge.hints .false then
        logInfoAt s.name_tok m!"opaque {s.name} : Type"
      setEnv env
      liftTermElabM $ addTermInfo' s.name_tok (mkConst s.name)
    | Except.error ex =>
      throwErrorAt s.name_tok ex.toMessageData (← getOptions)
    s.quantifier.elab s
  | some a => do
    elabCommand (← `(opaque $(mkIdent $ s.name.appendBefore "Is") : $(mkIdent a) → Prop))
    let first_char := (s.name.getString!.get! 0).toString
    elabCommand (← `(@[reducible] def $(mkIdent $ s.name) : Type := { $(mkIdent first_char) : $(mkIdent a) // $(mkIdent $ s.name.appendBefore "Is") $(mkIdent first_char) }))
    s.quantifier.elab s

/--
We need to elaborate all top-level sigs before all fields can be elaborated,
so `Sig.lift_and_elab_multiple` will elab all Sigs and then all of their fields.
-/
def Sig.lift_and_elab_multiple (sigs : List Sig) : CommandElabM Unit := do
  -- TODO: Make dependency DAG
  sigs.forM Sig.elab
  sigs.forM (λ s ↦ s.fields.forM (Field.elab s))

end ForgeSyntax
