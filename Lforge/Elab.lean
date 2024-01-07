import Lean
import Lforge.Utils
import Lforge.Syntax
open Lean Elab Meta Command Term System
set_option autoImplicit false

namespace ForgeSyntax

register_option forge.hints : Bool := {
  defValue := Bool.true
  descr := "Provides hints to generated definitions from Forge."
}

-- This allows us to use forge_commands as honest-to-goodness Lean syntax
syntax (name := forge_program) f_program : command

private partial def arrowTypeOfList (types : List Symbol) : TermElabM Expr := do
  match types with
  | [] =>
    pure (mkSort levelZero)
  | type :: rest =>
    mkArrow (mkConst type) (← arrowTypeOfList rest)

private partial def arrowValueOfList (types : List Symbol) : TermElabM Expr := do
  match types with
  | [] =>
    pure (mkConst `True)
  | type :: rest =>
    pure (.lam .anonymous (mkConst type) (← arrowValueOfList rest) .default)

def Field.Multiplicity.elab (_ : Sig) (f : Field) (m : Field.Multiplicity) : CommandElabM Unit := do
  let env ← getEnv
  /-
  The helper will create a declaration corresponding to the quanfication of a field, for example:
  lone_parent, one_teacher, pfunc_owner, etc.
  -/
  let helper (pre : String) (quantifier_predicate : Name) (tok : Syntax) : CommandElabM Unit := (do
    let statement ← liftTermElabM $ mkAppM quantifier_predicate #[mkConst f.name]
    let decl := Declaration.axiomDecl {
      name := f.name.appendBefore pre,
      levelParams := [],
      type := statement,
      isUnsafe := False,
    }
    match env.addDecl decl with
    | Except.ok env => do
      if (← getOptions).getBool `forge.hints then
        logInfoAt tok m!"axiom {pre}{f.name} : {statement}"
      setEnv env
    | Except.error ex =>
      throwErrorAt tok ex.toMessageData $ ← getOptions)
  match m with
  | .one tok => helper "one_" ``FieldQuantifier.one tok
  | .lone tok => helper "lone_" ``FieldQuantifier.lone tok
  | .pfunc tok => do
    match f.type with
    | _ :: _ :: [] => helper "pfunc_" ``FieldQuantifier.pfunc tok
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
    if (← getOptions).getBool `forge.hints then
      logInfoAt f.name_tok m!"opaque {f.name} : {fieldType}"
    setEnv env
  | Except.error ex =>
    throwErrorAt s.name_tok ex.toMessageData (← getOptions)
  f.multiplicity.elab s f

def Sig.Multiplicity.elab (s : Sig) (m : Sig.Multiplicity) : CommandElabM Unit := do
  -- Do something to do with finsets, etc
  -- throwError "TODO multiplicity elab"
  pure ()

def Sig.elab (s : Sig): CommandElabM Unit := do
  let env ← getEnv
  let sigDecl := Declaration.opaqueDecl {
    name := s.name,
    value := mkSort levelZero,
    levelParams := [],
    type := mkSort levelOne,
    isUnsafe := False,
  }
  match env.addDecl sigDecl with
  | Except.ok env =>
    if (← getOptions).getBool `forge.hints then
      logInfoAt s.name_tok m!"opaque {s.name} : Type"
    setEnv env
  | Except.error ex =>
    throwErrorAt s.name_tok ex.toMessageData (← getOptions)
  s.quantifier.elab s

/--
We need to elaborate all top-level sigs before all fields can be elaborated,
so `Sig.lift_and_elab_multiple` will elab all Sigs and then all of their fields.
-/
def Sig.lift_and_elab_multiple (sigs : List Sig) : CommandElabM Unit := do
  sigs.forM Sig.elab
  sigs.forM (λ s ↦ s.fields.forM (Field.elab s))

mutual
partial def Formula.elab (env : HashMap Name Expr) (fmla : Formula) : TermElabM Expr :=
  match fmla with
  | .unop op fmla _tok => do
    let fmla ← fmla.elab env
    match op with
    | Formula.UnOp.not => mkAppM ``Not #[fmla]
  | Formula.binop op fmla_a fmla_b _tok => do
    let fmla_a ← fmla_a.elab env
    let fmla_b ← fmla_b.elab env
    match op with
    | Formula.BinOp.and => mkAppM ``And #[fmla_a, fmla_b]
    | Formula.BinOp.or => mkAppM ``Or #[fmla_a, fmla_b]
    | Formula.BinOp.implies => mkAppM ``Implies #[fmla_a, fmla_b]
    | Formula.BinOp.iff => mkAppM ``Iff #[fmla_a, fmla_b]
  | Formula.implies_else fmla_a fmla_b fmla_c _tok => do
    let fmla_a ← fmla_a.elab env
    let fmla_b ← fmla_b.elab env
    let fmla_c ← fmla_c.elab env
    mkAppM ``And #[
      ← mkAppM ``Implies #[fmla_a, fmla_b],
      ← mkAppM ``Implies #[← mkAppM ``Not #[fmla_a], fmla_c]]
  | Formula.expr_unop op expr _tok => do
    let expr ← expr.elab env
    match op with
    | Formula.ExprUnOp.some => mkAppM ``ExprQuantifier.some #[expr]
    | Formula.ExprUnOp.no => mkAppM ``ExprQuantifier.no #[expr]
    | Formula.ExprUnOp.lone => mkAppM ``ExprQuantifier.lone #[expr]
    | Formula.ExprUnOp.one => mkAppM ``ExprQuantifier.one #[expr]
  | Formula.expr_binop op expr_a expr_b _tok => do
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    match op with
    | Formula.ExprBinOp.in => mkAppM ``Forge.HIn.subset #[expr_a, expr_b]
    | Formula.ExprBinOp.eq => mkAppM ``Forge.HEq.eq #[expr_a, expr_b]
    | Formula.ExprBinOp.neq => mkAppM ``Not #[← mkAppM ``Forge.HEq.eq #[expr_a, expr_b]]
  | Formula.quantifier quantification vars fmla _tok => do
    let vars ← vars.mapM (λ v ↦ do
      let (name, type) := v
      let v ← type.elab env
      pure (name, v))
    match quantification with
    | Formula.Quantifier.all => do
      -- This is a bit nasty, but the free variable/metavariable system takes a bit to wrangle
      -- Here we need to construct a bunch of local declarations for the free variables
      withLocalDeclsD
        -- A list of the variables, we need to construct the type for technical reasons
        (vars.toArray.map λ ⟨name, type⟩ ↦ ⟨name, λ _ ↦ pure type⟩)
        -- This is a lambda that takes the list of free variable Exprs we introduced earlier and returns the
        -- actual body with those bound.
        (λ fvars ↦ do
          -- A copy of vars, except with the types replaced with fresh metavariables from withLocalDeclsD
          let freed_vars := List.zipWith (λ ⟨name, _⟩ fvar ↦ (name, fvar)) vars fvars.toList
          -- A new environment for the elaboration, with all idents bound to the fresh fvars
          let new_env := freed_vars.foldr (λ (v : Name × Expr) (acc : HashMap Name Expr) ↦
            let (name, fvar_type) := v
            acc.insert name fvar_type) env
          let body ← fmla.elab new_env
          mkForallFVars fvars body)
    | Formula.Quantifier.some => do
      -- Mostly the same as the above, except we need to wrap the body in an existential for every layer
      withLocalDeclsD
        (vars.toArray.map λ ⟨name, type⟩ ↦ ⟨name, λ _ ↦ pure type⟩)
        (λ fvars ↦ do
          let freed_vars := List.zipWith (λ ⟨name, _⟩ fvar ↦ (name, fvar)) vars fvars.toList
          let new_env := freed_vars.foldr (λ (v : Name × Expr) (acc : HashMap Name Expr) ↦
            let (name, fvar_type) := v
            acc.insert name fvar_type) env
          let body ← fmla.elab new_env
          fvars.foldrM (λ (fvar : Expr) (acc : Expr) ↦ do
            -- Wraps an existential over every lambda created
            mkAppM ``Exists #[←mkLambdaFVars #[fvar] acc]) body)
    | _ =>
      throwError "TODO quantifier unreached"
  | Formula.app name args _tok => do
    let args ← args.mapM $ Expression.elab env
    mkAppM name args.toArray
  | Formula.true => mkConst ``True
  | Formula.false => mkConst ``False

partial def Expression.elab (env : HashMap Name Expr) (expr : Expression) : TermElabM Expr :=
  match expr with
  | Expression.unop op expr tok => do
    let expr ← expr.elab env
    match op with
    | .transpose =>
      mkAppM ``Forge.HTranspose.transpose #[expr]
    | .transitive_closure
    | .reflexive_transitive_closure => (
      -- Since TC and RTC are so similar, we do it in the same statement
      let applied_op := (match op with
        | .transitive_closure => ``Relation.TransGen
        | .reflexive_transitive_closure => ``Relation.ReflTransGen
        | _ => unreachable!)
      mkAppM applied_op #[expr])
  | Expression.binop op expr_a expr_b tok => do
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    match op with
    | .union
    | .set_difference
    | .intersection
    | .join => do
      let applied_op := ( match op with
        | .union => ``Union
        | .set_difference => ``SDiff
        | .intersection => ``Inter
        | .join => ``Forge.HJoin.join
        | _ => unreachable! )
      mkAppM applied_op #[expr_a, expr_b]
    | .cross => throwError "TODO cross product"
  | Expression.if_then_else fmla expr_a expr_b tok => do
    let fmla ← fmla.elab env
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    mkAppM ``ite #[fmla, expr_a, expr_b]
  | Expression.set_comprehension vars fmla tok =>
    throwError "TODO set comprehension"
  | Expression.app function args tok => do
    let function ← function.elab env
    let args ← args.mapM $ Expression.elab env
    mkAppM' function args.toArray
  | Expression.literal value tok => do
    -- checks if value is bound within the environment
    match (← getEnv).find? value with
    | .some _ => mkConst value
    | .none => match env.find? value with
      | .some e => pure e
      | .none => throwError m!"'{value}' is not defined in scope"
  | Expression.let id expression body tok => do
    let expression ← expression.elab env
    let body ← body.elab env
    throwError "TODO let elab"
end

def Predicate.elab (p : Predicate) : CommandElabM Unit := do
  let env ← getEnv
  let val ← liftTermElabM $ p.body.elab .empty
  let predDecl := Declaration.defnDecl {
    name := p.name,
    levelParams := [],
    type := mkSort levelZero,
    hints := ReducibilityHints.opaque,
    value := val,
    safety := .safe,
  }
  match env.addDecl predDecl with
  | Except.ok env => do
    setEnv env
    if (← getOptions).getBool `forge.hints then
      logInfoAt p.name_tok m!"def {p.name} : Prop"
  | Except.error ex =>
    throwErrorAt p.name_tok ex.toMessageData (← getOptions)

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

@[command_elab forge_program]
def forgeImpl : CommandElab
  | `(command| $s:f_program) => do
    let model ← liftTermElabM $ ForgeModel.of_syntax s
    -- Elaborate all sigs first, this is so sig Types are defined (and lifted) before we try to define any fields, functions or predicates
    Sig.lift_and_elab_multiple model.sigs
    model.predicates.forM Predicate.elab
  | _ => throwUnsupportedSyntax

end ForgeSyntax
