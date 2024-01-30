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

register_option forge.dot_join : Bool := {
  defValue := Bool.true
  descr := "Expands use of dots within Forge to represent a 'join' and not a scoping."
}

-- This allows us to use forge_commands as honest-to-goodness Lean syntax
syntax (name := forge_program) f_program : command

/--
Constructs an arrow type from a list, allows for `opaque` definitions.
-/
private partial def arrowTypeOfList (types : List Symbol) : TermElabM Expr := do
  match types with
  | [] =>
    -- Prop
    pure (mkSort levelZero)
    -- α → β → ... → Prop
  | type :: rest =>
    mkArrow (mkConst type) (← arrowTypeOfList rest)

/--
Constructs an arrow value from a list (ending in → Prop), allows for `opaque` definitions.
Just returns α → β → ... → True
-/
private partial def arrowValueOfList (types : List Symbol) : TermElabM Expr := do
  match types with
  | [] =>
    -- Prop
    pure (mkConst `True)
  | type :: rest =>
    -- α → β → ... → Prop
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
    | Formula.BinOp.implies =>
      -- This makes an arrow type implication, is the same as the elaboration for →
      return mkForall (← MonadQuotation.addMacroScope `a) BinderInfo.default fmla_a fmla_b
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
    | .join
    | .cross => do
      let applied_op := ( match op with
        | .union => ``Union
        | .set_difference => ``SDiff
        | .intersection => ``Inter
        | .join => ``Forge.HJoin.join
        | .cross => ``Forge.HCross.cross )
      mkAppM applied_op #[expr_a, expr_b]
  | Expression.if_then_else fmla expr_a expr_b tok => do
    let fmla ← fmla.elab env
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    mkAppM ``ite #[fmla, expr_a, expr_b]
  | Expression.set_comprehension vars fmla tok => do
    -- if vars is [α, β, γ], then constructs α → β → γ → fmla
    -- Does something similar to forall/exists statement
    let vars ← vars.mapM (λ v ↦ do
      let (name, type) := v
      let v ← type.elab env
      pure (name, v))
    withLocalDeclsD
      (vars.toArray.map λ ⟨name, type⟩ ↦ ⟨name, λ _ ↦ pure type⟩)
      (λ fvars ↦ do
        let freed_vars := List.zipWith (λ ⟨name, _⟩ fvar ↦ (name, fvar)) vars fvars.toList
        let new_env := freed_vars.foldr (λ (v : Name × Expr) (acc : HashMap Name Expr) ↦
          let (name, fvar_type) := v
          acc.insert name fvar_type) env
        let body ← fmla.elab new_env
        fvars.foldrM (λ (fvar : Expr) (acc : Expr) ↦ do
          mkLambdaFVars #[fvar] acc) body)
  | Expression.app function args tok => do
    let function ← function.elab env
    let args ← args.mapM $ Expression.elab env
    mkAppM' function args.toArray
  | Expression.literal value tok => do
    /- Here, we do some magic involving splitting up a name to join it.
       This is so we can use dots in Forge to represent a join, and not a scoping. -/
    -- Gets the list of all the names, flat if dot_join is disabled
    let names := ( if (← getOptions).getBool `forge.dot_join then
        explode_names_over_macro_scopes value |> List.reverse
      else
        [value] )
    -- Resolves all the names to constants, either in lean environment or our own
    let resolved_names ← names.mapM (λ value ↦ do
      -- Simple lookup and errors if not found
      match (← getEnv).find? value with
      | .some _ => Term.mkConst value
      | .none =>
        match env.find? value with
        | .some e => pure e
        | .none => throwError m!"'{value}' is not defined in scope")
    -- Folds over the resolved names, joining them all together
    resolved_names.tail!.foldr
      (λ elt acc ↦ do mkAppM ``Forge.HJoin.join #[← acc, elt] ) (pure resolved_names.head!)

  | Expression.let id expression body tok => do
    let expression ← expression.elab env
    let body ← body.elab env
    throwError "TODO let elab"
where
explode_names (name : Name) : List Name :=
  match name with
  | Name.str p s => s :: explode_names p
  | _ => []
explode_names_over_macro_scopes (name : Name) : List Name :=
  if name.hasMacroScopes then
    let view := extractMacroScopes name
    let inner_names := explode_names view.name
    inner_names.map (λ v ↦ { view with name := v }.review)
  else
    explode_names name
end

def Predicate.elab (p : Predicate) : CommandElabM Unit := do
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
          -- TODO: Get names in printed type statement
          mkLambdaFVars #[fvar] acc) body)
    )
  let type_symbol_list ← p.args.mapM (λ v ↦ match v.2 with
    | .literal l _tok => return l
    -- TODO: this is a bit janky
    | _ => throwError "Expected types in predicate definition, got expressions instead." )
  let type ← liftTermElabM $ arrowTypeOfList type_symbol_list
  let predDecl := Declaration.defnDecl {
    name := p.name,
    levelParams := [],
    type := type,
    hints := ReducibilityHints.opaque,
    value := val,
    safety := .safe,
  }
  match env.addDecl predDecl with
  | Except.ok env => do
    setEnv env
    if (← getOptions).getBool `forge.hints then
      let type_string := type_symbol_list.foldr (λ (s : Symbol) (acc : String) ↦ s.toString ++ " → " ++ acc) "Prop"
      logInfoAt p.name_tok m!"def {p.name} : {type_string}"
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
    model.predicates.reverse.forM Predicate.elab
    model.functions.reverse.forM Function.elab
  | _ => throwUnsupportedSyntax

end ForgeSyntax
