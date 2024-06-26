import Lean
import Lforge.Utils
import Lforge.Ast.Types
import Lforge.Ast.Utils
import Lforge.Elab.Options
open Lean Elab Meta Command Term System

set_option autoImplicit false

namespace ForgeSyntax

mutual
partial def Formula.elab (env : HashMap Name Expr) (fmla : Formula) : TermElabM Expr := withRef fmla.tok do
  let inner ← fmla.elab' env
  -- The following line adds a lot of `Prop` term infos, which we're unsure whether we want.
  -- addTermInfo' fmla.tok inner
  return inner

partial def Formula.elab' (env : HashMap Name Expr) (fmla : Formula) : TermElabM Expr :=
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
      mkForall (← MonadQuotation.addMacroScope `a) BinderInfo.default fmla_a fmla_b,
      mkForall (← MonadQuotation.addMacroScope `a) BinderInfo.default (← mkAppM ``Not #[fmla_a]) fmla_c]
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
    -- integer operations
    | Formula.ExprBinOp.lt
    | Formula.ExprBinOp.leq
    | Formula.ExprBinOp.gt
    | Formula.ExprBinOp.geq => do
      let op := ( match op with
        | Formula.ExprBinOp.lt => ``LT.lt
        | Formula.ExprBinOp.leq => ``LE.le
        | Formula.ExprBinOp.gt => ``GT.gt
        | Formula.ExprBinOp.geq => ``GE.ge
        | _ => unreachable! )
      -- Check that types are ints
      let expr_a_type ← ensureHasType (mkConst ``Int) expr_a
      let expr_b_type ← ensureHasType (mkConst ``Int) expr_b
      mkAppM op #[expr_a, expr_b]
  | Formula.quantifier quantification vars fmla tok => do
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
      /-
      TODO: Figure out what to do with the other quantifiers here:
       - one/no/lone: behavior is very whack when multiple binders are implied, ie
       ∃! x : X, ∃! y : Y, P x y
       is different from
       ∃! (x, y) : X × Y, P x y
       - We have `some` and `all` right now (and in theory the others could be mimicked using this)
       - This is a 'complete' set of quantifiers technically.
      -/
      throwErrorAt tok "Quantifiers aside from `some` and `all` are not yet supported due to their complexity and potential ambiguity, please rewrite this into an equivalent statement using universal and existential quantifications."
  | Formula.app name args tok => do
    let args ← args.mapM $ Expression.elab env
    addTermInfo' tok (mkConst name)
    mkAppM name args.toArray
  | Formula.let name expression body _tok => do
    let bound_expr ← expression.elab env
    let bound_type ← inferType bound_expr
    let let_body ← withLetDecl name bound_type bound_expr
      (λ fvar => do
        let body ← body.elab $ env.insert name fvar
        mkLetFVars #[fvar] body)
    return let_body
  | Formula.true _ => mkConst ``True
  | Formula.false _ => mkConst ``False

partial def Expression.elab (env : HashMap Name Expr) (expr : Expression) : TermElabM Expr := withRef expr.tok do
  let inner ← expr.elab' env
  addTermInfo' expr.tok inner
  return inner

partial def Expression.elab' (env : HashMap Name Expr) (expr : Expression) : TermElabM Expr :=
  match expr with
  | Expression.unop op expr _tok => do
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
  | Expression.binop op expr_a expr_b _tok => do
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    match op with
    | .union
    | .set_difference
    | .intersection
    | .join
    | .cross => do
      let applied_op := ( match op with
        | .union => ``Union.union
        | .set_difference => ``SDiff.sdiff
        | .intersection => ``Inter.inter
        | .join => ``Forge.HJoin.join
        | .cross => ``Forge.HCross.cross )
      -- TODO: Fix coercions
      mkAppM applied_op #[expr_a, expr_b]
  | Expression.if_then_else fmla expr_a expr_b _tok => do
    let fmla ← fmla.elab env
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    mkAppM ``ite #[fmla, expr_a, expr_b]
  | Expression.set_comprehension vars fmla _tok => do
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
  | Expression.app function args _tok => do
    let function ← function.elab env
    let args ← args.mapM $ Expression.elab env
    mkAppM' function args.toArray
  | Expression.literal value tok => do
    /- Here, we do some magic involving splitting up a name to join it.
       This is so we can use dots in Forge to represent a join, and not a scoping. -/
    -- Gets the list of all the names, flat if dot_join is disabled
    -- TODO: make this smarter! If it can resolve the nested type doesn't explode!
    -- TODO: If something is a Type, automatically cast it to either an atom or set
    let names := ( if (← getOptions).getBool `forge.dot_join .true then
        explode_names_over_macro_scopes value |> List.reverse
      else
        [value] )
    -- Resolves all the names to constants, either in lean environment or our own
    let resolved_names ← names.mapM (λ value ↦ do
      -- Simple lookup and errors if not found
      let resolved_name ← match (← getEnv).find? value with
      | .some _ => Term.mkConst value
      | .none =>
        -- Checks in our constructed environment for variables
        match env.find? value with
        | .some e => pure e
        | .none => throwErrorAt tok m!"'{value}' is not defined in scope"
      pure resolved_name)
    -- Folds over the resolved names, joining them all together
    resolved_names.tail!.foldl
      (λ acc elt ↦ do mkAppM ``Forge.HJoin.join #[← acc, elt] ) (pure resolved_names.head!)
  | Expression.cast expr types _tok => do
    let expr ← expr.elab env
    let elaborated_types ← types.mapM
      (λ type ↦ elabTerm type (mkSort levelOne))
    elaborated_types.foldlM
      (λ acc type ↦ do
        (← elabTerm (← PrettyPrinter.delab acc) type)
          |> ensureHasType type)
      expr
  | Expression.let name expression body _tok => do
    let bound_expr ← expression.elab env
    let bound_type ← inferType bound_expr
    let let_body ← withLetDecl name bound_type bound_expr
      (λ fvar => do
        let body ← body.elab $ env.insert name fvar
        mkLetFVars #[fvar] body)
    return let_body
  | Expression.int val _tok => Expr.ofInt (mkConst ``Int) val
  | Expression.int.count expr _tok => do
    let expr ← expr.elab env
    -- let stx ← PrettyPrinter.delab expr
    -- make metavariable and ensure set type
    -- let expr ← ensureHasType (mkApp (mkConst ``Set) (← mkFreshTypeMVar)) expr
    -- mkAppM ``Set.ncard #[expr]
    -- let set_term ← elabTerm stx (mkApp (mkConst ``Set) (← mkFreshTypeMVar))
    -- TODO: Fix cardinality
    mkAppM ``Forge.Card.card #[expr]
  | Expression.int.agg .sing expr _tok => do
    ensureHasType (mkConst ``Int) (← expr.elab env)
  | Expression.int.agg _op _expr tok => do
    -- TODO!
    throwErrorAt tok "TODO: int.agg"
    -- If Finset, takes Finset.min, Finset.max, Finset.sum, etc.
  | Expression.int.sum binder expr body _tok => do
    let expr ← expr.elab env
    let type ← mkAppM ``Finset #[expr]
    let expr' ← elabTerm (← PrettyPrinter.delab expr) type
    let expr'' ← ensureHasType type expr'
    withLocalDeclD binder (expr) (λ fvar => do
      let body ← body.elab $ env.insert binder fvar
      let body' ← ensureHasType (mkConst ``Int) body
      mkAppOptM ``Finset.sum #[(mkConst ``Int), expr, none, expr'', mkLambda binder BinderInfo.default (← inferType fvar) body'])
  | Expression.int.unop op expr _tok => do
    let expr ← expr.elab env
    match op with
    | .abs => mkAppM ``Int.natAbs #[expr]
    | .sgn => mkAppM ``Int.sign #[expr]
  | Expression.int.binop .mod expr_a expr_b _tok => do
    let expr_a ← expr_a.elab env
    let expr_b ← expr_b.elab env
    mkAppM ``Int.mod #[expr_a, expr_b]
  | Expression.int.mulop op exprs _tok => do
    let exprs ← exprs.mapM (λ e ↦ e.elab env)
    let exprs ← exprs.mapM (λ e ↦ ensureHasType (mkConst ``Int) e)
    let operation := ( match op with
      | .add => ``Int.add
      | .sub => ``Int.sub
      | .mul => ``Int.mul
      | .div => ``Int.div )
    exprs.tail!.foldlM (λ acc e ↦ mkAppM operation #[acc, e]) exprs.head!

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

end ForgeSyntax
