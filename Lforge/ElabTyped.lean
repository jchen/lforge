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

/--
`ExpressionType` represents the _type_ of an expression.

This helps with static type analysis, but also tags expressions by whether
they are a single element or a set. This allows for better optimizations relating
to `join` and the like.
-/
structure ExpressionType where
  /--
  This corresponds to an arrow type. For example an expression with type
  `A → B → Prop` will have type `[A, B]`.
  -/
  type : List Symbol
  deriving Repr, Inhabited

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
  | .unop op fmla tok => do
    let fmla ← fmla.elab env
    match op with
    | Formula.UnOp.not => mkAppM ``Not #[fmla]
  | Formula.binop op fmla_a fmla_b tok => do
    let fmla_a ← fmla_a.elab env
    let fmla_b ← fmla_b.elab env
    match op with
    | Formula.BinOp.and => mkAppM ``And #[fmla_a, fmla_b]
    | Formula.BinOp.or => mkAppM ``Or #[fmla_a, fmla_b]
    | Formula.BinOp.implies => mkAppM ``Implies #[fmla_a, fmla_b]
    | Formula.BinOp.iff => mkAppM ``Iff #[fmla_a, fmla_b]
  | Formula.implies_else fmla_a fmla_b fmla_c tok => do
    let fmla_a ← fmla_a.elab env
    let fmla_b ← fmla_b.elab env
    let fmla_c ← fmla_c.elab env
    mkAppM ``And #[
      ← mkAppM ``Implies #[fmla_a, fmla_b],
      ← mkAppM ``Implies #[← mkAppM ``Not #[fmla_a], fmla_c]]
  | Formula.expr_unop op expr tok => do
    let (expr, type) ← expr.elab env
    match op with
    | Formula.ExprUnOp.some => mkAppM ``ExprQuantifier.some #[expr]
    | Formula.ExprUnOp.no => mkAppM ``ExprQuantifier.no #[expr]
    | Formula.ExprUnOp.lone => mkAppM ``ExprQuantifier.lone #[expr]
    | Formula.ExprUnOp.one => mkAppM ``ExprQuantifier.one #[expr]
  | Formula.expr_binop op expr_a expr_b tok => do
    let (expr_a, type_a) ← expr_a.elab env
    let (expr_b, type_b) ← expr_b.elab env
    match op with
    | Formula.ExprBinOp.in => mkAppM ``ExprCmp.subset #[expr_a, expr_b]
    | Formula.ExprBinOp.eq => mkAppM ``ExprCmp.eq #[expr_a, expr_b]
    | Formula.ExprBinOp.neq => mkAppM ``Not #[← mkAppM ``ExprCmp.eq #[expr_a, expr_b]]
  | Formula.quantifier quantification vars fmla tok => do
    let vars ← vars.mapM (λ v ↦ do
      let (name, type) := v
      let v ← type.elab env
      pure (name, v))
    -- let fmla ← fmla.elab
    match quantification with
    | Formula.Quantifier.all => do
      -- TODO: this only does the first binder for now
      let ⟨name, ⟨type, _⟩⟩ := vars[0]!
      withLocalDecl name BinderInfo.default type λ fvar => do
        let body ← fmla.elab $ env.insert name fvar
        mkForallFVars #[fvar] body

      -- vars.foldrM (λ (v : Name × Expr) (acc : Expr) ↦
      --   let (name, type) := v
      --   -- mkForallFVars #[Expr.fvar {name := name}] acc) fmla
      --   return Expr.forallE name type acc .default) fmla
    | Formula.Quantifier.some => do
      throwError "TODO"
      -- vars.foldrM (λ (v : Name × Expr) (fmla : Expr) ↦
      --   let (name, type) := v
      --   mkAppM ``Exists #[Expr.lam name type fmla .default]) fmla
    | _ =>
      throwError "TODO"
  | Formula.app name args tok => do
    let args ← args.mapM $ Expression.elab env
    let expr_args := args.map Prod.fst
    mkAppM name expr_args.toArray
  | Formula.true => mkConst ``True
  | Formula.false => mkConst ``False

partial def Expression.elab (env : HashMap Name Expr) (expr : Expression) : TermElabM (Expr × ExpressionType) :=
  match expr with
  | Expression.unop op expr tok => do
    let (expr, expr_type) ← expr.elab env
    match op with
    | .transpose => (
      match expr_type with
      | { type := a :: b :: [] } => do
        pure (← mkAppM ``HTranspose.transpose #[expr], { type := [b, a] })
      | _ =>
        throwErrorAt tok "Expected expression to have arity 2.")
    | .transitive_closure
    | .reflexive_transitive_closure => (
      -- Since TC and RTC are so similar, we do it in the same statement
      let applied_op := (match op with
        | .transitive_closure => ``Relation.TransGen
        | .reflexive_transitive_closure => ``Relation.ReflTransGen
        | _ => unreachable!)
      match expr_type.type with
      | a :: b :: [] => do
        if a = b then
          pure (← mkAppM applied_op #[expr], expr_type)
        else
          throwErrorAt tok "Expected expression of arity 2 to have same type 'A => A'."
      | _ =>
        throwErrorAt tok "Expected expression to have arity 2 of the same type.")
  | Expression.binop op expr_a expr_b tok => do
    let (expr_a, type_a) ← expr_a.elab env
    let (expr_b, type_b) ← expr_b.elab env
    match op with
    | .union
    | .set_difference
    | .intersection => do
      let applied_op := ( match op with
        | .union => ``Union
        | .set_difference => ``SDiff
        | .intersection => ``Inter
        | _ => unreachable! )
      if type_a.type = type_b.type then
        pure (← mkAppM applied_op #[expr_a, expr_b], type_a)
      else
        throwErrorAt tok "Expected expressions to have the same type."
    | .join => do
      if type_a.type.reverse.head! = type_b.type.head! then
        pure (← mkAppM ``HJoin.join #[expr_a, expr_b],
          { type := type_a.type.reverse.tail.reverse ++ type_b.type })
      else
        throwErrorAt tok "Expected expressions to have the same nonempty."
    | .cross => throwError "TODO"
  | Expression.if_then_else fmla expr_a expr_b tok => do
    let fmla ← fmla.elab env
    let (expr_a, type_a) ← expr_a.elab env
    let (expr_b, type_b) ← expr_b.elab env
    if type_a.type = type_b.type then
      pure (← mkAppM ``ite #[fmla, expr_a, expr_b], type_a)
    else
      throwErrorAt tok "Expected expressions to have the same type."
  | Expression.set_comprehension vars fmla tok =>
    throwError "TODO"
  | Expression.app function args tok => do
    throwError "TODO"
    -- let ⟨function, function_type⟩ ← function.elab env
    -- let args_and_types ← args.mapM $ Expression.elab env
    -- let args := args_and_types.map Prod.fst
    -- let result_type := function_type.type.head
    -- pure (← mkAppM' function args.toArray, result_type)
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
    throwError "TODO"
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
  | Except.ok env => setEnv env
  | Except.error ex =>
    throwErrorAt p.name_tok ex.toMessageData (← getOptions)

def Function.elab (f : Function) : CommandElabM Unit := do
  let env ← getEnv
  let (val, type) ← liftTermElabM $ f.body.elab .empty
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

/-
TODOs / Note-to-self before Thanksgiving:
 - Most of this is partially implemented. Some things that remain are like `join` and quantifications.
 - Quantification follow the syntax of `all`, it eneds to bind some fvars and then use them in the body.
 - Add more static checking. Particularly in quantifications to evalyate the type of something.
 - If a sig appears in any body, we might want to add a `.u` that represents the universe of that sig. Like `Person.u : Person → Prop`.
 - By default, everything is a relation. But this makes things like `a in b` difficult if `a` is a singleton. Singletons are created from quantifications, as parameters of functions and/or predicates, or from `one sig`s. We want to add special cases for singletons - for example `a.b` for singleton a gives `b a` if `b` is a relation. So is `a[b]` or `a in b`. We should dispatch on what syntax to specifically generate based on whether we can turn `a` into a singleton.
 - Better type checking and static analysis, along with better linting.
-/


#check MetaM
