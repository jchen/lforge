import Lean
import Lforge.Utils
import Lforge.Elab.Options
import Lforge.Elab.Utils
import Lforge.Ast.Types
import Lforge.Ast.Utils

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
def Field.Multiplicity.elab (_ : Sig) (f : Field) (m : Field.Multiplicity) : CommandElabM Unit := withRef m.tok do
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
  -- | .one tok => helper "one_" ``FieldQuantifier.one tok
  | .lone tok => helper "lone_" ``FieldQuantifier.lone tok
  | .pfunc tok => do
    match f.type with
    | _ :: _ :: [] => helper "pfunc_" ``FieldQuantifier.pfunc tok
    -- todo: fix for a -> b -> c, can they be pfunc too?
    | _ => throwErrorAt tok m!"Failed to add axiom 'pfunc_{f.name}'. '{f.name}' does not have arity 2."
  -- All gets handled by Field.elab
  -- | .func tok => do
  --   match f.type with
  --   | _ :: _ :: [] =>
  --     -- This is handled by Field.elab
  --     -- helper "func_" ``FieldQuantifier.func tok
  --     return
  --   | _ => throwErrorAt tok m!"Failed to add axiom 'func_{f.name}'. '{f.name}' does not have arity 2."
  | _ => return

def Field.elab (s : Sig) (f : Field) : CommandElabM Unit := withRef f.tok do
  let fieldType ←
  match (f.multiplicity, f.type.length) with
    -- If one, it is a function
    | (.one _, 1) => liftTermElabM $ mkArrow (Lean.mkConst s.name) (Lean.mkConst $ f.type.get! 0)
    -- If func, it is a function
    | (.func _, _) =>
      let type_rev := ([s.name] ++ f.type).reverse
      let arrow_type :=
        arrowFunTypeOfList type_rev.tail!.reverse (Lean.mkConst type_rev.head!)
      liftTermElabM $ arrow_type
    | _ => liftTermElabM $ arrowTypeOfList ([s.name] ++ f.type)
  elabCommand (← `(noncomputable opaque $(mkIdent f.name) : $(← liftTermElabM $ PrettyPrinter.delab fieldType)))
  if (← getOptions).getBool `forge.hints .false then
    logInfoAt f.name_tok m!"opaque {f.name} : {fieldType}"
  liftTermElabM $ addTermInfo' f.name_tok (mkConst f.name)
  f.multiplicity.elab s f

def Sig.Multiplicity.elab (s : Sig) (m : Sig.Multiplicity) : CommandElabM Unit := withRef s.name_tok do
  -- Every type ought to be inhabited
  elabCommand (← `(@[instance] axiom $(mkIdent $ s.name.underscored.appendBefore "inhabited_") : Inhabited $(mkIdent s.name)))
  -- Every type is finitely inhabited
  elabCommand (← `(@[instance] axiom $(mkIdent $ s.name.underscored.appendBefore "fintype_") : Fintype $(mkIdent s.name)))
  match m with
  | .one tok => withRef tok do
    elabCommand (← `(@[instance] axiom $(mkIdent $ s.name.underscored.appendBefore "one_") : SigQuantifier.One $(mkIdent s.name)))
    liftTermElabM $ addTermInfo' tok (mkConst $ s.name.underscored.appendBefore "one_")
  | .lone tok => withRef tok do
    logInfoAt tok m!"Lforge does not currently support the lone quantifier, since all types currently default to being inhabited. You might want to consider using `one` or `abstract` instead."
  | _ => return

def Sig.elab (s : Sig): CommandElabM Unit := withRef s.name_tok do
  let env ← getEnv
  match s.ancestor with
  | .none =>
    let sigDecl := Declaration.opaqueDecl {
      name := s.name,
      value := .sort levelZero,
      levelParams := [],
      type := .sort levelOne,
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
    -- Check if s.quantifier is a .one type
    match (s.quantifier, s.fields.isEmpty) with
    | (.one _, true) => do
      elabCommand (← `(noncomputable opaque $(mkIdent s.name) : $(mkIdent a)))
      elabCommand (← `(def $(mkIdent $ s.name.appendBefore "Is") : $(mkIdent a) → Prop := ($(mkIdent s.name) = .)))
      liftTermElabM $ addTermInfo' s.name_tok (mkConst s.name)
    | _ =>
      elabCommand (← `(opaque $(mkIdent $ s.name.appendBefore "Is") : $(mkIdent a) → Prop))
      let first_char := (s.name.getString!.get! 0).toString
      elabCommand (← `(@[reducible] def $(mkIdent $ s.name) : Type := { $(mkIdent first_char) : $(mkIdent a) // $(mkIdent $ s.name.appendBefore "Is") $(mkIdent first_char) }))
      s.quantifier.elab s
      liftTermElabM $ addTermInfo' s.name_tok (mkConst s.name)

/--
Toposort the sigs based on inheritance structure, based on Sig's ancestor field.
-/
def orderSigs (sigs : List Sig) : List Sig := do
  -- TODO: Current for loop deep recursion?
  let mut sigs := sigs
  let mut orderedSigs := []
  while sigs.length > 0 do
    let (ordered, unordered) := sigs.partition (λ s ↦ s.ancestor == .none ∨ orderedSigs.any (λ os ↦ os.name == s.ancestor))
    orderedSigs := orderedSigs ++ ordered
    sigs := unordered
  orderedSigs

/--
Gets a list of ⟨abstract_sig, list of children⟩ pairs.
-/
def getChildrenOfAbstract (sigs : List Sig) : List (Sig × List Sig) := do
  sigs.filterMap (λ s ↦
    match s.quantifier with
    | .abstract _ => some (s, sigs.filter (λ c ↦ c.ancestor == s.name))
    | _ => none)

/--
Adds `abstract_[sig] : ∀ [first character] : [sig], Is[ChildSig1] _ ∨ Is[ChildSig2] _`
-/
def processAbstractSigs (abstract_sigs : List (Sig × List Sig)) : CommandElabM Unit := do
  abstract_sigs.forM (λ ⟨s, children⟩ ↦ withRef s.name_tok do
  -- If there are no children, add an error to abstract tok
    if children.isEmpty then
      throwErrorAt s.name_tok m!"Abstract sig '{s.name}' has no children."
    else
      let childrenName ← children.mapM (λ c ↦ liftTermElabM $ mkConst $ c.name.appendBefore "Is")
      let binderName := (s.name.getString!.get! 0).toString.toLower
      let statement ← liftTermElabM $ withLocalDeclD binderName (mkConst s.name) (λ fvar ↦ do
          let orList ← childrenName.tail!.foldrM (λ c acc ↦
            mkAppM ``Or #[mkApp c fvar, acc])
            (mkApp childrenName.head! fvar)
          mkForallFVars #[fvar] orList)
      let name := (s.name.underscored.appendBefore "abstract_")
      let decl := Declaration.axiomDecl {
        name := name,
        levelParams := [],
        type := statement,
        isUnsafe := False,
      }
      -- Get every unique ordered pair of childs, then sets them all disjoint
      let pairs := children.foldl (λ acc c ↦
        acc ++ (children.filter (λ c' ↦ c'.name.toString ≠ c.name.toString)).map (λ c' ↦ (c, c'))) []
      pairs.forM (λ ⟨c1, c2⟩ ↦ do
        -- Makes the types (or units in case of `one`) different
        let identifier_name := mkIdent $ s!"disjoint_{s.name.toString}_{c1.name.toString}_{c2.name.toString}"
        elabCommand (← `(@[reducible,simp] axiom $(identifier_name) : $(mkIdent $ c1.name) ≠ $(mkIdent $ c2.name)))
        -- Makes their predicates different
        let identifier_name := mkIdent $ s!"disjoint_{s.name.toString}_Is{c1.name.toString}_Is{c2.name.toString}"
        let binder := mkIdent $ (s.name.toString.get! 0).toString.toLower
        elabCommand (← `(@[reducible,simp] axiom $(identifier_name) : ∀ $(binder) : $(mkIdent s.name), $(mkIdent $ c1.name.appendBefore "Is") $(binder) ∧ $(mkIdent $ c2.name.appendBefore "Is") $(binder) → False))
      )
      let env ← getEnv
      match env.addDecl decl with
      | Except.ok env => do
        if (← getOptions).getBool `forge.hints .false then
          logInfo m!"axiom {name} : {statement}"
        setEnv env
        match s.quantifier with
        | .abstract tok =>
          liftTermElabM $ addTermInfo' tok (mkConst name)
        | _ => unreachable!
      | Except.error ex =>
        throwError ex.toMessageData (← getOptions))

/--
We need to elaborate all top-level sigs before all fields can be elaborated,
so `Sig.lift_and_elab_multiple` will elab all Sigs and then all of their fields.
-/
def Sig.lift_and_elab_multiple (sigs : List Sig) : CommandElabM Unit := do
  (sigs |> orderSigs).forM Sig.elab
  processAbstractSigs (getChildrenOfAbstract sigs)
  sigs.forM (λ s ↦ s.fields.forM (Field.elab s))

end ForgeSyntax
