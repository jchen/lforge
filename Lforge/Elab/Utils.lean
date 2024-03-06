import Lean
import Lforge.Ast.Types
import Lforge.Elab.Options
open Lean Elab Meta Command Term System

set_option autoImplicit false

namespace ForgeSyntax

/--
Constructs an arrow type from a list, allows for `opaque` definitions.
-/
def arrowTypeOfList (types : List Symbol) : TermElabM Expr := do
  match types with
  | [] =>
    -- Prop
    pure (mkSort levelZero)
    -- α → β → ... → Prop
  | type :: rest =>
    mkArrow (mkConst type) (← arrowTypeOfList rest)

/--
Constructs an arrow type from a list, with named variables. Used in Pred elaborator.
-/
def namedArrowTypeOfList (types : List (Symbol × Symbol)) : TermElabM Expr := do
  match types with
  | [] =>
    -- Prop
    pure (mkSort levelZero)
    -- α → β → ... → Prop
  | ⟨name, type⟩ :: rest =>
    return .forallE name (mkConst type) (← namedArrowTypeOfList rest) .default

/--
Constructs an arrow value from a list (ending in → Prop), allows for `opaque` definitions.
Just returns α → β → ... → True
-/
def arrowValueOfList (types : List Symbol) : TermElabM Expr := do
  match types with
  | [] =>
    -- Prop
    pure (mkConst `True)
  | type :: rest =>
    -- α → β → ... → Prop
    pure (.lam .anonymous (mkConst type) (← arrowValueOfList rest) .default)

end ForgeSyntax
