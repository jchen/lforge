import Lforge.Ast.Types
import Lforge.Ast.Syntax.Sig
open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

def Sig.Multiplicity.of_syntax (stx : TSyntax `f_sig_multiplicity) : MetaM Sig.Multiplicity :=
  match stx with
  | `(f_sig_multiplicity| one) => return .one stx
  | `(f_sig_multiplicity| lone) => return .lone stx
  | `(f_sig_multiplicity| abstract) => return .abstract stx
  | _ => throwUnsupportedSyntax

def Field.Multiplicity.of_syntax (stx : TSyntax `f_field_multiplicity) : MetaM Field.Multiplicity :=
  match stx with
  | `(f_field_multiplicity| one) => return .one stx
  | `(f_field_multiplicity| lone) => return .lone stx
  | `(f_field_multiplicity| pfunc) => return .pfunc stx
  | `(f_field_multiplicity| func) => return .func stx
  | `(f_field_multiplicity| set) => return .set stx
  | _ => throwUnsupportedSyntax

def Field.of_syntax : TSyntax `f_field → MetaM Field
  | `(f_field| $name:ident : $multiplicity:f_field_multiplicity $type:ident->*) => do
    let multiplicity ← Field.Multiplicity.of_syntax multiplicity
    pure { name := name.getId, name_tok := name, multiplicity := multiplicity, type := type.getElems.toList.map (λ i ↦ i.getId) }
  | _ => throwUnsupportedSyntax

def Sig.of_syntax : TSyntax `f_sig → MetaM Sig
  -- Bare sig
  | `(f_sig| $quantifier:f_sig_multiplicity ? sig $name:ident { $fields:f_field,* }) => do
    let quantifier ← match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => pure .unquantified
    let fields ← fields.getElems.toList.mapM Field.of_syntax
    pure { quantifier := quantifier, name := name.getId, name_tok := name, ancestor := none, fields := fields }
  -- Sig with ancestor
  | `(f_sig| $quantifier:f_sig_multiplicity ? sig $name:ident extends $ancestor:ident { $fields:f_field,* }) => do
    let quantifier ← match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => pure .unquantified
    let fields ← fields.getElems.toList.mapM Field.of_syntax
    pure { quantifier := quantifier, name := name.getId, name_tok := name, ancestor := some ancestor.getId, fields := fields }
  | _ => throwUnsupportedSyntax

end ForgeSyntax
