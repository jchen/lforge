import Lforge.Ast.Types
import Lforge.Ast.Syntax.Sig
open Lean Elab
set_option autoImplicit false

namespace ForgeSyntax

def Sig.Multiplicity.of_syntax (stx : TSyntax `forge_sig_multiplicity) : MetaM Sig.Multiplicity :=
  match stx with
  | `(forge_sig_multiplicity| one) => return .one stx
  | `(forge_sig_multiplicity| lone) => return .lone stx
  | `(forge_sig_multiplicity| abstract) => return .abstract stx
  | _ => throwUnsupportedSyntax

def Field.Multiplicity.of_syntax (stx : TSyntax `forge_field_multiplicity) : MetaM Field.Multiplicity :=
  match stx with
  | `(forge_field_multiplicity| one) => return .one stx
  | `(forge_field_multiplicity| lone) => return .lone stx
  | `(forge_field_multiplicity| pfunc) => return .pfunc stx
  | `(forge_field_multiplicity| func) => return .func stx
  | `(forge_field_multiplicity| set) => return .set stx
  | _ => throwUnsupportedSyntax

def Field.of_syntax (stx : TSyntax `forge_field) : MetaM (List Field) :=
  match stx with
  | `(forge_field| $names:ident,* : $multiplicity:forge_field_multiplicity $type:ident->*) => do
    names.getElems.toList.mapM (λ name : TSyntax `ident ↦ do
    let multiplicity ← Field.Multiplicity.of_syntax multiplicity
    pure { name := name.getId, name_tok := name, multiplicity := multiplicity, type := type.getElems.toList.map (λ i ↦ i.getId), tok := stx })
  | _ => throwUnsupportedSyntax

def Sig.of_syntax : TSyntax `forge_sig → MetaM (List Sig)
  -- Bare sig
  | `(forge_sig| $quantifier:forge_sig_multiplicity ? sig $names:ident,* { $fields:forge_field,* }) => do
    names.getElems.toList.mapM ( λ name ↦ do
    let quantifier ← match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => pure .unquantified
    let fields ← (← fields.getElems.toList.mapM Field.of_syntax).foldlM (λ acc elt ↦ return elt ++ acc) []
    pure { quantifier := quantifier, name := name.getId, name_tok := name, ancestor := none, fields := fields })
  -- Sig with ancestor
  | `(forge_sig| $quantifier:forge_sig_multiplicity ? sig $names:ident,* extends $ancestor:ident { $fields:forge_field,* }) => do
    names.getElems.toList.mapM ( λ name ↦ do
    let quantifier ← match quantifier with
      | some q => Sig.Multiplicity.of_syntax q
      | none => pure .unquantified
    let fields ← (← fields.getElems.toList.mapM Field.of_syntax).foldlM (λ acc elt ↦ return elt ++ acc) []
    pure { quantifier := quantifier, name := name.getId, name_tok := name, ancestor := some ancestor.getId, fields := fields })
  | _ => throwUnsupportedSyntax

end ForgeSyntax
