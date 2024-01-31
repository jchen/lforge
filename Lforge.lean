import Lforge.Elab
import Lforge.Utils
import Lean

open Lean Elab Command Term Meta

syntax (name := lang_forge) "#lang forge" : command

@[command_elab lang_forge]
def lang_forge_impl : CommandElab := fun _ => do
  return ()

syntax (name := lang_forge_bsl) "#lang forge/bsl" : command

@[command_elab lang_forge_bsl]
def lang_forge_bsl_impl : CommandElab := fun stx => do
  logInfoAt stx "Froglet is not yet supported. Certain functions such as `reachable` might not be available. Use `#lang forge` to dismiss this message."
