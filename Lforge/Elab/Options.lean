import Lean

namespace ForgeSyntax

register_option forge.hints : Bool := {
  defValue := Bool.false
  descr := "Provides hints to generated definitions from Forge."
}

register_option forge.dot_join : Bool := {
  defValue := Bool.true
  descr := "Expands use of dots within Forge to represent a 'join' and not a scoping."
}

end ForgeSyntax
