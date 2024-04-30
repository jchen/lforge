import Lforge.Ast.Syntax.Common
import Lforge.Ast.Syntax.Sig

namespace ForgeSyntax

declare_syntax_cat forge_fun

syntax "fun" ident "[" forge_args "]" ":" (forge_field_multiplicity)? forge_expr "{" forge_expr "}" : forge_fun

end ForgeSyntax
