import Lforge.Ast.Syntax.Common
import Lforge.Ast.Syntax.Sig

namespace ForgeSyntax

declare_syntax_cat f_fun

syntax "fun" ident "[" f_args "]" ":" (f_field_multiplicity)? f_expr "{" f_expr "}" : f_fun

end ForgeSyntax
