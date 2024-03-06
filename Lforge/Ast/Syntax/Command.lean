import Lforge.Ast.Syntax.Sig
import Lforge.Ast.Syntax.Pred
import Lforge.Ast.Syntax.Fun

namespace ForgeSyntax

declare_syntax_cat f_command
syntax f_sig : f_command
syntax f_pred : f_command
syntax f_fun : f_command

declare_syntax_cat f_program
syntax f_command+ : f_program

end ForgeSyntax
