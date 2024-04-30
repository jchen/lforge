import Lforge.Ast.Syntax.Sig
import Lforge.Ast.Syntax.Pred
import Lforge.Ast.Syntax.Fun

namespace ForgeSyntax

-- Check blocks
declare_syntax_cat forge_check
syntax "check" forge_fmla : forge_check
syntax "check" forge_fmla "for" (num ident),+ : forge_check

-- Commands
declare_syntax_cat forge_command
syntax forge_sig : forge_command
syntax forge_pred : forge_command
syntax forge_fun : forge_command
/--
Lforge does not support 'check' blocks (it is unable to execute specifications or automatically search for counterexamples). You might wish to prove your property as a theorem instead.

For example, if `Fact` is predicate you wish to prove, you should define a theorem like:
```
theorem check : Fact := by
  sorry
  done
```
-/
syntax forge_check : forge_command

-- Program (sequence of commands)
declare_syntax_cat forge_program
syntax forge_command+ : forge_program

end ForgeSyntax
