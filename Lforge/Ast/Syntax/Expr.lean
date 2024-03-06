import Lforge.Ast.Syntax.Common

namespace ForgeSyntax

/-
We're following the Alloy precedence and associativity rules described here:
https://alloytools.org/spec.html

All Expression operators have precedence >50,
all Formula operators have precedence 10-49
-/

-- Unary operators
syntax:100 "~" f_expr:100 : f_expr
syntax:100 "^" f_expr:100 : f_expr
syntax:100 "*" f_expr:100 : f_expr

-- Binary operators
syntax:60 f_expr:60 "+" f_expr:59 : f_expr
syntax:60 f_expr:60 "-" f_expr:59 : f_expr
syntax:75 f_expr:75 "&" f_expr:74 : f_expr
syntax:95 f_expr:94 "." f_expr:95 : f_expr
syntax:80 f_expr:80 "->" f_expr:79 : f_expr

-- if-then-else
syntax "if" f_fmla "then" f_expr "else" f_expr : f_expr

-- set comprehension
syntax "{" f_args "|" f_fmla "}" : f_expr

-- app
syntax:90 f_expr:90 "[" f_expr:90,* "]" : f_expr

-- literal
syntax ident : f_expr

-- let
syntax "let" ident "=" f_expr "|" f_expr : f_expr

-- parens
syntax "(" f_expr ")" : f_expr

end ForgeSyntax
