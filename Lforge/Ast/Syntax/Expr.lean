import Lforge.Ast.Syntax.Common

namespace ForgeSyntax

/-
We're following the Alloy precedence and associativity rules described here:
https://alloytools.org/spec.html

All Expression operators have precedence >50,
all Formula operators have precedence 10-49
-/

-- TODO: documentation

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


-- int literal
syntax num : f_expr
syntax "-" num : f_expr

-- count
syntax:65 "#" f_expr:65 : f_expr

-- aggs
syntax:91 "sing[" f_expr:91 "]" : f_expr
syntax:91 "sum[" f_expr:91 "]" : f_expr
syntax:91 "max[" f_expr:91 "]" : f_expr
syntax:91 "min[" f_expr:91 "]" : f_expr

-- sum
syntax:15 "sum" ident ":" f_expr "|" "{" f_expr:15 "}" : f_expr
syntax:15 "sum" ident ":" f_expr "|" f_expr:15 : f_expr

-- int unop
syntax:91 "abs[" f_expr:91 "]" : f_expr
syntax:91 "sign[" f_expr:91 "]" : f_expr

-- int mul-ops
syntax:91 "add[" f_expr:91,+ "]" : f_expr
syntax:91 "subtract[" f_expr:91,+ "]" : f_expr
syntax:91 "multiply[" f_expr:91,+ "]" : f_expr
syntax:91 "divide[" f_expr:91,+ "]" : f_expr
syntax:91 "remainder[" f_expr:91 "," f_expr:91 "]" : f_expr

end ForgeSyntax
