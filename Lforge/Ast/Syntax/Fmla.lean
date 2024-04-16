import Lforge.Ast.Syntax.Common

namespace ForgeSyntax

-- argument
syntax ident,+ ":" f_expr : f_arg
-- arguments
syntax f_arg,* : f_args

/--
`! <fmla>`: **true** when `<fmla>` evaluates to **false**. Can also be written as `not`. Produces `¬ <fmla>`.
-/
syntax:40 "!" f_fmla:40 : f_fmla
/--
`not <fmla>`: **true** when `<fmla>` evaluates to **false**. Can also be written as `!`. Produces `¬ <fmla>`.
-/
syntax:40 "not" f_fmla:40 : f_fmla

/--
`<fmla-a> && <fmla-b>`: **true** when both `<fmla-a>` and `<fmla-b>` evaluate to **true**. Can also be written as `and`. Produces `<fmla-a> ∧ <fmla-b>`.
-/
syntax:35 f_fmla:35 "&&" f_fmla:34 : f_fmla

/--
`<fmla-a> and <fmla-b>`: **true** when both `<fmla-a>` and `<fmla-b>` evaluate to **true**. Can also be written as `&&`. Produces `<fmla-a> ∧ <fmla-b>`.
-/
syntax:35 f_fmla:35 "and" f_fmla:34 : f_fmla

/--
`<fmla-a> || <fmla-b>`: **true** when either `<fmla-a>` or `<fmla-b>` evaluates to **true**. Can also be written as `or`. Produces `<fmla-a> ∨ <fmla-b>`.
-/
syntax:20 f_fmla:20 "||" f_fmla:19 : f_fmla

/--
`<fmla-a> or <fmla-b>`: **true** when either `<fmla-a>` is **true** or `<fmla-b>` evaluates to **true**. Can also be written as `||`. Produces `<fmla-a> ∨ <fmla-b>`.
-/
syntax:20 f_fmla:20 "or" f_fmla:19 : f_fmla

/--
`<fmla-a> => <fmla-b>`: **true** when either `<fmla-a>` evaluates to **false** or `<fmla-b>` evaluates to **true**. Can also be written as `implies`. Produces `<fmla-a> → <fmla-b>`.
-/
syntax:30 f_fmla:30 "=>" f_fmla:29 : f_fmla

/--
`<fmla-a> implies <fmla-b>`: **true** when either `<fmla-a>` evaluates to **false** or `<fmla-b>` evaluates to **true**. Can also be written as `=>`. Produces `<fmla-a> → <fmla-b>`.
-/
syntax:30 f_fmla:30 "implies" f_fmla:29 : f_fmla

/--
`<fmla-a> <=> <fmla-b>`: **true** when `<fmla-a>` evaluates to **true** exactly when `<fmla-b>` evaluates to **true**. Can also be written as `iff`. Produces `<fmla-a> ↔ <fmla-b>`.
-/
syntax:25 f_fmla:25 "<=>" f_fmla:24 : f_fmla

/--
`<fmla-a> iff <fmla-b>`: **true** when `<fmla-a>` evaluates to **true** exactly when `<fmla-b>` evaluates to **true**. Can also be written as `<=>`. Produces `<fmla-a> ↔ <fmla-b>`.
-/
syntax:25 f_fmla:25 "iff" f_fmla:24 : f_fmla

/-- `some <expr>`: true when `<expr>` contains **at least one** element -/
syntax:55 "some" f_expr:55 : f_fmla
/-- `no <expr>`: true when `<expr>` is **empty** -/
syntax:55 "no" f_expr:55 : f_fmla
/-- `lone <expr>`: true when `<expr>` contains **zero or one** elements -/
syntax:55 "lone" f_expr:55 : f_fmla
/-- `one <expr>`: true when `<expr>` contains **exactly one** element -/
syntax:55 "one" f_expr:55 : f_fmla

/--
`<expr-a> in <expr-b>`: true when `<expr-a>` is a **subset** of or equal to `<expr-b>`.
-/
syntax:50 f_expr:50 "in" f_expr:50 : f_fmla
/--
`<expr-a> not in <expr-b>`: true when `<expr-a>` is not a **subset** of or equal to `<expr-b>`.
-/
syntax:50 f_expr:50 "not in" f_expr:50 : f_fmla
/--
`<expr-a> !in <expr-b>`: true when `<expr-a>` is not a **subset** of or equal to `<expr-b>`.
-/
syntax:50 f_expr:50 "!in" f_expr:50 : f_fmla

/--
`<expr-a> = <expr-b>`: true when `<expr-a>` and `<expr-b>` contain exactly the **same elements**.
-/
syntax:50 f_expr:50 "=" f_expr:50 : f_fmla
/--
`<expr-a> != <expr-b>`: true when `<expr-a>` and `<expr-b>` contain **different elements**. In other words, when `<expr-a> = <expr-b>` is **false**.
-/
syntax:50 f_expr:50 "!=" f_expr:50 : f_fmla

-- Number operators
syntax:50 f_expr:50 "<" f_expr:50 : f_fmla
syntax:50 f_expr:50 "<=" f_expr:50 : f_fmla
syntax:50 f_expr:50 ">" f_expr:50 : f_fmla
syntax:50 f_expr:50 ">=" f_expr:50 : f_fmla

-- implies-else
/--
`<fmla-a> => <fmla-b> else <fmla-c>`: **true** when `<fmla-a>` evaluates to **true** and `<fmla-b>` evaluates to **true**, or `<fmla-a>` evaluates to **false** and `<fmla-c>` evaluates to **true**. Produces `<fmla-a> → <fmla-b> ∧ ¬ <fmla-a> → <fmla-c>`.
-/
syntax:30 f_fmla:30 "=>" f_fmla "else" f_fmla : f_fmla
/--
`<fmla-a> implies <fmla-b> else <fmla-c>`: **true** when `<fmla-a>` evaluates to **true** and `<fmla-b>` evaluates to **true**, or `<fmla-a>` evaluates to **false** and `<fmla-c>` evaluates to **true**. Produces `<fmla-a> → <fmla-b> ∧ ¬ <fmla-a> → <fmla-c>`.
-/
syntax:30 f_fmla:30 "implies" f_fmla "else" f_fmla : f_fmla

-- TODO: add documentation to all the following syntax
declare_syntax_cat f_fmla_quantifier
syntax:15 "no" : f_fmla_quantifier
syntax:15 "lone" : f_fmla_quantifier
syntax:15 "one" : f_fmla_quantifier
syntax:15 "some" : f_fmla_quantifier
syntax:15 "all" : f_fmla_quantifier

-- syntax:15 f_fmla_quantifier f_args "|" "{" f_fmla:15 "}" : f_fmla
syntax:15 f_fmla_quantifier f_args "|" f_fmla : f_fmla

-- literals
syntax ident : f_fmla

-- predicate application
syntax ident "[" f_expr,* "]" : f_fmla

-- let
syntax:15 "let" ident "=" f_expr "|" f_fmla:15 : f_fmla

-- parens
syntax:100 "(" f_fmla ")" : f_fmla
syntax:100 "{" f_fmla+ "}" : f_fmla

-- boolean literals
syntax "true" : f_fmla
syntax "false" : f_fmla

end ForgeSyntax
