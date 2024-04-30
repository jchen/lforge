import Lforge.Ast.Syntax.Common

namespace ForgeSyntax

-- argument
syntax ident,+ ":" forge_expr : forge_arg
-- arguments
syntax forge_arg,* : forge_args

/--
`! <fmla>`: **true** when `<fmla>` evaluates to **false**. Can also be written as `not`. Produces `¬ <fmla>`.
-/
syntax:40 "!" forge_fmla:40 : forge_fmla
/--
`not <fmla>`: **true** when `<fmla>` evaluates to **false**. Can also be written as `!`. Produces `¬ <fmla>`.
-/
syntax:40 "not" forge_fmla:40 : forge_fmla

/--
`<fmla-a> && <fmla-b>`: **true** when both `<fmla-a>` and `<fmla-b>` evaluate to **true**. Can also be written as `and`. Produces `<fmla-a> ∧ <fmla-b>`.
-/
syntax:35 forge_fmla:35 "&&" forge_fmla:34 : forge_fmla

/--
`<fmla-a> and <fmla-b>`: **true** when both `<fmla-a>` and `<fmla-b>` evaluate to **true**. Can also be written as `&&`. Produces `<fmla-a> ∧ <fmla-b>`.
-/
syntax:35 forge_fmla:35 "and" forge_fmla:34 : forge_fmla

/--
`<fmla-a> || <fmla-b>`: **true** when either `<fmla-a>` or `<fmla-b>` evaluates to **true**. Can also be written as `or`. Produces `<fmla-a> ∨ <fmla-b>`.
-/
syntax:20 forge_fmla:20 "||" forge_fmla:19 : forge_fmla

/--
`<fmla-a> or <fmla-b>`: **true** when either `<fmla-a>` is **true** or `<fmla-b>` evaluates to **true**. Can also be written as `||`. Produces `<fmla-a> ∨ <fmla-b>`.
-/
syntax:20 forge_fmla:20 "or" forge_fmla:19 : forge_fmla

/--
`<fmla-a> => <fmla-b>`: **true** when either `<fmla-a>` evaluates to **false** or `<fmla-b>` evaluates to **true**. Can also be written as `implies`. Produces `<fmla-a> → <fmla-b>`.
-/
syntax:30 forge_fmla:30 "=>" forge_fmla:29 : forge_fmla

/--
`<fmla-a> implies <fmla-b>`: **true** when either `<fmla-a>` evaluates to **false** or `<fmla-b>` evaluates to **true**. Can also be written as `=>`. Produces `<fmla-a> → <fmla-b>`.
-/
syntax:30 forge_fmla:30 "implies" forge_fmla:29 : forge_fmla

/--
`<fmla-a> <=> <fmla-b>`: **true** when `<fmla-a>` evaluates to **true** exactly when `<fmla-b>` evaluates to **true**. Can also be written as `iff`. Produces `<fmla-a> ↔ <fmla-b>`.
-/
syntax:25 forge_fmla:25 "<=>" forge_fmla:24 : forge_fmla

/--
`<fmla-a> iff <fmla-b>`: **true** when `<fmla-a>` evaluates to **true** exactly when `<fmla-b>` evaluates to **true**. Can also be written as `<=>`. Produces `<fmla-a> ↔ <fmla-b>`.
-/
syntax:25 forge_fmla:25 "iff" forge_fmla:24 : forge_fmla

/-- `some <expr>`: true when `<expr>` contains **at least one** element -/
syntax:55 "some" forge_expr:55 : forge_fmla
/-- `no <expr>`: true when `<expr>` is **empty** -/
syntax:55 "no" forge_expr:55 : forge_fmla
/-- `lone <expr>`: true when `<expr>` contains **zero or one** elements -/
syntax:55 "lone" forge_expr:55 : forge_fmla
/-- `one <expr>`: true when `<expr>` contains **exactly one** element -/
syntax:55 "one" forge_expr:55 : forge_fmla

/--
`<expr-a> in <expr-b>`: true when `<expr-a>` is a **subset** of or equal to `<expr-b>`.
-/
syntax:50 forge_expr:50 "in" forge_expr:50 : forge_fmla
/--
`<expr-a> not in <expr-b>`: true when `<expr-a>` is not a **subset** of or equal to `<expr-b>`.
-/
syntax:50 forge_expr:50 "not in" forge_expr:50 : forge_fmla
/--
`<expr-a> !in <expr-b>`: true when `<expr-a>` is not a **subset** of or equal to `<expr-b>`.
-/
syntax:50 forge_expr:50 "!in" forge_expr:50 : forge_fmla

/--
`<expr-a> = <expr-b>`: true when `<expr-a>` and `<expr-b>` contain exactly the **same elements**.
-/
syntax:50 forge_expr:50 "=" forge_expr:50 : forge_fmla
/--
`<expr-a> != <expr-b>`: true when `<expr-a>` and `<expr-b>` contain **different elements**. In other words, when `<expr-a> = <expr-b>` is **false**.
-/
syntax:50 forge_expr:50 "!=" forge_expr:50 : forge_fmla

-- Number operators
syntax:50 forge_expr:50 "<" forge_expr:50 : forge_fmla
syntax:50 forge_expr:50 "<=" forge_expr:50 : forge_fmla
syntax:50 forge_expr:50 ">" forge_expr:50 : forge_fmla
syntax:50 forge_expr:50 ">=" forge_expr:50 : forge_fmla

-- implies-else
/--
`<fmla-a> => <fmla-b> else <fmla-c>`: **true** when `<fmla-a>` evaluates to **true** and `<fmla-b>` evaluates to **true**, or `<fmla-a>` evaluates to **false** and `<fmla-c>` evaluates to **true**. Produces `<fmla-a> → <fmla-b> ∧ ¬ <fmla-a> → <fmla-c>`.
-/
syntax:30 forge_fmla:30 "=>" forge_fmla "else" forge_fmla : forge_fmla
/--
`<fmla-a> implies <fmla-b> else <fmla-c>`: **true** when `<fmla-a>` evaluates to **true** and `<fmla-b>` evaluates to **true**, or `<fmla-a>` evaluates to **false** and `<fmla-c>` evaluates to **true**. Produces `<fmla-a> → <fmla-b> ∧ ¬ <fmla-a> → <fmla-c>`.
-/
syntax:30 forge_fmla:30 "implies" forge_fmla "else" forge_fmla : forge_fmla

-- TODO: add documentation to all the following syntax
declare_syntax_cat forge_fmla_quantifier
syntax:15 "no" : forge_fmla_quantifier
syntax:15 "lone" : forge_fmla_quantifier
syntax:15 "one" : forge_fmla_quantifier
syntax:15 "some" : forge_fmla_quantifier
syntax:15 "all" : forge_fmla_quantifier

-- syntax:15 forge_fmla_quantifier forge_args "|" "{" forge_fmla:15 "}" : forge_fmla
syntax:15 forge_fmla_quantifier forge_args "|" forge_fmla : forge_fmla

-- literals
syntax ident : forge_fmla

-- predicate application
syntax ident "[" forge_expr,* "]" : forge_fmla

-- let
syntax:15 "let" ident "=" forge_expr "|" forge_fmla:15 : forge_fmla

-- parens
syntax:100 "(" forge_fmla ")" : forge_fmla
syntax:100 "{" forge_fmla+ "}" : forge_fmla

-- boolean literals
syntax "true" : forge_fmla
syntax "false" : forge_fmla

end ForgeSyntax
