import Lforge.Ast.Syntax.Common

namespace ForgeSyntax

/-
We're following the Alloy precedence and associativity rules described here:
https://alloytools.org/spec.html

All Expression operators have precedence >50,
all Formula operators have precedence 10-49

Docstrings here serve to document the syntax, as well as to provide tooltips on syntax hover.
-/

-- Unary operators
/--
`~<expr>` returns the transpose of `<expr>`, assuming it is has arity 2. (Attempting to use transpose on a different-arity relation will produce an error.)
-/
syntax:100 "~" forge_expr:100 : forge_expr
/--
`^<expr>` returns the transitive closure of `<expr>`, assuming it is has arity 2. Attempting to apply `^` to a relation of different arity will produce an error. The transitive closure of a binary relation $r$ is defined as the _smallest_ relation $t$ such that:
- `r in t`; and
- for all `a`, `b`, and `c`, if `a->b` is in `t` and `b->c` is in `t`, then `a->c` is in `t`.

Informally, it is useful to think of `^r` as encoding _reachability_ using `r`. It is equivalent to the (unbounded and thus inexpressible in Forge) union: `r + r.r + r.r.r + r.r.r.r + ...`.
-/
syntax:100 "^" forge_expr:100 : forge_expr
/--
`*<expr>` returns the reflexive-transitive closure of `<expr>`, assuming it is has arity 2. Attempting to apply `*` to a relation of different arity will produce an error.

For a given 2-ary relation `r`, `*r` is equivalent to `^r + iden`.
-/
syntax:100 "*" forge_expr:100 : forge_expr

-- Binary operators
/--
`<expr-a> + <expr-b>` returns the **union** of the two exprs, i.e., the set containing all elements that are in either of the two exprs.
-/
syntax:60 forge_expr:60 "+" forge_expr:59 : forge_expr
/--
`<expr-a> - <expr-b>` returns the **set difference** of the two exprs, i.e., everything in `expr-a` that is **not** also in `expr-b`.
-/
syntax:60 forge_expr:60 "-" forge_expr:59 : forge_expr
/--
`<expr-a> & <expr-b>` returns the **intersection** of the two exprs, i.e., all elements in both `expr-a` and `expr-b`.
-/
syntax:75 forge_expr:75 "&" forge_expr:74 : forge_expr
/--
`<expr-a> . <expr-b>` returns the **relational join** of the two exprs. It combines two relations by seeking out rows with common values in their rightmost and leftmost columns.
-/
syntax:95 forge_expr:94 "." forge_expr:95 : forge_expr
/--
`<expr-a> -> <expr-b>` returns the **cross product** of the two exprs.
-/
syntax:80 forge_expr:80 "->" forge_expr:79 : forge_expr

/--
`{<fmla> => <expr-a> else <expr-b>}` returns `<expr-a>` if `<fmla>` evaluates to true, and `<expr-b>` otherwise.
-/
syntax "if" forge_fmla "then" forge_expr "else" forge_expr : forge_expr
-- TODO: Alternative syntax?
-- TODO: Broken:
-- syntax forge_fmla "=>" forge_expr "else" forge_expr : forge_expr


/--
A set-comprehension expression `{x1: T1, ..., xn: Tn | <fmla>}` evaluates to a set of arity-n tuples. A tuple of objects `o1, ... on` is in the set if and only if `<fmla>` is satisfied when `x1` takes the value `o1`, etc.
-/
syntax "{" forge_args "|" forge_fmla "}" : forge_expr

-- app
syntax:90 forge_expr:90 "[" forge_expr:90,* "]" : forge_expr

-- literal
syntax ident : forge_expr

-- let
syntax:15 "let" ident "=" forge_expr "|" forge_expr : forge_expr

-- cast
/-
Note: This is custom syntax in Lforge to explicitly cast an expression to a particular type. This helps
move the Lean elaborator along and facilitates type coercions.
-/
/--
`x /* as P */` is a Lean type annotation `x` ought to have type `P`. In cases where Lean is having trouble unify Forge types, this can help move the elaborator along.

You can also chain casts, like if `x` is an element of type `K` and `K` is a child class of `P`. For example, `x /* as K, P → Prop */` casts `x` to type `P → Prop`.
-/
syntax:150 forge_expr "/*" "as" term,+ "*/" : forge_expr

-- parens
syntax:100 "(" forge_expr ")" : forge_expr

-- int literal
syntax num : forge_expr
syntax "-" num : forge_expr

-- count
syntax:65 "#" forge_expr : forge_expr

-- aggs
/--
`sing[<value>]`: returns an integer atom representing the given value
-/
syntax:91 "sing[" forge_expr "]" : forge_expr
/--
`sum[<atoms>]`: returns an integer value: the sum of the values that are represented by each of the int atoms in the set
-/
syntax:91 "sum[" forge_expr "]" : forge_expr
/--
`max[<atoms>]`: returns an integer value: the maximum of all the values represented by the int atoms in the set. Its behavior is undefined if the set is empty.
-/
syntax:91 "max[" forge_expr "]" : forge_expr
/--
`min[<atoms>]`: returns an integer value: the minimum of all the values represented by the int atoms in the set. Its behavior is undefined if the set is empty.
-/
syntax:91 "min[" forge_expr "]" : forge_expr

-- sum
syntax:15 "sum" ident ":" forge_expr "|" "{" forge_expr "}" : forge_expr
syntax:15 "sum" ident ":" forge_expr "|" forge_expr : forge_expr

-- int unop
/--
`abs[<value>]`: returns the absolute value of `value`
-/
syntax:91 "abs[" forge_expr "]" : forge_expr
/--
`sign[<value>]`: returns 1 if `value` is > 0, 0 if `value` is 0, and -1 if `value` is < 0
-/
syntax:91 "sign[" forge_expr "]" : forge_expr

-- int mul-ops
/--
`add[<value-a>, <value-b> ...]`: returns the value of the sum `value-a` + `value-b` + ...
-/
syntax:91 "add[" forge_expr,+ "]" : forge_expr
/--
`subtract[<value-a>, <value-a> ...]`: returns the value of the difference `value-a` - `value-b` - ...
-/
syntax:91 "subtract[" forge_expr,+ "]" : forge_expr
/--
`multiply[<value-a>, <value-b> ...]`: returns the value of the product `value-a` \* `value-b` \* ...
-/
syntax:91 "multiply[" forge_expr,+ "]" : forge_expr
/--
`divide[<value-a>, <value-b> ...]`: returns the value of the left-associative integer quotient (`value-a` / `value-b`) / ...
-/
syntax:91 "divide[" forge_expr,+ "]" : forge_expr
/--
`remainder[<value-a>, <value-b>]`: returns the remainder for doing integer division. Note that if `value-a` is negative, the result will also be negative, and that integer wrap-around may affect the answer.
-/
syntax:91 "remainder[" forge_expr "," forge_expr "]" : forge_expr

end ForgeSyntax
