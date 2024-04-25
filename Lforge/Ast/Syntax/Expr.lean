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
syntax:100 "~" f_expr:100 : f_expr
/--
`^<expr>` returns the transitive closure of `<expr>`, assuming it is has arity 2. Attempting to apply `^` to a relation of different arity will produce an error. The transitive closure of a binary relation $r$ is defined as the _smallest_ relation $t$ such that:
- `r in t`; and
- for all `a`, `b`, and `c`, if `a->b` is in `t` and `b->c` is in `t`, then `a->c` is in `t`.

Informally, it is useful to think of `^r` as encoding _reachability_ using `r`. It is equivalent to the (unbounded and thus inexpressible in Forge) union: `r + r.r + r.r.r + r.r.r.r + ...`.
-/
syntax:100 "^" f_expr:100 : f_expr
/--
`*<expr>` returns the reflexive-transitive closure of `<expr>`, assuming it is has arity 2. Attempting to apply `*` to a relation of different arity will produce an error.

For a given 2-ary relation `r`, `*r` is equivalent to `^r + iden`.
-/
syntax:100 "*" f_expr:100 : f_expr

-- Binary operators
/--
`<expr-a> + <expr-b>` returns the **union** of the two exprs, i.e., the set containing all elements that are in either of the two exprs.
-/
syntax:60 f_expr:60 "+" f_expr:59 : f_expr
/--
`<expr-a> - <expr-b>` returns the **set difference** of the two exprs, i.e., everything in `expr-a` that is **not** also in `expr-b`.
-/
syntax:60 f_expr:60 "-" f_expr:59 : f_expr
/--
`<expr-a> & <expr-b>` returns the **intersection** of the two exprs, i.e., all elements in both `expr-a` and `expr-b`.
-/
syntax:75 f_expr:75 "&" f_expr:74 : f_expr
/--
`<expr-a> . <expr-b>` returns the **relational join** of the two exprs. It combines two relations by seeking out rows with common values in their rightmost and leftmost columns.
-/
syntax:95 f_expr:94 "." f_expr:95 : f_expr
/--
`<expr-a> -> <expr-b>` returns the **cross product** of the two exprs.
-/
syntax:80 f_expr:80 "->" f_expr:79 : f_expr

/--
`{<fmla> => <expr-a> else <expr-b>}` returns `<expr-a>` if `<fmla>` evaluates to true, and `<expr-b>` otherwise.
-/
syntax "if" f_fmla "then" f_expr "else" f_expr : f_expr
-- TODO: Alternative syntax?
-- TODO: Broken:
-- syntax f_fmla "=>" f_expr "else" f_expr : f_expr


/--
A set-comprehension expression `{x1: T1, ..., xn: Tn | <fmla>}` evaluates to a set of arity-n tuples. A tuple of objects `o1, ... on` is in the set if and only if `<fmla>` is satisfied when `x1` takes the value `o1`, etc.
-/
syntax "{" f_args "|" f_fmla "}" : f_expr

-- app
syntax:90 f_expr:90 "[" f_expr:90,* "]" : f_expr

-- literal
syntax ident : f_expr

-- let
syntax:15 "let" ident "=" f_expr "|" f_expr : f_expr

-- cast
/-
Note: This is custom syntax in Lforge to explicitly cast an expression to a particular type. This helps
move the Lean elaborator along and facilitates type coercions.
-/
/--
`x /* as P */` is a Lean type annotation `x` ought to have type `P`. In cases where Lean is having trouble unify Forge types, this can help move the elaborator along.

You can also chain casts, like if `x` is an element of type `K` and `K` is a child class of `P`. For example, `x /* as K, P → Prop */` casts `x` to type `P → Prop`.
-/
syntax:150 f_expr "/*" "as" term,+ "*/" : f_expr

-- parens
syntax:100 "(" f_expr ")" : f_expr

-- int literal
syntax num : f_expr
syntax "-" num : f_expr

-- count
syntax:65 "#" f_expr : f_expr

-- aggs
/--
`sing[<value>]`: returns an integer atom representing the given value
-/
syntax:91 "sing[" f_expr "]" : f_expr
/--
`sum[<atoms>]`: returns an integer value: the sum of the values that are represented by each of the int atoms in the set
-/
syntax:91 "sum[" f_expr "]" : f_expr
/--
`max[<atoms>]`: returns an integer value: the maximum of all the values represented by the int atoms in the set. Its behavior is undefined if the set is empty.
-/
syntax:91 "max[" f_expr "]" : f_expr
/--
`min[<atoms>]`: returns an integer value: the minimum of all the values represented by the int atoms in the set. Its behavior is undefined if the set is empty.
-/
syntax:91 "min[" f_expr "]" : f_expr

-- sum
syntax:15 "sum" ident ":" f_expr "|" "{" f_expr "}" : f_expr
syntax:15 "sum" ident ":" f_expr "|" f_expr : f_expr

-- int unop
/--
`abs[<value>]`: returns the absolute value of `value`
-/
syntax:91 "abs[" f_expr "]" : f_expr
/--
`sign[<value>]`: returns 1 if `value` is > 0, 0 if `value` is 0, and -1 if `value` is < 0
-/
syntax:91 "sign[" f_expr "]" : f_expr

-- int mul-ops
/--
`add[<value-a>, <value-b> ...]`: returns the value of the sum `value-a` + `value-b` + ...
-/
syntax:91 "add[" f_expr,+ "]" : f_expr
/--
`subtract[<value-a>, <value-a> ...]`: returns the value of the difference `value-a` - `value-b` - ...
-/
syntax:91 "subtract[" f_expr,+ "]" : f_expr
/--
`multiply[<value-a>, <value-b> ...]`: returns the value of the product `value-a` \* `value-b` \* ...
-/
syntax:91 "multiply[" f_expr,+ "]" : f_expr
/--
`divide[<value-a>, <value-b> ...]`: returns the value of the left-associative integer quotient (`value-a` / `value-b`) / ...
-/
syntax:91 "divide[" f_expr,+ "]" : f_expr
/--
`remainder[<value-a>, <value-b>]`: returns the remainder for doing integer division. Note that if `value-a` is negative, the result will also be negative, and that integer wrap-around may affect the answer.
-/
syntax:91 "remainder[" f_expr "," f_expr "]" : f_expr

end ForgeSyntax
