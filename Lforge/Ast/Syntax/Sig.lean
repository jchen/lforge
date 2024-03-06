/-
Forge syntax for **fields** and **sigs**.
-/

namespace ForgeSyntax

/- TODO: Documentation -/
declare_syntax_cat f_sig_multiplicity
syntax "one" : f_sig_multiplicity
syntax "lone" : f_sig_multiplicity
syntax "abstract" : f_sig_multiplicity

/- TODO: Documentation-/
declare_syntax_cat f_field_multiplicity
syntax "one" : f_field_multiplicity
syntax "lone" : f_field_multiplicity
syntax "pfunc" : f_field_multiplicity
syntax "func" : f_field_multiplicity
syntax "set" : f_field_multiplicity

declare_syntax_cat f_field
/--
### Fields
Fields allow us to define relationships between a given `sig`s and other components of our model. Each _field_ in a `sig` has:

- a _**name**_ for the field;
- a _**multiplicity**_ (`one`, `lone`, `pfunc`, `func`, or, in Relational or Temporal Forge, `set`);
- a _**type**_ (a `->` separated list of `sig` names).

Here is a sig that defines the a `Person` type with a `bestFriend` field:
```
sig Person {
    bestFriend: lone Person
}
```
The `lone` multiplicity says that the field may contain at most one atom. (Note that this example has yet to express the constraint that everyone has a friend!)
-/
syntax ident ":" f_field_multiplicity sepBy1(ident, " -> ") : f_field

declare_syntax_cat f_sig
declare_syntax_cat f_sig'
/--
### Sigs
_Sigs_ (short for "signatures") are the basic building block of any model in Forge. They represent the types of the system being modeled. To declare one, use the `sig` keyword.

```
sig <name> {}
```

A `sig` can also have one or more _fields_, which define relationships between members of that `sig` other atoms. The definition above has no fields because the braces are empty. In contrast, this `sig` definition would have many fields:

```
sig <name> {
    <field>,
    <field>,
    ...
    <field>
}
```
-/
syntax f_sig' : f_sig
syntax f_sig_multiplicity ? "sig" ident "{" f_field,* "}" : f_sig'

declare_syntax_cat f_extends
/--
Sigs may inherit from other sigs via the `extends` keyword:

```
sig <name> extends <parent sig name> {
    <additional fields> ...
}
```

Sigs may only have _at most one parent sig_. Moreover, much like how no object can be belong to multiple top-level sigs, no object can belong to more than one immediate child of any sig. That is, any two sigs `A` and `B` will never contain an object in common unless one is a descendent of the other.

**Example:**

```
sig Cat {
    favoriteFood: one Food
}
sig ActorCat extends Cat {
    playName: one Play
}
sig ProgrammerCat extends Cat {}
```

This means that any `ProgrammerCat` object is also a `Cat` object, and so will have a `favoriteFood` field. But only `ActorCat`s have the `playName` field. Moreover, any cat may be either an `ActorCat`, `ProgrammerCat`, or neither---but not both.
-/
syntax "extends" ident : f_extends
syntax f_sig_multiplicity ? "sig" ident f_extends "{" f_field,* "}" : f_sig'

end ForgeSyntax
