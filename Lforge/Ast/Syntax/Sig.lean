/-
Forge syntax for **fields** and **sigs**.
-/

namespace ForgeSyntax

declare_syntax_cat forge_sig_multiplicity
/--
`one` states that there is always exactly one object of that sig.
-/
syntax "one" : forge_sig_multiplicity
/--
`lone` states there is never more than one object of this sig. That is, that there are zero or one.
-/
syntax "lone" : forge_sig_multiplicity
/-- `abstract` states that any object of this sig must also be a member of some child sig. -/
syntax "abstract" : forge_sig_multiplicity

declare_syntax_cat forge_field_multiplicity
/--
There is a single object of this field.

On an arrow type `A → B`, this means that this relation contains exactly one pair of `A × B`.
-/
syntax "one" : forge_field_multiplicity
/--
There is at most one object of this field.
-/
syntax "lone" : forge_field_multiplicity
-- TODO: Relax arity-2 condition?
/--
The relation **must** have arity 2. On relations from `A → B`, `pfunc` states that the relation is a partial function.
-/
syntax "pfunc" : forge_field_multiplicity
/--
The relation **must** have arity 2. On relations from `A → B`, `func` states that the relation is a total function.
-/
syntax "func" : forge_field_multiplicity
/--
`set` states that the relation is a set, this does not produce any additional quantifications or restraints.
-/
syntax "set" : forge_field_multiplicity

declare_syntax_cat forge_field
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
syntax ident,+ ":" forge_field_multiplicity sepBy1(ident, " -> ") : forge_field

declare_syntax_cat forge_sig
declare_syntax_cat forge_sig'
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
syntax forge_sig' : forge_sig
syntax forge_sig_multiplicity ? "sig" ident,+ "{" forge_field,* "}" : forge_sig'

declare_syntax_cat forge_extends
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
syntax "extends" ident : forge_extends
syntax forge_sig_multiplicity ? "sig" ident,+ forge_extends "{" forge_field,* "}" : forge_sig'

end ForgeSyntax
