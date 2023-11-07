/-
Modeling the syntax of Forge within Lean. 
-/

def Symbol := String

inductive SigMultiplicity where
  -- there is always exactly one object of that sig
  | one
  -- there is never more than one object of this sig
  | lone
  -- any object of this sig must also be a member of some child sig
  | abstract

inductive FieldMultiplicity where
  -- only one of
  | one
  -- one or zero of
  | lone
  -- is a -> relation and is a partial function
  | pfunc
  -- is a -> relation and is a total function
  | func
  -- is any set (least constraint)
  | set

structure Field where
  name : Symbol
  multiplicity : FieldMultiplicity -- is nested in Alloy
  type : List Symbol

structure Sig where
  quantifier : Option SigMultiplicity := none
  name : Symbol -- Some sugar here that allows defining multiple w/ no fields
  ancestor : Option Symbol := none
  fields : List Field

inductive Quantification where 
  | some
  | all
  | no
  | lone
  | one

mutual
  /-
  All formulas evaluate to boolean values
  -/
  inductive Formula where
    /- Operators -/
    | not (fmla : Formula)
    | and (fmla_a fmla_b : Formula)
    | or (fmla_a fmla_b : Formula)
    | implies (fmla_a fmla_b : Formula)
    -- if [fmla_a], then [fmla_b], otherwise [fmla_c]
    | implies_else (fmla_a fmla_b fmla_c : Formula)
    | iff (fmla_a fmla_b : Formula)

    /- Cardinality and membership -/
    | no (expr : Expression)
    | lone (expr : Expression)
    | one (expr : Expression)
    | some (expr : Expression)
    -- expr_a in expr_b
    | subset (expr_a expr_b : Expression)
    -- expr_a = expr_b
    | eq (expr_a expr_b : Expression)

    /- Quantifiers 
       Quantifies [var](s) over [expr](s) and binds [var](s) in [fmla] -/
    | quantifier (quantification : Quantification) (vars : List (Symbol × Expression)) (fmla : Formula)

    /- Predicate Evaluations -/
    | predicate_evaluation (name : Symbol) (args : List Expression)

  inductive Expression where
    | union (expr_a expr_b : Expression)
    | set_difference (expr_a expr_b : Expression)
    | intersection (expr_a expr_b : Expression)
    -- relational join
    | join (expr_a expr_b : Expression)
    -- cartesian product
    | cross (expr_a expr_b : Expression)
    -- transpose of a relation of arity-2
    | transpose (expr : Expression)
    -- transitive closure of a relation of arity-2
    | transitive_closure (expr : Expression) 
    | reflexive_transitive_closure (expr : Expression)
    -- if [fmla], then [expr_a], otherwise [expr_b]
    | if_then_else (fmla expr_a expr_b : Expression)
    -- { [var] | [fmla] }, binds [var](s) in fmla and includes in set if true
    | set_comprehension (vars : List (Symbol × Expression)) (fmla : Formula)

    -- Function application, also includes literals (TODO: ask?)
    | function_application (fun_name : Symbol) (args : List Expression)
    -- a literal value, can be sig, relation, or top-level expr (univ, none, iden, etc.)
    | literal (value : Symbol)
end

structure Predicate where
  name : Symbol
  args : List (Symbol × Symbol) -- (name, type) pairs
  body : Formula -- with args bound

structure Function where
  name : Symbol
  args : List (Symbol × Symbol) -- (name, type) pairs
  result_type : Expression
  -- Really ignored in Forge
  body : Expression -- with args bound

structure ForgeModel where
  sigs : List Sig
  predicates : List Predicate
  functions : List Function
