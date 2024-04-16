import Lforge
import Lforge.BorrowDemo.sigs

#lang forge

-- Predicates that are used by several modules and implement common functionality.


-- Determines if there is a path through the program from the start statement
-- to the target statement, by following either the sequence of statements or
-- stepping into inner scopes.
pred statementReachable[target: Statement, start: Statement] {
    -- The target is reachable by following either next (for sequential statements),
    -- var_scope_start (for inner scopes of var declarations), or
    -- curly_braces_start (for other inner scopes).
    -- reachable[target, start, next, inner_scope]
    true
}

-- Variant of statementReachable that only allows reachability via the `next` field.
-- This outrules any entering of inner scopes in order to reach the target.
pred statementReachableOnlyNext[target: Statement, start: Statement] {
    -- reachable[target, start, next]
}

-- Variant of statementReachable that allows for the target and start begin the same.
pred statementReachableInclusive[target: Statement, start: Statement] {
    statementReachable[target, start] or target = start
}

-- Checks if the `before` statement occurs strictly earlier in the program than the `after` statement.
pred isBefore[earlier: Statement, later: Statement] {
    -- Statement cannot be before itself
    earlier != later

    -- EITHER: You can directly reach `later` by traversing down the tree from `earlier`
    (statementReachable[later, earlier] or

    -- OR: You can "back up" the tree to some "common ancestor" statement whose
    -- scope contains the `earlier` statement, and occurs before the `later`.
    (some commonAncestor: Statement | {
        -- The common ancestor is a containing scope for `earlier`
        -- some commonAncestor.inner_scope
        statementReachableInclusive[earlier, commonAncestor.inner_scope]

        -- The common ancestor happens strictly before the `later`, and
        -- `later` is not part of the common ancestor's inner scope.
        -- some commonAncestor.next and statementReachableInclusive[later, commonAncestor.next]
    }))
}

-- A variant of isBefore that allows for the statements to be the same.
pred isBeforeOrEqual[earlier: Statement, later: Statement] {
    isBefore[earlier, later] or
    earlier = later
}

-- A variant of isBefore that enforces that the earlier statement be immediately
-- before the later statement, i.e. there are no intervening statements.
pred isDirectlyBefore[earlier: Statement, later: Statement] {
    isBefore[earlier, later]
    no middle: Statement | isBetween[middle, earlier, later]
}

-- Determines if a given statement is between a start and end statement, exclusive.
pred isBetween[middle: Statement, start: Statement, termination: Statement] {
    -- The middle is not at the endpoints (this is exclusive)
    middle != start
    middle != termination

    -- The middle is contained between the start/end, by being after the start and before the end.
    isBefore[start, middle]
    isBefore[middle, termination]
}

-- Determines if a given statement is between a start and end, inclusive of the bounds.
pred isBetweenInclusive[middle: Statement, start: Statement, termination: Statement] {
    middle = start or
    middle = termination or
    isBetween[middle, start, termination]
}

-- Determines if a given value is an owned value.
pred isOwned[value: Value] {
    no value.borrow_referent
    no value.borrow_mut_referent
}

-- Determines if a given type is an owned type.
pred isOwnedType[type: RustType] {
    no type.borrow_referent_type
    no type.borrow_mut_referent_type
}

-- Determines if a given value is a borrow (&).
pred isBorrow[value: Value] {
    some value.borrow_referent
}

-- Determines if a given type is a borrow type.
pred isBorrowType[type: RustType] {
    some type.borrow_referent_type
}

-- Determines if a given value is a mutable borrow.
pred isBorrowMut[value: Value] {
    some value.borrow_mut_referent
}

-- Determines if a given type is a borrow mut type.
pred isBorrowMutType[type: RustType] {
    some type.borrow_mut_referent_type
}

-- Extract the referent var of a given value, or none if the value is an Owned.
fun referent[borrow: Value]: Variable {
    if some borrow.borrow_referent then borrow.borrow_referent else borrow.borrow_mut_referent
}

-- Extract the referent value from a given borrow (or none, if Owned)
fun referentValue[value: Value]: Value {
    if some value.borrow_referent_value then value.borrow_referent_value else value.borrow_mut_referent_value
}

-- Determines if the given var is being modified either by reassigning to a new value or moving into or out of the var
pred varModification[var: Variable, statement: Statement] {
    statement.updated_var = var or    -- Being reassigned to
    statement.source = var or              -- Being moved out of
    statement.destination = var            -- Being moved into
}

-- Determines if the statement creates a value that references the given var.
pred varUseInValue[var: Variable, statement: Statement] {
    -- Account for uses of vars that are embedded in values, e.g. &mut a
    (some value: Value | {
        -- This value is part of this statement
        (statement.initial_value = value) or (statement.new_value = value) or (statement.moved_value = value)

        -- The value uses the var
        (value.borrow_referent = var) or (value.borrow_mut_referent = var)
    })
}

-- Determines if the given var is being "used" in the given statement.
-- NOTE: Excludes declaration and initialization, because if initializing
-- is considered use, and use before initialization is illegal, then
-- you can never initialize.
pred varUse[var: Variable, statement: Statement] {
    varModification[var, statement] or
    varUseInValue[var, statement]
}

-- Version of varUse that includes initialization statements as uses.
pred varUseOrInit[var: Variable, statement: Statement] {
    varUse[var, statement] or statement.initialized_var = var
}

-- Determines if the statement creates a borrow of the var or moves out of it.
pred readUseOfVariable[var: Variable, statement: Statement] {
    varUseInValue[var, statement] or
    statement.source = var
}

-- Determines if the given statement is the one that creates the given value.
pred valueCreated[statement: Statement, value: Value] {
    -- Only initialize/update statements can create values
    statement.initial_value = value or
    statement.new_value = value
}

-- Determines if the given statement assigns to the var (either by initializing,
-- updating, or doing a move).
pred assignsToVar[assignment: Statement, var: Variable] {
    assignment.initialized_var = var or
    assignment.updated_var = var or
    assignment.destination = var
}

-- Determines if the given value matches the one from the given assignment statement.
pred valueFromAssignment[assignment: Statement, value: Value] {
    value = assignment.initial_value or
    value = assignment.new_value or
    value = assignment.moved_value
}

-- Determine if the given statement is within the scope of the var.
pred inScopeOfVariable[statement: Statement, var: Variable] {
    some decl: DeclareVariable | {
        decl.declared_var = var
        statementReachableInclusive[statement, decl.inner_scope]
    }
}

-- Determines if the given var holds the given value right before the
-- execution of the given statement (not including effects of the statement itself).
pred varHasValueBeforeStmt[statement: Statement, var: Variable, value: Value] {
    -- In order for the var to have a value at all, it must be in scope
    inScopeOfVariable[statement, var]

    -- Look at the most recent assignment to determine the value
    some assignment: Statement | {
        assignsToVar[assignment, var]

        -- The assignment happens before the statement
        isBefore[assignment, statement]

        -- No other assignment to this var is more recent
        no moreRecentAssignment: Statement | {
            assignsToVar[moreRecentAssignment, var]
            isBetween[moreRecentAssignment, assignment, statement]
        }
        -- The var hasn't been moved out of since this assignment, because
        -- that would leave it uninitialized.
        (!isBorrow[value]) => (no moveOut: MoveOrCopy | {
            moveOut.source = var
            moveOut.moved_value = value
            isBetween[moveOut, assignment, statement]
        })

        -- The value comes from this most recent assignment
        valueFromAssignment[assignment, value]
    }
}

-- Determines if the given var holds the given value at the point in the
-- program when this statement occurs.
-- NOTE: This *includes* the effect of `statement` itself, so if it is is an
-- assignment, this will use the assignment's new value.
pred varHasValueAtStmt[statement: Statement, var: Variable, value: Value] {
    assignsToVar[statement, var] => {
        -- If the statement itself assigns to the var, get the value there
        valueFromAssignment[statement, value]
    } else {
        -- Otherwise, look for the value it had before this statement
        varHasValueBeforeStmt[statement, var, value]
    }
}

-- Determines if the target value is reachable via a chain of borrows from the start.
-- I.e., You could dereference the start value some number of times to get to the target.
pred borrowReachable[target: Value, start: Value] {
    reachable[target, start, borrow_referent_value, borrow_mut_referent_value]
}
