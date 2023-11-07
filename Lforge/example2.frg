#lang forge

abstract sig Student {}
sig Undergrad, Grad extends Student {}
one sig SpecialGrad extends Grad {}

sig Mascot {}

sig Year {
    mascot: one Mascot,
    next: lone Year
}

sig Class {
    students: set Student,
    // Using Alloy syntax here
    // pairs: Student one -> one Student,
    buddies: func Student -> Student,
    best_friend: pfunc Student -> Student
}

pred buddiesNoCycles {
    all c: Class | no x: Student | { reachable[x, x, c.buddies] }
    -- can also write reachable[x, c.buddies]
}

pred noSelfBuddies {
    all c: Class | no x: Student | { c.buddies[x] = x }
}

pred someStudent {
    some s: Student | { true }
}

pred someClass {
    some c: Class | { true }
}

test expect {
    { someClass && someStudent && buddiesNoCycles && noSelfBuddies } is unsat
    { ... } is theorem
}