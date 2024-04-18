import Lforge

/-
The following is adapted from cs1710, modeling a mutex:
https://csci1710.github.io/book/chapters/sets-and-boolean-logic/sets-induction-mutex.html

Modifications were made to suit the model for potentially more than 2 processes!
This is one of the benefits / selling points of our model.
 - Processes can enter a 'Waiting' state with flags.
 - A process can only enter the cricical state when an atomic check of all flags passes, that is, they are the only one with the flag raised.
 - If they are not the only one with flag raised, they back off and try again at a later time.
-/

#lang forge

abstract sig Location {}
one sig Uninterested, Waiting, InCS extends Location {}

sig Process {}

sig State {
  loc: func Process -> Location,
  flags: set Process
}

pred good[s: State] {
  all p: Process | (s.loc[p] = InCS or s.loc[p] = Waiting) implies p in s.flags
  lone {p: Process | s.loc[p] = InCS}
}

pred raise[pre: State, p: Process, post: State] {
  pre.loc[p] = Uninterested
  post.loc[p] = Waiting
  post.flags = pre.flags + p /* as Set Process */
  all p2: Process | p2 != p => post.loc[p2] = pre.loc[p2]
}

pred lower[pre: State, p: Process, post: State] {
  -- Only lower when it cannot acquire the lock.
  pre.flags != p
  pre.loc[p] = Waiting
  post.loc[p] = Uninterested
  post.flags = pre.flags - p /* as Set Process */
  all p2: Process | p2 != p => post.loc[p2] = pre.loc[p2]
}

pred enter[pre: State, p: Process, post: State] {
  -- A process can only enter if it is the only thread in contention, that is, only thread with flag
  pre.flags = p
  pre.loc[p] = Waiting
  post.loc[p] = InCS
  post.flags = pre.flags
  all p2: Process | p2 != p => post.loc[p2] = pre.loc[p2]
}

pred leave[pre: State, p: Process, post: State] {
  pre.loc[p] = InCS
  post.loc[p] = Uninterested
  post.flags = pre.flags - p /* as Set Process */
  all p2: Process | p2 != p => post.loc[p2] = pre.loc[p2]
}

pred init[s: State] {
  all p: Process | s.loc[p] = Uninterested
  no s.flags
}

pred delta[pre: State, post: State] {
  some p: Process |
    raise[pre, p, post] or
    lower[pre, p, post] or
    enter[pre, p, post] or
    leave[pre, p, post]
}

pred startGoodTransition[s1, s2: State] {
  good[s1]
  delta[s1,s2]
}

pred properties {
  all s : State | init[s] => good[s]
  all pre, post : State | startGoodTransition[pre, post] => good[post]
}
