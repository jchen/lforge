import Lforge

/-
The following is adapted from cs1710, modeling a mutex:
https://csci1710.github.io/book/chapters/sets-and-boolean-logic/sets-induction-mutex.html
-/

abstract sig Location {}
one sig Uninterested, Waiting, InCS extends Location {}

sig Process {}

sig State {
  loc: func Process -> Location,
  flags: set Process
}

pred raise[pre: State, p: Process, post: State] {
  pre.loc[p] = Uninterested
  post.loc[p] = Waiting
  post.flags = pre.flags + p /* as Set Process */
  all p2: Process | p2 != p => post.loc[p2] = pre.loc[p2]
}

pred enter[pre: State, p: Process, post: State] {
  pre.loc[p] = Waiting
  p in pre.flags
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
    enter[pre, p, post] or
    leave[pre, p, post]
}

pred good[s: State] {
  all p: Process | (s.loc[p] = InCS or s.loc[p] = Waiting) implies p in s.flags
  #{p: Process | s.loc[p] = InCS} <= 1
}

pred startGoodTransition[s1, s2: State] {
  good[s1]
  delta[s1,s2]
}

pred properties {
  all s : State | init[s] => good[s]
  all pre, post : State | startGoodTransition[pre, post] => good[post]
}

theorem init_good : ∀ s : State, init s → good s := by
  sorry
  done

example : properties := by
  rw [properties]
  apply And.intro
  {
    exact init_good
  }
  {
    intro pre post h_good_transition
    cases' h_good_transition with h_good_pre h_delta
    cases' h_good_pre with h_good_flags h_good_num_waiting
    cases' h_delta with p h_transition
    sorry
  }
  done
