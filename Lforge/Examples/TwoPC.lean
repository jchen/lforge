import Lforge

/-
This is the two-phase commit protocol described here:
https://en.wikipedia.org/wiki/Two-phase_commit_protocol

This example is loosely inspired by this Forge specification:
https://github.com/jinlang226/Forge-for-Distributed-System/blob/main/2pc/twoPC.frg
-/

#lang forge

-- `CoordinatorPhase` is the state of the coordinator.
-- For example, if the phase is `Commit`, this is equivalent to a message
-- of `Commit` being sent/broadcast to the participants.
abstract sig CoordinatorPhase {}
one sig Query, Commit, Rollback, End extends CoordinatorPhase {}

-- `ParticipantPhase` is the state of each participant in the system.
abstract sig ParticipantPhase {}
one sig Ready, Voted, Committed extends ParticipantPhase {}

-- `Action` represents both the action to be done
-- and the vote that will be cast.
abstract sig Vote {}
one sig Yes, No, None extends Vote {}

sig Participant {}

sig State {
  cphase: one CoordinatorPhase,
  pphase: func Participant -> ParticipantPhase,
  vote: func Participant -> Vote
}

pred init[s: State] {
  s.cphase = Query
  all p: Participant | {
    s.pphase[p] = Ready
    s.vote[p] = None
  }
}

-- Asserts that all participants don't change, only coordinator phase changed
pred coordinatorStep[pre, post: State] {
  pre.cphase != post.cphase
  all p : Participant | {
    pre.pphase[p] = post.pphase[p]
    pre.vote[p] = post.vote[p]
  }
}

-- Asserts that p is the only state change that happened
pred participantStep[p: Participant, pre, post: State] {
  pre.cphase = post.cphase
  all p2 : Participant | p != p2 => {
    pre.pphase[p] = post.pphase[p]
    pre.vote[p] = post.vote[p]
  }
}

-- The participant casts a vote if the coordinator step is querying
pred participantCastVote[p: Participant, pre, post: State] {
  participantStep[p, pre, post]
  -- Only vote when coordinator is querying the vote
  pre.cphase = Query
  -- Only vote when a vote hasn't yet been cast
  pre.vote[p] = None
  pre.pphase[p] = Ready
  -- Register the vote
  post.vote[p] = Yes or post.vote[p] = No
  post.pphase[p] = Voted
}

-- If everyone's voted, change coordinator state to result of vote
pred coordinatorTally[pre, post: State] {
  coordinatorStep[pre, post]
  pre.cphase = Query
  all p : Participant | pre.pphase[p] = Voted
  all p : Participant | pre.vote[p] = Yes implies
    post.cphase = Commit
  else
    post.cphase = Rollback
}

-- If the coordinator publishes commit, then commit
pred participantCommit[p: Participant, pre, post: State] {
  participantStep[p, pre, post]
  pre.cphase = Commit
  pre.pphase[p] = Voted
  post.pphase[p] = Committed
}

-- If the coordinator publishes rollback, become ready again and reset vote
pred participantRollback[p: Participant, pre, post: State] {
  participantStep[p, pre, post]
  pre.cphase = Rollback
  pre.pphase[p] = Voted
  post.pphase[p] = Ready
  post.vote[p] = None
}

-- If all participants have committed, then end
pred coordinatorEnd[pre, post: State] {
  coordinatorStep[pre, post]
  pre.cphase = Commit
  all p : Participant | pre.pphase[p] = Committed
  post.cphase = End
}

-- If the commit didn't work, then reset
pred coordinatorReset[pre, post: State] {
  coordinatorStep[pre, post]
  pre.cphase = Rollback
  all p : Participant | pre.pphase[p] = Ready
  post.cphase = Query
}

-- If we've ended, remain ended
pred coordinatorTerminal[pre, post: State] {
  coordinatorStep[pre, post]
  pre.cphase = End
  post.cphase = End
}

pred coordinatorMove[pre, post: State] {
  coordinatorTally[pre, post] or
  coordinatorEnd[pre, post] or
  coordinatorReset[pre, post] or
  coordinatorTerminal[pre, post]
}

pred participantMove[p: Participant, pre, post: State] {
  participantCastVote[p, pre, post] or
  participantCommit[p, pre, post] or
  participantRollback[p, pre, post]
}

pred delta[pre, post: State] {
  (coordinatorMove[pre, post]) or
  (some p : Participant | participantMove[p, pre, post])
}

pred good[s: State] {
  all p : Participant | s.pphase[p] = Ready <=> s.vote[p] = None
  s.cphase = Query => {
    all p : Participant | s.pphase[p] = Ready or s.pphase[p] = Voted
  }
  -- If someone's committed, everyone voted yes and nobody has reset
  { some p : Participant | s.pphase[p] = Committed } =>
  {
    all p : Participant | s.pphase[p] != Ready
    all p : Participant | s.vote[p] = Yes
  }
  -- Rollback means someone voted no
  s.cphase = Rollback => {
    some p : Participant | s.vote[p] != Yes
    all p : Participant | s.pphase[p] = Voted or s.pphase[p] = Ready
  }
  -- Commit means all voted yes
  s.cphase = Commit <=> {
    all p : Participant | s.vote[p] = Yes
    all p : Participant | s.pphase[p] = Voted or s.pphase[p] = Committed
  }
  -- End means everyone's committed
  s.cphase = End => { all p : Participant | s.pphase[p] = Committed }
  -- Came from a good state
  some i : State | init[i] and i->s in *delta
}

pred properties {
  all i : State | init[i] => good[i]
  all pre, post : State | good[pre] and delta[pre, post] => good[post]
}
