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

-- Proofs


theorem init_good : ∀ s : State, init s → good s := by
  intro s his
  simp [init] at his
  simp [good]
  cases' his with h_all h_no_flags
  constructor
  {
    intro p h_p_state
    rcases h_p_state with h | h <;> simp [h_all p] at h
  }
  {
    right
    refine Set.ext ?intro.right.h.h
    intro hp
    constructor
    { tauto }
    { simp [Membership.mem, Set.Mem, h_all hp] }
  }
  done

lemma raise_transition_good (pre : State) (post : State) (g : good pre) : raise pre p post → good post := by
  intro hpre
  simp [good] at g
  rcases g with ⟨h_flags_pre, h_lock_pre⟩
  simp [raise] at hpre
  rcases hpre with ⟨h_pre_uninterested, h_post_waiting, h_flags, h_invariant⟩
  -- Helper for us to split on
  have h_p_p' : ∀ p' : Process, p' = p ∨ p' ≠ p := by tauto
  simp [good]
  constructor
  {
    -- Flags are preserved
    intro p'
    rw [h_flags]
    rcases h_p_p' p' with heq | hneq
    { tauto }
    {
      -- p' isn't p, then loc post is unchanged
      rw [h_invariant p' hneq]
      intro h_pre_in_or_waiting
      have := h_flags_pre p' h_pre_in_or_waiting
      tauto
    }
  }
  {
    -- Only one proc has the lock
    have heq : (fun p ↦ loc pre p = InCS) = (fun p ↦ loc post p = InCS)
    {
      refine (funext ?heq.h).symm
      intro p'
      rcases h_p_p' p' with heq | hneq
      { simp [heq, h_post_waiting, h_pre_uninterested] }
      { tauto }
    }
    rw [←heq]
    exact h_lock_pre
  }
  done

lemma lower_transition_good (pre : State) (post : State) (g : good pre) : lower pre p post → good post := by
  intro hpre
  simp [good] at g
  rcases g with ⟨h_flags_pre, h_lock_pre⟩
  simp [lower] at hpre
  rcases hpre with ⟨_, h_pre_waiting, h_post_uninterested, h_flags, h_invariant⟩
  -- Helper for us to split on
  have h_p_p' : ∀ p' : Process, p' = p ∨ p' ≠ p := by tauto
  simp [good]
  constructor
  {
    -- Flags are preserved
    intro p'
    rw [h_flags]
    rcases h_p_p' p' with heq | hneq
    { simp [heq, h_post_uninterested] }
    {
      -- p' isn't p, then loc post is unchanged
      rw [h_invariant p' hneq]
      intro h_pre_in_or_waiting
      have := h_flags_pre p' h_pre_in_or_waiting
      simp [sdiff]
      tauto
    }
  }
  {
    have heq : (fun p ↦ loc pre p = InCS) = (fun p ↦ loc post p = InCS)
    {
      refine (funext ?heq.h).symm
      intro p'
      rcases h_p_p' p' with heq | hneq
      { simp [heq, h_post_uninterested, h_pre_waiting] }
      { tauto }
    }
    rw [←heq]
    exact h_lock_pre
  }
  done

lemma enter_transition_good (pre : State) (post : State) (g : good pre) : enter pre p post → good post := by
  intro hpre
  simp [good] at g
  rcases g with ⟨h_flags_pre, h_lock_pre⟩
  simp [enter] at hpre
  rcases hpre with ⟨h_pre_singleton, _, h_post_incs, h_flags, h_invariant⟩
  -- Helper for us to split on
  have h_p_p' : ∀ p' : Process, p' = p ∨ p' ≠ p := by tauto
  simp [good]
  constructor
  {
    intro p'
    rw [h_flags]
    rcases h_p_p' p' with heq | hneq
    {
      simp [heq, h_post_incs, h_pre_singleton]
      tauto
    }
    {
      rw [h_invariant p' hneq]
      intro h_pre_in_or_waiting
      exact h_flags_pre p' h_pre_in_or_waiting
    }
  }
  {
    left
    existsi p
    constructor
    {
      simp
      refine Function.funext_iff.mpr ?intro.intro.intro.intro.intro.right.h.left.a
      intro p'
      rcases h_p_p' p' with heq | hneq
      {
        simp [heq, h_post_incs]
        tauto
      }
      {
        simp [Set.singleton]
        have : loc post p' ≠ InCS
        {
          intro loc_post_p'_eq
          rw [h_invariant p' hneq] at loc_post_p'_eq
          have := h_flags_pre p' (Or.inl loc_post_p'_eq)
          simp [h_pre_singleton] at this
          tauto
        }
        tauto
      }
    }
    {
      simp
      intro p' h_one_in_lock
      have : ¬ p' ≠ p
      {
        intro h_p'_np
        rw [Set.singleton] at h_one_in_lock
        have : loc post p' = InCS
        {
          have : p' ∈ {b | b = p'} := by tauto
          rw [←h_one_in_lock] at this
          simp [Membership.mem, Set.Mem] at this
          exact this
        }
        rw [h_invariant p' h_p'_np] at this
        have flags_pre_p' := h_flags_pre p' (Or.inl this)
        rw [h_pre_singleton] at flags_pre_p'
        tauto
      }
      tauto
    }
  }
  done

lemma leave_transition_good (pre : State) (post : State) (g : good pre) : leave pre p post → good post := by
  intro hpre
  simp [good] at g
  rcases g with ⟨h_flags_pre, h_lock_pre⟩
  simp [leave] at hpre
  rcases hpre with ⟨h_pre_incs, h_post_uninterested, h_flags, h_invariant⟩
  -- Helper for us to split on
  have h_p_p' : ∀ p' : Process, p' = p ∨ p' ≠ p := by tauto
  simp [good]
  constructor
  {
    intro p'
    rw [h_flags]
    rcases h_p_p' p' with heq | hneq
    {
      rw [heq]
      intro h
      rcases h with h | h <;>
      simp [h_post_uninterested] at h
    }
    {
      rw [h_invariant p' hneq]
      intro h_pre_in_or_waiting
      have := h_flags_pre p' h_pre_in_or_waiting
      simp [sdiff]
      tauto
    }
  }
  {
    right
    refine (Set.eq_empty_of_forall_not_mem ?intro.intro.intro.intro.right.h.h).symm
    intro p'
    simp [Membership.mem, Set.Mem]
    rcases h_p_p' p' with heq | hneq
    {
      rw [heq]
      simp [h_post_uninterested]
    }
    {
      intro h_loc_post_incs
      rw [h_invariant p' hneq] at h_loc_post_incs
      rcases h_lock_pre with hone | hnone
      {
        rcases hone with ⟨p'', ⟨hl, hr⟩⟩
        have h_p_in : p ∈ {p | loc pre p = InCS} := by tauto
        simp [hl] at h_p_in
        have h_p'_in : p' ∈ {p | loc pre p = InCS} := by tauto
        simp [hl] at h_p'_in
        rw [h_p_in, h_p'_in] at hneq
        tauto
      }
      {
        have : p' ∈ {p | loc pre p = InCS} := by tauto
        rw [←hnone] at this
        tauto
      }
    }
  }
  done

-- This is equivalent to claiming `properties is theorem`
theorem properties_is_theorem : properties := by
  rw [properties]
  constructor
  {
    exact init_good
  }
  {
    intro pre post hstart
    rcases hstart with ⟨h, p, hraise | hlower | henter | hleave⟩
    exact raise_transition_good pre post h hraise
    exact lower_transition_good pre post h hlower
    exact enter_transition_good pre post h henter
    exact leave_transition_good pre post h hleave
  }
  done
