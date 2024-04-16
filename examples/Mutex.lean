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
  -- A process can only enter if it is currently not under contention
  all p1: Process | pre.loc[p] != InCS
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
    enter[pre, p, post] or
    leave[pre, p, post]
}

pred good[s: State] {
  all p: Process | (s.loc[p] = InCS or s.loc[p] = Waiting) implies p in s.flags
  lone {p: Process | s.loc[p] = InCS}
}

pred startGoodTransition[s1, s2: State] {
  good[s1]
  delta[s1,s2]
}

pred properties {
  all s : State | init[s] => good[s]
  all pre, post : State | startGoodTransition[pre, post] => good[post]
}

-------- Proofs --------

theorem init_good : ∀ s : State, init s → good s := by
  intro s his
  simp [init] at his
  simp [good]
  cases' his with h_all h_no_flags
  constructor
  {
    intro p h_p_state
    rcases h_p_state with ⟨hl⟩ | ⟨hr⟩
    rw [h_all p] at hl
    simp at hl
    rw [h_all p] at hr
    simp at hr
  }
  {
    -- rw [ExprQuantifier.lone, ExprQuantifier.no, ExprQuantifier.one]
    right
    refine Set.ext ?intro.right.h.h
    intro hp
    constructor
    tauto
    {
      intro hpin
      simp only [Membership.mem, Set.Mem] at hpin
      rw [h_all hp] at hpin
      simp at hpin
    }
  }
  done

theorem raise_transition_good (pre : State) (post : State) (g : good pre) : raise pre p post → good post := by
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
    {
      -- p' is p
      intro _
      rw [heq]
      tauto
    }
    {
      -- p' isn't p, then loc post is unchanged
      have h_loc_invariant := h_invariant p' hneq
      rw [h_loc_invariant]
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
      {
        -- Absurd
        rw [heq, h_post_waiting, h_pre_uninterested]
        simp
      }
      {
        -- Post and pre state same
        have h_loc_invariant := h_invariant p' hneq
        tauto
      }
    }
    rw [←heq]
    exact h_lock_pre
  }
  done

theorem enter_transition_good (pre : State) (post : State) (g : good pre) : enter pre p post → good post := by
  sorry
  done

theorem leave_transition_good (pre : State) (post : State) (g : good pre) : leave pre p post → good post := by
  sorry
  done


example : properties := by
  rw [properties]
  apply And.intro
  {
    exact init_good
  }
  {
    intro pre post hstart
    rcases hstart with ⟨h, ⟨p, ⟨hraise⟩ | ⟨henter⟩ | ⟨hleave⟩⟩⟩
    exact raise_transition_good pre post h hraise
    exact enter_transition_good pre post h henter
    exact leave_transition_good pre post h hleave
  }
  done
