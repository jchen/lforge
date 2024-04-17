import Lforge
import Lforge.Examples.Mutex

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
