import Lforge

/-
This is the classic 'barber who shaves themselves' example in logic.
We can model this using a Forge specification and disprove the statement that
there exists a barber using Lean. This is a toy example of our translation working
-/

sig Person {
  shaved_by: one Person
}

pred shavesThemselves[p: Person] {
  p = p.shaved_by
}

pred existsBarber {
  some barber : Person | all p : Person | {
    not shavesThemselves[p] <=> p.shaved_by = barber
  }
}

theorem no_barber : ¬ existsBarber := by
  simp [existsBarber, shavesThemselves]
  intro b
  existsi b
  tauto
  done

check existsBarber
