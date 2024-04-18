import Lforge

/-
This is the classic 'barber who shaves themselves' example in logic.
We can model this using a Forge specification and disprove the statement that
there exists a barber using Lean. This is a toy example of our translation working
-/

sig Person {
  shaver: one Person
}

pred shavesThemselves[p: Person] {
  p = p.shaver
}

pred existsBarber {
  some barber : Person | all p : Person | {
    not shavesThemselves[p] <=> p.shaver = barber
  }
}

theorem no_barber : ¬ existsBarber := by
  simp [existsBarber, shavesThemselves]
  intro b
  existsi b
  tauto
  done
