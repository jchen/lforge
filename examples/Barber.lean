import Lforge

/-
This is the classic 'barber who shaves themselves' example in logic.
We can model this using a Forge specification and disprove the statement that
there exists a barber using Lean. This is a toy example of our translation working
-/

sig Person {
  shaves: one Person
}

pred shavesThemselves[p: Person] {
  p = p.shaves
}

pred existsBarber {
  some b : Person | all p : Person | {
    not shavesThemselves[p] <=> b = p.shaves
  }
}

example : ¬ existsBarber := by
  simp [existsBarber, shavesThemselves]
  intro b
  existsi b
  tauto
  done
