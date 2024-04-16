import Lforge

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
  simp only [existsBarber, shavesThemselves]
  simp only [Forge.HJoin.join, Forge.HIn.subset, Coe.coe]
  intro heb
  cases' heb with b hall
  have h := hall b
  tauto
  done
