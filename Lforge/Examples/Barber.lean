import Lforge

#lang forge

sig Person {
  shaves: set Person
}

pred shavesThemselves[p: Person] {
  p in p.shaves
}

pred existsBarber {
  some b : Person | all p : Person | {
    not shavesThemselves[p] <=> b in p.shaves
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
