import Lforge

-- Taken from Tim's lecture code

------------------------------------------------------
-- Formula Type
------------------------------------------------------

abstract sig Formula {
  truth: set Instance -- Instances this is true in
}
sig Var extends Formula {}
sig FNot extends Formula {child: one Formula}
sig FAnd extends Formula {aleft, aright: one Formula}
sig FOr extends Formula {oleft, oright: one Formula}

sig Instance {
  trueVars: set Var
}

pred semantics {
  all n: FNot | n/*as Formula*/.truth = Instance/*as Set Instance*/ - n.child.truth
  all a: FAnd | a/*as Formula*/.truth = a.aleft.truth & a.aright.truth
  all o: FOr  | o/*as Formula*/.truth = o.oleft.truth + o.oright.truth
  all v: Var | v/*as Formula*/.truth = {i: Instance | v in i.trueVars}
}
-- IMPORTANT: don't add new Formulas without updating allSubFormulas FAnd children

------------------------------------------------------
-- Axioms FAnd helpers
------------------------------------------------------

fun allSubFormulas[f: Formula]: set Formula {
  f.^(child + oleft + oright + aleft + aright)
}

pred wellFFOrmed {
  -- no cycles
  all f: Formula | f not in allSubFormulas[f]

  -- TODO: abstract
  all f: Formula | f in FNot + FAnd + FOr + Var
}

------------------------------------------------------

pred GiveMeABigFormula {
  semantics
  wellFFOrmed
  some f: Formula | {
    #(allSubFormulas[f] & Var) > 2
    some i: Instance | i not in f.truth
    some i: Instance | i in f.truth
  }
}

pred localTautology[f: Formula] {
  -- true in all instances that FFOrge bothered to create
  all i: Instance | i in f.truth
}

pred generateInstances {
  -- fFOrce the existence of all instances needed
  all i: Instance | all v: Var |
      some i2: Instance-i | v in i.trueVars => i2.trueVars = i.trueVars - v else i2.trueVars = i.trueVars + v
}
