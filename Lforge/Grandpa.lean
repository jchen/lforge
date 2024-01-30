import Lean
import Lforge.Elab
open Lean Elab Command Term Meta

set_option forge.hints true
set_option forge.dot_join true

sig Person {
    parent1 : lone Person,
    parent2 : lone Person,
    spouse  : lone Person
}

pred isNotRelated[x: Person, y: Person] {
}
--     not y->x in (^parent1) + (^parent2)

pred isParent[x: Person, y: Person] {
    y = x.parent1 or y = x.parent2
}

pred FamilyFact {
    all p: Person | p.spouse != p
    all p: Person | isNotRelated[p, p]
    all p, q: Person | p.spouse = q implies {
        q.spouse = p
    }
    all p, q: Person | p.spouse = q implies {
        isNotRelated[p, q]
    }
    all p: Person | all q, r: Person | p.parent1 = q and p.parent2 = r implies {
        q != r
    }
    all p: Person | all q, r: Person | p.parent1 = q and p.parent2 = r implies {
        isNotRelated[q, r]
    }
    all p: Person | all q, r, s: Person | p.parent1 = q and p.parent2 = r and p.spouse = s implies {
        isNotRelated[q, s] and isNotRelated[r, s]
    }
}

#print FamilyFact

theorem proof : FamilyFact := by
  rw [FamilyFact]
  sorry
  done

pred ownGrandparent {
    some p, f, w, d: Person |
    isParent[d, w] and isParent[p, f] and p.spouse = w and f.spouse = d
}

#print ownGrandparent
