import Lforge

sig Person {
  parent1 : lone Person,
  parent2 : lone Person,
  spouse  : lone Person
}

pred isNotRelated[x: Person, y: Person] {
  not x->y in ^parent1 + ^parent2
}

pred isParent[x: Person, y: Person] {
  let p = x.parent1 | y = p or y = x.parent2
}

pred FamilyFact {
  -- No person should be their own spouse
  all p: Person | p.spouse != p
  -- You cannot be related to yourself
  all p: Person | isNotRelated[p, p]
  -- You are your spouse's spouse
  all p, q: Person | p.spouse = q => {
    q.spouse = p
  }
  -- You cannot be related to your spouse
  all p, q: Person | p.spouse = q implies {
    isNotRelated[p, q]
  }
  -- distinct parents
  all p: Person | all q, r: Person | (p.parent1 = q && p.parent2 = r) implies {
    q != r
  }

  -- For any person :
  --  - Your relatives on parent1's side (i.e. everyone related to parent1)
  --  cannot be your relatives on parent2's side
  --  - If someone is  related to you they cannot be related to your spouse
  -- Here by related we mean:
  -- A person is related to their parents, parent's parents and so on.
  all p: Person | all q, r: Person | p.parent1 = q and p.parent2 = r implies {
    isNotRelated[q, r]
  }
  all p: Person | all q, r, s: Person | p.parent1 = q and p.parent2 = r and p.spouse = s implies {
    isNotRelated[q, s] and isNotRelated[r, s]
  }
}


pred ownGrandparent {
  -- Fill in a constraint that requires there to be a case where someone is their own grandpa.
  -- (Properly expressing what it means to be your own grandpa is crucial!)
  some p, f, w, d: Person |
  isParent[d, w] and isParent[p, f] and p.spouse = w and f.spouse = d
}

-- While it can be fun to test this for more people your solution should
-- be valid for exactly 4 Person
-- run {FamilyFact ownGrandparent} for exactly 4 Person
