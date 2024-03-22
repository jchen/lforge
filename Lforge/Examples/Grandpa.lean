import Lforge

sig Child extends Person {}

sig Person {
    parent1 : lone Person,
    parent2 : lone Person,
    spouse  : lone Person
}

#check Child
#synth Inhabited Child
#synth Inhabited Person
noncomputable opaque c : Child
#check (c : Person)

#check IsChild

#check Person

instance child_person : Coe Child Person where
  coe c := c

#synth Coe Child Person

pred isNotRelated[x: Person, y: Person] {
    not x->y in ^parent1 + ^parent2
}

pred test2 {
  all c : Child | c.parent1 != c.parent2
}

#check @isNotRelated
#print isNotRelated

#synth Inhabited Person

#synth Coe Person Person

#synth Fintype Person

pred isParent[x: Person, y: Person] {
    let p = x.parent1 | y = p or y = x.parent2
}

#print isParent

example : isParent x y := by
  simp only [isParent]
  simp only [Forge.HJoin.join]
  simp only [Coe.coe]
  sorry
  done

fun parentOf[x: Person, y: Person]: set Person {
    x.parent1
}

fun numParentsOf[x: Person, y: Person]: Int {
    #x.parent1
}

#print isParent
#print numParentsOf

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
    --    cannot be your relatives on parent2's side
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

#print FamilyFact

theorem a : FamilyFact := by
  simp [FamilyFact]
  simp only [Forge.HJoin.join]
  simp only [Coe.coe]
  simp only [Forge.HEq.eq]
  simp only [Set.singleton]
  simp only [isNotRelated]

  sorry
  done

-- SAT based development
