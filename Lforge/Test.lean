import Lean
import Lforge.Elab
open Lean Elab Command Term Meta

set_option forge.hints true

#check 2 + 2 = 4
#reduce (λ x ↦ x + 2) = (λ x ↦ x + 3)

-- axiom lone_parent : True

sig TreeNode {
    parent: lone TreeNode,
    children: one TreeNode,
    number: set Int -> TreeNode
}

sig Pet {
    owner: one Person
}

sig Person {
    pets: set Pet,
    friends: set Person
}

-- pred ownerOwnsPet {
--     all p: Person | { p in p }
-- }

#check TreeNode
#check parent
#check children
#print lone_parent

#print ownerOwnsPet

#print p
