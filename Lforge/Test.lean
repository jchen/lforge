import Lean
import Lforge.Elab
open Lean Elab Command Term Meta

set_option forge.hints true

sig Pet {
    owner: one Person
}

sig Person {
    pets: set Pet,
    friends: set Person
}

pred ownerOwnsPet {
    some p: Person, pet: Pet | { pet in p . pets <=> p = pet . owner }
}

#print ownerOwnsPet

-- pred oneFriendOwnsOnePet[p: Person] {
--     one fs: p . friends | { one fs . pets }
-- }

-- pred someFriendOwnsAPet[p: Person] {
--     some fs: p . friends | { some fs . pets }
-- }

-- fun friendsPets[p: Person]: set Pet {
--     p . friends . pets
-- }
