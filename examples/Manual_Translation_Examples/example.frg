#lang forge

sig Pet {
    owner: one Person
}

sig Person {
    pets: set Pet,
    friends: set Person
}

pred ownerOwnsPet {
    all p: Person | all pet: Pet | { pet in p.pets <=> pet.owner = p }
}

pred oneFriendOwnsOnePet[p: Person] {
    one fs: p.friends | { one fs.pets }
}

pred someFriendOwnsAPet[p: Person] {
    some fs: p.friends | { some fs.pets }
}

fun friendsPets[p: Person]: set Pet {
    p.friends.pets
}

check {
    all p: Person | { oneFriendOwnsOnePet[p] => someFriendOwnsAPet[p] }
} for 1 Person, 0 Pet
