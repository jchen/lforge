import Lforge.ForgeSyntax
open ForgeSyntax
open Formula
open Expression
open Quantification

def sig_pet := {
  name := "Pet",
  fields := [
    {
      name := "owner",
      multiplicity := FieldMultiplicity.one,
      type := ["Person"]
    : Field
    }
  ]
  : Sig
}

def sig_person := {
  name := "Person",
  fields := [
    {
      name := "pets",
      multiplicity := FieldMultiplicity.set,
      type := ["Pet"]
    : Field
    },
    {
      name := "friends",
      multiplicity := FieldMultiplicity.set,
      type := ["Person"]
    : Field
    }
  ]
  : Sig
}

def pred_owner_owns_pet := {
  name := "ownerOwnsPet",
  args := [],
  body := quantifier all [("p", literal "Person")] (
    quantifier all [("pet", literal "Pet")] (
      iff
      -- pet ∈ p.pets
      (subset (literal "pet") (join (literal "p") (literal "pets")))
      -- pet.owner = p
      (eq (join (literal "pet") (literal "owner")) (literal "p"))))
  : Predicate
}

def pred_some_friends_own_a_pet := {
  name := "someFriendOwnsAPet",
  args := [("p", "Person")],
  body := quantifier some [("fs", join (literal "p") (literal "friends"))] (
    some (join (literal "fs") (literal "pets")))
  : Predicate
}

def fun_friends_pets := {
  name := "friendsPets",
  args := [("p", "Person")],
  result_type := literal "Pet",
  body := join (join (literal "p") (literal "friends")) (literal "pets")
  : Function
}

def model := {
  sigs := [sig_pet, sig_person],
  predicates := [pred_owner_owns_pet, pred_some_friends_own_a_pet],
  functions := [fun_friends_pets]
  : ForgeModel
}
