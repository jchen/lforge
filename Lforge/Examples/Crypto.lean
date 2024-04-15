import Lforge

abstract sig Key {}
one sig PrivateKey extends Key {}
sig PublicKey extends Key {}

one sig KeyPairs {
  pairs: set PrivateKey -> PublicKey
}

#check (PrivateKey : PrivateKey → Prop)
#check Bool
#check Sort 1
