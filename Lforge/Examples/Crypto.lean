import Lforge

abstract sig Key {}
sig PrivateKey extends Key {}
sig PublicKey extends Key {}

one sig KeyPairs {
  pairs: set PrivateKey -> PublicKey
}


test expect {
  force_checking: {some someKey: Key | some getInv[someKey]} is sat
}
