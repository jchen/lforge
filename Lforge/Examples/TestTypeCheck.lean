import Lforge

#check Finset.max
#check Finset.min
#check Finset.sum

sig Person {
  a: one Person
}

fun test[]: Int {
  sum x : Person | {
    0
  }
}
