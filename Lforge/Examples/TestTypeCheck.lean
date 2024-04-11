import Lforge

sig Person {
  a: one Person
}

fun test[]: Int {
  sum x : Person | {
    0
  }
}
