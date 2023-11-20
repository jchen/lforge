#lang forge

sig Node {
    next: one Node
}

pred noCycle {
    no n : Node | { n in n.^next }
}

pred someNode {
    some n : Node | { true }
}

test expect {
    { someNode && noCycle } is unsat
}