import Lforge

sig Node {
    next: lone Node
}

sig A {
    field: one Node
}

pred cycle {
    all n: Node | reachable[n.next, n, next]
}
