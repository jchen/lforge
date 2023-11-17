#lang forge

sig TreeNode {
    parent: lone TreeNode,
    children: set TreeNode
}

pred treeRoot[t: TreeNode] {
    no t.parent
}

pred treeChild[t: TreeNode] {
    some t.parent
}

pred notOwnParent[t: TreeNode] {
    t.parent != t
}

pred allNotOwnParent {
    all t : TreeNode | { notOwnParent[t] }
}

pred oneRoot {
    one t : TreeNode | { treeRoot[t] }
}

pred parentOfChildren {
    all t1 : TreeNode | all t2 : TreeNode | { t1.parent = t2 <=> t1 in t2.children }
}

pred wellFormed {
    allNotOwnParent
    oneRoot
    parentOfChildren
}

pred allReachable {
    all t1 : TreeNode | all t2 : TreeNode | { t1 != t2 }
}

test expect {
    { wellFormed  } is theorem
}