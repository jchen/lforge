import Lean
import Lforge.ForgeSyntax
open Lean Elab Command Term Meta

sig TreeNode {
    parent: lone TreeNode,
    children: set TreeNode
}

sig Pet {
    owner: one Person
}

sig Person {
    pets: set Pet,
    friends: set Person
}

#check TreeNode
#check parent
#check children
#print lone_parent
