import Lean
import Lforge.ForgeSyntax
open Lean Elab Command Term Meta

sig TreeNode {
    parent: lone TreeNode,
    children: set TreeNode
}

#check lone_parent
