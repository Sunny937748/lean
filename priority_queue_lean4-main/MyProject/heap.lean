import Mathlib.Data.Real.Basic
import Mathlib.Tactic

inductive BinaryTree (α : Type) [Ord α] where
  | leaf : α → BinaryTree α
  | left : α → BinaryTree α → BinaryTree α
  | right : α → BinaryTree α → BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α

def size {α : Type} [Ord α] : BinaryTree α → Nat
  | BinaryTree.leaf _ => 1
  | BinaryTree.left _ l => 1 + size l
  | BinaryTree.right _ r => 1 + size r
  | BinaryTree.node _ l r => 1 + size l + size r

def depth {α : Type}[Ord α] : BinaryTree α → Nat
  | BinaryTree.leaf _ => 1
  | BinaryTree.left _ l => 1 + depth l
  | BinaryTree.right _ r => 1 + depth r
  | BinaryTree.node _ l r => 1 + max (depth l) (depth r)

def is_complete_binary_tree {α : Type} [Ord α] : BinaryTree α → Bool
  | BinaryTree.leaf _ => true
  | BinaryTree.left _ l => depth l = 1
  | BinaryTree.right _ _ => false
  | BinaryTree.node _ l r => depth l >= depth r && size l >= size r && is_complete_binary_tree l && is_complete_binary_tree r

def preorder {α : Type}[Ord α] : BinaryTree α → List α
  | BinaryTree.leaf v => [v]
  | BinaryTree.left v l => v :: preorder l
  | BinaryTree.right v r => v :: preorder r
  | BinaryTree.node v l r => v :: preorder l ++ preorder r

def get_value : BinaryTree Nat → Nat
  | BinaryTree.leaf v => v
  | BinaryTree.left v _ => v
  | BinaryTree.right v _ => v
  | BinaryTree.node v _ _ => v

def is_min : BinaryTree Nat → Bool
  | BinaryTree.leaf _ => true
  | BinaryTree.left v l => get_value l >= v && is_min l
  | BinaryTree.right v r => get_value r >= v && is_min r
  | BinaryTree.node v l r => get_value l >= v && get_value r >= v && is_min l && is_min r

def is_max : BinaryTree Nat → Bool
  | BinaryTree.leaf _ => true
  | BinaryTree.left v l => get_value l <= v && is_max l
  | BinaryTree.right v r => get_value r <= v && is_max r
  | BinaryTree.node v l r => get_value l <= v && get_value r <= v && is_max l && is_max r

def is_min_heap : BinaryTree Nat → Bool :=
  λ t => is_complete_binary_tree t && is_min t

open BinaryTree
def exampleTree : BinaryTree Nat :=
  node 1
    (node 2
      (node 4 (leaf 8) (leaf 9))
      (node 5 (leaf 10) (leaf 11)))
    (node 3
      (node 6 (leaf 12) (leaf 13))
      (node 7 (leaf 14) (leaf 15)))

#eval is_min_heap exampleTree
-- #eval depth exampleTree2
-- #eval is_complete_binary_tree exampleTree2
