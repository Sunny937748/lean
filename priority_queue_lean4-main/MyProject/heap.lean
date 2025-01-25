import Mathlib.Data.Real.Basic
import Mathlib.Tactic

inductive BinaryTree (α : Type) [Ord α] where
  | empty : BinaryTree α
  | leaf : α → BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α

def is_empty {α : Type} [Ord α] : BinaryTree α → Bool
  | BinaryTree.empty => true
  | _ => false

def b_size {α : Type} [Ord α] : BinaryTree α → Nat
  | BinaryTree.empty => 0
  | BinaryTree.leaf _ => 1
  | BinaryTree.node _ l r => 1 + b_size l + b_size r

def b_depth {α : Type}[Ord α] : BinaryTree α → Nat
  | BinaryTree.empty => 0
  | BinaryTree.leaf _ => 1
  | BinaryTree.node _ l r => 1 + max (b_depth l) (b_depth r)

--层次遍历（BFS）
--检查完全二叉树是否也是平衡树
--判断是否为二叉搜索树

--查找最大值
def get_max_value {α : Type} [Ord α] : BinaryTree α → Option α
  | BinaryTree.empty => none
  | BinaryTree.leaf v => some v
  | BinaryTree.node _ _ r =>
    match get_max_value r with
    | some max => some max
    | none => none

--翻转二叉树
def invert_binary_tree {α : Type} [Ord α] : BinaryTree α → BinaryTree α
  | BinaryTree.empty => BinaryTree.empty
  | BinaryTree.leaf v => BinaryTree.leaf v
  | BinaryTree.node v l r => BinaryTree.node v (invert_binary_tree r) (invert_binary_tree l)

--后序遍历
def postorder {α : Type} [Ord α] : BinaryTree α → List α
  | BinaryTree.empty => []
  | BinaryTree.leaf v => [v]
  | BinaryTree.node v l r => postorder l ++ postorder r ++ [v]

--中序遍历 
def inorder {α : Type} [Ord α] : BinaryTree α → List α
  | BinaryTree.empty => []
  | BinaryTree.leaf v => [v]
  | BinaryTree.node v l r => inorder l ++ [v] ++ inorder r
--计算二叉树的叶子节点数
def count_leaves {α : Type} [Ord α] : BinaryTree α → Nat
  | BinaryTree.empty => 0
  | BinaryTree.leaf _ => 1
  | BinaryTree.node _ l r => count_leaves l + count_leaves r

--镜像二叉树
def mirror {α : Type} [Ord α] : BinaryTree α → BinaryTree α
  | BinaryTree.empty => BinaryTree.empty
  | BinaryTree.leaf v => BinaryTree.leaf v
  | BinaryTree.node v l r => BinaryTree.node v (mirror r) (mirror l)

--统计完全二叉树的节点数
def count_nodes {α : Type} [Ord α] : BinaryTree α → Nat
  | BinaryTree.empty => 0
  | BinaryTree.leaf _ => 1
  | BinaryTree.node _ l r =>
    if b_depth l == b_depth r then
      2 ^ b_depth l - 1
    else
      1 + count_nodes l + count_nodes r

--将二叉树转换为列表
def flatten_to_list {α : Type} [Ord α] : BinaryTree α → List α :=
  inorder

--路径搜索
def find_all_paths {α : Type} [Ord α] : BinaryTree α → List (List α)
  | BinaryTree.empty => []
  | BinaryTree.leaf v => [[v]]
  | BinaryTree.node v l r =>
    let leftPaths := find_all_paths l
    let rightPaths := find_all_paths r
    (leftPaths ++ rightPaths).map (fun path => v :: path)

--求二叉树的直径
def diameter {α : Type} [Ord α] : BinaryTree α → Nat
  | BinaryTree.empty => 0
  | BinaryTree.leaf _ => 0
  | BinaryTree.node _ l r =>
    let leftDepth := b_depth l
    let rightDepth := b_depth r
    let leftDiameter := diameter l
    let rightDiameter := diameter r
    max (leftDepth + rightDepth) (max leftDiameter rightDiameter)

--计算所有路径的长度
def sum_of_path_lengths {α : Type} [Ord α] : BinaryTree α → Nat
  | BinaryTree.empty => 0
  | t =>
    let rec helper (t : BinaryTree α) (depth : Nat) : Nat :=
      match t with
      | BinaryTree.empty => 0
      | BinaryTree.leaf _ => depth
      | BinaryTree.node _ l r => helper l (depth + 1) + helper r (depth + 1)
    helper t 0


def is_complete_binary_tree {α : Type} [Ord α] : BinaryTree α → Bool
  | BinaryTree.empty => true
  | BinaryTree.leaf _ => true
  | BinaryTree.node _ l r =>
    if b_depth l == b_depth r
    then if b_size l == 2 ^ (b_depth l) - 1
      then  is_complete_binary_tree r
      else false
    else b_depth l == b_depth r + 1
    && is_complete_binary_tree l
    && is_complete_binary_tree r

def insert_into_binary_tree {α : Type} [Ord α] : α → BinaryTree α → BinaryTree α
  | x, BinaryTree.empty => BinaryTree.leaf x
  | x, BinaryTree.leaf y => BinaryTree.node y (BinaryTree.leaf x) (BinaryTree.empty)
  | x, BinaryTree.node y l r =>
    if b_size l < 2 ^ (b_depth l) - 1 then BinaryTree.node y (insert_into_binary_tree x l) r
    else
      if b_size r < 2 ^ (b_depth l) - 1 then BinaryTree.node y l (insert_into_binary_tree x r)
      else BinaryTree.node y (insert_into_binary_tree x l) r

def array_to_heap {α : Type} [Ord α] (arr : Array α) : BinaryTree α :=
  arr.foldl (λ acc x => insert_into_binary_tree x acc) BinaryTree.empty

def array_to_max_heap (arr : Array Nat) : BinaryTree Nat :=
  let sortedArr := arr.qsort (· > ·)
  array_to_heap sortedArr

def array_to_min_heap (arr : Array Nat) : BinaryTree Nat :=
  let sortedArr := arr.qsort (· < ·)
  array_to_heap sortedArr

def preorder {α : Type}[Ord α] : BinaryTree α → List α
  | BinaryTree.empty => []
  | BinaryTree.leaf v => [v]
  | BinaryTree.node v l r => v :: preorder l ++ preorder r

def get_value : BinaryTree Nat → Nat
  | BinaryTree.empty => panic! "Cannot get value from an empty node"
  | BinaryTree.leaf v => v
  | BinaryTree.node v _ _ => v

def is_min : BinaryTree Nat → Bool
  | BinaryTree.empty => true
  | BinaryTree.leaf _ => true
  | BinaryTree.node v l r =>
    if is_empty l then true
      else get_value l >= v
    && if is_empty r then true
      else get_value r >= v
    && is_min l
    && is_min r

def is_max : BinaryTree Nat → Bool
  | BinaryTree.empty => true
  | BinaryTree.leaf _ => true
  | BinaryTree.node v l r =>
    if is_empty l then true
      else get_value l <= v
    && if is_empty r then true
      else get_value r <= v
    && is_max l
    && is_max r

def is_min_heap : BinaryTree Nat → Bool :=
  λ t => is_complete_binary_tree t && is_min t

def is_max_heap : BinaryTree Nat → Bool :=
  λ t => is_complete_binary_tree t && is_max t

def get_top {h : BinaryTree Nat} : Nat :=
  get_value h

def get_end_value : BinaryTree Nat → Nat
  | BinaryTree.empty => panic! "Cannot get value from an empty node"
  | BinaryTree.leaf v => v
  | BinaryTree.node _ l r =>
    if b_size l <= 2 ^ (b_depth l) - 1 && b_size r == 2 ^ (b_depth l) - 1 then get_end_value l
    else get_end_value r

def remove_last_node : BinaryTree Nat → BinaryTree Nat
  | BinaryTree.empty => BinaryTree.empty
  | BinaryTree.leaf v => BinaryTree.empty
  | BinaryTree.node v l r =>
    if b_size r > b_size l then
      let newRight := remove_last_node r
      BinaryTree.node v l newRight
    else
      let newLeft := remove_last_node l
      BinaryTree.node v newLeft r

def delete_top {h : BinaryTree Nat} : BinaryTree Nat :=
  sorry

set_option linter.unusedVariables false
def min_bubble_down : BinaryTree Nat → BinaryTree Nat
  | BinaryTree.empty => BinaryTree.empty
  | BinaryTree.leaf v => BinaryTree.leaf v
  | BinaryTree.node v l r =>
   match l, r with
    | BinaryTree.empty, _ => BinaryTree.node v l r
    | BinaryTree.leaf lv, BinaryTree.empty =>
      if v > lv then BinaryTree.node lv (BinaryTree.leaf v) r
      else BinaryTree.node v l r
    | BinaryTree.leaf lv, BinaryTree.leaf rv =>
      if v > lv then BinaryTree.node lv (BinaryTree.leaf v) r
      else if v > rv then BinaryTree.node rv l (BinaryTree.leaf v)
      else BinaryTree.node v l r
    | BinaryTree.leaf lv, BinaryTree.node rv rl rr => BinaryTree.node v l r
    | BinaryTree.node lv ll lr, BinaryTree.empty => BinaryTree.node v l r
    | BinaryTree.node lv ll lr, BinaryTree.leaf rv =>
      if v > lv then BinaryTree.node lv (min_bubble_down (BinaryTree.node v ll lr)) r
      else if v > rv then BinaryTree.node rv l (BinaryTree.leaf v)
      else BinaryTree.node v l r
    | BinaryTree.node lv ll lr, BinaryTree.node rv rl rr =>
      if v > lv && lv < rv then BinaryTree.node lv (min_bubble_down (BinaryTree.node v ll lr)) r
      else if v > lv && lv > rv then BinaryTree.node rv l (min_bubble_down (BinaryTree.node v rl rr))
      else BinaryTree.node v l r

def change_to_min_heap :BinaryTree Nat → BinaryTree Nat
  | BinaryTree.empty => BinaryTree.empty
  | BinaryTree.leaf v => BinaryTree.leaf v
  | BinaryTree.node v l r =>
    let l_fixed := change_to_min_heap l
    let r_fixed := change_to_min_heap r
    let updated := BinaryTree.node v l_fixed r_fixed
    min_bubble_down updated

-- Testing the functions with an example
open BinaryTree

def exampleTree : BinaryTree Nat :=
  node 100
    (node 2
      (node 11 (leaf 8) (leaf 23))
      (node 55 (leaf 12) (leaf 131)))
    (node 25
      (node 6 (leaf 13) (leaf 134))
      (node 4 (leaf 145) (leaf 153)))

def exampleTree2 : BinaryTree Nat :=
  empty

def exampleTree3 : BinaryTree Nat :=
  node 1
    empty (leaf 2)

def exampleArray : Array Nat := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

-- Original tests
#eval array_to_min_heap exampleArray
#eval remove_last_node (array_to_min_heap exampleArray)
#eval (insert_into_binary_tree 1 (array_to_min_heap exampleArray))
#eval is_min_heap (insert_into_binary_tree 1 (array_to_min_heap exampleArray))
#eval is_min_heap (change_to_min_heap (insert_into_binary_tree 1 (array_to_min_heap exampleArray)))
#eval is_min_heap exampleTree
#eval change_to_min_heap (exampleTree)
#eval is_min_heap ((change_to_min_heap (exampleTree)))
#eval is_complete_binary_tree exampleTree3

-- New tests for added functions
#eval get_max_value exampleTree 
#eval invert_binary_tree exampleTree 
#eval postorder exampleTree 
#eval inorder exampleTree 
#eval count_leaves exampleTree 
#eval mirror exampleTree 
#eval count_nodes exampleTree
#eval flatten_to_list exampleTree 
#eval find_all_paths exampleTree 
#eval diameter exampleTree 
#eval sum_of_path_lengths exampleTree 
