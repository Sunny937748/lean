git config --global url."https://mirrors.ustc.edu.cn/".insteadOf "https://github.com/"
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

-- 定义二叉树的结构
inductive BinaryTree (α : Type) [Ord α] where
  | leaf : α → BinaryTree α
  | left : α → BinaryTree α → BinaryTree α
  | right : α → BinaryTree α → BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α

namespace BinaryTree

variables {α : Type} [Ord α]

/-- 获取二叉树的节点值 -/
def get_value : BinaryTree α → α
  | BinaryTree.leaf v => v
  | BinaryTree.left v _ => v
  | BinaryTree.right v _ => v
  | BinaryTree.node v _ _ => v

/-- 判断是否为空堆 -/
def is_empty : BinaryTree α → Bool
  | BinaryTree.leaf _ => false
  | _ => false

/-- 计算二叉树的大小（节点数） -/
def size : BinaryTree α → Nat
  | BinaryTree.leaf _ => 1
  | BinaryTree.left _ l => 1 + size l
  | BinaryTree.right _ r => 1 + size r
  | BinaryTree.node _ l r => 1 + size l + size r

/-- 计算二叉树的深度（高度） -/
def depth : BinaryTree α → Nat
  | BinaryTree.leaf _ => 1
  | BinaryTree.left _ l => 1 + depth l
  | BinaryTree.right _ r => 1 + depth r
  | BinaryTree.node _ l r => 1 + max (depth l) (depth r)

/-- 判断二叉树是否为完全二叉树 -/
def is_complete_binary_tree : BinaryTree α → Bool
  | BinaryTree.leaf _ => true
  | BinaryTree.left _ l => depth l = 1
  | BinaryTree.right _ _ => false
  | BinaryTree.node _ l r =>
      depth l >= depth r && size l >= size r && is_complete_binary_tree l && is_complete_binary_tree r

/-- 先序遍历二叉树 -/
def preorder : BinaryTree α → List α
  | BinaryTree.leaf v => [v]
  | BinaryTree.left v l => v :: preorder l
  | BinaryTree.right v r => v :: preorder r
  | BinaryTree.node v l r => v :: preorder l ++ preorder r

/-- 判断二叉树是否为小顶堆 -/
def is_min_heap : BinaryTree α → Bool :=
  λ t => is_complete_binary_tree t &&
         match t with
         | leaf _ => true
         | left v l => get_value l >= v && is_min_heap l
         | right v r => get_value r >= v && is_min_heap r
         | node v l r => get_value l >= v && get_value r >= v && is_min_heap l && is_min_heap r

/-- 合并两个小顶堆 -/
def merge : BinaryTree α → BinaryTree α → BinaryTree α
  | t1@(leaf v1), t2@(leaf v2) =>
    if v1 ≤ v2 then left v1 t2 else left v2 t1
  | t1@(leaf v1), t2@(left v2 l2) =>
    if v1 ≤ v2 then left v1 t2 else left v2 (merge t1 l2)
  | t1@(leaf v1), t2@(right v2 r2) =>
    if v1 ≤ v2 then right v1 t2 else right v2 (merge t1 r2)
  | t1@(leaf v1), t2@(node v2 l2 r2) =>
    if v1 ≤ v2 then node v1 t2 (leaf v1) else node v2 (merge t1 l2) r2
  | t1@(node v1 l1 r1), t2@(node v2 l2 r2) =>
    if v1 ≤ v2 then node v1 l1 (merge r1 t2) else node v2 l2 (merge t1 r2)
  | t1@(node v1 l1 r1), t2@(leaf v2) =>
    if v1 ≤ v2 then node v1 l1 (merge r1 t2) else left v2 t1
  | t1@(node v1 l1 r1), t2@(left v2 l2) =>
    if v1 ≤ v2 then node v1 l1 (merge r1 t2) else left v2 (merge t1 l2)
  | t1@(node v1 l1 r1), t2@(right v2 r2) =>
    if v1 ≤ v2 then node v1 l1 (merge r1 t2) else right v2 (merge t1 r2)
  | t1, t2 => t1 -- fallback

/-- 上溢：调整堆使根节点值小于子节点值 -/
def bubble_up : BinaryTree α → BinaryTree α
  | BinaryTree.leaf v => BinaryTree.leaf v
  | BinaryTree.left v l =>
    if v > get_value l then BinaryTree.left (get_value l) (bubble_up (BinaryTree.leaf v))
    else BinaryTree.left v l
  | BinaryTree.right v r =>
    if v > get_value r then BinaryTree.right (get_value r) (bubble_up (BinaryTree.leaf v))
    else BinaryTree.right v r
  | BinaryTree.node v l r =>
    if v > get_value l && get_value l <= get_value r then
      BinaryTree.node (get_value l) (bubble_up (BinaryTree.leaf v)) r
    else if v > get_value r then
      BinaryTree.node (get_value r) l (bubble_up (BinaryTree.leaf v))
    else BinaryTree.node v l r

/-- 下溢：调整堆使父节点值小于子节点值 -/
def bubble_down : BinaryTree α → BinaryTree α
  | BinaryTree.leaf v => BinaryTree.leaf v
  | BinaryTree.left v l =>
    if v > get_value l then BinaryTree.left (get_value l) (bubble_down (BinaryTree.leaf v))
    else BinaryTree.left v l
  | BinaryTree.right v r =>
    if v > get_value r then BinaryTree.right (get_value r) (bubble_down (BinaryTree.leaf v))
    else BinaryTree.right v r
  | BinaryTree.node v l r =>
    if get_value l <= get_value r && v > get_value l then
      BinaryTree.node (get_value l) (bubble_down (BinaryTree.leaf v)) r
    else if get_value r < get_value l && v > get_value r then
      BinaryTree.node (get_value r) l (bubble_down (BinaryTree.leaf v))
    else BinaryTree.node v l r

/-- 插入一个元素到小顶堆 -/
def insert (x : α) (h : BinaryTree α) : BinaryTree α :=
  bubble_up (BinaryTree.node x h (BinaryTree.leaf x))

/-- 弹出小顶堆的最小值 -/
def pop_min : BinaryTree α → Option (α × BinaryTree α)
  | BinaryTree.leaf v => some (v, BinaryTree.leaf v)
  | BinaryTree.node v l r =>
    let new_heap := bubble_down (BinaryTree.node v l r)
    some (v, new_heap)
  | _ => none

end BinaryTree

-- 示例小顶堆
open BinaryTree

def exampleHeap1 : BinaryTree Nat :=
  node 1
    (node 2 (leaf 4) (leaf 5))
    (node 3 (leaf 6) (leaf 7))

def exampleHeap2 : BinaryTree Nat :=
  node 8
    (node 9 (leaf 10) (leaf 11))
    (node 12 (leaf 13) (leaf 14))

-- 测试代码
#eval size exampleHeap1
#eval depth exampleHeap1
#eval is_min_heap exampleHeap1
#eval merge exampleHeap1 exampleHeap2
#eval insert 0 exampleHeap1
#eval pop_min exampleHeap1
