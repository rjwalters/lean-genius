import Mathlib

/-
# Rooted plane trees are counted by the Catalan numbers, via an explicit
# bijection to Dyck words

The parent gallery entry `dyck-catalan-count-oq-01`
(`Proofs/DyckCatalanCountOQ01.lean`) packages Mathlib's headline count

  `DyckWord.card_dyckWord_semilength_eq_catalan :`
  `  Fintype.card { p : DyckWord // p.semilength = n } = catalan n`

with closed forms and the Segner recurrence.  The follow-up question asks us to
count *another* Catalan family by an **explicit bijection to Dyck words**, rather
than re-deriving an arithmetic recurrence.

The originally suggested family was triangulations of a convex polygon.  A
*faithful* geometric encoding (non-crossing maximal diagonal sets, with the
apex-uniqueness lemma underpinning the recursion) is a genuinely multi-session
undertaking in Lean.  The problem statement explicitly sanctions an alternative:

  > Counting an alternative family (rooted plane trees) is an acceptable fallback
  > if the triangulation encoding proves intractable.

So this file counts **rooted plane trees** (a.k.a. ordered rooted trees), the
second-most-classical Catalan family after triangulations and one that Mathlib
does *not* count.  A rooted plane tree is a root carrying an ordered list of
subtrees, each itself a plane tree; a *forest* is an ordered list of plane trees.
Plane trees are a genuinely different combinatorial object from the rooted binary
trees Mathlib already counts (`treesOfNumNodesEq`), even though both are counted
by the same Catalan numbers.

## What is proved

* `PlaneForest ≃ Tree Unit` (`forestEquivTree`) — **Knuth's natural
  correspondence** ("left-child / right-sibling" rotation): a forest
  `t₁ t₂ … tₖ` whose first tree `t₁` has children-forest `c` maps to the binary
  tree whose left subtree encodes `c` and whose right subtree encodes
  `t₂ … tₖ`.  This is the canonical bijection between forests of plane trees and
  rooted binary trees, given here with a fully verified two-sided inverse.
* `numNodes_toTree` — the bijection is **node-preserving**: a forest with `n`
  plane-tree nodes maps to a binary tree with `n` internal nodes.
* `forestEquivDyck` — composing with Mathlib's `DyckWord.equivTree` gives the
  requested **explicit bijection `PlaneForest ≃ DyckWord`** carrying node count to
  semilength.
* `card_planeForest_size_eq_catalan` — there are `catalan n` plane forests with
  `n` nodes, the count *transported* from the parent Dyck-word count.
* `card_planeTree_size_eq_catalan` — there are `catalan n` rooted plane trees with
  `n + 1` nodes (equivalently `n` edges): the headline Catalan interpretation
  `#{plane trees with n edges} = Cₙ`.
* Positivity and a small-case sanity ladder `1, 1, 2, 5`.

Everything is over `ℕ`, fully machine-checked, 0 axioms, 0 sorries, no
`decide` / `native_decide`.
-/

namespace PlaneTreeCatalan

/- A **rooted plane tree** is a root carrying an *ordered* forest of children;
a **plane forest** is an ordered (possibly empty) list of plane trees.  The two
types are mutually recursive.  Unlike rooted binary trees, the children of a node
form a sequence of arbitrary length, so this is a genuinely distinct Catalan
family. -/
mutual
/-- A rooted plane tree: a root carrying an ordered forest of children. -/
inductive PlaneTree : Type
  | node : PlaneForest → PlaneTree
/-- A plane forest: an ordered (possibly empty) list of plane trees. -/
inductive PlaneForest : Type
  | nil : PlaneForest
  | cons : PlaneTree → PlaneForest → PlaneForest
end

namespace PlaneTree

/- The number of nodes of a plane tree (resp. forest): one for the root plus the
nodes of its children forest. -/
mutual
/-- The number of nodes of a plane tree. -/
def size : PlaneTree → ℕ
  | .node c => c.size + 1
/-- The number of plane-tree nodes in a forest. -/
def _root_.PlaneTreeCatalan.PlaneForest.size : PlaneForest → ℕ
  | .nil => 0
  | .cons t f => t.size + f.size
end

end PlaneTree

/- **Knuth's natural correspondence (forest → binary tree).**  The empty forest
maps to the empty binary tree.  A forest `t :: f` whose head `t = node c` has
children-forest `c` maps to a binary node whose *left* subtree encodes `c` (the
children of the first tree) and whose *right* subtree encodes `f` (the remaining
trees).  This is the left-child/right-sibling rotation. -/
mutual
/-- Encode a single plane tree as the binary tree of its children forest. -/
def PlaneTree.toTree : PlaneTree → Tree Unit
  | .node c => c.toTree
/-- Encode a plane forest as a rooted binary tree (Knuth's correspondence). -/
def PlaneForest.toTree : PlaneForest → Tree Unit
  | .nil => Tree.nil
  | .cons t f => Tree.node () t.toTree f.toTree
end

/-- The inverse rotation (binary tree → forest).  A binary node `node () l r`
becomes the forest whose first tree has children-forest `fromTree l`, followed by
the forest `fromTree r`. -/
def fromTree : Tree Unit → PlaneForest
  | .nil => .nil
  | .node _ l r => .cons (.node (fromTree l)) (fromTree r)

/-- `fromTree` is a left inverse of `PlaneForest.toTree`: decoding the encoding of
any forest returns the forest. -/
theorem fromTree_toTree : ∀ f : PlaneForest, fromTree f.toTree = f
  | .nil => rfl
  | .cons (.node c) f => by
      simp only [PlaneForest.toTree, PlaneTree.toTree, fromTree]
      rw [fromTree_toTree c, fromTree_toTree f]
termination_by f => f.size
decreasing_by
  · simp only [PlaneForest.size, PlaneTree.size]; omega
  · simp only [PlaneForest.size, PlaneTree.size]; omega

/-- `fromTree` is a right inverse of `PlaneForest.toTree`: encoding the decoding of
any binary tree returns the binary tree. -/
theorem toTree_fromTree : ∀ t : Tree Unit, (fromTree t).toTree = t
  | .nil => rfl
  | .node _ l r => by
      simp only [fromTree, PlaneForest.toTree, PlaneTree.toTree]
      rw [toTree_fromTree l, toTree_fromTree r]

/-- **The explicit bijection** between plane forests and rooted binary trees:
Knuth's natural correspondence, with its verified two-sided inverse. -/
def forestEquivTree : PlaneForest ≃ Tree Unit where
  toFun := PlaneForest.toTree
  invFun := fromTree
  left_inv := fromTree_toTree
  right_inv := toTree_fromTree

/-- The bijection is **node-preserving**: a forest with `n` plane-tree nodes maps
to a binary tree with `n` internal nodes. -/
theorem numNodes_toTree : ∀ f : PlaneForest, f.toTree.numNodes = f.size
  | .nil => rfl
  | .cons (.node c) f => by
      simp only [PlaneForest.toTree, PlaneTree.toTree, Tree.numNodes,
        PlaneForest.size, PlaneTree.size]
      rw [numNodes_toTree c, numNodes_toTree f]; ring
termination_by f => f.size
decreasing_by
  · simp only [PlaneForest.size, PlaneTree.size]; omega
  · simp only [PlaneForest.size, PlaneTree.size]; omega

/-- The node-preserving bijection, restricted to a fixed size `n`:
plane forests with `n` nodes correspond to binary trees with `n` internal nodes. -/
def forestEquivTreeSize (n : ℕ) :
    { f : PlaneForest // f.size = n } ≃ { b : Tree Unit // b.numNodes = n } :=
  forestEquivTree.subtypeEquiv fun f => by
    simp only [forestEquivTree, Equiv.coe_fn_mk, numNodes_toTree]

/-- Binary trees with `n` internal nodes correspond to Dyck words of semilength
`n`, via Mathlib's `DyckWord.equivTree`. -/
def treeEquivDyckSize (n : ℕ) :
    { b : Tree Unit // b.numNodes = n } ≃ { p : DyckWord // p.semilength = n } :=
  (DyckWord.equivTree.subtypeEquiv fun p => by
    rw [DyckWord.semilength_eq_numNodes_equivTree]).symm

/-- **The requested explicit bijection to Dyck words.**  Composing Knuth's
correspondence with Mathlib's Dyck-word ↔ binary-tree bijection yields an
explicit bijection between plane forests with `n` nodes and Dyck words of
semilength `n`. -/
def forestEquivDyckSize (n : ℕ) :
    { f : PlaneForest // f.size = n } ≃ { p : DyckWord // p.semilength = n } :=
  (forestEquivTreeSize n).trans (treeEquivDyckSize n)

/-- **Headline (forests).**  The number of plane forests with `n` nodes is the
`n`-th Catalan number — the count *transported* along the explicit bijection to
Dyck words, not re-derived. -/
theorem card_planeForest_size_eq_catalan (n : ℕ) :
    Nat.card { f : PlaneForest // f.size = n } = catalan n := by
  rw [Nat.card_congr (forestEquivDyckSize n), Nat.card_eq_fintype_card,
    DyckWord.card_dyckWord_semilength_eq_catalan]

/-- A plane tree `node c` has exactly one more node than its children forest `c`,
so plane trees with `n + 1` nodes correspond to forests with `n` nodes. -/
def treeEquivForestSize (n : ℕ) :
    { t : PlaneTree // t.size = n + 1 } ≃ { f : PlaneForest // f.size = n } where
  toFun := fun ⟨t, ht⟩ => match t, ht with
    | .node c, ht => ⟨c, by simpa [PlaneTree.size] using ht⟩
  invFun := fun ⟨c, hc⟩ => ⟨.node c, by simp [PlaneTree.size, hc]⟩
  left_inv := fun ⟨t, ht⟩ => by cases t; rfl
  right_inv := fun ⟨c, hc⟩ => rfl

/-- **Headline (plane trees).**  The number of rooted plane trees with `n + 1`
nodes — equivalently `n` edges — is the `n`-th Catalan number `Cₙ`.  This is the
classical Catalan interpretation `#{ordered trees with n edges} = Cₙ`, here
obtained by transporting the parent Dyck-word count along an explicit bijection. -/
theorem card_planeTree_size_eq_catalan (n : ℕ) :
    Nat.card { t : PlaneTree // t.size = n + 1 } = catalan n := by
  rw [Nat.card_congr (treeEquivForestSize n), card_planeForest_size_eq_catalan]

/-! ### Positivity -/

/-- An explicit "caterpillar" forest of each size `n`: `n` single-node trees in a
row.  It witnesses that the counted set is nonempty. -/
def caterpillar : ℕ → PlaneForest
  | 0 => .nil
  | n + 1 => .cons (.node .nil) (caterpillar n)

@[simp] theorem caterpillar_size : ∀ n, (caterpillar n).size = n
  | 0 => rfl
  | n + 1 => by
      simp only [caterpillar, PlaneForest.size, PlaneTree.size, caterpillar_size n]
      omega

/-- There is always at least one plane forest of each size `n`, so the count is
positive (giving, via the headline, a combinatorial proof that `0 < catalan n`). -/
theorem card_planeForest_size_pos (n : ℕ) :
    0 < Nat.card { f : PlaneForest // f.size = n } := by
  have hfin : Finite { f : PlaneForest // f.size = n } :=
    Finite.of_equiv _ (forestEquivDyckSize n).symm
  have hne : Nonempty { f : PlaneForest // f.size = n } :=
    ⟨⟨caterpillar n, caterpillar_size n⟩⟩
  exact Nat.card_pos_iff.mpr ⟨hne, hfin⟩

/-! ### Small-case sanity ladder: `C₀, C₁, C₂, C₃ = 1, 1, 2, 5`.

Plane trees with `1, 2, 3, 4` nodes (i.e. `0, 1, 2, 3` edges) number `1, 1, 2, 5`. -/

example : Nat.card { t : PlaneTree // t.size = 1 } = 1 := by
  rw [card_planeTree_size_eq_catalan, catalan_zero]

example : Nat.card { t : PlaneTree // t.size = 2 } = 1 := by
  rw [card_planeTree_size_eq_catalan, catalan_one]

example : Nat.card { t : PlaneTree // t.size = 3 } = 2 := by
  rw [card_planeTree_size_eq_catalan, catalan_two]

example : Nat.card { t : PlaneTree // t.size = 4 } = 5 := by
  rw [card_planeTree_size_eq_catalan, catalan_three]

end PlaneTreeCatalan
