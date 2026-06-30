import Mathlib

/-!
# Plane trees are a Catalan family: the first-child/next-sibling bijection — OQ01·OQ01

The parent entry (`dyck-catalan-count-oq-01`) records the Mathlib theorem that **Dyck
words** of semilength `n` are counted by the Catalan number `catalan n`, via Mathlib's
explicit bijection `DyckWord.equivTree : DyckWord ≃ Tree Unit` with rooted *binary* trees.
Its first open question asks:

> Enumerate **another** Catalan family not yet counted in Mathlib, and exhibit an
> *explicit bijection* to Dyck words.

This file answers it with the classic and genuinely distinct family of **plane trees**
(a.k.a. *ordered rooted trees*): a root together with an **ordered list** of subtrees of
arbitrary arity.  Mathlib counts *binary* trees (`Tree Unit`), where every node has exactly
two — possibly empty — children; plane trees are different objects (a node may have any
number of children, in order), and Mathlib does not count them.

The bridge is the textbook **natural correspondence** between forests of plane trees and
binary trees (the *first-child / next-sibling*, or *left-child right-sibling*, encoding):

* the **left** child of a binary node holds the encoding of the **children** of the first
  plane tree of a forest;
* the **right** child holds the encoding of the **remaining** trees of the forest.

This is not a relabeling of the symbols of a Dyck word — it is a recursive,
arity-changing bijection.  Composing it with Mathlib's `equivTree` gives an explicit
bijection from plane forests (and plane trees) to Dyck words, and hence the count.

## Main results

* `PlaneTree` / `PlaneForest` : ordered rooted trees and forests.
* `PlaneForest.encode` / `Tree.decode` : the natural correspondence, with both round-trips
  proved (`encode_decode`, `decode_encode`), packaged as `forestEquivTree : PlaneForest ≃
  Tree Unit`.
* `forestEquivDyck` / `forestEquivDyckSubtype` : the resulting explicit bijection of plane
  forests with Dyck words, refined to fixed size / semilength.
* `card_planeForest_numNodes_eq_catalan` : **plane forests with `n` nodes are counted by
  `catalan n`.**
* `card_planeTree_numNodes_eq_catalan` : **plane trees with `n + 1` nodes are counted by
  `catalan n`** (a plane tree is a root over a forest of `n` nodes).
* `card_planeForest_eq_card_dyckWord` : the two families literally have the same cardinality
  at every size.

Everything is over `ℕ`, fully machine-checked, 0 axioms, 0 sorries, no `decide`/
`native_decide`.
-/

namespace PlaneTreeCatalan

open scoped Classical

/-- A **plane tree** (ordered rooted tree): a root carrying an *ordered list* of child
subtrees of arbitrary arity.  This is a nested inductive type; `PlaneForest` below is the
list of subtrees. -/
inductive PlaneTree : Type
  | node : List PlaneTree → PlaneTree

/-- A **plane forest** is an ordered list of plane trees. -/
abbrev PlaneForest := List PlaneTree

namespace PlaneForest

/-- Number of nodes in a plane forest (the sum of the node counts of its trees; a tree
`node cs` contributes `1` for its root plus the nodes of its child forest `cs`). -/
def numNodes : PlaneForest → ℕ
  | [] => 0
  | (PlaneTree.node cs) :: rest => 1 + numNodes cs + numNodes rest

/-- The **first-child / next-sibling** encoding of a plane forest as a binary tree.
The left child of the root holds the encoding of the children of the first plane tree;
the right child holds the encoding of the remaining trees. -/
def encode : PlaneForest → Tree Unit
  | [] => Tree.nil
  | (PlaneTree.node cs) :: rest => Tree.node () (encode cs) (encode rest)

end PlaneForest

/-- Inverse of `PlaneForest.encode`: decode a binary tree back into a plane forest.
A `nil` becomes the empty forest; a `node` becomes a forest whose first tree has the
decoding of the left child as its own children, followed by the decoding of the right
child. -/
def Tree.decodeForest : Tree Unit → PlaneForest
  | Tree.nil => []
  | Tree.node _ l r => PlaneTree.node (Tree.decodeForest l) :: Tree.decodeForest r

namespace PlaneForest

@[simp] theorem encode_nil : encode [] = Tree.nil := by simp [encode]

@[simp] theorem encode_cons (cs rest : PlaneForest) :
    encode (PlaneTree.node cs :: rest) = Tree.node () (encode cs) (encode rest) := by
  simp [encode]

@[simp] theorem decodeForest_nil : Tree.decodeForest Tree.nil = ([] : PlaneForest) := rfl

@[simp] theorem decodeForest_node (a : Unit) (l r : Tree Unit) :
    Tree.decodeForest (Tree.node a l r) =
      PlaneTree.node (Tree.decodeForest l) :: Tree.decodeForest r := rfl

/-- `encode` followed by `decodeForest` is the identity on plane forests.  This is the
left inverse; the recursion descends into both the children of the head tree and the rest
of the forest, each strictly smaller than the input. -/
theorem decode_encode : ∀ f : PlaneForest, Tree.decodeForest (encode f) = f
  | [] => by simp
  | (PlaneTree.node cs) :: rest => by
      rw [encode_cons, decodeForest_node, decode_encode cs, decode_encode rest]

/-- `decodeForest` followed by `encode` is the identity on binary trees.  This is the
right inverse, by structural induction on the tree. -/
theorem encode_decode : ∀ t : Tree Unit, encode (Tree.decodeForest t) = t
  | Tree.nil => by simp
  | Tree.node a l r => by
      rw [decodeForest_node, encode_cons, encode_decode l, encode_decode r]

/-- The **natural correspondence** as an equivalence: plane forests are in explicit
bijection with rooted binary trees. -/
def forestEquivTree : PlaneForest ≃ Tree Unit where
  toFun := encode
  invFun := Tree.decodeForest
  left_inv := decode_encode
  right_inv := encode_decode

@[simp] theorem forestEquivTree_apply (f : PlaneForest) : forestEquivTree f = encode f := rfl

@[simp] theorem forestEquivTree_symm_apply (t : Tree Unit) :
    forestEquivTree.symm t = Tree.decodeForest t := rfl

/-- The encoding preserves size: the number of internal nodes of the encoded binary tree
equals the number of nodes of the plane forest.  (Each plane-tree root becomes one binary
internal node.) -/
theorem numNodes_encode : ∀ f : PlaneForest, (encode f).numNodes = numNodes f
  | [] => by simp [numNodes]
  | (PlaneTree.node cs) :: rest => by
      rw [encode_cons, Tree.numNodes, numNodes_encode cs, numNodes_encode rest]
      simp only [numNodes]
      ring

end PlaneForest

/-! ## From plane forests to Dyck words

We now chain `forestEquivTree` with Mathlib's `DyckWord.equivTree` to land on Dyck words,
and refine everything to fixed size. -/

namespace PlaneForest

/-- An explicit bijection between **plane forests** and **Dyck words**, obtained by
composing the first-child/next-sibling encoding with Mathlib's `DyckWord.equivTree`. -/
noncomputable def forestEquivDyck : PlaneForest ≃ DyckWord :=
  forestEquivTree.trans DyckWord.equivTree.symm

/-- Size-refined bijection: plane forests with `n` nodes correspond to binary trees with
`n` internal nodes. -/
def forestEquivTreeSubtype (n : ℕ) :
    { f : PlaneForest // numNodes f = n } ≃ { t : Tree Unit // t.numNodes = n } :=
  forestEquivTree.subtypeEquiv fun f => by
    simp [forestEquivTree_apply, numNodes_encode]

/-- Size-refined bijection: plane forests with `n` nodes correspond to Dyck words of
semilength `n`.  This is the explicit bijection the open question asks for. -/
noncomputable def forestEquivDyckSubtype (n : ℕ) :
    { f : PlaneForest // numNodes f = n } ≃ { p : DyckWord // p.semilength = n } :=
  (forestEquivTreeSubtype n).trans
    { toFun := fun ⟨t, ht⟩ => ⟨DyckWord.equivTree.symm t, by
        rw [DyckWord.semilength_eq_numNodes_equivTree, Equiv.apply_symm_apply, ht]⟩
      invFun := fun ⟨p, hp⟩ => ⟨DyckWord.equivTree p, by
        rw [← DyckWord.semilength_eq_numNodes_equivTree, hp]⟩
      left_inv := fun ⟨t, _⟩ => by simp
      right_inv := fun ⟨p, _⟩ => by simp }

noncomputable instance fintypeNumNodes (n : ℕ) :
    Fintype { f : PlaneForest // numNodes f = n } :=
  Fintype.ofEquiv _ (forestEquivDyckSubtype n).symm

/-- **Main count.** Plane forests with `n` nodes are counted by the Catalan number
`catalan n`. -/
theorem card_planeForest_numNodes_eq_catalan (n : ℕ) :
    Fintype.card { f : PlaneForest // numNodes f = n } = catalan n := by
  rw [Fintype.card_congr (forestEquivDyckSubtype n),
    DyckWord.card_dyckWord_semilength_eq_catalan]

/-- The plane-forest and Dyck-word families have the same cardinality at every size. -/
theorem card_planeForest_eq_card_dyckWord (n : ℕ) :
    Fintype.card { f : PlaneForest // numNodes f = n }
      = Fintype.card { p : DyckWord // p.semilength = n } :=
  Fintype.card_congr (forestEquivDyckSubtype n)

end PlaneForest

/-! ## The single-tree version

A plane tree is exactly a root placed over a forest of its children, so plane trees with
`n + 1` nodes correspond to plane forests with `n` nodes — and hence to `catalan n`. -/

namespace PlaneTree

/-- Number of nodes of a plane tree (`1` for the root plus the nodes of its children). -/
def numNodes : PlaneTree → ℕ
  | PlaneTree.node cs => 1 + PlaneForest.numNodes cs

@[simp] theorem numNodes_node (cs : PlaneForest) :
    (PlaneTree.node cs).numNodes = 1 + PlaneForest.numNodes cs := rfl

/-- The constructor `node : PlaneForest → PlaneTree` is an equivalence: every plane tree is
the root over a unique forest of children. -/
def equivForest : PlaneTree ≃ PlaneForest where
  toFun := fun t => match t with | PlaneTree.node cs => cs
  invFun := PlaneTree.node
  left_inv := fun t => by cases t; rfl
  right_inv := fun _ => rfl

/-- Size-refined: plane trees with `n + 1` nodes correspond to plane forests with `n`
nodes (delete the root). -/
def equivForestSubtype (n : ℕ) :
    { t : PlaneTree // t.numNodes = n + 1 } ≃ { f : PlaneForest // PlaneForest.numNodes f = n } :=
  equivForest.subtypeEquiv fun t => by
    cases t with
    | node cs => simp only [equivForest, numNodes, Equiv.coe_fn_mk]; omega

noncomputable instance fintypeNumNodes (n : ℕ) :
    Fintype { t : PlaneTree // t.numNodes = n + 1 } :=
  Fintype.ofEquiv _ (equivForestSubtype n).symm

/-- **Plane-tree count.** Plane trees with `n + 1` nodes are counted by `catalan n`. -/
theorem card_planeTree_numNodes_eq_catalan (n : ℕ) :
    Fintype.card { t : PlaneTree // t.numNodes = n + 1 } = catalan n := by
  rw [Fintype.card_congr (equivForestSubtype n),
    PlaneForest.card_planeForest_numNodes_eq_catalan]

end PlaneTree

/-! ## Sanity checks (small cases) -/

/-- There is a unique empty plane forest of size `0` (it is `catalan 0 = 1`). -/
example : Fintype.card { f : PlaneForest // PlaneForest.numNodes f = 0 } = 1 := by
  rw [PlaneForest.card_planeForest_numNodes_eq_catalan]; exact catalan_zero

/-- Plane forests of size `3` number `catalan 3 = 5`. -/
example : Fintype.card { f : PlaneForest // PlaneForest.numNodes f = 3 } = 5 := by
  rw [PlaneForest.card_planeForest_numNodes_eq_catalan]; exact catalan_three

/-- Plane trees with `4` nodes number `catalan 3 = 5`. -/
example : Fintype.card { t : PlaneTree // t.numNodes = 3 + 1 } = 5 := by
  rw [PlaneTree.card_planeTree_numNodes_eq_catalan]; exact catalan_three

end PlaneTreeCatalan
