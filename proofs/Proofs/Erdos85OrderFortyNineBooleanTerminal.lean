import Mathlib.Tactic

/-!
# Kernel-checkable Boolean terminal for the order-49 branch

This file gives a compact, label-level encoding of a graph on 49 vertices.
Only the `choose(49,2) = 1176` unordered edge bits are stored.  Symmetry and
looplessness are therefore true by construction.  The remaining conditions
are exactly those used by the independently generated DIMACS instances:

* the prescribed high-support of every vertex;
* degrees eight on the initial high segment and seven elsewhere;
* at most one common neighbor for every two distinct vertices;
* every low neighborhood meets every high neighborhood.

The final condition is the graph-facing support-partition law.  Its
uniqueness is already implied by the common-neighbor bound.
-/

namespace Erdos85

/-- Zero-based position of `{i,j}` in the lexicographic list of the 1176
unordered pairs from `Fin 49`, for `i ≠ j`. -/
def orderFortyNineEdgeIndex (i j : Fin 49) : Nat :=
  let a := min i.val j.val
  let b := max i.val j.val
  1176 - ((49 - a) * (48 - a) / 2) + (b - a) - 1

/-- Symmetric loopless adjacency read from the 1176 unordered edge bits. -/
def orderFortyNineBitAdj (edges : BitVec 1176) (i j : Fin 49) : Bool :=
  if i = j then false else edges.getLsbD (orderFortyNineEdgeIndex i j)

/-- The 49-bit adjacency row of a vertex. -/
def orderFortyNineBitRow (edges : BitVec 1176) (i : Fin 49) : BitVec 49 :=
  BitVec.ofBoolListLE (List.ofFn fun j : Fin 49 => orderFortyNineBitAdj edges i j)

/-- The prescribed high-support masks, read as nine-bit vectors. -/
def orderFortyNineSupportMask (masks : Array Nat) (i : Fin 49) : BitVec 9 :=
  BitVec.ofNat 9 (masks.getD i.val 0)

/-- The 49-bit indicator of the vertices incident with high point `w`. -/
def orderFortyNineSupportColumn (masks : Array Nat) (w : Fin 9) : BitVec 49 :=
  BitVec.ofBoolListLE (List.ofFn fun i : Fin 49 =>
    (orderFortyNineSupportMask masks i).getLsbD w.val)

/-- Boolean constraints common to every classified high-support instance. -/
def orderFortyNineBooleanConstraints
    (h : Nat) (masks : Array Nat) (edges : BitVec 1176) : Prop :=
  masks.size = 49 ∧ h ≤ 9 ∧
  (∀ i : Fin 49,
    (orderFortyNineBitRow edges i).cpop = if i.val < h then 8 else 7) ∧
  (∀ i j : Fin 49, i ≠ j →
    ((orderFortyNineBitRow edges i) &&&
      orderFortyNineBitRow edges j).cpop ≤ 1) ∧
  (∀ i : Fin 49, ∀ w : Fin 9, w.val < h →
    orderFortyNineBitAdj edges i ⟨w.val, by omega⟩ =
      (orderFortyNineSupportMask masks i).getLsbD w.val) ∧
  (∀ i : Fin 49, h ≤ i.val → ∀ w : Fin 9, w.val < h →
    (((orderFortyNineBitRow edges i) &&&
      orderFortyNineSupportColumn masks w).cpop = 1))

/-- First canonical four-triple support system at `h=9`:
`012, 345, 367, 468`.  Vertices are ordered as in the certification
manifest: highs, triples, uncovered pairs, then singleton repetitions. -/
def orderFortyNineH9T4Rep0Masks : Array Nat :=
  #[0, 0, 0, 0, 0, 0, 0, 0, 0,
    7, 56, 200, 336,
    9, 17, 33, 65, 129, 257, 10, 18, 34, 66, 130, 258,
    12, 20, 36, 68, 132, 260, 264, 144, 96, 160, 288, 384,
    1, 2, 4, 8, 8, 16, 16, 32, 64, 64, 128, 256]

end Erdos85
