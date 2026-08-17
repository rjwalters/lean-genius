import Proofs.Erdos85Problem

/-!
# The `k = 3` binary existence jaw: an 8-regular C4-free graph on 63 vertices

Explicit instantiation of the even polarity core (`Erdos85PolarityEven`) at
`K = F₈`: take the polarity graph of `PG(2,8)` (adjacency = orthogonality
`p · r = 0` over `F₈ = F₂[x]/(x³+x+1)`), delete the nine absolute points and
the nucleus `(1,1,1)`.  What remains is an 8-regular `C₄`-free graph on
`63 = 8² − 1` vertices — the concrete first witness of the binary drop family
`q = 2^k, k ≥ 3` (goal #22 pivot), the analogue at 63/64 of the Boza-type
`(48,7)` witness.  Externally cross-checked (Python, exhaustive: 8-regular,
all pairs of vertices have at most one common neighbor).

Adjacency is stored as sorted neighbor rows for fast kernel `decide`.
-/

namespace Erdos85

open SimpleGraph

/-- Sorted neighbor rows of the 63-vertex even polarity core over `F₈`. -/
def sixtyThreeRegularRows : Fin 63 → List (Fin 63) :=
  fun i => [
    [1, 8, 21, 28, 35, 42, 49, 56],
    [0, 8, 9, 10, 11, 12, 13, 14],
    [5, 8, 18, 22, 31, 37, 48, 52],
    [6, 8, 19, 27, 29, 45, 51, 60],
    [7, 8, 20, 25, 36, 47, 53, 59],
    [2, 8, 15, 24, 33, 38, 43, 61],
    [3, 8, 16, 26, 32, 41, 50, 58],
    [4, 8, 17, 34, 40, 44, 54, 57],
    [0, 1, 2, 3, 4, 5, 6, 7],
    [1, 12, 18, 25, 32, 46, 54, 61],
    [1, 13, 19, 26, 33, 40, 47, 55],
    [1, 14, 20, 27, 34, 41, 48, 62],
    [1, 9, 15, 23, 37, 44, 51, 58],
    [1, 10, 16, 30, 38, 45, 52, 59],
    [1, 11, 17, 24, 31, 39, 53, 60],
    [5, 12, 24, 29, 41, 44, 55, 59],
    [6, 13, 22, 34, 38, 46, 53, 58],
    [7, 14, 23, 32, 40, 43, 52, 60],
    [2, 9, 26, 31, 36, 45, 54, 62],
    [3, 10, 25, 33, 39, 48, 51, 57],
    [4, 11, 27, 30, 37, 47, 50, 61],
    [0, 42, 43, 44, 45, 46, 47, 48],
    [2, 16, 25, 34, 37, 42, 55, 60],
    [12, 17, 27, 33, 36, 42, 52, 58],
    [5, 14, 15, 26, 30, 42, 53, 57],
    [4, 9, 19, 22, 32, 39, 42, 59],
    [6, 10, 18, 24, 40, 42, 50, 62],
    [3, 11, 20, 23, 29, 38, 42, 54],
    [0, 49, 50, 51, 52, 53, 54, 55],
    [3, 15, 27, 31, 40, 46, 49, 59],
    [13, 20, 24, 32, 37, 45, 49, 57],
    [2, 14, 18, 29, 39, 47, 49, 58],
    [6, 9, 17, 25, 30, 41, 43, 49],
    [5, 10, 19, 23, 34, 36, 49, 61],
    [7, 11, 16, 22, 33, 44, 49, 62],
    [0, 56, 57, 58, 59, 60, 61, 62],
    [4, 18, 23, 33, 41, 45, 53, 56],
    [2, 12, 20, 22, 30, 40, 51, 56],
    [5, 13, 16, 27, 39, 43, 54, 56],
    [14, 19, 25, 31, 38, 44, 50, 56],
    [7, 10, 17, 26, 29, 37, 46, 56],
    [6, 11, 15, 32, 36, 48, 55, 56],
    [0, 21, 22, 23, 24, 25, 26, 27],
    [5, 17, 21, 32, 38, 47, 51, 62],
    [7, 12, 15, 21, 34, 39, 45, 50],
    [3, 13, 18, 21, 30, 36, 44, 60],
    [9, 16, 21, 29, 40, 48, 53, 61],
    [4, 10, 20, 21, 31, 43, 55, 58],
    [2, 11, 19, 21, 41, 46, 52, 57],
    [0, 28, 29, 30, 31, 32, 33, 34],
    [6, 20, 26, 28, 39, 44, 52, 61],
    [3, 12, 19, 28, 37, 43, 53, 62],
    [2, 13, 17, 23, 28, 48, 50, 59],
    [4, 14, 16, 24, 28, 36, 46, 51],
    [7, 9, 18, 27, 28, 38, 55, 57],
    [10, 15, 22, 28, 41, 47, 54, 60],
    [0, 35, 36, 37, 38, 39, 40, 41],
    [7, 19, 24, 30, 35, 48, 54, 58],
    [6, 12, 16, 23, 31, 35, 47, 57],
    [4, 13, 15, 25, 29, 35, 52, 62],
    [3, 14, 17, 22, 35, 45, 55, 61],
    [5, 9, 20, 33, 35, 46, 50, 60],
    [11, 18, 26, 34, 35, 43, 51, 59]].get i

/-- The 63-vertex, 8-regular polarity-core graph. -/
def sixtyThreeRegular : SimpleGraph (Fin 63) where
  Adj i j := j ∈ sixtyThreeRegularRows i ∧ i ≠ j
  symm.symm := by decide
  loopless.irrefl := fun _ h => h.2 rfl

instance : DecidableRel sixtyThreeRegular.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ _))

set_option maxRecDepth 10000 in
theorem sixtyThreeRegular_degree : ∀ v, sixtyThreeRegular.degree v = 8 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem sixtyThreeRegular_common_le_one : ∀ x y : Fin 63, x ≠ y →
    (sixtyThreeRegular.neighborFinset x ∩ sixtyThreeRegular.neighborFinset y).card ≤ 1 := by
  decide

theorem sixtyThreeRegular_not_containsC4 :
    ¬ containsC4 (Fin 63) sixtyThreeRegular :=
  not_containsC4_of_forall_common_le_one sixtyThreeRegular_common_le_one

/-- **The `k = 3` binary existence jaw**: `C4FreeMinDegreeWitness 63 8`. -/
theorem c4FreeMinDegreeWitness_sixtyThree_eight :
    C4FreeMinDegreeWitness 63 8 := by
  refine ⟨sixtyThreeRegular, inferInstance, ?_, sixtyThreeRegular_not_containsC4⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  intro v
  rw [sixtyThreeRegular_degree v]

end Erdos85
