/-
# Erdős Problem #1018, OQ-04 → incomplete-01 → OQ-01
## Sharp edge-count threshold for the planar obstruction in Kₙ

The density argument behind Erdős #1018 OQ-04 (`Erdos1018OQ04Incomplete01.lean`)
rests on Euler's planar edge bound: a simple graph on `n ≥ 3` vertices that
embeds in the plane has at most `3n − 6` edges. A dense graph eventually exceeds
this bound and therefore contains a non-planar configuration. The complete graph
`Kₙ` has `C(n, 2) = n(n − 1)/2` edges, so a natural and fully elementary question
underlies that argument:

> For exactly which `n` does the edge count of `Kₙ` *by itself* force
> non-planarity — i.e. when is `C(n, 2) > 3n − 6`?

This file pins the threshold down precisely and shows it is **sharp**:

* `Kn_exceeds_planar_bound` — for every `n ≥ 5`, `3n − 6 < C(n, 2)`.
* `Kn_within_planar_bound` — for `3 ≤ n ≤ 4`, `C(n, 2) ≤ 3n − 6`
  (in fact with equality: `K₃` and `K₄` meet the bound exactly).
* `planar_obstruction_threshold` — for `n ≥ 3`,
  `3n − 6 < C(n, 2) ↔ 5 ≤ n`.

So the counting obstruction switches on exactly at `n = 5`, matching the
classical fact that `K₅` (10 edges, bound 9) is the smallest complete graph
that cannot be planar, while `K₃` (3 = 3) and `K₄` (6 = 6) sit right on the
boundary and are planar.

This is the elementary first-moment core of the density argument, isolated and
machine-checked. All results are fully verified: **0 axioms, 0 sorries.**

## References

- Euler, L. (1758). Planar graph edge bound `e ≤ 3v − 6`.
- Kuratowski, K. (1930). "Sur le problème des courbes gauches en topologie."
- Parent: `Erdos1018OQ04Incomplete01.lean` (concrete embeddability + K₃/K₄/K₅).
-/
import Mathlib

namespace Erdos1018OQ04Incomplete01OQ01

/-- Number of edges of the complete graph `Kₙ`: the binomial coefficient `C(n, 2)`. -/
def completeEdges (n : ℕ) : ℕ := n.choose 2

/-- Euler's planar edge bound for a simple graph on `n ≥ 3` vertices:
    at most `3n − 6` edges. -/
def planarBound (n : ℕ) : ℕ := 3 * n - 6

/-- Pascal's identity in the form needed here:
    `C(n + 1, 2) = C(n, 2) + n`. -/
lemma completeEdges_succ (n : ℕ) : completeEdges (n + 1) = completeEdges n + n := by
  simp only [completeEdges]
  have h : (n + 1).choose 2 = n.choose 1 + n.choose 2 := Nat.choose_succ_succ n 1
  rw [Nat.choose_one_right] at h
  omega

/-- **Counting obstruction.** For every `n ≥ 5` the complete graph `Kₙ` has
    strictly more than `3n − 6` edges, so it cannot satisfy Euler's planar
    bound. -/
theorem Kn_exceeds_planar_bound (n : ℕ) (hn : 5 ≤ n) :
    planarBound n < completeEdges n := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- `K₅`: `3·5 − 6 = 9 < 10 = C(5, 2)`.
    decide
  | succ n hn ih =>
    rw [completeEdges_succ]
    simp only [planarBound] at ih ⊢
    omega

/-- **Sharpness, lower side.** For `3 ≤ n ≤ 4` the edge count of `Kₙ` does *not*
    exceed Euler's bound; the two coincide (`K₃: 3 = 3`, `K₄: 6 = 6`). -/
theorem Kn_within_planar_bound (n : ℕ) (h3 : 3 ≤ n) (h4 : n ≤ 4) :
    completeEdges n ≤ planarBound n := by
  interval_cases n <;> decide

/-- **The threshold is exactly `n = 5`.** For every `n ≥ 3`, the edge count of
    `Kₙ` exceeds the planar bound `3n − 6` if and only if `n ≥ 5`. This isolates
    the first-moment core of the Erdős #1018 OQ-04 density argument. -/
theorem planar_obstruction_threshold (n : ℕ) (hn : 3 ≤ n) :
    planarBound n < completeEdges n ↔ 5 ≤ n := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hle : completeEdges n ≤ planarBound n :=
      Kn_within_planar_bound n hn (by omega)
    omega
  · exact Kn_exceeds_planar_bound n

/-! ### Boundary witnesses -/

/-- `K₃` meets Euler's bound with equality: `C(3, 2) = 3 = 3·3 − 6`. -/
theorem K3_meets_bound : completeEdges 3 = planarBound 3 := by decide

/-- `K₄` meets Euler's bound with equality: `C(4, 2) = 6 = 3·4 − 6`. -/
theorem K4_meets_bound : completeEdges 4 = planarBound 4 := by decide

/-- `K₅` is the first complete graph to exceed Euler's bound:
    `C(5, 2) = 10 > 9 = 3·5 − 6`. -/
theorem K5_exceeds_bound : planarBound 5 < completeEdges 5 := by decide

end Erdos1018OQ04Incomplete01OQ01
