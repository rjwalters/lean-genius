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

Two further results quantify and generalize the obstruction:

* `excess_eq` — for `n ≥ 3`, `C(n, 2) = (3n − 6) + C(n − 3, 2)`: the overshoot of
  the planar bound is *itself* a complete-graph edge count `(n − 3)(n − 4)/2`,
  sharpening the `Kn_exceeds_planar_bound` inequality to an exact identity.
* `completeEdges_superlinear` — for every `C` there is `N` with `C(n, 2) > C·n` for
  `n ≥ N`: `Kₙ` eventually beats *any* linear edge bound, so the obstruction does
  not depend on Euler's specific `3n − 6` coefficient (the discrete companion of the
  parent's real-analytic `dense_graph_not_planar`).

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

/-! ### The exact excess over Euler's bound, and superlinearity

The threshold results above answer *when* `Kₙ` overshoots Euler's planar bound.
Here we quantify *by how much*, and show the overshoot grows without limit relative
to *any* linear bound — not merely the specific `3n − 6`.

The key identity is exact and division-free:
`completeEdges n = planarBound n + completeEdges (n − 3)` for `n ≥ 3`, i.e. the
excess `C(n,2) − (3n − 6)` is itself a smaller complete-graph edge count,
`C(n − 3, 2) = (n − 3)(n − 4)/2`.  It re-proves the threshold (`excess > 0 ⇔
n − 3 ≥ 2 ⇔ n ≥ 5`) and makes precise that the obstruction deepens quadratically. -/

/-- `2·C(n, 2) = n(n − 1)` — the standard closed form for the complete-graph edge
    count, cleared of division (proved by induction via `completeEdges_succ`). -/
lemma two_mul_completeEdges (n : ℕ) : 2 * completeEdges n = n * (n - 1) := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [completeEdges_succ, Nat.mul_add, ih]
    cases n with
    | zero => decide
    | succ m => simp only [Nat.succ_sub_one]; ring

/-- **Exact excess over Euler's bound.**  For `n ≥ 3`,
    `C(n, 2) = (3n − 6) + C(n − 3, 2)`: the amount by which `Kₙ` overshoots the
    planar edge bound is itself the edge count of the complete graph on `n − 3`
    vertices, i.e. `(n − 3)(n − 4)/2`.  In particular the overshoot is `0` for
    `n ∈ {3, 4}` (where `n − 3 ∈ {0, 1}` and `C(·, 2) = 0`) and strictly positive,
    growing quadratically, for `n ≥ 5`.  A sharpening of `Kn_exceeds_planar_bound`
    from an inequality to an exact identity. -/
theorem excess_eq (n : ℕ) (hn : 3 ≤ n) :
    completeEdges n = planarBound n + completeEdges (n - 3) := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [completeEdges_succ, ih]
    have h1 : n + 1 - 3 = (n - 3) + 1 := by omega
    rw [h1, completeEdges_succ]
    simp only [planarBound]
    omega

/-- **The complete-graph edge count is superlinear.**  For every constant `C` there
    is an `N` beyond which `C(n, 2) > C · n`.  So `Kₙ` eventually exceeds *any*
    linear edge bound `C · n`, not just Euler's `3n − 6`: the counting obstruction
    behind Erdős #1018 OQ-04 is robust to the exact linear coefficient.  Concretely
    `N = 2C + 2` works, since `2·C(n,2) = n(n−1) ≥ n(2C+1) > 2Cn` once `n ≥ 2C + 2`.
    This is the discrete companion of the real-analytic `dense_graph_not_planar`
    (`n^{1+ε} > 3n` eventually) in the parent file. -/
theorem completeEdges_superlinear (C : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → C * n < completeEdges n := by
  refine ⟨2 * C + 2, fun n hn => ?_⟩
  have h2 : 2 * completeEdges n = n * (n - 1) := two_mul_completeEdges n
  have hn1 : 2 * C + 1 ≤ n - 1 := by omega
  have hmul : n * (2 * C + 1) ≤ n * (n - 1) := Nat.mul_le_mul (le_refl n) hn1
  have he : n * (2 * C + 1) = 2 * (C * n) + n := by ring
  omega

end Erdos1018OQ04Incomplete01OQ01
