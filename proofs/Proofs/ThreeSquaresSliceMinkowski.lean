/-
  The 2D-slice Minkowski bound for the three-squares Dirichlet construction.

  This file isolates the single remaining open step of `dirichlet_key_lemma`
  in `Proofs/ThreeSquares.lean`. Session researcher-11 (2026-06-16, recorded in
  `G2-minkowski-2p-gap.md`) pinned down that the 3D index-p² ellipsoid route
  CANNOT supply the required `Q < 2p` bound — the generic 2ⁿ Minkowski bound on
  the covolume-p² sublattice only gives `Q ≲ p^(4/3)`, too weak by a factor
  `~p^(1/3)`. The attainable route restricts to the slice `z = 0`, dropping to
  the index-p sublattice `{(x,y) ∈ ℤ² : x ≡ r·y (mod p)}` with the BINARY form
  `x² + d·y²`. Its 2D Hermite bound gives a nonzero point with
  `x² + d·y² ≤ (2/√3)·√d·p`, which is `< 2p` exactly when `d ≤ 2` — and the file's
  own case split uses only `d ∈ {1, 2}`.

  Two pieces:
  - `exists_slice_point_lt_two_mul` (OPEN, Aristotle target): the pure 2D
    geometry-of-numbers existence. True for every `p > 0` and `d ∈ {1, 2}`.
    Disk `x² + d·y² ≤ R` has area `πR/√d`; Minkowski on the covolume-p
    sublattice needs `πR/√d > 4p` and `R < 2p`, simultaneously solvable iff
    `√d < π/2`, i.e. `d ≤ 2`.
  - `slice_point_to_dirichlet_vector` (PROVED): pure plumbing that lifts a 2D
    slice point `(x, y)` to the `Fin 3 → ℤ` vector `![x, y, 0]`, landing in the
    Dirichlet sublattice `{p ∣ (v0 − r·v1) ∧ p ∣ v2}` with form value `< 2p`.
    This is exactly the input shape consumed by `dirichletForm_dvd_of_in_sublattice`
    and `dirichletForm_eq_p_of_lt_two_mul` in `ThreeSquares.lean`.

  NOTE: build-pending and intentionally UNregistered in `Proofs.lean` — it
  carries one `sorry` (the Aristotle target) and must not gate the deployer build.
-/
import Mathlib

namespace ThreeSquaresSlice

/-- **The missing `Q < 2p` step (2D slice).**

For `d ∈ {1, 2}` and any `p > 0`, the index-`p` sublattice
`{(x, y) ∈ ℤ² : x ≡ r·y (mod p)}` of `ℤ²` contains a nonzero vector on which the
binary form `x² + d·y²` is strictly below `2p`.

This is the sole remaining open input to `dirichlet_key_lemma` in
`Proofs/ThreeSquares.lean`. Combined with the sublattice divisibility
`p ∣ x² + d·y²` (from `r² + d ≡ 0 (mod p)`) and strict positivity, it forces the
form value to equal `p` exactly, discharging the Dirichlet Key Lemma.

Hermite/Minkowski bound: the minimum of `x² + d·y²` over the covolume-`p`
sublattice is `≤ (2/√3)·√d·p`, which is `< 2p` for `d ∈ {1, 2}`. -/
theorem exists_slice_point_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ x y : ℤ, (x, y) ≠ (0, 0) ∧ (p : ℤ) ∣ (x - r * y) ∧
      x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p := by
  sorry

/-- **Bridge (proved): 2D slice point → Dirichlet sublattice vector.**

Lifts a 2D slice point `(x, y)` with `p ∣ (x − r·y)` and `x² + d·y² < 2p` to the
`Fin 3 → ℤ` vector `![x, y, 0]`. The third coordinate `0` makes the second
sublattice condition `p ∣ v 2` automatic, and the ternary form
`v 0² + d·v 1² + d·v 2²` collapses to the binary `x² + d·y²`. This is exactly the
input shape of `dirichletForm_dvd_of_in_sublattice` and
`dirichletForm_eq_p_of_lt_two_mul` (`ThreeSquares.lean`).

No geometry of numbers here — pure plumbing, so it is fully proved. -/
theorem slice_point_to_dirichlet_vector
    (p d : ℕ) (r x y : ℤ)
    (hxy : (x, y) ≠ (0, 0))
    (hdvd : (p : ℤ) ∣ (x - r * y))
    (hlt : x ^ 2 + (d : ℤ) * y ^ 2 < 2 * p) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      ((p : ℤ) ∣ (v 0 - r * v 1) ∧ (p : ℤ) ∣ v 2) ∧
      v 0 ^ 2 + (d : ℤ) * v 1 ^ 2 + (d : ℤ) * v 2 ^ 2 < 2 * p := by
  refine ⟨![x, y, 0], ?_, ⟨?_, ?_⟩, ?_⟩
  · -- ![x, y, 0] ≠ 0 since (x, y) ≠ (0, 0)
    intro h
    apply hxy
    have hx : x = 0 := by have := congrFun h 0; simpa using this
    have hy : y = 0 := by have := congrFun h 1; simpa using this
    simp [hx, hy]
  · simpa using hdvd
  · simp
  · simpa using hlt

/-- **Assembled existence**: composing the (open) 2D Minkowski bound with the
(proved) bridge gives directly the `Fin 3 → ℤ` lattice point that
`dirichlet_key_lemma` consumes. Once `exists_slice_point_lt_two_mul` is closed,
this is sorry-free. -/
theorem exists_dirichlet_vector_lt_two_mul
    (p d : ℕ) (hp : 0 < p) (hd : 0 < d) (hd2 : d ≤ 2) (r : ℤ) :
    ∃ v : Fin 3 → ℤ, v ≠ 0 ∧
      ((p : ℤ) ∣ (v 0 - r * v 1) ∧ (p : ℤ) ∣ v 2) ∧
      v 0 ^ 2 + (d : ℤ) * v 1 ^ 2 + (d : ℤ) * v 2 ^ 2 < 2 * p := by
  obtain ⟨x, y, hxy, hdvd, hlt⟩ := exists_slice_point_lt_two_mul p d hp hd hd2 r
  exact slice_point_to_dirichlet_vector p d r x y hxy hdvd hlt

end ThreeSquaresSlice
