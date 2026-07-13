/-
# Erdős Problem #1018, OQ-04 → incomplete-01 → OQ-02
## Sharp edge-count threshold for the *bipartite* planar obstruction (K₃,₃)

The sibling file `Erdos1018OQ04Incomplete01OQ01.lean` pins the counting threshold
for the general planar obstruction: `Kₙ` overshoots Euler's bound `3n − 6`
exactly for `n ≥ 5`, with the exact excess `C(n, 2) − (3n − 6) = C(n − 3, 2)`.
That is the `K₅` half of Kuratowski's characterisation.

This file supplies the **`K₃,₃` half**.  A simple *bipartite* (equivalently
triangle-free) planar graph on `V ≥ 3` vertices has at most `2V − 4` edges — the
girth-4 refinement of Euler's `3V − 6`.  The complete bipartite graph `K_{m,n}`
has `m · n` edges on `m + n` vertices, so the elementary question mirroring the
`Kₙ` one is:

> For which `m, n` does the edge count of `K_{m,n}` *by itself* force
> non-planarity — i.e. when is `m · n > 2(m + n) − 4`?

The answer is perfectly parallel to the `Kₙ` story, and just as sharp:

* `bipartite_excess_eq` — for `m, n ≥ 2`, `m · n = (2(m + n) − 4) + (m − 2)(n − 2)`:
  the overshoot of the bipartite planar bound is exactly `(m − 2)(n − 2)`, itself
  the edge count of the complete bipartite graph `K_{m−2, n−2}` — the bipartite
  analogue of `excess_eq`'s `C(n − 3, 2)`.
* `Kmn_exceeds_bipartite_bound` — for `m, n ≥ 3`, `2(m + n) − 4 < m · n`.
* `K2n_meets_bipartite_bound` — for `n ≥ 2`, `K_{2,n}` sits *exactly* on the bound
  (`2n = 2(2 + n) − 4`): the boundary planar family, analogue of `K₃`, `K₄`.
* `bipartite_obstruction_threshold` — for `m, n ≥ 2`,
  `2(m + n) − 4 < m · n ↔ (3 ≤ m ∧ 3 ≤ n)`: the counting obstruction switches on
  exactly when *both* sides reach `3`, so `K₃,₃` (9 edges, bound 8) is the smallest
  complete bipartite graph the edge count alone rules out — matching the classical
  fact that `K₃,₃` is the minimal non-planar complete bipartite graph.
* `K33_exceeds_bound` / `K23_meets_bound` — the numeric corner cases `9 > 8` and
  `6 = 6`.

Everything is fully elementary (the excess factors as `(m − 2)(n − 2)`, so the
threshold is just positivity of a product) and self-contained: only `import
Mathlib`.  **0 axioms, 0 sorries.**

## References

- Euler / girth-4 planar bound `e ≤ 2v − 4` for bipartite planar graphs.
- Kuratowski, K. (1930). "Sur le problème des courbes gauches en topologie."
- Sibling: `Erdos1018OQ04Incomplete01OQ01.lean` (the `Kₙ` / `3n − 6` threshold).
-/
import Mathlib

namespace Erdos1018OQ04Incomplete01OQ02

/-- The edge count of the complete bipartite graph `K_{m,n}`: `m · n`. -/
def completeBipartiteEdges (m n : ℕ) : ℕ := m * n

/-- The bipartite (girth-4) planar edge bound on `m + n` vertices: `2(m + n) − 4`.
    A simple bipartite planar graph on `V ≥ 3` vertices has at most `2V − 4` edges. -/
def bipartitePlanarBound (m n : ℕ) : ℕ := 2 * (m + n) - 4

/-- **Exact excess over the bipartite planar bound.**  For `m, n ≥ 2`,
    `m · n = (2(m + n) − 4) + (m − 2)(n − 2)`: the amount by which `K_{m,n}`
    overshoots the bipartite planar bound is itself the edge count of the complete
    bipartite graph `K_{m−2, n−2}`.  The bipartite analogue of the sibling file's
    `excess_eq` (`C(n, 2) = (3n − 6) + C(n − 3, 2)`).  In particular the overshoot
    is `0` exactly when `m = 2` or `n = 2`, and positive precisely when both
    `m, n ≥ 3`. -/
theorem bipartite_excess_eq (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    completeBipartiteEdges m n
      = bipartitePlanarBound m n + completeBipartiteEdges (m - 2) (n - 2) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp only [completeBipartiteEdges, bipartitePlanarBound]
  -- `m = 2 + a`, `n = 2 + b`; both sides expand to `a·b + 2a + 2b + 4`.
  have e1 : 2 + a - 2 = a := by omega
  have e2 : 2 + b - 2 = b := by omega
  rw [e1, e2]
  have h8 : 2 * ((2 + a) + (2 + b)) = (2 * a + 2 * b + 4) + 4 := by ring
  rw [h8, Nat.add_sub_cancel]
  ring

/-- **`K_{m,n}` exceeds the bipartite planar bound for `m, n ≥ 3`.**  Immediate from
    `bipartite_excess_eq`: the excess `(m − 2)(n − 2)` is at least `1` once both
    `m, n ≥ 3`. -/
theorem Kmn_exceeds_bipartite_bound (m n : ℕ) (hm : 3 ≤ m) (hn : 3 ≤ n) :
    bipartitePlanarBound m n < completeBipartiteEdges m n := by
  have hexc := bipartite_excess_eq m n (by omega) (by omega)
  have hpos : 0 < completeBipartiteEdges (m - 2) (n - 2) := by
    simp only [completeBipartiteEdges]
    have : 0 < (m - 2) * (n - 2) := Nat.mul_pos (by omega) (by omega)
    exact this
  omega

/-- **`K_{2,n}` sits exactly on the bipartite planar bound.**  For `n ≥ 2`,
    `completeBipartiteEdges 2 n = bipartitePlanarBound 2 n` (`2n = 2(2 + n) − 4`):
    the complete bipartite graphs with a side of size `2` are the boundary planar
    family, the bipartite analogue of `K₃`, `K₄` meeting Euler's bound. -/
theorem K2n_meets_bipartite_bound (n : ℕ) (hn : 2 ≤ n) :
    completeBipartiteEdges 2 n = bipartitePlanarBound 2 n := by
  simp only [completeBipartiteEdges, bipartitePlanarBound]
  omega

/-- **Sharp threshold for the bipartite counting obstruction.**  For `m, n ≥ 2`,
    the edge count of `K_{m,n}` exceeds the bipartite planar bound **iff** both
    sides reach `3`: `2(m + n) − 4 < m · n ↔ (3 ≤ m ∧ 3 ≤ n)`.  Via
    `bipartite_excess_eq` the strict inequality is equivalent to
    `0 < (m − 2)(n − 2)`, i.e. positivity of both factors.  So `K₃,₃` is the
    smallest complete bipartite graph the edge count alone rules out. -/
theorem bipartite_obstruction_threshold (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    bipartitePlanarBound m n < completeBipartiteEdges m n ↔ (3 ≤ m ∧ 3 ≤ n) := by
  have hexc := bipartite_excess_eq m n hm hn
  simp only [completeBipartiteEdges] at hexc ⊢
  constructor
  · intro h
    -- `bound < mn = bound + (m-2)(n-2)` forces `(m-2)(n-2) > 0`, so both factors > 0.
    have hpos : 0 < (m - 2) * (n - 2) := by omega
    have hm2 : 0 < m - 2 := by
      rcases Nat.eq_zero_or_pos (m - 2) with h0 | h0
      · rw [h0, Nat.zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    have hn2 : 0 < n - 2 := by
      rcases Nat.eq_zero_or_pos (n - 2) with h0 | h0
      · rw [h0, Nat.mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩
    have hpos : 0 < (m - 2) * (n - 2) := Nat.mul_pos (by omega) (by omega)
    omega

/-- `K₃,₃` exceeds the bipartite planar bound: `9 > 8`. -/
theorem K33_exceeds_bound :
    bipartitePlanarBound 3 3 < completeBipartiteEdges 3 3 := by decide

/-- `K₂,₃` meets the bipartite planar bound exactly: `6 = 6`. -/
theorem K23_meets_bound :
    completeBipartiteEdges 2 3 = bipartitePlanarBound 2 3 := by decide

end Erdos1018OQ04Incomplete01OQ02
