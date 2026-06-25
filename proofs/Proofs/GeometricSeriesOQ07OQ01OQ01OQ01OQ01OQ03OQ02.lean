import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ01

/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-01-oq-03-oq-02:
# The fourth column of the Eulerian triangle, ⟨n,3⟩

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01-oq-01` established the
explicit closed forms for the first three columns of the Eulerian triangle:

* `eulerian_col_zero` : `⟨n,0⟩ = 1`
* `eulerian_col_one`  : `⟨n,1⟩ = 2ⁿ − n − 1`                      (OEIS A000295)
* `eulerian_col_two`  : `2·⟨n,2⟩ = 2·3ⁿ − (n+1)·2ⁿ⁺¹ + n·(n+1)`  (OEIS A000460)

and left the next column as an explicit follow-up. This entry settles it:

* `eulerian_col_three` :
    `6·⟨n,3⟩ = 6·4ⁿ − 6·(n+1)·3ⁿ + 3·n·(n+1)·2ⁿ − (n−1)·n·(n+1)`   (OEIS A000498)

equivalently `⟨n,3⟩ = 4ⁿ − (n+1)·3ⁿ + C(n+1,2)·2ⁿ − C(n+1,3)`, the third
nontrivial case of the inclusion–exclusion formula
`⟨n,k⟩ = ∑_{i=0}^{k} (−1)ⁱ·C(n+1,i)·(k+1−i)ⁿ`. It is stated cleared of its `/6`
so the identity stays over `ℤ` with no division.

For example the rows `1,4,1`, `1,11,11,1`, `1,26,66,26,1` give `⟨3,3⟩ = 0`,
`⟨4,3⟩ = 1`, `⟨5,3⟩ = 26`; and indeed
`6·0 = 6·64 − 6·4·27 + 3·3·4·8 − 2·3·4 = 0`,
`6·1 = 6·256 − 6·5·81 + 3·4·5·16 − 3·4·5 = 6`,
`6·26 = 6·1024 − 6·6·243 + 3·5·6·32 − 4·5·6 = 156`.

## Method

Induction on `n` driven by the single-step Eulerian recurrence
`⟨n+1,3⟩ = 4·⟨n,3⟩ + (n−2)·⟨n,2⟩` (definitional, `rfl`). The previous column is
fed in through the parent's `eulerian_col_two`. The only care needed is the
truncated subtraction `(n − 2 : ℕ)`: for `n ∈ {0,1}` it collapses to `0`, but
there `⟨n,2⟩ = 0` as well (`2·⟨0,2⟩ = 2·⟨1,2⟩ = 0` from the column-two formula),
so the contribution vanishes either way and the integer identity goes through;
for `n ≥ 2` the cast `((n − 2 : ℕ) : ℤ) = (n : ℤ) − 2` is honest. This mirrors the
parent's handling of `(n − 1)` in `eulerian_col_two`, one column deeper.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ03OQ02

open Nat Finset GeometricSeriesOQ07OQ01OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01OQ01

/-- **Fourth column of the Eulerian triangle.**
`6·⟨n,3⟩ = 6·4ⁿ − 6·(n+1)·3ⁿ + 3·n·(n+1)·2ⁿ − (n−1)·n·(n+1)`
(equivalently `⟨n,3⟩ = 4ⁿ − (n+1)·3ⁿ + C(n+1,2)·2ⁿ − C(n+1,3)`, OEIS A000498),
stated over `ℤ` cleared of its `/6`. -/
theorem eulerian_col_three (n : ℕ) :
    6 * (eulerian n 3 : ℤ)
      = 6 * 4 ^ n - 6 * (n + 1) * 3 ^ n + 3 * n * (n + 1) * 2 ^ n
        - ((n : ℤ) - 1) * n * (n + 1) := by
  induction n with
  | zero => norm_num [eulerian]
  | succ n ih =>
    -- Eulerian recurrence for column 3: `⟨n+1,3⟩ = 4·⟨n,3⟩ + (n−2)·⟨n,2⟩`.
    have hrec : (6 * (eulerian (n + 1) 3 : ℤ))
        = 4 * (6 * (eulerian n 3 : ℤ))
          + 3 * ((n - 2 : ℕ) : ℤ) * (2 * (eulerian n 2 : ℤ)) := by
      rw [show eulerian (n + 1) 3 = 4 * eulerian n 3 + (n - 2) * eulerian n 2 from rfl]
      push_cast; ring
    -- Reconcile the truncated `(n − 2 : ℕ)` with `(n − 2 : ℤ)`: harmless because
    -- `⟨0,2⟩ = ⟨1,2⟩ = 0`, so feeding the column-two formula is exact.
    have key : 3 * ((n - 2 : ℕ) : ℤ) * (2 * (eulerian n 2 : ℤ))
        = 3 * ((n : ℤ) - 2) * (2 * 3 ^ n - (n + 1) * 2 ^ (n + 1) + n * (n + 1)) := by
      rw [eulerian_col_two n]
      rcases n with _ | _ | m
      · norm_num
      · norm_num
      · have hsub : ((m + 1 + 1 - 2 : ℕ) : ℤ) = (m : ℤ) := by
          simp
        rw [hsub]; push_cast; ring
    rw [hrec, ih, key]; push_cast [pow_succ]; ring

end GeometricSeriesOQ07OQ01OQ01OQ01OQ01OQ03OQ02
