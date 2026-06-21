/-
# Four-Square Distribution, OQ-05: 2-adic structure of the symmetry multiplier

The parent file `FourSquareDistribution.lean` decomposes the count r₄(n) of
four-square representations of n by *type* (the sorted 4-tuple of absolute
values a₁ ≤ a₂ ≤ a₃ ≤ a₄ with a₁²+a₂²+a₃²+a₄² = n), assigning each type a
symmetry multiplier

    contribution(t) = permutations(t) · signFactor(t),
    signFactor(t)   = 2 ^ (number of nonzero entries),

and proves the *bounds* `contribution t ≤ 384 = |B₄|`, `permutations t ≤ 24`,
`signFactor t ≤ 16`. It does not record any *divisibility* property of the
multiplier.

This file supplies the 2-adic (sign-change) structure: the sign-symmetry
subgroup of order `2^(nonzeroCount)` always divides the contribution. This is
the "factor of 2^k" half of the hyperoctahedral symmetry B₄ = (ℤ/2)⁴ ⋊ S₄ that
underlies Jacobi's factor of 8, isolated at the level of a single type:

    2 ^ (nonzeroCount t)  ∣  contribution t,

so in particular `8 ∣ contribution t` once a type has ≥ 3 nonzero entries, and
`16 ∣ contribution t` when all four entries are nonzero.

## Main results

- `signFactor_dvd_contribution`            : signFactor t ∣ contribution t
- `two_pow_nonzeroCount_dvd_contribution`  : 2^(nonzeroCount t) ∣ contribution t
- `two_pow_dvd_contribution_of_le`         : k ≤ nonzeroCount t → 2^k ∣ contribution t
- `two_dvd_contribution_of_pos`            : 1 ≤ nonzeroCount t → 2  ∣ contribution t
- `four_dvd_contribution_of_two_le`        : 2 ≤ nonzeroCount t → 4  ∣ contribution t
- `eight_dvd_contribution_of_three_le`     : 3 ≤ nonzeroCount t → 8  ∣ contribution t
- `sixteen_dvd_contribution_of_four`       : nonzeroCount t = 4 → 16 ∣ contribution t

All results are fully machine-checked: 0 sorries, 0 `axiom` declarations.

## Honest scope

The full statement `8 ∣ contribution t` for *every* type with ≥ 1 nonzero entry
(which would give Jacobi's `8 ∣ r₄(n)` for n ≥ 1) additionally needs the parity
of the *permutation* part in the one- and two-nonzero cases, and is NOT proved
here. This file establishes only the sign-part `2^k` divisibility, which is
exact for k ≤ nonzeroCount.

## References

- Jacobi (1834), four-square formula r₄(n) = 8·σ*(n)
- Parent gallery entry four-square-distribution (type decomposition, bounds)
-/

import Proofs.FourSquareDistribution
import Mathlib.Tactic

namespace FourSquareDistribution

variable {n : ℕ}

/-- The sign factor is at least `1`. -/
theorem one_le_signFactor (t : RepType n) : 1 ≤ t.signFactor := by
  unfold RepType.signFactor
  exact Nat.one_le_two_pow

/-- The sign factor is a divisor of the contribution (it is one of its factors). -/
theorem signFactor_dvd_contribution (t : RepType n) :
    t.signFactor ∣ t.contribution :=
  ⟨t.permutations, by unfold RepType.contribution; ring⟩

/-- **Sign-part divisibility.** `2^(nonzeroCount)` divides the contribution —
    the order of the sign-change subgroup `(ℤ/2)^(nonzeroCount)` of `B₄`. -/
theorem two_pow_nonzeroCount_dvd_contribution (t : RepType n) :
    2 ^ t.nonzeroCount ∣ t.contribution := by
  have h := signFactor_dvd_contribution t
  unfold RepType.signFactor at h
  exact h

/-- For any `k ≤ nonzeroCount`, `2^k` divides the contribution. -/
theorem two_pow_dvd_contribution_of_le (t : RepType n) {k : ℕ}
    (hk : k ≤ t.nonzeroCount) : 2 ^ k ∣ t.contribution :=
  (pow_dvd_pow 2 hk).trans (two_pow_nonzeroCount_dvd_contribution t)

/-- A type with at least one nonzero entry contributes an even number. -/
theorem two_dvd_contribution_of_pos (t : RepType n) (h : 1 ≤ t.nonzeroCount) :
    2 ∣ t.contribution := by
  have := two_pow_dvd_contribution_of_le t h
  simpa using this

/-- A type with at least two nonzero entries contributes a multiple of 4. -/
theorem four_dvd_contribution_of_two_le (t : RepType n) (h : 2 ≤ t.nonzeroCount) :
    4 ∣ t.contribution := by
  have := two_pow_dvd_contribution_of_le t h
  simpa using this

/-- **The "factor of 8" at the type level.** A type with at least 3 nonzero
    entries contributes a multiple of 8 (from its sign-change symmetry alone). -/
theorem eight_dvd_contribution_of_three_le (t : RepType n)
    (h : 3 ≤ t.nonzeroCount) : 8 ∣ t.contribution := by
  have := two_pow_dvd_contribution_of_le t h
  simpa using this

/-- A type with all four entries nonzero contributes a multiple of 16. -/
theorem sixteen_dvd_contribution_of_four (t : RepType n)
    (h : t.nonzeroCount = 4) : 16 ∣ t.contribution := by
  have := two_pow_dvd_contribution_of_le t (le_of_eq h.symm)
  simpa using this

end FourSquareDistribution
