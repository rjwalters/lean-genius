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

### The full type-level factor of 8 (this revision)

The previous revision proved only the *sign-part* `2^k` divisibility, leaving the
parity of the *permutation* part in the one- and two-nonzero cases as the open
step. That step is now closed:

- `zero_pattern_one` / `zero_pattern_two` : sortedness pins the zero pattern
  (`(0,0,0,a₄)` resp. `(0,0,a₃,a₄)`) once the nonzero count is `1` resp. `2`.
- `permutations_one_nonzero`              : a one-nonzero type has exactly `4`
  permutations, so its contribution is `4·2 = 8`.
- `two_dvd_permutations_two_nonzero`      : a two-nonzero type has an *even*
  permutation count (`6` or `12`), so its contribution `perm·4` is a multiple of `8`.
- `eight_dvd_contribution_of_pos`         : **1 ≤ nonzeroCount t → 8 ∣ contribution t.**

This is the per-type divisibility behind Jacobi's `8 ∣ r₄(n)` for `n ≥ 1`: combined
with the additive decomposition `r₄(n) = Σ_types contribution t` (parent file), every
summand is a multiple of `8`, hence so is the total.

All results are fully machine-checked: 0 sorries, 0 `axiom` declarations.

## Honest scope

`eight_dvd_contribution_of_pos` settles the per-type factor of `8`. Deriving the
global `8 ∣ r₄(n)` from it additionally requires the parent's decomposition
`r₄(n) = Σ contribution t` over the (finite) set of types — that summation lemma
lives upstream and is not re-proved here; this file supplies the per-summand
divisibility that the decomposition needs.

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

/-! ### The full type-level factor of 8

The sign part above gives `8 ∣ contribution` only for `nonzeroCount ≥ 3`. To reach
`8 ∣ contribution` for *every* nonzero type we must also control the *permutation*
part when `nonzeroCount ∈ {1, 2}`. Sortedness pins the zero pattern, and the
multinomial permutation count is then computed explicitly. -/

/-- A sorted type with exactly one nonzero entry has shape `(0,0,0,a₄)`, `a₄ ≠ 0`. -/
theorem zero_pattern_one (t : RepType n) (h : t.nonzeroCount = 1) :
    t.a₁ = 0 ∧ t.a₂ = 0 ∧ t.a₃ = 0 ∧ t.a₄ ≠ 0 := by
  obtain ⟨s1, s2, s3⟩ := t.sorted
  simp only [RepType.nonzeroCount] at h
  by_cases h1 : t.a₁ = 0 <;> by_cases h2 : t.a₂ = 0 <;>
    by_cases h3 : t.a₃ = 0 <;> by_cases h4 : t.a₄ = 0 <;> simp_all

/-- A sorted type with exactly two nonzero entries has shape `(0,0,a₃,a₄)`, both nonzero. -/
theorem zero_pattern_two (t : RepType n) (h : t.nonzeroCount = 2) :
    t.a₁ = 0 ∧ t.a₂ = 0 ∧ t.a₃ ≠ 0 ∧ t.a₄ ≠ 0 := by
  obtain ⟨s1, s2, s3⟩ := t.sorted
  simp only [RepType.nonzeroCount] at h
  by_cases h1 : t.a₁ = 0 <;> by_cases h2 : t.a₂ = 0 <;>
    by_cases h3 : t.a₃ = 0 <;> by_cases h4 : t.a₄ = 0 <;> simp_all

/-- The one-nonzero type `(0,0,0,a₄)` has exactly `4 = 4!/3!` permutations. -/
theorem permutations_one_nonzero (t : RepType n)
    (h1 : t.a₁ = 0) (h2 : t.a₂ = 0) (h3 : t.a₃ = 0) (h4 : t.a₄ ≠ 0) :
    t.permutations = 4 := by
  have h4' : (0 : ℕ) ≠ t.a₄ := Ne.symm h4
  unfold RepType.permutations
  simp only [h1, h2, h3]
  rw [List.dedup_cons_of_mem (by simp), List.dedup_cons_of_mem (by simp),
      List.dedup_cons_of_notMem (by simp [h4']), List.dedup_cons_of_notMem (by simp),
      List.dedup_nil]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    List.count_cons_self, List.count_cons_of_ne h4', List.count_nil,
    List.count_cons_of_ne h4]
  decide

/-- The two-nonzero type `(0,0,a₃,a₄)` has an *even* permutation count
    (`6 = 4!/(2!·2!)` when `a₃ = a₄`, `12 = 4!/2!` when `a₃ ≠ a₄`). -/
theorem two_dvd_permutations_two_nonzero (t : RepType n)
    (h1 : t.a₁ = 0) (h2 : t.a₂ = 0) (h3 : t.a₃ ≠ 0) (h4 : t.a₄ ≠ 0) :
    2 ∣ t.permutations := by
  have h3' : (0 : ℕ) ≠ t.a₃ := Ne.symm h3
  have h4' : (0 : ℕ) ≠ t.a₄ := Ne.symm h4
  unfold RepType.permutations
  simp only [h1, h2]
  rw [List.dedup_cons_of_mem (by simp), List.dedup_cons_of_notMem (by simp [h3', h4'])]
  by_cases he : t.a₃ = t.a₄
  · -- (0,0,v,v): permutations = 6
    rw [he, List.dedup_cons_of_mem (by simp), List.dedup_cons_of_notMem (by simp),
        List.dedup_nil]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.count_cons_self, List.count_cons_of_ne h4', List.count_cons_of_ne h4,
      List.count_nil]
    decide
  · -- (0,0,u,v): permutations = 12
    have he' : t.a₄ ≠ t.a₃ := Ne.symm he
    rw [List.dedup_cons_of_notMem (by simp [he]), List.dedup_cons_of_notMem (by simp),
        List.dedup_nil]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.count_cons_self, List.count_cons_of_ne h3', List.count_cons_of_ne h4',
      List.count_cons_of_ne h3, List.count_cons_of_ne h4, List.count_cons_of_ne he,
      List.count_cons_of_ne he', List.count_nil]
    decide

/-- **Jacobi's factor of 8, at the type level.** Every representation type with at
    least one nonzero entry contributes a multiple of `8` to `r₄(n)`. For
    `nonzeroCount ≥ 3` this is the sign part alone; the new content is the
    `nonzeroCount ∈ {1, 2}` cases, where the permutation count supplies the
    missing factors of `2`. -/
theorem eight_dvd_contribution_of_pos (t : RepType n) (h : 1 ≤ t.nonzeroCount) :
    8 ∣ t.contribution := by
  have hle : t.nonzeroCount ≤ 4 := nonzeroCount_le_four t
  unfold RepType.contribution RepType.signFactor
  rcases (show t.nonzeroCount = 1 ∨ t.nonzeroCount = 2 ∨ 3 ≤ t.nonzeroCount from by omega)
    with hc | hc | hc
  · -- one nonzero: permutations = 4, signFactor = 2, contribution = 8
    obtain ⟨e1, e2, e3, e4⟩ := zero_pattern_one t hc
    rw [permutations_one_nonzero t e1 e2 e3 e4, hc]; decide
  · -- two nonzero: 2 ∣ permutations, signFactor = 4, contribution = (even)·4
    obtain ⟨e1, e2, e3, e4⟩ := zero_pattern_two t hc
    obtain ⟨m, hm⟩ := two_dvd_permutations_two_nonzero t e1 e2 e3 e4
    rw [hm, hc]; exact ⟨m, by ring⟩
  · -- three or four nonzero: the sign part already gives 8
    have := eight_dvd_contribution_of_three_le t hc
    unfold RepType.contribution RepType.signFactor at this; exact this

end FourSquareDistribution
