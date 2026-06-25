/-
# Necklace Divisor Sum: ∑_{d ∣ n} φ(n/d)·k^d = (#necklaces) · n
## (burnside-counting-oq-03-oq-02-oq-01-oq-02)

**Open question** (from `burnside-counting-oq-03-oq-02-oq-01`): the parent proves the
cyclic Burnside count in *rotation-indexed* integer form
`∑_{r : ZMod n} k^{gcd(n, r)} = (#necklaces up to rotation) · n`. Push this to the
classical **divisor form** `∑_{d ∣ n} φ(n/d) · k^d` by grouping the `n` rotations
according to their cycle count.

The bridge is a pure number-theoretic reindexing of the rotation sum, independent of the
necklace interpretation:

* **(A) Rotation sum = range sum** (`sum_zmod_eq_sum_range`):
    `∑_{r : ZMod n} k^{gcd(n, r.val)} = ∑_{i < n} k^{gcd(n, i)}`,
  via the bijection `r ↦ r.val` between `ZMod n` and `{0, …, n-1}`.

* **(B) Range sum = divisor sum** (`sum_range_pow_gcd_eq_divisor_sum`):
    `∑_{i < n} k^{gcd(n, i)} = ∑_{d ∣ n} φ(n/d) · k^d`.
  Group the integers `i < n` by the value `gcd(n, i)`, which always divides `n`. The fibre
  `{i < n : gcd(n, i) = d}` has exactly `φ(n/d)` elements (Mathlib's `totient_div_of_dvd`),
  and on it the summand is the constant `k^d`. Fiberwise summation (`sum_fiberwise_of_maps_to'`)
  assembles the divisor sum.

* **(C) Classical necklace count** (`divisor_sum_eq_card_necklaces_mul`):
    `∑_{d ∣ n} φ(n/d) · k^d = (#necklaces up to rotation) · n`,
  immediate from `(A)`, `(B)` and the parent's `sum_pow_gcd_eq_card_necklaces_mul`. Dividing by
  `n` recovers the textbook cyclic-necklace formula `(1/n) ∑_{d ∣ n} φ(n/d) k^d`.

* **(D) Symmetric form** (`divisor_sum_symm`):
    `∑_{d ∣ n} φ(d) · k^{n/d} = ∑_{d ∣ n} φ(n/d) · k^d`,
  the usual `d ↔ n/d` reindexing, so the count is equally `(1/n) ∑_{d ∣ n} φ(d) k^{n/d}`.

This closes the gap between the parent's `gcd`-indexed sum and the divisor-sum form quoted in
every reference statement of the cyclic necklace-counting theorem.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

import Mathlib
import Proofs.BurnsideCountingOQ03OQ02OQ01

open MulAction BigOperators Finset

namespace BurnsideCountingOQ03OQ02OQ01OQ02

open BurnsideCountingOQ03OQ02OQ01 (Rot rotation sum_pow_gcd_eq_card_necklaces_mul)

variable {n : ℕ} [NeZero n]

/-! ## (A) The rotation sum equals the sum over `{0, …, n-1}`

`r ↦ r.val` is a bijection `ZMod n ≃ {0, …, n-1}`, so summing `k^{gcd(n, r.val)}` over all
rotations is the same as summing `k^{gcd(n, i)}` over `i < n`. -/

/-- **(A)** Reindex the rotation sum along the bijection `r ↦ r.val`. -/
theorem sum_zmod_eq_sum_range (k : ℕ) :
    (∑ r : ZMod n, k ^ Nat.gcd n r.val) = ∑ i ∈ Finset.range n, k ^ Nat.gcd n i := by
  refine Finset.sum_bij' (fun r _ => r.val) (fun i _ => (i : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro r _; exact Finset.mem_range.2 (ZMod.val_lt r)
  · intro i _; exact Finset.mem_univ _
  · intro r _; exact ZMod.natCast_zmod_val r
  · intro i hi; exact ZMod.val_natCast_of_lt (Finset.mem_range.1 hi)
  · intro r _; rfl

/-! ## (B) The range sum equals the divisor sum

Grouping `i < n` by `d = gcd(n, i)` (which always divides `n`) and using that the fibre over
`d` has `φ(n/d)` elements turns `∑_{i < n} k^{gcd(n,i)}` into `∑_{d ∣ n} φ(n/d) · k^d`. -/

/-- **(B)** The classical divisor form of the cyclic Burnside sum. -/
theorem sum_range_pow_gcd_eq_divisor_sum (k : ℕ) :
    (∑ i ∈ Finset.range n, k ^ Nat.gcd n i)
      = ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  -- Fiberwise over `g i = gcd(n, i)`, which maps `range n` into `n.divisors`.
  rw [← Finset.sum_fiberwise_of_maps_to' (s := Finset.range n) (t := n.divisors)
        (g := fun i => Nat.gcd n i)
        (fun i _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n i, NeZero.ne n⟩)
        (fun d => k ^ d)]
  -- On each fibre the summand `k^d` is constant; the fibre has `φ(n/d)` elements.
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.sum_const, smul_eq_mul, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-! ## (C) The classical cyclic necklace-counting identity -/

/-- **(C)** The number of `k`-colored `n`-bead necklaces (up to rotation), times `n`, equals the
divisor sum `∑_{d ∣ n} φ(n/d) · k^d`. Dividing by `n` gives the textbook necklace formula. -/
theorem divisor_sum_eq_card_necklaces_mul (k : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d)
      = Nat.card (orbitRel.Quotient (Rot n) (Rot n → Fin k)) * n := by
  rw [← sum_range_pow_gcd_eq_divisor_sum, ← sum_zmod_eq_sum_range,
    sum_pow_gcd_eq_card_necklaces_mul]

/-! ## (D) The symmetric `d ↔ n/d` form -/

/-- **(D)** Reindexing `d ↔ n/d` gives the equivalent textbook form `∑_{d ∣ n} φ(d) · k^{n/d}`. -/
theorem divisor_sum_symm (k : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient d * k ^ (n / d))
      = ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  rw [← Nat.sum_div_divisors n (fun d => Nat.totient (n / d) * k ^ d)]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) (NeZero.ne n)]

/-- **(D′)** The necklace count in the symmetric divisor form. -/
theorem symm_divisor_sum_eq_card_necklaces_mul (k : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient d * k ^ (n / d))
      = Nat.card (orbitRel.Quotient (Rot n) (Rot n → Fin k)) * n := by
  rw [divisor_sum_symm, divisor_sum_eq_card_necklaces_mul]

#check @sum_zmod_eq_sum_range
#check @sum_range_pow_gcd_eq_divisor_sum
#check @divisor_sum_eq_card_necklaces_mul
#check @divisor_sum_symm
#check @symm_divisor_sum_eq_card_necklaces_mul

end BurnsideCountingOQ03OQ02OQ01OQ02
