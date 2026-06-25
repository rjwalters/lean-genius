/-
# Necklace Divisor-Sum: ∑_{r} k^{gcd(n,r)} = ∑_{d∣n} φ(n/d)·k^d
## (burnside-counting-oq-03-oq-02-oq-01-oq-02)

**Open question** (from `burnside-counting-oq-03-oq-02-oq-01`): the parent proves the
cyclic Burnside count in the *raw rotation-indexed* form
`∑_{r : ZMod n} k ^ gcd(n, r.val) = (#necklaces) · n` — every one of the `n` rotations
contributes `k ^ gcd(n, r)` fixed colorings. Push this to the classical **divisor-sum**
shape by grouping the `n` rotations according to their order.

The order of rotation `r` is `n / gcd(n, r)`, so rotations of order `n/d` are exactly the
`r` with `gcd(n, r) = d`, and there are `φ(n/d)` of them (Euler's totient counts the
generators of the cyclic subgroup of index `d`). Collecting the `n` rotations into these
fibres turns the flat sum into a sum over divisors:

* **(A) Fibre-collapse** (`sum_pow_gcd_eq_divisor_sum`):
    `∑_{r : ZMod n} k ^ gcd(n, r.val) = ∑_{d ∈ n.divisors} φ(n/d) · k ^ d`.
  Reindex `ZMod n` along `ZMod.val` to `range n`, fibre the sum over the divisor-valued
  map `i ↦ gcd(n, i)` (`Finset.sum_fiberwise_of_maps_to`, since `gcd n i ∣ n`), and read off
  each fibre's size as `φ(n/d)` via Mathlib's `Nat.totient_div_of_dvd`.

* **(B) Divisor-form necklace count** (`divisor_sum_eq_card_necklaces_mul`):
    `∑_{d ∈ n.divisors} φ(n/d) · k ^ d = (#necklaces up to rotation) · n`,
  the parent's count (C) rewritten in divisor form by chaining `(A)` with the parent's
  `sum_pow_gcd_eq_card_necklaces_mul`.

* **(C) Textbook form** (`divisor_sum_swap`):
    `∑_{d ∈ n.divisors} φ(n/d) · k ^ d = ∑_{d ∈ n.divisors} φ(d) · k ^ (n/d)`,
  the familiar `(1/n) ∑_{d∣n} φ(d) · k^{n/d}` necklace formula, obtained from the
  divisor involution `d ↦ n/d` (`Nat.sum_div_divisors`).

This converts the parent's per-rotation value `k^{gcd(n,r)}` into the standard closed form
quoted in every combinatorics text for the number of `k`-colored `n`-bead necklaces.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

import Mathlib
import Proofs.BurnsideCountingOQ03OQ02OQ01

open Finset BigOperators

namespace BurnsideCountingOQ03OQ02OQ01OQ02

open BurnsideCountingOQ03OQ02OQ01 (Rot rotation sum_pow_gcd_eq_card_necklaces_mul)

variable {n : ℕ} [NeZero n]

/-! ## Section I: reindex the rotation sum over `range n`

`ZMod.val` is a bijection from `ZMod n` onto `{0, …, n-1} = range n` (for `n ≠ 0`), so the
sum over all `n` rotations is literally the sum over `range n` of `k ^ gcd(n, i)`. -/

/-- The flat sum over `ZMod n` equals the sum over `range n` along `ZMod.val`. -/
lemma sum_zmod_eq_sum_range (k : ℕ) :
    (∑ r : ZMod n, k ^ Nat.gcd n r.val) = ∑ i ∈ range n, k ^ Nat.gcd n i := by
  refine Finset.sum_bij (fun r _ => r.val) ?_ ?_ ?_ ?_
  · -- maps `univ` into `range n`
    intro r _
    exact mem_range.2 (ZMod.val_lt r)
  · -- injective
    intro a _ b _ hab
    exact ZMod.val_injective n hab
  · -- surjective onto `range n`
    intro i hi
    exact ⟨(i : ZMod n), mem_univ _, ZMod.val_cast_of_lt (mem_range.1 hi)⟩
  · -- value agreement
    intro r _
    rfl

/-! ## Section II: (A) fibre-collapse to the divisor sum -/

/-- **(A)** Grouping the `n` rotations by `gcd(n, r)` collapses the flat sum into a divisor
sum, the fibre over `d ∣ n` having size `φ(n/d)`. -/
theorem sum_pow_gcd_eq_divisor_sum (k : ℕ) :
    (∑ r : ZMod n, k ^ Nat.gcd n r.val)
      = ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  rw [sum_zmod_eq_sum_range]
  have hn : n ≠ 0 := NeZero.ne n
  -- fibre `range n` over the divisor-valued map `i ↦ gcd n i`
  have hmaps : ∀ i ∈ range n, Nat.gcd n i ∈ n.divisors := by
    intro i _
    exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left _ _, hn⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => k ^ Nat.gcd n i)]
  -- each fibre is constant `k ^ d` with cardinality `φ(n/d)`
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [Finset.sum_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2]),
      Finset.sum_const, Nat.totient_div_of_dvd hdvd, smul_eq_mul]

/-! ## Section III: (B) divisor-form necklace count -/

/-- **(B)** The classical cyclic necklace count in divisor form:
`∑_{d∣n} φ(n/d) · k^d = (#necklaces up to rotation) · n`. -/
theorem divisor_sum_eq_card_necklaces_mul (k : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d)
      = Nat.card (MulAction.orbitRel.Quotient (Rot n) (Rot n → Fin k)) * n := by
  rw [← sum_pow_gcd_eq_divisor_sum, sum_pow_gcd_eq_card_necklaces_mul]

/-! ## Section IV: (C) textbook `∑ φ(d)·k^{n/d}` form -/

/-- **(C)** The divisor involution `d ↦ n/d` rewrites the sum into the standard textbook
shape `∑_{d∣n} φ(d) · k^{n/d}`, whose `1/n`-average is the usual necklace formula. -/
theorem divisor_sum_swap (k : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d)
      = ∑ d ∈ n.divisors, Nat.totient d * k ^ (n / d) := by
  rw [← Nat.sum_div_divisors n (fun d => Nat.totient d * k ^ (n / d))]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  rw [Nat.div_div_self hdvd (NeZero.ne n)]

/-- **(B′)** Textbook necklace count: `∑_{d∣n} φ(d) · k^{n/d} = (#necklaces) · n`. -/
theorem textbook_necklace_count (k : ℕ) :
    (∑ d ∈ n.divisors, Nat.totient d * k ^ (n / d))
      = Nat.card (MulAction.orbitRel.Quotient (Rot n) (Rot n → Fin k)) * n := by
  rw [← divisor_sum_swap, divisor_sum_eq_card_necklaces_mul]

#check @sum_pow_gcd_eq_divisor_sum
#check @divisor_sum_eq_card_necklaces_mul
#check @divisor_sum_swap
#check @textbook_necklace_count

end BurnsideCountingOQ03OQ02OQ01OQ02
