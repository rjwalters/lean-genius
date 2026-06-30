/-
# Necklace Burnside Sum in Divisor Form: ∑_{r} k^{gcd(n,r)} = ∑_{d∣n} φ(n/d)·k^d
## (burnside-counting-oq-03-oq-02-oq-01-oq-02)

**Open question** (from `burnside-counting-oq-03-oq-02-oq-01`, OQ[2]): the parent
proves the concrete cyclic cycle-count `cyc (rotation r) = gcd(n, r)` and assembles the
integer-form Burnside total
`∑_{r : ZMod n} k^{gcd(n,r)} = (#necklaces up to rotation) · n`  (its result `(C)`).
Push this to the **standard number-theoretic divisor form** by grouping the `n`
rotations according to the value of their cycle count.

The classical statement is
  `∑_{r=0}^{n-1} k^{gcd(n,r)} = ∑_{d ∣ n} φ(n/d) · k^d`.
The mechanism is fiber-counting: a rotation `r` contributes `k^{gcd(n,r)}`, the
positions `r ∈ [0, n)` with `gcd(n, r) = d` are exactly the multiples `d·s` with
`gcd(n/d, s) = 1`, and there are `φ(n/d)` of them. We prove:

* **(D) Range form** (`sum_range_pow_gcd_eq_sum_divisors`):
    `∑_{r ∈ range n} k^{gcd(n,r)} = ∑_{d ∣ n} φ(n/d) · k^d`.
  Regroup `range n` along the map `r ↦ gcd(n,r)` (whose values are divisors of `n`)
  via `Finset.sum_fiberwise_of_maps_to'`; each fiber is constant `k^d`, and its
  cardinality is `φ(n/d)` by Mathlib's `Nat.totient_div_of_dvd` — the exact
  combinatorial input behind Gauss's `∑_{d∣n} φ(d) = n`.

* **(E) ZMod form** (`sum_pow_gcd_eq_sum_divisors_totient`):
    `∑_{r : ZMod n} k^{gcd(n, r.val)} = ∑_{d ∣ n} φ(n/d) · k^d`,
  obtained from `(D)` by the bijection `ZMod.val : ZMod n ≃ range n`.

* **(F) Necklace count in divisor form** (`card_necklaces_mul_eq_sum_divisors`):
    `(#necklaces up to rotation) · n = ∑_{d ∣ n} φ(n/d) · k^d`,
  combining `(E)` with the parent's integer-form Burnside total `(C)`. Dividing by
  `n` gives the textbook cyclic necklace formula
  `(1/n) ∑_{d∣n} φ(n/d) k^d`.

**Sorry count**: 0. **Axiom count**: 0 (only Lean/Mathlib foundational axioms).
-/

import Mathlib
import Proofs.BurnsideCountingOQ03OQ02OQ01

open Finset BigOperators MulAction

namespace BurnsideCountingOQ03OQ02OQ01OQ02

open BurnsideCountingOQ03OQ02OQ01 (Rot rotation sum_pow_gcd_eq_card_necklaces_mul)

/-! ## Section I: (D) The divisor-sum identity over `range n`

This is the purely number-theoretic heart of the matter: grouping the `n` residues by
the value of `gcd(n, ·)` turns the Burnside sum into a sum over divisors, weighted by
totients. -/

/-- **(D)** The cyclic Burnside sum in divisor form:
`∑_{r < n} k^{gcd(n,r)} = ∑_{d ∣ n} φ(n/d) · k^d`. -/
theorem sum_range_pow_gcd_eq_sum_divisors (n k : ℕ) (hn : 0 < n) :
    (∑ r ∈ Finset.range n, k ^ Nat.gcd n r)
      = ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  -- Regroup `range n` along `r ↦ gcd(n, r)`, whose values lie in `n.divisors`.
  rw [← Finset.sum_fiberwise_of_maps_to'
        (s := Finset.range n) (t := n.divisors) (g := fun r => Nat.gcd n r)
        (fun r _ => Nat.mem_divisors.2 ⟨Nat.gcd_dvd_left n r, hn.ne'⟩)
        (f := fun d => k ^ d)]
  -- Each fiber is a constant `k^d`; its cardinality is `φ(n/d)`.
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.sum_const, smul_eq_mul, Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-! ## Section II: (E) The same identity summed over `ZMod n`

The parent's Burnside total is phrased over `ZMod n` (residues `r.val`), so we transport
`(D)` along the bijection `ZMod.val : ZMod n ≃ range n`. -/

variable {n : ℕ} [NeZero n]

/-- **(E)** The cyclic Burnside sum over `ZMod n` in divisor form. -/
theorem sum_pow_gcd_eq_sum_divisors_totient (k : ℕ) :
    (∑ r : ZMod n, k ^ Nat.gcd n r.val)
      = ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rw [← sum_range_pow_gcd_eq_sum_divisors n k hn]
  -- `ZMod.val` bijects `univ : Finset (ZMod n)` with `range n`.
  refine Finset.sum_bij' (fun (r : ZMod n) _ => r.val) (fun (i : ℕ) _ => (i : ZMod n))
    (fun r _ => Finset.mem_range.2 (ZMod.val_lt r))
    (fun i _ => Finset.mem_univ _)
    (fun r _ => ZMod.natCast_zmod_val r)
    (fun i hi => ZMod.val_natCast_of_lt (Finset.mem_range.1 hi))
    (fun r _ => rfl)

/-! ## Section III: (F) Necklace count in divisor form

Combining `(E)` with the parent's integer-form Burnside total `(C)` gives the textbook
divisor-sum formula for the number of `k`-colored `n`-bead necklaces. -/

/-- **(F)** The number of `k`-colored `n`-bead necklaces (up to rotation), times `n`,
equals the totient-weighted divisor sum `∑_{d ∣ n} φ(n/d) · k^d`. Dividing by `n`
recovers the classical cyclic necklace count `(1/n) ∑_{d∣n} φ(n/d) k^d`. -/
theorem card_necklaces_mul_eq_sum_divisors (k : ℕ) :
    Nat.card (orbitRel.Quotient (Rot n) (Rot n → Fin k)) * n
      = ∑ d ∈ n.divisors, Nat.totient (n / d) * k ^ d := by
  rw [← sum_pow_gcd_eq_card_necklaces_mul (k := k), sum_pow_gcd_eq_sum_divisors_totient]

#check @sum_range_pow_gcd_eq_sum_divisors
#check @sum_pow_gcd_eq_sum_divisors_totient
#check @card_necklaces_mul_eq_sum_divisors

end BurnsideCountingOQ03OQ02OQ01OQ02
