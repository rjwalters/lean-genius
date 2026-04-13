/-
Gauss's Generalization of Wilson's Theorem (OQ-04)

For n ≥ 3, the product of all integers coprime to n in {1, ..., n-1}
is congruent to -1 (mod n) if and only if n is one of:
  4, p^k, or 2·p^k  (p odd prime, k ≥ 1).

This is equivalent to: ∏ (ZMod n)ˣ = -1 iff the unit group is cyclic.

## Status
- [x] unitsProduct definition (product of coprime residues)
- [x] IsCyclic ↔ units product = -1 (via Mathlib + OQ02 bridge)
- [x] Full classification: {4, p^k, 2p^k} (via Mathlib's ZMod.isCyclic_units_iff)
- [x] Computational verification for n ≤ 50
- [x] Connection: concrete (unitsProduct n % n) ↔ abstract (∏ units)

Parent proof: WilsonsTheorem.lean (Wilson's theorem for primes)
Open question: "Can we formalize the Gauss generalization?"
Answer: Yes. See gauss_wilson below.

Proof architecture:
- WilsonsTheoremOQ01.lean: unitsProduct, computational verification, classification
- WilsonsTheoremOQ02.lean: abstract bridge (∏ units = -1 ↔ IsCyclic)
-/

import Proofs.WilsonsTheoremOQ01

namespace WilsonsTheoremGauss

open WilsonsTheoremGeneralization

/-
## Gauss's Generalization — Main Statement

The product of all units mod n satisfies ∏ units ≡ -1 (mod n)
if and only if n ∈ {4, p^k, 2·p^k} for some odd prime p.

This is proved by combining:
1. The concrete→abstract bridge (unitsProduct ↔ IsCyclic) from OQ01/OQ02
2. Mathlib's ZMod.isCyclic_units_iff classifying when (ZMod n)ˣ is cyclic
-/

/-- **Gauss–Wilson Theorem**: For n ≥ 3, the product of all coprime residues
    mod n equals n−1 (i.e., ≡ −1) iff n is 4, an odd prime power, or twice
    an odd prime power.

    This is a re-export of `gaussWilson_classification` from OQ01,
    presented as the standalone answer to open question OQ-04. -/
theorem gauss_wilson (n : ℕ) (hn : n ≥ 3) :
    unitsProduct n % n = n - 1 ↔
    (∃ p k, Nat.Prime p ∧ p ≠ 2 ∧ k ≥ 1 ∧ (n = p ^ k ∨ n = 2 * p ^ k)) ∨ n = 4 :=
  gaussWilson_classification n hn

/-- The product of coprime residues mod n equals n−1 iff (ZMod n)ˣ is cyclic. -/
theorem gauss_wilson_cyclic (n : ℕ) (hn : n ≥ 3) :
    unitsProduct n % n = n - 1 ↔ IsCyclic (ZMod n)ˣ :=
  unitsProduct_eq_neg_one_iff_cyclic hn

/-- For any odd prime p, the product of coprime residues mod p equals p−1
    (recovering Wilson's theorem via the Gauss generalization). -/
theorem gauss_wilson_prime (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    unitsProduct p % p = p - 1 := by
  rw [gauss_wilson p hp3]
  left
  exact ⟨p, 1, hp, by omega, by omega, Or.inl (by simp)⟩

end WilsonsTheoremGauss
