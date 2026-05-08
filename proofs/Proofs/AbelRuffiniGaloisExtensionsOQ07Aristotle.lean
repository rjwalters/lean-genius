/-
  Aristotle targets for Burnside's p^a q^b Theorem (OQ-07)
  Routine supporting lemmas for automated proof search.
  See AbelRuffiniGaloisExtensionsOQ07.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (Burnside's theorem itself remains `sorry`
    in the main file)
  - Routine cardinality / divisibility / Sylow facts that the main proof
    will rely on
  - No axioms (use `theorem ... := by sorry` instead)
  - No definition sorries

  Included targets (Session 2 scaffold):
  - card_pq_pow_pos        : 0 < p^a * q^b when p, q ≥ 2
  - p_pow_dvd_card_pq      : p^a ∣ p^a * q^b
  - q_pow_dvd_card_pq      : q^b ∣ p^a * q^b
  - prime_pow_solvable     : finite group of prime-power order is solvable
                             (already in Mathlib via IsPGroup.isNilpotent
                             + IsNilpotent.to_isSolvable; restated as a
                             single-step Aristotle target)
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Nilpotent

namespace AbelRuffiniGaloisExtensionsOQ07Aristotle

open Group

/-- Routine: a product of two prime powers is positive. -/
theorem card_pq_pow_pos {p q a b : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    0 < p ^ a * q ^ b :=
  Nat.mul_pos (Nat.pos_of_ne_zero (pow_ne_zero a (by omega)))
              (Nat.pos_of_ne_zero (pow_ne_zero b (by omega)))

/-- Routine: `p^a` divides `p^a * q^b`. -/
theorem p_pow_dvd_card_pq (p q a b : ℕ) : p ^ a ∣ p ^ a * q ^ b :=
  Dvd.intro _ rfl

/-- Routine: `q^b` divides `p^a * q^b`. -/
theorem q_pow_dvd_card_pq (p q a b : ℕ) : q ^ b ∣ p ^ a * q ^ b := by
  rw [Nat.mul_comm]
  exact Dvd.intro _ rfl

/-- A finite group of prime-power order is solvable.

This is provable directly in Mathlib via `IsPGroup.of_card`, `IsPGroup.isNilpotent`,
and the `IsNilpotent.to_isSolvable` instance. Restated here as a one-step
Aristotle target supporting the trivial reductions of Burnside's theorem. -/
theorem prime_pow_solvable {G : Type*} [Group G] [Finite G]
    {p n : ℕ} [Fact p.Prime] (hG : Nat.card G = p ^ n) : IsSolvable G := by
  have hpG : IsPGroup p G := IsPGroup.of_card hG
  haveI : IsNilpotent G := hpG.isNilpotent
  infer_instance

end AbelRuffiniGaloisExtensionsOQ07Aristotle
