import Proofs.Erdos85PolarityFamily

/-!
# A cofinal prime-order family for Erdős Problem 85

The projective-plane construction specializes to the prime fields `ZMod p`.
Consequently the exact values supplied by the polarity construction occur at
arbitrarily large parameters.
-/

namespace Erdos85.Polarity

/-- The polarity construction over the prime field of order `p`. -/
theorem minDegreeForC4_prime (p : ℕ) (hp : p.Prime) :
    minDegreeForC4 (p ^ 2 + p + 1) = p + 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := minDegreeForC4_projectivePlane (K := ZMod p)
  simp only [Nat.card_eq_fintype_card, ZMod.card] at h
  convert h using 1 <;> ring

/-- Exact values from the prime-field polarity graphs occur beyond every
prescribed field-order bound. -/
theorem exists_prime_exact_family_ge (B : ℕ) :
    ∃ p : ℕ, B ≤ p ∧ p.Prime ∧
      minDegreeForC4 (p ^ 2 + p + 1) = p + 1 := by
  obtain ⟨p, hp, hBp⟩ := Nat.exists_infinite_primes B
  exact ⟨p, hp, hBp, minDegreeForC4_prime p hBp⟩

/-- In particular, the exact prime-field family proves directly that the
extremal threshold function is unbounded. -/
theorem minDegreeForC4_unbounded :
    ∀ B : ℕ, ∃ n : ℕ, B < minDegreeForC4 n := by
  intro B
  obtain ⟨p, hBp, hp, hexact⟩ := exists_prime_exact_family_ge B
  refine ⟨p ^ 2 + p + 1, ?_⟩
  rw [hexact]
  omega

end Erdos85.Polarity
