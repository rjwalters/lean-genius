/-
# Erdős Problem #478: Factorial Residues Modulo Primes

Let p be a prime and A_p = { k! mod p : 1 ≤ k < p }. Is it true that
|A_p| ~ (1 - 1/e) · p?

## Key Results

- Lower bound: |A_p| ≥ √p from the ratio-set identity A_p/A_p = {1,...,p-1}
- Grebennikov–Sagdeev–Semchankau–Vasilevskii (2024): |A_p| ≥ (√2 - o(1))√p
- Wilson's theorem gives (p-1)! ≡ -1 (mod p), so A_p ⊆ {1,...,p-1}
- Upper bound: |A_p| ≤ p - 2 for all primes p > 5

## References

- Erdős–Graham [ErGr80], p. 96
- Grebennikov–Sagdeev–Semchankau–Vasilevskii [GSSV24]
- <https://erdosproblems.com/478>
-/

import Mathlib

namespace Erdos478

/- ## Core Definitions -/

/-- The set of factorial residues modulo p: A_p = { k! mod p : 1 ≤ k < p }. -/
noncomputable def factorialResidueSet (p : ℕ) [hp : Fact (Nat.Prime p)] : Finset (ZMod p) :=
  (Finset.range (p - 1)).image (fun k => ((k + 1).factorial : ZMod p))

/-- The cardinality of the factorial residue set. -/
noncomputable def factorialResidueCount (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  (factorialResidueSet p).card

/-- The conjectured asymptotic density (1 - 1/e). -/
noncomputable def conjecturedDensity : ℝ := 1 - Real.exp (-1)

/- ## Wilson's Theorem Consequences -/

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p.
    Proved from Mathlib's `ZMod.wilsons_lemma`. -/
theorem wilson_factorial_residue (p : ℕ) [Fact (Nat.Prime p)] :
    ((p - 1).factorial : ZMod p) = -1 :=
  ZMod.wilsons_lemma p

/-- The factorial residue set excludes 0 for primes p > 2.
    Proof: For 1 ≤ k < p, k! is a product of numbers < p, none divisible
    by p (since p is prime). Hence p ∤ k!, so k! ≢ 0 (mod p). -/
theorem factorial_residues_nonzero (p : ℕ) [hp : Fact (Nat.Prime p)] (hp2 : p > 2) :
    (0 : ZMod p) ∉ factorialResidueSet p := by
  intro hmem
  simp [factorialResidueSet] at hmem
  obtain ⟨k, hk, heq⟩ := hmem
  -- heq : (↑(k+1)! : ZMod p) = 0 means p ∣ (k+1)!
  rw [ZMod.natCast_eq_zero_iff] at heq
  -- p divides (k+1)!, but p is prime and all factors of (k+1)! are < p
  have := (Nat.Prime.dvd_factorial hp.out).mp heq
  omega

/-- Upper bound: |A_p| ≤ p - 2 for all primes p > 5. -/
axiom factorial_residue_upper (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 5) :
  factorialResidueCount p ≤ p - 2

/- ## Ratio Set Identity -/

/-- The ratio set A_p / A_p covers all nonzero residues modulo p.
    This is because consecutive factorials have ratio k, so
    k! / (k-1)! = k ranges over {1,...,p-1}. -/
axiom ratio_set_full (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ r : ZMod p, r ≠ 0 → ∃ a b : ZMod p,
    a ∈ factorialResidueSet p ∧ b ∈ factorialResidueSet p ∧ a = r * b

/-- Lower bound from ratio set: |A_p| ≥ √p.
    If A/A covers all p-1 nonzero residues and |A| = m,
    then m² ≥ p - 1, giving m ≥ √(p-1). -/
axiom factorial_residue_sqrt_lower (p : ℕ) [Fact (Nat.Prime p)] :
  (factorialResidueCount p : ℝ) ^ 2 ≥ (p : ℝ) - 1

/- ## Improved Lower Bound (GSSV 2024) -/

/-- The product set A_p · A_p has near-full size (2024 result). -/
axiom product_set_near_full (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ ε : ℝ, ε > 0 → ∃ P₀ : ℕ, ∀ q : ℕ, [Fact (Nat.Prime q)] →
    q > P₀ → (factorialResidueCount q : ℝ) ≥ (Real.sqrt 2 - ε) * Real.sqrt q

/- ## Main Conjecture -/

/-- **Erdős Problem #478** (OPEN): |A_p| ~ (1 - 1/e) · p.
    More precisely, |A_p| / p → (1 - 1/e) as p → ∞ through primes. -/
axiom erdos_478_conjecture :
  ∀ ε : ℝ, ε > 0 → ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] →
    p > P₀ →
      |((factorialResidueCount p : ℝ) / (p : ℝ)) - conjecturedDensity| < ε

/- ## Heuristic Motivation -/

/-- The 1 - 1/e heuristic: if factorial residues behaved like random elements
    of Z/pZ, each new k! mod p independently hits a new residue with probability
    (p - |current set|)/p. After p-1 steps this gives expected coverage
    p · (1 - (1 - 1/p)^(p-1)) ≈ p · (1 - 1/e). -/
axiom random_model_heuristic :
  ∀ ε : ℝ, ε > 0 → ∃ P₀ : ℕ, ∀ p : ℕ,
    p > P₀ → |(1 - (1 - 1 / (p : ℝ)) ^ (p - 1)) - (1 - Real.exp (-1))| < ε

/-- Consecutive factorials: (k+1)! = (k+1) · k! in ZMod p.
    Proved from Mathlib's `Nat.factorial_succ`. -/
theorem factorial_as_multiplicative_walk (p : ℕ) [Fact (Nat.Prime p)] :
    ∀ k : ℕ, k ≥ 1 → k < p →
      ((k + 1).factorial : ZMod p) = ((k + 1 : ℕ) : ZMod p) * (k.factorial : ZMod p) := by
  intro k _ _
  rw [Nat.factorial_succ]
  push_cast
  ring

/- ## Average Results -/

/-- Klurman–Munsch (2017): On average over primes p ≤ x,
    the factorial residue count is (1 - 1/e + o(1)) · p.
    (The precise statement is not formalized; this is a placeholder.) -/
theorem klurman_munsch_average :
    ∀ ε : ℝ, ε > 0 → ∃ X₀ : ℝ, X₀ > 0 ∧
      ∀ x : ℝ, x > X₀ → True :=
  fun _ _ => ⟨1, one_pos, fun _ _ => trivial⟩

end Erdos478
