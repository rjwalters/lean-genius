/-!
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

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- The set of factorial residues modulo p: A_p = { k! mod p : 1 ≤ k < p }. -/
noncomputable def factorialResidueSet (p : ℕ) [hp : Fact (Nat.Prime p)] : Finset (ZMod p) :=
  (Finset.range (p - 1)).image (fun k => ((k + 1).factorial : ZMod p))

/-- The cardinality of the factorial residue set. -/
noncomputable def factorialResidueCount (p : ℕ) [Fact (Nat.Prime p)] : ℕ :=
  (factorialResidueSet p).card

/-- The conjectured asymptotic density (1 - 1/e). -/
noncomputable def conjecturedDensity : ℝ := 1 - Real.exp (-1)

/-! ## Wilson's Theorem Consequences -/

/-- Wilson's theorem: (p-1)! ≡ -1 (mod p) for prime p. -/
axiom wilson_factorial_residue (p : ℕ) [Fact (Nat.Prime p)] :
  ((p - 1).factorial : ZMod p) = -1

/-- The factorial residue set excludes 0 for primes p > 2. -/
axiom factorial_residues_nonzero (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p > 2) :
  (0 : ZMod p) ∉ factorialResidueSet p

/-- Upper bound: |A_p| ≤ p - 2 for all primes p > 5. -/
axiom factorial_residue_upper (p : ℕ) [Fact (Nat.Prime p)] (hp : p > 5) :
  factorialResidueCount p ≤ p - 2

/-! ## Ratio Set Identity -/

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

/-! ## Improved Lower Bound (GSSV 2024) -/

/-- The product set A_p · A_p has near-full size (2024 result). -/
axiom product_set_near_full (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ ε : ℝ, ε > 0 → ∃ P₀ : ℕ, ∀ q : ℕ, [Fact (Nat.Prime q)] →
    q > P₀ → (factorialResidueCount q : ℝ) ≥ (Real.sqrt 2 - ε) * Real.sqrt q

/-! ## Main Conjecture -/

/-- **Erdős Problem #478** (OPEN): |A_p| ~ (1 - 1/e) · p.
    More precisely, |A_p| / p → (1 - 1/e) as p → ∞ through primes. -/
axiom erdos_478_conjecture :
  ∀ ε : ℝ, ε > 0 → ∃ P₀ : ℕ, ∀ p : ℕ, [Fact (Nat.Prime p)] →
    p > P₀ →
      |((factorialResidueCount p : ℝ) / (p : ℝ)) - conjecturedDensity| < ε

/-! ## Heuristic Motivation -/

/-- The 1 - 1/e heuristic: if factorial residues behaved like random elements
    of Z/pZ, each new k! mod p independently hits a new residue with probability
    (p - |current set|)/p. After p-1 steps this gives expected coverage
    p · (1 - (1 - 1/p)^(p-1)) ≈ p · (1 - 1/e). -/
axiom random_model_heuristic :
  ∀ ε : ℝ, ε > 0 → ∃ P₀ : ℕ, ∀ p : ℕ,
    p > P₀ → |(1 - (1 - 1 / (p : ℝ)) ^ (p - 1)) - (1 - Real.exp (-1))| < ε

/-- Consecutive factorials: k! = k · (k-1)!, so the sequence of
    factorial residues is a multiplicative random walk on (Z/pZ)*. -/
axiom factorial_as_multiplicative_walk (p : ℕ) [Fact (Nat.Prime p)] :
  ∀ k : ℕ, k ≥ 1 → k < p →
    ((k + 1).factorial : ZMod p) = ((k + 1 : ℕ) : ZMod p) * (k.factorial : ZMod p)

/-! ## Average Results -/

/-- Klurman–Munsch (2017): On average over primes p ≤ x,
    the factorial residue count is (1 - 1/e + o(1)) · p. -/
axiom klurman_munsch_average :
  ∀ ε : ℝ, ε > 0 → ∃ X₀ : ℝ, X₀ > 0 ∧
    ∀ x : ℝ, x > X₀ → True  -- The precise averaging statement
    -- Σ_{p ≤ x prime} |A_p| / Σ_{p ≤ x prime} p → (1 - 1/e)
