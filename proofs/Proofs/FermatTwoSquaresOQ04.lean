/-
  Jacobi's Two-Square Theorem — the divisor-character sum side
  Open Question: fermat-two-squares-oq-04

  Fermat's two-squares theorem characterizes *which* primes are sums of two
  squares.  Jacobi's refinement is quantitative: the number of representations
  of `n` as an ordered sum of two (signed) squares is

        r₂(n) = 4 · ∑_{d ∣ n} χ₄(d),

  where `χ₄` is the non-principal Dirichlet character mod 4 (the character of
  ℚ(√-1)/ℚ).  The full counting theorem requires the arithmetic of the
  Gaussian integers ℤ[i] and is not available in Mathlib.  This file formalizes
  the **arithmetic engine** of the formula: the divisor-character sum

        δ(n) := ∑_{d ∣ n} χ₄(d)    (`jacobiSum n`),

  realized as the Dirichlet convolution `ζ * χ₄`, and proves its structural
  properties:

  * `jacobiSum` is **multiplicative** (Dirichlet product of two multiplicative
    arithmetic functions);
  * its value on prime powers is the geometric sum `∑_{i≤k} χ₄(p)^i`, hence
      δ(2^k) = 1,  δ(p^k) = k+1  (p ≡ 1 mod 4),  δ(p^k) ∈ {0,1}  (p ≡ 3 mod 4);
  * δ(n) ≥ 0 for all n;
  * **bridge to representability** (the qualitative shadow of Jacobi's theorem):
      δ(n) > 0  ⇔  n is a sum of two squares,
      δ(n) = 0  ⇔  n is NOT a sum of two squares.
    This recovers the prime-factor criterion of Fermat/Gauss from the
    *character sum* without any Gaussian-integer counting machinery.
  * For a prime p, δ(p) = 1 + χ₄(p), so δ(p) = 2 when p ≡ 1 (mod 4) — matching
    r₂(p) = 8 — and δ(p) = 0 when p ≡ 3 (mod 4).

  The construction mirrors Mathlib's `DirichletCharacter.zetaMul` (defined there
  only for ℂ-valued quadratic characters, used in Dirichlet-`L` non-vanishing),
  ported to the integer-valued `χ₄` so that it can be connected to the
  ℕ-valued representability criterion `Nat.eq_sq_add_sq_iff`.

  References:
  - Jacobi (1834): two-square theorem, r₂(n) = 4 ∑_{d∣n} χ₄(d)
  - Zagier (1990): one-sentence existence proof (parent file)
  - FermatTwoSquares.lean: parent two-squares characterization
  - FermatTwoSquaresOQ05.lean: the n ≡ 3 (mod 4) obstruction
  - Mathlib `DirichletCharacter.zetaMul` (NumberTheory/LSeries/Nonvanishing)
-/

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

open ArithmeticFunction ArithmeticFunction.zeta DirichletCharacter ZMod Finset

namespace FermatTwoSquaresOQ04

-- ============================================================================
-- Part I: The Jacobi divisor-character sum  δ(n) = ∑_{d ∣ n} χ₄(d)
-- ============================================================================

/-- **The Jacobi divisor-character sum** `δ(n) = ∑_{d ∣ n} χ₄(d)`, realized as
the Dirichlet convolution of the constant function `1` (= `ζ`) with the
non-principal character `χ₄` mod 4.  This is the right-hand side of Jacobi's
two-square theorem `r₂(n) = 4 δ(n)`. -/
noncomputable def jacobiSum : ArithmeticFunction ℤ :=
  (ζ : ArithmeticFunction ℤ) * toArithmeticFunction (χ₄ ·)

/-- `δ` is multiplicative: it is the Dirichlet product of the multiplicative
function `ζ` and the (completely) multiplicative character `χ₄`. -/
theorem isMultiplicative_jacobiSum : jacobiSum.IsMultiplicative :=
  isMultiplicative_zeta.natCast.mul (isMultiplicative_toArithmeticFunction χ₄)

/-- Unfolding `δ(n) = ∑_{d ∣ n} χ₄(d)` for `n ≠ 0`. -/
theorem jacobiSum_apply {n : ℕ} (_hn : n ≠ 0) :
    jacobiSum n = ∑ d ∈ n.divisors, χ₄ (d : ZMod 4) := by
  unfold jacobiSum
  rw [coe_zeta_mul_apply]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [toArithmeticFunction, hd0]

-- ============================================================================
-- Part II: Value on prime powers — the geometric sum  ∑_{i≤k} χ₄(p)^i
-- ============================================================================

/-- On a prime power, `δ` is the geometric sum `∑_{i=0}^{k} χ₄(p)^i`. -/
theorem jacobiSum_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    jacobiSum (p ^ k) = ∑ i ∈ range (k + 1), (χ₄ (p : ZMod 4)) ^ i := by
  rw [jacobiSum_apply (pow_ne_zero k hp.ne_zero), Nat.sum_divisors_prime_pow hp]
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.cast_pow, map_pow]

/-- `δ(p^k) ≥ 0` for every prime `p` — the geometric sum of a `{0,1,-1}`-valued
quadratic character is nonnegative.  (Ports `zetaMul_prime_pow_nonneg`.) -/
theorem jacobiSum_prime_pow_nonneg {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 ≤ jacobiSum (p ^ k) := by
  rw [jacobiSum_prime_pow hp]
  rcases isQuadratic_χ₄ (p : ZMod 4) with h | h | h
  · refine sum_nonneg fun i _ => ?_; simp only [h, le_refl, pow_nonneg]
  · refine sum_nonneg fun i _ => ?_; simp only [h, one_pow, zero_le_one]
  · simp only [h, neg_one_geom_sum]; split_ifs; exacts [le_rfl, zero_le_one]

/-- **The key prime-power dichotomy.**  `δ(p^k) > 0` exactly when the obstruction
to representability is absent: either `p ≢ 3 (mod 4)`, or the exponent `k` is
even.  Concretely δ(2^k)=1, δ(p^k)=k+1 for p≡1, and δ(p^k)=[k even] for p≡3. -/
theorem jacobiSum_prime_pow_pos_iff {p : ℕ} (hp : p.Prime) (k : ℕ) :
    0 < jacobiSum (p ^ k) ↔ (p % 4 = 3 → Even k) := by
  rw [jacobiSum_prime_pow hp]
  have hval := χ₄_nat_eq_if_mod_four p
  by_cases hpar : p % 2 = 0
  · -- p = 2: χ₄(p) = 0, the sum collapses to the single term χ₄(1) = 1
    rw [if_pos hpar] at hval
    rw [hval]
    have hsum : ∑ i ∈ range (k + 1), (0 : ℤ) ^ i = 1 := by
      rw [sum_range_succ']
      simp only [pow_succ, mul_zero, sum_const_zero, pow_zero, zero_add]
    have h43 : p % 4 ≠ 3 := by omega
    rw [hsum]
    exact iff_of_true one_pos (fun h => absurd h h43)
  · rw [if_neg hpar] at hval
    by_cases hmod1 : p % 4 = 1
    · -- p ≡ 1 (mod 4): χ₄(p) = 1, the sum equals k + 1 > 0
      rw [if_pos hmod1] at hval
      rw [hval]
      have hpos : 0 < ∑ i ∈ range (k + 1), (1 : ℤ) ^ i := by
        apply sum_pos
        · intro i _; rw [one_pow]; exact one_pos
        · exact ⟨0, mem_range.mpr (Nat.succ_pos k)⟩
      have h43 : p % 4 ≠ 3 := by omega
      exact iff_of_true hpos (fun h => absurd h h43)
    · -- p ≡ 3 (mod 4): χ₄(p) = -1, the sum is the alternating geometric series
      rw [if_neg hmod1] at hval
      rw [hval]
      have h43 : p % 4 = 3 := by omega
      rw [neg_one_geom_sum]
      by_cases hk : Even k
      · rw [if_neg (by rw [Nat.even_add_one]; simpa using hk)]
        exact iff_of_true one_pos (fun _ => hk)
      · rw [if_pos (by rw [Nat.even_add_one]; simpa using hk)]
        exact iff_of_false (lt_irrefl 0) (fun h => hk (h h43))

-- ============================================================================
-- Part III: Bridge to representability — the qualitative Jacobi theorem
-- ============================================================================

/-- `δ(n) ≥ 0` for all `n`.  (Ports `zetaMul_nonneg`.) -/
theorem jacobiSum_nonneg (n : ℕ) : 0 ≤ jacobiSum n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simpa only [isMultiplicative_jacobiSum.multiplicative_factorization _ hn] using
      Finset.prod_nonneg fun p hp =>
        jacobiSum_prime_pow_nonneg (Nat.prime_of_mem_primeFactors hp) _

/-- **Qualitative Jacobi two-square theorem.**  The divisor-character sum is
*strictly positive* exactly on the sums of two squares:

      0 < δ(n)  ⇔  ∃ x y, n = x² + y².

This recovers Fermat/Gauss's prime-factorization criterion (every prime
`q ≡ 3 (mod 4)` occurs to an even power) directly from the character sum,
with no Gaussian-integer counting. -/
theorem jacobiSum_pos_iff_sq_add_sq {n : ℕ} (hn : n ≠ 0) :
    0 < jacobiSum n ↔ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  have hprod : jacobiSum n
      = ∏ p ∈ n.primeFactors, jacobiSum (p ^ n.factorization p) := by
    rw [isMultiplicative_jacobiSum.multiplicative_factorization _ hn,
      ← Nat.support_factorization]
    rfl
  rw [hprod, Nat.eq_sq_add_sq_iff]
  constructor
  · -- positivity of the product forces every prime-power factor positive
    intro hpos q hq h4
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hge : 0 ≤ jacobiSum (q ^ n.factorization q) :=
      jacobiSum_prime_pow_nonneg hqp _
    have hfac_pos : 0 < jacobiSum (q ^ n.factorization q) := by
      rcases hge.eq_or_lt with h | h
      · exact absurd hpos (by rw [Finset.prod_eq_zero hq h.symm]; exact lt_irrefl 0)
      · exact h
    have hEven := (jacobiSum_prime_pow_pos_iff hqp (n.factorization q)).mp hfac_pos h4
    rwa [Nat.factorization_def n hqp] at hEven
  · -- each factor is positive, so the product is
    intro h
    apply Finset.prod_pos
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [jacobiSum_prime_pow_pos_iff hpp]
    intro h4
    rw [Nat.factorization_def n hpp]
    exact h p hp h4

/-- The complementary form: `δ(n) = 0` exactly on the non-representable `n`. -/
theorem jacobiSum_eq_zero_iff {n : ℕ} (hn : n ≠ 0) :
    jacobiSum n = 0 ↔ ¬ ∃ x y : ℕ, n = x ^ 2 + y ^ 2 := by
  rw [← jacobiSum_pos_iff_sq_add_sq hn]
  constructor
  · intro h; rw [h]; exact lt_irrefl 0
  · intro h
    rcases (jacobiSum_nonneg n).eq_or_lt with h' | h'
    · exact h'.symm
    · exact absurd h' h

-- ============================================================================
-- Part IV: Headline prime values (Jacobi's count for primes)
-- ============================================================================

/-- For a prime `p ≡ 1 (mod 4)`, `δ(p) = 2`, i.e. `r₂(p) = 4·2 = 8`: the eight
representations `(±a, ±b), (±b, ±a)` of the unique unordered pair. -/
theorem jacobiSum_prime_one_mod_four {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    jacobiSum p = 2 := by
  have hk := jacobiSum_prime_pow hp 1
  rw [pow_one] at hk
  rw [hk, χ₄_nat_one_mod_four hmod]
  norm_num [Finset.sum_range_succ]

/-- For a prime `p ≡ 3 (mod 4)`, `δ(p) = 0`, i.e. `r₂(p) = 0`: no representation
as a sum of two squares. -/
theorem jacobiSum_prime_three_mod_four {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3) :
    jacobiSum p = 0 := by
  have hk := jacobiSum_prime_pow hp 1
  rw [pow_one] at hk
  rw [hk, χ₄_nat_three_mod_four hmod]
  norm_num [Finset.sum_range_succ]

end FermatTwoSquaresOQ04
