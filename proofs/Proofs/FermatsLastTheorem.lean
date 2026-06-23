import Mathlib.NumberTheory.FLT.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Fermat's Last Theorem

## What This Proves
For n > 2, there are no three positive integers a, b, c such that aⁿ + bⁿ = cⁿ.
We present the cases n = 3 and n = 4 from Mathlib, and axiomatize the general
theorem pending the Lean FLT project completion.

## Approach
- **Foundation (from Mathlib):** Mathlib provides `fermatLastTheoremFour` and
  `fermatLastTheoremThree`. The general theorem will come from the Imperial
  College Lean FLT project.
- **Original Contributions:** This file provides pedagogical exposition of
  the proof structure (Frey curves, modularity, Ribet's theorem) and wraps
  the Mathlib theorems. The general case is axiomatized.
- **Proof Techniques Demonstrated:** Infinite descent (n=4), algebraic number
  theory (n=3), axiomatization of deep results.

## Status
- [ ] Complete proof
- [ ] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [ ] Pedagogical example
- [x] Incomplete (has sorries)

## Mathlib Dependencies
- `FermatLastTheoremFor` : Statement that n has no non-trivial solutions
- `fermatLastTheoremFour` : Fermat's proof for n = 4 via infinite descent
- `fermatLastTheoremThree` : Euler's proof for n = 3
- `NumberTheory.FLT.Basic` : FLT foundations

Note: 3 sorries remain. The full theorem requires the Modularity Theorem and
Ribet's theorem, currently being formalized by the Imperial College FLT project.

Historical Note: Fermat claimed a proof in 1637. Andrew Wiles proved it in
1995 using the modularity of elliptic curves—one of mathematics' greatest
achievements.
-/

-- Mathlib defines these key theorems
#check FermatLastTheoremFor
#check fermatLastTheoremFour
#check fermatLastTheoremThree

/-! ## Part I: The Theorem Statement

Fermat's Last Theorem: For n > 2, the equation xⁿ + yⁿ = zⁿ has no solutions
in positive integers. -/

namespace FermatsLastTheorem

/-! ### The Statement

We use Mathlib's formulation: `FermatLastTheoremFor n` states that n has no
non-trivial integer solutions. -/

/-- The statement of Fermat's Last Theorem for a specific exponent.
    FermatLastTheoremFor n means: ∀ a b c : ℤ, a ≠ 0 → b ≠ 0 → c ≠ 0 → a^n + b^n ≠ c^n -/
example (n : ℕ) : Prop := FermatLastTheoremFor n

/-! ## Part II: The Frey Curve

Given a hypothetical counterexample (a, b, c) to Fermat's equation for prime p,
the Frey curve is the elliptic curve:

  E : y² = x(x - aᵖ)(x + bᵖ)

This curve has remarkable properties:
- It is semi-stable (all bad reduction is multiplicative)
- Its discriminant is Δ = (abc)²ᵖ · 2⁻⁸ (divisible by huge prime powers)
- Its conductor is unusually small compared to its discriminant -/

-- The Frey curve construction would be:
-- def FreyCurve (a b : ℤ) (p : ℕ) [hp : Fact (Nat.Prime p)] :
--     EllipticCurve ℚ where
--   ... (requires Mathlib.NumberTheory.EllipticCurve.Basic)

/- FreyCurve_is_semistable: For any solution aᵖ + bᵖ = cᵖ with p > 2 and abc ≠ 0,
   the associated Frey elliptic curve E_{a,b,c} : y² = x(x - aᵖ)(x + bᵖ) is semi-stable.
   This is a key geometric property proved by Ribet using properties of the discriminant.
   It would need the definition of elliptic curves and semi-stability in Lean 4. -/

/-! ## Part III: The Modularity Theorem

**Theorem (Wiles, Taylor-Wiles 1995)**: Every semi-stable elliptic curve over ℚ
is modular.

An elliptic curve E is *modular* if there exists a modular form f of weight 2
for some Γ₀(N) such that E and f have the same L-function. This means:

  aₚ(E) = aₚ(f) for all primes p ∤ N

where aₚ(E) = p + 1 - #E(𝔽ₚ) counts points over the finite field. -/

/- The Modularity Theorem for semi-stable elliptic curves:
    All semi-stable elliptic curves over ℚ are modular.
    This is the main theorem Wiles proved, requiring ~100 pages of proof.
    (Axiomatized in this file as the key step toward FLT.) -/

/-! ## Part IV: Ribet's Theorem

**Theorem (Ribet 1986)**: If E is the Frey curve arising from a solution to
Fermat's equation at a prime p > 2, then E cannot be modular.

More precisely: if E is modular corresponding to a form f of level N,
then p | N. But the conductor of the Frey curve forces N to be 2,
and there are no weight 2 cusp forms for Γ₀(2). Contradiction! -/

/- RibetTheorem: Ribet's theorem (1986): if the Frey curve E_{a,b,c} were modular
   (corresponding to a cusp form f of level N), then p | N, but the conductor of
   the Frey curve forces N = 2, and there are no weight-2 cusp forms for Γ₀(2).
   This contradiction means Frey curves cannot be modular. It requires modularity
   theory and level-lowering — beyond current Mathlib formalization. -/

/-! ## Part V: Putting It Together

The proof of FLT for odd prime exponents:
1. Assume (a, b, c, p) is a counterexample with p an odd prime
2. Construct the Frey curve E
3. By Modularity, E is modular
4. By Ribet, E is not modular
5. Contradiction! -/

/-- FLT for odd primes follows from Modularity + Ribet (axiomatized).
    The actual proof would unpack the theorems above. -/
axiom FLT_for_odd_primes (p : ℕ) (hp : Nat.Prime p) (hodd : p > 2) :
  FermatLastTheoremFor p

/-! ## Part VI: Special Cases with Elementary Proofs

These cases have elementary proofs that don't require the full machinery. -/

/-- FLT for n = 4 was proved by Fermat himself using infinite descent.
    This is the only case Fermat definitely proved! -/
theorem fermat_four : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

/-- For n = 4, the proof uses infinite descent:
    Assume x⁴ + y⁴ = z² has a solution (proving x⁴ + y⁴ = z⁴ impossible).
    Factor: (x² + y²)(x² - y²) = z²
    Use Pythagorean triple structure to get a smaller solution.
    But we can't descend forever! -/
example : FermatLastTheoremFor 4 := fermatLastTheoremFour

/-- FLT for n = 3 was proved by Euler (1770).
    The proof uses the Eisenstein integers ℤ[ω] where ω = e^{2πi/3}.
    This is fully formalized in Mathlib! -/
theorem fermat_three : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/-- If FLT holds for n, it holds for all multiples of n.
    So we only need to prove it for n = 4 and odd primes. -/
theorem flt_multiple (n m : ℕ) (hm : m ≠ 0) (h : FermatLastTheoremFor n) :
    FermatLastTheoremFor (m * n) := by
  intro a b c ha hb hc heq
  have hpow : a^(m*n) + b^(m*n) = c^(m*n) := heq
  have hpow' : (a^m)^n + (b^m)^n = (c^m)^n := by
    simp only [← pow_mul]
    exact hpow
  have ham : a^m ≠ 0 := pow_ne_zero m ha
  have hbm : b^m ≠ 0 := pow_ne_zero m hb
  have hcm : c^m ≠ 0 := pow_ne_zero m hc
  exact h (a^m) (b^m) (c^m) ham hbm hcm hpow'

/-! ## Part VII: The Full Theorem

The complete statement, combining all cases. The proof that
FermatLastTheoremFor n holds for ALL n ≥ 3 requires the full
machinery above for prime exponents, then reduction to primes. -/

/-- Fermat's Last Theorem (Full Statement).
    For n ≥ 3, the equation xⁿ + yⁿ = zⁿ has no solutions in positive integers.

    Status: Axiomatized pending the Lean FLT project.
    See: https://github.com/ImperialCollegeLondon/FLT -/
axiom fermatLastTheorem :
  ∀ n : ℕ, n ≥ 3 → FermatLastTheoremFor n

/-! ### Corollaries

These follow directly from FermatLastTheoremFor. -/

/-- No non-zero integer cubes sum to a cube (from Mathlib). -/
theorem no_sum_of_cubes : FermatLastTheoremFor 3 :=
  fermatLastTheoremThree

/-- No non-zero integer fourth powers sum to a fourth power (from Mathlib). -/
theorem no_sum_of_fourth_powers : FermatLastTheoremFor 4 :=
  fermatLastTheoremFour

/-- No non-zero integer fifth powers sum to a fifth power (axiomatized). -/
theorem no_sum_of_fifth_powers : FermatLastTheoremFor 5 :=
  fermatLastTheorem 5 (by norm_num)

end FermatsLastTheorem
