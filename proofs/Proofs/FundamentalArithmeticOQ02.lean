import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Tactic

/-
# Failure of Unique Factorization in ℤ[√-5]

## Open Question
"Can the failure of unique factorization in ℤ[√-5] be formalized as a
counterexample showing it is not a UFD?"

## Answer
**Yes.** We formalize the classic counterexample:

  6 = 2 · 3 = (1 + √-5)(1 - √-5)

These are two genuinely different factorizations of 6 into irreducibles
in ℤ[√-5]. To show this is a true failure of unique factorization, we prove:
1. ℤ[√-5] is an integral domain
2. The norm N(a + b√-5) = a² + 5b² is multiplicative
3. 2, 3, (1+√-5), (1-√-5) are all irreducible in ℤ[√-5]
4. 2 is not prime (hence ℤ[√-5] is not a UFD)

The norm argument is key: an element is a unit iff N(α) = 1, and
irreducibility can be tested by showing N(α) has no non-trivial divisor
that is itself a norm.

## Historical Context
This example motivated Kummer's invention of "ideal numbers" (1847) and
Dedekind's theory of ideals (1871), leading to the concept of class number.
ℤ[√-5] has class number 2 — the failure of unique factorization is measured
by the class group.

## References
- Kummer (1847): Ideal numbers
- Dedekind (1871): Theory of algebraic integers
- Ireland & Rosen, "A Classical Introduction to Modern Number Theory"
-/

set_option linter.unusedVariables false

namespace FundamentalArithmeticOQ02

open Zsqrtd

-- ============================================================
-- PART 1: ℤ[√-5] as a Ring
-- ============================================================

abbrev ZSqrtNeg5 := Zsqrtd (-5)

/-- -5 is not a perfect square, so ℤ[√-5] is an integral domain. -/
instance : Nonsquare (-5 : ℤ) where
  ns n h := by
    have := sq_nonneg n
    have : n * n = n ^ 2 := by ring
    linarith

def two : ZSqrtNeg5 := ⟨2, 0⟩
def three : ZSqrtNeg5 := ⟨3, 0⟩
def onePlusSqrt : ZSqrtNeg5 := ⟨1, 1⟩
def oneMinusSqrt : ZSqrtNeg5 := ⟨1, -1⟩
def six : ZSqrtNeg5 := ⟨6, 0⟩

-- ============================================================
-- PART 2: The Norm Function
-- ============================================================

/-- The norm of a + b√-5 is a² + 5b².
    This is multiplicative: N(αβ) = N(α)N(β). -/
def norm (z : ZSqrtNeg5) : ℤ := z.re ^ 2 + 5 * z.im ^ 2

theorem norm_nonneg (z : ZSqrtNeg5) : 0 ≤ norm z := by
  unfold norm; nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem norm_mul (z w : ZSqrtNeg5) : norm (z * w) = norm z * norm w := by
  unfold norm; simp only [Zsqrtd.mul_re, Zsqrtd.mul_im]; ring

theorem norm_two : norm two = 4 := by unfold norm two; norm_num
theorem norm_three : norm three = 9 := by unfold norm three; norm_num
theorem norm_onePlus : norm onePlusSqrt = 6 := by unfold norm onePlusSqrt; norm_num
theorem norm_oneMinus : norm oneMinusSqrt = 6 := by unfold norm oneMinusSqrt; norm_num
theorem norm_six : norm six = 36 := by unfold norm six; norm_num

-- ============================================================
-- PART 3: No Elements of Norm 2 or 3
-- ============================================================

/-- No element of ℤ[√-5] has norm 2.
    This is the key lemma: a² + 5b² = 2 has no integer solutions. -/
theorem no_norm_two (z : ZSqrtNeg5) : norm z ≠ 2 := by
  intro h
  unfold norm at h
  have hb : z.im = 0 := by
    by_contra hb'
    have : z.im ^ 2 ≥ 1 := by nlinarith [sq_abs z.im, abs_pos.mpr hb']
    nlinarith [sq_nonneg z.re]
  have : z.re ^ 2 = 2 := by nlinarith [hb]
  have h1 : -1 ≤ z.re := by nlinarith
  have h2 : z.re ≤ 1 := by nlinarith
  interval_cases z.re <;> omega

/-- No element of ℤ[√-5] has norm 3. -/
theorem no_norm_three (z : ZSqrtNeg5) : norm z ≠ 3 := by
  intro h
  unfold norm at h
  have hb : z.im = 0 := by
    by_contra hb'
    have : z.im ^ 2 ≥ 1 := by nlinarith [sq_abs z.im, abs_pos.mpr hb']
    nlinarith [sq_nonneg z.re]
  have : z.re ^ 2 = 3 := by nlinarith [hb]
  have h1 : -1 ≤ z.re := by nlinarith
  have h2 : z.re ≤ 1 := by nlinarith
  interval_cases z.re <;> omega

-- ============================================================
-- PART 4: Units in ℤ[√-5]
-- ============================================================

/-- A unit in ℤ[√-5] has norm 1, and conversely. -/
theorem unit_iff_norm_one (z : ZSqrtNeg5) : IsUnit z ↔ norm z = 1 := by
  constructor
  · -- Forward: IsUnit → norm = 1
    rintro ⟨u, rfl⟩
    -- u * u⁻¹ = 1 in ZSqrtNeg5, so norm(u) * norm(u⁻¹) = norm(1) = 1
    have key : norm (↑u : ZSqrtNeg5) * norm (u.inv : ZSqrtNeg5) = 1 := by
      calc norm (↑u : ZSqrtNeg5) * norm (u.inv : ZSqrtNeg5)
          = norm ((↑u : ZSqrtNeg5) * u.inv) := (norm_mul _ _).symm
        _ = norm (1 : ZSqrtNeg5) := by rw [u.val_inv]
        _ = 1 := by unfold norm; simp
    -- norm is a unit in ℤ, hence ±1; but norm ≥ 0 forces norm = 1
    have hu := isUnit_of_mul_eq_one _ _ key
    rcases Int.isUnit_iff.mp hu with h | h
    · exact h
    · linarith [norm_nonneg (↑u : ZSqrtNeg5)]
  · -- Backward: norm = 1 → IsUnit
    intro h
    unfold norm at h
    have him : z.im = 0 := by
      by_contra h'
      have : z.im ^ 2 ≥ 1 := by nlinarith [sq_abs z.im, abs_pos.mpr h']
      nlinarith [sq_nonneg z.re]
    have hre : z.re = 1 ∨ z.re = -1 := by
      have hsq : z.re ^ 2 = 1 := by nlinarith [him]
      have : (z.re - 1) * (z.re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h' | h'
      · left; linarith
      · right; linarith
    rcases hre with hre | hre
    · have : z = 1 := by ext <;> simp [hre, him]
      rw [this]; exact isUnit_one
    · have : z = -1 := by ext <;> simp [hre, him]
      rw [this]; exact isUnit_one.neg

/-- The only units in ℤ[√-5] are ±1 -/
theorem units_are_pm_one (z : ZSqrtNeg5) (hz : IsUnit z) :
    z = ⟨1, 0⟩ ∨ z = ⟨-1, 0⟩ := by
  have h := (unit_iff_norm_one z).mp hz
  unfold norm at h
  have him : z.im = 0 := by
    by_contra h'
    have : z.im ^ 2 ≥ 1 := by nlinarith [sq_abs z.im, abs_pos.mpr h']
    nlinarith [sq_nonneg z.re]
  have hre : z.re = 1 ∨ z.re = -1 := by
    have hsq : z.re ^ 2 = 1 := by nlinarith [him]
    have : (z.re - 1) * (z.re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h' | h'
    · left; linarith
    · right; linarith
  rcases hre with h | h
  · left; ext <;> simp [h, him]
  · right; ext <;> simp [h, him]

-- ============================================================
-- PART 5: The Two Factorizations of 6
-- ============================================================

/-- **First factorization**: 6 = 2 · 3 -/
theorem factorization_1 : six = two * three := by
  unfold six two three; ext <;> simp <;> ring

/-- **Second factorization**: 6 = (1+√-5)(1-√-5) -/
theorem factorization_2 : six = onePlusSqrt * oneMinusSqrt := by
  unfold six onePlusSqrt oneMinusSqrt; ext <;> simp <;> ring

-- ============================================================
-- PART 6: Irreducibility of the Factors
-- ============================================================

/-- **2 is irreducible in ℤ[√-5]**

    Proof by norm: N(2) = 4. If 2 = αβ with neither a unit, then
    N(α), N(β) > 1 and N(α)N(β) = 4. So N(α) = N(β) = 2.
    But a² + 5b² = 2 has no integer solutions. -/
theorem two_irreducible : Irreducible two := by
  refine ⟨fun h => absurd ((unit_iff_norm_one two).mp h) (by rw [norm_two]; omega), ?_⟩
  intro a b hab
  have hn : norm a * norm b = 4 := by rw [← norm_mul, hab, norm_two]
  have ha := norm_nonneg a; have hb := norm_nonneg b
  -- If neither is a unit, both norms > 1, product = 4, so both = 2
  by_contra hc; push_neg at hc; obtain ⟨hna, hnb⟩ := hc
  have hna1 : 1 < norm a := by
    have h0 : norm a ≠ 0 := by intro h0; have := hn; rw [h0, zero_mul] at this; omega
    have h1 : norm a ≠ 1 := fun h1 => hna ((unit_iff_norm_one a).mpr h1)
    omega
  have hnb1 : 1 < norm b := by
    have h0 : norm b ≠ 0 := by intro h0; have := hn; rw [h0, mul_zero] at this; omega
    have h1 : norm b ≠ 1 := fun h1 => hnb ((unit_iff_norm_one b).mpr h1)
    omega
  -- norm a ≥ 2 and norm b ≥ 2, product = 4, so norm a = 2
  have : norm a = 2 := by nlinarith
  exact no_norm_two a this

/-- **3 is irreducible in ℤ[√-5]**

    Proof: N(3) = 9. If 3 = αβ, then N(α)N(β) = 9.
    Need N(α) = 3, but a² + 5b² = 3 has no solutions. -/
theorem three_irreducible : Irreducible three := by
  refine ⟨fun h => absurd ((unit_iff_norm_one three).mp h) (by rw [norm_three]; omega), ?_⟩
  intro a b hab
  have hn : norm a * norm b = 9 := by rw [← norm_mul, hab, norm_three]
  have ha := norm_nonneg a; have hb := norm_nonneg b
  by_contra hc; push_neg at hc; obtain ⟨hna, hnb⟩ := hc
  have hna1 : 1 < norm a := by
    have h0 : norm a ≠ 0 := by intro h0; have := hn; rw [h0, zero_mul] at this; omega
    have h1 : norm a ≠ 1 := fun h1 => hna ((unit_iff_norm_one a).mpr h1)
    omega
  have hnb1 : 1 < norm b := by
    have h0 : norm b ≠ 0 := by intro h0; have := hn; rw [h0, mul_zero] at this; omega
    have h1 : norm b ≠ 1 := fun h1 => hnb ((unit_iff_norm_one b).mpr h1)
    omega
  -- norm a ∈ {2,3,4} (≥ 2 and ≤ 4), product = 9
  have ha_bound : norm a ≤ 4 := by nlinarith
  have : norm a = 2 ∨ norm a = 3 ∨ norm a = 4 := by omega
  rcases this with h | h | h
  · exact no_norm_two a h
  · exact no_norm_three a h
  · -- norm a = 4 → 4 * norm b = 9, impossible
    omega

/-- **1 + √-5 is irreducible in ℤ[√-5]**

    Proof: N(1+√-5) = 6. If 1+√-5 = αβ, then N(α)N(β) = 6.
    Possible nontrivial splits: {2,3} or {3,2}. But there are no elements
    of norm 2 or 3. -/
theorem onePlus_irreducible : Irreducible onePlusSqrt := by
  refine ⟨fun h => absurd ((unit_iff_norm_one onePlusSqrt).mp h)
    (by rw [norm_onePlus]; omega), ?_⟩
  intro a b hab
  have hn : norm a * norm b = 6 := by rw [← norm_mul, hab, norm_onePlus]
  have ha := norm_nonneg a; have hb := norm_nonneg b
  by_contra hc; push_neg at hc; obtain ⟨hna, hnb⟩ := hc
  have hna1 : 1 < norm a := by
    have h0 : norm a ≠ 0 := by intro h0; have := hn; rw [h0, zero_mul] at this; omega
    have h1 : norm a ≠ 1 := fun h1 => hna ((unit_iff_norm_one a).mpr h1)
    omega
  have hnb1 : 1 < norm b := by
    have h0 : norm b ≠ 0 := by intro h0; have := hn; rw [h0, mul_zero] at this; omega
    have h1 : norm b ≠ 1 := fun h1 => hnb ((unit_iff_norm_one b).mpr h1)
    omega
  -- norm a ∈ {2,3} (≥ 2, ≤ 3 since norm b ≥ 2)
  have ha_bound : norm a ≤ 3 := by nlinarith
  have : norm a = 2 ∨ norm a = 3 := by omega
  rcases this with h | h
  · exact no_norm_two a h
  · exact no_norm_three a h

/-- **1 - √-5 is irreducible in ℤ[√-5]**

    Same argument as for 1 + √-5 (by conjugate symmetry). -/
theorem oneMinus_irreducible : Irreducible oneMinusSqrt := by
  refine ⟨fun h => absurd ((unit_iff_norm_one oneMinusSqrt).mp h)
    (by rw [norm_oneMinus]; omega), ?_⟩
  intro a b hab
  have hn : norm a * norm b = 6 := by rw [← norm_mul, hab, norm_oneMinus]
  have ha := norm_nonneg a; have hb := norm_nonneg b
  by_contra hc; push_neg at hc; obtain ⟨hna, hnb⟩ := hc
  have hna1 : 1 < norm a := by
    have h0 : norm a ≠ 0 := by intro h0; have := hn; rw [h0, zero_mul] at this; omega
    have h1 : norm a ≠ 1 := fun h1 => hna ((unit_iff_norm_one a).mpr h1)
    omega
  have hnb1 : 1 < norm b := by
    have h0 : norm b ≠ 0 := by intro h0; have := hn; rw [h0, mul_zero] at this; omega
    have h1 : norm b ≠ 1 := fun h1 => hnb ((unit_iff_norm_one b).mpr h1)
    omega
  have ha_bound : norm a ≤ 3 := by nlinarith
  have : norm a = 2 ∨ norm a = 3 := by omega
  rcases this with h | h
  · exact no_norm_two a h
  · exact no_norm_three a h

-- ============================================================
-- PART 7: The Factors Are Not Associates
-- ============================================================

/-- **2 and (1+√-5) are not associates**

    If two = onePlusSqrt * u for a unit u, then the imaginary part gives
    0 = 1 * u.re + 1 * ... , but the imaginary part of two * any element
    is always even, while onePlusSqrt has odd imaginary part. -/
theorem two_not_assoc_onePlus : ¬Associated two onePlusSqrt := by
  rintro ⟨u, hu⟩
  -- hu : two * ↑u = onePlusSqrt
  have := congr_arg Zsqrtd.im hu
  simp only [two, onePlusSqrt] at this
  -- (⟨2,0⟩ * ↑u).im = 1, which is 2 * (↑u).im = 1
  simp at this
  omega

/-- **2 and (1-√-5) are not associates** -/
theorem two_not_assoc_oneMinus : ¬Associated two oneMinusSqrt := by
  rintro ⟨u, hu⟩
  have := congr_arg Zsqrtd.im hu
  simp only [two, oneMinusSqrt] at this
  simp at this
  omega

/-- **2 and 3 are not associates** -/
theorem two_not_assoc_three : ¬Associated two three := by
  rintro ⟨u, hu⟩
  have := congr_arg Zsqrtd.re hu
  simp only [two, three] at this
  simp at this
  -- 2 * (↑u).re = 3, impossible (2 doesn't divide 3)
  omega

-- ============================================================
-- PART 8: 2 is Not Divisible by (1+√-5) or (1-√-5) and vice versa
-- ============================================================

/-- 2 does not divide (1+√-5) in ℤ[√-5].
    If ⟨1,1⟩ = ⟨2,0⟩ * q, then 1 = 2*q.im, impossible. -/
theorem two_not_dvd_onePlus : ¬(two ∣ onePlusSqrt) := by
  rintro ⟨q, hq⟩
  have := congr_arg Zsqrtd.im hq
  simp [onePlusSqrt, two] at this
  omega

/-- 2 does not divide (1-√-5) in ℤ[√-5]. -/
theorem two_not_dvd_oneMinus : ¬(two ∣ oneMinusSqrt) := by
  rintro ⟨q, hq⟩
  have := congr_arg Zsqrtd.im hq
  simp [oneMinusSqrt, two] at this
  omega

-- ============================================================
-- PART 9: ℤ[√-5] is NOT a UFD
-- ============================================================

/-- **Main Theorem: ℤ[√-5] is not a UFD**

    Strategy: In a UFD, every irreducible is prime. We show 2 is
    irreducible but NOT prime:
    - 2 | 6 = (1+√-5)(1-√-5), so 2 | (1+√-5)(1-√-5)
    - But 2 ∤ (1+√-5) and 2 ∤ (1-√-5)
    - So 2 is not prime
    - Contradiction with UFD. -/
theorem zsqrt_neg5_not_ufd : ¬ UniqueFactorizationMonoid ZSqrtNeg5 := by
  intro hufm
  haveI : UniqueFactorizationMonoid ZSqrtNeg5 := hufm
  -- In a UFD, irreducible → prime
  have hprime : Prime two := irreducible_iff_prime.mp two_irreducible
  -- 2 | (1+√-5)(1-√-5) since 6 = 2·3 = (1+√-5)(1-√-5)
  have hdvd : two ∣ onePlusSqrt * oneMinusSqrt :=
    ⟨three, by rw [← factorization_1, factorization_2]⟩
  -- By primality, 2 | (1+√-5) or 2 | (1-√-5)
  rcases hprime.dvd_or_dvd hdvd with h | h
  · exact two_not_dvd_onePlus h
  · exact two_not_dvd_oneMinus h

-- ============================================================
-- PART 10: The Class Number Connection
-- ============================================================

/-
The failure of unique factorization in ℤ[√-5] is quantified by the
**class number** h = 2. This means:
- Unique factorization of IDEALS still holds (Dedekind domain)
- Every ideal is a product of prime ideals
- But not every ideal is principal
- The class group ℤ/2ℤ measures the "failure" of unique factorization

In ℤ[√-5]:
- (2) = (2, 1+√-5)² (the ideal (2) is not prime)
- (3) = (3, 1+√-5)(3, 1-√-5) (splits into two prime ideals)
- (6) = (2, 1+√-5)²(3, 1+√-5)(3, 1-√-5) (UNIQUE prime ideal factorization)

The two element factorizations 2·3 and (1+√-5)(1-√-5) correspond to
different groupings of this unique prime ideal factorization.
-/

-- ============================================================
-- PART 11: Summary
-- ============================================================

/-
## Summary of Results

### Core Computations (fully proved):
1. norm_nonneg: N(z) ≥ 0
2. norm_mul: N(zw) = N(z)N(w) (multiplicativity)
3. norm_two/three/onePlus/oneMinus/six: Concrete norm computations
4. no_norm_two: ¬∃z, N(z) = 2
5. no_norm_three: ¬∃z, N(z) = 3

### Algebraic Structure (fully proved):
6. unit_iff_norm_one: units ↔ norm = 1
7. units_are_pm_one: units = {±1}
8. factorization_1: 6 = 2 · 3
9. factorization_2: 6 = (1+√-5)(1-√-5)
10. two/three/onePlus/oneMinus_irreducible: all four are irreducible
11. two_not_assoc_onePlus/oneMinus/three: non-association
12. two_not_dvd_onePlus/oneMinus: divisibility failures

### Main Theorem:
13. zsqrt_neg5_not_ufd: ℤ[√-5] is NOT a UFD
-/

#check @zsqrt_neg5_not_ufd
#check @two_irreducible
#check @three_irreducible
#check @onePlus_irreducible
#check @oneMinus_irreducible
#check @factorization_1
#check @factorization_2

end FundamentalArithmeticOQ02
