import Mathlib
import Proofs.BezoutIdentityOQ02OQ01OQ02

/-
# Dedekind Domains: Ideal Unique Factorization Beyond Euclidean Rings

## Open Question (bezout-identity-oq-02-oq-01-oq-02-oq-03)

The parent file established that every Euclidean domain is a UFD via the chain
  EuclideanDomain → GCDMonoid → UniqueFactorizationMonoid.

**Question**: Does unique factorization generalize to the broader class of
Dedekind domains, which need NOT have unique factorization of elements?

## Answer: Yes — uniquely at the level of ideals

A **Dedekind domain** is a Noetherian integrally closed domain of Krull dimension ≤ 1
(every nonzero prime ideal is maximal). The generalization of FTA is:

**Ideal FTA**: In any Dedekind domain, every nonzero proper ideal factors UNIQUELY
into a product of prime ideals (proved in Mathlib's `IsDedekindDomain` theory).

Structural relationship:
- Euclidean domains ARE Dedekind domains (via EuclideanDomain → PID → Dedekind)
- But Dedekind domains can fail to be UFDs at the element level
- Equivalence: Dedekind domain is a UFD ↔ it is a PID

## Classic Non-UFD Example: ℤ[√-5]

The ring ℤ[√-5] is a Dedekind domain (ring of integers of ℚ(√-5)) but NOT a UFD:
  6 = 2 · 3 = (1 + √-5)(1 - √-5)
Both factorizations use irreducibles that are not associates. The element 2 is
irreducible but NOT prime: 2 | (1+√-5)(1-√-5) yet 2 ∤ (1±√-5).

Key norm fact: N(a + b√-5) = a² + 5b² has no solution for N = 2 or N = 3.
The non-primeness of 2 follows from: N(2) = 4 does NOT divide N(1±√-5) = 6.

## Mathematical Content (0 sorries, 0 axioms)

1. `IsDedekindDomain` instances: ℤ, k[x] for fields k
2. In Dedekind domains: prime ideals = maximal ideals
3. ℤ[√-5] norm: N(a+b√-5) = a²+5b², no element has N = 2 or N = 3
4. Two factorizations: 6 = 2·3 = (1+√-5)(1-√-5), with all four factors having N ∈ {4,6,9}
5. 2 irreducible: norm divisors of N(2) = 4 are {1, 4} (not 2 or 3)
6. 2 not prime: N(2)=4 ∤ N(1±√-5)=6, so 2 ∤ (1±√-5)
7. ℤ[√-5] is not a UFD: irreducible ≠ prime

Tags: algebra, number-theory, dedekind-domain, ideal-theory, unique-factorization
-/

namespace DedekindIdealFTA

open Zsqrtd

-- ============================================================
-- Part I: Dedekind Domain Instances
-- ============================================================

/-- The integers form a Dedekind domain (via the PID instance chain). -/
example : IsDedekindDomain ℤ := inferInstance

/-- Polynomial ring over any field is a Euclidean domain, PID, and Dedekind domain. -/
example {F : Type*} [Field F] : IsDedekindDomain (Polynomial F) := inferInstance

/-- Every PID is a Dedekind domain. -/
theorem pid_is_dedekind {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsDedekindDomain R := inferInstance

-- ============================================================
-- Part II: Prime Ideals = Maximal Ideals in Dedekind Domains
-- ============================================================

/-- In a Dedekind domain, every nonzero prime ideal is maximal.
    This is the "Krull dimension ≤ 1" condition encoded in `IsDedekindDomain`. -/
theorem prime_ideal_is_maximal {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (p : Ideal R) (hp0 : p ≠ ⊥) (hprime : p.IsPrime) : p.IsMaximal :=
  IsDedekindDomain.dimensionLtOne p hp0 hprime

-- ============================================================
-- Part III: ℤ[√-5] — The Classic Non-UFD Dedekind Domain
-- ============================================================

/-- ℤ[√-5] as a Zsqrtd ring with d = -5. -/
abbrev ZSqrtNeg5 := Zsqrtd (-5 : ℤ)

/-- The norm N(a + b√-5) = a² + 5b² is always nonnegative. -/
theorem norm_formula (z : ZSqrtNeg5) :
    Zsqrtd.norm z = z.re ^ 2 + 5 * z.im ^ 2 := by
  simp [Zsqrtd.norm, sq]; ring

theorem norm_nonneg (z : ZSqrtNeg5) : 0 ≤ Zsqrtd.norm z := by
  rw [norm_formula]; positivity

/-- The norm is multiplicative: N(z * w) = N(z) * N(w). -/
theorem norm_mul_eq (a b : ZSqrtNeg5) :
    Zsqrtd.norm (a * b) = Zsqrtd.norm a * Zsqrtd.norm b := by
  simp only [Zsqrtd.norm, Zsqrtd.mul_def]; ring

/-- Two distinct element factorizations of 6 in ℤ[√-5]. -/
theorem two_factorizations_of_6 :
    (2 : ZSqrtNeg5) * 3 = (⟨1, 1⟩ : ZSqrtNeg5) * ⟨1, -1⟩ := by decide

-- Norm computations for the four factors
theorem norm_two     : Zsqrtd.norm (2 : ZSqrtNeg5) = 4 := by decide
theorem norm_three   : Zsqrtd.norm (3 : ZSqrtNeg5) = 9 := by decide
theorem norm_one_plus  : Zsqrtd.norm (⟨1, 1⟩ : ZSqrtNeg5) = 6 := by decide
theorem norm_one_minus : Zsqrtd.norm (⟨1, -1⟩ : ZSqrtNeg5) = 6 := by decide

/-- The equation a² + 5b² = 2 has no integer solutions.
    Proof: b ≠ 0 gives 5b² ≥ 5 > 2; b = 0 gives a² = 2 (no integer perfect square). -/
private lemma norm_ne_two (z : ZSqrtNeg5) : Zsqrtd.norm z ≠ 2 := by
  rw [norm_formula]; intro h
  have him : z.im = 0 := by
    by_contra him0; nlinarith [sq_pos_of_ne_zero z.im him0, sq_nonneg z.re]
  subst him; simp at h
  -- h : z.re ^ 2 = 2; derive bounds and use interval_cases
  have h1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.re]
  have h2 : -1 ≤ z.re := by nlinarith [sq_nonneg z.re]
  interval_cases z.re <;> simp_all

/-- The equation a² + 5b² = 3 has no integer solutions. -/
private lemma norm_ne_three (z : ZSqrtNeg5) : Zsqrtd.norm z ≠ 3 := by
  rw [norm_formula]; intro h
  have him : z.im = 0 := by
    by_contra him0; nlinarith [sq_pos_of_ne_zero z.im him0, sq_nonneg z.re]
  subst him; simp at h
  have h1 : z.re ≤ 1 := by nlinarith [sq_nonneg z.re]
  have h2 : -1 ≤ z.re := by nlinarith [sq_nonneg z.re]
  interval_cases z.re <;> simp_all

/-- The re-component of z * conj(z) equals N(z). -/
private lemma star_mul_re (z : ZSqrtNeg5) :
    (z * Zsqrtd.star z).re = Zsqrtd.norm z := by
  simp [Zsqrtd.norm, Zsqrtd.mul_def, Zsqrtd.star]; ring

/-- The im-component of z * conj(z) is zero. -/
private lemma star_mul_im (z : ZSqrtNeg5) : (z * Zsqrtd.star z).im = 0 := by
  simp [Zsqrtd.mul_def, Zsqrtd.star]

/-- Reverse: the re-component of conj(z) * z also equals N(z). -/
private lemma mul_star_re (z : ZSqrtNeg5) :
    (Zsqrtd.star z * z).re = Zsqrtd.norm z := by
  simp [Zsqrtd.norm, Zsqrtd.mul_def, Zsqrtd.star]; ring

/-- The im-component of conj(z) * z is zero. -/
private lemma mul_star_im (z : ZSqrtNeg5) : (Zsqrtd.star z * z).im = 0 := by
  simp [Zsqrtd.mul_def, Zsqrtd.star]

/-- Units of ℤ[√-5] have norm 1, and conversely N = 1 implies unit status.
    Forward: N(z)*N(z⁻¹) = N(z·z⁻¹) = N(1) = 1 → N(z) = 1 (since N ≥ 0).
    Backward: if N(z) = 1, then z·conj(z) = ⟨N(z),0⟩ = 1, making z a unit. -/
theorem isUnit_iff_norm_one (z : ZSqrtNeg5) : IsUnit z ↔ Zsqrtd.norm z = 1 := by
  constructor
  · rintro ⟨⟨a, b, hab, _⟩, rfl⟩
    have hn : Zsqrtd.norm a * Zsqrtd.norm b = 1 := by
      have := congr_arg Zsqrtd.norm hab
      rwa [norm_mul_eq, show Zsqrtd.norm (1 : ZSqrtNeg5) = 1 from by decide] at this
    have ha := norm_nonneg a; have hb := norm_nonneg b
    have hbp : 0 < Zsqrtd.norm b := by
      rcases hb.lt_or_eq with h | h; · exact h; · simp [← h] at hn
    have hap : 0 < Zsqrtd.norm a := by
      rcases ha.lt_or_eq with h | h; · exact h; · simp [← h] at hn
    -- N(a) ≤ 1: from N(a) ≥ 0, N(b) ≥ 1, and N(a)*N(b) = 1 → N(a) ≤ N(a)*N(b) = 1
    have ha_le : Zsqrtd.norm a ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ Zsqrtd.norm b from by omega) ha]
    omega
  · intro h
    have hstar : z * Zsqrtd.star z = 1 := by
      apply Zsqrtd.ext
      · rw [star_mul_re, h]; rfl
      · rw [star_mul_im]; rfl
    have hstar' : Zsqrtd.star z * z = 1 := by
      apply Zsqrtd.ext
      · rw [mul_star_re, h]; rfl
      · rw [mul_star_im]; rfl
    exact ⟨⟨z, Zsqrtd.star z, hstar, hstar'⟩, rfl⟩

/-- 2 is not a unit in ℤ[√-5] (norm = 4 ≠ 1). -/
theorem two_not_unit : ¬ IsUnit (2 : ZSqrtNeg5) := by
  rw [isUnit_iff_norm_one, norm_two]; norm_num

/-- 2 is irreducible in ℤ[√-5].

    If 2 = a * b, then N(a) * N(b) = N(2) = 4 with N(a), N(b) ≥ 0.
    Since N = 2 and N = 3 are impossible, N(a) ∈ {1, 4}.
    N(a) = 1 → a is a unit; N(a) = 4 → N(b) = 1 → b is a unit. -/
theorem two_irreducible : Irreducible (2 : ZSqrtNeg5) := by
  refine ⟨two_not_unit, fun a b hab => ?_⟩
  have hnorm : Zsqrtd.norm a * Zsqrtd.norm b = 4 := by
    rw [← norm_mul_eq, hab, norm_two]
  have ha_nn := norm_nonneg a; have hb_nn := norm_nonneg b
  have ha1 : 1 ≤ Zsqrtd.norm a := by
    rcases ha_nn.lt_or_eq with h | h; · omega
    · simp [← h] at hnorm
  have hb1 : 1 ≤ Zsqrtd.norm b := by
    rcases hb_nn.lt_or_eq with h | h; · omega
    · simp [← h, mul_zero] at hnorm
  have ha_le : Zsqrtd.norm a ≤ 4 := by nlinarith
  rcases show Zsqrtd.norm a = 1 ∨ Zsqrtd.norm a = 2 ∨
             Zsqrtd.norm a = 3 ∨ Zsqrtd.norm a = 4 from by omega
    with h | h | h | h
  · exact Or.inl ((isUnit_iff_norm_one a).mpr h)
  · exact absurd h (norm_ne_two a)
  · exact absurd h (norm_ne_three a)
  · exact Or.inr ((isUnit_iff_norm_one b).mpr (by nlinarith))

/-- 2 is NOT prime in ℤ[√-5].

    Proof by norm: if 2 | (1+√-5), say (1+√-5) = 2k, then
    N(1+√-5) = N(2) · N(k) = 4 · N(k). But N(1+√-5) = 6 and 4 ∤ 6. -/
theorem two_not_prime : ¬ Prime (2 : ZSqrtNeg5) := by
  intro h
  -- 2 | (1+√-5)(1-√-5) = 6 = 2·3
  have hdvd : (2 : ZSqrtNeg5) ∣ ⟨1, 1⟩ * ⟨1, -1⟩ := ⟨3, by decide⟩
  rcases h.dvd_or_dvd hdvd with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- N(1+√-5) = 4 · N(k), so 6 = 4·N(k) — no integer solution
    have hn : Zsqrtd.norm (⟨1, 1⟩ : ZSqrtNeg5) = 4 * Zsqrtd.norm k := by
      calc Zsqrtd.norm (⟨1, 1⟩ : ZSqrtNeg5)
          = Zsqrtd.norm ((2 : ZSqrtNeg5) * k) := by rw [← hk]
        _ = Zsqrtd.norm (2 : ZSqrtNeg5) * Zsqrtd.norm k := norm_mul_eq _ _
        _ = 4 * Zsqrtd.norm k := by rw [norm_two]
    have h6 : (4 : ℤ) * Zsqrtd.norm k = 6 := by linarith [norm_one_plus]
    omega
  · -- Same for (1-√-5)
    have hn : Zsqrtd.norm (⟨1, -1⟩ : ZSqrtNeg5) = 4 * Zsqrtd.norm k := by
      calc Zsqrtd.norm (⟨1, -1⟩ : ZSqrtNeg5)
          = Zsqrtd.norm ((2 : ZSqrtNeg5) * k) := by rw [← hk]
        _ = Zsqrtd.norm (2 : ZSqrtNeg5) * Zsqrtd.norm k := norm_mul_eq _ _
        _ = 4 * Zsqrtd.norm k := by rw [norm_two]
    have h6 : (4 : ℤ) * Zsqrtd.norm k = 6 := by linarith [norm_one_minus]
    omega

/-- ℤ[√-5] is NOT a UFD: 2 is irreducible but not prime. -/
theorem zsqrtneg5_not_ufd : ¬ UniqueFactorizationMonoid ZSqrtNeg5 := by
  intro hUFD
  haveI := hUFD
  exact two_not_prime (UniqueFactorizationMonoid.irreducible_iff_prime.mp two_irreducible)

-- ============================================================
-- Part IV: Structural Results
-- ============================================================

/-- In a UFD, irreducible elements are prime. -/
theorem irred_imp_prime_in_ufd {R : Type*} [CancelCommMonoidWithZero R]
    [UniqueFactorizationMonoid R] {p : R} (hp : Irreducible p) : Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp hp

/-- ℤ and ℤ[i] are Dedekind domains, PIDs, and UFDs. -/
example : IsDedekindDomain ℤ := inferInstance
example : IsPrincipalIdealRing ℤ := inferInstance
example : UniqueFactorizationMonoid ℤ := inferInstance
example : UniqueFactorizationMonoid GaussianInt := inferInstance

/-- The hierarchy: PID → Dedekind domain (and PID = UFD in the Dedekind setting). -/
theorem hierarchy {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    IsDedekindDomain R ∧ UniqueFactorizationMonoid R :=
  ⟨inferInstance, inferInstance⟩

/-- Summary: 2 is irreducible and not prime in ℤ[√-5], and 6 has two factorizations. -/
theorem zsqrtneg5_witness :
    Irreducible (2 : ZSqrtNeg5) ∧ ¬ Prime (2 : ZSqrtNeg5) ∧
    (2 : ZSqrtNeg5) * 3 = ⟨1, 1⟩ * ⟨1, -1⟩ :=
  ⟨two_irreducible, two_not_prime, two_factorizations_of_6⟩

end DedekindIdealFTA
