import Proofs.FourSquareDistribution
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

/-
# Jacobi's Four-Square Formula (OQ-01 of FourSquareDistribution)

## Open Question (Gallery OQ-01 of `four-square-distribution`)
"Can Jacobi's four-square formula r₄(n) = 8·∑_{4∤d|n} d be formally
proved in Lean 4?"

## What This Provides

This file is the **OBSERVE/ORIENT contribution** for OQ-01:

1. Defines Jacobi's modified divisor sum σ*(n) := Σ_{d|n, 4∤d} d.
2. Defines the brute-force enumeration r₄(n) over signed integer 4-tuples.
3. Proves the conjecture *numerically* for n = 1..10 via `native_decide`.
4. States Jacobi's formula as `axiom jacobi_r4_formula` — the precise open
   target whose general proof requires modular form theory.
5. Connects the small-case verification to the type-decomposition results
   in `FourSquareDistribution.lean` so that the same numerical content is
   independently checkable from two different combinatorial definitions.

## Mathematical Background

For each n ≥ 1, define
$$
  r_4(n) = \#\{(a,b,c,d) \in \mathbb{Z}^4 : a^2+b^2+c^2+d^2 = n\}
$$
$$
  \sigma^*(n) = \sum_{\substack{d \mid n \\ 4 \nmid d}} d.
$$
**Jacobi (1834)**: r₄(n) = 8·σ*(n) for all n ≥ 1.

The classical proof uses θ(q)⁴ where θ(q) = ∑_{k∈ℤ} q^{k²}. Jacobi shows
θ(q)⁴ is a weight-2 modular form of level 4 and identifies its
q-expansion with 1 + 8∑_{n≥1} σ*(n) q^n.

Mathlib infrastructure already present (as of 4.26.0, 2026-05):
* `Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable` — defines
  `jacobiTheta` on the upper half-plane, with the modular transformations
  `jacobiTheta_T_sq_smul` and `jacobiTheta_S_smul`.
* `Mathlib.NumberTheory.ModularForms.EisensteinSeries.*` — defines the
  Eisenstein series with bounded-at-cusp / modular invariance lemmas.
* `Mathlib.NumberTheory.SumFourSquares` — Lagrange's existence theorem.

What is **missing** for a full Lean proof:
* Fourier coefficients / q-expansion of `jacobiTheta`.
* Identification of `jacobiTheta^4` with a specific Eisenstein-series
  combination (e.g. E₂(τ) - 4·E₂(4τ), up to normalization).
* The arithmetic identity expressing the n-th Fourier coefficient as
  8·σ*(n).

## File Status
* axioms: 1 (`jacobi_r4_formula`)
* sorries: 0
* numerically verified: n = 1..10
-/

namespace FourSquareDistributionOQ01

open Finset Nat

-- =====================================================================
-- PART 1: Jacobi's modified divisor sum σ*(n)
-- =====================================================================

/-- Jacobi's modified divisor sum: σ*(n) = Σ_{d|n, 4∤d} d.

    Drops every divisor of n that is divisible by 4. The factor of 8
    in Jacobi's r₄ formula relates to this via 8 = 2³ and the
    sign/permutation symmetry group acting on a 4-tuple. -/
def sigmaStar (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if 4 ∣ d then 0 else d

-- σ*(n) values for n = 1..10:
theorem sigmaStar_1  : sigmaStar 1  = 1  := by native_decide
theorem sigmaStar_2  : sigmaStar 2  = 3  := by native_decide
theorem sigmaStar_3  : sigmaStar 3  = 4  := by native_decide
theorem sigmaStar_4  : sigmaStar 4  = 3  := by native_decide
theorem sigmaStar_5  : sigmaStar 5  = 6  := by native_decide
theorem sigmaStar_6  : sigmaStar 6  = 12 := by native_decide
theorem sigmaStar_7  : sigmaStar 7  = 8  := by native_decide
theorem sigmaStar_8  : sigmaStar 8  = 3  := by native_decide
theorem sigmaStar_9  : sigmaStar 9  = 13 := by native_decide
theorem sigmaStar_10 : sigmaStar 10 = 18 := by native_decide

/-- Jacobi's prediction: r₄(n) = 8·σ*(n). -/
def jacobiR4 (n : ℕ) : ℕ := 8 * sigmaStar n

theorem jacobiR4_1  : jacobiR4 1  = 8   := by native_decide
theorem jacobiR4_2  : jacobiR4 2  = 24  := by native_decide
theorem jacobiR4_3  : jacobiR4 3  = 32  := by native_decide
theorem jacobiR4_4  : jacobiR4 4  = 24  := by native_decide
theorem jacobiR4_5  : jacobiR4 5  = 48  := by native_decide
theorem jacobiR4_6  : jacobiR4 6  = 96  := by native_decide
theorem jacobiR4_7  : jacobiR4 7  = 64  := by native_decide
theorem jacobiR4_8  : jacobiR4 8  = 24  := by native_decide
theorem jacobiR4_9  : jacobiR4 9  = 104 := by native_decide
theorem jacobiR4_10 : jacobiR4 10 = 144 := by native_decide

-- =====================================================================
-- PART 2: Brute-force enumeration of integer 4-tuples
-- =====================================================================

/-- Bound a tuple component to [-n, n] via offset by n. -/
def shiftedRange (n : ℕ) : List ℤ :=
  (List.range (2 * n + 1)).map (fun k => (k : ℤ) - n)

/-- Brute-force count of integer 4-tuples (a, b, c, d) ∈ ℤ⁴ with
    a² + b² + c² + d² = n.

    Since a² ≤ n implies |a| ≤ √n ≤ n, enumerating each component over
    [-n, n] is correct (over-counts the bound but stays correct). -/
def r4Count (n : ℕ) : ℕ :=
  let R := shiftedRange n
  R.foldl (fun acc a =>
    R.foldl (fun acc b =>
      R.foldl (fun acc c =>
        R.foldl (fun acc d =>
          if a^2 + b^2 + c^2 + d^2 = (n : ℤ) then acc + 1 else acc)
          acc) acc) acc) 0

-- =====================================================================
-- PART 3: Numerical verification of Jacobi's formula for n = 1..10
-- =====================================================================

theorem r4Count_1  : r4Count 1  = 8   := by native_decide
theorem r4Count_2  : r4Count 2  = 24  := by native_decide
theorem r4Count_3  : r4Count 3  = 32  := by native_decide
theorem r4Count_4  : r4Count 4  = 24  := by native_decide
theorem r4Count_5  : r4Count 5  = 48  := by native_decide
theorem r4Count_6  : r4Count 6  = 96  := by native_decide
theorem r4Count_7  : r4Count 7  = 64  := by native_decide
theorem r4Count_8  : r4Count 8  = 24  := by native_decide
theorem r4Count_9  : r4Count 9  = 104 := by native_decide
theorem r4Count_10 : r4Count 10 = 144 := by native_decide

/-- The brute-force count agrees with Jacobi's prediction r₄(n) = 8 σ*(n)
    for n = 1..10. -/
theorem jacobi_holds_1  : r4Count 1  = jacobiR4 1  := by native_decide
theorem jacobi_holds_2  : r4Count 2  = jacobiR4 2  := by native_decide
theorem jacobi_holds_3  : r4Count 3  = jacobiR4 3  := by native_decide
theorem jacobi_holds_4  : r4Count 4  = jacobiR4 4  := by native_decide
theorem jacobi_holds_5  : r4Count 5  = jacobiR4 5  := by native_decide
theorem jacobi_holds_6  : r4Count 6  = jacobiR4 6  := by native_decide
theorem jacobi_holds_7  : r4Count 7  = jacobiR4 7  := by native_decide
theorem jacobi_holds_8  : r4Count 8  = jacobiR4 8  := by native_decide
theorem jacobi_holds_9  : r4Count 9  = jacobiR4 9  := by native_decide
theorem jacobi_holds_10 : r4Count 10 = jacobiR4 10 := by native_decide

-- =====================================================================
-- PART 4: Connection to the FourSquareDistribution type-decomposition
-- =====================================================================

open FourSquareDistribution

/-- The single-type cases (n = 1, 2, 3, 5, 6, 7) match Jacobi's prediction
    via the parent file's `distribution_complete_*`. -/
theorem distribution_matches_jacobi_1 : type_1_a.contribution = jacobiR4 1 := by
  rw [type_1_contribution, jacobiR4_1]
theorem distribution_matches_jacobi_2 : type_2_a.contribution = jacobiR4 2 := by
  rw [type_2_contribution, jacobiR4_2]
theorem distribution_matches_jacobi_3 : type_3_a.contribution = jacobiR4 3 := by
  rw [type_3_contribution, jacobiR4_3]
theorem distribution_matches_jacobi_5 : type_5_a.contribution = jacobiR4 5 := by
  rw [type_5_contribution, jacobiR4_5]
theorem distribution_matches_jacobi_6 : type_6_a.contribution = jacobiR4 6 := by
  rw [type_6_contribution, jacobiR4_6]
theorem distribution_matches_jacobi_7 : type_7_a.contribution = jacobiR4 7 := by
  rw [type_7_contribution, jacobiR4_7]

/-- The multi-type cases (n = 4, 9, 10) match Jacobi's prediction via the
    parent file's two-type decomposition theorems. -/
theorem distribution_matches_jacobi_4 :
    type_4_a.contribution + type_4_b.contribution = jacobiR4 4 := by
  rw [r₄_4_distribution, jacobiR4_4]
theorem distribution_matches_jacobi_9 :
    type_9_a.contribution + type_9_b.contribution = jacobiR4 9 := by
  rw [r₄_9_distribution, jacobiR4_9]
theorem distribution_matches_jacobi_10 :
    type_10_a.contribution + type_10_b.contribution = jacobiR4 10 := by
  rw [r₄_10_distribution, jacobiR4_10]

-- =====================================================================
-- PART 5: Jacobi's general theorem (open conjecture, axiomatized)
-- =====================================================================

/-- **Jacobi's Four-Square Theorem** (Jacobi 1834).

    For every n ≥ 1, the count of integer 4-tuples (a, b, c, d) summing
    to n in squares equals 8·σ*(n):
    $$ r_4(n) = 8 \sum_{\substack{d \mid n \\ 4 \nmid d}} d. $$

    **Status**: Numerically verified above for n = 1..10. The general
    proof requires modular form theory not yet in Mathlib (specifically:
    Fourier coefficients of `jacobiTheta`, identification of θ⁴ with
    weight-2 Eisenstein series E₂(τ) - 4 E₂(4τ), up to constants). -/
axiom jacobi_r4_formula :
    ∀ n : ℕ, 0 < n → r4Count n = jacobiR4 n

/-- The boundary case n = 0: only the all-zero tuple contributes. -/
theorem r4Count_zero : r4Count 0 = 1 := by native_decide

/-- σ*(0) = 0 (the divisors of 0 are empty in Mathlib). -/
theorem sigmaStar_zero : sigmaStar 0 = 0 := by native_decide

-- =====================================================================
-- PART 6: Structural lemmas — connecting σ*(n) to the standard divisor
-- sum σ(n) := Σ_{d|n} d. These are honest (axiom-free) reductions of
-- the arithmetic content of σ*. They eliminate the need to reason
-- directly about the indicator `4 ∣ d` and let future work apply
-- Mathlib's σ machinery (e.g. `ArithmeticFunction.sigma`) to σ*.
-- =====================================================================

/-- Standard divisor sum σ(n) := Σ_{d|n} d.

    Equivalent to `(ArithmeticFunction.sigma 1) n` from Mathlib via
    `ArithmeticFunction.sigma_one_apply`, but defined locally to avoid
    the heavy ArithmeticFunction wrapper for these small structural
    lemmas. -/
def sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

theorem sigmaOne_zero : sigmaOne 0 = 0 := by
  unfold sigmaOne; simp

theorem sigmaOne_one : sigmaOne 1 = 1 := by
  unfold sigmaOne; decide

/-- Complement of σ*: sum over divisors of n that ARE divisible by 4.
    Together with σ*, partitions the standard divisor sum:
    σ*(n) + sigmaFourDvd(n) = σ(n). -/
def sigmaFourDvd (n : ℕ) : ℕ := ∑ d ∈ n.divisors, if 4 ∣ d then d else 0

/-- Partition identity: σ* and sigmaFourDvd jointly cover σ.
    σ*(n) + (sum over 4-divisible divisors) = σ(n). -/
theorem sigmaStar_add_sigmaFourDvd (n : ℕ) :
    sigmaStar n + sigmaFourDvd n = sigmaOne n := by
  unfold sigmaStar sigmaFourDvd sigmaOne
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intros d _
  split_ifs with h <;> simp

/-- For n with 4 ∤ n, every divisor d of n satisfies 4 ∤ d (because
    4 ∣ d would imply 4 ∣ n). Hence σ*(n) = σ(n). -/
theorem sigmaStar_eq_sigmaOne_of_not_four_dvd {n : ℕ} (hn : ¬ 4 ∣ n) :
    sigmaStar n = sigmaOne n := by
  unfold sigmaStar sigmaOne
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Nat.mem_divisors] at hd
  have h4 : ¬ 4 ∣ d := fun h4d => hn (h4d.trans hd.1)
  simp [h4]

/-- Specialization: for odd n, σ*(n) = σ(n). -/
theorem sigmaStar_eq_sigmaOne_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) :
    sigmaStar n = sigmaOne n :=
  sigmaStar_eq_sigmaOne_of_not_four_dvd
    (fun h4 => hn (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4))

/-- Bijection lemma: when 4 ∣ n, the divisors of n divisible by 4 are
    in bijection with divisors of n/4 via e ↔ 4·e. -/
theorem divisors_filter_four_dvd_eq_image {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) :
    n.divisors.filter (4 ∣ ·) = (n / 4).divisors.image (fun e => 4 * e) := by
  obtain ⟨k, hk⟩ := h4
  have hk_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk'
    · simp [hk] at hn
    · exact hk'
  have hnk : n / 4 = k := by rw [hk]; exact Nat.mul_div_cancel_left k (by norm_num)
  ext d
  rw [Finset.mem_filter, Finset.mem_image, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, _hn0⟩, hd4⟩
    obtain ⟨e, rfl⟩ := hd4
    refine ⟨e, ?_, rfl⟩
    rw [Nat.mem_divisors, hnk]
    refine ⟨?_, hk_pos.ne'⟩
    rw [hk] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0:ℕ) < 4)).mp hdvd
  · rintro ⟨e, he, rfl⟩
    rw [Nat.mem_divisors, hnk] at he
    refine ⟨⟨?_, hn.ne'⟩, ⟨e, rfl⟩⟩
    obtain ⟨m, hm⟩ := he.1
    refine ⟨m, ?_⟩
    rw [hk, hm]; ring

/-- When 4 ∣ n, the sum over 4-divisible divisors of n equals 4·σ(n/4).
    Proof: each such divisor is 4·e for a unique e | (n/4), and
    Σ_{e | (n/4)} 4·e = 4·σ(n/4). -/
theorem sigmaFourDvd_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) :
    sigmaFourDvd n = 4 * sigmaOne (n / 4) := by
  unfold sigmaFourDvd sigmaOne
  rw [Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero,
      divisors_filter_four_dvd_eq_image h4 hn]
  exact Finset.sum_image (fun e₁ _ e₂ _ h => by omega)

/-- **Structural identity** — main contribution of this session.

    For every n with 4 ∣ n,
        σ*(n) + 4·σ(n/4) = σ(n),
    i.e., σ*(n) is exactly σ(n) minus 4·σ(n/4) — the contribution from
    those divisors of n that are themselves divisible by 4. Combined
    with `sigmaStar_eq_sigmaOne_of_not_four_dvd` (the case 4 ∤ n), this
    gives a complete reformulation of σ* in terms of Mathlib's standard
    divisor sum:

        σ*(n) = σ(n)              if 4 ∤ n,
        σ*(n) = σ(n) − 4·σ(n/4)   if 4 ∣ n.

    This is a real reduction of Jacobi's formula:
    once Mathlib gains the q-expansion machinery for `jacobiTheta`, the
    target identity `r₄(n) = 8·σ*(n)` decomposes into two case-statements
    in σ — a function for which Mathlib already has multiplicativity
    (`Nat.Coprime.sum_divisors_mul`), prime-power closed forms, and
    Eisenstein-series identities. -/
theorem sigmaStar_of_four_dvd {n : ℕ} (h4 : 4 ∣ n) (hn : 0 < n) :
    sigmaStar n + 4 * sigmaOne (n / 4) = sigmaOne n := by
  rw [← sigmaFourDvd_of_four_dvd h4 hn, sigmaStar_add_sigmaFourDvd]

-- =====================================================================
-- PART 7: Cross-validation of the structural identity for small n
-- =====================================================================

theorem sigmaOne_1  : sigmaOne 1  = 1   := by native_decide
theorem sigmaOne_2  : sigmaOne 2  = 3   := by native_decide
theorem sigmaOne_4  : sigmaOne 4  = 7   := by native_decide
theorem sigmaOne_8  : sigmaOne 8  = 15  := by native_decide
theorem sigmaOne_12 : sigmaOne 12 = 28  := by native_decide
theorem sigmaOne_16 : sigmaOne 16 = 31  := by native_decide

/-- Cross-check: σ*(4) + 4·σ(1) = σ(4), i.e. 3 + 4·1 = 7. -/
example : sigmaStar 4 + 4 * sigmaOne 1 = sigmaOne 4 :=
  sigmaStar_of_four_dvd (by decide) (by decide)

/-- Cross-check: σ*(8) + 4·σ(2) = σ(8), i.e. 3 + 4·3 = 15. -/
example : sigmaStar 8 + 4 * sigmaOne 2 = sigmaOne 8 :=
  sigmaStar_of_four_dvd (by decide) (by decide)

/-- Cross-check: σ*(12) + 4·σ(3) = σ(12), i.e. 12 + 4·4 = 28. -/
example : sigmaStar 12 + 4 * sigmaOne 3 = sigmaOne 12 :=
  sigmaStar_of_four_dvd (by decide) (by decide)

/-- Cross-check: σ*(16) + 4·σ(4) = σ(16), i.e. 3 + 4·7 = 31. -/
example : sigmaStar 16 + 4 * sigmaOne 4 = sigmaOne 16 :=
  sigmaStar_of_four_dvd (by decide) (by decide)

/-- Cross-check (odd n): σ*(15) = σ(15). -/
example : sigmaStar 15 = sigmaOne 15 :=
  sigmaStar_eq_sigmaOne_of_odd (by decide)

-- =====================================================================
-- PART 8: σ* on odd prime powers
--
-- For an odd prime p, no power p^k is divisible by 4 (since 4 = 2^2 and
-- 2 ∤ p when p ≠ 2). So σ*(p^k) collapses to the standard divisor sum
-- σ(p^k), which Mathlib provides via `sigma_one_apply_prime_pow`. This
-- is the σ*-side preparation needed once Mathlib gains q-expansion
-- machinery: r₄(p^k) = 8·σ*(p^k) will then reduce, for odd primes, to
-- a statement purely about σ — for which Mathlib already provides
-- multiplicativity and prime-power closed forms.
-- =====================================================================

/-- For p prime and p ≠ 2, no power p^k is divisible by 4.

    Proof: 4 = 2² | p^k ⇒ 2 | p^k ⇒ 2 | p (since 2 is prime, by
    `Nat.Prime.dvd_of_dvd_pow`) ⇒ p = 2 (since p prime) ⇒ contradiction. -/
theorem not_four_dvd_prime_pow_of_ne_two {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (k : ℕ) :
    ¬ 4 ∣ p ^ k := by
  intro h4
  have h2_dvd_pk : (2 : ℕ) ∣ p ^ k :=
    dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4
  have h2_dvd_p : (2 : ℕ) ∣ p :=
    Nat.prime_two.dvd_of_dvd_pow h2_dvd_pk
  rcases hp.eq_one_or_self_of_dvd 2 h2_dvd_p with h | h
  · exact absurd h (by decide)
  · exact h2 h.symm

/-- For an odd prime p, σ*(p^k) = σ(p^k).

    No divisor of p^k is divisible by 4, so the indicator `4 ∤ d` in
    σ*'s definition is always true on `(p^k).divisors` and σ* collapses
    to σ. Combined with `Nat.sigma_one_apply_prime_pow`, this gives the
    closed form σ*(p^k) = 1 + p + p^2 + ... + p^k for odd prime p. -/
theorem sigmaStar_prime_pow_of_odd_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (k : ℕ) :
    sigmaStar (p ^ k) = sigmaOne (p ^ k) :=
  sigmaStar_eq_sigmaOne_of_not_four_dvd (not_four_dvd_prime_pow_of_ne_two hp h2 k)

/-- Cross-check on p = 3, k = 2: σ*(9) = σ(9) = 1 + 3 + 9 = 13. -/
example : sigmaStar (3 ^ 2) = sigmaOne (3 ^ 2) :=
  sigmaStar_prime_pow_of_odd_prime (by decide) (by decide) 2

/-- Cross-check on p = 5, k = 1: σ*(5) = σ(5) = 1 + 5 = 6. -/
example : sigmaStar (5 ^ 1) = sigmaOne (5 ^ 1) :=
  sigmaStar_prime_pow_of_odd_prime (by decide) (by decide) 1

/-- Cross-check on p = 7, k = 0: σ*(1) = σ(1) = 1 (vacuous case). -/
example : sigmaStar (7 ^ 0) = sigmaOne (7 ^ 0) :=
  sigmaStar_prime_pow_of_odd_prime (by decide) (by decide) 0

-- =====================================================================
-- PART 9: σ* on doubled odd numbers — σ*(2n) = 3·σ(n) for n odd.
--
-- This is the cleanest non-trivial structural identity for σ*. It
-- exhibits σ* as a "twisted multiplicative" function: σ*(2 · n) factors
-- as σ*(2) · σ*(n) = 3 · σ(n) when n is odd, paralleling Mathlib's
-- general multiplicativity for σ at coprime arguments. It also explains
-- a numerical pattern in Jacobi's data: σ*(2) = σ*(4) = σ*(8) = 3, and
-- more generally σ*(2^k · m) = 3 · σ(m) for k ≥ 1, m odd (proven for
-- k = 1, 2 below).
-- =====================================================================

/-- For n odd with n > 0, the divisors of 2n partition into
    `n.divisors` (the odd divisors of 2n) and `n.divisors.image (· * 2)`
    (the even divisors of 2n, all of the form 2·d with d | n).

    Note: this set equality actually holds for any n > 0 (even or odd),
    but the *partition* / disjointness is what requires oddness — see
    `disjoint_divisors_image_two_of_odd`. -/
theorem divisors_two_mul_of_odd {n : ℕ} (_hn : ¬ 2 ∣ n) (hpos : 0 < n) :
    (2 * n).divisors = n.divisors ∪ n.divisors.image (fun e => 2 * e) := by
  have h2n_ne : 2 * n ≠ 0 := by positivity
  ext d
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
  refine ⟨?_, ?_⟩
  · rintro ⟨hdvd, _⟩
    by_cases hd2 : 2 ∣ d
    · obtain ⟨e, rfl⟩ := hd2
      right
      refine ⟨e, ⟨?_, hpos.ne'⟩, by ring⟩
      exact (Nat.mul_dvd_mul_iff_left (show 0 < 2 by decide)).mp hdvd
    · left
      refine ⟨?_, hpos.ne'⟩
      have hcop : Nat.Coprime d 2 :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hd2).symm
      exact hcop.dvd_of_dvd_mul_left hdvd
  · rintro (⟨hd, _⟩ | ⟨e, ⟨he, _⟩, rfl⟩)
    · exact ⟨hd.mul_left 2, h2n_ne⟩
    · exact ⟨Nat.mul_dvd_mul_left 2 he, h2n_ne⟩

/-- Disjointness of the two pieces in `divisors_two_mul_of_odd`: an odd
    n has only odd divisors, so `n.divisors` and `n.divisors.image (· * 2)`
    cannot overlap. -/
theorem disjoint_divisors_image_two_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) :
    Disjoint n.divisors (n.divisors.image (fun e => 2 * e)) := by
  rw [Finset.disjoint_left]
  intro d hd hd'
  rw [Nat.mem_divisors] at hd
  rw [Finset.mem_image] at hd'
  obtain ⟨e, _, rfl⟩ := hd'
  exact hn (dvd_trans ⟨e, rfl⟩ hd.1)

/-- Multiplicativity of σ at (2, n) for n odd: σ(2n) = 3·σ(n).

    Proof: partition (2n).divisors as in `divisors_two_mul_of_odd` and
    sum each piece. The odd-divisor sum is σ(n); the even-divisor sum
    is 2·σ(n) by the image bijection e ↦ 2e (injective on n.divisors). -/
theorem sigmaOne_two_mul_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) (hpos : 0 < n) :
    sigmaOne (2 * n) = 3 * sigmaOne n := by
  unfold sigmaOne
  rw [divisors_two_mul_of_odd hn hpos,
      Finset.sum_union (disjoint_divisors_image_two_of_odd hn)]
  rw [Finset.sum_image (fun e₁ _ e₂ _ h => by omega)]
  rw [← Finset.mul_sum]
  ring

/-- **σ*-multiplicativity at (2, n) for n odd**: σ*(2n) = 3·σ(n).

    Proof: 4 ∤ 2n when n is odd, so σ*(2n) = σ(2n) by
    `sigmaStar_eq_sigmaOne_of_not_four_dvd`; then σ(2n) = 3·σ(n) by
    `sigmaOne_two_mul_of_odd`. Combined with `sigmaStar_eq_sigmaOne_of_odd`
    (which gives σ*(n) = σ(n) for odd n), this also says
    σ*(2n) = 3·σ*(n) for n odd — a clean multiplicativity statement. -/
theorem sigmaStar_two_mul_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) (hpos : 0 < n) :
    sigmaStar (2 * n) = 3 * sigmaOne n := by
  have h4 : ¬ 4 ∣ (2 * n) := by
    intro h
    obtain ⟨k, hk⟩ := h
    exact hn ⟨k, by linarith⟩
  rw [sigmaStar_eq_sigmaOne_of_not_four_dvd h4, sigmaOne_two_mul_of_odd hn hpos]

/-- σ(4n) = 7·σ(n) for n odd: by partitioning (4n).divisors into three
    pieces by 2-adic valuation 0, 1, 2 (i.e., d, 2d, 4d for d | n). -/
theorem sigmaOne_four_mul_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) (hpos : 0 < n) :
    sigmaOne (4 * n) = 7 * sigmaOne n := by
  have h4n_pos : 0 < 4 * n := by positivity
  have h4n_ne : 4 * n ≠ 0 := h4n_pos.ne'
  have hSet : (4 * n).divisors =
      n.divisors ∪
      (n.divisors.image (fun e => 2 * e) ∪ n.divisors.image (fun e => 4 * e)) := by
    ext d
    simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors]
    refine ⟨?_, ?_⟩
    · rintro ⟨hdvd, _⟩
      by_cases hd2 : 2 ∣ d
      · obtain ⟨e, rfl⟩ := hd2
        by_cases he2 : 2 ∣ e
        · obtain ⟨f, rfl⟩ := he2
          right; right
          refine ⟨f, ⟨?_, hpos.ne'⟩, by ring⟩
          have h4f : 4 * f ∣ 4 * n := by
            have hh : 2 * (2 * f) ∣ 4 * n := hdvd
            have : 4 * f = 2 * (2 * f) := by ring
            rw [this]; exact hh
          exact (Nat.mul_dvd_mul_iff_left (show 0 < 4 by decide)).mp h4f
        · right; left
          refine ⟨e, ⟨?_, hpos.ne'⟩, rfl⟩
          have h2e_dvd_2_2n : 2 * e ∣ 2 * (2 * n) := by
            have : 2 * (2 * n) = 4 * n := by ring
            rw [this]; exact hdvd
          have he_dvd_2n : e ∣ 2 * n :=
            (Nat.mul_dvd_mul_iff_left (show 0 < 2 by decide)).mp h2e_dvd_2_2n
          have hcop : Nat.Coprime e 2 :=
            ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr he2).symm
          exact hcop.dvd_of_dvd_mul_left he_dvd_2n
      · left
        refine ⟨?_, hpos.ne'⟩
        have hcop2 : Nat.Coprime d 2 :=
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hd2).symm
        have hcop4 : Nat.Coprime d 4 := by
          have h22 : (4 : ℕ) = 2 * 2 := by decide
          rw [h22]
          exact hcop2.mul_right hcop2
        exact hcop4.dvd_of_dvd_mul_left hdvd
    · rintro (⟨hd, _⟩ | (⟨e, ⟨he, _⟩, rfl⟩ | ⟨e, ⟨he, _⟩, rfl⟩))
      · exact ⟨dvd_mul_of_dvd_right hd 4, h4n_ne⟩
      · refine ⟨?_, h4n_ne⟩
        have h4n_eq : 4 * n = 2 * (2 * n) := by ring
        rw [h4n_eq]
        exact Nat.mul_dvd_mul_left 2 (dvd_mul_of_dvd_right he 2)
      · exact ⟨Nat.mul_dvd_mul_left 4 he, h4n_ne⟩
  have hd01 : Disjoint n.divisors (n.divisors.image (fun e => 2 * e)) :=
    disjoint_divisors_image_two_of_odd hn
  have hd02 : Disjoint n.divisors (n.divisors.image (fun e => 4 * e)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    rw [Nat.mem_divisors] at hd
    rw [Finset.mem_image] at hd'
    obtain ⟨e, _, rfl⟩ := hd'
    exact hn (dvd_trans ⟨2 * e, by ring⟩ hd.1)
  have hd12 : Disjoint (n.divisors.image (fun e => 2 * e))
                       (n.divisors.image (fun e => 4 * e)) := by
    rw [Finset.disjoint_left]
    intro d hd hd'
    rw [Finset.mem_image] at hd hd'
    obtain ⟨e₁, he₁, rfl⟩ := hd
    obtain ⟨e₂, he₂, he12⟩ := hd'
    have heq : e₁ = 2 * e₂ := by linarith
    rw [Nat.mem_divisors] at he₁
    exact hn (dvd_trans ⟨e₂, heq⟩ he₁.1)
  have hd_union : Disjoint n.divisors
      (n.divisors.image (fun e => 2 * e) ∪ n.divisors.image (fun e => 4 * e)) :=
    Finset.disjoint_union_right.mpr ⟨hd01, hd02⟩
  unfold sigmaOne
  rw [hSet, Finset.sum_union hd_union, Finset.sum_union hd12]
  rw [Finset.sum_image (fun e₁ _ e₂ _ h => by omega)]
  rw [Finset.sum_image (fun e₁ _ e₂ _ h => by omega)]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- **σ*(4n) = 3·σ(n) for n odd** — same factor of 3 as σ*(2n).

    This proves the k = 2 case of the general pattern σ*(2^k m) = 3·σ(m)
    for k ≥ 1, m odd: the power of 2 contributes the same factor 3 = σ*(2)
    independent of how high (≥ 1). Proof: combine `sigmaStar_of_four_dvd`
    (σ*(4n) + 4·σ(n) = σ(4n)) with `sigmaOne_four_mul_of_odd`
    (σ(4n) = 7·σ(n)). -/
theorem sigmaStar_four_mul_of_odd {n : ℕ} (hn : ¬ 2 ∣ n) (hpos : 0 < n) :
    sigmaStar (4 * n) = 3 * sigmaOne n := by
  have h4 : 4 ∣ (4 * n) := ⟨n, rfl⟩
  have h4n_pos : 0 < 4 * n := by positivity
  have hdiv : (4 * n) / 4 = n :=
    Nat.mul_div_cancel_left _ (by norm_num : (0:ℕ) < 4)
  have hbase : sigmaStar (4 * n) + 4 * sigmaOne ((4 * n) / 4) = sigmaOne (4 * n) :=
    sigmaStar_of_four_dvd h4 h4n_pos
  rw [hdiv] at hbase
  rw [sigmaOne_four_mul_of_odd hn hpos] at hbase
  omega

-- =====================================================================
-- PART 10: Cross-validation of σ*(2n) = 3·σ(n) and σ*(4n) = 3·σ(n).
-- =====================================================================

/-- Cross-check: σ*(2·1) = 3·σ(1) — i.e., σ*(2) = 3. -/
example : sigmaStar (2 * 1) = 3 * sigmaOne 1 :=
  sigmaStar_two_mul_of_odd (by decide) (by decide)

/-- Cross-check: σ*(2·3) = 3·σ(3) — i.e., σ*(6) = 12. -/
example : sigmaStar (2 * 3) = 3 * sigmaOne 3 :=
  sigmaStar_two_mul_of_odd (by decide) (by decide)

/-- Cross-check: σ*(2·5) = 3·σ(5) — i.e., σ*(10) = 18. -/
example : sigmaStar (2 * 5) = 3 * sigmaOne 5 :=
  sigmaStar_two_mul_of_odd (by decide) (by decide)

/-- Cross-check: σ*(2·9) = 3·σ(9) — i.e., σ*(18) = 39. -/
example : sigmaStar (2 * 9) = 3 * sigmaOne 9 :=
  sigmaStar_two_mul_of_odd (by decide) (by decide)

/-- Cross-check: σ*(4·1) = 3·σ(1) — i.e., σ*(4) = 3. -/
example : sigmaStar (4 * 1) = 3 * sigmaOne 1 :=
  sigmaStar_four_mul_of_odd (by decide) (by decide)

/-- Cross-check: σ*(4·3) = 3·σ(3) — i.e., σ*(12) = 12. -/
example : sigmaStar (4 * 3) = 3 * sigmaOne 3 :=
  sigmaStar_four_mul_of_odd (by decide) (by decide)

/-- Cross-check: σ*(4·5) = 3·σ(5) — i.e., σ*(20) = 18. -/
example : sigmaStar (4 * 5) = 3 * sigmaOne 5 :=
  sigmaStar_four_mul_of_odd (by decide) (by decide)

-- =====================================================================
-- PART 11: σ-multiplicativity at coprime arguments via Mathlib bridge.
-- =====================================================================

/-- Bridge: our locally-defined `sigmaOne` equals Mathlib's
    `ArithmeticFunction.sigma 1`. -/
theorem sigmaOne_eq_arithmeticSigmaOne (n : ℕ) :
    sigmaOne n = ArithmeticFunction.sigma 1 n := by
  simp [sigmaOne, ArithmeticFunction.sigma_apply, pow_one]

/-- σ-multiplicativity at coprime arguments: σ(mn) = σ(m)·σ(n) when
    `gcd(m, n) = 1`. Pulled back through the Mathlib bridge. -/
theorem sigmaOne_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigmaOne (m * n) = sigmaOne m * sigmaOne n := by
  rw [sigmaOne_eq_arithmeticSigmaOne, sigmaOne_eq_arithmeticSigmaOne,
      sigmaOne_eq_arithmeticSigmaOne]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h

-- =====================================================================
-- PART 12: σ*-multiplicativity at coprime arguments.
--
-- **Goal**: σ*(mn) = σ*(m)·σ*(n) whenever gcd(m,n) = 1, m, n > 0.
--
-- This is the high-value structural property of Jacobi's σ*: combined
-- with closed forms for σ* on prime powers (`sigmaStar_prime_pow_of_odd_prime`
-- in Part 8 and `sigmaStar_two_pow` in Part 13), it reduces the open
-- Jacobi target r₄(n) = 8·σ*(n) to a prime-power calculation.
--
-- Proof strategy: case split on `4 ∣ m` vs `4 ∣ n`, which by coprimality
-- cannot both hold. When neither holds, σ* = σ on each side and σ-mult
-- closes the goal. When one (say m) is divisible by 4, the structural
-- identity from Part 6 expresses σ*(·) as σ(·) − 4·σ(·/4) on m and on
-- mn; σ-mult on each piece + algebra closes the goal.
-- =====================================================================

private theorem not_two_dvd_of_coprime_two_dvd_left {m n : ℕ}
    (h : Nat.Coprime m n) (h2m : 2 ∣ m) : ¬ 2 ∣ n := by
  intro h2n
  have hgcd : (2 : ℕ) ∣ Nat.gcd m n := Nat.dvd_gcd h2m h2n
  rw [Nat.Coprime] at h
  rw [h] at hgcd
  exact absurd hgcd (by decide)

private theorem coprime_four_of_not_two_dvd {n : ℕ} (hn : ¬ 2 ∣ n) :
    Nat.Coprime 4 n := by
  have hc2 : Nat.Coprime 2 n :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hn
  have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4eq]
  exact hc2.pow_left 2

private theorem not_four_dvd_mul_of_coprime
    {m n : ℕ} (h : Nat.Coprime m n) (h4m : ¬ 4 ∣ m) (h4n : ¬ 4 ∣ n) :
    ¬ 4 ∣ m * n := by
  intro h4mn
  by_cases h2m : 2 ∣ m
  · have h2n : ¬ 2 ∣ n := not_two_dvd_of_coprime_two_dvd_left h h2m
    have hcop4n : Nat.Coprime 4 n := coprime_four_of_not_two_dvd h2n
    exact h4m (hcop4n.dvd_of_dvd_mul_right h4mn)
  · by_cases h2n : 2 ∣ n
    · have hcop4m : Nat.Coprime 4 m := coprime_four_of_not_two_dvd h2m
      exact h4n (hcop4m.dvd_of_dvd_mul_left h4mn)
    · have h2mn : ¬ 2 ∣ m * n := by
        intro h2mn'
        rcases Nat.prime_two.dvd_mul.mp h2mn' with h | h
        · exact h2m h
        · exact h2n h
      exact h2mn (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4mn)

private theorem coprime_div_four_of_dvd_left
    {m n : ℕ} (h : Nat.Coprime m n) (h4m : 4 ∣ m) :
    Nat.Coprime (m / 4) n :=
  h.coprime_dvd_left (Nat.div_dvd_of_dvd h4m)

private theorem coprime_div_four_of_dvd_right
    {m n : ℕ} (h : Nat.Coprime m n) (h4n : 4 ∣ n) :
    Nat.Coprime m (n / 4) :=
  h.coprime_dvd_right (Nat.div_dvd_of_dvd h4n)

/-- **σ*-multiplicativity at coprime arguments** (main theorem of S4).

    For all positive `m, n` with `gcd(m, n) = 1`:
    $$ \sigma^*(m \cdot n) = \sigma^*(m) \cdot \sigma^*(n). $$

    Together with the closed forms σ*(p^k) on prime powers (Part 8 for
    odd `p`, Part 13 for `p = 2`), this fully determines σ* by its
    values on prime-power arguments, mirroring the standard
    multiplicative theory of σ in Mathlib's
    `ArithmeticFunction.IsMultiplicative.sigma`. -/
theorem sigmaStar_mul_of_coprime {m n : ℕ}
    (h : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  by_cases h4m : 4 ∣ m
  · -- Case A: 4 ∣ m. Coprimality ⇒ 2 ∤ n ⇒ 4 ∤ n; also 4 ∣ mn.
    have h2m : (2 : ℕ) ∣ m := dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4m
    have h2n : ¬ 2 ∣ n := not_two_dvd_of_coprime_two_dvd_left h h2m
    have h4n : ¬ 4 ∣ n := fun h4n_dvd =>
      h2n (dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4n_dvd)
    have h4mn : 4 ∣ m * n := h4m.mul_right n
    have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
    have struct_m : sigmaStar m + 4 * sigmaOne (m / 4) = sigmaOne m :=
      sigmaStar_of_four_dvd h4m hm
    have struct_mn :
        sigmaStar (m * n) + 4 * sigmaOne ((m * n) / 4) = sigmaOne (m * n) :=
      sigmaStar_of_four_dvd h4mn hmn_pos
    have h_mn_div4 : (m * n) / 4 = (m / 4) * n := by
      rw [mul_comm m n, Nat.mul_div_assoc n h4m, mul_comm]
    have h_cop_div : Nat.Coprime (m / 4) n :=
      coprime_div_four_of_dvd_left h h4m
    have h_mult : sigmaOne (m * n) = sigmaOne m * sigmaOne n :=
      sigmaOne_mul_of_coprime h
    have h_mult_div : sigmaOne ((m / 4) * n) = sigmaOne (m / 4) * sigmaOne n :=
      sigmaOne_mul_of_coprime h_cop_div
    have h_n_eq : sigmaStar n = sigmaOne n :=
      sigmaStar_eq_sigmaOne_of_not_four_dvd h4n
    rw [h_n_eq]
    have struct_mn' :
        sigmaStar (m * n) + 4 * sigmaOne (m / 4) * sigmaOne n
          = sigmaOne m * sigmaOne n := by
      have hh := struct_mn
      rw [h_mn_div4, h_mult_div, h_mult] at hh
      linarith [hh, mul_assoc (4 : ℕ) (sigmaOne (m / 4)) (sigmaOne n)]
    have h1 :
        sigmaStar m * sigmaOne n + 4 * sigmaOne (m / 4) * sigmaOne n
          = sigmaOne m * sigmaOne n := by
      calc sigmaStar m * sigmaOne n + 4 * sigmaOne (m / 4) * sigmaOne n
          = (sigmaStar m + 4 * sigmaOne (m / 4)) * sigmaOne n := by ring
        _ = sigmaOne m * sigmaOne n := by rw [struct_m]
    have hkey : sigmaStar (m * n) + 4 * sigmaOne (m / 4) * sigmaOne n
              = sigmaStar m * sigmaOne n + 4 * sigmaOne (m / 4) * sigmaOne n :=
      struct_mn'.trans h1.symm
    exact Nat.add_right_cancel hkey
  · by_cases h4n : 4 ∣ n
    · -- Case B: 4 ∤ m, 4 ∣ n. Symmetric.
      have h2n : (2 : ℕ) ∣ n := dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4n
      have h2m : ¬ 2 ∣ m := not_two_dvd_of_coprime_two_dvd_left h.symm h2n
      have h4mn : 4 ∣ m * n := h4n.mul_left m
      have hmn_pos : 0 < m * n := Nat.mul_pos hm hn
      have struct_n : sigmaStar n + 4 * sigmaOne (n / 4) = sigmaOne n :=
        sigmaStar_of_four_dvd h4n hn
      have struct_mn :
          sigmaStar (m * n) + 4 * sigmaOne ((m * n) / 4) = sigmaOne (m * n) :=
        sigmaStar_of_four_dvd h4mn hmn_pos
      have h_mn_div4 : (m * n) / 4 = m * (n / 4) :=
        Nat.mul_div_assoc m h4n
      have h_cop_div : Nat.Coprime m (n / 4) :=
        coprime_div_four_of_dvd_right h h4n
      have h_mult : sigmaOne (m * n) = sigmaOne m * sigmaOne n :=
        sigmaOne_mul_of_coprime h
      have h_mult_div : sigmaOne (m * (n / 4)) = sigmaOne m * sigmaOne (n / 4) :=
        sigmaOne_mul_of_coprime h_cop_div
      have h_m_eq : sigmaStar m = sigmaOne m :=
        sigmaStar_eq_sigmaOne_of_not_four_dvd h4m
      rw [h_m_eq]
      have struct_mn' :
          sigmaStar (m * n) + 4 * sigmaOne m * sigmaOne (n / 4)
            = sigmaOne m * sigmaOne n := by
        have hh := struct_mn
        rw [h_mn_div4, h_mult_div, h_mult] at hh
        linarith [hh, mul_assoc (4 : ℕ) (sigmaOne m) (sigmaOne (n / 4))]
      have h1 :
          sigmaOne m * sigmaStar n + 4 * sigmaOne m * sigmaOne (n / 4)
            = sigmaOne m * sigmaOne n := by
        calc sigmaOne m * sigmaStar n + 4 * sigmaOne m * sigmaOne (n / 4)
            = sigmaOne m * (sigmaStar n + 4 * sigmaOne (n / 4)) := by ring
          _ = sigmaOne m * sigmaOne n := by rw [struct_n]
      have hkey :
          sigmaStar (m * n) + 4 * sigmaOne m * sigmaOne (n / 4)
            = sigmaOne m * sigmaStar n + 4 * sigmaOne m * sigmaOne (n / 4) :=
        struct_mn'.trans h1.symm
      exact Nat.add_right_cancel hkey
    · -- Case C: neither 4 ∣ m nor 4 ∣ n. Then 4 ∤ mn, so σ* = σ throughout.
      have h4mn : ¬ 4 ∣ m * n := not_four_dvd_mul_of_coprime h h4m h4n
      rw [sigmaStar_eq_sigmaOne_of_not_four_dvd h4mn,
          sigmaStar_eq_sigmaOne_of_not_four_dvd h4m,
          sigmaStar_eq_sigmaOne_of_not_four_dvd h4n]
      exact sigmaOne_mul_of_coprime h

-- =====================================================================
-- PART 13: σ* on pure powers of 2 — closed form σ*(2^k) = 3 for k ≥ 1.
--
-- The divisors of 2^k are {1, 2, 4, ..., 2^k}. Of these, only 1 and 2
-- are not divisible by 4 (for k ≥ 1). So σ*(2^k) = 1 + 2 = 3 for any
-- k ≥ 1, and σ*(2^0) = σ*(1) = 1.
-- =====================================================================

/-- Geometric series sum on ℕ: ∑_{i=0}^{j} 2^i = 2^{j+1} - 1. -/
private theorem sum_two_pow_eq (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (2 : ℕ) ^ i = 2 ^ (j + 1) - 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have hpow_pos : 1 ≤ (2 : ℕ) ^ (j + 1) := Nat.one_le_pow _ _ (by decide)
    omega

/-- σ(2^k) = 2^(k+1) - 1, the closed form for σ on a 2-power argument. -/
private theorem sigmaOne_two_pow (k : ℕ) : sigmaOne (2 ^ k) = 2 ^ (k + 1) - 1 := by
  rw [sigmaOne_eq_arithmeticSigmaOne,
      ArithmeticFunction.sigma_apply_prime_pow Nat.prime_two]
  simp only [mul_one]
  exact sum_two_pow_eq k

/-- **Closed form for σ* on pure powers of 2**: σ*(2^k) = 3 for k ≥ 1.

    Proof: σ(2^k) = 2^(k+1) - 1, σ*(2^k) + (sum over 4∣d|2^k of d) = σ(2^k),
    and the latter sum is 4·σ(2^(k-2)) = 2^(k+1) - 4 by the Part 6
    structural identity. So σ*(2^k) = (2^(k+1) - 1) - (2^(k+1) - 4) = 3. -/
theorem sigmaStar_two_pow {k : ℕ} (hk : 1 ≤ k) : sigmaStar (2 ^ k) = 3 := by
  have hpos : 0 < 2 ^ k := pow_pos (by decide : (0:ℕ) < 2) k
  have hsum_partition :
      sigmaStar (2 ^ k) + sigmaFourDvd (2 ^ k) = sigmaOne (2 ^ k) :=
    sigmaStar_add_sigmaFourDvd (2 ^ k)
  have hsigma : sigmaOne (2 ^ k) = 2 ^ (k + 1) - 1 := sigmaOne_two_pow k
  have hfourdvd : sigmaFourDvd (2 ^ k) = 2 ^ (k + 1) - 4 := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · -- k = 1 (only case since hk : 1 ≤ k, hk2 : k < 2)
      interval_cases k
      unfold sigmaFourDvd; native_decide
    · have h4_dvd : 4 ∣ 2 ^ k := by
        have hdvd : (2 : ℕ) ^ 2 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk2
        have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4eq]; exact hdvd
      rw [sigmaFourDvd_of_four_dvd h4_dvd hpos]
      have hkdiv : (2 ^ k) / 4 = 2 ^ (k - 2) := by
        have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4eq, Nat.pow_div hk2 (by decide : (0:ℕ) < 2)]
      rw [hkdiv, sigmaOne_two_pow]
      have hsucc : k - 2 + 1 = k - 1 := by omega
      rw [hsucc]
      have hpow_pos : 1 ≤ (2 : ℕ) ^ (k - 1) := Nat.one_le_pow _ _ (by decide)
      have hpow_eq : (2 : ℕ) ^ (k + 1) = 4 * 2 ^ (k - 1) := by
        have hkk : k + 1 = 2 + (k - 1) := by omega
        rw [hkk, pow_add]; ring
      rw [hpow_eq]
      have hge4 : (4 : ℕ) ≤ 4 * 2 ^ (k - 1) := by
        calc (4 : ℕ) = 4 * 1 := by ring
          _ ≤ 4 * 2 ^ (k - 1) := Nat.mul_le_mul_left 4 hpow_pos
      omega
  rw [hsigma, hfourdvd] at hsum_partition
  have hpow4 : (4 : ℕ) ≤ 2 ^ (k + 1) := by
    have h2 : (2 : ℕ) ^ 2 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4eq]; exact h2
  omega

-- =====================================================================
-- PART 14: Cross-validation of σ*-multiplicativity and σ*(2^k) = 3.
-- =====================================================================

example : sigmaStar (2 ^ 1) = 3 := sigmaStar_two_pow (by decide)
example : sigmaStar (2 ^ 2) = 3 := sigmaStar_two_pow (by decide)
example : sigmaStar (2 ^ 3) = 3 := sigmaStar_two_pow (by decide)
example : sigmaStar (2 ^ 5) = 3 := sigmaStar_two_pow (by decide)

/-- σ*(15) = σ*(3) · σ*(5) = 4 · 6 = 24. -/
example : sigmaStar (3 * 5) = sigmaStar 3 * sigmaStar 5 :=
  sigmaStar_mul_of_coprime (by decide) (by decide) (by decide)

/-- σ*(6) = σ*(2) · σ*(3) = 3 · 4 = 12. -/
example : sigmaStar (2 * 3) = sigmaStar 2 * sigmaStar 3 :=
  sigmaStar_mul_of_coprime (by decide) (by decide) (by decide)

/-- σ*(12) = σ*(4) · σ*(3) = 3 · 4 = 12. -/
example : sigmaStar (4 * 3) = sigmaStar 4 * sigmaStar 3 :=
  sigmaStar_mul_of_coprime (by decide) (by decide) (by decide)

/-- σ*(40) = σ*(8) · σ*(5) = 3 · 6 = 18. -/
example : sigmaStar (8 * 5) = sigmaStar 8 * sigmaStar 5 :=
  sigmaStar_mul_of_coprime (by decide) (by decide) (by decide)

/-- σ*(45) = σ*(9) · σ*(5) = 13 · 6 = 78. -/
example : sigmaStar (9 * 5) = sigmaStar 9 * sigmaStar 5 :=
  sigmaStar_mul_of_coprime (by decide) (by decide) (by decide)

-- =====================================================================
-- PART 15: Closed form σ*(2^k · m) = 3·σ(m) for k ≥ 1, m odd.
--
-- Combines σ*-multiplicativity (Part 12) with σ*(2^k) = 3 (Part 13)
-- and σ*(m) = σ(m) for m odd (Part 6) into a single closed form.
--
-- Together with `sigmaStar_eq_sigmaOne_of_odd`, this gives a COMPLETE
-- characterization of σ*(n) by the 2-adic valuation and odd part of n:
--
--    σ*(n)  =  σ(odd_part(n))                      if n is odd
--    σ*(n)  =  3 · σ(odd_part(n))                  if 2 ∣ n
--
-- This reduces the σ*-side of Jacobi's r₄ formula to a single Mathlib
-- σ-value computation regardless of the 2-adic valuation of n.
-- =====================================================================

/-- Closed form for σ*(2^k · m) when k ≥ 1 and m is odd: σ*(2^k · m) = 3 · σ(m).

    Proof outline:
    1. Coprime (2^k) m  (from m odd via `Nat.Prime.coprime_iff_not_dvd`).
    2. σ*-multiplicativity: σ*(2^k · m) = σ*(2^k) · σ*(m).
    3. σ*(2^k) = 3 (Part 13).
    4. σ*(m) = σ(m) since m is odd (Part 6).
    5. Combine: σ*(2^k · m) = 3 · σ(m). -/
theorem sigmaStar_two_pow_mul_odd {k : ℕ} (hk : 1 ≤ k) {m : ℕ}
    (hm : ¬ 2 ∣ m) (hmpos : 0 < m) :
    sigmaStar (2 ^ k * m) = 3 * sigmaOne m := by
  have h2_pos : 0 < 2 ^ k := pow_pos (by decide : (0 : ℕ) < 2) k
  have h2_cop : Nat.Coprime 2 m :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
  have hcop : Nat.Coprime (2 ^ k) m := h2_cop.pow_left k
  rw [sigmaStar_mul_of_coprime hcop h2_pos hmpos,
      sigmaStar_two_pow hk, sigmaStar_eq_sigmaOne_of_odd hm]

/-- Closed form for jacobiR4 on `2^k · m` with `m` odd, k ≥ 1:
    jacobiR4(2^k · m) = 24 · σ(m).

    Pairing this with `sigmaStar_eq_sigmaOne_of_odd` gives a complete
    closed form for jacobiR4(n) given n's 2-adic decomposition:
    - n odd: jacobiR4(n) = 8 · σ(n)
    - n with v₂(n) ≥ 1: jacobiR4(n) = 24 · σ(odd_part(n))

    Once Mathlib provides the q-expansion of jacobiTheta⁴, this lemma is
    one of the two halves needed to close `axiom jacobi_r4_formula`
    (the other being r4Count = q-expansion coefficient).  -/
theorem jacobiR4_two_pow_mul_odd {k : ℕ} (hk : 1 ≤ k) {m : ℕ}
    (hm : ¬ 2 ∣ m) (hmpos : 0 < m) :
    jacobiR4 (2 ^ k * m) = 24 * sigmaOne m := by
  unfold jacobiR4
  rw [sigmaStar_two_pow_mul_odd hk hm hmpos]; ring

-- ---------------------------------------------------------------------
-- Cross-validation of the closed form against PART 1 numeric values.
-- ---------------------------------------------------------------------

/-- σ*(2) = σ*(2^1 · 1) = 3 · σ(1) = 3. -/
example : sigmaStar (2 ^ 1 * 1) = 3 * sigmaOne 1 :=
  sigmaStar_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- σ*(4) = σ*(2^2 · 1) = 3 · σ(1) = 3. -/
example : sigmaStar (2 ^ 2 * 1) = 3 * sigmaOne 1 :=
  sigmaStar_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- σ*(6) = σ*(2^1 · 3) = 3 · σ(3) = 3 · 4 = 12. -/
example : sigmaStar (2 ^ 1 * 3) = 3 * sigmaOne 3 :=
  sigmaStar_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- σ*(8) = σ*(2^3 · 1) = 3 · σ(1) = 3. -/
example : sigmaStar (2 ^ 3 * 1) = 3 * sigmaOne 1 :=
  sigmaStar_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- σ*(10) = σ*(2^1 · 5) = 3 · σ(5) = 3 · 6 = 18. -/
example : sigmaStar (2 ^ 1 * 5) = 3 * sigmaOne 5 :=
  sigmaStar_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- σ*(40) = σ*(2^3 · 5) = 3 · σ(5) = 3 · 6 = 18. -/
example : sigmaStar (2 ^ 3 * 5) = 3 * sigmaOne 5 :=
  sigmaStar_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- jacobiR4(8) = jacobiR4(2^3 · 1) = 24 · σ(1) = 24. -/
example : jacobiR4 (2 ^ 3 * 1) = 24 * sigmaOne 1 :=
  jacobiR4_two_pow_mul_odd (by decide) (by decide) (by decide)

/-- jacobiR4(40) = jacobiR4(2^3 · 5) = 24 · σ(5) = 144 — matches r4Count(40)
    prediction (not numerically verified beyond n = 10, but consistent with
    the closed form r₄(2^k · m) = 24 · σ(m) for odd m, k ≥ 1). -/
example : jacobiR4 (2 ^ 3 * 5) = 24 * sigmaOne 5 :=
  jacobiR4_two_pow_mul_odd (by decide) (by decide) (by decide)

end FourSquareDistributionOQ01
