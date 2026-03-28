/-
Erdős Problem #952: The Gaussian Moat Problem

**Problem Statement (OPEN)**

Is there an infinite sequence of distinct Gaussian primes x₁, x₂, ... such that
|x_{n+1} - x_n| ≪ 1 (i.e., consecutive Gaussian primes with bounded gaps)?

**Historical Note:**
This is notably NOT actually an Erdős problem. According to Erdős himself, the
conjecture originated with Theodore Motzkin, Basil Gordon, and others at a 1963
Pasadena number theory meeting. Erdős popularized it by sharing it widely, and
the attribution was eventually forgotten.

**Background:**
- Gaussian integers: ℤ[i] = {a + bi : a, b ∈ ℤ}
- Gaussian primes: irreducible elements in ℤ[i]
- The "moat" refers to regions without Gaussian primes
- Question: Can we walk from 0 to infinity on Gaussian primes with bounded steps?

**Known Results:**
- Jordan and Rabung (1970): No such walk exists with step size ≤ 2
- Tsuchimura (2005): No such walk exists with step size ≤ √26
- Gethner et al.: Step size 4 is insufficient

**Status:** OPEN - Terence Tao considers this difficult

**Reference:** [Er952], Wikipedia: Gaussian_moat

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open GaussianInt

namespace Erdos952

/-
# Part 1: Gaussian Integers and Primes

The Gaussian integers ℤ[i] form a unique factorization domain.
-/

-- A Gaussian integer is prime in ℤ[i]
def IsGaussianPrime (z : GaussianInt) : Prop := Prime z

-- The set of all Gaussian primes
def GaussianPrimes : Set GaussianInt := {z | IsGaussianPrime z}

/-
# Part 2: Gaussian Prime Classification

A Gaussian integer π is prime iff:
1. π = ±1 ± i (norm 2)
2. π = p or ±i·p where p ≡ 3 (mod 4) is a rational prime
3. π has norm p where p ≡ 1 (mod 4) is a rational prime
-/

-- Classification types for Gaussian primes
def IsNorm2Prime (z : GaussianInt) : Prop :=
  z.norm = 2

def IsInertPrime (z : GaussianInt) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ z.norm = p ^ 2

def IsSplitPrime (z : GaussianInt) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ z.norm = p

/-
# Part 2a: Proved Classification (Backward Direction)

We prove: each of the three classification types implies primality.
The key tool is that elements with prime natAbs norm are irreducible in ℤ[i]
(a Euclidean domain where irreducible ↔ prime).
-/

/-- Elements of ℤ[i] with prime natAbs norm are irreducible, hence prime.
    This handles both norm-2 primes and split primes. -/
theorem prime_of_prime_natAbs_norm {z : GaussianInt}
    (hp : Nat.Prime z.norm.natAbs) : IsGaussianPrime z := by
  unfold IsGaussianPrime
  rw [← irreducible_iff_prime]
  refine ⟨?_, ?_⟩
  · -- Not a unit: units have natAbs norm = 1, but hp says prime (≥ 2)
    exact mt Zsqrtd.norm_eq_one_iff.mpr (Nat.Prime.ne_one hp)
  · -- If z = a * b, one factor must be a unit
    intro a b hab
    have hn : a.norm.natAbs * b.norm.natAbs = z.norm.natAbs := by
      rw [hab, Zsqrtd.norm_mul, Int.natAbs_mul]
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, hn.symm⟩ with ha | ha
    · left; exact Zsqrtd.norm_eq_one_iff.mp ha
    · right; apply Zsqrtd.norm_eq_one_iff.mp
      have hpos : 0 < z.norm.natAbs := hp.pos
      omega

/-- Norm-2 elements are prime in ℤ[i] (e.g., 1+i, 1-i and associates). -/
theorem prime_of_norm2 {z : GaussianInt} (h : IsNorm2Prime z) : IsGaussianPrime z := by
  apply prime_of_prime_natAbs_norm
  unfold IsNorm2Prime at h
  rw [h]; decide

/-- Elements with norm equal to a prime p ≡ 1 mod 4 are prime in ℤ[i]. -/
theorem prime_of_split {z : GaussianInt} {p : ℕ} (hp : p.Prime) (_ : p % 4 = 1)
    (hnorm : z.norm = p) : IsGaussianPrime z := by
  apply prime_of_prime_natAbs_norm
  rw [hnorm, Int.natAbs_natCast]
  exact hp

/-- Elements with norm p² where p ≡ 3 mod 4 is prime are irreducible, hence prime.
    Key insight: the only non-unit factorization a·b with norm(a)·norm(b) = p² would
    require both norms to be p, but p ≡ 3 mod 4 can't be a sum of two squares. -/
theorem prime_of_inert {z : GaussianInt} {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 3)
    (hnorm : z.norm = (p : ℤ) ^ 2) : IsGaussianPrime z := by
  unfold IsGaussianPrime
  rw [← irreducible_iff_prime]
  refine ⟨?_, ?_⟩
  · -- Not a unit: norm = p² ≥ 4 > 1
    intro hu
    have h1 := (Zsqrtd.norm_eq_one_iff' (show (-1 : ℤ) ≤ 0 by norm_num)).mpr hu
    have : (p : ℤ) ^ 2 ≥ 4 := by
      have := hp.two_le; positivity
    omega
  · -- If z = a * b, one must be a unit
    intro a b hab
    by_contra h
    push_neg at h
    obtain ⟨hau, hbu⟩ := h
    -- Neither factor is a unit, so natAbs norms ≠ 1
    have hau' : a.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp hau
    have hbu' : b.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mp hbu
    -- natAbs norms multiply to p²
    have hn : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
      rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hnorm,
        Int.natAbs_pow, Int.natAbs_natCast]
    -- By prime factorization of p²: both natAbs norms must equal p
    have hfact := (hp.mul_eq_prime_sq_iff hau' hbu').mp hn
    -- So norm(a).natAbs = p. Since GaussianInt norms are non-negative, norm(a) = p.
    have ha_norm_eq : a.norm = (p : ℤ) := by
      rw [Int.natAbs_eq_iff] at hfact
      rcases hfact.1 with h | h
      · exact_mod_cast h
      · linarith [GaussianInt.norm_nonneg a, hp.pos]
    -- norm(a) = re² + im² for Gaussian integers (since d = -1)
    have ha_sum : a.re ^ 2 + a.im ^ 2 = (p : ℤ) := by
      have hn_def : a.norm = a.re * a.re - (-1 : ℤ) * (a.im * a.im) := rfl
      have : a.re * a.re = a.re ^ 2 := by ring
      have : a.im * a.im = a.im ^ 2 := by ring
      linarith
    -- Cast to ZMod 4: squares mod 4 ∈ {0,1}, so sums ∈ {0,1,2}. But p ≡ 3 mod 4.
    have h4 : (a.re : ZMod 4) ^ 2 + (a.im : ZMod 4) ^ 2 = (p : ZMod 4) := by
      have := congr_arg (Int.cast : ℤ → ZMod 4) ha_sum
      push_cast at this ⊢
      exact this
    have hp4 : (p : ZMod 4) = (3 : ZMod 4) := by
      change ((p : ℤ) : ZMod 4) = 3
      rw [show (p : ℤ) = ((p % 4 : ℕ) : ℤ) + 4 * ((p / 4 : ℕ) : ℤ) from by omega]
      simp [hmod]
    rw [hp4] at h4
    revert h4; decide

/-- Backward direction of classification: each type implies Gaussian primality. -/
theorem classification_backward (z : GaussianInt) :
    IsNorm2Prime z ∨ IsInertPrime z ∨ IsSplitPrime z → IsGaussianPrime z := by
  rintro (h | ⟨p, hp, hmod, hnorm⟩ | ⟨p, hp, hmod, hnorm⟩)
  · exact prime_of_norm2 h
  · exact prime_of_inert hp hmod hnorm
  · exact prime_of_split hp hmod hnorm

/-- Forward direction: a Gaussian prime must be one of the three types.
    Requires showing every prime in ℤ[i] lies over a rational prime
    (follows from ℤ[i] being integral of degree 2 over ℤ). -/
axiom classification_forward (z : GaussianInt) :
    IsGaussianPrime z → IsNorm2Prime z ∨ IsInertPrime z ∨ IsSplitPrime z

/-- Full Gaussian prime classification (backward proved, forward axiom). -/
theorem gaussian_prime_classification (z : GaussianInt) :
    IsGaussianPrime z ↔ IsNorm2Prime z ∨ IsInertPrime z ∨ IsSplitPrime z :=
  ⟨classification_forward z, classification_backward z⟩

/-
# Part 3: The Moat Problem

Can we walk from 0 to infinity on Gaussian primes with bounded step size?
-/

-- An infinite walk is a sequence of Gaussian primes
def IsInfiniteGaussianPrimeWalk (x : ℕ → GaussianInt) : Prop :=
  Function.Injective x ∧ ∀ n, IsGaussianPrime (x n)

-- A walk has bounded gaps if consecutive steps have norm < C
def HasBoundedGaps (x : ℕ → GaussianInt) (C : ℕ) : Prop :=
  ∀ n, (x (n + 1) - x n).norm < C

-- The moat of width k: can we escape to infinity with steps of norm < k?
def CanEscapeMoat (k : ℕ) : Prop :=
  ∃ x : ℕ → GaussianInt, IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x k

-- The Gaussian moat conjecture (positive form)
def GaussianMoatConjecture : Prop :=
  ∃ (x : ℕ → GaussianInt) (C : ℕ),
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x C

-- Equivalent to Erdős 952 statement
def ErdosConjecture952 : Prop := GaussianMoatConjecture

/-
# Part 4: Known Negative Results

Various researchers have shown bounded walks don't exist for small step sizes.
-/

-- Tsuchimura (2005): No walk with step size ≤ √26 (strongest known)
axiom tsuchimura : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 27  -- norm < 27 means |step| < √27

-- Jordan-Rabung (1970): No walk with step size ≤ 2
-- Follows from Tsuchimura since 5 < 27: any walk with norm < 5 also has norm < 27
theorem jordan_rabung : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 5 := by
  intro ⟨x, hwalk, hgaps⟩
  exact tsuchimura ⟨x, hwalk, fun n => lt_trans (hgaps n) (by norm_num)⟩

-- Gethner et al.: step size 4 insufficient
-- Follows from Tsuchimura since 17 < 27
theorem gethner_et_al : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 17 := by
  intro ⟨x, hwalk, hgaps⟩
  exact tsuchimura ⟨x, hwalk, fun n => lt_trans (hgaps n) (by norm_num)⟩

-- Generalization: Tsuchimura subsumes all step sizes ≤ √26
theorem not_canEscapeMoat_le_27 (k : ℕ) (hk : k ≤ 27) : ¬CanEscapeMoat k := by
  intro ⟨x, hwalk, hgaps⟩
  exact tsuchimura ⟨x, hwalk, fun n => lt_of_lt_of_le (hgaps n) hk⟩

-- Monotonicity: escaping a moat of width k implies escaping width k' ≥ k
theorem canEscapeMoat_mono {k k' : ℕ} (hk : k ≤ k') (h : CanEscapeMoat k) :
    CanEscapeMoat k' := by
  obtain ⟨x, hwalk, hgaps⟩ := h
  exact ⟨x, hwalk, fun n => lt_of_lt_of_le (hgaps n) hk⟩

-- Current state: unknown for larger step sizes
def CurrentBestBound : ℕ := 27

/-
# Part 5: The Moat Width

A "moat" is a region around 0 containing no Gaussian primes beyond a certain norm.
-/

-- The critical moat width (if it exists)
noncomputable def criticalMoatWidth : ℕ :=
  Nat.find (⟨0, fun x hx => hx.1 0⟩ : ∃ k, ¬ CanEscapeMoat k)

-- If no walk exists for any k, the conjecture is false
def StrongNegation : Prop := ∀ k, ¬ CanEscapeMoat k

/-
# Part 6: Density of Gaussian Primes

Gaussian primes have density related to 1/log(norm).
-/

-- Count of Gaussian primes with norm ≤ R² in the box [-R, R] × [-R, R]
noncomputable def gaussianPrimeCount (R : ℕ) : ℕ :=
  ((Finset.Icc (-(R : ℤ)) R ×ˢ Finset.Icc (-(R : ℤ)) R).filter
    (fun p : ℤ × ℤ =>
      let z : GaussianInt := ⟨p.1, p.2⟩
      IsGaussianPrime z ∧ z.norm ≤ R ^ 2)).card

-- Asymptotic: π_ℤ[i](x) ~ x / log(x)
-- Similar to rational prime counting function
axiom gaussian_prime_theorem : ∀ ε > 0, ∃ N : ℕ,
  ∀ R ≥ N, |((gaussianPrimeCount R : ℝ) / R ^ 2) - 1 / Real.log R| < ε

/-
# Part 7: Connections to Rational Primes

The problem is related to gaps between primes in arithmetic progressions.
-/

-- Primes p ≡ 1 (mod 4) split in ℤ[i]
-- For such p, p = π · π̄ where π, π̄ are Gaussian primes with norm p

-- The splitting behavior: given p ≡ 1 mod 4 prime, produce the Gaussian factors
-- Uses Fermat's two-square theorem (Nat.Prime.sq_add_sq from Mathlib)
noncomputable def splitPrime (p : ℕ) (hp : p.Prime) (hmod : p % 4 = 1) :
    GaussianInt × GaussianInt :=
  haveI : Fact p.Prime := ⟨hp⟩
  let ⟨a, b, _⟩ := hp.sq_add_sq (by omega : p % 4 ≠ 3)
  (⟨(a : ℤ), (b : ℤ)⟩, ⟨(a : ℤ), -(b : ℤ)⟩)

-- Connection: large gaps in primes ≡ 1 (mod 4) create large moats
axiom primes_mod_4_connection :
    (∀ k, ¬ CanEscapeMoat k) →
    ∀ C, ∃ᶠ n in Filter.atTop, ∀ m ∈ Finset.range C,
      ¬ (n + m).Prime ∨ (n + m) % 4 ≠ 1

/-
# Part 8: Equivalences and Structural Results
-/

/-- The conjecture is equivalent to the existence of some escapable moat width. -/
theorem conjecture_iff_canEscape :
    GaussianMoatConjecture ↔ ∃ k, CanEscapeMoat k := by
  unfold GaussianMoatConjecture CanEscapeMoat
  unfold IsInfiniteGaussianPrimeWalk HasBoundedGaps
  constructor
  · rintro ⟨x, C, hwalks, hgaps⟩; exact ⟨C, x, hwalks, hgaps⟩
  · rintro ⟨C, x, hwalks, hgaps⟩; exact ⟨x, C, hwalks, hgaps⟩

/-- The strong negation is the negation of the conjecture. -/
theorem strongNegation_iff_not_conjecture :
    StrongNegation ↔ ¬GaussianMoatConjecture := by
  rw [conjecture_iff_canEscape]
  unfold StrongNegation
  push_neg
  rfl

-- Main formal statement
theorem erdos_952_statement :
    ErdosConjecture952 ↔
    ∃ (x : ℕ → GaussianInt) (C : ℕ),
      (Function.Injective x ∧ ∀ n, Prime (x n)) ∧
      (∀ n, (x (n + 1) - x n).norm < C) := by
  unfold ErdosConjecture952 GaussianMoatConjecture
  unfold IsInfiniteGaussianPrimeWalk HasBoundedGaps IsGaussianPrime
  rfl

/-
# Part 9: Variants

Related problems about walking on various prime sets.
-/

-- Can we walk to infinity on Eisenstein primes (ℤ[ω], ω = e^{2πi/3})?
def EisensteinMoatProblem : Prop :=
  True  -- Analogous question for Eisenstein integers

-- Can we walk on rational primes with bounded gaps?
-- This is related to the twin prime conjecture
def RationalPrimeMoat : Prop :=
  ∃ C : ℕ, ∃ᶠ n in Filter.atTop, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < n ∧ n < q ∧ q - p ≤ C

/-
# Summary

**Problem:** Can we walk from 0 to infinity on Gaussian primes with bounded step size?

**Known:**
- Steps ≤ 2: Jordan-Rabung (1970) showed NO
- Steps ≤ √26: Tsuchimura (2005) showed NO
- Computational evidence: moats exist requiring larger steps

**Unknown:**
- Whether any bounded step size suffices
- The critical moat width (if the answer is NO)

**Axioms (4):**
- classification_forward: prime → one of three norm types (deep, requires integral extension theory)
- tsuchimura: computational verification (no walk ≤ √26)
- gaussian_prime_theorem: asymptotic density (analytic number theory)
- primes_mod_4_connection: moat structure from prime gaps

**Proved from Mathlib:**
- Classification backward direction (3 norm types → prime)
  - prime_of_prime_natAbs_norm: prime norm → Gaussian prime
  - prime_of_inert: p² norm with p ≡ 3 mod 4 → prime (via ZMod 4 argument)
- splitPrime definition (via Fermat's two-square theorem)
- jordan_rabung, gethner_et_al from tsuchimura
- Moat monotonicity and structural equivalences

**Difficulty:** Requires understanding global distribution of Gaussian primes.
-/

-- The problem is open
def erdos_952_status : String := "OPEN"

-- Attribution note
def attribution_note : String :=
  "Not actually an Erdős problem. Originated with Motzkin, Gordon, and others (1963)."

end Erdos952
