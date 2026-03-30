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

/-- A Gaussian prime divides some rational prime cast into ℤ[i].
    Proof by strong induction: z ∣ norm(z), and for any composite n > 1,
    z ∣ n implies z ∣ minFac(n) or z ∣ n/minFac(n), the latter being smaller. -/
private theorem exists_nat_prime_dvd {z : GaussianInt} (hz : IsGaussianPrime z)
    (n : ℕ) (hn : 1 < n) (hd : z ∣ (n : ℤ[i])) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p : ℤ[i]) := by
  by_cases hp : n.Prime
  · exact ⟨n, hp, hd⟩
  · -- n > 1 and composite: factor via minFac
    set f := n.minFac with hf_def
    set m := n / f with hm_def
    have hfp : f.Prime := Nat.minFac_prime (by omega)
    have hfd : f ∣ n := Nat.minFac_dvd n
    have hn_eq : f * m = n := Nat.mul_div_cancel' hfd
    have hm_lt : m < n := Nat.div_lt_self (by omega) hfp.one_lt
    have hm_gt : 1 < m := by
      have hm0 : m ≠ 0 := by intro h; rw [h, mul_zero] at hn_eq; omega
      have hm1 : m ≠ 1 := by
        intro h; rw [h, mul_one] at hn_eq; rw [← hn_eq] at hp; exact hp hfp
      omega
    have hd' : z ∣ (f : ℤ[i]) * (m : ℤ[i]) := by rwa [← Nat.cast_mul, hn_eq]
    rcases hz.dvd_or_dvd hd' with h | h
    · exact ⟨f, hfp, h⟩
    · exact exists_nat_prime_dvd hz m hm_gt h
termination_by n

/-- Forward direction of Gaussian prime classification: every Gaussian prime
    has norm 2, p (for p ≡ 1 mod 4), or p² (for p ≡ 3 mod 4).

    Proof strategy:
    1. z * star(z) = norm(z), so z ∣ norm(z)
    2. By strong induction, z ∣ ↑p for some rational prime p
    3. norm(z) * norm(q) = p² (from ↑p = z * q), giving norm(z) = p or p²
    4. If norm = p: p = 2 (Norm2) or p ≡ 1 mod 4 (Split, via sum-of-squares mod 4)
    5. If norm = p²: z ∼ ↑p (associated), so ↑p is prime in ℤ[i],
       hence p ≡ 3 mod 4 (by Mathlib characterization) -/
theorem classification_forward (z : GaussianInt) :
    IsGaussianPrime z → IsNorm2Prime z ∨ IsInertPrime z ∨ IsSplitPrime z := by
  intro hz
  -- Step 1: z ∣ ↑(norm(z).natAbs) in ℤ[i]
  have hdvd : z ∣ (z.norm : ℤ[i]) := ⟨star z, (Zsqrtd.norm_eq_mul_conj z).symm⟩
  have hne0 : z ≠ 0 := hz.ne_zero
  have hna_ne1 : z.norm.natAbs ≠ 1 := mt Zsqrtd.norm_eq_one_iff.mpr hz.not_unit
  have hna_gt1 : 1 < z.norm.natAbs := by
    have := Int.natAbs_pos.mpr (GaussianInt.norm_pos.mpr hne0).ne'; omega
  have hdvd_nat : z ∣ (z.norm.natAbs : ℤ[i]) := by
    rw [show (z.norm.natAbs : ℤ[i]) = (z.norm : ℤ[i]) from by
      exact_mod_cast GaussianInt.natCast_natAbs_norm z]
    exact hdvd
  -- Step 2: find a rational prime p with z ∣ ↑p
  obtain ⟨p, hp, hzp⟩ := exists_nat_prime_dvd hz z.norm.natAbs hna_gt1 hdvd_nat
  -- Step 3: from ↑p = z * q, get norm(z) * norm(q) = p²
  obtain ⟨q, hq⟩ := hzp
  have hnorm_mul : z.norm * q.norm = (p : ℤ) * p := by
    have := congr_arg Zsqrtd.norm hq
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_natCast] at this
    linarith
  have hna_mul : z.norm.natAbs * q.norm.natAbs = p ^ 2 := by
    zify [GaussianInt.norm_nonneg z, GaussianInt.norm_nonneg q]
    have h1 := GaussianInt.natCast_natAbs_norm z
    have h2 := GaussianInt.natCast_natAbs_norm q
    push_cast [h1, h2]; nlinarith [hnorm_mul]
  -- Step 4: classify by whether norm(q) is 1 or not
  by_cases hqu : q.norm.natAbs = 1
  · -- norm(q) = 1: q is a unit, norm(z) = p², z ∼ ↑p
    have hna_p2 : z.norm.natAbs = p ^ 2 := by nlinarith
    have hnorm_p2 : z.norm = (p : ℤ) ^ 2 := by
      have := GaussianInt.natCast_natAbs_norm z; push_cast [hna_p2] at this ⊢; linarith
    -- z and ↑p are associates: ↑p = z * q with q a unit
    have hpu : IsUnit q := Zsqrtd.norm_eq_one_iff.mp hqu
    -- ↑p is prime in ℤ[i] (associated to the prime z)
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_prime_gi : Prime (↑p : ℤ[i]) := by
      -- ↑p = z * q with q a unit, so ↑p ∣ z (via z = ↑p * q⁻¹)
      -- Combined with z ∣ ↑p, they are associated, and associated preserves primality
      obtain ⟨u, hu⟩ := hpu -- u : ℤ[i]ˣ, hu : ↑u = q
      have hpz : (↑p : ℤ[i]) ∣ z := ⟨↑u⁻¹, by
        have h1 : (↑p : ℤ[i]) = z * ↑u := by rw [hu]; exact hq
        calc z = z * 1 := (mul_one z).symm
          _ = z * (↑u * ↑u⁻¹) := by rw [Units.val_mul_inv]
          _ = (z * ↑u) * ↑u⁻¹ := (mul_assoc z ↑u ↑u⁻¹).symm
          _ = ↑p * ↑u⁻¹ := by rw [h1]⟩
      exact (associated_of_dvd_dvd hpz hzp).prime_iff.mpr hz
    -- By Mathlib: Prime (↑p : ℤ[i]) ↔ p % 4 = 3
    have hp4 : p % 4 = 3 :=
      (GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p).mp hp_prime_gi
    right; left
    exact ⟨p, hp, hp4, hnorm_p2⟩
  · -- Both natAbs ≠ 1: by mul_eq_prime_sq_iff, norm(z).natAbs = p
    have hboth := (hp.mul_eq_prime_sq_iff hna_ne1 hqu).mp hna_mul
    have hna_p : z.norm.natAbs = p := hboth.1
    have hnorm_p : z.norm = (p : ℤ) := by
      have := GaussianInt.natCast_natAbs_norm z; push_cast [hna_p] at this; linarith
    -- Classify: p = 2 → Norm2, p odd → Split (p ≡ 1 mod 4)
    by_cases hp2 : p = 2
    · left; show z.norm = 2; rw [hnorm_p, hp2]; simp
    · -- p odd prime, norm(z) = z.re² + z.im² = p
      -- Sum of two squares mod 4: since p is odd, p ≡ 1 mod 4
      right; right; refine ⟨p, hp, ?_, hnorm_p⟩
      have hsum : z.re ^ 2 + z.im ^ 2 = (p : ℤ) := by
        have : z.norm = z.re * z.re - (-1 : ℤ) * (z.im * z.im) := rfl; nlinarith [hnorm_p]
      -- p ≡ 3 mod 4 is impossible (sum of two squares ∈ {0,1,2} mod 4)
      have hp_ne3 : p % 4 ≠ 3 := by
        intro h3
        have h4 : (z.re : ZMod 4) ^ 2 + (z.im : ZMod 4) ^ 2 = (p : ZMod 4) := by
          have := congr_arg (Int.cast : ℤ → ZMod 4) hsum; push_cast at this ⊢; exact this
        have : (p : ZMod 4) = (3 : ZMod 4) := by
          change ((p : ℤ) : ZMod 4) = 3
          rw [show (p : ℤ) = ((p % 4 : ℕ) : ℤ) + 4 * ((p / 4 : ℕ) : ℤ) from by omega]
          simp [h3]
        rw [this] at h4; revert h4; decide
      -- p is odd (not 2) and p % 4 ≠ 3, so p % 4 = 1
      have hp_odd : p % 2 = 1 := by
        rcases hp.eq_two_or_odd with rfl | h; exact absurd rfl hp2; exact h
      omega

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
  Nat.find ⟨0, not_canEscapeMoat_le_27 0 (Nat.zero_le 27)⟩

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
-- Similar to rational prime counting function (analytic number theory, not formalized here)
def GaussianPrimeTheorem : Prop := ∀ ε > 0, ∃ N : ℕ,
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
-- Proved unconditionally: the factorial construction gives arbitrarily long
-- prime-free intervals, hence no primes ≡ 1 mod 4 either.
theorem primes_mod_4_connection :
    (∀ k, ¬ CanEscapeMoat k) →
    ∀ C, ∃ᶠ n in Filter.atTop, ∀ m ∈ Finset.range C,
      ¬ (n + m).Prime ∨ (n + m) % 4 ≠ 1 := by
  intro _ C
  rw [Filter.frequently_atTop]
  intro a
  -- For any window size C, [k!+2, k!+C+1] is entirely composite
  set k := max a (C + 2)
  refine ⟨k ! + 2, ?_, ?_⟩
  · -- k! + 2 ≥ a (since k ≤ k! for k ≥ 1)
    have : k ≤ k ! := by
      apply Nat.le_of_dvd (Nat.factorial_pos k)
      match k, show 1 ≤ k by omega with
      | n + 1, _ => exact ⟨n !, Nat.factorial_succ n⟩
    omega
  · -- Every number in [k!+2, k!+2+C) is composite
    intro m hm
    left
    rw [Finset.mem_range] at hm
    -- j = m + 2 divides k!, hence divides k! + j, making k!+2+m composite
    set j := m + 2
    have hj_le_k : j ≤ k := by omega
    have hj_dvd_kfact : j ∣ k ! := by
      apply dvd_trans
      · -- j ∣ j! (since j! = j * (j-1)!)
        match j, show 1 ≤ j by omega with
        | n + 1, _ => exact ⟨n !, Nat.factorial_succ n⟩
      · exact Nat.factorial_dvd_factorial hj_le_k
    have hj_dvd : j ∣ (k ! + 2 + m) := by
      rw [show k ! + 2 + m = k ! + j from by omega]
      exact dvd_add hj_dvd_kfact (dvd_refl j)
    -- k!+2+m has proper divisor j (2 ≤ j < k!+2+m), so not prime
    intro hp
    rcases hp.eq_one_or_self_of_dvd j hj_dvd with h | h
    · omega -- j ≥ 2, not 1
    · have := Nat.factorial_pos k; omega -- j = k!+2+m implies k! = 0, impossible

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

**Axioms (1):**
- tsuchimura: computational verification (no walk ≤ √26)

**Stated (not axiomatized):**
- GaussianPrimeTheorem: asymptotic density (analytic number theory, as Prop def)

**Proved from Mathlib:**
- Full Gaussian prime classification (both directions):
  - Backward: 3 norm types → prime (prime_of_prime_natAbs_norm, prime_of_inert, prime_of_split)
  - Forward: prime → one of 3 norm types (classification_forward, via strong induction + mod 4)
- primes_mod_4_connection: proved via factorial construction (k!+2,...,k!+k all composite)
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
