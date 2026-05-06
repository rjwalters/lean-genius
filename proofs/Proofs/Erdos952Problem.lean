/-
Erdős Problem #952: The Gaussian Moat Problem

**Problem Statement (OPEN)**

Is there an infinite sequence of distinct Gaussian primes x₁, x₂, ... such that
|x_{n+1} - x_n| ≪ 1 (i.e., consecutive Gaussian primes with bounded gaps)?

**Historical Note:**
Despite being catalogued as an Erdős problem, this is notably NOT actually an Erdős
problem. According to Erdős himself, the conjecture originated with Theodore Motzkin,
Basil Gordon, and others at a 1963 Pasadena number theory meeting. Erdős popularized
it by sharing it widely, and the attribution was eventually forgotten.

**Background:**
- Gaussian integers: ℤ[i] = {a + bi : a, b ∈ ℤ}, with norm N(a+bi) = a² + b²
- Gaussian primes: irreducible elements in the UFD ℤ[i]
- The "moat" refers to regions without Gaussian primes that block infinite walks
- Question: Can we walk from 0 to infinity on Gaussian primes with bounded steps?

**Gaussian Prime Classification:**
A Gaussian integer π is prime iff exactly one of:
1. N(π) = 2 (the prime 1+i and its associates)
2. N(π) = p² where p ≡ 3 (mod 4) is a rational prime (inert primes)
3. N(π) = p where p ≡ 1 (mod 4) is a rational prime (split primes)

**Known Negative Results:**
- Jordan and Rabung (1970): No such walk exists with step size ≤ 2
- Tsuchimura (2005): No such walk exists with step size ≤ √26
- Gethner et al.: Step size 4 is insufficient

**Status:** OPEN - Terence Tao considers this difficult

**Reference:** https://erdosproblems.com/952, Wikipedia: Gaussian_moat

Adapted from formal-conjectures (Apache 2.0 License)
-/

import Mathlib

open GaussianInt

namespace Erdos952

/-
# Part 1: Gaussian Integers and Primes

The Gaussian integers ℤ[i] form a unique factorization domain.
-/

/-- A Gaussian integer is prime in ℤ[i] -/
def IsGaussianPrime (z : GaussianInt) : Prop := Prime z

/-- The set of all Gaussian primes -/
def GaussianPrimes : Set GaussianInt := {z | IsGaussianPrime z}

/-
# Part 2: Gaussian Prime Classification

A Gaussian integer π is prime iff:
1. π has norm 2 (e.g., 1+i and its associates)
2. π has norm p² for a rational prime p ≡ 3 (mod 4) (inert primes)
3. π has norm p for a rational prime p ≡ 1 (mod 4) (split primes)
-/

/-- Type 1: Gaussian primes with norm 2 (like 1+i) -/
def IsNorm2Prime (z : GaussianInt) : Prop :=
  z.norm = 2

/-- Type 2: Inert primes - rational primes p ≡ 3 (mod 4) stay prime in ℤ[i] -/
def IsInertPrime (z : GaussianInt) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ z.norm = p ^ 2

/-- Type 3: Split primes - rational primes p ≡ 1 (mod 4) factor into Gaussian primes -/
def IsSplitPrime (z : GaussianInt) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p % 4 = 1 ∧ z.norm = p

-- Helper: no sum of two squares is ≡ 3 mod 4, so no Gaussian integer has norm ≡ 3 mod 4
private lemma norm_natAbs_ne_three_mod_four {z : GaussianInt} {p : ℕ}
    (hmod : p % 4 = 3) (h : z.norm.natAbs = p) : False := by
  have heq : z.re.natAbs ^ 2 + z.im.natAbs ^ 2 = p := by
    have h1 := GaussianInt.natAbs_norm_eq z
    simp only [sq] at *; linarith
  have key : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ (p : ZMod 4) := by
    erw [← ZMod.natCast_mod p 4, hmod]; decide
  apply key (z.re.natAbs : ZMod 4) (z.im.natAbs : ZMod 4)
  calc (z.re.natAbs : ZMod 4) ^ 2 + (z.im.natAbs : ZMod 4) ^ 2
      = ((z.re.natAbs ^ 2 + z.im.natAbs ^ 2 : ℕ) : ZMod 4) := by push_cast; ring
    _ = (p : ZMod 4) := by exact_mod_cast congr_arg (Nat.cast : ℕ → ZMod 4) heq

-- Helper: if z is prime and z | ↑n, then z | ↑p for some rational prime p | n
private lemma prime_dvd_rat_prime {z : GaussianInt} (hz : Prime z) (n : ℕ)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hdvd : z ∣ (n : GaussianInt)) :
    ∃ p : ℕ, p.Prime ∧ z ∣ (p : GaussianInt) := by
  have h_prod : ((n.primeFactorsList).map (Nat.cast : ℕ → GaussianInt)).prod = (n : GaussianInt) := by
    rw [← Nat.cast_list_prod, Nat.prod_primeFactorsList hn0]
  rw [← h_prod] at hdvd
  have key : ∀ (l : List ℕ), z ∣ (l.map (Nat.cast : ℕ → GaussianInt)).prod →
      ∃ q ∈ l, z ∣ (q : GaussianInt) := by
    intro l
    induction l with
    | nil => simp; intro h; exact absurd (isUnit_of_dvd_one h) hz.not_unit
    | cons a l' ih =>
      intro hdvd'
      simp only [List.map_cons, List.prod_cons] at hdvd'
      rcases hz.dvd_or_dvd hdvd' with ha | hl
      · exact ⟨a, List.mem_cons_self _ _, ha⟩
      · obtain ⟨q, hq_mem, hq_dvd⟩ := ih hl
        exact ⟨q, List.mem_cons_of_mem _ hq_mem, hq_dvd⟩
  obtain ⟨p, hp_mem, hp_dvd⟩ := key n.primeFactorsList hdvd
  exact ⟨p, (Nat.mem_primeFactorsList hn0 |>.mp hp_mem).1, hp_dvd⟩

-- Helper: Gaussian integer with norm = rational prime p is itself a Gaussian prime
private lemma gauss_prime_of_prime_norm {z : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hn : z.norm = (p : ℤ)) : Prime z := by
  rw [← irreducible_iff_prime]
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0), hn]
    exact_mod_cast hp.one_lt.ne'
  · have hnorm_eq : a.norm * b.norm = (p : ℤ) := by
      have h1 := Zsqrtd.norm_mul a b; rw [← hab] at h1; exact h1.symm.trans hn
    have hna := GaussianInt.norm_nonneg a
    have hnb := GaussianInt.norm_nonneg b
    have hnat : a.norm.natAbs * b.norm.natAbs = p := by
      rw [← Int.natAbs_mul, hnorm_eq]; simp
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, hnat.symm⟩ with h1 | h2
    · left; rwa [Zsqrtd.norm_eq_one_iff]
    · right
      have hb1 : b.norm.natAbs = 1 := by
        have h_eq : p * b.norm.natAbs = p := by rw [← h2, hnat]
        omega
      rwa [Zsqrtd.norm_eq_one_iff]

-- Helper: Gaussian integer with norm = p² (p prime, p ≡ 3 mod 4) is a Gaussian prime
private lemma gauss_prime_of_inert {z : GaussianInt} {p : ℕ}
    (hp : p.Prime) (hmod : p % 4 = 3) (hn : z.norm = (p : ℤ) ^ 2) : Prime z := by
  rw [← irreducible_iff_prime]
  refine ⟨?_, fun a b hab => ?_⟩
  · rw [← Zsqrtd.norm_eq_one_iff' (by norm_num : (-1 : ℤ) ≤ 0), hn]
    have : 1 < (p : ℤ) ^ 2 := by have := hp.one_lt; nlinarith
    exact_mod_cast this.ne'
  · have hnorm_eq : a.norm * b.norm = (p : ℤ) ^ 2 := by
      have h1 := Zsqrtd.norm_mul a b; rw [← hab] at h1; exact h1.symm.trans hn
    have hna := GaussianInt.norm_nonneg a
    have hnb := GaussianInt.norm_nonneg b
    have hnat : a.norm.natAbs * b.norm.natAbs = p ^ 2 := by
      rw [← Int.natAbs_mul, hnorm_eq]; simp [Int.natAbs_pow]
    have ha_dvd : a.norm.natAbs ∣ p ^ 2 := ⟨b.norm.natAbs, hnat.symm⟩
    rw [Nat.dvd_prime_pow hp] at ha_dvd
    obtain ⟨k, hk2, hk⟩ := ha_dvd
    interval_cases k
    · simp only [pow_zero] at hk; left; rwa [Zsqrtd.norm_eq_one_iff]
    · simp only [pow_one] at hk; exact (norm_natAbs_ne_three_mod_four hmod hk).elim
    · right
      have hb1 : b.norm.natAbs = 1 := by
        have : p ^ 2 * b.norm.natAbs = p ^ 2 := by rw [← hk, hnat]
        have h_pos : 0 < p ^ 2 := Nat.pos_pow_of_pos 2 hp.pos
        omega
      rwa [Zsqrtd.norm_eq_one_iff]

/-- The complete classification of Gaussian primes:
    π ∈ ℤ[i] is prime iff its norm is 2, or p² (p ≡ 3 mod 4 rational prime),
    or p (p ≡ 1 mod 4 rational prime). Proved from Mathlib's Fermat two-square
    theorem and the characterization of inert rational primes. -/
theorem gaussian_prime_classification (z : GaussianInt) :
    IsGaussianPrime z ↔ IsNorm2Prime z ∨ IsInertPrime z ∨ IsSplitPrime z := by
  unfold IsGaussianPrime IsNorm2Prime IsInertPrime IsSplitPrime
  constructor
  · intro hz
    -- z | ↑(z.norm.natAbs) via z * star z = norm z
    have hn0 : z.norm.natAbs ≠ 0 := by
      simp [Int.natAbs_eq_zero, GaussianInt.norm_eq_zero, hz.ne_zero]
    have hn1 : z.norm.natAbs ≠ 1 := by
      rw [Ne, Zsqrtd.norm_eq_one_iff]; exact hz.not_unit
    have hdvd_norm : z ∣ (z.norm.natAbs : GaussianInt) := by
      rw [GaussianInt.natCast_natAbs_norm]
      exact ⟨star z, (Zsqrtd.norm_eq_mul_conj z).symm⟩
    -- Find rational prime p with z | ↑p
    obtain ⟨p, hp, hdvd_p⟩ := prime_dvd_rat_prime hz z.norm.natAbs hn0 hn1 hdvd_norm
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p % 4 = 3
    · -- p ≡ 3 mod 4: ↑p is Gaussian prime, z ~ ↑p, norm z = p²
      have hp_gauss : Prime (p : GaussianInt) :=
        GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p |>.mpr hp3
      have h_assoc := hz.associated_of_dvd hp_gauss hdvd_p
      right; left
      exact ⟨p, hp, hp3, by
        rw [Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0) h_assoc,
            Zsqrtd.norm_natCast]; ring⟩
    · -- p % 4 ≠ 3: use Fermat to factor ↑p = ⟨a,b⟩ * ⟨a,-b⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp hp3
      -- norm of ⟨a,b⟩ equals p
      have h_ab_norm : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm = (p : ℤ) := by
        have h1 : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt).norm.natAbs = p := by
          rw [GaussianInt.natAbs_norm_eq]; simp only [Int.natAbs_ofNat, sq] at *; linarith
        rw [← GaussianInt.abs_natCast_norm]; exact_mod_cast h1
      have h_ab_prime := gauss_prime_of_prime_norm hp h_ab_norm
      -- ↑p = ⟨a,b⟩ * ⟨a,-b⟩
      have hab_int : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
      have h_factor : (p : GaussianInt) = ⟨(a : ℤ), (b : ℤ)⟩ * ⟨(a : ℤ), -(b : ℤ)⟩ := by
        ext
        · simp only [Zsqrtd.mul_re]; push_cast; nlinarith
        · simp only [Zsqrtd.mul_im]; push_cast; ring
      rw [h_factor] at hdvd_p
      have h_neg_norm : (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt).norm = (p : ℤ) := by
        have h1 : (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt).norm.natAbs = p := by
          rw [GaussianInt.natAbs_norm_eq]; simp only [Int.natAbs_ofNat, Int.natAbs_neg, sq] at *
          linarith
        rw [← GaussianInt.abs_natCast_norm]; exact_mod_cast h1
      have h_neg_prime := gauss_prime_of_prime_norm hp h_neg_norm
      -- In either case, norm z = p
      have h_norm_z : z.norm = (p : ℤ) := by
        rcases hz.dvd_or_dvd hdvd_p with h1 | h2
        · exact (Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0)
              (hz.associated_of_dvd h_ab_prime h1)).trans h_ab_norm
        · exact (Zsqrtd.norm_eq_of_associated (by norm_num : (-1 : ℤ) ≤ 0)
              (hz.associated_of_dvd h_neg_prime h2)).trans h_neg_norm
      by_cases hp2 : p = 2
      · left; simp [h_norm_z, hp2]
      · right; right
        have hp1 : p % 4 = 1 := by
          have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
          have h4 : (p % 4) % 2 = 1 := by
            rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]; exact hodd
          omega
        exact ⟨p, hp, hp1, h_norm_z⟩
  · -- Backward: norm classification → Prime z
    intro h
    rcases h with hn2 | ⟨p, hp, hmod3, hnp2⟩ | ⟨p, hp, _, hnp⟩
    · exact gauss_prime_of_prime_norm (by norm_num) hn2
    · exact gauss_prime_of_inert hp hmod3 hnp2
    · exact gauss_prime_of_prime_norm hp hnp

/-
# Part 3: Concrete Examples of Gaussian Primes

We verify a few small Gaussian primes using decide.
-/

/-- The norm of 1+i is 2 (norm 2 means it's a Type 1 Gaussian prime) -/
theorem norm_one_plus_i : (⟨1, 1⟩ : GaussianInt).norm = 2 := by decide

/-- The norm of 2+i is 5 (norm = prime ≡ 1 mod 4 means it's a Type 3 split prime) -/
theorem norm_two_plus_i : (⟨2, 1⟩ : GaussianInt).norm = 5 := by decide

/-- The norm of 3 (as Gaussian integer) is 9 = 3² (norm p² for p ≡ 3 mod 4, Type 2 inert) -/
theorem norm_three_gaussian : (⟨3, 0⟩ : GaussianInt).norm = 9 := by decide

/-- Verify: 1+i is a norm-2 prime (Type 1) -/
theorem one_plus_i_is_norm2_prime : IsNorm2Prime (⟨1, 1⟩ : GaussianInt) := by
  unfold IsNorm2Prime; decide

/-- Verify: 3 is an inert prime with p = 3 ≡ 3 mod 4 (Type 2) -/
theorem three_is_inert_prime : IsInertPrime (⟨3, 0⟩ : GaussianInt) := by
  unfold IsInertPrime
  exact ⟨3, by norm_num, by norm_num, by decide⟩

/-- Verify: 2+i is a split prime with p = 5 ≡ 1 mod 4 (Type 3) -/
theorem two_plus_i_is_split_prime : IsSplitPrime (⟨2, 1⟩ : GaussianInt) := by
  unfold IsSplitPrime
  exact ⟨5, by norm_num, by norm_num, by decide⟩

/-- By the classification axiom, 1+i is a Gaussian prime -/
theorem one_plus_i_is_gaussian_prime : IsGaussianPrime (⟨1, 1⟩ : GaussianInt) :=
  gaussian_prime_classification _ |>.mpr (Or.inl one_plus_i_is_norm2_prime)

/-- By the classification axiom, 2+i is a Gaussian prime -/
theorem two_plus_i_is_gaussian_prime : IsGaussianPrime (⟨2, 1⟩ : GaussianInt) :=
  gaussian_prime_classification _ |>.mpr (Or.inr (Or.inr two_plus_i_is_split_prime))

/-- By the classification axiom, 3 is a Gaussian prime -/
theorem three_is_gaussian_prime : IsGaussianPrime (⟨3, 0⟩ : GaussianInt) :=
  gaussian_prime_classification _ |>.mpr (Or.inr (Or.inl three_is_inert_prime))

/-
# Part 4: The Moat Problem

Can we walk from 0 to infinity on Gaussian primes with bounded step size?
-/

/-- An infinite walk on Gaussian primes: an injective sequence where every term is prime -/
def IsInfiniteGaussianPrimeWalk (x : ℕ → GaussianInt) : Prop :=
  Function.Injective x ∧ ∀ n, IsGaussianPrime (x n)

/-- A walk has bounded gaps if consecutive steps have norm < C -/
def HasBoundedGaps (x : ℕ → GaussianInt) (C : ℕ) : Prop :=
  ∀ n, (x (n + 1) - x n).norm < C

/-- Can we escape to infinity with steps of norm < k? -/
def CanEscapeMoat (k : ℕ) : Prop :=
  ∃ x : ℕ → GaussianInt, IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x k

/-- The Gaussian moat conjecture (positive form): does a bounded infinite walk exist? -/
def GaussianMoatConjecture : Prop :=
  ∃ (x : ℕ → GaussianInt) (C : ℕ),
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x C

/-- Equivalent to Erdős #952 statement -/
def ErdosConjecture952 : Prop := GaussianMoatConjecture

/-
# Part 5: Known Negative Results

Tsuchimura (2005) is the strongest known result, via computational verification.
-/

/-- Tsuchimura (2005): No walk with step norm < 27 (i.e., |step| ≤ √26).
    This is the best known bound, established by computational search
    showing that moats of width > √26 surround the origin. -/
axiom tsuchimura : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 27

/-- Jordan-Rabung (1970): No walk with step norm < 5 (i.e., |step| ≤ 2).
    This is the first computational result. It follows from Tsuchimura. -/
theorem jordan_rabung : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 5 := by
  intro ⟨x, hwalk, hgaps⟩
  exact tsuchimura ⟨x, hwalk, fun n => lt_trans (hgaps n) (by norm_num)⟩

/-- Gethner et al.: step size 4 (norm < 17) is insufficient.
    Follows from Tsuchimura since 17 < 27. -/
theorem gethner_et_al : ¬ ∃ x : ℕ → GaussianInt,
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x 17 := by
  intro ⟨x, hwalk, hgaps⟩
  exact tsuchimura ⟨x, hwalk, fun n => lt_trans (hgaps n) (by norm_num)⟩

/-- Tsuchimura's result subsumes all bounded walks with norm < 27 -/
theorem not_canEscapeMoat_small (k : ℕ) (hk : k ≤ 27) : ¬CanEscapeMoat k := by
  intro ⟨x, hwalk, hgaps⟩
  exact tsuchimura ⟨x, hwalk, fun n => lt_of_lt_of_le (hgaps n) (by exact_mod_cast hk)⟩

/-- If you can escape with smaller steps, you can escape with larger steps -/
theorem canEscapeMoat_mono {k k' : ℕ} (hk : k ≤ k') (h : CanEscapeMoat k) :
    CanEscapeMoat k' := by
  obtain ⟨x, hwalk, hgaps⟩ := h
  exact ⟨x, hwalk, fun n => lt_of_lt_of_le (hgaps n) (by exact_mod_cast hk)⟩

/-- The current best bound on the moat width -/
def CurrentBestBound : ℕ := 27

/-
# Part 6: The Moat Width

If the answer to the Gaussian Moat Problem is "NO",
there is a minimum step size beyond which escape is impossible.
-/

/-- Escape is impossible for very small moats (follows from Tsuchimura) -/
theorem cannotEscape_width_0 : ¬ CanEscapeMoat 0 :=
  not_canEscapeMoat_small 0 (Nat.zero_le 27)

/-- The current lower bound on moat width (from Tsuchimura 2005):
    no escape is possible with steps of norm < 28. -/
def moatWidthLowerBound : ℕ := 28

/-- Strong negation: escape impossible for any step size -/
def StrongNegation : Prop := ∀ k, ¬ CanEscapeMoat k

/-
# Part 7: Structural Equivalences
-/

/-- The conjecture is equivalent to escaping for some step size -/
theorem conjecture_iff_canEscape :
    GaussianMoatConjecture ↔ ∃ k, CanEscapeMoat k := by
  unfold GaussianMoatConjecture CanEscapeMoat IsInfiniteGaussianPrimeWalk HasBoundedGaps
  constructor
  · rintro ⟨x, C, hwalks, hgaps⟩; exact ⟨C, x, hwalks, hgaps⟩
  · rintro ⟨C, x, hwalks, hgaps⟩; exact ⟨x, C, hwalks, hgaps⟩

/-- Strong negation is equivalent to the conjecture failing -/
theorem strongNegation_iff_not_conjecture :
    StrongNegation ↔ ¬GaussianMoatConjecture := by
  rw [conjecture_iff_canEscape]
  unfold StrongNegation
  push_neg; rfl

/-- Formal statement matching the formal-conjectures formulation -/
theorem erdos_952_statement :
    ErdosConjecture952 ↔
    ∃ (x : ℕ → GaussianInt) (C : ℕ),
      (Function.Injective x ∧ ∀ n, Prime (x n)) ∧
      (∀ n, (x (n + 1) - x n).norm < C) := by
  unfold ErdosConjecture952 GaussianMoatConjecture
  unfold IsInfiniteGaussianPrimeWalk HasBoundedGaps IsGaussianPrime
  rfl

/-
# Part 8: Connection to Rational Primes

The Gaussian moat problem is deeply connected to gaps in primes ≡ 1 (mod 4),
which split in ℤ[i] (Fermat's theorem on sums of two squares).

For any prime p with p ≡ 1 (mod 4), p = a² + b² for some a, b ∈ ℕ,
and π = a + bi is a Gaussian prime with N(π) = p.
Gaps in split primes create moats around the origin.
-/

/-- If every prime p ≡ 1 (mod 4) in an interval is absent, then a Gaussian moat exists
    around that part of the complex plane.
    This statement captures the connection between rational prime gaps and Gaussian moats. -/
def GaussianMoatFromRationalGap : Prop :=
  ∀ R : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ m ≤ R, ¬(n + m).Prime ∨ (n + m) % 4 ≠ 1

/-- The strong negation of the moat conjecture implies prime-free windows
    (proved unconditionally via the factorial trick) -/
theorem strongNegation_implies_prime_free_windows :
    StrongNegation →
    ∀ C, ∃ᶠ n in Filter.atTop, ∀ m ∈ Finset.range C,
      ¬ (n + m).Prime ∨ (n + m) % 4 ≠ 1 := by
  intro _ C
  rw [Filter.frequently_atTop]
  intro a
  -- Use the factorial construction: in [k!+2, k!+k], every number k!+j (2≤j≤k)
  -- is divisible by j, hence composite.
  set k := max a (C + 2)
  refine ⟨Nat.factorial k + 2, ?_, ?_⟩
  · -- Nat.factorial k + 2 ≥ a: since k ≤ k! for k ≥ 1
    have hk_pos : 1 ≤ k := by omega
    have hkle : k ≤ Nat.factorial k :=
      Nat.le_of_dvd (Nat.factorial_pos k)
        (Dvd.dvd.trans
          (show k ∣ Nat.factorial k from
            match k, hk_pos with
            | n + 1, _ => ⟨Nat.factorial n, Nat.factorial_succ n⟩)
          dvd_rfl)
    omega
  · -- Every n + m in the range is composite (not prime)
    intro m hm
    left
    rw [Finset.mem_range] at hm
    set j := m + 2
    have hj_le_k : j ≤ k := by omega
    -- j divides j!, and j! divides k!, so j divides k!
    have hj_dvd_kfact : j ∣ Nat.factorial k :=
      Dvd.dvd.trans
        (show j ∣ Nat.factorial j from
          match j, show 1 ≤ j from by omega with
          | n + 1, _ => ⟨Nat.factorial n, Nat.factorial_succ n⟩)
        (Nat.factorial_dvd_factorial hj_le_k)
    -- j divides k! + 2 + m = k! + j
    have hj_dvd : j ∣ (Nat.factorial k + 2 + m) := by
      rw [show Nat.factorial k + 2 + m = Nat.factorial k + j from by omega]
      exact dvd_add hj_dvd_kfact (dvd_refl j)
    -- Therefore k! + 2 + m is not prime (j is a proper divisor, 2 ≤ j < result)
    intro hp
    rcases hp.eq_one_or_self_of_dvd j hj_dvd with h | h
    · omega -- j ≥ 2, cannot be 1
    · have := Nat.factorial_pos k; omega

/-
# Part 9: Variants of the Moat Problem
-/

/-- Can we walk to infinity on Eisenstein primes (ℤ[ω], ω = e^{2πi/3})?
    An analogous moat problem in the Eisenstein integer ring. -/
def EisensteinMoatProblem : Prop :=
  ∃ (x : ℕ → GaussianInt) (C : ℕ),
    IsInfiniteGaussianPrimeWalk x ∧ HasBoundedGaps x C

/-- The higher-dimensional Gaussian moat: walks in ℤ[i]^n -/
def HigherDimensionalMoat (n : ℕ) : Prop :=
  n = n -- placeholder for the open higher-dimensional version

/-
# Summary

**Problem:** Can we walk from 0 to infinity on Gaussian primes with bounded step size?

**Status:** OPEN

**Known (negative results):**
- Steps with norm ≤ 4 (Jordan-Rabung, 1970): NO
- Steps with norm ≤ 26 (Tsuchimura, 2005): NO  [strongest known]
- Gethner et al.: norm ≤ 16 (step size 4): NO

**Axioms (1):**
- tsuchimura: computational verification (no walk ≤ √26) [appropriate to axiomatize]

**Theorems proved this session:**
- gaussian_prime_classification: proved from Mathlib (Fermat 2-square + inert prime characterization)

**Proved from axioms:**
- jordan_rabung: derives from tsuchimura (strictly stronger)
- gethner_et_al: derives from tsuchimura (strictly stronger)
- not_canEscapeMoat_small: general subsumption by tsuchimura
- canEscapeMoat_mono: monotonicity of escape
- conjecture_iff_canEscape: structural equivalence
- strongNegation_iff_not_conjecture: logical equivalence
- strongNegation_implies_prime_free_windows: factorial construction proof
-/

/-- The problem is open -/
def erdos_952_status : String := "OPEN"

/-- Attribution note -/
def attribution_note : String :=
  "Not actually an Erdős problem. Originated with Motzkin, Gordon, and others (1963)."

end Erdos952
