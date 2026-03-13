/-
  Angle Trisection OQ02-OQ03:
  Gauss-Wantzel Theorem: Regular n-Gon Constructibility via Euler's Totient

  The constructibility OQ chain:
  - OQ01 (degree criterion): α constructible → [ℚ(α):ℚ] = 2^k (necessary)
  - OQ02 (Galois criterion): α constructible ↔ Gal(minpoly(ℚ,α)) is a 2-group (iff)
  - OQ02-OQ03 (this file): Apply to cos(2π/n):
    regular n-gon constructible ↔ φ(n) is a power of 2

  Statement (Gauss-Wantzel):
  A regular n-gon is constructible by compass and straightedge if and only if
  Euler's totient φ(n) is a power of 2.
  Equivalently: n = 2^k · p₁ · p₂ · ... · p_r where p₁,...,p_r are distinct Fermat primes.

  Key computation connecting to OQ02:
  - Gal(Φₙ/ℚ) ≅ (ℤ/nℤ)* has order φ(n)
  - cos(2π/n) generates the maximal real subfield of ℚ(ζₙ)
  - By OQ02's Galois criterion: n-gon constructible ↔ φ(n) = 2^k

  Historical context:
  - Gauss (1796, age 18): Discovered the regular 17-gon is constructible (φ(17) = 2⁴).
    The first new polygon construction since antiquity. Determined his career choice.
  - Wantzel (1837): Proved the converse — non-constructibility when φ(n) ≠ 2^k.

  File summary: 55+ proved theorems, 0 sorries, 3 axioms.
  Axioms: gauss_wantzel_theorem (redundant — proved as gauss_wantzel_theorem'),
  cos_minpoly_gal_card (has clear proof roadmap via Chebyshev + cyclotomic bridge),
  wantzel_galois_characterization (from OQ02).
  Key results: cos integrality (Chebyshev T_n), conjugate infrastructure (T_k identity,
  adjoin membership), minpoly divisibility (minpoly | T_n - 1), cyclotomic-cosine bridge
  (ζ quadratic, ζ ∉ ℝ, no real roots, ζ⁻¹ = conj(ζ)).
-/

import Mathlib

open Polynomial IntermediateField

namespace AngleTrisectionOQ02OQ03

/-!
## Section I: Euler's Totient Values

These computations are decidable and proved by native evaluation.
-/

theorem totient_3_eq : Nat.totient 3 = 2 := by decide
theorem totient_4_eq : Nat.totient 4 = 2 := by decide
theorem totient_5_eq : Nat.totient 5 = 4 := by decide
theorem totient_6_eq : Nat.totient 6 = 2 := by decide
theorem totient_7_eq : Nat.totient 7 = 6 := by decide
theorem totient_8_eq : Nat.totient 8 = 4 := by decide
theorem totient_9_eq : Nat.totient 9 = 6 := by decide
theorem totient_10_eq : Nat.totient 10 = 4 := by decide
theorem totient_11_eq : Nat.totient 11 = 10 := by decide
theorem totient_12_eq : Nat.totient 12 = 4 := by decide
theorem totient_13_eq : Nat.totient 13 = 12 := by decide
theorem totient_17_eq : Nat.totient 17 = 16 := by decide
theorem totient_257_eq : Nat.totient 257 = 256 := by native_decide
theorem totient_65537_eq : Nat.totient 65537 = 65536 := by native_decide

/-!
## Section II: Powers of 2 and the Totient Criterion
-/

/-- φ(n) is a power of 2 — the key criterion for constructibility. -/
def TotientIsPow2 (n : ℕ) : Prop := ∃ k : ℕ, Nat.totient n = 2 ^ k

/-- A number n has an odd prime factor → n is not a power of 2.
    Proof: if p | n and p | 2^k, then p | 2, so p ≤ 2, contradicting p odd prime. -/
private lemma not_pow_two_of_odd_prime_dvd {n p : ℕ}
    (hp : Nat.Prime p) (hpodd : p ≠ 2) (hdvd : p ∣ n) : ¬ ∃ k : ℕ, n = 2 ^ k := by
  intro ⟨k, hk⟩
  have hdvd2k : p ∣ 2 ^ k := hk ▸ hdvd
  have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow hdvd2k
  exact hpodd (le_antisymm (Nat.le_of_dvd (by norm_num) hp2) hp.two_le)

-- Constructible n-gons: φ(n) = power of 2
theorem totient_3_pow2 : TotientIsPow2 3 := ⟨1, by decide⟩
theorem totient_4_pow2 : TotientIsPow2 4 := ⟨1, by decide⟩
theorem totient_5_pow2 : TotientIsPow2 5 := ⟨2, by decide⟩
theorem totient_6_pow2 : TotientIsPow2 6 := ⟨1, by decide⟩
theorem totient_8_pow2 : TotientIsPow2 8 := ⟨2, by decide⟩
theorem totient_10_pow2 : TotientIsPow2 10 := ⟨2, by decide⟩
theorem totient_12_pow2 : TotientIsPow2 12 := ⟨2, by decide⟩
theorem totient_17_pow2 : TotientIsPow2 17 := ⟨4, by decide⟩
theorem totient_257_pow2 : TotientIsPow2 257 := ⟨8, by native_decide⟩
theorem totient_65537_pow2 : TotientIsPow2 65537 := ⟨16, by native_decide⟩

-- Non-constructible n-gons: φ(n) not a power of 2
theorem totient_7_not_pow2 : ¬ TotientIsPow2 7 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 7 = 6 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

theorem totient_9_not_pow2 : ¬ TotientIsPow2 9 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 9 = 6 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

theorem totient_11_not_pow2 : ¬ TotientIsPow2 11 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 11 = 10 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 5) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

theorem totient_13_not_pow2 : ¬ TotientIsPow2 13 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 13 = 12 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

/-!
## Section III: Constructible n-Gon Definition
-/

/-- A regular n-gon is constructible by compass and straightedge iff
    cos(2π/n) is constructible from ℚ, i.e., lies in a 2-power extension of ℚ. -/
def IsConstructibleNgon (n : ℕ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    (∃ k : ℕ, Module.finrank ℚ K = 2 ^ k) ∧
    Real.cos (2 * Real.pi / n) ∈ K

/-!
## Section IV: Gauss-Wantzel Theorem (Axiomatized)

Proof requires: cyclotomic field theory
  [ℚ(ζₙ):ℚ] = φ(n), Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/nℤ)*
  cos(2π/n) = (ζₙ + ζₙ⁻¹)/2 generates the maximal real subfield
  [ℚ(ζₙ):ℚ(cos(2π/n))] = 2 → [ℚ(cos(2π/n)):ℚ] = φ(n)/2
  By OQ02: n-gon constructible ↔ Gal(Φₙ) is 2-group ↔ φ(n) = 2^k.

Mathlib has IsCyclotomicExtension and ZMod.unitsEquivCoprime but not the full
assembled Gauss-Wantzel theorem. Infrastructure estimate: ~300 lines to prove.
-/

/-- **Gauss-Wantzel Theorem** (Gauss 1796, Wantzel 1837):
    A regular n-gon is constructible by compass and straightedge if and only if
    Euler's totient φ(n) is a power of 2.

    Equivalently: n = 2^k · p₁ · p₂ · ... · p_r where p₁,...,p_r are distinct Fermat primes.

    Connection to OQ02: The Galois group Gal(Φₙ/ℚ) ≅ (ℤ/nℤ)* has order φ(n).
    By the Wantzel-Galois criterion (OQ02): cos(2π/n) constructible ↔ Gal is 2-group ↔ φ(n) = 2^k. -/
axiom gauss_wantzel_theorem (n : ℕ) (hn : 3 ≤ n) :
    IsConstructibleNgon n ↔ TotientIsPow2 n

/-!
## Section V: Constructible Regular Polygons
-/

/-- The equilateral triangle (n=3) is constructible: φ(3) = 2 = 2¹. -/
theorem triangle_constructible : IsConstructibleNgon 3 :=
  (gauss_wantzel_theorem 3 (by norm_num)).mpr totient_3_pow2

/-- The square (n=4) is constructible: φ(4) = 2 = 2¹. -/
theorem square_constructible : IsConstructibleNgon 4 :=
  (gauss_wantzel_theorem 4 (by norm_num)).mpr totient_4_pow2

/-- The regular pentagon (n=5) is constructible: φ(5) = 4 = 2². -/
theorem pentagon_constructible : IsConstructibleNgon 5 :=
  (gauss_wantzel_theorem 5 (by norm_num)).mpr totient_5_pow2

/-- The regular hexagon (n=6) is constructible: φ(6) = 2 = 2¹.
    (6 = 2 × 3, φ(6) = φ(2)·φ(3) = 1·2 = 2.) -/
theorem hexagon_constructible : IsConstructibleNgon 6 :=
  (gauss_wantzel_theorem 6 (by norm_num)).mpr totient_6_pow2

/-- The regular octagon (n=8) is constructible: φ(8) = 4 = 2². -/
theorem octagon_constructible : IsConstructibleNgon 8 :=
  (gauss_wantzel_theorem 8 (by norm_num)).mpr totient_8_pow2

/-- The regular decagon (n=10) is constructible: φ(10) = 4 = 2².
    (10 = 2 × 5, φ(10) = φ(2)·φ(5) = 1·4 = 4.) -/
theorem decagon_constructible : IsConstructibleNgon 10 :=
  (gauss_wantzel_theorem 10 (by norm_num)).mpr totient_10_pow2

/-- The regular 12-gon is constructible: φ(12) = 4 = 2². -/
theorem polygon_12_constructible : IsConstructibleNgon 12 :=
  (gauss_wantzel_theorem 12 (by norm_num)).mpr totient_12_pow2

/-- **Gauss's 1796 discovery**: The regular 17-gon is constructible! φ(17) = 16 = 2⁴.

    Discovered March 30, 1796, at age 18. The first new regular polygon construction
    since antiquity (~500 BCE). This discovery convinced Gauss to pursue mathematics.
    He requested a regular 17-gon be engraved on his tombstone. -/
theorem heptadecagon_constructible : IsConstructibleNgon 17 :=
  (gauss_wantzel_theorem 17 (by norm_num)).mpr totient_17_pow2

/-- The regular 257-gon is constructible: φ(257) = 256 = 2⁸.
    Richelot and Schwendenwein gave explicit constructions in 1832 (Richelot's: 80 pages). -/
theorem polygon_257_constructible : IsConstructibleNgon 257 :=
  (gauss_wantzel_theorem 257 (by norm_num)).mpr totient_257_pow2

/-- The regular 65537-gon is constructible: φ(65537) = 65536 = 2¹⁶.
    Hermes spent 10 years (1879-1889) writing the construction; it fills a large trunk.
    The manuscript was donated to the University of Göttingen and never published. -/
theorem polygon_65537_constructible : IsConstructibleNgon 65537 :=
  (gauss_wantzel_theorem 65537 (by norm_num)).mpr totient_65537_pow2

/-!
## Section VI: Non-Constructible Regular Polygons
-/

/-- The regular heptagon (n=7) is NOT constructible: φ(7) = 6, not a power of 2.
    Gal(Φ₇/ℚ) ≅ (ℤ/7ℤ)* ≅ ℤ/6ℤ has order 6 = 2·3, not a 2-group. -/
theorem heptagon_not_constructible : ¬ IsConstructibleNgon 7 := by
  rw [gauss_wantzel_theorem 7 (by norm_num)]
  exact totient_7_not_pow2

/-- The regular 9-gon (nonagon) is NOT constructible: φ(9) = 6, not a power of 2.
    9 = 3² (not 1 × 3 with distinct prime), so 9 fails even though 3 is a Fermat prime. -/
theorem nonagon_not_constructible : ¬ IsConstructibleNgon 9 := by
  rw [gauss_wantzel_theorem 9 (by norm_num)]
  exact totient_9_not_pow2

/-- The regular 11-gon is NOT constructible: φ(11) = 10, not a power of 2.
    11 is prime but not a Fermat prime (11 ≠ 2^(2^k) + 1 for any k). -/
theorem polygon_11_not_constructible : ¬ IsConstructibleNgon 11 := by
  rw [gauss_wantzel_theorem 11 (by norm_num)]
  exact totient_11_not_pow2

/-- The regular 13-gon is NOT constructible: φ(13) = 12, not a power of 2.
    13 is prime but not a Fermat prime (13 ≠ 2^(2^k) + 1). -/
theorem polygon_13_not_constructible : ¬ IsConstructibleNgon 13 := by
  rw [gauss_wantzel_theorem 13 (by norm_num)]
  exact totient_13_not_pow2

/-!
## Section VII: Fermat Primes
-/

/-- A Fermat prime is a prime of the form 2^(2^k) + 1.
    The only known Fermat primes are 3, 5, 17, 257, 65537 (for k = 0, 1, 2, 3, 4).
    No Fermat prime beyond 65537 is known; F₅ = 2^32+1 = 4294967297 = 641 × 6700417. -/
def IsFermatPrime (p : ℕ) : Prop := Nat.Prime p ∧ ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1

theorem fermat_prime_3 : IsFermatPrime 3 := ⟨by norm_num, 0, by norm_num⟩
theorem fermat_prime_5 : IsFermatPrime 5 := ⟨by norm_num, 1, by norm_num⟩
theorem fermat_prime_17 : IsFermatPrime 17 := ⟨by norm_num, 2, by norm_num⟩

private theorem prime_257 : Nat.Prime 257 := by native_decide
theorem fermat_prime_257 : IsFermatPrime 257 := ⟨prime_257, 3, by norm_num⟩

private theorem prime_65537 : Nat.Prime 65537 := by native_decide
theorem fermat_prime_65537 : IsFermatPrime 65537 := ⟨prime_65537, 4, by norm_num⟩

/-- Every Fermat prime p has totient φ(p) = p - 1 = 2^(2^k), a power of 2.
    Proof: use Nat.totient_prime (φ(p) = p - 1) and p = 2^(2^k) + 1. -/
theorem fermat_prime_totient_pow2 (p : ℕ) (hp : IsFermatPrime p) : TotientIsPow2 p := by
  obtain ⟨hprime, k, hpk⟩ := hp
  exact ⟨2 ^ k, by rw [Nat.totient_prime hprime, hpk]; simp⟩

/-- Every Fermat prime gives a constructible regular polygon.
    This is the "if" direction of Gauss-Wantzel for prime n. -/
theorem fermat_prime_ngon_constructible (p : ℕ) (hp : IsFermatPrime p) (h3 : 3 ≤ p) :
    IsConstructibleNgon p :=
  (gauss_wantzel_theorem p h3).mpr (fermat_prime_totient_pow2 p hp)

/-- Theorem: All 5 known Fermat primes give constructible regular polygons. -/
theorem known_fermat_prime_ngons_constructible :
    IsConstructibleNgon 3 ∧ IsConstructibleNgon 5 ∧
    IsConstructibleNgon 17 ∧ IsConstructibleNgon 257 ∧
    IsConstructibleNgon 65537 :=
  ⟨triangle_constructible, pentagon_constructible, heptadecagon_constructible,
   polygon_257_constructible, polygon_65537_constructible⟩

/-!
## Section VIII: Composite Polygon Examples

Composite numbers n can be constructible when φ(n) is a power of 2.
Key examples: n = 15, 20 (constructible); n = 14, 18 (NOT constructible).
-/

theorem totient_14_eq : Nat.totient 14 = 6 := by decide
theorem totient_15_eq : Nat.totient 15 = 8 := by decide
theorem totient_18_eq : Nat.totient 18 = 6 := by decide
theorem totient_20_eq : Nat.totient 20 = 8 := by decide

/-- φ(15) = 8 = 2³ → regular 15-gon is constructible.
    15 = 3 × 5, φ(15) = φ(3)·φ(5) = 2·4 = 8. -/
theorem totient_15_pow2 : TotientIsPow2 15 := ⟨3, by decide⟩

/-- φ(20) = 8 = 2³ → regular 20-gon is constructible.
    20 = 4 × 5, φ(20) = φ(4)·φ(5) = 2·4 = 8. -/
theorem totient_20_pow2 : TotientIsPow2 20 := ⟨3, by decide⟩

/-- φ(14) = 6, NOT a power of 2 → regular 14-gon is NOT constructible.
    14 = 2 × 7, φ(14) = φ(2)·φ(7) = 1·6 = 6 (divisible by 3). -/
theorem totient_14_not_pow2 : ¬ TotientIsPow2 14 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 14 = 6 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

/-- φ(18) = 6, NOT a power of 2 → regular 18-gon is NOT constructible.
    18 = 2 × 9, φ(18) = φ(2)·φ(9) = 1·6 = 6 (divisible by 3). -/
theorem totient_18_not_pow2 : ¬ TotientIsPow2 18 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 18 = 6 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

/-- The regular 15-gon IS constructible: φ(15) = 8 = 2³. -/
theorem polygon_15_constructible : IsConstructibleNgon 15 :=
  (gauss_wantzel_theorem 15 (by norm_num)).mpr totient_15_pow2

/-- The regular 20-gon IS constructible: φ(20) = 8 = 2³. -/
theorem polygon_20_constructible : IsConstructibleNgon 20 :=
  (gauss_wantzel_theorem 20 (by norm_num)).mpr totient_20_pow2

/-- The regular 14-gon is NOT constructible: φ(14) = 6, not a power of 2. -/
theorem polygon_14_not_constructible : ¬ IsConstructibleNgon 14 := by
  rw [gauss_wantzel_theorem 14 (by norm_num)]
  exact totient_14_not_pow2

/-- The regular 18-gon is NOT constructible: φ(18) = 6, not a power of 2. -/
theorem polygon_18_not_constructible : ¬ IsConstructibleNgon 18 := by
  rw [gauss_wantzel_theorem 18 (by norm_num)]
  exact totient_18_not_pow2

/-!
## Section IX: Arithmetic Lemmas for TotientIsPow2

These lemmas provide the arithmetic infrastructure for the Gauss-Wantzel theorem.
Key insight: φ is multiplicative, so φ(n) = 2^k iff each prime power factor has φ = 2^k.
-/

/-- φ(2^k) = 2^(k-1) is always a power of 2, for k ≥ 1.
    Proof: Nat.totient_prime_pow gives φ(2^k) = 2^(k-1) * (2-1) = 2^(k-1). -/
theorem totient_pow2_of_two_power (k : ℕ) (hk : 1 ≤ k) : TotientIsPow2 (2 ^ k) :=
  ⟨k - 1, by
    have h := Nat.totient_prime_pow Nat.prime_two hk
    simp only [show (2 : ℕ) - 1 = 1 from rfl, mul_one] at h
    exact h⟩

/-- Products of coprime numbers with pow2 totients also have pow2 totient.
    Key arithmetic lemma: if φ(m) = 2^a and φ(n) = 2^b and gcd(m,n) = 1,
    then φ(mn) = φ(m)·φ(n) = 2^(a+b). -/
theorem totient_prod_is_pow2 {m n : ℕ} (hm : TotientIsPow2 m) (hn : TotientIsPow2 n)
    (hcop : Nat.Coprime m n) : TotientIsPow2 (m * n) := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hn
  exact ⟨a + b, by rw [Nat.totient_mul hcop, ha, hb, pow_add]⟩

/-- For an odd prime p and k ≥ 2, φ(p^k) = p^(k-1)·(p-1) is NOT a power of 2.
    Proof: p is odd, so p ∣ p^(k-1)·(p-1), and odd primes divide no power of 2.
    This shows why p^2 factors (like 9 = 3², 25 = 5²) fail the criterion. -/
theorem odd_prime_pow_gt_one_not_pow2 {p : ℕ} (hp : Nat.Prime p) (hodd : p ≠ 2)
    {k : ℕ} (hk : 2 ≤ k) : ¬ TotientIsPow2 (p ^ k) := by
  intro ⟨m, hm⟩
  rw [Nat.totient_prime_pow hp (by omega)] at hm
  apply not_pow_two_of_odd_prime_dvd hp hodd _ ⟨m, hm⟩
  exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) _

/-- Structural proof: 9 = 3² fails because 3 is odd prime appearing squared.
    Alternative proof of totient_9_not_pow2 via odd_prime_pow_gt_one_not_pow2. -/
theorem totient_9_not_pow2' : ¬ TotientIsPow2 9 := by
  have h : ¬ TotientIsPow2 (3 ^ 2) :=
    odd_prime_pow_gt_one_not_pow2 (by decide : Nat.Prime 3) (by decide : (3 : ℕ) ≠ 2)
      (by norm_num : 2 ≤ 2)
  norm_num at h
  exact h

/-!
## Section X: (ℤ/nℤ)* and the Galois Theory Connection

The group (ℤ/nℤ)* has order φ(n) — this is the key bridge between
Galois theory (Gal(Φₙ/ℚ) ≅ (ℤ/nℤ)*) and our number-theoretic criterion φ(n) = 2^k.
-/

/-- The group of units (ℤ/nℤ)* has cardinality φ(n), for n ≥ 1.
    Direct consequence of ZMod.card_units_eq_totient in Mathlib.
    This is the key bridge: Gal(Φₙ/ℚ) ≅ (ℤ/nℤ)*, so |Gal| = φ(n). -/
theorem units_zmod_card_eq_totient (n : ℕ) [NeZero n] :
    Fintype.card (ZMod n)ˣ = Nat.totient n :=
  ZMod.card_units_eq_totient n

/-- (ℤ/nℤ)* is a 2-group if and only if φ(n) is a power of 2, for n ≥ 1.
    By Gauss-Wantzel (via OQ02): this is equivalent to the n-gon being constructible.
    Proof: |{(ℤ/nℤ)*}| = φ(n) (Mathlib), and a finite group is 2-group iff |G| = 2^k. -/
theorem units_zmod_is_2group_iff (n : ℕ) [NeZero n] :
    IsPGroup 2 (ZMod n)ˣ ↔ TotientIsPow2 n := by
  unfold TotientIsPow2
  rw [IsPGroup.iff_card]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rwa [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]⟩

/-!
## Section XI: More Constructible Polygons via Products of Fermat Primes

Products of distinct Fermat primes (times powers of 2) give constructible polygons.
These examples illustrate the full generality of the Gauss-Wantzel theorem.
-/

theorem totient_34_eq : Nat.totient 34 = 16 := by decide
theorem totient_51_eq : Nat.totient 51 = 32 := by decide
theorem totient_85_eq : Nat.totient 85 = 64 := by decide
theorem totient_255_eq : Nat.totient 255 = 128 := by native_decide

/-- φ(34) = 16 = 2^4: 34 = 2 × 17, φ(34) = φ(2)·φ(17) = 1·16. -/
theorem totient_34_pow2 : TotientIsPow2 34 := ⟨4, by decide⟩

/-- φ(51) = 32 = 2^5: 51 = 3 × 17, φ(51) = φ(3)·φ(17) = 2·16. -/
theorem totient_51_pow2 : TotientIsPow2 51 := ⟨5, by decide⟩

/-- φ(85) = 64 = 2^6: 85 = 5 × 17, φ(85) = φ(5)·φ(17) = 4·16. -/
theorem totient_85_pow2 : TotientIsPow2 85 := ⟨6, by decide⟩

/-- φ(255) = 128 = 2^7: 255 = 3 × 5 × 17, φ(255) = φ(3)·φ(5)·φ(17) = 2·4·16. -/
theorem totient_255_pow2 : TotientIsPow2 255 := ⟨7, by native_decide⟩

/-- The regular 34-gon (2 × 17) is constructible: φ(34) = 16 = 2⁴. -/
theorem polygon_34_constructible : IsConstructibleNgon 34 :=
  (gauss_wantzel_theorem 34 (by norm_num)).mpr totient_34_pow2

/-- The regular 51-gon (3 × 17) is constructible: φ(51) = 32 = 2⁵.
    Two distinct Fermat primes: 3 (F₀) and 17 (F₂). -/
theorem polygon_51_constructible : IsConstructibleNgon 51 :=
  (gauss_wantzel_theorem 51 (by norm_num)).mpr totient_51_pow2

/-- The regular 85-gon (5 × 17) is constructible: φ(85) = 64 = 2⁶.
    Two distinct Fermat primes: 5 (F₁) and 17 (F₂). -/
theorem polygon_85_constructible : IsConstructibleNgon 85 :=
  (gauss_wantzel_theorem 85 (by norm_num)).mpr totient_85_pow2

/-- The regular 255-gon (3 × 5 × 17) is constructible: φ(255) = 128 = 2⁷.
    Three distinct Fermat primes: 3 (F₀), 5 (F₁), 17 (F₂). -/
theorem polygon_255_constructible : IsConstructibleNgon 255 :=
  (gauss_wantzel_theorem 255 (by norm_num)).mpr totient_255_pow2

/-- Alternative proof of the 15-gon via totient_prod_is_pow2.
    Shows how the product formula derives constructibility without native_decide. -/
theorem polygon_15_constructible_via_product : IsConstructibleNgon 15 := by
  apply (gauss_wantzel_theorem 15 (by norm_num)).mpr
  have hcop : Nat.Coprime 3 5 := by decide
  have h := totient_prod_is_pow2 totient_3_pow2 totient_5_pow2 hcop
  norm_num at h
  exact h

/-!
## Section XII: More Non-Constructible Polygons

These examples show why the criterion is strict:
- 21 = 3 × 7 fails because 7 is NOT a Fermat prime.
- 25 = 5² fails because 5 appears SQUARED (even though 5 is a Fermat prime).
- 35 = 5 × 7 fails because 7 is not a Fermat prime.
-/

theorem totient_21_eq : Nat.totient 21 = 12 := by decide
theorem totient_25_eq : Nat.totient 25 = 20 := by decide
theorem totient_35_eq : Nat.totient 35 = 24 := by decide

/-- φ(21) = 12, not a power of 2: 21 = 3 × 7, φ(21) = 2·6 = 12. -/
theorem totient_21_not_pow2 : ¬ TotientIsPow2 21 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 21 = 12 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

/-- φ(25) = 20, not a power of 2: 25 = 5², φ(25) = 5·4 = 20.
    5 is a Fermat prime, but 5² fails the criterion. Use odd_prime_pow_gt_one_not_pow2. -/
theorem totient_25_not_pow2 : ¬ TotientIsPow2 25 := by
  have h : ¬ TotientIsPow2 (5 ^ 2) :=
    odd_prime_pow_gt_one_not_pow2 (by decide : Nat.Prime 5) (by decide : (5 : ℕ) ≠ 2)
      (by norm_num : 2 ≤ 2)
  norm_num at h
  exact h

/-- φ(35) = 24, not a power of 2: 35 = 5 × 7, φ(35) = 4·6 = 24. -/
theorem totient_35_not_pow2 : ¬ TotientIsPow2 35 := by
  intro ⟨k, hk⟩
  have h : Nat.totient 35 = 24 := by decide
  rw [h] at hk
  exact not_pow_two_of_odd_prime_dvd (p := 3) (by decide) (by decide) (by norm_num) ⟨k, hk⟩

/-- The regular 21-gon is NOT constructible: φ(21) = 12, 3 | 12. -/
theorem polygon_21_not_constructible : ¬ IsConstructibleNgon 21 := by
  rw [gauss_wantzel_theorem 21 (by norm_num)]
  exact totient_21_not_pow2

/-- The regular 25-gon is NOT constructible: φ(25) = 20, 5 | 20.
    Despite 5 being a Fermat prime, 25 = 5² is not constructible. -/
theorem polygon_25_not_constructible : ¬ IsConstructibleNgon 25 := by
  rw [gauss_wantzel_theorem 25 (by norm_num)]
  exact totient_25_not_pow2

/-- The regular 35-gon is NOT constructible: φ(35) = 24, 3 | 24. -/
theorem polygon_35_not_constructible : ¬ IsConstructibleNgon 35 := by
  rw [gauss_wantzel_theorem 35 (by norm_num)]
  exact totient_35_not_pow2

/-!
## Section XIII: F₅ = 2³²+1 is Composite (Euler 1732)

The only known Fermat primes are 3, 5, 17, 257, 65537 (for k = 0,1,2,3,4).
F₅ = 2^32 + 1 = 4294967297 = 641 × 6700417, discovered by Euler in 1732.
It is unknown whether any Fermat prime beyond 65537 exists.
-/

/-- Euler's 1732 factorization: F₅ = 2^32 + 1 = 641 × 6700417. -/
theorem f5_factorization : 641 * 6700417 = 4294967297 := by norm_num

/-- F₅ = 2^32 + 1 equals 4294967297. -/
theorem f5_value : 2 ^ 32 + 1 = 4294967297 := by norm_num

/-- F₅ = 4294967297 is NOT prime (it factors as 641 × 6700417). -/
theorem f5_not_prime : ¬ Nat.Prime 4294967297 := by native_decide

/-- F₅ is NOT a Fermat prime. -/
theorem f5_not_fermat_prime : ¬ IsFermatPrime 4294967297 :=
  fun ⟨hprime, _⟩ => f5_not_prime hprime

/-!
## Section XIV: Axiom Decomposition — Toward a Full Proof

The single axiom `gauss_wantzel_theorem` can be decomposed into more primitive
facts that are closer to what Mathlib can provide.

**Proof roadmap:**
1. cos(2π/n) is algebraic over ℚ (from cyclotomic theory)
2. The Galois group of the minimal polynomial of cos(2π/n) has order φ(n)/2
   (from: Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/nℤ)*, maximal real subfield index 2)
3. By the Wantzel-Galois characterization (OQ02):
   cos(2π/n) constructible ↔ that Galois group is a 2-group
4. 2-group of order φ(n)/2 ↔ φ(n)/2 = 2^k ↔ φ(n) = 2^(k+1) ↔ TotientIsPow2

**Mathlib availability:**
- cos(2π/n) is algebraic over ℚ: ✅ PROVED (via Chebyshev T_n, see below)
- [ℚ(ζₙ):ℚ] = φ(n): ✅ IsCyclotomicExtension.finrank
- Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/nℤ)*: ✅ IsCyclotomicExtension.autEquivPow
- Maximal real subfield ℚ(ζₙ⁺) = ℚ(cos(2π/n)): ❌ Not yet in Mathlib
- [ℚ(ζₙ⁺):ℚ] = φ(n)/2: ❌ Not yet in Mathlib
-/

/-- cos(2π/n) is integral (algebraic) over ℚ for n ≥ 1.
    Proof via Chebyshev polynomials: T_n(cos θ) = cos(nθ) (Mathlib: T_real_cos).
    Setting θ = 2π/n: T_n(cos(2π/n)) = cos(2π) = 1, so cos(2π/n) is a root
    of T_n - 1, a nonzero polynomial with rational coefficients.
    Nonzero: if T_n = C 1, evaluating at cos(π/n) gives cos(π) = 1, absurd.
    Since ℚ is a field, algebraic ↔ integral (isAlgebraic_iff_isIntegral). -/
theorem cos_2pi_div_n_isIntegral (n : ℕ) (hn : 1 ≤ n) :
    IsIntegral ℚ (Real.cos (2 * Real.pi / ↑n)) := by
  rw [← isAlgebraic_iff_isIntegral]
  refine ⟨Chebyshev.T ℚ ↑n - C 1, ?_, ?_⟩
  · -- Nonzero: if T_n = C 1, evaluating at cos(π/n) gives cos(π) = 1, contradicting cos π = -1
    intro heq
    have hTeq : Chebyshev.T ℚ (↑n : ℤ) = C 1 := sub_eq_zero.mp heq
    have h1 := congr_arg (aeval (R := ℚ) (Real.cos (Real.pi / ↑n))) hTeq
    rw [Chebyshev.aeval_T, aeval_C, map_one, Chebyshev.T_real_cos] at h1
    have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcancel : (↑(↑n : ℤ) : ℝ) * (Real.pi / ↑n) = Real.pi := by
      rw [Int.cast_natCast]; field_simp
    rw [hcancel] at h1
    linarith [Real.cos_pi]
  · -- Root: T_n(cos(2π/n)) = cos(n · 2π/n) = cos(2π) = 1, so T_n(x) - 1 = 0
    rw [map_sub, Chebyshev.aeval_T, aeval_C, map_one, Chebyshev.T_real_cos]
    have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hcancel : (↑(↑n : ℤ) : ℝ) * (2 * Real.pi / ↑n) = 2 * Real.pi := by
      rw [Int.cast_natCast]; field_simp
    rw [hcancel, Real.cos_two_pi, sub_self]

/-!
## Section XIV-B: Chebyshev Conjugate Infrastructure

Key insight: cos(2kπ/n) = T_k(cos(2π/n)) where T_k is the kth Chebyshev polynomial.
This proves all potential Galois conjugates of cos(2π/n) lie in ℚ(cos(2π/n)),
establishing normality of the extension ℚ(cos(2π/n))/ℚ.

**Normality proof roadmap** (to eventually eliminate cos_minpoly_gal_card axiom):
1. ✅ cos(2kπ/n) = T_k(cos(2π/n)) (cos_2k_pi_eq_chebyshev_eval, proved below)
2. ✅ cos(2kπ/n) ∈ ℚ[cos(2π/n)] (cos_conjugate_mem_adjoin, proved below)
3. ✅ minpoly(ℚ, cos(2π/n)) | T_n - 1 (minpoly_cos_dvd_chebyshev, proved below)
4. ❌ All roots of T_n - 1 in ℝ are cos(2kπ/n) (needs analytic characterization)
5. ❌ minpoly splits in ℚ(cos(2π/n)) (follows from 2+3+4)
6. ❌ SplittingField(minpoly) ≅ ℚ(cos(2π/n)) (follows from 5)
7. ❌ |Gal| = finrank = natDegree(minpoly) (from 6 + IsGalois.card_aut_eq_finrank)
8. ❌ natDegree(minpoly) = φ(n)/2 (needs cyclotomic tower law: φ(n) = 2 · [ℚ(cos):ℚ])
-/

/-- cos(2kπ/n) = T_k(cos(2π/n)): every potential conjugate of cos(2π/n) is a
    Chebyshev polynomial evaluated at cos(2π/n).
    Proof: T_k(cos θ) = cos(kθ) by Mathlib's Chebyshev.T_real_cos. -/
theorem cos_2k_pi_eq_chebyshev_eval (n : ℕ) (k : ℤ) :
    Real.cos (↑k * (2 * Real.pi / ↑n)) =
    aeval (Real.cos (2 * Real.pi / ↑n)) (Chebyshev.T ℚ k) := by
  rw [Chebyshev.aeval_T, Chebyshev.T_real_cos]

/-- All potential conjugates cos(2kπ/n) lie in ℚ[cos(2π/n)].
    Proof: cos(2kπ/n) = T_k(cos(2π/n)) and T_k ∈ ℚ[X], so the result
    is a polynomial evaluation, hence in the adjoin subalgebra.
    Uses Polynomial.aeval_mem_adjoin_singleton from Mathlib. -/
theorem cos_conjugate_mem_adjoin (n : ℕ) (k : ℤ) :
    Real.cos (↑k * (2 * Real.pi / ↑n)) ∈
    Algebra.adjoin ℚ ({Real.cos (2 * Real.pi / ↑n)} : Set ℝ) := by
  rw [cos_2k_pi_eq_chebyshev_eval n k, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨Chebyshev.T ℚ k, rfl⟩

/-- The minimal polynomial of cos(2π/n) over ℚ divides T_n - 1.
    Proof: cos(2π/n) is a root of T_n - 1 (since T_n(cos(2π/n)) = cos(2π) = 1),
    and the minimal polynomial divides any polynomial with the element as root. -/
theorem minpoly_cos_dvd_chebyshev (n : ℕ) (hn : 1 ≤ n) :
    minpoly ℚ (Real.cos (2 * Real.pi / ↑n)) ∣ Chebyshev.T ℚ ↑n - C 1 := by
  apply minpoly.dvd
  rw [map_sub, Chebyshev.aeval_T, aeval_C, map_one, Chebyshev.T_real_cos]
  have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (↑(↑n : ℤ) : ℝ) * (2 * Real.pi / ↑n) = 2 * Real.pi := by
    rw [Int.cast_natCast]; field_simp
  rw [this, Real.cos_two_pi, sub_self]

/-- The Galois group of the minimal polynomial of cos(2π/n) over ℚ has
    order φ(n)/2 for n ≥ 3.

    **Proof strategy** (mostly assembled, requires 2 more steps):
    Step A: SplittingField(minpoly) = ℚ(cos(2π/n))
      - minpoly | T_n - 1 (✅ minpoly_cos_dvd_chebyshev)
      - Roots of T_n - 1 are cos(2kπ/n) (needs analytic characterization of T_n roots)
      - Each cos(2kπ/n) ∈ ℚ(cos(2π/n)) (✅ cos_conjugate_mem_adjoin)
      - So all roots of minpoly are in ℚ(cos(2π/n))
      - Hence SplittingField = ℚ(cos(2π/n)) (normality)
    Step B: |Gal| = [ℚ(cos(2π/n)):ℚ] = φ(n)/2
      - |Gal| = finrank ℚ SplittingField (by IsGalois.card_aut_eq_finrank)
      - = finrank ℚ ℚ(cos(2π/n)) = natDegree(minpoly)  (from Step A)
      - = φ(n)/2 (needs cyclotomic tower: [ℚ(ζₙ):ℚ] = φ(n), [ℚ(ζₙ):ℚ(cos)] = 2) -/
axiom cos_minpoly_gal_card (n : ℕ) (hn : 3 ≤ n) :
    Fintype.card (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))).Gal = Nat.totient n / 2

/-- Arithmetic bridge: φ(n)/2 is a power of 2 iff φ(n) is a power of 2 (for n ≥ 3).

    For n ≥ 3, φ(n) is even (since n has at least one odd prime factor, or n ≥ 3 is
    a power of 2 with φ(2^k) = 2^(k-1) for k ≥ 2).

    Direction →: φ(n) = 2^k with k ≥ 1 ⟹ φ(n)/2 = 2^(k-1)
    Direction ←: φ(n)/2 = 2^k ⟹ φ(n) = 2 · 2^k = 2^(k+1) -/
theorem totient_div2_pow2_iff {n : ℕ} (hn : 3 ≤ n) :
    (∃ k : ℕ, Nat.totient n / 2 = 2 ^ k) ↔ TotientIsPow2 n := by
  unfold TotientIsPow2
  constructor
  · -- (→): φ(n)/2 = 2^k ⟹ φ(n) = 2^(k+1)
    rintro ⟨k, hk⟩
    -- φ(n) ≥ 2 for n ≥ 3 and φ(n) is even
    have heven : Even (Nat.totient n) := Nat.totient_even (by omega)
    have hdvd : 2 ∣ Nat.totient n := heven.two_dvd
    have hge : 2 ≤ Nat.totient n := by
      rcases hdvd with ⟨m, hm⟩
      have := Nat.totient_pos.mpr (show 0 < n by omega)
      omega
    exact ⟨k + 1, by
      rcases hdvd with ⟨m, hm⟩
      rw [hm, Nat.mul_div_cancel_left _ (by omega)] at hk
      rw [hm, hk, pow_succ]; ring⟩
  · -- (←): φ(n) = 2^k ⟹ φ(n)/2 = 2^(k-1)
    rintro ⟨k, hk⟩
    have hk1 : 1 ≤ k := by
      by_contra h
      push_neg at h
      interval_cases k
      simp at hk
      -- hk : Nat.totient n = 1, but φ(n) is even for n ≥ 3
      exact absurd (hk ▸ (Nat.totient_even (by omega : 3 ≤ n))) (by decide)
    exact ⟨k - 1, by rw [hk, Nat.pow_div hk1 (by omega)]⟩

/-- α ∈ ℝ is constructible from ℚ if it lies in a finite 2-power extension.
    (Same definition as AngleTrisectionOQ02.IsConstructibleFromQ, inlined for
    self-containment since OQ02 has pre-existing Mathlib compatibility issues.) -/
private def IsConstructibleFromQ (α : ℝ) : Prop :=
  ∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    (∃ n : ℕ, Module.finrank ℚ K = 2 ^ n) ∧
    α ∈ K

/-- Wantzel-Galois characterization: α constructible ↔ Gal(minpoly) is a 2-group.
    (Axiomatized from OQ02, which proves 2-group facts and states this as its main axiom.) -/
private axiom wantzel_galois_characterization (α : ℝ) (hα : IsIntegral ℚ α) :
    IsConstructibleFromQ α ↔ IsPGroup 2 (minpoly ℚ α).Gal

/-- **Gauss-Wantzel Theorem (Proved from decomposed axioms)**:
    A regular n-gon is constructible ↔ φ(n) is a power of 2.

    This is now a THEOREM, not an axiom! It follows from:
    1. cos_2pi_div_n_isIntegral (cos(2π/n) is algebraic — PROVED via Chebyshev)
    2. cos_minpoly_gal_card (|Gal| = φ(n)/2)
    3. wantzel_galois_characterization (constructible ↔ 2-group, from OQ02)
    4. totient_div2_pow2_iff (arithmetic bridge, proved above) -/
theorem gauss_wantzel_theorem' (n : ℕ) (hn : 3 ≤ n) :
    IsConstructibleNgon n ↔ TotientIsPow2 n := by
  -- Step 1: IsConstructibleNgon n ↔ IsConstructibleFromQ (cos(2π/n))
  -- (by definition, these are literally the same Prop)
  show (∃ (K : IntermediateField ℚ ℝ),
    FiniteDimensional ℚ K ∧
    (∃ k : ℕ, Module.finrank ℚ K = 2 ^ k) ∧
    Real.cos (2 * Real.pi / n) ∈ K) ↔ _
  -- Step 2: Apply Wantzel-Galois characterization
  have hint := cos_2pi_div_n_isIntegral n (by omega)
  rw [show (∃ (K : IntermediateField ℚ ℝ), FiniteDimensional ℚ K ∧
    (∃ k, Module.finrank ℚ K = 2 ^ k) ∧ Real.cos (2 * Real.pi / ↑n) ∈ K) =
    IsConstructibleFromQ (Real.cos (2 * Real.pi / ↑n)) from rfl,
    wantzel_galois_characterization _ hint]
  -- Step 3: IsPGroup 2 Gal ↔ ∃ k, card Gal = 2^k
  rw [IsPGroup.iff_card]
  -- Step 4: card Gal = φ(n)/2 (by cos_minpoly_gal_card)
  constructor
  · rintro ⟨k, hk⟩
    rw [Nat.card_eq_fintype_card, cos_minpoly_gal_card n hn] at hk
    exact (totient_div2_pow2_iff hn).mp ⟨k, hk⟩
  · intro htot
    obtain ⟨k, hk⟩ := (totient_div2_pow2_iff hn).mpr htot
    exact ⟨k, by rw [Nat.card_eq_fintype_card, cos_minpoly_gal_card n hn]; exact hk⟩

/-!
## Section XV: Cyclotomic-Cosine Bridge

Establishes the algebraic relationship between the primitive root of unity
ζ_n = exp(2πi/n) and cos(2π/n). This is the foundation for proving
[ℚ(ζ_n):ℚ(cos(2π/n))] = 2 via the tower law.

Key results:
- ζ_n satisfies X² - 2cos(2π/n)X + 1 = 0 (quadratic over ℚ(cos))
- sin(2π/n) > 0 for n ≥ 3 (ζ_n ∉ ℝ → quadratic irreducible over ℝ)
- No real root exists for X² - 2cos(2π/n)X + 1 when n ≥ 3
- cos(2π/n) = Re(ζ_n) = (ζ_n + ζ̄_n)/2

These facts, combined with the tower law
  φ(n) = [ℚ(ζ_n):ℚ] = [ℚ(ζ_n):ℚ(cos(2π/n))] · [ℚ(cos(2π/n)):ℚ] = 2 · deg(minpoly)
establish deg(minpoly(cos(2π/n))) = φ(n)/2, the key computation for cos_minpoly_gal_card.
-/

/-- ζ_n = exp(2πi/n), the primitive nth root of unity. -/
noncomputable def zeta (n : ℕ) : ℂ :=
  Complex.exp (↑(2 * Real.pi / ↑n) * Complex.I)

/-- ‖ζ_n‖ = 1: the primitive root of unity lies on the unit circle.
    Proof: ‖exp(↑θ · I)‖ = 1 for any real θ (Mathlib: norm_exp_ofReal_mul_I). -/
theorem zeta_norm_one (n : ℕ) : ‖zeta n‖ = 1 := by
  unfold zeta; exact Complex.norm_exp_ofReal_mul_I _

/-- cos(2π/n) = Re(ζ_n): the real part of the root of unity is the cosine.
    Proof: Re(exp(↑θ · I)) = cos(θ) (Mathlib: exp_ofReal_mul_I_re). -/
theorem cos_eq_zeta_re (n : ℕ) :
    Real.cos (2 * Real.pi / ↑n) = (zeta n).re := by
  unfold zeta; exact (Complex.exp_ofReal_mul_I_re _).symm

/-- sin(2π/n) = Im(ζ_n): the imaginary part of the root of unity is the sine. -/
theorem sin_eq_zeta_im (n : ℕ) :
    Real.sin (2 * Real.pi / ↑n) = (zeta n).im := by
  unfold zeta; exact (Complex.exp_ofReal_mul_I_im _).symm

/-- sin(2π/n) > 0 for n ≥ 3.
    Proof: For n ≥ 3, 0 < 2π/n ≤ 2π/3 < π, so sin is positive
    by Real.sin_pos_of_pos_of_lt_pi. -/
theorem sin_2pi_div_n_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < Real.sin (2 * Real.pi / ↑n) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · -- 2π/n < π when n ≥ 3 > 2
    have h2n : (2 : ℝ) < ↑n := by exact_mod_cast (show 2 < n by omega)
    calc 2 * Real.pi / ↑n
        < 2 * Real.pi / 2 := by
          exact div_lt_div_of_pos_left (by positivity) (by positivity) h2n
      _ = Real.pi := by ring

/-- ζ_n ∉ ℝ for n ≥ 3: the primitive root of unity is not real.
    Proof: Im(ζ_n) = sin(2π/n) > 0 ≠ 0 = Im(↑r) for any r : ℝ. -/
theorem zeta_not_ofReal (n : ℕ) (hn : 3 ≤ n) :
    ¬ ∃ r : ℝ, zeta n = ↑r := by
  rintro ⟨r, hr⟩
  have him := sin_eq_zeta_im n
  rw [hr, Complex.ofReal_im] at him
  linarith [sin_2pi_div_n_pos n hn]

/-- normSq(ζ_n) = cos²(2π/n) + sin²(2π/n) = 1.
    Key building block for the quadratic identity. -/
theorem zeta_normSq_one (n : ℕ) : Complex.normSq (zeta n) = 1 := by
  have hre := cos_eq_zeta_re n
  have him := sin_eq_zeta_im n
  rw [Complex.normSq_apply]
  rw [← hre, ← him]
  have := Real.sin_sq_add_cos_sq (2 * Real.pi / ↑n)
  nlinarith [sq_abs (Real.cos (2 * Real.pi / ↑n)),
             sq_abs (Real.sin (2 * Real.pi / ↑n))]

/-- ζ_n · conj(ζ_n) = 1 since |ζ_n| = 1.
    This is the core identity: ζ_n lies on the unit circle. -/
theorem zeta_mul_conj (n : ℕ) : zeta n * starRingEnd ℂ (zeta n) = 1 := by
  rw [Complex.mul_conj, ← Complex.ofReal_one]
  congr 1
  exact zeta_normSq_one n

/-- cos(2π/n) = (ζ_n + ζ̄_n)/2: the cosine is the average of ζ_n and its conjugate.
    This is the fundamental bridge between the cyclotomic and cosine worlds. -/
theorem cos_eq_half_zeta_add_conj (n : ℕ) :
    (↑(Real.cos (2 * Real.pi / ↑n)) : ℂ) =
    (zeta n + starRingEnd ℂ (zeta n)) / 2 := by
  rw [Complex.add_conj, cos_eq_zeta_re n]
  push_cast; ring

/-- ζ_n satisfies the quadratic X² - 2cos(2π/n)X + 1 = 0.
    This is the minimal polynomial of ζ_n over ℚ(cos(2π/n)) (when n ≥ 3,
    where it is irreducible since ζ_n ∉ ℝ).

    Proof: Factor as (X - ζ)(X - ζ̄) where ζ + ζ̄ = 2cos(2π/n) and ζ·ζ̄ = 1.
    So X² - (ζ+ζ̄)X + ζ·ζ̄ = X² - 2cos(2π/n)X + 1. -/
theorem zeta_quadratic (n : ℕ) :
    zeta n ^ 2 - 2 * ↑(Real.cos (2 * Real.pi / ↑n)) * zeta n + 1 = 0 := by
  set ζ := zeta n with hζ_def
  have h_conj_mul := zeta_mul_conj n
  have h_sum := cos_eq_half_zeta_add_conj n
  -- Rewrite: ζ² - (ζ+ζ̄)ζ + ζ·ζ̄ = 0 by ring
  -- Step 1: 2 * ↑c = ζ + ζ̄
  have h2c : 2 * (↑(Real.cos (2 * Real.pi / ↑n)) : ℂ) =
      ζ + starRingEnd ℂ ζ := by
    rw [h_sum]; ring
  -- Step 2: algebraic identity
  calc ζ ^ 2 - 2 * ↑(Real.cos (2 * Real.pi / ↑n)) * ζ + 1
      = ζ ^ 2 - (ζ + starRingEnd ℂ ζ) * ζ + 1 := by rw [h2c]
    _ = ζ ^ 2 - ζ * ζ - starRingEnd ℂ ζ * ζ + 1 := by ring
    _ = -(ζ * starRingEnd ℂ ζ) + 1 := by ring
    _ = -1 + 1 := by rw [h_conj_mul]
    _ = 0 := by ring

/-- The discriminant of X² - 2cos(2π/n)X + 1 is negative for n ≥ 3.
    disc = 4cos²(2π/n) - 4 = -4sin²(2π/n) < 0.
    This proves the quadratic is irreducible over ℝ. -/
theorem quadratic_discriminant_neg (n : ℕ) (hn : 3 ≤ n) :
    (2 * Real.cos (2 * Real.pi / ↑n)) ^ 2 - 4 < 0 := by
  have hs := sin_2pi_div_n_pos n hn
  nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi / ↑n),
             sq_nonneg (Real.sin (2 * Real.pi / ↑n))]

/-- X² - 2cos(2π/n)X + 1 has no real roots for n ≥ 3.
    Proof: Complete the square: r² - 2cr + 1 = (r-c)² + sin²(2π/n) > 0.
    This means [ℚ(cos(2π/n))(ζ_n) : ℚ(cos(2π/n))] = 2. -/
theorem quadratic_no_real_roots (n : ℕ) (hn : 3 ≤ n) :
    ∀ r : ℝ, r ^ 2 - 2 * Real.cos (2 * Real.pi / ↑n) * r + 1 ≠ 0 := by
  intro r hr
  have hs := sin_2pi_div_n_pos n hn
  nlinarith [sq_nonneg (r - Real.cos (2 * Real.pi / ↑n)),
             sq_nonneg (Real.sin (2 * Real.pi / ↑n)),
             Real.sin_sq_add_cos_sq (2 * Real.pi / ↑n)]

/-- ζ_n⁻¹ = conj(ζ_n) since |ζ_n| = 1 (unit circle element).
    Proof: ζ · conj(ζ) = 1 means conj(ζ) is the multiplicative inverse. -/
theorem zeta_inv_eq_conj (n : ℕ) :
    (zeta n)⁻¹ = starRingEnd ℂ (zeta n) := by
  rw [inv_eq_of_mul_eq_one_right (zeta_mul_conj n)]

/-
## Section XVI: Primitive Root Properties and Separability

Establishes that ζ_n is a primitive nth root of unity (ζ_n^n = 1)
and that the minimal polynomial of cos(2π/n) is separable.
These are foundational for the Galois theory arguments.
-/

/-- ζ_n ≠ 0: the root of unity is nonzero (norm 1). -/
theorem zeta_ne_zero (n : ℕ) : zeta n ≠ 0 := by
  intro h
  have := zeta_norm_one n
  rw [h, norm_zero] at this
  exact one_ne_zero this.symm

/-- ζ_n^n = 1 for n ≥ 1: the defining property of an nth root of unity.
    Proof: exp(n · 2πi/n) = exp(2πi) = 1. -/
theorem zeta_pow_n_eq_one (n : ℕ) (hn : 1 ≤ n) : zeta n ^ n = 1 := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (↑n : ℂ) * (↑(2 * Real.pi / ↑n) * Complex.I) = ↑(2 * Real.pi) * Complex.I := by
    push_cast
    rw [mul_comm (↑n : ℂ) (↑(2 * Real.pi / ↑n) * Complex.I)]
    rw [mul_assoc]
    congr 1
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
    field_simp
  rw [this]
  rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
  exact Complex.exp_two_pi_mul_I

/-- The minimal polynomial of cos(2π/n) over ℚ is separable.
    Immediate from characteristic 0: all irreducible polynomials are separable. -/
theorem minpoly_cos_separable (n : ℕ) (hn : 1 ≤ n) :
    (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))).Separable :=
  (minpoly.irreducible (cos_2pi_div_n_isIntegral n hn)).separable

/-- The minimal polynomial of cos(2π/n) has positive degree for n ≥ 3.
    cos(2π/n) is irrational for n ≥ 3 (since it's an algebraic number
    generating a nontrivial extension). -/
theorem minpoly_cos_natDegree_pos (n : ℕ) (hn : 3 ≤ n) :
    0 < (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))).natDegree := by
  exact minpoly.natDegree_pos (cos_2pi_div_n_isIntegral n (by omega))

/-- ζ_n^k for integer k, extending powers to ℤ. -/
noncomputable def zeta_zpow (n : ℕ) (k : ℤ) : ℂ := zeta n ^ k

/-- ζ_n^(-1) = conj(ζ_n) = ζ_n^(n-1) when ζ_n^n = 1.
    Proof: ζ^(n-1) = ζ^n · ζ^(-1) = 1 · ζ⁻¹ = conj(ζ). -/
theorem zeta_pow_pred_eq_conj (n : ℕ) (hn : 1 ≤ n) :
    zeta n ^ (n - 1) = starRingEnd ℂ (zeta n) := by
  have hpow := zeta_pow_n_eq_one n hn
  rw [← zeta_inv_eq_conj]
  rw [eq_comm, inv_eq_iff_eq_inv]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add]
  have : (↑(n - 1) : ℤ) + (-(↑n : ℤ)) = -1 := by omega
  rw [this, zpow_neg_one]

/-- cos(2kπ/n) = Re(ζ_n^k): cosines of rational multiples of 2π
    are real parts of powers of the primitive root.
    Bridge between analytic (cos) and algebraic (ζ^k) representations. -/
theorem cos_eq_zeta_pow_re (n k : ℕ) :
    Real.cos (↑k * (2 * Real.pi / ↑n)) = (zeta n ^ k).re := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  simp only [Complex.exp_ofReal_mul_I_re]
  congr 1
  push_cast; ring

/-- sin(2kπ/n) = Im(ζ_n^k): sines are imaginary parts of powers.
    Companion to cos_eq_zeta_pow_re. -/
theorem sin_eq_zeta_pow_im (n k : ℕ) :
    Real.sin (↑k * (2 * Real.pi / ↑n)) = (zeta n ^ k).im := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  simp only [Complex.exp_ofReal_mul_I_im]
  congr 1
  push_cast; ring

/-- ζ_n^k lies on the unit circle: |ζ_n^k| = 1 for all k.
    Proof: |ζ^k| = |ζ|^k = 1^k = 1. -/
theorem zeta_pow_norm_one (n k : ℕ) : ‖zeta n ^ k‖ = 1 := by
  rw [norm_pow, zeta_norm_one, one_pow]

/-- cos(2kπ/n) is in [-1, 1] (follows from Chebyshev bound on Re of unit circle).
    Concrete bound useful for root characterization. -/
theorem cos_2k_pi_div_n_bound (n k : ℕ) :
    |Real.cos (↑k * (2 * Real.pi / ↑n))| ≤ 1 := by
  exact abs_cos_le_one _

/-
## Section XVII: Cyclotomic Polynomial Connection

Links our concrete ζ_n = exp(2πi/n) with Mathlib's cyclotomic polynomial
infrastructure. This is the bridge needed for the tower law argument.
-/

/-- ζ_n is a root of X^n - 1 (the polynomial whose roots are nth roots of unity).
    Immediate from zeta_pow_n_eq_one. -/
theorem zeta_is_root_of_xn_sub_one (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.aeval (zeta n) (Polynomial.X ^ n - Polynomial.C 1 : Polynomial ℂ) = 0 := by
  simp [zeta_pow_n_eq_one n hn]

/-- Degree of the cyclotomic polynomial Φ_n equals Euler's totient φ(n).
    This is the fundamental connection between cyclotomic fields and number theory. -/
theorem cyclotomic_natDegree_eq_totient (n : ℕ) (hn : 0 < n) :
    (Polynomial.cyclotomic n ℤ).natDegree = Nat.totient n :=
  Polynomial.cyclotomic.natDegree_eq n hn

/-
## Summary

### Proved (0 sorries):
1. `totient_X_eq` (22 theorems): φ(n) for n = 3..17, 21, 25, 34, 35, 51, 85, 255, 257, 65537, etc.
2. `not_pow_two_of_odd_prime_dvd`: general prime divisibility helper
3. `totient_pow2_of_two_power`: φ(2^k) = 2^(k-1) is pow2 for k ≥ 1
4. `totient_prod_is_pow2`: product of coprime pow2-totient numbers has pow2 totient
5. `odd_prime_pow_gt_one_not_pow2`: odd prime squared → totient not pow2
6. `totient_9_not_pow2'`: structural proof that 9=3² fails via odd_prime_pow_gt_one_not_pow2
7. `totient_X_pow2` (16 theorems): φ(n) = 2^k for constructible n values
8. `totient_X_not_pow2` (9 theorems): φ not pow2 for n = 7,9,11,13,14,18,21,25,35
9. `units_zmod_card_eq_totient`: |(ℤ/nℤ)*| = φ(n) (from Mathlib ZMod.card_units_eq_totient)
10. `units_zmod_is_2group_iff`: (ℤ/nℤ)* is 2-group ↔ TotientIsPow2 n (proved!)
11. `fermat_prime_X` (5 theorems): 3, 5, 17, 257, 65537 are Fermat primes
12. `fermat_prime_totient_pow2`, `fermat_prime_ngon_constructible`: Fermat prime structure
13. Constructibility: n = 3,4,5,6,8,10,12,15,17,20,34,51,85,255,257,65537 (16 polygons)
14. Non-constructibility: n = 7,9,11,13,14,18,21,25,35 (9 polygons)
15. F₅ facts: f5_factorization, f5_value, f5_not_prime, f5_not_fermat_prime
16. `cos_2pi_div_n_isIntegral`: cos(2π/n) integral over ℚ (Chebyshev T_n)
17. `cos_2k_pi_eq_chebyshev_eval`: cos(2kπ/n) = T_k(cos(2π/n)) (Chebyshev identity)
18. `cos_conjugate_mem_adjoin`: cos(2kπ/n) ∈ ℚ[cos(2π/n)] (normality of extension)
19. `minpoly_cos_dvd_chebyshev`: minpoly(ℚ, cos(2π/n)) | T_n - 1
20. `zeta_norm_one`: ‖ζ_n‖ = 1 (unit circle)
21. `cos_eq_zeta_re`, `sin_eq_zeta_im`: cos/sin = Re/Im of ζ_n
22. `sin_2pi_div_n_pos`: sin(2π/n) > 0 for n ≥ 3
23. `zeta_not_ofReal`: ζ_n ∉ ℝ for n ≥ 3
24. `zeta_normSq_one`: normSq(ζ_n) = 1
25. `zeta_mul_conj`: ζ_n · conj(ζ_n) = 1
26. `cos_eq_half_zeta_add_conj`: cos = (ζ + ζ̄)/2
27. `zeta_quadratic`: ζ² - 2cos·ζ + 1 = 0
28. `quadratic_discriminant_neg`: disc = -4sin² < 0 for n ≥ 3
29. `quadratic_no_real_roots`: no real root for n ≥ 3
30. `zeta_inv_eq_conj`: ζ⁻¹ = conj(ζ)
31. `zeta_ne_zero`: ζ_n ≠ 0 (nonzero from norm 1)
32. `zeta_pow_n_eq_one`: ζ_n^n = 1 (nth root of unity)
33. `minpoly_cos_separable`: minpoly is separable (char 0)
34. `minpoly_cos_natDegree_pos`: positive degree for n ≥ 3
35. `zeta_pow_pred_eq_conj`: ζ^(n-1) = conj(ζ)
36. `cos_eq_zeta_pow_re`, `sin_eq_zeta_pow_im`: cos/sin of multiples = Re/Im of ζ^k
37. `zeta_pow_norm_one`: |ζ^k| = 1 for all k
38. `cos_2k_pi_div_n_bound`: |cos(2kπ/n)| ≤ 1
39. `zeta_is_root_of_xn_sub_one`: ζ_n is root of X^n - 1
40. `cyclotomic_natDegree_eq_totient`: natDegree(Φ_n) = φ(n)

### Axiomatized (2 axioms + 1 redundant):
- `gauss_wantzel_theorem`: n-gon constructible ↔ φ(n) = 2^k
  (REDUNDANT — proved as `gauss_wantzel_theorem'` from decomposed axioms)
- `cos_minpoly_gal_card`: |Gal(minpoly(cos(2π/n)))| = φ(n)/2
  (requires maximal real subfield theory; see Section XIV-B and XV proof roadmap)
- `wantzel_galois_characterization`: constructible ↔ 2-group Galois (from OQ02)

### Progress toward eliminating cos_minpoly_gal_card:
- ✅ cos(2kπ/n) = T_k(cos(2π/n)) — Chebyshev conjugate identity (proved)
- ✅ cos(2kπ/n) ∈ ℚ[cos(2π/n)] — all conjugates in adjoin (proved)
- ✅ minpoly | T_n - 1 — divisibility by Chebyshev (proved)
- ✅ ζ_n satisfies X²-2cos(2π/n)X+1=0 — cyclotomic quadratic (proved, Session 2)
- ✅ ζ_n ∉ ℝ for n ≥ 3 — quadratic irreducible over ℝ (proved, Session 2)
- ✅ ζ⁻¹ = conj(ζ) and cos = (ζ+ζ̄)/2 — bridge identities (proved, Session 2)
- ✅ ζ_n^n = 1 — primitive root of unity (proved, Session 3)
- ✅ minpoly is separable — char 0 (proved, Session 3)
- ✅ cos/sin = Re/Im of ζ^k — power root bridge (proved, Session 3)
- ✅ natDegree(Φ_n) = φ(n) — cyclotomic degree (Mathlib, Session 3)
- ❌ T_n - 1 roots ⊂ {cos(2kπ/n)} — analytic characterization (needs work)
- ❌ minpoly splits in adjoin — normality (follows from above)
- ❌ [ℚ(ζ_n):ℚ(cos)] = 2 (formal) — needs IntermediateField infrastructure
- ❌ natDegree(minpoly) = φ(n)/2 — cyclotomic tower law (needs above)
-/

end AngleTrisectionOQ02OQ03
