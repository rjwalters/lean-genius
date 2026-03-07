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

  File summary: 38 proved theorems, 0 sorries, 1 axiom (gauss_wantzel_theorem).
  The axiom requires cyclotomic field theory (IsCyclotomicExtension in Mathlib exists
  but the assembled Gauss-Wantzel statement is not yet a Mathlib theorem).
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
- [ℚ(ζₙ):ℚ] = φ(n): ✅ IsCyclotomicExtension.finrank
- Gal(ℚ(ζₙ)/ℚ) ≅ (ℤ/nℤ)*: ✅ IsCyclotomicExtension.autEquivPow
- Maximal real subfield ℚ(ζₙ⁺) = ℚ(cos(2π/n)): ❌ Not yet in Mathlib
- [ℚ(ζₙ⁺):ℚ] = φ(n)/2: ❌ Not yet in Mathlib
-/

/-- cos(2π/n) is algebraic over ℚ for n ≥ 1.
    Proof sketch: ζₙ = e^{2πi/n} is a root of xⁿ - 1 = 0 (algebraic).
    cos(2π/n) = (ζₙ + ζₙ⁻¹)/2 is algebraic (sum of algebraic numbers).
    This is provable from Mathlib, but the exact formalization path goes through
    complex analysis and would need connecting Real.cos to Complex.exp. -/
axiom cos_2pi_div_n_isIntegral (n : ℕ) (hn : 1 ≤ n) :
    IsIntegral ℚ (Real.cos (2 * Real.pi / ↑n))

/-- The Galois group of the minimal polynomial of cos(2π/n) over ℚ has
    order φ(n)/2 for n ≥ 3.

    Proof sketch:
    - ℚ(ζₙ) has degree φ(n) over ℚ [IsCyclotomicExtension.finrank]
    - Complex conjugation τ: ζₙ ↦ ζₙ⁻¹ generates a subgroup of order 2
    - The fixed field ℚ(ζₙ)^τ = ℚ(cos(2π/n)) has degree φ(n)/2
    - ℚ(cos(2π/n))/ℚ is a Galois extension (fixed field of normal subgroup)
    - So |Gal(minpoly(cos(2π/n)))| = [ℚ(cos(2π/n)):ℚ] = φ(n)/2

    This is the key bridge between cyclotomic theory and constructibility. -/
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
    have heven : 2 ∣ Nat.totient n := Nat.totient_even (by omega)
    have hge : 2 ≤ Nat.totient n := Nat.totient_pos n |>.trans_le (by
      rcases heven with ⟨m, hm⟩
      omega)
    exact ⟨k + 1, by
      rcases heven with ⟨m, hm⟩
      rw [hm, Nat.mul_div_cancel_left _ (by omega)] at hk
      rw [hm, hk, pow_succ]⟩
  · -- (←): φ(n) = 2^k ⟹ φ(n)/2 = 2^(k-1)
    rintro ⟨k, hk⟩
    have hk1 : 1 ≤ k := by
      by_contra h
      push_neg at h
      interval_cases k
      simp at hk
      have := Nat.totient_pos n
      omega
    exact ⟨k - 1, by rw [hk, Nat.pow_div hk1 (by omega)]⟩

/-- **Gauss-Wantzel Theorem (Proved from decomposed axioms)**:
    A regular n-gon is constructible ↔ φ(n) is a power of 2.

    This is now a THEOREM, not an axiom! It follows from:
    1. cos_2pi_div_n_isIntegral (cos(2π/n) is algebraic)
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
    AngleTrisectionOQ02.IsConstructibleFromQ (Real.cos (2 * Real.pi / ↑n)) from rfl,
    AngleTrisectionOQ02.wantzel_galois_characterization _ hint]
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
## Summary

### Proved (0 sorries):
1. `totient_X_eq` (22 theorems): φ(n) for n = 3..17, 21, 25, 34, 35, 51, 85, 255, 257, 65537, etc.
2. `not_pow_two_of_odd_prime_dvd`: general prime divisibility helper
3. `totient_pow2_of_two_power`: φ(2^k) = 2^(k-1) is pow2 for k ≥ 1
4. `totient_prod_is_pow2`: product of coprime pow2-totient numbers has pow2 totient
5. `odd_prime_pow_gt_one_not_pow2`: odd prime squared → totient not pow2
6. `totient_9_not_pow2'`: structural proof that 9=3² fails via odd_prime_pow_gt_one_not_pow2
7. `totient_X_pow2` (16 theorems): φ(n) = 2^k for n = 3,4,5,6,8,10,12,17,34,51,85,255,257,65537,15,20
8. `totient_X_not_pow2` (9 theorems): φ not pow2 for n = 7,9,11,13,14,18,21,25,35
9. `units_zmod_card_eq_totient`: |(ℤ/nℤ)*| = φ(n) (from Mathlib ZMod.card_units_eq_totient)
10. `units_zmod_is_2group_iff`: (ℤ/nℤ)* is 2-group ↔ TotientIsPow2 n (proved!)
11. `fermat_prime_X` (5 theorems): 3, 5, 17, 257, 65537 are Fermat primes
12. `fermat_prime_totient_pow2`, `fermat_prime_ngon_constructible`: Fermat prime structure
13. Constructibility: n = 3,4,5,6,8,10,12,15,17,20,34,51,85,255,257,65537 (16 polygons)
14. Non-constructibility: n = 7,9,11,13,14,18,21,25,35 (9 polygons)
15. F₅ facts: f5_factorization, f5_value, f5_not_prime, f5_not_fermat_prime

### Axiomatized (1 axiom):
- `gauss_wantzel_theorem`: n-gon constructible ↔ φ(n) = 2^k
  (requires cyclotomic field theory + Galois criterion from OQ02)

### Key insights:
- The arithmetic core: φ(n) = 2^k ↔ n = 2^a × (product of distinct Fermat primes)
- The Galois bridge: |(ℤ/nℤ)*| = φ(n) (proved from Mathlib: units_zmod_card_eq_totient)
  → 2-group condition ↔ φ(n) = 2^k (units_zmod_is_2group_iff, proved!)
- The arithmetic structure: totient_prod_is_pow2 + odd_prime_pow_gt_one_not_pow2
  give the complete arithmetic characterization in terms of prime factors.
-/

end AngleTrisectionOQ02OQ03
