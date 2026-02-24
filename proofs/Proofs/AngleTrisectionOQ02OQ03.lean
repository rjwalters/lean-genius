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
  exact ⟨2 ^ k, by rw [Nat.totient_prime hprime, hpk]; omega⟩

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
## Summary

### Proved (0 sorries):
1. `totient_X_eq` (14 theorems): φ(n) values for n = 3..17, 257, 65537 (by decide/native_decide)
2. `not_pow_two_of_odd_prime_dvd`: general helper using prime divisibility
3. `totient_X_pow2` (10 theorems): φ(n) = 2^k verified with explicit witnesses
4. `totient_X_not_pow2` (4 theorems): φ(7)=6, φ(9)=6, φ(11)=10, φ(13)=12 not powers of 2
5. `fermat_prime_X` (5 theorems): 3, 5, 17, 257, 65537 are Fermat primes
6. `fermat_prime_totient_pow2`: φ(p) = 2^(2^k) for Fermat prime p = 2^(2^k)+1
7. `fermat_prime_ngon_constructible`: Fermat primes give constructible polygons
8. Constructibility theorems for n = 3, 4, 5, 6, 8, 10, 12, 17, 257, 65537
9. Non-constructibility theorems for n = 7, 9, 11, 13

### Axiomatized (1 axiom):
- `gauss_wantzel_theorem`: n-gon constructible ↔ φ(n) = 2^k
  (requires cyclotomic field theory + Galois criterion from OQ02)

### Key insight:
The Gauss-Wantzel theorem bridges OQ02 (Galois criterion for algebraic numbers)
to the classical characterization of constructible polygons. The Galois group
Gal(Φₙ/ℚ) ≅ (ℤ/nℤ)* has order φ(n), so the 2-group condition becomes φ(n) = 2^k.
-/

end AngleTrisectionOQ02OQ03
