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

  File summary: 67+ proved theorems, 0 sorries, 0 axioms.
  galois_conjugate_count: PROVED (coprime pairing via lower-half injectivity).
  minpoly_cos_natDegree_eq PROVED (3 sorries eliminated: h_top, h_deg, combining).
  gauss_wantzel_theorem PROVED (via degree theory from OQ02OQ03OQ01).
  All 3 former axioms eliminated: gauss_wantzel_theorem, cos_minpoly_gal_card,
  wantzel_galois_characterization.
  Key results: cos integrality (Chebyshev T_n), conjugate infrastructure (T_k identity,
  adjoin membership), minpoly divisibility (minpoly | T_n - 1), cyclotomic-cosine bridge
  (ζ quadratic, ζ ∉ ℝ, no real roots, ζ⁻¹ = conj(ζ)),
  cyclotomic tower infrastructure (ζ integral, minpoly ζ = Φₙ, finrank ℚ(ζ) = φ(n),
  cos ∈ ℚ(ζ), ℚ(cos) ≤ ℚ(ζ)).
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ03OQ01

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
## Section IV: Gauss-Wantzel Theorem (Proved)

Proof via degree theory from OQ02OQ03OQ01:
  1. cos_extension_is_galois: ∃ K with [K:ℚ] = φ(n)/2 containing cos(2π/n)
  2. minpoly_cos_natDegree_eq: natDeg(minpoly ℚ cos(2π/n)) = φ(n)/2
  3. Forward (→): cos ∈ K with [K:ℚ] = 2^m → φ(n)/2 | 2^m → φ(n) = 2^k
  4. Backward (←): φ(n) = 2^k → φ(n)/2 = 2^(k-1) → K witnesses constructibility
-/

/-- A positive divisor of 2^m is itself a power of 2. -/
private theorem dvd_pow_two_is_pow_two {d m : ℕ} (hd : 0 < d) (h : d ∣ 2 ^ m) :
    ∃ k : ℕ, d = 2 ^ k := by
  induction m generalizing d with
  | zero =>
    rw [pow_zero] at h
    exact ⟨0, Nat.eq_one_of_dvd_one h⟩
  | succ m ih =>
    by_cases h2 : 2 ∣ d
    · obtain ⟨d', rfl⟩ := h2
      have hd' : 0 < d' := by omega
      have h' : d' ∣ 2 ^ m := by
        rw [pow_succ] at h
        exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp h
      obtain ⟨k, hk⟩ := ih hd' h'
      exact ⟨k + 1, by rw [hk, pow_succ]⟩
    · -- d is odd and divides 2^(m+1), so d = 1
      have hd1 : d = 1 := by
        by_contra hne
        obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
        have hpeq2 : p = 2 := by
          have hp2 : p ∣ 2 := hp.dvd_of_dvd_pow (dvd_trans hpd h)
          exact le_antisymm (Nat.le_of_dvd (by omega) hp2) hp.two_le
        exact h2 (hpeq2 ▸ hpd)
      exact ⟨0, by rw [hd1, pow_zero]⟩

/-- **Gauss-Wantzel Theorem** (Gauss 1796, Wantzel 1837):
    A regular n-gon is constructible by compass and straightedge if and only if
    Euler's totient φ(n) is a power of 2.

    Equivalently: n = 2^k · p₁ · p₂ · ... · p_r where p₁,...,p_r are distinct Fermat primes.

    Proved via cyclotomic field degree theory (OQ02OQ03OQ01). -/
theorem gauss_wantzel_theorem (n : ℕ) (hn : 3 ≤ n) :
    IsConstructibleNgon n ↔ TotientIsPow2 n := by
  constructor
  · -- Forward: IsConstructibleNgon → TotientIsPow2
    rintro ⟨K, hK_fd, ⟨m, hK_pow⟩, hcos_mem⟩
    set c := Real.cos (2 * Real.pi / ↑n) with hc_def
    have h_int : IsIntegral ℚ c :=
      (AngleTrisectionOQ02OQ03OQ01.cos_algebraic_from_cyclotomic n hn).isIntegral
    -- finrank ℚ (adjoin ℚ {c}) = φ(n)/2
    set F := IntermediateField.adjoin ℚ ({c} : Set ℝ)
    have h_finrank_F : Module.finrank ℚ ↥F = Nat.totient n / 2 := by
      have h_adj := IntermediateField.adjoin.finrank h_int
      have h_deg := AngleTrisectionOQ02OQ03OQ01.minpoly_cos_natDegree_eq n hn
      linarith
    -- F ≤ K since c ∈ K
    have hF_le_K : F ≤ K :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hcos_mem)
    -- Tower law: finrank ℚ K = finrank ℚ F * finrank F K
    -- so finrank ℚ F ∣ finrank ℚ K = 2^m
    have h_dvd : Nat.totient n / 2 ∣ 2 ^ m := by
      rw [← h_finrank_F, ← hK_pow]
      exact ⟨Module.finrank ↥F ↥K,
        (Module.finrank_mul_finrank ℚ ↥F ↥K).symm⟩
    -- φ(n)/2 divides 2^m → φ(n)/2 = 2^j
    have h_pos : 0 < Nat.totient n / 2 := by
      have := (Nat.totient_pos).mpr (show 0 < n by omega)
      have := (Nat.totient_even (show 3 ≤ n by omega)).two_dvd
      omega
    obtain ⟨j, hj⟩ := dvd_pow_two_is_pow_two h_pos h_dvd
    exact (totient_div2_pow2_iff hn).mp ⟨j, hj⟩
  · -- Backward: TotientIsPow2 → IsConstructibleNgon
    rintro htot
    obtain ⟨j, hj⟩ := (totient_div2_pow2_iff hn).mpr htot
    obtain ⟨K, hK_fd, hcos_mem, hK_rank⟩ :=
      AngleTrisectionOQ02OQ03OQ01.cos_extension_is_galois n hn
    exact ⟨K, hK_fd, ⟨j, by rw [hK_rank]; exact hj⟩, hcos_mem⟩

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

**Normality proof roadmap** (cos_minpoly_gal_card axiom ELIMINATED via direct degree argument):
1. ✅ cos(2kπ/n) = T_k(cos(2π/n)) (cos_2k_pi_eq_chebyshev_eval, proved below)
2. ✅ cos(2kπ/n) ∈ ℚ[cos(2π/n)] (cos_conjugate_mem_adjoin, proved below)
3. ✅ minpoly(ℚ, cos(2π/n)) | T_n - 1 (minpoly_cos_dvd_chebyshev, proved below)
Note: The Gauss-Wantzel theorem is now proved directly from degree theory
(via OQ02OQ03OQ01), bypassing the Galois group cardinality entirely.
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
establish deg(minpoly(cos(2π/n))) = φ(n)/2 (now proved in OQ02OQ03OQ01).
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
  have hn_c : (↑n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (↑n : ℂ) * (↑(2 * Real.pi / ↑n) * Complex.I) =
    2 * ↑Real.pi * Complex.I := by push_cast; field_simp
  rw [this]; exact Complex.exp_two_pi_mul_I

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
  rw [← zeta_inv_eq_conj]
  symm
  apply inv_eq_of_mul_eq_one_right
  calc zeta n * zeta n ^ (n - 1)
      = zeta n ^ 1 * zeta n ^ (n - 1) := by rw [pow_one]
    _ = zeta n ^ (1 + (n - 1)) := (pow_add _ _ _).symm
    _ = zeta n ^ n := by congr 1; omega
    _ = 1 := zeta_pow_n_eq_one n hn

/-- cos(2kπ/n) = Re(ζ_n^k): cosines of rational multiples of 2π
    are real parts of powers of the primitive root.
    Bridge between analytic (cos) and algebraic (ζ^k) representations. -/
theorem cos_eq_zeta_pow_re (n k : ℕ) :
    Real.cos (↑k * (2 * Real.pi / ↑n)) = (zeta n ^ k).re := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have h : (↑k : ℂ) * (↑(2 * Real.pi / ↑n) * Complex.I) =
    ↑(↑k * (2 * Real.pi / ↑n)) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_re]

/-- sin(2kπ/n) = Im(ζ_n^k): sines are imaginary parts of powers.
    Companion to cos_eq_zeta_pow_re. -/
theorem sin_eq_zeta_pow_im (n k : ℕ) :
    Real.sin (↑k * (2 * Real.pi / ↑n)) = (zeta n ^ k).im := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  have h : (↑k : ℂ) * (↑(2 * Real.pi / ↑n) * Complex.I) =
    ↑(↑k * (2 * Real.pi / ↑n)) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I_im]

/-- ζ_n^k lies on the unit circle: |ζ_n^k| = 1 for all k.
    Proof: |ζ^k| = |ζ|^k = 1^k = 1. -/
theorem zeta_pow_norm_one (n k : ℕ) : ‖zeta n ^ k‖ = 1 := by
  rw [norm_pow, zeta_norm_one, one_pow]

/-- cos(2kπ/n) is in [-1, 1] (follows from Chebyshev bound on Re of unit circle).
    Concrete bound useful for root characterization. -/
theorem cos_2k_pi_div_n_bound (n k : ℕ) :
    |Real.cos (↑k * (2 * Real.pi / ↑n))| ≤ 1 := by
  exact Real.abs_cos_le_one _

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
theorem cyclotomic_natDegree_eq_totient (n : ℕ) :
    (Polynomial.cyclotomic n ℤ).natDegree = Nat.totient n :=
  Polynomial.natDegree_cyclotomic n ℤ

/-
## Section XVIII: Roots of T_n − 1

Establishes that cos(2kπ/n) are roots of the Chebyshev polynomial T_n − 1.
Combined with minpoly | T_n − 1, this constrains the roots of the minimal
polynomial to lie among these cosine values.
-/

/-- cos(2kπ/n) is a root of T_n − 1 for any k.
    Proof: T_n(cos(2kπ/n)) = cos(n · 2kπ/n) = cos(2kπ) = 1.
    So T_n(cos(2kπ/n)) − 1 = 0. -/
theorem cos_is_root_of_chebyshev_sub_one (n k : ℕ) (hn : 1 ≤ n) :
    Polynomial.aeval (Real.cos (↑k * (2 * Real.pi / ↑n)))
      (Chebyshev.T ℝ n - Polynomial.C 1) = 0 := by
  simp only [map_sub, Chebyshev.aeval_T, map_one]
  rw [Chebyshev.T_real_cos]
  have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h1 : (↑(↑n : ℤ) : ℝ) * (↑k * (2 * Real.pi / ↑n)) = ↑k * (2 * Real.pi) := by
    rw [Int.cast_natCast]; field_simp
  rw [h1]
  have h2 : ↑k * (2 * Real.pi) = ↑(↑k : ℤ) * (2 * Real.pi) := by push_cast; ring
  rw [h2, Real.cos_int_mul_two_pi]
  simp

/-- ζ_n^k + ζ_n^(-k) = 2cos(2kπ/n): sum of a root of unity and its inverse
    equals twice the cosine. Generalization of cos_eq_half_zeta_add_conj. -/
theorem zeta_pow_add_inv_pow (n k : ℕ) :
    zeta n ^ k + (zeta n ^ k)⁻¹ = 2 * ↑(Real.cos (↑k * (2 * Real.pi / ↑n))) := by
  have h_re := cos_eq_zeta_pow_re n k
  have h_norm := zeta_pow_norm_one n k
  -- (z^k)⁻¹ = conj(z^k) since |z^k| = 1
  have h_inv : (zeta n ^ k)⁻¹ = starRingEnd ℂ (zeta n ^ k) := by
    rw [inv_eq_of_mul_eq_one_right]
    rw [Complex.mul_conj, ← Complex.ofReal_one]
    congr 1
    rw [Complex.normSq_eq_norm_sq, h_norm, one_pow]
  rw [h_inv, Complex.add_conj, h_re]
  push_cast; ring

/-- ζ_n^k · ζ_n^(-k) = 1: product of conjugate powers on the unit circle. -/
theorem zeta_pow_mul_inv_pow (n k : ℕ) :
    zeta n ^ k * (zeta n ^ k)⁻¹ = 1 := by
  rcases eq_or_ne (zeta n ^ k) 0 with h | h
  · exfalso
    have := zeta_pow_norm_one n k
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm
  · exact mul_inv_cancel₀ h

/-- The Chebyshev polynomial T_n evaluated at cos(2π/n) equals 1.
    This is the k=1 case that was used for minpoly_cos_dvd_chebyshev,
    stated as a standalone identity. -/
theorem chebyshev_T_eval_cos_eq_one (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.aeval (Real.cos (2 * Real.pi / ↑n)) (Chebyshev.T ℝ n) = 1 := by
  rw [Chebyshev.aeval_T, Chebyshev.T_real_cos]
  have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : (↑(↑n : ℤ) : ℝ) * (2 * Real.pi / ↑n) = 2 * Real.pi := by
    rw [Int.cast_natCast]; field_simp
  rw [this, Real.cos_two_pi]

/-- cos(0) = 1 is always a root of T_n − 1 (the k=0 case).
    More precisely, T_n(1) = 1 for all n. -/
theorem chebyshev_T_one_eq_one (n : ℕ) :
    Polynomial.aeval (1 : ℝ) (Chebyshev.T ℝ n) = 1 := by
  conv_lhs => rw [show (1 : ℝ) = Real.cos 0 from Real.cos_zero.symm]
  rw [Chebyshev.aeval_T, Chebyshev.T_real_cos, mul_zero, Real.cos_zero]

/-
## Section XIX: IsPrimitiveRoot Connection

Connects our concrete ζ_n = exp(2πi/n) to Mathlib's IsPrimitiveRoot predicate.
This unlocks the full cyclotomic field infrastructure:
- IsCyclotomicExtension, finrank = φ(n)
- autEquivPow ≅ (ℤ/nℤ)*
- Cyclotomic polynomial factorization
-/

/-- Our ζ_n equals the Mathlib standard form exp(2πi/n).
    Our definition: exp(↑(2π/n) * I) = exp((2π/n : ℝ) * I)
    Mathlib form:   exp(2 * ↑π * I / ↑n) = exp(2πI/n)
    These are equal by commutativity and associativity of multiplication. -/
theorem zeta_eq_mathlib_form (n : ℕ) :
    zeta n = Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) := by
  unfold zeta
  congr 1
  push_cast
  ring

/-- ζ_n is a primitive nth root of unity (Mathlib's IsPrimitiveRoot).
    Connects to Complex.isPrimitiveRoot_exp from Mathlib. -/
theorem zeta_isPrimitiveRoot (n : ℕ) (hn : 1 ≤ n) :
    IsPrimitiveRoot (zeta n) n := by
  rw [zeta_eq_mathlib_form]
  exact Complex.isPrimitiveRoot_exp n (by omega)

/-- ζ_n^k = 1 iff n ∣ k: characterization of when powers of ζ_n equal 1.
    Direct from IsPrimitiveRoot. -/
theorem zeta_pow_eq_one_iff (n : ℕ) (hn : 1 ≤ n) (k : ℕ) :
    zeta n ^ k = 1 ↔ n ∣ k :=
  (zeta_isPrimitiveRoot n hn).pow_eq_one_iff_dvd k

/-- ζ_n is a root of the cyclotomic polynomial Φ_n.
    Proof: IsPrimitiveRoot implies isRoot_cyclotomic. -/
theorem zeta_isRoot_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    Polynomial.IsRoot (Polynomial.cyclotomic n ℂ) (zeta n) :=
  (zeta_isPrimitiveRoot n hn).isRoot_cyclotomic (by omega)

/-- The minimal polynomial of ζ_n over ℤ divides the cyclotomic polynomial Φ_n.
    Since Φ_n is irreducible over ℚ, they are actually equal. -/
theorem minpoly_zeta_dvd_cyclotomic (n : ℕ) (hn : 1 ≤ n) :
    minpoly ℤ (zeta n) ∣ Polynomial.cyclotomic n ℤ :=
  (zeta_isPrimitiveRoot n hn).minpoly_dvd_cyclotomic (by omega)



/-
## Section XXI: ζ_n as Root of Cyclotomic Polynomial (Algebraic Bridge)

The key algebraic fact: since ζ_n is a primitive nth root of unity,
it is a root of the cyclotomic polynomial Φ_n, which is irreducible over ℚ.
Therefore minpoly(ℚ, ζ_n) = Φ_n (up to leading coefficient), giving
[ℚ(ζ_n):ℚ] = deg(Φ_n) = φ(n).

Combined with [ℚ(ζ_n):ℚ(cos)] = 2 (from the quadratic X²-2cos·X+1),
the tower law gives [ℚ(cos):ℚ] = φ(n)/2.
-/

/-- ζ_n^k is also a primitive nth root when gcd(k,n) = 1.
    This identifies all the primitive roots among powers of ζ_n. -/
theorem zeta_pow_isPrimitiveRoot_of_coprime (n : ℕ) (hn : 1 ≤ n) (k : ℕ)
    (hk : k.Coprime n) : IsPrimitiveRoot (zeta n ^ k) n :=
  (zeta_isPrimitiveRoot n hn).pow_of_coprime k hk

/-- cos(2kπ/n) = cos(2(n-k)π/n) for k ≤ n: cosines are symmetric about k = n/2.
    This is why the degree of minpoly(cos) is φ(n)/2 rather than φ(n):
    conjugates pair up as cos(2kπ/n) = cos(2(n-k)π/n). -/
theorem cos_symmetric (n k : ℕ) (hkn : k ≤ n) (hn : 1 ≤ n) :
    Real.cos (↑(n - k) * (2 * Real.pi / ↑n)) =
    Real.cos (↑k * (2 * Real.pi / ↑n)) := by
  have hn_ne : (↑n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [show (↑(n - k) : ℝ) * (2 * Real.pi / ↑n) =
      -(↑k * (2 * Real.pi / ↑n)) + 2 * Real.pi from by
    push_cast [Nat.cast_sub hkn]; field_simp; ring]
  rw [Real.cos_add_two_pi, Real.cos_neg]

/-- ζ_n^(n-k) = conj(ζ_n^k) for k ≤ n: powers symmetric about n/2 are conjugates.
    Proof: ζ^(n-k) = ζ^n · ζ^(-k) = ζ^(-k) = (ζ^k)⁻¹ = conj(ζ^k). -/
theorem zeta_pow_sub_eq_conj (n k : ℕ) (hn : 1 ≤ n) (hkn : k ≤ n) :
    zeta n ^ (n - k) = starRingEnd ℂ (zeta n ^ k) := by
  -- (ζ^k)⁻¹ = conj(ζ^k) since |ζ^k| = 1
  have h_conj : (zeta n ^ k)⁻¹ = starRingEnd ℂ (zeta n ^ k) := by
    apply inv_eq_of_mul_eq_one_right
    rw [Complex.mul_conj, ← Complex.ofReal_one]
    congr 1
    rw [Complex.normSq_eq_norm_sq, zeta_pow_norm_one, one_pow]
  rw [← h_conj]
  -- ζ^(n-k) * ζ^k = ζ^n = 1, so ζ^(n-k) = (ζ^k)⁻¹
  have hne : zeta n ^ k ≠ 0 := pow_ne_zero k (zeta_ne_zero n)
  have h_prod : zeta n ^ (n - k) * zeta n ^ k = 1 := by
    rw [← pow_add, show n - k + k = n from by omega, zeta_pow_n_eq_one n hn]
  exact mul_right_cancel₀ hne (by rw [h_prod, inv_mul_cancel₀ hne])

/-- For n ≥ 3 and 0 < k < n/2, ζ_n^k ∉ ℝ (has positive imaginary part).
    This proves ζ^k ≠ conj(ζ^k), i.e., the conjugate pairing is nontrivial. -/
theorem zeta_pow_not_real (n k : ℕ) (hn : 3 ≤ n) (hk0 : 0 < k)
    (hk : 2 * k < n) : ¬ ∃ r : ℝ, zeta n ^ k = ↑r := by
  rintro ⟨r, hr⟩
  have h_im : (zeta n ^ k).im = 0 := by rw [hr, Complex.ofReal_im]
  rw [← sin_eq_zeta_pow_im] at h_im
  have h_pos : 0 < Real.sin (↑k * (2 * Real.pi / ↑n)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hn_pos : (0 : ℝ) < ↑n := by positivity
      have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
      calc (↑k : ℝ) * (2 * Real.pi / ↑n)
          < ↑n / 2 * (2 * Real.pi / ↑n) := by
            apply mul_lt_mul_of_pos_right _ (by positivity)
            have : (↑(2 * k) : ℝ) < ↑n := by exact_mod_cast hk
            push_cast at this; linarith
        _ = Real.pi := by field_simp
  linarith

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
41. `zeta_eq_mathlib_form`: our ζ_n = Mathlib's exp(2πI/n)
42. `zeta_isPrimitiveRoot`: IsPrimitiveRoot ζ_n n (connects to Mathlib cyclotomic)
43. `zeta_pow_eq_one_iff`: ζ^k = 1 ↔ n ∣ k
44. `zeta_isRoot_cyclotomic`: ζ_n is root of Φ_n
45. `minpoly_zeta_dvd_cyclotomic`: minpoly(ℤ, ζ_n) | Φ_n
46. `zeta_pow_isPrimitiveRoot_of_coprime`: ζ^k primitive when gcd(k,n)=1
47. `cos_symmetric`: cos(2(n-k)π/n) = cos(2kπ/n)
48. `zeta_pow_sub_eq_conj`: ζ^(n-k) = conj(ζ^k)
49. `zeta_pow_not_real`: ζ^k ∉ ℝ for 0 < k < n/2

### Axiomatized: NONE (all axioms eliminated)
- `gauss_wantzel_theorem`: ✅ PROVED via degree theory from OQ02OQ03OQ01
- `cos_minpoly_gal_card`: ✅ ELIMINATED (bypassed by direct degree argument)
- `wantzel_galois_characterization`: ✅ ELIMINATED (bypassed by direct degree argument)
-/

/-
═══════════════════════════════════════════════════════════════════════════════
Section XVIII: ROOT CHARACTERIZATION FOR T_n - 1

Root characterization infrastructure (retained for mathematical completeness):
- Characterize when cos(2kπ/n) = cos(2jπ/n) (cosine equality criterion)
- Count distinct values in {cos(2kπ/n) : gcd(k,n) = 1}
- Show these are exactly the Galois conjugates of cos(2π/n)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- cos(α) = cos(β) iff ∃ k : ℤ, α = β + 2kπ or α = -β + 2kπ.
    Direct consequence of Mathlib's `Real.cos_eq_cos_iff`. -/
theorem cos_eq_cos_iff (α β : ℝ) :
    Real.cos α = Real.cos β ↔
      ∃ k : ℤ, α = β + 2 * ↑k * Real.pi ∨ α = -β + 2 * ↑k * Real.pi := by
  rw [Real.cos_eq_cos_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨-k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨k, Or.inr (by push_cast; linarith)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨-k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨k, Or.inr (by push_cast; linarith)⟩

/-- Two cosines of rational multiples of 2π/n are equal iff indices are conjugate mod n:
    cos(2kπ/n) = cos(2jπ/n) ↔ k ≡ j (mod n) ∨ k ≡ n-j (mod n). -/
theorem cos_2kpi_div_n_eq_iff (n : ℕ) (hn : 1 ≤ n) (k j : ℕ) :
    Real.cos (2 * ↑k * Real.pi / ↑n) = Real.cos (2 * ↑j * Real.pi / ↑n) ↔
      k % n = j % n ∨ k % n = (n - j % n) % n := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  rw [Real.cos_eq_cos_iff]
  constructor
  · rintro ⟨m, h | h⟩
    · -- h : 2jπ/n = 2mπ + 2kπ/n → j ≡ k (mod n)
      left
      have h_real : (↑j : ℝ) = ↑m * ↑n + ↑k := by
        have := h; field_simp at this ⊢; nlinarith
      have h_int : (↑j : ℤ) = m * ↑n + ↑k := by
        have : ((↑j : ℤ) : ℝ) = ((m * ↑n + ↑k : ℤ) : ℝ) := by
          push_cast; linarith [h_real]
        exact_mod_cast this
      -- j ≡ k (mod n) in ℤ → k % n = j % n in ℕ
      have h_dvd : (↑n : ℤ) ∣ ((↑j : ℤ) - ↑k) := ⟨m, by linarith⟩
      exact_mod_cast (Int.modEq_iff_dvd.mpr h_dvd : (↑k : ℤ) ≡ (↑j : ℤ) [ZMOD ↑n])
    · -- h : 2jπ/n = 2mπ - 2kπ/n → k ≡ n - j (mod n)
      right
      have h_real : (↑j : ℝ) + ↑k = ↑m * ↑n := by
        have := h; field_simp at this ⊢; nlinarith
      have h_int : (↑j : ℤ) + ↑k = m * ↑n := by
        have : ((↑j + ↑k : ℤ) : ℝ) = ((m * ↑n : ℤ) : ℝ) := by
          push_cast; linarith [h_real]
        exact_mod_cast this
      -- j + k ≡ 0 (mod n) → k % n = (n - j%n) % n
      have h_dvd_z : (↑n : ℤ) ∣ ((↑j : ℤ) + ↑k) := ⟨m, by linarith⟩
      have h_dvd_nat : n ∣ (j + k) := by exact_mod_cast h_dvd_z
      have h_sum : (j + k) % n = 0 := Nat.mod_eq_zero_of_dvd h_dvd_nat
      have hj_lt := Nat.mod_lt j (show 0 < n by omega)
      have hk_lt := Nat.mod_lt k (show 0 < n by omega)
      rw [Nat.add_mod] at h_sum
      by_cases hjz : j % n = 0
      · simp [hjz, Nat.mod_self] at h_sum ⊢; exact h_sum
      · rw [Nat.mod_eq_of_lt (by omega : n - j % n < n)]
        -- j%n + k%n is a positive multiple of n less than 2n, so equals n
        obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero h_sum
        -- hq : j%n + k%n = n * q, derive q = 1, then simplify
        have hq_eq : q = 1 := by
          have h_bound : j % n + k % n < 2 * n := by omega
          have hq1 : 0 < q := by
            by_contra h; push_neg at h
            rw [show q = 0 by omega, Nat.mul_zero] at hq; omega
          have hq2 : q < 2 := by
            by_contra h; push_neg at h
            have := Nat.mul_le_mul_left n h; omega
          omega
        rw [hq_eq, Nat.mul_one] at hq; omega
  · rintro (h | h)
    · -- k % n = j % n → cos equal via periodicity
      have h_modeq : (↑k : ℤ) ≡ (↑j : ℤ) [ZMOD ↑n] := by exact_mod_cast h
      obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp h_modeq
      -- hm : ↑j - ↑k = ↑n * m
      refine ⟨m, Or.inl ?_⟩
      have h_int : (↑j : ℤ) = m * ↑n + ↑k := by linarith
      have h_real : (↑j : ℝ) = ↑m * ↑n + ↑k := by
        have := congr_arg (Int.cast (R := ℝ)) h_int; push_cast at this; exact this
      field_simp; nlinarith [h_real]
    · -- k % n = (n - j % n) % n → cos equal via reflection
      have h_sum : (j + k) % n = 0 := by
        have hn_pos : 0 < n := by omega
        have hj_lt := Nat.mod_lt j hn_pos
        rw [Nat.add_mod, h]
        by_cases hjz : j % n = 0
        · simp [hjz, Nat.mod_self]
        · rw [Nat.mod_eq_of_lt (by omega : n - j % n < n),
              Nat.add_sub_cancel' (by omega : j % n ≤ n), Nat.mod_self]
      obtain ⟨m', hm'⟩ := Nat.dvd_of_mod_eq_zero h_sum
      have h_int : (↑j : ℤ) + ↑k = ↑m' * ↑n := by
        have := congr_arg (Nat.cast (R := ℤ)) hm'; push_cast at this; linarith
      refine ⟨(m' : ℤ), Or.inr ?_⟩
      have h_real : (↑j : ℝ) + ↑k = ↑(m' : ℤ) * ↑n := by exact_mod_cast h_int
      field_simp; nlinarith [h_real]

/-- If gcd(k, n) = 1 then gcd(n - k, n) = 1. -/
private lemma coprime_sub_self {n k : ℕ} (hk : k ≤ n) (hc : k.Coprime n) :
    (n - k).Coprime n := by
  rw [Nat.Coprime] at *
  by_contra hne
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hne
  have hpnk : p ∣ (n - k) := hpg.trans (Nat.gcd_dvd_left _ _)
  have hpn : p ∣ n := hpg.trans (Nat.gcd_dvd_right _ _)
  -- In ℤ: p | n and p | (n-k) implies p | k
  have hpk : p ∣ k := by
    have h1 : (↑p : ℤ) ∣ ↑n := by exact_mod_cast hpn
    have h2 : (↑p : ℤ) ∣ (↑(n - k) : ℤ) := by exact_mod_cast hpnk
    have h3 : (↑k : ℤ) = ↑n - ↑(n - k) := by push_cast; omega
    have h4 : (↑p : ℤ) ∣ (↑k : ℤ) := h3 ▸ dvd_sub h1 h2
    exact_mod_cast h4
  -- p | gcd(k, n) = 1, contradiction with p prime
  have : p ∣ Nat.gcd k n := Nat.dvd_gcd hpk hpn
  rw [hc] at this
  exact absurd (Nat.le_of_dvd one_pos this) (not_le.mpr hp.one_lt)

/-- For n ≥ 3 and coprime k ∈ (0, n), k ≠ n - k (the pairing has no fixed points). -/
private lemma coprime_ne_sub_self {n k : ℕ} (hn : 3 ≤ n) (hk0 : 0 < k) (hk : k < n)
    (hc : k.Coprime n) : k ≠ n - k := by
  intro h
  have hkn : k ∣ n := ⟨2, by omega⟩
  have := Nat.le_of_dvd (by omega) (Nat.dvd_gcd (dvd_refl k) hkn)
  rw [hc] at this; omega

/-- Coprime residues in range n are positive when n ≥ 3. -/
private lemma coprime_pos_of_ge_three {n k : ℕ} (hn : 3 ≤ n)
    (hk_mem : k ∈ Finset.filter (fun k => k.Coprime n) (Finset.range n)) : 0 < k := by
  have hk := Finset.mem_filter.mp hk_mem
  have hc := hk.2
  by_contra h; push_neg at h
  interval_cases k
  simp only [Nat.Coprime, Nat.gcd_zero_left] at hc; omega

/-- n - k is in the coprime filter when k is. -/
private lemma sub_mem_coprime_filter {n k : ℕ} (hn : 3 ≤ n) (hk0 : 0 < k)
    (hk : k < n) (hc : k.Coprime n) :
    n - k ∈ Finset.filter (fun j => j.Coprime n) (Finset.range n) := by
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, coprime_sub_self (by omega) hc⟩

/-- cos(2kπ/n) = cos(2(n-k)π/n) for k < n. Cosine pairs coprime residues. -/
theorem cos_complement_eq (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : k < n) :
    Real.cos (2 * ↑(n - k) * Real.pi / ↑n) = Real.cos (2 * ↑k * Real.pi / ↑n) := by
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hle : k ≤ n := le_of_lt hk
  rw [Nat.cast_sub hle]
  rw [show 2 * ((↑n : ℝ) - ↑k) * Real.pi / ↑n = -(2 * ↑k * Real.pi / ↑n - 2 * Real.pi)
    from by field_simp; ring]
  rw [Real.cos_neg, Real.cos_sub_two_pi]

/-- If k is coprime to n and k < n, then n - k is also coprime to n. -/
theorem coprime_complement (n k : ℕ) (hk : k < n) (hc : Nat.Coprime k n) :
    Nat.Coprime (n - k) n := by
  rw [Nat.Coprime] at *
  -- gcd(n-k, n) = gcd(n-k, k) via gcd(a, b + k*a) = gcd(a, b)
  have h1 : Nat.gcd (n - k) n = Nat.gcd (n - k) k := by
    have := Nat.gcd_add_mul_right_right (n - k) k 1
    rw [show k + 1 * (n - k) = n from by omega] at this
    exact this
  -- gcd(k, n-k) = gcd(k, n) by the same principle
  have h2 : Nat.gcd k (n - k) = Nat.gcd k n := by
    have := Nat.gcd_add_mul_right_right k (n - k) 1
    rw [show n - k + 1 * k = n from by omega] at this
    exact this.symm
  rw [h1, Nat.gcd_comm, h2]
  exact hc

/-- For n ≥ 3 and k coprime to n with 0 < k < n, we have k ≠ n - k.
    (k = n-k would give 2k = n, so gcd(k, n) = gcd(n/2, n) = n/2 ≥ 2, not coprime.) -/
theorem coprime_ne_complement (n k : ℕ) (hn : 3 ≤ n) (hk_pos : 0 < k) (hk_lt : k < n)
    (hc : Nat.Coprime k n) : k ≠ n - k := by
  intro heq
  have h2k : 2 * k = n := by omega
  have : Nat.gcd k n = k := by
    rw [← h2k]
    exact Nat.gcd_eq_left (Dvd.intro 2 (by omega))
  rw [Nat.Coprime, this] at hc
  omega  -- k = 1, but then n = 2, contradicting n ≥ 3

/-- The number of distinct Galois conjugates of cos(2π/n) over ℚ is φ(n)/2.
    The conjugates are {cos(2kπ/n) : 1 ≤ k ≤ n, gcd(k,n) = 1}, and these come
    in pairs {k, n-k} (since cos(2kπ/n) = cos(2(n-k)π/n)). -/
theorem galois_conjugate_count (n : ℕ) (hn : 3 ≤ n) :
    Finset.card (Finset.image (fun k => Real.cos (2 * ↑k * Real.pi / ↑n))
      (Finset.filter (fun k => Nat.Coprime k n) (Finset.range n))) =
    Nat.totient n / 2 := by
  -- Let S = coprime residues mod n, f = cos(2kπ/n)
  set S := Finset.filter (fun k => Nat.Coprime k n) (Finset.range n) with hS_def
  set f := fun k : ℕ => Real.cos (2 * ↑k * Real.pi / ↑n) with hf_def
  -- "Lower half": coprime residues with 2k < n
  set S₁ := S.filter (fun k => 2 * k < n) with hS₁_def
  -- Step 1: S₁ has cardinality totient(n) / 2
  -- The involution σ(k) = n - k maps S₁ ↔ S₂ := S.filter (fun k => 2k > n)
  -- with no fixed points (coprime_ne_sub_self ensures 2k ≠ n)
  have hS_card : S.card = Nat.totient n := by
    rw [hS_def]
    -- totient n = (range n).filter (n.Coprime ·)|.card, but our filter uses (k.Coprime n)
    -- These are equal since Nat.Coprime is symmetric (Nat.gcd is commutative)
    have : S = (Finset.range n).filter (fun k => n.Coprime k) := by
      ext k; simp only [Finset.mem_filter, hS_def]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩, fun ⟨h1, h2⟩ => ⟨h1, h2.symm⟩⟩
    rw [this]; rfl
  -- Step 2: image(f, S) = image(f, S₁)
  -- Because for k ∈ S with 2k ≥ n, n-k ∈ S₁ and f(k) = f(n-k)
  have himg : S.image f = S₁.image f := by
    ext x; simp only [Finset.mem_image]; constructor
    · rintro ⟨k, hk, rfl⟩
      by_cases h2k : 2 * k < n
      · exact ⟨k, Finset.mem_filter.mpr ⟨hk, h2k⟩, rfl⟩
      · -- k ∈ S but 2k ≥ n, so use n - k ∈ S₁ instead
        have hk_mem := Finset.mem_filter.mp hk
        have hk_range := Finset.mem_range.mp hk_mem.1
        have hk_cop := hk_mem.2
        have hk_pos : 0 < k := coprime_pos_of_ge_three hn hk
        -- n - k is coprime and in range
        have hnk_cop := coprime_sub_self (by omega) hk_cop
        have hnk_pos : 0 < n - k := by omega
        have hnk_lt : n - k < n := by omega
        have hnk_half : 2 * (n - k) < n := by omega
        have hnk_mem : n - k ∈ S₁ := by
          rw [hS₁_def]; simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨⟨⟨hnk_lt, hnk_cop⟩, hnk_half⟩⟩
        exact ⟨n - k, hnk_mem, (cos_complement_eq n (by omega) k hk_range).symm⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, Finset.filter_subset _ _ hk, rfl⟩
  -- Step 3: f is injective on S₁
  -- For k, j ∈ S₁ with 2k < n and 2j < n: f(k) = f(j) → k = j
  have hinj : Set.InjOn f ↑S₁ := by
    intro k hk j hj hfkj
    have hk_mem := Finset.mem_coe.mp hk
    have hj_mem := Finset.mem_coe.mp hj
    rw [hS₁_def] at hk_mem hj_mem
    have hk_filt := (Finset.mem_filter.mp hk_mem).1
    have hk_half := (Finset.mem_filter.mp hk_mem).2
    have hj_filt := (Finset.mem_filter.mp hj_mem).1
    have hj_half := (Finset.mem_filter.mp hj_mem).2
    have hk_range := Finset.mem_range.mp (Finset.mem_filter.mp hk_filt).1
    have hj_range := Finset.mem_range.mp (Finset.mem_filter.mp hj_filt).1
    -- Use cos_2kpi_div_n_eq_iff to get k%n = j%n ∨ k%n = (n-j%n)%n
    rw [hf_def] at hfkj
    rw [cos_2kpi_div_n_eq_iff n (by omega) k j] at hfkj
    simp only [Nat.mod_eq_of_lt hk_range, Nat.mod_eq_of_lt hj_range] at hfkj
    rcases hfkj with h | h
    · exact h
    · -- k = (n - j) % n with j < n means k = n - j
      rw [Nat.mod_eq_of_lt (by omega : n - j < n)] at h
      -- But 2k < n and 2j < n, so k + j < n, contradicting k = n - j (k + j = n)
      omega
  -- Step 4: Combine
  rw [himg, Finset.card_image_of_injOn hinj]
  -- Need: S₁.card = totient(n) / 2
  -- S₁ and S₂ partition S (no coprime k has 2k = n since gcd(n/2,n) ≥ 2)
  -- The involution k → n-k bijects S₁ to S₂, so |S₁| = |S₂| = |S|/2
  have hno_mid : ∀ k ∈ S, 2 * k ≠ n := by
    intro k hk h2k
    have hk_cop := (Finset.mem_filter.mp hk).2
    have : k ∣ n := ⟨2, by omega⟩
    have := Nat.le_of_dvd (by omega) (Nat.dvd_gcd (dvd_refl k) this)
    rw [hk_cop] at this; omega
  -- S₂ = S.filter (fun k => n < 2 * k)
  set S₂ := S.filter (fun k => n < 2 * k) with hS₂_def
  -- S = S₁ ∪ S₂ disjointly (since no coprime k has 2k = n)
  have hpart : S = S₁ ∪ S₂ := by
    ext k; simp only [Finset.mem_union, hS₁_def, hS₂_def,
      Finset.mem_filter]
    constructor
    · intro hk; by_cases h : 2 * k < n
      · left; exact ⟨hk, h⟩
      · right; exact ⟨hk, by omega⟩
    · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2; omega
  -- The involution σ(k) = n - k maps S₁ → S₂ injectively
  have hσ_inj : Set.InjOn (fun k => n - k) ↑S₁ := by
    intro a ha b hb hab
    have ha' := Finset.mem_coe.mp ha
    have hb' := Finset.mem_coe.mp hb
    omega
  have hσ_maps : ∀ k ∈ S₁, n - k ∈ S₂ := by
    intro k hk
    rw [hS₁_def] at hk
    have hk_S := (Finset.mem_filter.mp hk).1
    have hk_half := (Finset.mem_filter.mp hk).2
    have hk_cop := (Finset.mem_filter.mp hk_S).2
    have hk_range := Finset.mem_range.mp (Finset.mem_filter.mp hk_S).1
    have hk_pos := coprime_pos_of_ge_three hn hk_S
    rw [hS₂_def]; simp only [Finset.mem_filter, Finset.mem_range, hS_def]
    exact ⟨⟨⟨by omega, coprime_sub_self (by omega) hk_cop⟩, by omega⟩⟩
  -- σ maps S₂ → S₁ injectively (inverse)
  have hσ_inv : ∀ k ∈ S₂, n - k ∈ S₁ := by
    intro k hk
    rw [hS₂_def] at hk
    have hk_S := (Finset.mem_filter.mp hk).1
    have hk_half := (Finset.mem_filter.mp hk).2
    have hk_cop := (Finset.mem_filter.mp hk_S).2
    have hk_range := Finset.mem_range.mp (Finset.mem_filter.mp hk_S).1
    rw [hS₁_def]; simp only [Finset.mem_filter, Finset.mem_range, hS_def]
    exact ⟨⟨⟨by omega, coprime_sub_self (by omega) hk_cop⟩, by omega⟩⟩
  -- |S₁| = |S₂| via the bijection
  have hcard_eq : S₁.card = S₂.card := by
    apply le_antisymm
    · exact Finset.card_le_card_of_injOn (fun k => n - k) hσ_maps
        (fun a ha b hb hab => by omega)
    · exact Finset.card_le_card_of_injOn (fun k => n - k) hσ_inv
        (fun a ha b hb hab => by omega)
  -- |S| = |S₁| + |S₂| = 2 * |S₁|
  have hS_split : S.card = S₁.card + S₂.card := by
    rw [hpart]; exact Finset.card_union_of_disjoint hdisj
  rw [hS_card] at hS_split
  omega

/-- Every root of T_n - 1 in ℝ is of the form cos(2kπ/n) for some k.
    Proof: T_n(x) = cos(n·arccos(x)) for |x| ≤ 1. T_n(x) = 1 iff
    n·arccos(x) = 2kπ iff arccos(x) = 2kπ/n iff x = cos(2kπ/n). -/
theorem chebyshev_T_sub_one_roots (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : |x| ≤ 1)
    (h_root : Polynomial.aeval x (Chebyshev.T ℝ n - 1) = 0) :
    ∃ k : ℕ, k < n ∧ x = Real.cos (2 * ↑k * Real.pi / ↑n) := by
  -- Step 1: T_n(x) = 1
  have hT : Polynomial.aeval x (Chebyshev.T ℝ n) = 1 := by
    have := h_root; simp only [map_sub, map_one] at this; linarith
  -- Step 2: x = cos(arccos x) since |x| ≤ 1
  have hx1 : -1 ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ 1 := (abs_le.mp hx).2
  have hcos_arccos : Real.cos (Real.arccos x) = x := Real.cos_arccos hx1 hx2
  -- Step 3: cos(n * arccos x) = 1
  have hT' : Real.cos (↑(↑n : ℤ) * Real.arccos x) = 1 := by
    have key : Polynomial.aeval (Real.cos (Real.arccos x)) (Chebyshev.T ℝ n) =
               Real.cos (↑(↑n : ℤ) * Real.arccos x) := by
      rw [Chebyshev.aeval_T, Chebyshev.T_real_cos]
    rw [← key, hcos_arccos]; exact hT
  -- Step 4: n * arccos x = m * (2π) for some m : ℤ
  rw [Real.cos_eq_one_iff] at hT'
  obtain ⟨m, hm⟩ := hT'
  -- hm : ↑m * (2 * π) = ↑↑n * arccos x
  have hn_pos : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (by omega)
  have hn_ne : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h_arc_nn : 0 ≤ Real.arccos x := Real.arccos_nonneg x
  have h_arc_le : Real.arccos x ≤ Real.pi := Real.arccos_le_pi x
  -- Normalize ↑↑n to ↑n in hm for consistent reasoning
  have hm' : ↑m * (2 * Real.pi) = (↑n : ℝ) * Real.arccos x := by
    have := hm; push_cast [Int.cast_natCast] at this; linarith
  -- Step 5: m ≥ 0 (from arccos x ≥ 0 and n > 0)
  have hm_nn : 0 ≤ m := by
    by_contra h; push_neg at h
    have : (↑m : ℝ) < 0 := Int.cast_lt_zero.mpr h
    nlinarith [mul_nonneg (le_of_lt hn_pos) h_arc_nn]
  -- Step 6: m < n (from arccos x ≤ π)
  have hm_lt_n : m < ↑n := by
    by_contra h; push_neg at h
    have hm_bound : (↑n : ℝ) ≤ ↑m := by exact_mod_cast h
    -- From hm': m * 2π = n * arccos x ≤ n * π (since arccos x ≤ π)
    have h1 : ↑m * (2 * Real.pi) ≤ (↑n : ℝ) * Real.pi := by
      nlinarith [mul_le_mul_of_nonneg_left h_arc_le (le_of_lt hn_pos)]
    -- But m ≥ n → m * 2π ≥ n * 2π > n * π
    nlinarith [mul_le_mul_of_nonneg_right hm_bound (show (0 : ℝ) ≤ 2 * Real.pi by linarith)]
  -- Step 7: Convert m to ℕ
  set k := m.toNat with hk_def
  have hk_eq : (↑k : ℤ) = m := Int.toNat_of_nonneg hm_nn
  have hk_lt : k < n := by omega
  refine ⟨k, hk_lt, ?_⟩
  -- Step 8: x = cos(2kπ/n)
  -- arccos x = m * 2π / n, so x = cos(arccos x) = cos(2kπ/n)
  rw [← hcos_arccos]
  congr 1
  -- arccos x = m * 2π / n = 2kπ/n
  have h_arccos_eq : ↑(↑n : ℤ) * Real.arccos x = ↑m * (2 * Real.pi) := hm.symm
  have hm_eq : (↑m : ℝ) = ↑k := by exact_mod_cast hk_eq.symm
  rw [hm_eq] at h_arccos_eq
  -- h_arccos_eq : ↑↑n * arccos x = ↑k * (2 * π)
  -- goal: arccos x = 2 * ↑k * π / ↑n
  rw [eq_div_iff hn_ne]
  push_cast [Int.cast_natCast] at h_arccos_eq
  linarith

/-
## Section XXIII: Cyclotomic Tower Law (minpoly degree = φ(n)/2)

Proof strategy:
  1. minpoly ℚ ζ_n = Φ_n (cyclotomic), so natDegree = φ(n)
  2. cos(2π/n) = (ζ + ζ⁻¹)/2 ∈ ℚ(ζ_n), so ℚ(cos) ⊆ ℚ(ζ_n)
  3. ζ_n satisfies X² - 2cos·X + 1 = 0 over ℚ(cos), so [ℚ(ζ):ℚ(cos)] ≤ 2
  4. ζ_n ∉ ℝ for n ≥ 3, and ℚ(cos) ⊂ ℝ, so [ℚ(ζ):ℚ(cos)] = 2
  5. Tower: φ(n) = natDegree(minpoly ℚ cos) · 2, giving natDegree = φ(n)/2
-/

/-- ζ_n is integral (algebraic) over ℚ: it's a root of X^n - 1. -/
theorem zeta_isIntegral (n : ℕ) (hn : 1 ≤ n) : IsIntegral ℚ (zeta n) := by
  rw [← isAlgebraic_iff_isIntegral]
  refine ⟨X ^ n - C 1, ?_, ?_⟩
  · intro h
    have h1 : (X ^ n : ℚ[X]) = C 1 := sub_eq_zero.mp h
    have h2 := congr_arg Polynomial.natDegree h1
    simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at h2
    omega
  · simp only [map_sub, map_pow, aeval_X, map_one]
    rw [zeta_pow_n_eq_one n hn, sub_self]

/-- natDegree of the minimal polynomial of ζ_n over ℚ equals φ(n). -/
theorem minpoly_zeta_natDegree (n : ℕ) (hn : 1 ≤ n) :
    (minpoly ℚ (zeta n)).natDegree = Nat.totient n := by
  have h_prim := zeta_isPrimitiveRoot n hn
  have hirr := Polynomial.cyclotomic.irreducible_rat (n := n) (by omega)
  have hne : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
  rw [← h_prim.minpoly_eq_cyclotomic_of_irreducible hirr]
  exact Polynomial.natDegree_cyclotomic n ℚ

/-- finrank ℚ ℚ(ζ_n) = φ(n), where ℚ(ζ_n) = IntermediateField.adjoin ℚ {ζ_n} in ℂ. -/
theorem finrank_adjoin_zeta (n : ℕ) (hn : 1 ≤ n) :
    Module.finrank ℚ ↥(IntermediateField.adjoin ℚ ({zeta n} : Set ℂ)) =
    Nat.totient n := by
  rw [IntermediateField.adjoin.finrank (zeta_isIntegral n hn)]
  exact minpoly_zeta_natDegree n hn

/-- The complex cast of cos(2π/n) lies in ℚ(ζ_n): cos = (ζ + ζ⁻¹)/2 ∈ ℚ(ζ). -/
theorem cos_mem_adjoin_zeta (n : ℕ) :
    (↑(Real.cos (2 * Real.pi / ↑n)) : ℂ) ∈
    IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) := by
  have h_cos := cos_eq_half_zeta_add_conj n
  -- cos = (ζ + conj(ζ))/2, and conj(ζ) = ζ⁻¹ ∈ ℚ(ζ)
  rw [h_cos]
  have h_mem : zeta n ∈ IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) :=
    IntermediateField.mem_adjoin_simple_self ℚ (zeta n)
  set F := IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) with hF_def
  apply F.div_mem
  · apply F.add_mem
    · exact h_mem
    · rw [← zeta_inv_eq_conj n]
      exact F.inv_mem h_mem
  · exact F.natCast_mem 2

/-- ℚ(cos(2π/n)) ≤ ℚ(ζ_n) as intermediate fields of ℚ → ℂ. -/
theorem adjoin_cos_le_adjoin_zeta (n : ℕ) :
    IntermediateField.adjoin ℚ ({(↑(Real.cos (2 * Real.pi / ↑n)) : ℂ)} : Set ℂ) ≤
    IntermediateField.adjoin ℚ ({zeta n} : Set ℂ) :=
  IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (cos_mem_adjoin_zeta n))

set_option maxHeartbeats 800000 in
/-- The minimal polynomial of cos(2π/n) has degree exactly φ(n)/2.

    Proof: Cyclotomic tower law.
    ζ_n generates an extension of degree φ(n) over ℚ.
    cos(2π/n) = (ζ + ζ⁻¹)/2 generates a subfield, and ζ satisfies
    a quadratic X² - 2cos·X + 1 over it (irreducible since ζ ∉ ℝ).
    Tower: φ(n) = [ℚ(ζ):ℚ] = [ℚ(ζ):ℚ(cos)] · [ℚ(cos):ℚ] = 2 · natDegree(minpoly).

    This is now also proved independently in OQ02OQ03OQ01 via the fixed field approach. -/
theorem minpoly_cos_natDegree_eq (n : ℕ) (hn : 3 ≤ n) :
    (minpoly ℚ (Real.cos (2 * Real.pi / ↑n))).natDegree = Nat.totient n / 2 := by
  -- The key idea: work in ℂ with intermediate fields ℚ ⊂ ℚ(cos) ⊂ ℚ(ζ_n)
  set c := (↑(Real.cos (2 * Real.pi / ↑n)) : ℂ) with hc_def
  set ζ := zeta n with hζ_def
  set F := IntermediateField.adjoin ℚ ({c} : Set ℂ) with hF_def
  set E := IntermediateField.adjoin ℚ ({ζ} : Set ℂ) with hE_def
  -- Step 1: natDegree(minpoly ℚ cos_ℝ) = natDegree(minpoly ℚ cos_ℂ)
  -- because algebraMap ℝ ℂ is injective
  have h_minpoly_eq : minpoly ℚ (Real.cos (2 * Real.pi / ↑n)) =
      minpoly ℚ c := by
    exact (minpoly.algHom_eq (IsScalarTower.toAlgHom ℚ ℝ ℂ)
      (IsScalarTower.toAlgHom ℚ ℝ ℂ).injective _).symm
  rw [h_minpoly_eq]
  -- Step 2: natDegree(minpoly ℚ c) = finrank ℚ F
  have h_int_c : IsIntegral ℚ c := by
    exact (cos_2pi_div_n_isIntegral n (by omega)).map (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have h_deg_F : (minpoly ℚ c).natDegree = Module.finrank ℚ ↥F := by
    rw [IntermediateField.adjoin.finrank h_int_c]
  rw [h_deg_F]
  -- Step 3: finrank ℚ E = φ(n)
  have h_finrank_E := finrank_adjoin_zeta n (by omega : 1 ≤ n)
  -- Step 4: F ≤ E
  have hFE : F ≤ E := adjoin_cos_le_adjoin_zeta n
  -- Step 5: ℚ(cos) ⊂ ℝ (every element of F has zero imaginary part)
  have hF_real : ∀ x ∈ (F : Set ℂ), (x : ℂ).im = 0 := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem y hy =>
      rw [Set.mem_singleton_iff.mp hy, hc_def]; exact Complex.ofReal_im _
    | algebraMap q =>
      rw [IsScalarTower.algebraMap_apply ℚ ℝ ℂ]; exact Complex.ofReal_im _
    | add a b ha hb => simp [Complex.add_im, *]
    | inv a _ ih =>
      show (a⁻¹).im = 0
      by_cases ha0 : a = 0
      · simp [ha0]
      · have hre : a = ↑a.re := Complex.ext rfl (by rw [Complex.ofReal_im]; exact ih)
        rw [hre, ← Complex.ofReal_inv]; exact Complex.ofReal_im _
    | mul a b ha hb => simp [Complex.mul_im, *]
  -- Step 6: ζ ∉ F (since ζ.im ≠ 0 but all of F has im = 0)
  have hζ_notin_F : ζ ∉ (F : Set ℂ) := by
    intro hζF
    apply zeta_not_ofReal n hn
    exact ⟨ζ.re, Complex.ext rfl (hF_real ζ hζF)⟩
  -- Step 7: F < E (strict containment)
  have hFE_strict : F < E := lt_of_le_of_ne hFE (by
    intro h_eq
    exact hζ_notin_F (h_eq ▸ IntermediateField.mem_adjoin_simple_self ℚ ζ))
  -- Step 8: Set up algebra tower ℚ → ↥F → ↥E
  haveI : FiniteDimensional ℚ ↥E := adjoin.finiteDimensional (zeta_isIntegral n (by omega))
  haveI : FiniteDimensional ℚ ↥F := adjoin.finiteDimensional h_int_c
  letI algFE : Algebra ↥F ↥E :=
    (IntermediateField.inclusion hFE).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥F ↥E := IsScalarTower.of_algebraMap_eq (fun q => by
    show (IntermediateField.inclusion hFE) ((algebraMap ℚ ↥F) q) = (algebraMap ℚ ↥E) q
    ext; rfl)
  -- Step 9: Tower law + [E:F] = 2 → finrank ℚ F = φ(n)/2
  -- Tower law: [E:ℚ] = [F:ℚ] * [E:F]
  have h_tower := Module.finrank_mul_finrank ℚ ↥F ↥E
  -- [E:F] ≤ 2: ζ satisfies X² - 2cos·X + 1 over F (degree 2)
  -- [E:F] ≥ 2: F ≠ E (ζ ∉ F), so strict containment, so [E:F] > 1
  -- Therefore [E:F] = 2 and φ(n) = 2 * finrank ℚ F
  have h_ef_eq : Module.finrank ↥F ↥E = 2 := by
    -- Upper bound: [E:F] ≤ 2 via the quadratic X²-2cos·X+1
    have h_le : Module.finrank ↥F ↥E ≤ 2 := by
      have hζ_in_E : ζ ∈ (E : Set ℂ) :=
        IntermediateField.mem_adjoin_simple_self ℚ ζ
      set ζ_E : ↥E := ⟨ζ, hζ_in_E⟩ with hζ_E_def
      have h_int_ζ : IsIntegral ↥F ζ_E :=
        IsIntegral.tower_top (Algebra.IsIntegral.isIntegral (R := ℚ) ζ_E)
      -- Step A: F(ζ) = E (ζ generates E over any intermediate F ≥ ℚ)
      have h_top : IntermediateField.adjoin ↥F ({ζ_E} : Set ↥E) = ⊤ := by
        have h_int_ζ_outer := zeta_isIntegral n (by omega)
        -- ζ generates E over ℚ via PowerBasis
        let pb := IntermediateField.adjoin.powerBasis h_int_ζ_outer
        -- pb.gen and ζ_E have the same underlying value in ℂ
        have h_gen_eq : pb.gen = ζ_E := Subtype.ext rfl
        -- Algebra.adjoin ℚ {ζ_E} = ⊤
        have h_alg_top : Algebra.adjoin ℚ ({ζ_E} : Set ↥E) = ⊤ := by
          rw [← h_gen_eq]; exact pb.adjoin_gen_eq_top
        -- Lift to IntermediateField.adjoin
        have h_gen_Q : IntermediateField.adjoin ℚ ({ζ_E} : Set ↥E) = ⊤ := by
          rw [eq_top_iff]; intro x _
          exact IntermediateField.algebra_adjoin_le_adjoin ℚ ({ζ_E} : Set ↥E)
            (h_alg_top ▸ Algebra.mem_top)
        exact IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ h_gen_Q
      -- Step B: deg(minpoly F ζ) ≤ 2 (ζ satisfies X²-2cos·X+1 over F)
      have h_deg : (minpoly ↥F ζ_E).natDegree ≤ 2 := by
        have h_c_in_F : c ∈ (F : Set ℂ) := IntermediateField.mem_adjoin_simple_self ℚ c
        set cF : ↥F := ⟨c, h_c_in_F⟩
        -- Construct annihilating polynomial p = X² - 2cos·X + 1 over F
        set p : Polynomial ↥F :=
          Polynomial.C (1 : ↥F) * Polynomial.X ^ 2 +
          Polynomial.C (-(2 * cF) : ↥F) * Polynomial.X +
          Polynomial.C (1 : ↥F)
        -- p has degree 2
        have h_deg_p : p.natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
        -- ζ_E is a root of p (push to ℂ via Subtype.val_injective)
        have h_aeval : Polynomial.aeval ζ_E p = 0 := by
          have h_key := zeta_quadratic n
          -- Evaluate p at ζ_E explicitly
          have h_eval : Polynomial.aeval ζ_E p =
              ζ_E ^ 2 + algebraMap ↥F ↥E (-(2 * cF)) * ζ_E + 1 := by
            simp only [p, Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
              Polynomial.aeval_X, Polynomial.aeval_X_pow, map_one, one_mul]
          rw [h_eval]
          -- Embed in ℂ via injective E.subtype ring hom
          apply E.subtype.injective
          rw [map_zero, map_add, map_add, map_mul, map_pow, map_one]
          -- Goal: E.subtype ζ_E ^ 2 + E.subtype(algebraMap F E (-(2*cF))) * E.subtype ζ_E + 1 = 0
          -- These are definitionally equal (subtype/inclusion chain preserves values)
          show (zeta n) ^ 2 + (-(2 * ↑(Real.cos (2 * Real.pi / ↑n)))) * (zeta n) + 1 = 0
          linear_combination h_key
        -- minpoly divides p, so natDegree(minpoly) ≤ 2
        have h_dvd := minpoly.dvd (↥F) ζ_E h_aeval
        have h_p_ne : p ≠ 0 := by
          intro hp; rw [hp, Polynomial.natDegree_zero] at h_deg_p; omega
        exact le_trans (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne) (le_of_eq h_deg_p)
      -- Step C: finrank F E ≤ 2 (from adjoin F {ζ_E} = ⊤ + minpoly degree ≤ 2)
      have h_adj := IntermediateField.adjoin.finrank h_int_ζ
      have h_finrank_eq : Module.finrank ↥F ↥E = (minpoly ↥F ζ_E).natDegree := by
        have := h_adj; erw [h_top, IntermediateField.finrank_top'] at this; exact this
      linarith
    -- Lower bound: [E:F] ≥ 2 from tower law + strict inequality
    have h_ge : Module.finrank ↥F ↥E ≥ 2 := by
      have h_finrank_E' : Module.finrank ℚ ↥E = Nat.totient n := by
        rw [hE_def, hζ_def]; exact h_finrank_E
      have hφ2 : 2 ≤ Nat.totient n := by
        obtain ⟨k, hk⟩ := Nat.totient_even (show 2 < n by omega)
        have := (Nat.totient_pos).mpr (show 0 < n by omega)
        omega
      -- [E:F] ≠ 0 (from tower law + φ(n) ≥ 2)
      have h_ne_zero : Module.finrank ↥F ↥E ≠ 0 := by
        intro h0; rw [h0, mul_zero] at h_tower; linarith [h_finrank_E']
      -- [E:F] ≠ 1 (from F ⊊ E: same Q-dim would force F = E)
      have h_ne_one : Module.finrank ↥F ↥E ≠ 1 := by
        intro h1; rw [h1, mul_one] at h_tower
        have h_dim_eq : Module.finrank ℚ ↥F = Module.finrank ℚ ↥E := by
          linarith [h_finrank_E']
        exact absurd (IntermediateField.eq_of_le_of_finrank_eq hFE h_dim_eq)
          (ne_of_lt hFE_strict)
      omega
    omega
  -- Step 10: Goal is already finrank ℚ ↥F = n.totient / 2 (from rw in Steps 1-2)
  -- From tower: finrank ℚ F * 2 = finrank ℚ E = φ(n)
  have h_eq : Module.finrank ℚ ↥F * 2 = Nat.totient n := by
    have := h_tower; rw [h_ef_eq] at this; linarith [h_finrank_E]
  omega

end AngleTrisectionOQ02OQ03
