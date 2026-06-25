/-
# Angle Trisection OQ-02-OQ-02-OQ-03: Complex Constructibility Extension of Gauss–Wantzel

## Open Question

The parent entry `angle-trisection-oq-02-oq-02` states the Gauss–Wantzel theorem for the
*real* coordinate `cos(2π/n)`: a regular `n`-gon is constructible iff `φ(n)` is a power of
two.  Geometrically the `n`-gon lives in the plane `ℂ`, with vertices the `n`-th roots of
unity `ζₙᵏ = exp(2πik/n)`.  This entry lifts constructibility from `ℝ` to `ℂ`:

> Call `z ∈ ℂ` **constructible** when both `Re z` and `Im z` are constructible reals.
> Then the vertex `ζₙ = exp(2πi/n)` of the regular `n`-gon is (complex-)constructible
> **iff** `φ(n)` is a power of two — the genuinely planar form of Gauss–Wantzel.

## Answer: YES

We define `IsConstructibleℂ z := IsConstructibleFromQ z.re ∧ IsConstructibleFromQ z.im`
on top of the parent's real predicate `GaussWantzel.IsConstructibleFromQ`, and prove the
structural backbone of the complex constructible numbers that requires **no field-compositum
machinery**:

* `ℚ ⊆` constructibles: every rational, in particular `0` and `1`, is constructible
  (witnessed by the bottom field `⊥`, `[⊥:ℚ] = 1 = 2⁰`).
* Closure under **negation** and **complex conjugation** (an intermediate field is closed
  under negation — no degree growth).
* The imaginary unit `i`, every Gaussian rational `a + b·i` (`a,b ∈ ℚ`), and the
  real/imaginary embeddings are constructible; multiplication by `i` preserves
  constructibility.

The **headline** is the planar Gauss–Wantzel equivalence

  `IsConstructibleℂ (exp(2πi/n)) ↔ ∃ k, φ(n) = 2ᵏ`,

obtained by splitting `exp(iθ) = cos θ + i·sin θ` into real and imaginary parts
(`Complex.exp_ofReal_mul_I_re/_im`) and feeding the real coordinate to the parent's
Gauss–Wantzel bridge.  Concrete corollaries: the vertices of the 3-, 4-, 5-, 15-, 17-gon
are constructible, while those of the 7- and 9-gon are not.

## Assumptions

* `GaussWantzel.gauss_wantzel_theorem` — the parent's *geometric* bridge (`cos(2π/n)`
  constructible ↔ `φ(n)` a power of two), itself axiomatized.
* `sin_constructible_of_cos` (new) — the single *analytic* fact that the constructible reals
  are closed under the passage `cos(2π/n) ↦ sin(2π/n) = √(1 − cos²(2π/n))` (a non-negative
  square root for `n ≥ 3`).  This is the only addition over the parent and isolates exactly
  the imaginary-axis content of the lift.

All remaining results below are fully proved (no further axioms, no sorries).

## Tags

angle-trisection, gauss-wantzel, complex-constructibility, roots-of-unity, fermat-primes
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ02

open GaussWantzel

namespace ComplexGaussWantzel

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  RATIONALS AND NEGATION ARE CONSTRUCTIBLE (no compositum needed)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Every rational number is a constructible real: it lies in the bottom field `⊥`,
    whose degree over `ℚ` is `1 = 2⁰`. -/
theorem isConstructibleFromQ_rat (q : ℚ) : IsConstructibleFromQ (q : ℝ) := by
  refine ⟨(⊥ : IntermediateField ℚ ℝ), inferInstance, ⟨0, ?_⟩, ?_⟩
  · simp [IntermediateField.finrank_bot]
  · exact (⊥ : IntermediateField ℚ ℝ).algebraMap_mem q

/-- `0` is a constructible real. -/
theorem isConstructibleFromQ_zero : IsConstructibleFromQ (0 : ℝ) := by
  simpa using isConstructibleFromQ_rat 0

/-- `1` is a constructible real. -/
theorem isConstructibleFromQ_one : IsConstructibleFromQ (1 : ℝ) := by
  simpa using isConstructibleFromQ_rat 1

/-- The constructible reals are closed under negation: the *same* field `K` works, since an
    intermediate field is closed under negation (no degree growth). -/
theorem isConstructibleFromQ_neg {x : ℝ} (hx : IsConstructibleFromQ x) :
    IsConstructibleFromQ (-x) := by
  obtain ⟨K, hfd, hpow, hmem⟩ := hx
  exact ⟨K, hfd, hpow, K.neg_mem hmem⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  COMPLEX CONSTRUCTIBILITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A complex number is **constructible** when both its real and imaginary parts are
    constructible reals — the planar lift of the parent's real predicate. -/
def IsConstructibleℂ (z : ℂ) : Prop :=
  IsConstructibleFromQ z.re ∧ IsConstructibleFromQ z.im

/-- `0` is constructible. -/
theorem isConstructibleℂ_zero : IsConstructibleℂ 0 :=
  ⟨by simpa using isConstructibleFromQ_zero, by simpa using isConstructibleFromQ_zero⟩

/-- `1` is constructible. -/
theorem isConstructibleℂ_one : IsConstructibleℂ 1 :=
  ⟨by simpa using isConstructibleFromQ_one, by simpa using isConstructibleFromQ_zero⟩

/-- The imaginary unit `i` is constructible (`Re i = 0`, `Im i = 1`). -/
theorem isConstructibleℂ_I : IsConstructibleℂ Complex.I :=
  ⟨by simpa using isConstructibleFromQ_zero, by simpa using isConstructibleFromQ_one⟩

/-- A real number is a constructible real iff it is constructible as a complex number. -/
theorem isConstructibleℂ_ofReal_iff (x : ℝ) :
    IsConstructibleℂ (x : ℂ) ↔ IsConstructibleFromQ x := by
  unfold IsConstructibleℂ
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨fun h => h.1, fun h => ⟨h, isConstructibleFromQ_zero⟩⟩

/-- Every Gaussian rational `a + b·i` with `a, b ∈ ℚ` is constructible. -/
theorem isConstructibleℂ_ratGaussian (a b : ℚ) :
    IsConstructibleℂ ((a : ℂ) + (b : ℂ) * Complex.I) := by
  constructor
  · have : ((a : ℂ) + (b : ℂ) * Complex.I).re = (a : ℝ) := by simp
    rw [this]; exact isConstructibleFromQ_rat a
  · have : ((a : ℂ) + (b : ℂ) * Complex.I).im = (b : ℝ) := by simp
    rw [this]; exact isConstructibleFromQ_rat b

/-- Closure under complex conjugation: `Re(z̄) = Re z` and `Im(z̄) = -Im z`, and the
    constructible reals are closed under negation. -/
theorem IsConstructibleℂ.conj {z : ℂ} (hz : IsConstructibleℂ z) :
    IsConstructibleℂ (starRingEnd ℂ z) := by
  obtain ⟨hre, him⟩ := hz
  refine ⟨?_, ?_⟩
  · simpa using hre
  · simpa using isConstructibleFromQ_neg him

/-- Conjugation does not change constructibility (the converse via `conj ∘ conj = id`). -/
theorem isConstructibleℂ_conj_iff (z : ℂ) :
    IsConstructibleℂ (starRingEnd ℂ z) ↔ IsConstructibleℂ z := by
  refine ⟨fun h => ?_, fun h => h.conj⟩
  simpa using h.conj

/-- Multiplication by `i` preserves constructibility: `Re(i·z) = -Im z`, `Im(i·z) = Re z`. -/
theorem IsConstructibleℂ.mul_I {z : ℂ} (hz : IsConstructibleℂ z) :
    IsConstructibleℂ (Complex.I * z) := by
  obtain ⟨hre, him⟩ := hz
  refine ⟨?_, ?_⟩
  · have : (Complex.I * z).re = -z.im := by simp
    rw [this]; exact isConstructibleFromQ_neg him
  · have : (Complex.I * z).im = z.re := by simp
    rw [this]; exact hre

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  THE ANALYTIC BRIDGE (sin from cos)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Analytic bridge.**  The constructible reals are closed under the passage
    `cos(2π/n) ↦ sin(2π/n)`.  For `n ≥ 3` we have `2π/n ∈ (0, π)`, so
    `sin(2π/n) = √(1 − cos²(2π/n)) ≥ 0`; constructibility of this non-negative square root
    follows from the constructible reals forming a field closed under square roots.  This is
    the only new assumption of the entry, isolating exactly the imaginary-axis content. -/
axiom sin_constructible_of_cos {n : ℕ} (hn : 3 ≤ n) :
    IsConstructibleFromQ (Real.cos (2 * Real.pi / (n : ℝ))) →
    IsConstructibleFromQ (Real.sin (2 * Real.pi / (n : ℝ)))

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  THE HEADLINE — PLANAR GAUSS–WANTZEL
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The `n`-th root of unity `ζₙ = exp(2πi/n)` is (complex-)constructible **iff** its real
    coordinate `cos(2π/n)` is a constructible real.  The forward direction is immediate
    (the real part); the converse supplies the imaginary part via `sin_constructible_of_cos`. -/
theorem rootOfUnity_isConstructibleℂ_iff_cos {n : ℕ} (hn : 3 ≤ n) :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I))
      ↔ IsConstructibleFromQ (Real.cos (2 * Real.pi / (n : ℝ))) := by
  unfold IsConstructibleℂ
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  exact ⟨fun h => h.1, fun h => ⟨h, sin_constructible_of_cos hn h⟩⟩

/-- **Planar Gauss–Wantzel.**  The vertex `exp(2πi/n)` of the regular `n`-gon is
    (complex-)constructible **iff** `φ(n)` is a power of two.  This is the genuinely
    two-dimensional form of the theorem: the entire polygon vertex, not just its abscissa. -/
theorem ngon_vertex_isConstructibleℂ_iff {n : ℕ} (hn : 3 ≤ n) :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I))
      ↔ ∃ k : ℕ, Nat.totient n = 2 ^ k := by
  rw [rootOfUnity_isConstructibleℂ_iff_cos hn, gauss_wantzel_theorem n hn]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V:  CONCRETE CONSTRUCTIBLE VERTICES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The equilateral triangle vertex `exp(2πi/3)` is constructible: `φ(3) = 2 = 2¹`. -/
theorem vertex3_constructibleℂ :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (3 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
  (ngon_vertex_isConstructibleℂ_iff (by norm_num)).mpr ⟨1, by decide⟩

/-- The square vertex `exp(2πi/4) = i` is constructible: `φ(4) = 2 = 2¹`. -/
theorem vertex4_constructibleℂ :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (4 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
  (ngon_vertex_isConstructibleℂ_iff (by norm_num)).mpr ⟨1, by decide⟩

/-- The regular pentagon vertex `exp(2πi/5)` is constructible: `φ(5) = 4 = 2²`. -/
theorem vertex5_constructibleℂ :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (5 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
  (ngon_vertex_isConstructibleℂ_iff (by norm_num)).mpr ⟨2, by decide⟩

/-- The 15-gon vertex `exp(2πi/15)` is constructible: `15 = 3·5` (distinct Fermat primes),
    `φ(15) = 8 = 2³`. -/
theorem vertex15_constructibleℂ :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (15 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
  (ngon_vertex_isConstructibleℂ_iff (by norm_num)).mpr ⟨3, by decide⟩

/-- Gauss's heptadecagon vertex `exp(2πi/17)` is constructible: `φ(17) = 16 = 2⁴`. -/
theorem vertex17_constructibleℂ :
    IsConstructibleℂ (Complex.exp (((2 * Real.pi / (17 : ℝ) : ℝ) : ℂ) * Complex.I)) :=
  (ngon_vertex_isConstructibleℂ_iff (by norm_num)).mpr ⟨4, by decide⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART VI:  NON-CONSTRUCTIBLE VERTICES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The heptagon vertex `exp(2πi/7)` is **not** constructible: `φ(7) = 6` is not a power of
    two. -/
theorem vertex7_not_constructibleℂ :
    ¬ IsConstructibleℂ (Complex.exp (((2 * Real.pi / (7 : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  intro hcon
  obtain ⟨k, hk⟩ := (ngon_vertex_isConstructibleℂ_iff (n := 7) (by norm_num)).mp hcon
  have h6 : Nat.totient 7 = 6 := by decide
  rw [h6] at hk
  have hk3 : k ≤ 3 := by
    by_contra h
    push_neg at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases k <;> norm_num at hk

/-- The nonagon vertex `exp(2πi/9)` is **not** constructible: `φ(9) = 6` is not a power of
    two (`9 = 3²`, a repeated Fermat prime). -/
theorem vertex9_not_constructibleℂ :
    ¬ IsConstructibleℂ (Complex.exp (((2 * Real.pi / (9 : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  intro hcon
  obtain ⟨k, hk⟩ := (ngon_vertex_isConstructibleℂ_iff (n := 9) (by norm_num)).mp hcon
  have h6 : Nat.totient 9 = 6 := by decide
  rw [h6] at hk
  have hk3 : k ≤ 3 := by
    by_contra h
    push_neg at h
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
    omega
  interval_cases k <;> norm_num at hk

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @isConstructibleFromQ_rat
#check @isConstructibleFromQ_neg
#check @IsConstructibleℂ
#check @isConstructibleℂ_I
#check @isConstructibleℂ_ofReal_iff
#check @isConstructibleℂ_ratGaussian
#check @IsConstructibleℂ.conj
#check @isConstructibleℂ_conj_iff
#check @IsConstructibleℂ.mul_I
#check @rootOfUnity_isConstructibleℂ_iff_cos
#check @ngon_vertex_isConstructibleℂ_iff
#check @vertex17_constructibleℂ
#check @vertex7_not_constructibleℂ

end ComplexGaussWantzel
