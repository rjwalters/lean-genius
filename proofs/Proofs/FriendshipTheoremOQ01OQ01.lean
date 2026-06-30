/-
Copyright (c) 2024-2025 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-
# Friendship Theorem OQ-01-OQ-01: The Integrality Condition for Strongly Regular Graphs

The Friendship Theorem (Erdős–Rényi–Sós, 1966) and its spectral proof
(`FriendshipTheoremOQ01`) hinge on a number-theoretic step: a `k`-regular
friendship graph has adjacency matrix satisfying `A² = (k-1)·I + J`, and the
characteristic-polynomial / UFD argument forces `k - 1` to be a perfect square.

The **open question OQ-04** of the parent entry asks whether this elementary
"polynomial + UFD" approach generalizes from friendship graphs to **strongly
regular graphs (SRGs)**.  A graph is strongly regular with parameters
`(n, k, λ, μ)` when it is `k`-regular, every pair of adjacent vertices has `λ`
common neighbors, and every pair of non-adjacent vertices has `μ` common
neighbors.  Its adjacency matrix satisfies the *quadratic* identity

  `A² = (k - μ)·I + μ·J + (λ - μ)·A`.

Off the all-ones eigenvector `𝟙` (eigenvalue `k`), the remaining eigenvalues
are the two roots `r, s` of

  `x² - (λ - μ)·x - (k - μ) = 0`,

so by Vieta `r + s = λ - μ` and `r·s = -(k - μ)`.  If they occur with
non-negative integer multiplicities `f` and `g`, then counting dimensions and
taking the trace of `A` (which is `0`, the graph being loopless) give

  `f + g = n - 1`        (dimensions)
  `k + f·r + g·s = 0`    (trace).

This file proves, **with zero axioms**, the classical *integrality / rationality
dichotomy* (Bose 1963 / Cameron–Van Lint) that this data forces:

  **either** the discriminant `D = (λ - μ)² + 4(k - μ)` is a perfect square
  (the "integer eigenvalue" case),

  **or** `f = g` and `2k + (n - 1)(λ - μ) = 0`
  (the "conference graph" / half case).

This is exactly the SRG analogue of the friendship step, and we recover that
step as a corollary: for friendship graphs `λ = μ = 1`, the half case is
impossible (it would need `2k = 0`), so the discriminant `4(k - 1)` — and hence
`k - 1` itself — must be a perfect square.

## Why this is conditional, not axiomatic

We take the eigenvalue/multiplicity equations (`f + g = n - 1`,
`k + f·r + g·s = 0`, `r + s = λ - μ`, `r·s = -(k - μ)`) as **hypotheses**, not
as `axiom` declarations.  They are the standard output of the spectral theorem
applied to the symmetric matrix `A`; Mathlib does not yet provide the spectral
decomposition of an arbitrary integer symmetric matrix at the generality
required (this is precisely the gap the parent entry's char-poly approach was
built to sidestep).  Encoding them as hypotheses keeps the theorem honest and
fully machine-checked: the *integrality argument itself* — the genuinely
number-theoretic content the open question asks about — is what we verify, and
it carries no assumptions.

## Status
- 0 axioms, 0 sorries — fully verified.
-/

namespace FriendshipTheoremSRGIntegrality

/-! ## Part I: Integer square helper lemmas -/

/-- If `m² ∣ c²` over `ℤ` then `m ∣ c`.  (Squares reflect divisibility.) -/
theorem dvd_of_sq_dvd_sq {m c : ℤ} (h : m ^ 2 ∣ c ^ 2) : m ∣ c := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h
    have hc2 : c ^ 2 = 0 := zero_dvd_iff.mp h
    rw [pow_two] at hc2
    rcases mul_eq_zero.mp hc2 with h' | h' <;> simp [h']
  · exact (Int.pow_dvd_pow_iff (by norm_num : (2 : ℕ) ≠ 0)).mp h

/-- **Core integrality lemma.** If `m² · D = c²` with `m ≠ 0`, then `D` is a
    perfect square.  This is the engine behind the SRG discriminant being a
    square. -/
theorem isSquare_of_sq_mul {m D c : ℤ} (hm : m ≠ 0) (h : m ^ 2 * D = c ^ 2) :
    IsSquare D := by
  have hdvd : m ^ 2 ∣ c ^ 2 := ⟨D, by linarith [h]⟩
  obtain ⟨t, rfl⟩ := dvd_of_sq_dvd_sq hdvd
  have hm2 : (m : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have heq : m ^ 2 * D = m ^ 2 * t ^ 2 := by rw [h]; ring
  have hDt : D = t ^ 2 := mul_left_cancel₀ hm2 heq
  exact ⟨t, by rw [hDt]; ring⟩

/-- If `4 * x` is a perfect square then so is `x`.  (Used to descend from the
    friendship discriminant `4(k-1)` to `k-1`.) -/
theorem isSquare_of_four_mul {x : ℤ} (h : IsSquare (4 * x)) : IsSquare x := by
  obtain ⟨y, hy⟩ := h
  have hdvd : (2 : ℤ) ∣ y * y := ⟨2 * x, by linarith [hy]⟩
  have h2y : (2 : ℤ) ∣ y := (Int.prime_two.dvd_or_dvd hdvd).elim id id
  obtain ⟨z, rfl⟩ := h2y
  refine ⟨z, ?_⟩
  have h4 : (4 : ℤ) ≠ 0 := by norm_num
  have hcancel : 4 * x = 4 * (z * z) := by rw [hy]; ring
  exact mul_left_cancel₀ h4 hcancel

/-! ## Part II: The strongly regular graph integrality dichotomy -/

/-- The **discriminant** of the restricted-eigenvalue quadratic
    `x² - (λ-μ)x - (k-μ)` of a strongly regular graph with parameters
    `(n, k, λ, μ)`. -/
def srgDiscriminant (k lam mu : ℤ) : ℤ := (lam - mu) ^ 2 + 4 * (k - mu)

/-- The **half-case quantity** `2k + (n-1)(λ-μ)`.  It vanishes exactly in the
    conference-graph case. -/
def srgHalfQuantity (n k lam mu : ℤ) : ℤ := 2 * k + (n - 1) * (lam - mu)

/-- **SRG integrality dichotomy** (Bose 1963 / Cameron–Van Lint).

Suppose a strongly regular graph with parameters `(n, k, λ, μ)` has restricted
eigenvalues `r, s : ℝ` (the roots of `x² - (λ-μ)x - (k-μ)`, so `r + s = λ - μ`
and `r·s = -(k - μ)`) occurring with non-negative integer multiplicities `f, g`
satisfying the dimension count `f + g = n - 1` and the zero-trace relation
`k + f·r + g·s = 0`.

Then **either** the discriminant `(λ-μ)² + 4(k-μ)` is a perfect square (integer
eigenvalues), **or** the multiplicities are equal and `2k + (n-1)(λ-μ) = 0`
(the conference-graph / half case).

This is the strongly-regular generalization of the friendship-graph step
`k - 1 = ⬚`, answering OQ-04 of the parent entry. -/
theorem srg_integrality
    (n k lam mu : ℤ) (f g : ℤ) (r s : ℝ)
    (_hf : 0 ≤ f) (_hg : 0 ≤ g)
    (hsum : f + g = n - 1)
    (hVietaSum : r + s = ((lam - mu : ℤ) : ℝ))
    (hVietaProd : r * s = (-(k - mu : ℤ) : ℝ))
    (htrace : (k : ℝ) + f * r + g * s = 0) :
    IsSquare (srgDiscriminant k lam mu) ∨
      (f = g ∧ srgHalfQuantity n k lam mu = 0) := by
  set c : ℤ := 2 * k + (n - 1) * (lam - mu) with hc
  -- Step 1: the real identity (f - g)(r - s) = -(2k + (n-1)(λ-μ)).
  have hfrgs : (f : ℝ) * r + g * s = -(k : ℝ) := by linarith [htrace]
  have hcastsum : ((f : ℝ) + g) = ((n - 1 : ℤ) : ℝ) := by exact_mod_cast hsum
  have hdiff : ((f : ℝ) - g) * (r - s) = -((c : ℤ) : ℝ) := by
    have e1 : (f : ℝ) * r + g * s = -(k : ℝ) := hfrgs
    have e2 : r + s = ((lam - mu : ℤ) : ℝ) := hVietaSum
    have e3 : (f : ℝ) + g = ((n - 1 : ℤ) : ℝ) := hcastsum
    have hcR : ((c : ℤ) : ℝ) = 2 * (k : ℝ) + ((n : ℝ) - 1) * ((lam : ℝ) - mu) := by
      rw [hc]; push_cast; ring
    rw [hcR]
    push_cast at e1 e2 e3 ⊢
    linear_combination (2 : ℝ) * e1 - ((f : ℝ) + g) * e2 - ((lam : ℝ) - mu) * e3
  -- Step 2: square it.  (r - s)² = (r + s)² - 4 r s = discriminant.
  have hrs_sq : (r - s) ^ 2 = ((srgDiscriminant k lam mu : ℤ) : ℝ) := by
    have hexpand : (r - s) ^ 2 = (r + s) ^ 2 - 4 * (r * s) := by ring
    rw [hexpand, hVietaSum, hVietaProd]
    simp only [srgDiscriminant]; push_cast; ring
  have hsq : ((f : ℝ) - g) ^ 2 * (r - s) ^ 2 = (c : ℝ) ^ 2 := by
    calc ((f : ℝ) - g) ^ 2 * (r - s) ^ 2
        = (((f : ℝ) - g) * (r - s)) ^ 2 := by ring
      _ = (-((c : ℤ) : ℝ)) ^ 2 := by rw [hdiff]
      _ = (c : ℝ) ^ 2 := by ring
  rw [hrs_sq] at hsq
  -- Push down to ℤ.
  have hInt : (f - g) ^ 2 * srgDiscriminant k lam mu = c ^ 2 := by exact_mod_cast hsq
  -- Step 3: integer dichotomy.
  rcases eq_or_ne (f - g) 0 with hfg | hfg
  · right
    have hfeqg : f = g := sub_eq_zero.mp hfg
    refine ⟨hfeqg, ?_⟩
    have hc2 : c ^ 2 = 0 := by rw [← hInt, hfg]; ring
    have hcc : c * c = 0 := by rw [pow_two] at hc2; exact hc2
    have hc0 : c = 0 := mul_self_eq_zero.mp hcc
    simp only [srgHalfQuantity]
    rw [← hc]; exact hc0
  · left
    exact isSquare_of_sq_mul hfg hInt

/-! ## Part III: Recovering the friendship-graph step (λ = μ = 1) -/

/-- **Friendship graphs as the `λ = μ = 1` special case.**

For a `k`-regular friendship graph with `k ≥ 1`, the SRG parameters are
`λ = μ = 1`, the half case is impossible (it would need `2k = 0`), and the
dichotomy collapses to its first branch: the discriminant `4(k - 1)` is a
perfect square, hence so is `k - 1`.  This is exactly the number-theoretic
heart of the spectral proof in `FriendshipTheoremOQ01`, re-derived from the
general SRG integrality theorem. -/
theorem friendship_discriminant_isSquare
    (n k : ℤ) (f g : ℤ) (r s : ℝ)
    (hk : 1 ≤ k)
    (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hsum : f + g = n - 1)
    (hVietaSum : r + s = ((1 - 1 : ℤ) : ℝ))
    (hVietaProd : r * s = (-(k - 1 : ℤ) : ℝ))
    (htrace : (k : ℝ) + f * r + g * s = 0) :
    IsSquare (k - 1) := by
  have H := srg_integrality n k 1 1 f g r s hf hg hsum hVietaSum hVietaProd htrace
  rcases H with hsq | ⟨_, hhalf⟩
  · have hd : srgDiscriminant k 1 1 = 4 * (k - 1) := by simp only [srgDiscriminant]; ring
    rw [hd] at hsq
    exact isSquare_of_four_mul hsq
  · exfalso
    simp only [srgHalfQuantity] at hhalf
    have h2k : 2 * k = 0 := by linear_combination hhalf
    omega

/-! ## Part IV: The conference-graph case -/

/-- In the conference-graph (half) case the equal multiplicities force `n` to be
    **odd**: from `f = g` and `f + g = n - 1` we get `n = 2f + 1`. -/
theorem srg_conference_card_odd
    (n f g : ℤ) (hfg : f = g) (hsum : f + g = n - 1) :
    Odd n := by
  refine ⟨f, ?_⟩
  linarith [hfg, hsum]

/-- In the conference-graph case the parameters satisfy `2k = (n-1)(μ-λ)`. -/
theorem srg_conference_param
    (n k lam mu : ℤ) (hhalf : srgHalfQuantity n k lam mu = 0) :
    2 * k = (n - 1) * (mu - lam) := by
  simp only [srgHalfQuantity] at hhalf
  linear_combination hhalf

/-! ## Part V: Worked example — the Petersen graph srg(10, 3, 0, 1)

The Petersen graph is strongly regular with `(n, k, λ, μ) = (10, 3, 0, 1)`.
Its restricted eigenvalues are `r = 1` (multiplicity `5`) and `s = -2`
(multiplicity `4`): `r + s = -1 = λ - μ`, `r·s = -2 = -(k - μ)`,
`f + g = 9 = n - 1`, and the trace `3 + 5·1 + 4·(-2) = 0`.  The discriminant is
`(0-1)² + 4(3-1) = 9 = 3²`, a perfect square — the integer-eigenvalue branch. -/
example : IsSquare (srgDiscriminant 3 0 1) ∨
    ((5 : ℤ) = 4 ∧ srgHalfQuantity 10 3 0 1 = 0) :=
  srg_integrality 10 3 0 1 5 4 (1 : ℝ) (-2 : ℝ)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The Petersen discriminant is concretely the perfect square `9 = 3²`. -/
example : srgDiscriminant 3 0 1 = 9 := by simp only [srgDiscriminant]; norm_num

end FriendshipTheoremSRGIntegrality
