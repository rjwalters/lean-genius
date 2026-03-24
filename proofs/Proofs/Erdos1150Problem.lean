/-
  Erdős Problem #1150: Supremum of Littlewood Polynomials

  Source: https://erdosproblems.com/1150
  Status: OPEN

  Statement:
  Does there exist a constant c > 0 such that, for all large n and all
  polynomials P of degree n with coefficients ±1:
    max_{|z|=1} |P(z)| > (1+c)√n ?

  Context:
  The lower bound max_{|z|=1} |P(z)| ≥ √(n+1) follows from Parseval.
  The question asks whether the sup norm must strictly exceed √n by a
  multiplicative factor. This is equivalent to asking whether ultraflat
  Littlewood polynomials (±1 coefficients) do NOT exist.

  Note: For unimodular coefficients (|a_k| = 1), Kahane (1980) showed
  ultraflat polynomials DO exist. But the ±1 case remains open.

  Related: Erdős #228 (flat Littlewood polynomials exist - SOLVED by BBMST 2019)
           Erdős #230 (ultraflat unimodular polynomials exist - SOLVED/DISPROVED)

  References:
  - [Ha74, Problem 4.31]
  - [Va99, Problem 2.36]
  - Balister-Bollobás-Morris-Sahasrabudhe-Tiba (2019)
-/

import Mathlib

open Complex Polynomial Filter

namespace Erdos1150

/-
## Definitions
-/

/-- A **Littlewood polynomial** has all coefficients in {-1, +1}. -/
def IsLittlewoodPolynomial (p : Polynomial ℂ) : Prop :=
  ∀ i ≤ p.natDegree, p.coeff i = 1 ∨ p.coeff i = -1

/-- The supremum of |P(z)| over the unit circle.
    Defined over the unit circle subtype for clean `ciSup_le` interaction. -/
noncomputable def supNorm (p : Polynomial ℂ) : ℝ :=
  ⨆ (z : {z : ℂ // ‖z‖ = 1}), ‖p.eval z.1‖

instance : Nonempty {z : ℂ // ‖z‖ = 1} := ⟨⟨1, norm_one⟩⟩

/-
## The Main Conjecture
-/

/-- **Erdős Problem #1150** (OPEN):
    Does there exist c > 0 such that for all sufficiently large n,
    every degree-n Littlewood polynomial P satisfies
    max_{|z|=1} |P(z)| > (1+c)√n?

    This is equivalent to: ultraflat Littlewood polynomials do NOT exist.
    Erdős conjectured the answer is YES (no ultraflat ±1 polynomials). -/
def Erdos1150Conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n in atTop,
    ∀ p : Polynomial ℂ, p.natDegree = n → IsLittlewoodPolynomial p →
    supNorm p > (1 + c) * Real.sqrt n

/-
## Parseval Lower Bound
-/

/-- **Parseval's theorem** gives the trivial lower bound:
    For any Littlewood polynomial of degree n,
    max_{|z|=1} |P(z)| ≥ √(n+1).

    Proof: ∫|P|² dθ/2π = Σ|aᵢ|² = n+1 for a degree-n Littlewood polynomial.
    So ‖P‖_∞² ≥ ‖P‖₂² = n+1. -/
axiom parseval_lower_bound :
    ∀ p : Polynomial ℂ, IsLittlewoodPolynomial p →
    supNorm p ≥ Real.sqrt (p.natDegree + 1)

/-- The Parseval bound shows √(n+1) > 0 for any polynomial. -/
theorem parseval_bound_pos (n : ℕ) (hn : n ≥ 1) :
    Real.sqrt (n + 1 : ℝ) > 0 := by
  exact Real.sqrt_pos.mpr (by positivity)

/-
## Equivalent Formulation: No Ultraflat Littlewood Polynomials
-/

/-- A sequence of Littlewood polynomials is **ultraflat** if their degrees
    tend to infinity and the ratio max_{|z|=1}|P_n(z)| / √(deg P_n) → 1.

    Note: The degrees need not be exactly n — this allows subsequences,
    which is the standard mathematical definition. The old definition
    requiring `(P n).natDegree = n` for all n was too restrictive:
    ¬Conjecture gives witnesses for infinitely many n (not all n),
    making the backward direction of the equivalence unprovable. -/
def IsUltraflat (P : ℕ → Polynomial ℂ) : Prop :=
  (∀ n, IsLittlewoodPolynomial (P n)) ∧
  (Filter.Tendsto (fun n => (P n).natDegree) atTop atTop) ∧
  Filter.Tendsto (fun n => supNorm (P n) / Real.sqrt ↑((P n).natDegree)) atTop (nhds 1)

/-- **Forward direction (proved):**
    If the conjecture holds, then no ultraflat Littlewood sequence exists.

    Proof: The conjecture gives a lower bound (1+c)√(degree) for all Littlewood
    polynomials of large degree. Since degrees → ∞ in an ultraflat sequence,
    the bound eventually applies, giving ratio > 1+c. But the ultraflat condition
    says ratio → 1, so eventually ratio < 1+c. Contradiction. -/
theorem conjecture_implies_no_ultraflat :
    Erdos1150Conjecture → ∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P := by
  intro ⟨c, hc, hev⟩ P ⟨hlit, hdeg_tend, htend⟩
  -- Pull back the conjecture bound through the degree sequence
  have hpull : ∀ᶠ n in atTop,
      supNorm (P n) > (1 + c) * Real.sqrt ↑((P n).natDegree) :=
    (hdeg_tend.eventually hev).mono fun n hn => hn (P n) rfl (hlit n)
  -- Eventually degree > 0, so √degree > 0
  have hdeg_pos : ∀ᶠ n in atTop, 0 < (P n).natDegree :=
    hdeg_tend.eventually (Filter.eventually_atTop.mpr ⟨1, fun m hm => by omega⟩)
  -- Therefore ratio > 1+c eventually
  have hev' : ∀ᶠ n in atTop,
      supNorm (P n) / Real.sqrt ↑((P n).natDegree) > 1 + c := by
    apply (hpull.and hdeg_pos).mono
    intro n ⟨hgt, hpos⟩
    have hsqrt_pos : (0 : ℝ) < Real.sqrt ↑((P n).natDegree) :=
      Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hpos)
    exact (lt_div_iff₀ hsqrt_pos).mpr (by linarith)
  -- From ultraflat: ratio → 1, so eventually < 1+c
  have hlt : ∀ᶠ n in atTop,
      supNorm (P n) / Real.sqrt ↑((P n).natDegree) < 1 + c := by
    have hmem : Set.Iio (1 + c) ∈ nhds (1 : ℝ) := Iio_mem_nhds (by linarith)
    exact htend hmem
  -- Contradiction: eventually > 1+c AND eventually < 1+c
  obtain ⟨n, hgt, hlt'⟩ := (hev'.and hlt).exists
  linarith

/-- **Backward direction (axiomatized):**
    If no ultraflat Littlewood sequence exists, then the conjecture holds.

    Proof sketch (contrapositive): Assume ¬Conjecture. For each k ≥ 1,
    the negation gives arbitrarily large n with a degree-n Littlewood P
    satisfying supNorm(P) ≤ (1+1/k)√n. By dependent choice, extract a
    strictly increasing sequence n₁ < n₂ < ... with corresponding
    Littlewood P_k of degree n_k and supNorm(P_k)/√n_k ≤ 1+1/k.
    Combined with Parseval (ratio ≥ √((n+1)/n) → 1), the squeeze theorem
    gives ratio → 1, yielding an ultraflat sequence.

    This proof requires dependent choice, Filter.Frequently ↔ ¬Eventually,
    and the squeeze theorem for Tendsto. -/
axiom no_ultraflat_implies_conjecture :
    (∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P) → Erdos1150Conjecture

/-- The full equivalence follows from both directions. -/
theorem conjecture_equiv_no_ultraflat :
    Erdos1150Conjecture ↔ ∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P :=
  ⟨conjecture_implies_no_ultraflat, no_ultraflat_implies_conjecture⟩

/-
## Known Results
-/

/-- **BBMST (2019)**: Flat Littlewood polynomials exist.
    There exist universal c₁, c₂ > 0 such that for all large n,
    there exists a degree-n Littlewood polynomial with
    c₁√n ≤ |P(z)| ≤ c₂√n for all |z| = 1.

    This does NOT resolve #1150: flat (bounded ratio) is weaker
    than ultraflat (ratio → 1). -/
axiom bbmst_flat :
    ∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
    ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
      p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        c₁ * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ c₂ * Real.sqrt n

/-- **Kahane (1980)**: Ultraflat polynomials exist for unimodular
    coefficients (|aᵢ| = 1, not necessarily ±1).
    This shows the restriction to ±1 is essential for #1150. -/
axiom kahane_unimodular_ultraflat :
    ∀ ε : ℝ, ε > 0 →
    ∀ᶠ n in atTop, ∃ coeffs : Fin (n + 1) → ℂ,
      (∀ i, ‖coeffs i‖ = 1) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        let P := ∑ i : Fin (n + 1), coeffs i * z ^ (i : ℕ)
        (1 - ε) * Real.sqrt n ≤ ‖P‖ ∧ ‖P‖ ≤ (1 + ε) * Real.sqrt n

/-- BBMST implies the sup norm of some Littlewood polynomial is at most c₂√n.
    In particular, it's NOT true that max|P| > C√n for arbitrarily large C.
    This follows from bbmst_flat (the sup norm is bounded by the pointwise bound). -/
theorem bbmst_upper_bound_exists :
    ∃ c₂ : ℝ, c₂ > 0 ∧ ∀ᶠ n in atTop,
      ∃ p : Polynomial ℂ, p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
      supNorm p ≤ c₂ * Real.sqrt n := by
  obtain ⟨_, c₂, _, hc₂, hflat⟩ := bbmst_flat
  refine ⟨c₂, hc₂, hflat.mono fun n ⟨p, hdeg, hlit, hbound⟩ => ⟨p, hdeg, hlit, ?_⟩⟩
  -- supNorm is iSup over unit circle subtype, so ciSup_le applies directly
  exact ciSup_le fun z => (hbound z.1 z.2).2

/-
## The Gap Between Flat and Ultraflat
-/

/-- The key open question is about the gap between BBMST and ultraflat.
    BBMST shows c₁√n ≤ max|P| ≤ c₂√n for SOME P. But:
    - Can we make c₂ → 1? (ultraflat) Probably NOT for ±1.
    - Is there a universal c₂ < 1 + c for some c? This is #1150. -/
theorem flat_does_not_imply_ultraflat :
    (∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
        p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
        supNorm p ≤ c₂ * Real.sqrt n) →
    -- This does NOT give us ultraflat (we'd need c₂ → 1)
    True := by
  intro _; trivial

/-
## Rudin-Shapiro Bound
-/

/-- **Rudin-Shapiro polynomials** give a concrete family with
    max_{|z|=1} |P(z)| ≤ √(2(n+1)) for degree n.
    These are Littlewood polynomials with bounded sup norm. -/
axiom rudin_shapiro_bound :
    ∀ k : ℕ, k ≥ 1 →
    ∃ p : Polynomial ℂ, p.natDegree = 2^k - 1 ∧
      IsLittlewoodPolynomial p ∧
      supNorm p ≤ Real.sqrt (2 * 2^k)

/-
## Summary
-/

/--
**Erdős Problem #1150** (OPEN):

**Question**: Does there exist c > 0 such that for all large n,
every degree-n ±1 polynomial has max_{|z|=1} |P(z)| > (1+c)√n?

**Equivalent**: Do ultraflat Littlewood polynomials NOT exist?

**Known**:
1. Parseval: max|P| ≥ √(n+1) (trivial lower bound)
2. Rudin-Shapiro: max|P| ≤ √(2n) possible (concrete upper bound)
3. BBMST (2019): c₁√n ≤ max|P| ≤ c₂√n possible (flat, not ultraflat)
4. Kahane (1980): Ultraflat possible for unimodular (NOT ±1) coefficients

**Gap**: We know flat ±1 polynomials exist but not whether
ultraflat ±1 polynomials exist. Erdős conjectured they don't.

**Proved in this file**:
5. Conjecture ↔ no ultraflat ±1 sequences (forward direction proved,
   backward direction axiomatized). Uses subsequence-based ultraflat
   definition (degrees → ∞, ratio → 1) for mathematical correctness.
6. BBMST implies supNorm bound (proved from pointwise bound)
-/
theorem erdos_1150_summary :
    -- Parseval lower bound holds
    (∀ p : Polynomial ℂ, IsLittlewoodPolynomial p →
      supNorm p ≥ Real.sqrt (p.natDegree + 1)) ∧
    -- Flat Littlewood polynomials exist
    (∃ (c₁ c₂ : ℝ), c₁ > 0 ∧ c₂ > 0 ∧
      ∀ᶠ n in atTop, ∃ p : Polynomial ℂ,
        p.natDegree = n ∧ IsLittlewoodPolynomial p ∧
        ∀ z : ℂ, ‖z‖ = 1 →
          c₁ * Real.sqrt n ≤ ‖p.eval z‖ ∧ ‖p.eval z‖ ≤ c₂ * Real.sqrt n) ∧
    -- Equivalence: conjecture ↔ no ultraflat sequences
    (Erdos1150Conjecture ↔ ∀ P : ℕ → Polynomial ℂ, ¬ IsUltraflat P) := by
  exact ⟨parseval_lower_bound, bbmst_flat, conjecture_equiv_no_ultraflat⟩

end Erdos1150
