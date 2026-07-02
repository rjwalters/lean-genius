/-
Erdős Problem #516: Gap Series and the Minimum Modulus Problem

**Statement**: Let f(z) = Σ aₖzⁿᵏ be an entire function of finite order such that
nₖ/k → ∞ (Fabry gaps). Define M(r) = max_{|z|=r} |f(z)| and m(r) = min_{|z|=r} |f(z)|.
Is it true that lim sup (log m(r))/(log M(r)) = 1?

**Answer**: YES - proved by Fuchs (1963)

**Historical Development**:
- Pólya (1929): Originally posed this question
- Wiman (1914): Proved under (nₖ₊₁ - nₖ)² > nₖ
- Erdős & Macintyre (1954): Proved under Σ 1/(nₖ₊₁ - nₖ) < ∞
- Fuchs (1963): Full solution - lim sup = 1 for Fabry gaps
- Kovári (1965): Extended to nₖ > k(log k)^{2+c}

**Related Open Problem**: Does Σ 1/nₖ < ∞ suffice for arbitrary entire functions?

Reference: https://erdosproblems.com/516
-/

import Mathlib

open scoped Nat
open Filter Real Set Topology

namespace Erdos516

/-
## Gap Series Definitions

A **gap series** is a power series where many coefficients are zero.
The sequence (nₖ) records the positions of nonzero coefficients.
-/

/-- The Fabry gap condition: nₖ/k → ∞.
    This means the gaps between nonzero terms grow faster than linear. -/
def HasFabryGaps (n : ℕ → ℕ) : Prop :=
  Tendsto (fun k => (n k : ℝ) / k) atTop atTop

/-- The Fejér gap condition: Σ 1/nₖ < ∞.
    A distinct gap condition from Fabry gaps: in general neither implies
    the other. For increasing (nₖ), Σ 1/nₖ < ∞ forces nₖ/k → ∞ (so Fejér
    gaps imply Fabry gaps), but the converse fails — e.g. nₖ = k⌊log k⌋
    satisfies nₖ/k → ∞ while Σ 1/nₖ = Σ 1/(k⌊log k⌋) diverges. Hence there
    is no `fabry_implies_fejer` implication. -/
def HasFejerGaps (n : ℕ → ℕ) : Prop :=
  Summable (fun k => (1 : ℝ) / n k)

/-
## Structural Properties of the Gap Conditions (fully verified)

The lemmas below carry no axioms. They turn the informal descriptions of the
gap conditions into machine-checked statements and, most importantly, prove the
implication `Fejér gaps ⟹ Fabry gaps` for strictly increasing exponent
sequences — the relationship asserted (but not proved) in the definition of
`HasFejerGaps`.
-/

/-- **Fabry gaps dominate every linear function.** The condition `nₖ/k → ∞`
means precisely that for each slope `C`, eventually `C·k ≤ nₖ`. This is the
quantitative content of "the gaps grow faster than linear". -/
theorem fabry_gaps_ge {n : ℕ → ℕ} (h : HasFabryGaps n) (C : ℝ) :
    ∀ᶠ (k : ℕ) in atTop, C * (k : ℝ) ≤ (n k : ℝ) := by
  have h' : Tendsto (fun k => (n k : ℝ) / k) atTop atTop := h
  filter_upwards [h'.eventually_ge_atTop C, Filter.eventually_gt_atTop 0] with k hk hk0
  have hk' : C ≤ (n k : ℝ) / (k : ℝ) := hk
  have hk0' : (0 : ℝ) < k := by exact_mod_cast hk0
  rw [le_div_iff₀ hk0'] at hk'
  exact hk'

/-- **Fabry gaps force `nₖ → ∞`.** Taking slope `C = 1` in `fabry_gaps_ge`
shows the exponents themselves diverge. -/
theorem fabry_tendsto_atTop {n : ℕ → ℕ} (h : HasFabryGaps n) :
    Tendsto (fun k => (n k : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards [fabry_gaps_ge h 1] with k hk
  simpa using hk

/-- **Fejér gaps imply Fabry gaps (for strictly increasing exponents).**

If `(nₖ)` is strictly increasing and `Σ 1/nₖ < ∞`, then `nₖ/k → ∞`. This is the
implication referenced in the definition of `HasFejerGaps`: for increasing
sequences the Fejér condition is *stronger* than the Fabry condition. (The
converse fails, so the two conditions are genuinely distinct.)

Proof: fix a target slope `M`. Since the tail `∑_{i≥N} 1/nᵢ → 0`, choose `N`
with tail `< 1/(2M)`. For `k ≥ 2N` there are `k+1-N ≥ k/2` indices
`N, …, k`, and monotonicity gives `1/n_j ≥ 1/n_k` for each. Hence
`(k/2)·(1/n_k) ≤ ∑_{j=N}^{k} 1/n_j ≤ tail < 1/(2M)`, which rearranges to
`M ≤ n_k/k`. -/
theorem fejer_implies_fabry {n : ℕ → ℕ} (hmono : StrictMono n)
    (hfej : HasFejerGaps n) : HasFabryGaps n := by
  have hfej' : Summable (fun k => (1 : ℝ) / n k) := hfej
  set g : ℕ → ℝ := fun k => (1 : ℝ) / n k with hg
  have hg_nonneg : ∀ i, 0 ≤ g i := by
    intro i; simp only [hg]; positivity
  -- positivity of nₖ for k ≥ 1 (strict monotonicity of ℕ → ℕ)
  have hnpos : ∀ ⦃k⦄, 1 ≤ k → 0 < n k := by
    intro k hk
    have h1 : 0 < n 1 := (Nat.zero_le (n 0)).trans_lt (hmono (by norm_num))
    exact lt_of_lt_of_le h1 (hmono.monotone hk)
  show Tendsto (fun k => (n k : ℝ) / k) atTop atTop
  rw [tendsto_atTop]
  intro M
  rcases le_or_gt M 0 with hM | hM
  · filter_upwards with k
    show M ≤ (n k : ℝ) / (k : ℝ)
    have h0 : (0 : ℝ) ≤ (n k : ℝ) / (k : ℝ) := by positivity
    linarith
  · -- M > 0: pick N so the tail is < 1/(2M), then work with k ≥ 2N
    have hpos : (0 : ℝ) < 1 / (2 * M) := by positivity
    have htail : Tendsto (fun i => ∑' j, g (j + i)) atTop (𝓝 0) := tendsto_sum_nat_add g
    obtain ⟨N, hTN, hN1⟩ :=
      ((htail.eventually_lt_const hpos).and (Filter.eventually_ge_atTop 1)).exists
    filter_upwards [Filter.eventually_ge_atTop (2 * N)] with k hk2N
    have hk1 : 1 ≤ k := by omega
    have hNk1 : N ≤ k + 1 := by omega
    have hkpos : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hnpos hk1
    have hkℝ : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    -- Lower bound: each of the (Icc N k) terms is ≥ 1/n_k
    have lower : (Finset.Icc N k).card • g k ≤ ∑ j ∈ Finset.Icc N k, g j := by
      apply Finset.card_nsmul_le_sum
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hjpos : (0 : ℝ) < (n j : ℝ) := by exact_mod_cast hnpos (le_trans hN1 hj.1)
      have hjk : (n j : ℝ) ≤ (n k : ℝ) := by exact_mod_cast hmono.monotone hj.2
      simp only [hg]
      exact one_div_le_one_div_of_le hjpos hjk
    -- Block sum ≤ tail
    have hsum_le : ∑ j ∈ Finset.Icc N k, g j ≤ ∑' j, g (j + N) := by
      rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
      have hsummable : Summable (fun i => g (i + N)) := (summable_nat_add_iff N).2 hfej'
      calc ∑ i ∈ Finset.range (k + 1 - N), g (N + i)
            = ∑ i ∈ Finset.range (k + 1 - N), g (i + N) :=
              Finset.sum_congr rfl (fun i _ => by rw [Nat.add_comm])
        _ ≤ ∑' i, g (i + N) := hsummable.sum_le_tsum _ (fun i _ => hg_nonneg (i + N))
    -- Combine: card / n_k < 1/(2M)
    have hgk : g k = 1 / (n k : ℝ) := by simp only [hg]
    have hlt : ((Finset.Icc N k).card : ℝ) / (n k : ℝ) < 1 / (2 * M) := by
      have hle : (Finset.Icc N k).card • g k ≤ ∑' j, g (j + N) := le_trans lower hsum_le
      rw [nsmul_eq_mul, hgk, mul_one_div] at hle
      exact lt_of_le_of_lt hle hTN
    have hstep : ((Finset.Icc N k).card : ℝ) * (2 * M) < (n k : ℝ) := by
      have h2M : (0 : ℝ) < 2 * M := by positivity
      have h3 : ((Finset.Icc N k).card : ℝ) < 1 / (2 * M) * (n k : ℝ) :=
        (div_lt_iff₀ hkpos).1 hlt
      calc ((Finset.Icc N k).card : ℝ) * (2 * M)
            < (1 / (2 * M) * (n k : ℝ)) * (2 * M) := mul_lt_mul_of_pos_right h3 h2M
        _ = (n k : ℝ) := by field_simp
    -- card = k + 1 - N, hence k ≤ 2 * card
    have hcard : ((Finset.Icc N k).card : ℝ) = (k : ℝ) + 1 - (N : ℝ) := by
      rw [Nat.card_Icc, Nat.cast_sub hNk1]; push_cast; ring
    have hk2Nℝ : 2 * (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2N
    have hk2c : (k : ℝ) ≤ 2 * ((Finset.Icc N k).card : ℝ) := by rw [hcard]; linarith
    -- Finish: M * k ≤ n_k
    show M ≤ (n k : ℝ) / (k : ℝ)
    rw [le_div_iff₀ hkℝ]
    have hMk : M * (k : ℝ) ≤ M * (2 * ((Finset.Icc N k).card : ℝ)) :=
      mul_le_mul_of_nonneg_left hk2c hM.le
    nlinarith [hMk, hstep]

/-
## Entire Functions of Finite Order

An entire function is analytic on all of ℂ.
Finite order means the growth is at most exponential in |z|^a for some a.
-/

/-- An entire function f is of finite order if there exist c, a ≥ 0
    such that |f(z)| ≤ c · exp(|z|^a) for all z. -/
def OfFiniteOrder (f : ℂ → ℂ) : Prop :=
  Differentiable ℂ f ∧ ∃ c ≥ (0 : ℝ), ∃ a ≥ (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ c * rexp (‖z‖ ^ a)

/-- The order of an entire function is the infimum of valid exponents a. -/
noncomputable def orderOf (f : ℂ → ℂ) : ℝ :=
  sInf { a : ℝ | a ≥ 0 ∧ ∃ c ≥ (0 : ℝ), ∀ z : ℂ, ‖f z‖ ≤ c * rexp (‖z‖ ^ a) }

/-
## Maximum and Minimum Modulus

For an entire function f, we study its behavior on circles |z| = r.
-/

/-- The maximum modulus M(r) = max_{|z|=r} |f(z)|. -/
noncomputable def maxModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨆ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The minimum modulus m(r) = min_{|z|=r} |f(z)|. -/
noncomputable def minModulus (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  ⨅ z : {z : ℂ // ‖z‖ = r}, ‖f z‖

/-- The ratio log m(r) / log M(r). -/
noncomputable def modulusRatio (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (minModulus f r).log / (maxModulus f r).log

/-
## The Main Theorems

Fuchs (1963) proved that for Fabry gap series of finite order,
lim sup (log m(r))/(log M(r)) = 1.
-/

/--
**Fuchs's Theorem (1963)** - The Solution to Erdős Problem #516

Let f(z) = Σ aₖzⁿᵏ be an entire function of finite order with Fabry gaps (nₖ/k → ∞).
Then lim sup (log m(r))/(log M(r)) = 1.

More precisely, for any ε > 0, log m(r) > (1-ε) log M(r) holds outside
a set of logarithmic density 0.

This is axiomatized as the proof requires deep complex analysis
(Nevanlinna theory, Phragmén-Lindelöf principles) beyond current Mathlib.
-/
axiom fuchs_theorem {f : ℂ → ℂ} {n : ℕ → ℕ}
    (hn : HasFabryGaps n) {a : ℕ → ℂ}
    (hf_sum : ∀ z, HasSum (fun k => a k * z ^ n k) (f z))
    (hf_order : OfFiniteOrder f) :
    limsup (fun r => modulusRatio f r) atTop = 1

/-
## Historical Precedents

Earlier results under stronger gap conditions.
-/

/-
**Wiman's Theorem (1914)**

Under the stronger condition (nₖ₊₁ - nₖ)² > nₖ,
we get lim sup m(r)/M(r) = 1 (without logarithms!).
-/
/-
**Erdős-Macintyre Theorem (1954)**

Under Σ 1/(nₖ₊₁ - nₖ) < ∞, the result holds.
-/
/-
## Extensions Beyond Finite Order

Kovári (1965) extended the result to entire functions of infinite order
under a stronger gap condition.
-/

/-
**Kovári's Theorem (1965)**

For any entire function (not necessarily of finite order) with gaps
nₖ > k(log k)^{2+c} for some c > 0, the lim sup is still 1.
-/
/-
## The Remaining Open Question

Kovári's condition nₖ > k(log k)^{2+c} is stronger than Fejér gaps (Σ 1/nₖ < ∞).
It remains open whether Fejér gaps suffice for arbitrary entire functions.
-/

/--
**Open Conjecture**: Does Σ 1/nₖ < ∞ suffice?

For any entire function f(z) = Σ aₖzⁿᵏ with Fejér gaps,
is lim sup (log m(r))/(log M(r)) = 1?

Macintyre (1952) showed this would be optimal: if Σ 1/nₖ = ∞,
counterexamples exist.
-/
def fejer_gap_conjecture : Prop :=
  ∀ {f : ℂ → ℂ} {n : ℕ → ℕ},
    HasFejerGaps n →
    ∀ {a : ℕ → ℂ}, (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
    Differentiable ℂ f →
    limsup (fun r => modulusRatio f r) atTop = 1

/-
**Macintyre's Counterexample (1952)**

Given any sequence (nₖ) with Σ 1/nₖ = ∞, there exists an entire function
f(z) = Σ aₖzⁿᵏ that tends to 0 along the positive real axis.

This shows Fejér gaps would be the optimal condition if the conjecture holds.
-/
/-
## The Answer to Erdős Problem #516

The original question (for finite order with Fabry gaps) was answered
affirmatively by Fuchs in 1963.
-/

/-- Erdős Problem #516 is SOLVED: The answer is YES for finite order + Fabry gaps. -/
theorem erdos_516_solved :
    ∀ {f : ℂ → ℂ} {n : ℕ → ℕ},
      HasFabryGaps n →
      ∀ {a : ℕ → ℂ}, (∀ z, HasSum (fun k => a k * z ^ n k) (f z)) →
      OfFiniteOrder f →
      limsup (fun r => modulusRatio f r) atTop = 1 :=
  fun hn _ hf_sum hf_order => fuchs_theorem hn hf_sum hf_order

end Erdos516
