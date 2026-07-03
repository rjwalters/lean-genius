/-
  Laws of Large Numbers — OQ-01-OQ-02-OQ-01-OQ-02
  Marcinkiewicz–Zygmund SLLN: the Silverman–Toeplitz summability engine

  Chain:
    laws-of-large-numbers
      → -oq-01              (heavy-tailed LLN)
      → -oq-01-oq-02        (SLLN rate of convergence)
      → -oq-01-oq-02-oq-01  (Marcinkiewicz–Zygmund SLLN: Kronecker's lemma)
      → -oq-01-oq-02-oq-01-oq-02  (this leaf: package the Toeplitz null step into
                                    the general Silverman–Toeplitz theorem)

  The Kronecker-lemma entry (`LawsOfLargeNumbersOQ01OQ02OQ01.lean`) proved a single
  *nonnegative-weight* Toeplitz null step, `tendsto_weighted_average_zero`, and used
  it to close Kronecker's lemma.  Its second open question asked to package that step
  into the general **Silverman–Toeplitz regular-matrix summability theorem**, of which
  both that lemma and Mathlib's unweighted Cesàro mean are special cases.  This file
  supplies it.

  A (triangular) **summability matrix** `A : ℕ → ℕ → ℝ` transforms a sequence `x` into
  `y n = ∑_{k<n} A n k * x k`.  Toeplitz's classical characterisation says the method
  is **regular** — it preserves every limit — as soon as

    * (col) every column tends to `0`      : `∀ k, A · k → 0`,
    * (bnd) row absolute sums are bounded   : `∀ n, ∑_{k<n} |A n k| ≤ C`,
    * (row) row sums tend to `1`            : `∑_{k<n} A n k → 1`.

  This file proves both the null form and the full regular (limit-preserving) form,
  and derives the Cesàro mean as the special case `A n k = 1/n`, exhibiting the
  general engine that subsumes the earlier signed/normaliser Toeplitz step
  (its `A n k = c k / A_norm n`, with `C = 1`).

  Verified: 0 sorry, 0 axiom.
-/
import Mathlib

open Filter Finset
open scoped Topology

namespace LawsOfLargeNumbers.Toeplitz

/-- **Toeplitz null step (general, signed weights).** Let `A : ℕ → ℕ → ℝ` be a
triangular summability matrix whose row absolute sums are bounded by `C`
(`∑_{k<n} |A n k| ≤ C`) and each of whose columns tends to `0`
(`A · k → 0`). If `e k → 0`, then the transformed sequence
`∑_{k<n} A n k * e k → 0`.

This generalises the earlier nonnegative-weight step
(`tendsto_weighted_average_zero`): there `A n k = c k / A_norm n` with `c ≥ 0` and
`∑_{k<n} c k ≤ A_norm n`, giving row absolute sums `≤ 1` and columns
`c k / A_norm n → 0`.  Here the weights may have arbitrary sign; only the two
Toeplitz conditions are used.

Proof: given `ε`, past some `N` the factor `e k` is uniformly below
`ε / (2(C+1))`, so the tail contributes at most `(ε/2(C+1)) · C < ε/2`; the fixed
head `∑_{k<N} A n k * e k` is a finite sum of columns, each `→ 0`, hence `< ε/2`
eventually. -/
theorem tendsto_toeplitz_zero
    (A : ℕ → ℕ → ℝ) (e : ℕ → ℝ) (C : ℝ)
    (hbnd : ∀ n, ∑ k ∈ range n, |A n k| ≤ C)
    (hcol : ∀ k, Tendsto (fun n => A n k) atTop (𝓝 0))
    (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (fun n => ∑ k ∈ range n, A n k * e k) atTop (𝓝 0) := by
  have hC : (0 : ℝ) ≤ C := by have := hbnd 0; simpa using this
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (2 * (C + 1)) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  -- `e` is eventually below `δ`
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp he δ hδpos
  -- the head, a finite sum of columns, tends to `0`
  have hhead : Tendsto (fun n => ∑ k ∈ range N, A n k * e k) atTop (𝓝 0) := by
    have : Tendsto (fun n => ∑ k ∈ range N, A n k * e k) atTop
        (𝓝 (∑ k ∈ range N, (0 : ℝ) * e k)) := by
      apply tendsto_finset_sum
      intro k _
      exact (hcol k).mul_const (e k)
    simpa using this
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hhead (ε / 2) (by positivity)
  refine ⟨max M N, fun n hn => ?_⟩
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hnN : N ≤ n := le_trans (le_max_right _ _) hn
  rw [Real.dist_eq, sub_zero]
  -- split the sum at `N`
  have hsplit : (∑ k ∈ range n, A n k * e k)
      = (∑ k ∈ range N, A n k * e k) + ∑ k ∈ Ico N n, A n k * e k := by
    rw [Finset.sum_range_add_sum_Ico _ hnN]
  rw [hsplit]
  -- head bound
  have hheadb : |∑ k ∈ range N, A n k * e k| < ε / 2 := by
    have := hM n hnM; rw [Real.dist_eq, sub_zero] at this; exact this
  -- tail bound: `≤ δ * C`
  have htailb : |∑ k ∈ Ico N n, A n k * e k| ≤ δ * C := by
    calc |∑ k ∈ Ico N n, A n k * e k|
        ≤ ∑ k ∈ Ico N n, |A n k * e k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Ico N n, |A n k| * δ := by
            apply Finset.sum_le_sum
            intro k hk
            rw [abs_mul]
            have hek : |e k| ≤ δ := by
              have := hN k (mem_Ico.1 hk).1
              rw [Real.dist_eq, sub_zero] at this
              exact this.le
            exact mul_le_mul_of_nonneg_left hek (abs_nonneg _)
      _ = (∑ k ∈ Ico N n, |A n k|) * δ := by rw [Finset.sum_mul]
      _ ≤ (∑ k ∈ range n, |A n k|) * δ := by
            apply mul_le_mul_of_nonneg_right _ hδpos.le
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · rw [range_eq_Ico]; exact Ico_subset_Ico (Nat.zero_le _) le_rfl
            · exact fun k _ _ => abs_nonneg _
      _ ≤ C * δ := mul_le_mul_of_nonneg_right (hbnd n) hδpos.le
      _ = δ * C := by ring
  -- `δ * C ≤ ε / 2`
  have hδC : δ * C ≤ ε / 2 := by
    rw [hδdef, div_mul_eq_mul_div,
        div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))]
    nlinarith [hε, hC]
  calc |(∑ k ∈ range N, A n k * e k) + ∑ k ∈ Ico N n, A n k * e k|
      ≤ |∑ k ∈ range N, A n k * e k| + |∑ k ∈ Ico N n, A n k * e k| := abs_add_le _ _
    _ < ε / 2 + δ * C := by linarith [hheadb, htailb]
    _ ≤ ε / 2 + ε / 2 := by linarith [hδC]
    _ = ε := by ring

/-- **Silverman–Toeplitz regularity theorem.** A triangular summability matrix `A`
that is (col) column-null, (bnd) row-absolutely bounded and (row) row-sum-normalised
to `1` is **regular**: it preserves every limit. If `x n → L`, then the transformed
sequence `∑_{k<n} A n k * x k → L`.

This is the sufficiency ("Toeplitz") direction of the Silverman–Toeplitz theorem;
Mathlib's Cesàro mean and the Marcinkiewicz–Zygmund Kronecker step are both instances.

Proof: write `∑ A n k x k = ∑ A n k (x k − L) + (∑ A n k) · L`.  The first term is
`tendsto_toeplitz_zero` applied to the null sequence `x k − L`; the second tends to
`1 · L = L` by (row). -/
theorem tendsto_toeplitz
    (A : ℕ → ℕ → ℝ) (x : ℕ → ℝ) (L C : ℝ)
    (hbnd : ∀ n, ∑ k ∈ range n, |A n k| ≤ C)
    (hcol : ∀ k, Tendsto (fun n => A n k) atTop (𝓝 0))
    (hrow : Tendsto (fun n => ∑ k ∈ range n, A n k) atTop (𝓝 1))
    (hx : Tendsto x atTop (𝓝 L)) :
    Tendsto (fun n => ∑ k ∈ range n, A n k * x k) atTop (𝓝 L) := by
  -- null part: `∑ A n k (x k − L) → 0`
  have hnull := tendsto_toeplitz_zero A (fun k => x k - L) C hbnd hcol
    (by have := hx.sub_const L; simpa using this)
  -- row part: `(∑ A n k) · L → 1 · L = L`
  have hrowL : Tendsto (fun n => (∑ k ∈ range n, A n k) * L) atTop (𝓝 (1 * L)) :=
    hrow.mul_const L
  rw [one_mul] at hrowL
  have hsum := hnull.add hrowL
  rw [zero_add] at hsum
  -- reassemble pointwise: `∑ A n k (x k − L) + (∑ A n k) · L = ∑ A n k · x k`
  refine Tendsto.congr (fun n => ?_) hsum
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

/-- **Cesàro mean as a Silverman–Toeplitz instance.** The unweighted average of a
convergent sequence converges to the same limit — obtained here from
`tendsto_toeplitz` with the matrix `A n k = 1/n` (columns `1/n → 0`, row absolute
sums `= 1 ≤ 1`, row sums `= 1`).  This is the classical special case; it matches
Mathlib's `Filter.Tendsto.cesaro` and witnesses that the general engine subsumes it. -/
theorem tendsto_cesaro_of_toeplitz (x : ℕ → ℝ) (L : ℝ)
    (hx : Tendsto x atTop (𝓝 L)) :
    Tendsto (fun n => (∑ k ∈ range n, x k) / n) atTop (𝓝 L) := by
  have h := tendsto_toeplitz (fun n _ => (n : ℝ)⁻¹) x L 1 ?_ ?_ ?_ hx
  · refine h.congr (fun n => ?_)
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · -- (bnd) `∑_{k<n} |1/n| ≤ 1`
    intro n
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · have : ∑ k ∈ range n, |(↑n : ℝ)⁻¹| = 1 := by
        rw [Finset.sum_const, card_range, nsmul_eq_mul, abs_of_nonneg (by positivity),
            mul_inv_cancel₀ (by exact_mod_cast h0.ne')]
      exact le_of_eq this
  · -- (col) each column `1/n → 0`
    intro k
    exact tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  · -- (row) `∑_{k<n} 1/n → 1`
    have hev : (fun n => ∑ k ∈ range n, (↑n : ℝ)⁻¹) =ᶠ[atTop] (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Finset.sum_const, card_range, nsmul_eq_mul,
          mul_inv_cancel₀ (by exact_mod_cast hn.ne')]
    exact tendsto_const_nhds.congr' hev.symm

end LawsOfLargeNumbers.Toeplitz

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms LawsOfLargeNumbers.Toeplitz.tendsto_toeplitz
