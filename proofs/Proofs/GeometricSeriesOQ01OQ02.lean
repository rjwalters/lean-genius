import Mathlib
import Proofs.GeometricSeriesOQ01

/-
# Geometric Series OQ-01 / OQ-02: Cesàro (C,1) regularity and its strict extension

## The Open Question (OQ-02 of `geometric-series-oq-01`)

The parent entry proves the *concrete* Grandi instance by hand: the Cesàro
mean of `1 - 1 + 1 - 1 + ⋯` converges to `1/2` (`grandiCesaro_tendsto`).
OQ-02 asks for the *general* statement behind that bespoke computation — the
**regularity** (a.k.a. consistency) property of (C,1) summation:

> If a series `∑ aₙ` converges (in the ordinary sense) to `s`, then its
> Cesàro mean also converges to `s`. Moreover (C,1) summability is *strictly*
> stronger than convergence: there exist divergent series that are (C,1)
> summable.

## What this file proves

* `cesaroMean S n = (n:ℝ)⁻¹ * ∑ k ∈ range n, S k` — the (C,1) average of the
  *partial-sum sequence* `S` (the object one averages is the partial sums,
  **not** the terms `aₙ`; averaging the terms gives `0` whenever `∑ aₙ`
  converges, which is not the (C,1) mean of the series).
* `CesaroSummable S L` — predicate: the partial-sum sequence `S` is (C,1)
  summable to `L`.
* **M1 — regularity** (`cesaroSummable_of_tendsto`): ordinary convergence of
  the partial sums to `s` implies (C,1) summability to the same `s`. This is
  a one-line consequence of Mathlib's `Filter.Tendsto.cesaro`, applied to the
  partial-sum sequence. A `HasSum` corollary (`cesaroSummable_of_hasSum`) is
  also provided.
* **M2 — strict extension** (`cesaro_strictly_extends_convergence`): Grandi's
  series witnesses that the converse of regularity fails. Its partial sums
  `Sₙ = ∑_{i<n} (-1)ⁱ` are (C,1) summable to `1/2`, yet the sequence `Sₙ`
  itself does *not* converge (it oscillates `0,1,0,1,…`).

The (C,1) mean of Grandi here is computed via the clean closed form
`∑_{k<n} Sₖ = (n − Sₙ)/2`, giving `cesaroMean = (n − Sₙ)/(2n)` and hence
`|cesaroMean − 1/2| = |Sₙ|/(2n) ≤ 1/(2n) → 0`.

## Relationship to the parent

The parent `GeometricSeriesOQ01.grandiCesaro_tendsto` averages `S₁,…,Sₙ`
(an index-shifted variant that drops the empty partial sum `S₀ = 0`); this
file averages `S₀,…,S_{n-1}`, matching Mathlib's `Filter.Tendsto.cesaro`
convention exactly. Both averages share the limit `1/2`. The parent's
`grandi_even`, `grandi_odd`, and `grandi_double_sum` are reused here.

## Axiom / sorry status

No axioms, no sorries. Everything reduces to `Filter.Tendsto.cesaro`,
`HasSum.tendsto_sum_nat`, and the parent's elementary Grandi lemmas.
-/

namespace GeometricSeriesOQ01OQ02

open Finset Filter

/-- The Cesàro (C,1) mean of a partial-sum sequence `S`:
    `σₙ = (1/n) · (S₀ + S₁ + ⋯ + S_{n-1})`. Matches the convention of
    Mathlib's `Filter.Tendsto.cesaro` (division by `n` over `range n`). -/
noncomputable def cesaroMean (S : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ k ∈ range n, S k

/-- A partial-sum sequence `S` is **Cesàro (C,1) summable to `L`** if its
    Cesàro means converge to `L`. -/
def CesaroSummable (S : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto (cesaroMean S) atTop (nhds L)

-- ============================================================
-- M1: Regularity of (C,1) summation
-- ============================================================

/-- **Regularity / consistency of (C,1) summation.**
    If the partial sums `S N = ∑_{i<N} aᵢ` converge to `s`, then the Cesàro
    mean of `S` also converges to `s`. Immediate from `Filter.Tendsto.cesaro`. -/
theorem cesaroSummable_of_tendsto {a : ℕ → ℝ} {s : ℝ}
    (h : Tendsto (fun N => ∑ i ∈ range N, a i) atTop (nhds s)) :
    CesaroSummable (fun N => ∑ i ∈ range N, a i) s :=
  h.cesaro

/-- Corollary: if `∑ aₙ` is unconditionally summable with sum `s`
    (`HasSum a s`), then its ordered partial sums are (C,1) summable to `s`. -/
theorem cesaroSummable_of_hasSum {a : ℕ → ℝ} {s : ℝ} (h : HasSum a s) :
    CesaroSummable (fun N => ∑ i ∈ range N, a i) s :=
  cesaroSummable_of_tendsto h.tendsto_sum_nat

-- ============================================================
-- M2: Grandi's series — (C,1) summable but divergent
-- ============================================================

/-- Closed form for the running sum of Grandi partial sums:
    `∑_{k<n} (∑_{i<k} (-1)ⁱ) = (n − ∑_{i<n} (-1)ⁱ) / 2`.
    Proved by induction using `grandi_double_sum` (`2·Sₙ = 1 − (−1)ⁿ`). -/
theorem sum_grandiPartial (n : ℕ) :
    (∑ k ∈ range n, (∑ i ∈ range k, (-1 : ℝ) ^ i))
      = ((n : ℝ) - ∑ i ∈ range n, (-1 : ℝ) ^ i) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have h := GeometricSeriesOQ01.grandi_double_sum n
    push_cast
    linarith [h]

/-- The Grandi partial sum `Sₙ = ∑_{i<n} (-1)ⁱ` satisfies `|Sₙ| ≤ 1`
    (it is `0` for even `n`, `1` for odd `n`). -/
theorem grandi_partial_abs_le_one (n : ℕ) :
    |∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ 1 := by
  have h := GeometricSeriesOQ01.grandi_double_sum n
  have hb : (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
    rcases Nat.even_or_odd n with he | ho
    · exact Or.inl (Even.neg_one_pow he)
    · exact Or.inr (Odd.neg_one_pow ho)
  rw [abs_le]
  rcases hb with hb | hb <;> rw [hb] at h <;> constructor <;> linarith

/-- The Cesàro mean of Grandi's partial sums in closed form:
    `σₙ = (1/n) · (n − Sₙ)/2`. -/
theorem grandiCesaroMean_eq (n : ℕ) :
    cesaroMean (fun N => ∑ i ∈ range N, (-1 : ℝ) ^ i) n
      = (n : ℝ)⁻¹ * (((n : ℝ) - ∑ i ∈ range n, (-1 : ℝ) ^ i) / 2) := by
  simp only [cesaroMean]
  rw [sum_grandiPartial]

/-- **The Cesàro mean of Grandi's series converges to `1/2`.**
    Bound: `|σₙ − 1/2| = |Sₙ|/(2n) ≤ 1/(2n)`. -/
theorem grandiCesaroMean_tendsto :
    CesaroSummable (fun N => ∑ i ∈ range N, (-1 : ℝ) ^ i) (1 / 2) := by
  unfold CesaroSummable
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (2 * ε))
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 0 < n := lt_of_lt_of_le Nat.one_pos (le_of_max_le_right hn)
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn1
  have hne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  rw [Real.dist_eq, grandiCesaroMean_eq]
  have hSabs : |∑ i ∈ range n, (-1 : ℝ) ^ i| ≤ 1 := grandi_partial_abs_le_one n
  set S := ∑ i ∈ range n, (-1 : ℝ) ^ i with hSdef
  have hkey : (n : ℝ)⁻¹ * (((n : ℝ) - S) / 2) - 1 / 2 = -(S / (2 * (n : ℝ))) := by
    field_simp
    ring
  rw [hkey, abs_neg, abs_div, abs_of_pos (show (0 : ℝ) < 2 * (n : ℝ) by positivity)]
  have hstep1 : |S| / (2 * (n : ℝ)) ≤ 1 / (2 * (n : ℝ)) := by gcongr
  have hstep2 : 1 / (2 * (n : ℝ)) < ε := by
    rw [div_lt_iff₀ (show (0 : ℝ) < 2 * (n : ℝ) by positivity)]
    have hNn : (N : ℝ) ≤ n := by exact_mod_cast le_of_max_le_left hn
    have hb2 : 1 / (2 * ε) < (n : ℝ) := lt_of_lt_of_le hN hNn
    rw [div_lt_iff₀ (show (0 : ℝ) < 2 * ε by positivity)] at hb2
    nlinarith
  linarith

/-- Grandi's partial sums do **not** converge: the even subsequence is `0`,
    the odd subsequence is `1`, so no single limit can exist. -/
theorem grandi_partial_not_tendsto :
    ¬ ∃ L, Tendsto (fun N => ∑ i ∈ range N, (-1 : ℝ) ^ i) atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have h2 : Tendsto (fun m : ℕ => 2 * m) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  have h2' : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 (fun b => ⟨b, fun a ha => by omega⟩)
  -- even subsequence ⟹ L = 0
  have heven : Tendsto (fun m : ℕ => ∑ i ∈ range (2 * m), (-1 : ℝ) ^ i)
      atTop (nhds L) := hL.comp h2
  have hL0 : L = 0 := by
    have hc : (fun m : ℕ => ∑ i ∈ range (2 * m), (-1 : ℝ) ^ i) = (fun _ => (0 : ℝ)) := by
      funext m; exact GeometricSeriesOQ01.grandi_even m
    rw [hc] at heven
    exact tendsto_nhds_unique heven tendsto_const_nhds
  -- odd subsequence ⟹ L = 1
  have hodd : Tendsto (fun m : ℕ => ∑ i ∈ range (2 * m + 1), (-1 : ℝ) ^ i)
      atTop (nhds L) := hL.comp h2'
  have hL1 : L = 1 := by
    have hc : (fun m : ℕ => ∑ i ∈ range (2 * m + 1), (-1 : ℝ) ^ i) = (fun _ => (1 : ℝ)) := by
      funext m; exact GeometricSeriesOQ01.grandi_odd m
    rw [hc] at hodd
    exact tendsto_nhds_unique hodd tendsto_const_nhds
  rw [hL0] at hL1
  norm_num at hL1

/-- **(C,1) summability strictly extends convergence.**
    Grandi's series is (C,1) summable to `1/2` but its partial sums diverge. -/
theorem cesaro_strictly_extends_convergence :
    CesaroSummable (fun N => ∑ i ∈ range N, (-1 : ℝ) ^ i) (1 / 2)
      ∧ ¬ ∃ L, Tendsto (fun N => ∑ i ∈ range N, (-1 : ℝ) ^ i) atTop (nhds L) :=
  ⟨grandiCesaroMean_tendsto, grandi_partial_not_tendsto⟩

-- ============================================================
-- Sanity checks
-- ============================================================

#check @cesaroSummable_of_tendsto
#check @cesaroSummable_of_hasSum
#check @grandiCesaroMean_tendsto
#check @cesaro_strictly_extends_convergence

end GeometricSeriesOQ01OQ02
