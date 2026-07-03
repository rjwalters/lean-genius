/-
Proof: Completing the second-order correction hierarchy for Erdős #1179.
Date: 2026-07-02
Research: erdos-1179-oq-01-oq-02 (researcher-16)

Erdős Problem #1179 (PROVED, Erdős–Hall 1976) establishes that the minimal
number `g_ε(N)` of random group elements needed for an ε-uniform subset-sum
representation function satisfies `g_ε(N) ∼ log₂ N`.  The open question studied
by the parent file `Proofs/Erdos1179OQ01.lean` concerns the precise second-order
correction `corr(N) := g_ε(N) − log₂ N`, and formalizes three candidate rates:

  * `CorrectionIsBounded`        —  |corr(N)| ≤ C            (the O(1) hypothesis, open)
  * `CorrectionIsLogLog`         —  c₁·log log N ≤ corr(N) ≤ c₂·log log N   (Θ(log log N))
  * `CorrectionIsSublinearInLog` —  |corr(N)| = o(log₂ N)    (the o(log) hypothesis, known)

The parent proves `CorrectionIsBounded ⟹ CorrectionIsSublinearInLog`
(`bounded_implies_sublinear`) and remarks that the remaining implication
`CorrectionIsLogLog ⟹ CorrectionIsSublinearInLog` is "straightforward but not
formalized."  This file formalizes that remaining implication, axiom-free,
thereby completing the correction hierarchy: BOTH the O(1) branch and the
Θ(log log N) branch collapse into the known o(log₂ N) rate.

A note on the hierarchy.  The literal chain "O(1) ⟹ Θ(log log N)" is *false*:
a bounded correction (|corr| ≤ C) cannot satisfy the growing lower bound
`c₁·log log N ≤ corr` for large N.  The two nontrivial hypotheses are instead
mutually exclusive *sharpenings*, each of which independently implies the weakest
(known) rate o(log₂ N).  What this file establishes is precisely the second of
those two independent implications.

Mathematical content.  The single analytic input is `log log N = o(log N)`:
for every ε' > 0, `log(log N) < ε'·log N` for all large N.  This follows from
Mathlib's `Real.isLittleO_log_id_atTop` (`log x = o(x)`) composed with
`log x → ∞`.  Given the two-sided bound `c₁·log log N ≤ corr(N) ≤ c₂·log log N`,
the correction is eventually non-negative (so `|corr(N)| = corr(N)`), bounded
above by `c₂·log log N`, which is in turn `< δ·log₂ N` for any δ > 0 and all
large N.  Hence `CorrectionIsSublinearInLog`.

Zero axioms, zero sorries.
-/
import Mathlib

open Real Filter Asymptotics
open scoped Topology

namespace Erdos1179OQ01OQ02

/-! ## Correction-term definitions (restated from the parent file)

These match `Proofs/Erdos1179OQ01.lean` verbatim so the file is self-contained. -/

/-- The second-order correction term `g_ε(N) − log₂ N`. -/
noncomputable def correctionTerm (gEps : ℝ → ℕ → ℕ) (ε : ℝ) (N : ℕ) : ℝ :=
  (gEps ε N : ℝ) - Real.logb 2 ↑N

/-- The correction is o(log₂ N) — the known (weakest) rate. -/
def CorrectionIsSublinearInLog (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ δ : ℝ, δ > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    |correctionTerm gEps ε N| < δ * Real.logb 2 ↑N

/-- The correction is Θ(log log N) — conjectured by analogy with Problem #543. -/
def CorrectionIsLogLog (gEps : ℝ → ℕ → ℕ) (ε : ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ →
    c₁ * Real.log (Real.log ↑N) ≤ correctionTerm gEps ε N ∧
    correctionTerm gEps ε N ≤ c₂ * Real.log (Real.log ↑N)

/-! ## The analytic core: `log log x = o(log x)` -/

/-- `log (log x) = o(log x)`: for every `ε' > 0`, eventually `log (log x) < ε'·log x`.
    Derived from `Real.isLittleO_log_id_atTop` (`log = o(id)`) composed with
    `log x → ∞`. -/
lemma eventually_loglog_lt {ε' : ℝ} (hε' : 0 < ε') :
    ∀ᶠ x : ℝ in atTop, Real.log (Real.log x) < ε' * Real.log x := by
  -- `log = o(id)`, then compose with `log → atTop` to get `log ∘ log = o(log)`.
  have h1 : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x) :=
    Real.isLittleO_log_id_atTop
  have h2 : (fun x : ℝ => Real.log (Real.log x)) =o[atTop] (fun x : ℝ => Real.log x) := by
    have := h1.comp_tendsto Real.tendsto_log_atTop
    simpa [Function.comp] using this
  -- Extract the `≤ (ε'/2)‖·‖` bound and combine with `log x > 0`.
  have hc : (0 : ℝ) < ε' / 2 := by positivity
  have hbound := (Asymptotics.isLittleO_iff.mp h2) hc
  have hpos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x :=
    Real.tendsto_log_atTop.eventually_gt_atTop 0
  filter_upwards [hbound, hpos] with x hx hxpos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hxpos] at hx
  calc Real.log (Real.log x)
      ≤ |Real.log (Real.log x)| := le_abs_self _
    _ ≤ (ε' / 2) * Real.log x := hx
    _ < ε' * Real.log x := by nlinarith [hxpos, hε']

/-! ## Main result: Θ(log log N) ⟹ o(log₂ N) -/

/-- **The remaining hierarchy implication.**  If the correction term is bounded
    both below and above by constant multiples of `log log N` (the Θ(log log N)
    hypothesis), then it is `o(log₂ N)` (the known sublinear rate).

    This is the implication the parent file (`Proofs/Erdos1179OQ01.lean`) leaves
    "straightforward but not formalized." -/
theorem loglog_implies_sublinear (gEps : ℝ → ℕ → ℕ) (ε : ℝ)
    (h : CorrectionIsLogLog gEps ε) : CorrectionIsSublinearInLog gEps ε := by
  obtain ⟨c₁, c₂, hc₁, hc₂, N₀, hN₀⟩ := h
  intro δ hδ
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- The scale factor turning `log log N < ε'·log N` into `< δ·log₂ N`.
  set ε' : ℝ := δ / (c₂ * Real.log 2) with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; exact div_pos hδ (mul_pos hc₂ hlog2)
  -- Combined eventual fact: `log log x < ε'·log x` and `1 ≤ log x` (⇒ `log log x ≥ 0`).
  have hev : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) < ε' * Real.log x ∧ 1 ≤ Real.log x := by
    have h1 := eventually_loglog_lt hε'
    have h2 : ∀ᶠ x : ℝ in atTop, 1 ≤ Real.log x :=
      Real.tendsto_log_atTop.eventually_ge_atTop 1
    filter_upwards [h1, h2] with x ha hb using ⟨ha, hb⟩
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.mp hev
  -- Threshold: large enough for the Θ-bounds (N₀) and for the analytic estimate (⌈X⌉₊).
  refine ⟨max N₀ ⌈X⌉₊, fun N hN => ?_⟩
  have hNN₀ : N ≥ N₀ := le_trans (le_max_left _ _) hN
  have hNceil : (⌈X⌉₊ : ℕ) ≤ N := le_trans (le_max_right _ _) hN
  have hXle : X ≤ (N : ℝ) := le_trans (Nat.le_ceil X) (by exact_mod_cast hNceil)
  obtain ⟨hll_lt, hlogge1⟩ := hX (N : ℝ) hXle
  obtain ⟨hlo, hhi⟩ := hN₀ N hNN₀
  -- `log log N ≥ 0`, hence the correction is non-negative and `|corr| = corr`.
  have hll_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hlogge1
  have hcorr_nonneg : 0 ≤ correctionTerm gEps ε N :=
    le_trans (mul_nonneg hc₁.le hll_nonneg) hlo
  rw [abs_of_nonneg hcorr_nonneg]
  -- `c₂·log log N < c₂·ε'·log N = δ·log₂ N`.
  have hchain : c₂ * Real.log (Real.log (N : ℝ)) < δ * Real.logb 2 (N : ℝ) := by
    have step : c₂ * Real.log (Real.log (N : ℝ)) < c₂ * (ε' * Real.log (N : ℝ)) :=
      mul_lt_mul_of_pos_left hll_lt hc₂
    have hc₂' : c₂ ≠ 0 := ne_of_gt hc₂
    have hlog2' : Real.log 2 ≠ 0 := ne_of_gt hlog2
    have eq : c₂ * (ε' * Real.log (N : ℝ)) = δ * Real.logb 2 (N : ℝ) := by
      simp only [hε'def, Real.logb]
      field_simp
    rw [eq] at step
    exact step
  linarith [hhi, hchain]

end Erdos1179OQ01OQ02
