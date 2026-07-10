import Mathlib

/-
# Hausdorff Dimension of Sets with Given Irrationality Measure (Jarník–Besicovitch)

## Open Question: liouville-theorem-oq-03

For a real exponent `τ`, the **τ-well-approximable set** is

  `W(τ) = { x : ℝ | ∃ C, for infinitely many q, ∃ p, |x - p/q| < C / q^τ }`,

which is exactly Mathlib's `{ x | LiouvilleWith τ x }`. The
**Jarník–Besicovitch theorem** (Jarník 1931, Besicovitch 1934) computes its
Hausdorff dimension:

  `dimH (W τ) = 2 / τ`   for every `τ ≥ 2`.

This is one of the foundational results of metric Diophantine approximation. Its
proof has two halves: an upper bound `≤ 2/τ` by an efficient covering of the
approximating intervals (a convergence/Borel–Cantelli argument), and a lower
bound `≥ 2/τ` by constructing a Cantor-like subset carrying a mass distribution
(the mass distribution principle / Frostman's lemma). Mathlib currently has the
`LiouvilleWith` predicate and the full `dimH` Hausdorff-dimension API, but **not**
the Jarník–Besicovitch dimension formula itself, which depends on Hausdorff
measure estimates for these specific sets that are not yet formalized.

## What this entry does

We formalize the statement and its structural surroundings, separating the
machine-checkable content from the one deep input:

* **Verified, 0-axiom** (genuine Mathlib derivations):
  - the well-approximable sets are *antitone* in the exponent
    (`wellApprox_antitone`), so `dimH (W τ)` is monotone — proved from
    `LiouvilleWith.mono`;
  - every Liouville number lies in *every* `W τ`
    (`liouville_subset_wellApprox`) — proved from `Liouville.liouvilleWith`;
  - hence `dimH {Liouville} ≤ dimH (W τ)` for all `τ` (`dimH_liouville_le_wellApprox`);
  - `W τ = univ` for `τ ≤ 1` (`wellApprox_le_one`);
  - elementary properties of the dimension exponent `τ ↦ 2/τ`.

* **The Jarník–Besicovitch formula** enters as the single `axiom`
  `dimH_wellApprox` (`dimH (W τ) = ENNReal.ofReal (2/τ)` for `τ ≥ 2`), the known
  deep theorem not yet in Mathlib.

* **Derived from the axiom** (real consequences, not restatements):
  - `dimH_wellApprox_two`: `dimH (W 2) = 1`;
  - the family shape: `dimH_wellApprox_pos` (`0 < dimH (W τ)` for `τ ≥ 2`),
    `dimH_wellApprox_lt_one` (`< 1` for `τ > 2`), `dimH_wellApprox_strictAntitone`
    (strict decrease for `2 ≤ σ < τ`), and `dimH_wellApprox_tendsto_zero`
    (`dimH (W τ) → 0` as `τ → ∞`);
  - `dimH_liouville_le`: `dimH {Liouville} ≤ 2/τ` for every `τ ≥ 2`;
  - **`dimH_liouville_eq_zero`**: the Liouville numbers have Hausdorff dimension
    `0` — squeezed from the bound as `τ → ∞`. This recovers the classical fact
    that the Liouville set, while uncountable, is dimensionally negligible.

## References
  * V. Jarník, "Über die simultanen diophantischen Approximationen" (Math. Z. 33, 1931).
  * A.S. Besicovitch, "Sets of fractional dimensions (IV)" (J. London Math. Soc. 9, 1934).
  * Y. Bugeaud, *Approximation by Algebraic Numbers* (Cambridge, 2004), Ch. 1.

**Axiom count**: 1 (the Jarník–Besicovitch dimension formula).  **Sorry count**: 0
-/

open Filter Set Topology
open scoped ENNReal

namespace LiouvilleTheoremOQ03

/-! ## Part I: The well-approximable sets `W τ` -/

/-- The τ-well-approximable set `W τ = { x | LiouvilleWith τ x }`: reals
approximable by rationals `p/q` to within `C/q^τ` for infinitely many `q`. -/
def wellApprox (τ : ℝ) : Set ℝ := {x : ℝ | LiouvilleWith τ x}

@[simp] theorem mem_wellApprox {τ x : ℝ} : x ∈ wellApprox τ ↔ LiouvilleWith τ x := Iff.rfl

/-- **Antitone in the exponent.** A larger approximation exponent is a stronger
demand, so `W` shrinks: `σ ≤ τ → W τ ⊆ W σ`. Proved from `LiouvilleWith.mono`. -/
theorem wellApprox_antitone {σ τ : ℝ} (h : σ ≤ τ) : wellApprox τ ⊆ wellApprox σ :=
  fun _ hx => hx.mono h

/-- For exponent `τ ≤ 1` every real is well-approximable: `W τ = univ`. -/
theorem wellApprox_le_one {τ : ℝ} (h : τ ≤ 1) : wellApprox τ = Set.univ := by
  ext x
  simp only [mem_wellApprox, Set.mem_univ, iff_true]
  exact (liouvilleWith_one x).mono h

/-- In particular `W 1 = univ`. -/
theorem wellApprox_one : wellApprox 1 = Set.univ := wellApprox_le_one le_rfl

/-- **Every Liouville number is well-approximable to every order.**
`{x | Liouville x} ⊆ W τ` for all `τ`. Proved from `Liouville.liouvilleWith`. -/
theorem liouville_subset_wellApprox (τ : ℝ) : {x : ℝ | Liouville x} ⊆ wellApprox τ :=
  fun _ hx => hx.liouvilleWith τ

/-! ## Part II: Monotonicity of the Hausdorff dimension -/

/-- The Hausdorff dimension of `W τ` is antitone in `τ`: `σ ≤ τ → dimH (W τ) ≤ dimH (W σ)`.
A purely structural consequence of `wellApprox_antitone` and `dimH_mono`. -/
theorem dimH_wellApprox_antitone {σ τ : ℝ} (h : σ ≤ τ) :
    dimH (wellApprox τ) ≤ dimH (wellApprox σ) :=
  dimH_mono (wellApprox_antitone h)

/-- The Liouville set has dimension below that of every `W τ`. -/
theorem dimH_liouville_le_wellApprox (τ : ℝ) :
    dimH {x : ℝ | Liouville x} ≤ dimH (wellApprox τ) :=
  dimH_mono (liouville_subset_wellApprox τ)

/-! ## Part III: The dimension exponent `τ ↦ 2/τ` -/

/-- The Jarník–Besicovitch dimension exponent `d(τ) = 2/τ`. -/
noncomputable def jbDim (τ : ℝ) : ℝ := 2 / τ

/-- `d(2) = 1`: the well-approximable set at the natural threshold `τ = 2` is
full-dimensional in ℝ. -/
@[simp] theorem jbDim_two : jbDim 2 = 1 := by unfold jbDim; norm_num

/-- `d(τ) > 0` for `τ > 0`. -/
theorem jbDim_pos {τ : ℝ} (h : 0 < τ) : 0 < jbDim τ := by
  unfold jbDim; positivity

/-- `d(τ) ≤ 1` for `τ ≥ 2`: above the threshold the dimension drops to a proper
fraction of the line. -/
theorem jbDim_le_one {τ : ℝ} (h : 2 ≤ τ) : jbDim τ ≤ 1 := by
  unfold jbDim
  rw [div_le_one (by linarith)]
  linarith

/-- `d(τ) < 1` strictly for `τ > 2`. -/
theorem jbDim_lt_one {τ : ℝ} (h : 2 < τ) : jbDim τ < 1 := by
  unfold jbDim
  rw [div_lt_one (by linarith)]
  linarith

/-- `d` is antitone on the positive reals: `0 < σ ≤ τ → d(τ) ≤ d(σ)`. -/
theorem jbDim_antitone {σ τ : ℝ} (hσ : 0 < σ) (h : σ ≤ τ) : jbDim τ ≤ jbDim σ := by
  unfold jbDim
  gcongr

/-! ## Part IV: The Jarník–Besicovitch theorem (axiomatized) -/

/-- **Jarník–Besicovitch theorem.** For every exponent `τ ≥ 2`, the
τ-well-approximable set has Hausdorff dimension `2/τ`:

  `dimH (W τ) = 2 / τ`.

This is the deep result of metric Diophantine approximation (Jarník 1931,
Besicovitch 1934). It is not yet available in Mathlib — the upper bound needs a
covering/Borel–Cantelli estimate and the lower bound a mass-distribution
(Frostman) construction on a Cantor subset — so it is recorded here as the single
axiom of this entry. The constant `C` in `LiouvilleWith` does not affect the
dimension (countable stability of `dimH` over `C ∈ ℕ`). -/
axiom dimH_wellApprox (τ : ℝ) (hτ : 2 ≤ τ) :
    dimH (wellApprox τ) = ENNReal.ofReal (2 / τ)

/-- At the threshold `τ = 2` the well-approximable set has full dimension `1`. -/
theorem dimH_wellApprox_two : dimH (wellApprox 2) = 1 := by
  rw [dimH_wellApprox 2 le_rfl, show (2 : ℝ) / 2 = 1 by norm_num, ENNReal.ofReal_one]

/-- The Hausdorff dimension of `W τ` matches the exponent `d(τ) = 2/τ`. -/
theorem dimH_wellApprox_eq_jbDim (τ : ℝ) (hτ : 2 ≤ τ) :
    dimH (wellApprox τ) = ENNReal.ofReal (jbDim τ) :=
  dimH_wellApprox τ hτ

/-! ### Full dimension on `[1, 2]` — closing the sub-threshold gap

The axiom `dimH_wellApprox` only speaks for `τ ≥ 2` (where `2/τ ≤ 1`). For
`τ ≤ 2` the Jarník–Besicovitch value `2/τ` would exceed `1`, but a set of reals
can have dimension at most `1`, so the true dimension saturates at the full value
`1`. The proofs below establish this *without* strengthening the axiom, by
squeezing `W 2 ⊆ W τ ⊆ ℝ`; together with the axiom they give the complete
dimension law `dimH (W τ) = min(1, 2/τ)`. -/

/-- **Full dimension below the threshold.** For every `τ ≤ 2` the well-approximable
set has full Hausdorff dimension `1`. This fills the range `1 < τ < 2` that the
axiom (stated for `τ ≥ 2`) does not reach: since `2/τ > 1` there, the dimension is
capped at the line's dimension `1`. Squeeze `1 = dimH (W 2) ≤ dimH (W τ) ≤ dimH ℝ
= 1`, using antitonicity below the threshold and `Real.dimH_univ`. -/
theorem dimH_wellApprox_eq_one_of_le_two {τ : ℝ} (hτ : τ ≤ 2) :
    dimH (wellApprox τ) = 1 := by
  refine le_antisymm ?_ ?_
  · calc dimH (wellApprox τ) ≤ dimH (Set.univ : Set ℝ) := dimH_mono (Set.subset_univ _)
      _ = 1 := Real.dimH_univ
  · calc (1 : ℝ≥0∞) = dimH (wellApprox 2) := dimH_wellApprox_two.symm
      _ ≤ dimH (wellApprox τ) := dimH_wellApprox_antitone hτ

/-- **The complete Jarník–Besicovitch dimension law.** For every `τ ≥ 1`,

  `dimH (W τ) = min(1, 2/τ)`,

i.e. the dimension is the full `1` for `1 ≤ τ ≤ 2` and drops to `2/τ` for `τ ≥ 2`,
matching continuously at the threshold `τ = 2`. This unifies the axiom
`dimH_wellApprox` (the `τ ≥ 2` branch) with `dimH_wellApprox_eq_one_of_le_two`
(the saturated `τ ≤ 2` branch) into a single formula valid across the whole
range. -/
theorem dimH_wellApprox_eq_min {τ : ℝ} (hτ : 1 ≤ τ) :
    dimH (wellApprox τ) = ENNReal.ofReal (min 1 (2 / τ)) := by
  have hτ0 : (0 : ℝ) < τ := by linarith
  rcases le_or_lt τ 2 with h2 | h2
  · rw [dimH_wellApprox_eq_one_of_le_two h2]
    have h1 : (1 : ℝ) ≤ 2 / τ := by rw [le_div_iff₀ hτ0]; linarith
    rw [min_eq_left h1, ENNReal.ofReal_one]
  · rw [dimH_wellApprox τ h2.le]
    have h1 : 2 / τ ≤ 1 := by rw [div_le_one hτ0]; linarith
    rw [min_eq_right h1]

/-! ### Quantitative shape of the dimension family `τ ↦ dimH (W τ)`

The Jarník–Besicovitch formula pins the dimension exactly, so the qualitative
picture of the whole family follows: each `W τ` (for `τ ≥ 2`) is a genuine
fractal of *positive* dimension, strictly below the full line once `τ > 2`, and
the dimension decays to `0` as the approximation demand `τ → ∞`. These are the
family-level analogues of the single-set Liouville statement in Part V. -/

/-- **Positive dimension.** For `τ ≥ 2` the well-approximable set is a genuine
fractal: `0 < dimH (W τ)`. It is never dimensionally negligible at any finite
exponent. -/
theorem dimH_wellApprox_pos {τ : ℝ} (hτ : 2 ≤ τ) : 0 < dimH (wellApprox τ) := by
  rw [dimH_wellApprox τ hτ, ENNReal.ofReal_pos]
  positivity

/-- **Sub-line dimension for `τ > 2`.** Above the threshold the dimension is a
proper fraction of the line: `dimH (W τ) < 1`. Together with
`dimH_wellApprox_pos` this places `W τ` strictly between a point set and the full
line for every `τ > 2`. -/
theorem dimH_wellApprox_lt_one {τ : ℝ} (hτ : 2 < τ) : dimH (wellApprox τ) < 1 := by
  rw [dimH_wellApprox τ hτ.le, ENNReal.ofReal_lt_one]
  rw [div_lt_one (by linarith)]
  linarith

/-- **Strict antitonicity of the dimension.** For `2 ≤ σ < τ` the dimension
strictly decreases: `dimH (W τ) < dimH (W σ)`. A larger exponent is a strictly
stronger demand, and the Jarník–Besicovitch value `2/τ` records that strictly.
(The set-level inclusion `wellApprox_antitone` only gives `≤`; the strict drop is
a genuine consequence of the dimension *formula*.) -/
theorem dimH_wellApprox_strictAntitone {σ τ : ℝ} (hσ : 2 ≤ σ) (h : σ < τ) :
    dimH (wellApprox τ) < dimH (wellApprox σ) := by
  have hσ0 : (0 : ℝ) < σ := by linarith
  rw [dimH_wellApprox τ (hσ.trans h.le), dimH_wellApprox σ hσ]
  rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
  exact div_lt_div_of_pos_left (by norm_num) hσ0 h

/-- **The dimension family decays to zero.** As the approximation exponent
`τ → ∞` the well-approximable sets vanish dimensionally:
`dimH (W τ) → 0`. This lifts the single-set fact
`dimH_liouville_eq_zero` to the whole nested family, and is what forces the
Liouville set — contained in every `W τ` — to have dimension `0`. -/
theorem dimH_wellApprox_tendsto_zero :
    Tendsto (fun τ : ℝ => dimH (wellApprox τ)) atTop (𝓝 0) := by
  -- The exact values `2/τ → 0` (as extended reals) drive the limit.
  have h0 : Tendsto (fun τ : ℝ => (2 : ℝ) / τ) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_inv_atTop_zero.const_mul (2 : ℝ)
  have h1 : Tendsto (fun τ : ℝ => ENNReal.ofReal (2 / τ)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    simpa using this
  -- The family agrees with those values eventually (for `τ ≥ 2`).
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with τ hτ
  exact (dimH_wellApprox τ hτ).symm

/-! ## Part V: Liouville numbers have Hausdorff dimension zero -/

/-- For every `τ ≥ 2`, the Liouville set is dimension-bounded by `2/τ`.
Combines the subset relation with the Jarník–Besicovitch formula. -/
theorem dimH_liouville_le {τ : ℝ} (hτ : 2 ≤ τ) :
    dimH {x : ℝ | Liouville x} ≤ ENNReal.ofReal (2 / τ) :=
  (dimH_liouville_le_wellApprox τ).trans (dimH_wellApprox τ hτ).le

/-- **The Liouville numbers have Hausdorff dimension zero.**

Although the Liouville set is uncountable (indeed comeagre), it is dimensionally
negligible: it sits inside `W τ` for every `τ`, so its dimension is at most
`2/τ → 0`. This is the classical corollary of Jarník–Besicovitch, here derived by
an explicit squeeze of the bound `dimH ≤ 2/n` along `n → ∞`. -/
theorem dimH_liouville_eq_zero : dimH {x : ℝ | Liouville x} = 0 := by
  -- Bound along natural exponents `n ≥ 2`.
  have hbound : ∀ n : ℕ, 2 ≤ n →
      dimH {x : ℝ | Liouville x} ≤ ENNReal.ofReal (2 / (n : ℝ)) := by
    intro n hn
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact dimH_liouville_le this
  -- The bounds tend to `0`.
  have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (2 / (n : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat 2
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h0
    simpa using this
  -- Squeeze: a constant below sequences converging to `0` is `≤ 0`.
  have hle : dimH {x : ℝ | Liouville x} ≤ 0 :=
    ge_of_tendsto htend (eventually_atTop.2 ⟨2, fun n hn => hbound n hn⟩)
  exact le_antisymm hle (zero_le _)

/-! ## Part VI: Summary -/

/-- **Summary.** The Jarník–Besicovitch picture for `liouville-theorem-oq-03`:
the well-approximable sets are antitone with antitone dimension, the dimension at
the threshold is `1`, and the Liouville numbers — contained in every `W τ` — have
dimension `0`. -/
theorem jarnik_besicovitch_summary :
    (∀ σ τ : ℝ, σ ≤ τ → wellApprox τ ⊆ wellApprox σ) ∧
    (∀ τ : ℝ, {x : ℝ | Liouville x} ⊆ wellApprox τ) ∧
    dimH (wellApprox 2) = 1 ∧
    dimH {x : ℝ | Liouville x} = 0 :=
  ⟨fun _ _ h => wellApprox_antitone h,
   liouville_subset_wellApprox,
   dimH_wellApprox_two,
   dimH_liouville_eq_zero⟩

end LiouvilleTheoremOQ03
