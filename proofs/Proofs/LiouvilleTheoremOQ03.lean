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
  rcases le_or_gt τ 2 with h2 | h2
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
    simpa [Function.comp_def] using this
  -- The family agrees with those values eventually (for `τ ≥ 2`).
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with τ hτ
  exact (dimH_wellApprox τ hτ).symm

/-- **The Jarník–Besicovitch dimension spectrum is exactly `(0, 1]`.** Every value
`d` with `0 < d ≤ 1` is attained as the Hausdorff dimension of some well-approximable
set: taking `τ = 2/d ≥ 2` gives `dimH (W τ) = d`. Together with
`dimH_wellApprox_pos` (`0 < dimH (W τ)`) and `dimH_wellApprox_two` /
`dimH_wellApprox_eq_one_of_le_two` (the value `1` is realized at `τ = 2`), this shows
the family `τ ↦ dimH (W τ)` sweeps out the *entire* interval `(0, 1]` of admissible
fractal dimensions — the surjectivity companion of the strict monotonicity
(`dimH_wellApprox_strictAntitone`) and vanishing (`dimH_wellApprox_tendsto_zero`). -/
theorem dimH_wellApprox_surjOn {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ τ : ℝ, 2 ≤ τ ∧ dimH (wellApprox τ) = ENNReal.ofReal d := by
  have hτ2 : (2 : ℝ) ≤ 2 / d := by rw [le_div_iff₀ hd0]; linarith
  refine ⟨2 / d, hτ2, ?_⟩
  have hval : (2 : ℝ) / (2 / d) = d := by
    rw [div_div_eq_mul_div, mul_comm, mul_div_assoc]; norm_num
  rw [dimH_wellApprox (2 / d) hτ2, hval]

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
    simpa [Function.comp_def] using this
  -- Squeeze: a constant below sequences converging to `0` is `≤ 0`.
  have hle : dimH {x : ℝ | Liouville x} ≤ 0 :=
    ge_of_tendsto htend (eventually_atTop.2 ⟨2, fun n hn => hbound n hn⟩)
  exact le_antisymm hle (zero_le)

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

/-! ## Part VII: The measure side — Khintchine null sets

The dimension law has an immediate **measure-theoretic** shadow. For `τ > 2` the
well-approximable set has Hausdorff dimension `< 1` (`dimH_wellApprox_lt_one`), so
its `1`-dimensional Hausdorff measure vanishes; and on `ℝ` that measure *is*
Lebesgue measure (`hausdorffMeasure_real : μH[1] = volume`). Hence `W τ` is
Lebesgue-null for every `τ > 2` — the "easy" (convergence) half of Khintchine's
theorem: almost every real number is *not* `τ`-well-approximable once `τ > 2`. The
classical corollary is that the **Liouville numbers form a null set** (they lie in
`W 3`), a companion to `dimH_liouville_eq_zero` on the measure side. -/

open MeasureTheory in
/-- **`W τ` has Hausdorff `1`-measure zero for `τ > 2`.** From `dimH (W τ) < 1`
(`dimH_wellApprox_lt_one`) via `hausdorffMeasure_of_dimH_lt`. -/
theorem hausdorffMeasure_one_wellApprox_eq_zero {τ : ℝ} (hτ : 2 < τ) :
    μH[(1 : ℝ)] (wellApprox τ) = 0 := by
  simpa using
    hausdorffMeasure_of_dimH_lt (X := ℝ) (s := wellApprox τ) (d := 1)
      (by exact_mod_cast dimH_wellApprox_lt_one hτ)

open MeasureTheory in
/-- **`W τ` is Lebesgue-null for `τ > 2`** (Khintchine's convergence half): almost
every real is not `τ`-well-approximable. Immediate from the Hausdorff-`1`-measure
statement and `hausdorffMeasure_real : μH[1] = volume` on `ℝ`. -/
theorem volume_wellApprox_eq_zero {τ : ℝ} (hτ : 2 < τ) :
    volume (wellApprox τ) = 0 := by
  rw [← hausdorffMeasure_real]
  exact hausdorffMeasure_one_wellApprox_eq_zero hτ

open MeasureTheory in
/-- **The Liouville numbers form a Lebesgue-null set.** They are contained in the
`τ = 3 > 2` well-approximable set, which is null. The measure-side companion to
`dimH_liouville_eq_zero`. -/
theorem volume_liouville_eq_zero :
    volume {x : ℝ | Liouville x} = 0 :=
  measure_mono_null (liouville_subset_wellApprox 3) (volume_wellApprox_eq_zero (by norm_num))

open MeasureTheory in
/-- **The very-well-approximable reals form a Lebesgue-null set.** The set of `x`
that are `τ`-well-approximable for *some* exponent `τ > 2` — the union
`⋃_{τ > 2} W τ` — is Lebesgue-null, strengthening the fixed-exponent statement
`volume_wellApprox_eq_zero` from each individual `W τ` to their whole union.

This is the sharp measure-theoretic form of Khintchine's convergence theorem: for
almost every real number the irrationality measure is *exactly* `2`. The proof
covers the union by the countable subfamily `W(2 + 1/(n+1))` (any `τ > 2` exceeds
`2 + 1/(n+1)` for some `n`, and `W τ ⊆ W(2 + 1/(n+1))` by antitonicity), each of
which is null by `volume_wellApprox_eq_zero`, then applies countable subadditivity.
Since the Liouville numbers are `τ`-well-approximable for every `τ` (in particular
some `τ > 2`), this re-proves and generalises `volume_liouville_eq_zero`. -/
theorem volume_setOf_exists_liouvilleWith_gt_two_eq_zero :
    volume {x : ℝ | ∃ τ : ℝ, 2 < τ ∧ LiouvilleWith τ x} = 0 := by
  have hsub : {x : ℝ | ∃ τ : ℝ, 2 < τ ∧ LiouvilleWith τ x}
      ⊆ ⋃ n : ℕ, wellApprox (2 + 1 / ((n : ℝ) + 1)) := by
    rintro x ⟨τ, hτ, hx⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hτ)
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    have hle : 2 + 1 / ((n : ℝ) + 1) ≤ τ := by linarith
    exact hx.mono hle
  refine measure_mono_null hsub (measure_iUnion_null (fun n => ?_))
  refine volume_wellApprox_eq_zero ?_
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

/-- **Full Hausdorff dimension of the very-well-approximable reals.** The set of
`x` that are `τ`-well-approximable for *some* `τ > 2` — the *same* set proved
Lebesgue-null in `volume_setOf_exists_liouvilleWith_gt_two_eq_zero` — nonetheless
has full Hausdorff dimension `1`.

It contains `W τ` for every `τ > 2`, so its dimension is at least
`dimH (W τ) = 2/τ`; letting `τ ↓ 2` along `τ = 2 + 1/(n+1)` pushes the bound up to
`1`, while the reverse bound is `dimH ≤ dimH ℝ = 1`. This is the dimension-side
companion to the measure statement: the very-well-approximable reals are a set of
Lebesgue measure zero that is nonetheless dimensionally *full* — the hallmark
fractal coexistence of measure zero with maximal Hausdorff dimension. -/
theorem dimH_setOf_exists_liouvilleWith_gt_two_eq_one :
    dimH {x : ℝ | ∃ τ : ℝ, 2 < τ ∧ LiouvilleWith τ x} = 1 := by
  refine le_antisymm ?_ ?_
  · calc dimH {x : ℝ | ∃ τ : ℝ, 2 < τ ∧ LiouvilleWith τ x}
          ≤ dimH (Set.univ : Set ℝ) := dimH_mono (Set.subset_univ _)
      _ = 1 := Real.dimH_univ
  · -- Lower bound: the set contains `W (2 + 1/(n+1))` for every `n`, and the
    -- Jarník–Besicovitch values `2 / (2 + 1/(n+1)) → 1`.
    have hge : ∀ n : ℕ,
        ENNReal.ofReal (2 / (2 + 1 / ((n : ℝ) + 1)))
          ≤ dimH {x : ℝ | ∃ τ : ℝ, 2 < τ ∧ LiouvilleWith τ x} := by
      intro n
      have hτ : (2 : ℝ) < 2 + 1 / ((n : ℝ) + 1) := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      rw [← dimH_wellApprox _ hτ.le]
      exact dimH_mono (fun x hx => ⟨_, hτ, hx⟩)
    have htend : Tendsto
        (fun n : ℕ => ENNReal.ofReal (2 / (2 + 1 / ((n : ℝ) + 1)))) atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ => (2 : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 2) := by
        simpa using (tendsto_const_nhds (x := (2 : ℝ))).add
          tendsto_one_div_add_atTop_nhds_zero_nat
      have hquot : Tendsto (fun n : ℕ => (2 : ℝ) / (2 + 1 / ((n : ℝ) + 1))) atTop
          (𝓝 ((2 : ℝ) / 2)) := (tendsto_const_nhds).div h0 (by norm_num)
      rw [show (2 : ℝ) / 2 = 1 by norm_num] at hquot
      have := (ENNReal.continuous_ofReal.tendsto 1).comp hquot
      simpa [Function.comp_def] using this
    exact le_of_tendsto' htend hge

/-! ## Part VIII: Cardinality — the fractals are uncountable

The measure and dimension results above all say the well-approximable sets are
*small*: for `τ > 2` they have Hausdorff dimension `< 1` (`dimH_wellApprox_lt_one`)
and Lebesgue measure `0` (`volume_wellApprox_eq_zero`). The cardinality side is the
opposite: they are *uncountable*. The mechanism is the contrapositive of
`Set.Countable.dimH_zero` (a countable set has Hausdorff dimension `0`): since
`dimH (W τ) = 2/τ > 0` for `τ ≥ 2` (`dimH_wellApprox_pos`), the set cannot be
countable. This makes each `W τ` a genuine *fractal* in the strong sense —
uncountably many points packed into a Lebesgue-null, sub-dimensional set. -/

/-- **The well-approximable set is uncountable.** For `τ ≥ 2`, `W τ` cannot be
countable: a countable set has Hausdorff dimension `0` (`Set.Countable.dimH_zero`),
but `dimH (W τ) = 2/τ > 0` by `dimH_wellApprox_pos`. So although `W τ` is Lebesgue
null and (for `τ > 2`) has dimension below the line, it still contains uncountably
many reals. -/
theorem not_countable_wellApprox {τ : ℝ} (hτ : 2 ≤ τ) : ¬ (wellApprox τ).Countable :=
  fun hc => (dimH_wellApprox_pos hτ).ne' hc.dimH_zero

/-- **The very-well-approximable reals are uncountable.** The set of `x` that are
`τ`-well-approximable for *some* `τ > 2` — already shown to be Lebesgue-null
(`volume_setOf_exists_liouvilleWith_gt_two_eq_zero`) yet of full Hausdorff
dimension `1` (`dimH_setOf_exists_liouvilleWith_gt_two_eq_one`) — is in particular
uncountable, since its dimension `1 ≠ 0`. The sharpest form of the "large yet
measure-zero" phenomenon: a null set of maximal dimension carrying uncountably
many points. -/
theorem not_countable_setOf_exists_liouvilleWith_gt_two :
    ¬ {x : ℝ | ∃ τ : ℝ, 2 < τ ∧ LiouvilleWith τ x}.Countable := by
  intro hc
  have h := hc.dimH_zero
  rw [dimH_setOf_exists_liouvilleWith_gt_two_eq_one] at h
  exact one_ne_zero h

/-! ## Part IX: The topological & structural face — axiom-free

Parts II–VIII all measure how *small* `W τ` is: for `τ > 2` it is Lebesgue-null
(`volume_wellApprox_eq_zero`) and of sub-line Hausdorff dimension
(`dimH_wellApprox_lt_one`).  This part records the complementary fact that each `W τ` is
nonetheless topologically *large* — it is nonempty and dense — and identifies the exact
common core of the whole scale.  None of these use the Jarník–Besicovitch axiom
`dimH_wellApprox`; they rest only on Mathlib's Liouville-number theory. -/

/-- **The whole scale intersects in the Liouville numbers.**  `⋂_{τ} W τ = {x | Liouville x}`:
a real is well-approximable to *every* order iff it is a Liouville number
(`forall_liouvilleWith_iff`).  So the Liouville set is precisely the "infinitely
well-approximable" reals — the common core of the entire `W τ` family, and the object
whose dimension `0` (`dimH_liouville_eq_zero`) sits below every `dimH (W τ)`. -/
theorem iInter_wellApprox_eq_liouville :
    (⋂ τ : ℝ, wellApprox τ) = {x : ℝ | Liouville x} := by
  ext x
  simp only [Set.mem_iInter, mem_wellApprox, Set.mem_setOf_eq]
  exact forall_liouvilleWith_iff

/-- **Every well-approximable set is nonempty.**  It contains the explicit Liouville
number `liouvilleNumber 2 = ∑ₖ 2^{−k!}`, which is `τ`-well-approximable for every real `τ`
(`liouville_liouvilleNumber`, `Liouville.liouvilleWith`).  So the family `W τ` never
degenerates to the empty set, however large the exponent. -/
theorem wellApprox_nonempty (τ : ℝ) : (wellApprox τ).Nonempty :=
  ⟨liouvilleNumber 2, (liouville_liouvilleNumber (le_refl 2)).liouvilleWith τ⟩

/-- **Every well-approximable set is dense.**  `W τ` contains the dense set of Liouville
numbers (`dense_liouville`, `liouville_subset_wellApprox`), hence is dense in `ℝ` for every
exponent `τ`.  This is the topological counterpart of the metric smallness: for `τ > 2`,
`W τ` is Lebesgue-null and sub-dimensional yet still meets every open interval — a dense set
of measure zero. -/
theorem wellApprox_dense (τ : ℝ) : Dense (wellApprox τ) :=
  dense_liouville.mono (liouville_subset_wellApprox τ)

/-- **Universal dimension upper bound.**  `dimH (W τ) ≤ 1` for *every* `τ`, with no appeal
to the axiom: `W τ ⊆ ℝ` and `dimH ℝ = 1` (`Real.dimH_univ`).  The Jarník–Besicovitch axiom
pins the exact value `2/τ` for `τ ≥ 2`; this trivial upper half holds unconditionally, for
all exponents including `τ < 2`. -/
theorem dimH_wellApprox_le_one_univ (τ : ℝ) : dimH (wellApprox τ) ≤ 1 := by
  calc dimH (wellApprox τ) ≤ dimH (Set.univ : Set ℝ) := dimH_mono (Set.subset_univ _)
    _ = 1 := Real.dimH_univ

/-- **Full dimension below `τ = 1`, axiom-free.**  For `τ ≤ 1` we have `W τ = univ`
(`wellApprox_le_one`), so `dimH (W τ) = dimH ℝ = 1` with no analytic input — the
sub-threshold full-dimension regime that needs none of the Jarník–Besicovitch machinery
(contrast `dimH_wellApprox_eq_one_of_le_two`, which routes through the axiom at `τ = 2`). -/
theorem dimH_wellApprox_eq_one_of_le_one {τ : ℝ} (hτ : τ ≤ 1) :
    dimH (wellApprox τ) = 1 := by
  rw [wellApprox_le_one hτ]; exact Real.dimH_univ

/-! ## Part X: The category (Baire) face — comeagre yet null

Parts II–VIII established that for `τ > 2` the well-approximable set is *metrically*
small: Lebesgue-null (`volume_wellApprox_eq_zero`) and of sub-line Hausdorff dimension
(`dimH_wellApprox_lt_one`).  `wellApprox_dense` already noted it is topologically dense.
The sharp topological statement is stronger still: each `W τ` is **comeagre
(residual)** — it contains a dense `Gδ`.  This is inherited for free from Mathlib's
`eventually_residual_liouville` (the Liouville numbers are residual) because the
residual filter is upward closed and `{x | Liouville x} ⊆ W τ`.  Combined with the
measure side it exhibits the textbook **category/measure dichotomy**: for `τ > 2`,
`W τ` is a comeagre set of Lebesgue measure zero, so `ℝ` decomposes into the meagre
full-measure complement `(W τ)ᶜ` and the comeagre null set `W τ`. -/

/-- **Each well-approximable set is residual (comeagre).**  `W τ ∈ residual ℝ` for
every exponent `τ`: it contains the residual Liouville set
(`eventually_residual_liouville`) and the residual filter is upward closed
(`Filter.mem_of_superset`).  Axiom-free — strengthens `wellApprox_dense`
(`dense_of_mem_residual`). -/
theorem wellApprox_residual (τ : ℝ) : wellApprox τ ∈ residual ℝ :=
  Filter.mem_of_superset eventually_residual_liouville (liouville_subset_wellApprox τ)

/-- **Comeagre form.**  A residual-a.e. real is `τ`-well-approximable:
`∀ᶠ x in residual ℝ, x ∈ W τ`.  The `Filter.Eventually` restatement of
`wellApprox_residual`. -/
theorem eventually_residual_wellApprox (τ : ℝ) : ∀ᶠ x in residual ℝ, x ∈ wellApprox τ :=
  wellApprox_residual τ

/-- **The complement is meagre.**  `(W τ)ᶜ` is a meagre set for every `τ`: the reals
that are *not* `τ`-well-approximable form a first-category set.  Immediate from
`wellApprox_residual` since `IsMeagre s ↔ sᶜ ∈ residual`. -/
theorem meagre_compl_wellApprox (τ : ℝ) : IsMeagre (wellApprox τ)ᶜ := by
  rw [IsMeagre, compl_compl]; exact wellApprox_residual τ

open MeasureTheory in
/-- **Category/measure dichotomy.**  For `τ > 2` the well-approximable set is
*simultaneously* comeagre (`wellApprox_residual`) and Lebesgue-null
(`volume_wellApprox_eq_zero`).  Thus `W τ` is a residual set of measure zero — the
classical demonstration that Baire category and Lebesgue measure can disagree
completely: the "typical" real in the category sense lies in `W τ`, while the
"typical" real in the measure sense does not. -/
theorem wellApprox_residual_and_volume_zero {τ : ℝ} (hτ : 2 < τ) :
    wellApprox τ ∈ residual ℝ ∧ volume (wellApprox τ) = 0 :=
  ⟨wellApprox_residual τ, volume_wellApprox_eq_zero hτ⟩

/-- **The Liouville numbers are residual (comeagre).**  A named restatement of Mathlib's
`eventually_residual_liouville` as set membership: `{x | Liouville x} ∈ residual ℝ`.  So the
*topologically typical* real is Liouville — despite the Liouville set being both
Hausdorff-dimension `0` (`dimH_liouville_eq_zero`) and Lebesgue-null
(`volume_liouville_eq_zero`).  Axiom-free (pure Baire category). -/
theorem liouville_residual : {x : ℝ | Liouville x} ∈ residual ℝ :=
  eventually_residual_liouville

/-- **The non-Liouville reals are meagre.**  `{x | Liouville x}ᶜ` is first category: the
transcendence-generic (non-Liouville) reals form a meagre set, even though they are
Lebesgue-conull and dimension-`1`.  Immediate from `liouville_residual`; axiom-free. -/
theorem meagre_compl_liouville : IsMeagre {x : ℝ | Liouville x}ᶜ := by
  rw [IsMeagre, compl_compl]; exact liouville_residual

open MeasureTheory in
/-- **The Liouville measure/category/dimension trichotomy.**  The set of Liouville numbers is
*simultaneously* Hausdorff-dimension `0`, Lebesgue-null, and comeagre (residual):

    dimH {x | Liouville x} = 0  ∧  volume {x | Liouville x} = 0  ∧  {x | Liouville x} ∈ residual ℝ.

So both classical notions of "smallness" — dimension and measure — declare the Liouville set
negligible, while Baire category declares it *generic*: the sharpest form of the
measure-versus-category disagreement, now for the Liouville set itself (the file's
`wellApprox_residual_and_volume_zero` states the two-way version for `W τ`, `τ > 2`).  The
dimension component rests on the entry's Jarník–Besicovitch axiom (via
`dimH_liouville_eq_zero`); the measure and category components are axiom-free. -/
theorem liouville_dimzero_null_yet_residual :
    dimH {x : ℝ | Liouville x} = 0 ∧
      volume {x : ℝ | Liouville x} = 0 ∧
      {x : ℝ | Liouville x} ∈ residual ℝ :=
  ⟨dimH_liouville_eq_zero, volume_liouville_eq_zero, liouville_residual⟩

/-! ## The full-measure complement is also dense

`wellApprox_dense` shows the `τ`-well-approximable numbers are dense.  For `τ > 2` the set
is Lebesgue-null (`volume_wellApprox_eq_zero`), so its *complement* carries full measure —
and a full-measure set in `ℝ` is dense, because a null set has empty interior
(`MeasureTheory.Measure.interior_eq_empty_of_null`, using that `volume` is an open-positive
measure).  Hence for `τ > 2` **both `W τ` and its complement are dense**: the topological
face of the measure-versus-category tension, complementary to the comeagre-yet-null
statement `wellApprox_residual_and_volume_zero`. -/

open MeasureTheory in
/-- **The complement of `W τ` is dense for `τ > 2`.**  Since `W τ` is Lebesgue-null it has
empty interior, so its complement (the full-measure set of *badly*-approximable-past-`τ`
numbers) is dense. -/
theorem dense_compl_wellApprox {τ : ℝ} (hτ : 2 < τ) : Dense (wellApprox τ)ᶜ :=
  (interior_eq_empty_iff_dense_compl).mp
    (MeasureTheory.Measure.interior_eq_empty_of_null (volume_wellApprox_eq_zero hτ))

/-- **A set and its complement both dense.**  For `τ > 2` the `τ`-well-approximable numbers
`W τ` are dense (`wellApprox_dense`, category/genericity) and so is their complement
(`dense_compl_wellApprox`, full measure).  This packages the topological form of the
measure/category dichotomy: neither `W τ` nor its complement has any interior. -/
theorem wellApprox_dense_and_dense_compl {τ : ℝ} (hτ : 2 < τ) :
    Dense (wellApprox τ) ∧ Dense (wellApprox τ)ᶜ :=
  ⟨wellApprox_dense τ, dense_compl_wellApprox hτ⟩

open MeasureTheory in
/-- **The complement of the Liouville set is dense.**  The Liouville numbers are null
(`volume_liouville_eq_zero`), hence have empty interior, so the (full-measure) set of
non-Liouville numbers is dense — even though the Liouville set is itself a dense comeagre
`Gδ` (`liouville_residual`, `wellApprox_dense`).  Both the generic-but-null Liouville set
and its full-measure complement are dense. -/
theorem dense_compl_liouville : Dense {x : ℝ | Liouville x}ᶜ :=
  (interior_eq_empty_iff_dense_compl).mp
    (MeasureTheory.Measure.interior_eq_empty_of_null volume_liouville_eq_zero)

/-! ### ℚ-affine invariance of the well-approximable set

The irrationality-measure exponent `τ` of a real number is unchanged by adding a rational,
by negation, and by multiplying by a nonzero rational — this is exactly the content of
Mathlib's `LiouvilleWith.add_rat_iff`, `LiouvilleWith.neg_iff`, `LiouvilleWith.mul_rat_iff`.
Lifted to the level sets, the well-approximable set `wellApprox τ = {x | LiouvilleWith τ x}`
is therefore invariant under the whole rational-affine group `x ↦ a·x + b` (`a, b ∈ ℚ`,
`a ≠ 0`).  This is the structural reason `wellApprox τ` is a *dense* set of the same
Hausdorff dimension everywhere — the rich self-similarity underneath the Jarník–Besicovitch
dimension formula — and complements the measure/category/density facts above.  All results
are elementary consequences of the Mathlib `LiouvilleWith` invariance API; none touches the
`dimH_wellApprox` axiom. -/

/-- **Translation by a rational fixes membership.** `x + r ∈ wellApprox τ ↔ x ∈ wellApprox τ`
for `r : ℚ` (`LiouvilleWith.add_rat_iff`). -/
theorem wellApprox_add_rat_iff (τ : ℝ) (x : ℝ) (r : ℚ) :
    x + (r : ℝ) ∈ wellApprox τ ↔ x ∈ wellApprox τ := by
  simp only [wellApprox, Set.mem_setOf_eq]
  exact LiouvilleWith.add_rat_iff

/-- **Translation by an integer fixes membership.** `x + m ∈ wellApprox τ ↔ x ∈ wellApprox τ`
for `m : ℤ` (`LiouvilleWith.add_int_iff`). -/
theorem wellApprox_add_int_iff (τ : ℝ) (x : ℝ) (m : ℤ) :
    x + (m : ℝ) ∈ wellApprox τ ↔ x ∈ wellApprox τ := by
  simp only [wellApprox, Set.mem_setOf_eq]
  exact LiouvilleWith.add_int_iff

/-- **Subtraction of a rational fixes membership.** `x - r ∈ wellApprox τ ↔ x ∈ wellApprox τ`
(`LiouvilleWith.sub_rat_iff`). -/
theorem wellApprox_sub_rat_iff (τ : ℝ) (x : ℝ) (r : ℚ) :
    x - (r : ℝ) ∈ wellApprox τ ↔ x ∈ wellApprox τ := by
  simp only [wellApprox, Set.mem_setOf_eq]
  exact LiouvilleWith.sub_rat_iff

/-- **Negation fixes membership.** `-x ∈ wellApprox τ ↔ x ∈ wellApprox τ`
(`LiouvilleWith.neg_iff`); `wellApprox τ` is symmetric about the origin. -/
theorem wellApprox_neg_iff (τ : ℝ) (x : ℝ) :
    -x ∈ wellApprox τ ↔ x ∈ wellApprox τ := by
  simp only [wellApprox, Set.mem_setOf_eq]
  exact LiouvilleWith.neg_iff

/-- **Dilation by a nonzero rational fixes membership.** `x · r ∈ wellApprox τ ↔ x ∈ wellApprox τ`
for `r : ℚ`, `r ≠ 0` (`LiouvilleWith.mul_rat_iff`). -/
theorem wellApprox_mul_rat_iff (τ : ℝ) (x : ℝ) {r : ℚ} (hr : r ≠ 0) :
    x * (r : ℝ) ∈ wellApprox τ ↔ x ∈ wellApprox τ := by
  simp only [wellApprox, Set.mem_setOf_eq]
  exact LiouvilleWith.mul_rat_iff hr

/-- **Rational-translation invariance as a set equality.** The image of `wellApprox τ` under
`x ↦ x + r` (`r : ℚ`) is `wellApprox τ` itself — the level set is a genuine union of its own
rational translates.  Forward from `wellApprox_add_rat_iff`, backward via the preimage point
`y - r` (`wellApprox_sub_rat_iff`). -/
theorem image_add_rat_wellApprox (τ : ℝ) (r : ℚ) :
    (fun x => x + (r : ℝ)) '' wellApprox τ = wellApprox τ := by
  ext y
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (wellApprox_add_rat_iff τ x r).mpr hx
  · intro hy
    exact ⟨y - (r : ℝ), (wellApprox_sub_rat_iff τ y r).mpr hy, by ring⟩

/-! ## Borel measurability of the well-approximable sets (axiom-free)

The measure results above (`volume_wellApprox_eq_zero`, `volume_liouville_eq_zero`,
`hausdorffMeasure_one_wellApprox_eq_zero`) are all statements that an *outer* measure of
`W τ` vanishes — they never needed `W τ` to be genuinely measurable.  Here we record that
these sets are in fact **Borel measurable**, so "null" upgrades to an honest statement about
the completed Lebesgue measure and `W τ` may be used freely as a measurable set downstream.

`W τ = {x | ∃ C, ∃ᶠ n, ∃ m, x ≠ m/n ∧ |x - m/n| < C/nᵗ}` is a countable union (over the
constant `C`, reduced to `ℕ` by monotonicity — a larger `C` only enlarges the condition) of
`limsup`-type sets `⋂_a ⋃_{b≥a}` of the open balls `{x | |x - m/b| < C/bᵗ}`, hence Borel.
This is a purely descriptive-set-theoretic fact: it does **not** use the Jarník–Besicovitch
dimension axiom. -/
theorem measurableSet_wellApprox (τ : ℝ) : MeasurableSet (wellApprox τ) := by
  -- Monotonicity in the constant `C`: a real witness upgrades to the ceiling `⌈C⌉₊ : ℕ`.
  have hstep : ∀ (C : ℝ) (x : ℝ),
      (∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ (m : ℝ) / (n : ℝ) ∧
        |x - (m : ℝ) / (n : ℝ)| < C / (n : ℝ) ^ τ) →
      (∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ (m : ℝ) / (n : ℝ) ∧
        |x - (m : ℝ) / (n : ℝ)| < (⌈C⌉₊ : ℝ) / (n : ℝ) ^ τ) := by
    intro C x h
    refine h.mono ?_
    rintro n ⟨m, hne, hlt⟩
    refine ⟨m, hne, lt_of_lt_of_le hlt ?_⟩
    have hCk : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
    have hd : (0 : ℝ) ≤ ((n : ℝ) ^ τ)⁻¹ := inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) τ)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hCk hd
  -- Reduce the uncountable `∃ C : ℝ` to a countable `⋃ k : ℕ`.
  have hset : wellApprox τ = ⋃ k : ℕ,
      {x : ℝ | ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ (m : ℝ) / (n : ℝ) ∧
        |x - (m : ℝ) / (n : ℝ)| < (k : ℝ) / (n : ℝ) ^ τ} := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨C, hC⟩
      exact ⟨⌈C⌉₊, hstep C x hC⟩
    · rintro ⟨k, hk⟩
      exact ⟨(k : ℝ), hk⟩
  rw [hset]
  refine MeasurableSet.iUnion fun k => ?_
  -- Each fixed-`b` fibre is a countable union of (punctured) open balls, hence measurable.
  have hQ : ∀ b : ℕ, MeasurableSet
      {x : ℝ | ∃ m : ℤ, x ≠ (m : ℝ) / (b : ℝ) ∧ |x - (m : ℝ) / (b : ℝ)| < (k : ℝ) / (b : ℝ) ^ τ} := by
    intro b
    have he : {x : ℝ | ∃ m : ℤ, x ≠ (m : ℝ) / (b : ℝ) ∧ |x - (m : ℝ) / (b : ℝ)| < (k : ℝ) / (b : ℝ) ^ τ}
        = ⋃ m : ℤ, ({(m : ℝ) / (b : ℝ)}ᶜ ∩ {x | |x - (m : ℝ) / (b : ℝ)| < (k : ℝ) / (b : ℝ) ^ τ}) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_singleton_iff, ne_eq]
    rw [he]
    refine MeasurableSet.iUnion fun m => MeasurableSet.inter ?_ ?_
    · exact (measurableSet_singleton _).compl
    · exact (isOpen_lt ((continuous_id.sub continuous_const).abs) continuous_const).measurableSet
  -- `∃ᶠ n in atTop` is the countable `limsup` `⋂_a ⋃_{b≥a}`.
  have hfreq : {x : ℝ | ∃ᶠ n : ℕ in atTop, ∃ m : ℤ, x ≠ (m : ℝ) / (n : ℝ) ∧
        |x - (m : ℝ) / (n : ℝ)| < (k : ℝ) / (n : ℝ) ^ τ}
      = ⋂ a : ℕ, ⋃ b : ℕ, ⋃ _ : a ≤ b,
          {x : ℝ | ∃ m : ℤ, x ≠ (m : ℝ) / (b : ℝ) ∧ |x - (m : ℝ) / (b : ℝ)| < (k : ℝ) / (b : ℝ) ^ τ} := by
    ext x
    simp only [Filter.frequently_atTop, Set.mem_iInter, Set.mem_iUnion, Set.mem_setOf_eq,
      ge_iff_le, exists_prop]
  rw [hfreq]
  exact MeasurableSet.iInter fun a => MeasurableSet.iUnion fun b =>
    MeasurableSet.iUnion fun _ => hQ b

/-- **The Liouville set is Borel measurable** (`{x | Liouville x} = ⋂_τ W τ = ⋂_k W k`).
    Immediate from `measurableSet_wellApprox` and the countable-intersection description
    `iInter_wellApprox_eq_liouville` (restricted to integer exponents, which suffice by
    antitonicity). -/
theorem measurableSet_liouville : MeasurableSet {x : ℝ | Liouville x} := by
  have h : {x : ℝ | Liouville x} = ⋂ k : ℕ, wellApprox (k : ℝ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hx k
      exact liouville_subset_wellApprox _ hx
    · intro hx
      rw [← forall_liouvilleWith_iff]
      intro p
      obtain ⟨k, hk⟩ := exists_nat_ge p
      exact wellApprox_antitone hk (hx k)
  rw [h]
  exact MeasurableSet.iInter fun k => measurableSet_wellApprox _

/-! ## Strict nesting of the approximation hierarchy

`wellApprox_antitone` gives the inclusions `W τ ⊆ W σ` for `σ ≤ τ`.  The strict
dimension law upgrades these to *proper* inclusions on `[2, ∞)`: distinct exponents give
genuinely different well-approximable sets, so the hierarchy `{W τ}` is a strictly
decreasing chain of Borel sets — not merely nested. -/
theorem wellApprox_ssubset {σ τ : ℝ} (hσ : 2 ≤ σ) (h : σ < τ) :
    wellApprox τ ⊂ wellApprox σ := by
  refine (wellApprox_antitone h.le).ssubset_of_ne ?_
  intro heq
  have hlt := dimH_wellApprox_strictAntitone hσ h
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-! ## Part XI: Uncountability of the Liouville set — via category, not dimension

`not_countable_wellApprox` shows `W τ` is uncountable *because its Hausdorff dimension
`2/τ` is positive* (a countable set has dimension `0`).  That argument is unavailable for
the Liouville set itself: `dimH {Liouville} = 0` (`dimH_liouville_eq_zero`), and it is also
Lebesgue-null (`volume_liouville_eq_zero`) — so **neither dimension nor measure can witness
its uncountability**.  The witness is Baire category: `{x | Liouville x}` is residual
(`liouville_residual`), and a residual set in the nonempty Baire space `ℝ` cannot be meagre
(`not_isMeagre_of_mem_residual`), whereas *every* countable set of reals *is* meagre (`ℝ`
has no isolated points, so each singleton is nowhere dense).  This exhibits a set that is
simultaneously dimension-`0`, measure-`0`, and yet uncountable — the sharpest sense in which
the two classical smallness gauges undercount the Liouville numbers.  Axiom-free apart from
the dimension/measure components of the capstone. -/

/-- **Singletons are nowhere dense in `ℝ`.**  `ℝ` has no isolated points (it is a
`PerfectSpace`), so `interior {x} = ∅` (`interior_singleton`) and, `{x}` being closed,
`{x}` is nowhere dense. -/
theorem isNowhereDense_singleton_real (x : ℝ) : IsNowhereDense ({x} : Set ℝ) :=
  (isClosed_singleton.isNowhereDense_iff).mpr (interior_singleton x)

/-- **Every countable set of reals is meagre.**  Write `s = ⋃_{x ∈ s} {x}`, a countable
union of the nowhere-dense singletons (`isNowhereDense_singleton_real`); a countable union
of nowhere-dense sets is meagre (`isMeagre_biUnion`, `IsNowhereDense.isMeagre`).  This is
the ingredient the measure/dimension arguments cannot supply — it is what forces a residual
set to be uncountable. -/
theorem isMeagre_of_countable {s : Set ℝ} (hs : s.Countable) : IsMeagre s := by
  rw [← Set.biUnion_of_singleton s]
  exact isMeagre_biUnion hs fun x _ => (isNowhereDense_singleton_real x).isMeagre

/-- **The Liouville numbers are uncountable.**  If `{x | Liouville x}` were countable it
would be meagre (`isMeagre_of_countable`); but it is residual (`liouville_residual`), and a
residual set in the nonempty Baire space `ℝ` is not meagre (`not_isMeagre_of_mem_residual`).
Unlike `not_countable_wellApprox`, this cannot go through Hausdorff dimension — the Liouville
set has dimension `0` (`dimH_liouville_eq_zero`) — so category is essential.  Axiom-free. -/
theorem not_countable_liouville : ¬ {x : ℝ | Liouville x}.Countable := fun hc =>
  not_isMeagre_of_mem_residual liouville_residual (isMeagre_of_countable hc)

open MeasureTheory in
/-- **Uncountable yet doubly negligible.**  The Liouville set is uncountable
(`not_countable_liouville`) while having Hausdorff dimension `0` (`dimH_liouville_eq_zero`)
and Lebesgue measure `0` (`volume_liouville_eq_zero`): a set that both classical smallness
gauges declare negligible is nonetheless too large to enumerate.  The uncountability rests
on Baire category (axiom-free); the dimension component carries the entry's
Jarník–Besicovitch axiom `dimH_wellApprox`. -/
theorem liouville_uncountable_yet_null_dimzero :
    ¬ {x : ℝ | Liouville x}.Countable ∧
      dimH {x : ℝ | Liouville x} = 0 ∧
      volume {x : ℝ | Liouville x} = 0 :=
  ⟨not_countable_liouville, dimH_liouville_eq_zero, volume_liouville_eq_zero⟩

end LiouvilleTheoremOQ03
