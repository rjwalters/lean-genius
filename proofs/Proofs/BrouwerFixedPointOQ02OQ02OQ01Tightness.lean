import Mathlib
import Proofs.BrouwerFixedPointOQ02OQ02OQ01AdversaryFamily

/-
# Brouwer Fixed Point: OQ-02 / OQ-02 / OQ-01
# Tightness of the One-Query Lower Bound — the Query is Worthless

## Open Question (oq-02-oq-02-oq-01), completion of the characterization
The base entry `BrouwerFixedPointOQ02OQ02OQ01Adversary.lean` and its
parametrized extension `...AdversaryFamily.lean` establish the **lower** half of
the story: over the class of affine contractions of [0,1] probed by a single
value query at `x = 0`, the one-query worst-case error has *supremum* exactly
`1/2` (`sup_lower_bound_is_half`). No one-query algorithm can guarantee accuracy
below `1/2`.

What was never formalized is the matching **upper** half — and its striking
consequence. Because every fixed point of a self-map of [0,1] lies in [0,1], the
*constant* answer `A₀ ≡ 1/2` (which ignores its oracle input entirely — a genuine
**zero-query** algorithm) already errs by at most `1/2` on every instance, and by
exactly `1/2 − δ < 1/2` on the family pair at parameter `δ`. Its worst-case error
therefore has supremum `1/2` as well.

Putting the two halves together yields the sharp characterization:

  the one-query minimax error over this class **equals** the zero-query minimax
  error, both `= 1/2`.

In other words, for the adversary family, **the single value query is worthless**:
it buys no worst-case accuracy over simply guessing the midpoint. This is the
quantitative heart of the Chen–Deng query-complexity phenomenon at `n = 1`.

## Results (0 sorries, 0 axioms)
1. `A₀`, `A₀_ignores_input` — the input-ignoring midpoint (zero-query) algorithm.
2. `midpoint_error_le_half` — `A₀` errs by `≤ 1/2` on *any* fixed point in [0,1].
3. `midpoint_family_error` — on the family pair its max error is exactly `1/2 − δ`.
4. `midpoint_family_error_lt_half` — hence `< 1/2` on every single instance.
5. `midpoint_worst_case_sup` — its worst-case error nonetheless has supremum `1/2`.
6. `minimax_lower_bound` — every algorithm has worst-case error `≥ 1/2` (repackaging
   of the family lower bound: no algorithm beats the midpoint in the worst case).
7. `one_query_minimax_error_eq_half` — the capstone two-sided statement: the class
   forces worst-case error up to `1/2` against *every* algorithm, while the
   zero-query `A₀` already attains it. The query provides no worst-case advantage.

Reference: Chen–Deng (2009); the adversary method (Aaronson / Ambainis); the
sibling entries `BrouwerFixedPointOQ02OQ02OQ01Adversary.lean` and
`BrouwerFixedPointOQ02OQ02OQ01AdversaryFamily.lean`.
-/

set_option linter.unusedVariables false

namespace BrouwerOQ02OQ02OQ01Tightness

open Set
open BrouwerOQ02OQ02OQ01AdversaryFamily

-- ============================================================
-- SECTION I: The zero-query midpoint algorithm and its upper bound
-- ============================================================

/-- The **midpoint algorithm**: always answer `1/2`, ignoring the oracle value.
    A genuine *zero-query* algorithm, viewed as a degenerate one-query one. -/
noncomputable def A₀ : ℝ → ℝ := fun _ => 1 / 2

/-- `A₀` truly ignores its input: it returns the same answer for every observation.
    This is what makes the tightness result say "the query is worthless". -/
theorem A₀_ignores_input (x y : ℝ) : A₀ x = A₀ y := rfl

/-- **Trivial upper bound.** Since every fixed point of a self-map of [0,1] lies in
    [0,1], the midpoint answer errs by at most `1/2` against it — with no query. -/
theorem midpoint_error_le_half {p : ℝ} (hp : p ∈ Icc (0:ℝ) 1) :
    |(1 / 2 : ℝ) - p| ≤ 1 / 2 := by
  rw [mem_Icc] at hp
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2]

-- ============================================================
-- SECTION II: The midpoint algorithm on the adversary family
-- ============================================================

/-- On the family pair at parameter `δ`, `A₀`'s error against *both* true fixed
    points (`δ` and `1 − δ`) is the same value `1/2 − δ`; hence so is its max. -/
theorem midpoint_family_error {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    max (|A₀ (fδ δ 0) - δ|) (|A₀ (gδ δ 0) - (1 - δ)|) = 1 / 2 - δ := by
  have e1 : |A₀ (fδ δ 0) - δ| = 1 / 2 - δ := by
    show |(1 / 2 : ℝ) - δ| = 1 / 2 - δ
    rw [abs_of_nonneg (by linarith)]
  have e2 : |A₀ (gδ δ 0) - (1 - δ)| = 1 / 2 - δ := by
    show |(1 / 2 : ℝ) - (1 - δ)| = 1 / 2 - δ
    rw [show (1 / 2 : ℝ) - (1 - δ) = -(1 / 2 - δ) by ring, abs_neg,
      abs_of_nonneg (by linarith)]
  rw [e1, e2, max_self]

/-- On *every single instance* the midpoint answer strictly beats accuracy `1/2`. -/
theorem midpoint_family_error_lt_half {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    max (|A₀ (fδ δ 0) - δ|) (|A₀ (gδ δ 0) - (1 - δ)|) < 1 / 2 := by
  rw [midpoint_family_error h0 h1]; linarith

/-- **The midpoint algorithm's worst-case error has supremum `1/2`.**
    For every target `ε < 1/2` there is a parameter `δ` on which `A₀`'s error
    exceeds `1/2 − ε`. Combined with `midpoint_family_error_lt_half`, the worst-case
    error of `A₀` is the *supremum* `1/2`, matching the lower bound exactly. -/
theorem midpoint_worst_case_sup {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      1 / 2 - ε < max (|A₀ (fδ δ 0) - δ|) (|A₀ (gδ δ 0) - (1 - δ)|) := by
  refine ⟨ε / 2, by linarith, by linarith, ?_⟩
  rw [midpoint_family_error (by linarith) (by linarith)]
  linarith

-- ============================================================
-- SECTION III: Minimax lower bound and the capstone tightness theorem
-- ============================================================

/-- **Every algorithm has worst-case error `≥ 1/2`.**
    For any one-query algorithm `A` and any target `ε < 1/2` there is a family
    parameter `δ` forcing `A`'s error to exceed `1/2 − ε`. This repackages the
    parametrized lower bound `one_query_lower_bound_family`: no algorithm can do
    better than the input-ignoring midpoint in the worst case. -/
theorem minimax_lower_bound (A : ℝ → ℝ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      1 / 2 - ε < max (|A (fδ δ 0) - δ|) (|A (gδ δ 0) - (1 - δ)|) := by
  refine ⟨ε / 2, by linarith, by linarith, ?_⟩
  have h := one_query_lower_bound_family (δ := ε / 2) (by linarith) A
  have hrw : (1 - 2 * (ε / 2)) / 2 = 1 / 2 - ε / 2 := by ring
  rw [hrw] at h
  linarith

/-- **Capstone: the one-query minimax error equals the zero-query minimax error `= 1/2`.**

    The conjunction packages the two-sided tightness of the adversary bound:

    * (lower) against **every** algorithm `A`, the family forces worst-case error
      arbitrarily close to `1/2` from below — so no algorithm, however it uses its
      one query, guarantees accuracy `≤ ε` uniformly for any `ε < 1/2`; yet

    * (upper) the input-ignoring **zero-query** midpoint algorithm `A₀` already
      achieves error `< 1/2` on every instance (worst case `= 1/2` in the limit).

    Hence the single value query buys **no** worst-case accuracy: one-query
    complexity `= 1/2 =` zero-query complexity over this class. -/
theorem one_query_minimax_error_eq_half :
    (∀ A : ℝ → ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
      ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
        1 / 2 - ε < max (|A (fδ δ 0) - δ|) (|A (gδ δ 0) - (1 - δ)|))
    ∧ (∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
        max (|A₀ (fδ δ 0) - δ|) (|A₀ (gδ δ 0) - (1 - δ)|) < 1 / 2) := by
  refine ⟨fun A ε hε0 hε1 => minimax_lower_bound A hε0 hε1, ?_⟩
  intro δ h0 h1
  exact midpoint_family_error_lt_half h0 h1

end BrouwerOQ02OQ02OQ01Tightness
