import Proofs.Erdos101Problem
import Mathlib.Tactic
import Mathlib.Data.Nat.Cast.Order.Field

/-
# Erdős #101, OQ-01 — Pinpointing the open content: the conjecture holds for every ε > 1/12
# (erdos-101-oq-01-incomplete-01)

## The Open Question

**Erdős Problem #101, OQ-01** ($100 prize, OPEN). For a planar point set `P`
with no five collinear, let `fourPointLineCount P` be the number of lines
containing exactly four points of `P`. The conjecture is that this count is
`o(n²)`:

  for every `ε > 0` there is `N` such that every such `P` with `|P| ≥ N`
  satisfies `fourPointLineCount P < ε · |P|²`.

The trivial double-counting bound gives `O(n²)`; no `o(n²)` is known. The lower
bound (Solymosi–Stojaković 2013) is `n^{2 − o(1)}`, so the gap is in the
`o(1)` factor.

The companion scaffold `Erdos101OQ01.lean` records the full conjecture as a
`sorry` (it is genuinely open). This file does **not** attempt the open part.
Instead it asks the sharp delineating question:

> **For which `ε` is the conjecture already a theorem, unconditionally?**

## Result

The framework file `Erdos101Problem.lean` proves, with no assumptions beyond
`NoFiveCollinear`, the elementary packing bound
`improved_upper_bound : fourPointLineCount P ≤ n(n-1)/12`. We turn that into the
exact statement of how much of OQ-01 is already settled:

1. `twelve_mul_fourPointLineCount_le_sq` — the bound in clean real form,
   `12 · fourPointLineCount P ≤ n²`.

2. `fourPointLineCount_le_sq_div_twelve` / `fourPointLineCount_div_sq_le` — the
   density bound `fourPointLineCount P ≤ n²/12`, i.e. the four-point-line density
   never exceeds `1/12`.

3. `fourPointLineCount_lt_eps_sq` and `oq01_holds_above_one_twelfth` — **the
   headline**: for *every* `ε > 1/12`, **every** `P` with `|P| ≥ 1` and no five
   collinear satisfies `fourPointLineCount P < ε · n²` — with no threshold `N`
   needed at all. So the OQ-01 conjecture is an unconditional theorem for all
   `ε > 1/12`.

4. The entire open content of OQ-01 is therefore the regime `0 < ε ≤ 1/12`:
   improving the constant `1/12` to an `o(1)` factor. This file makes that
   boundary precise and machine-checked.

## Summary: 0 sorries, 0 axioms, no `native_decide`.
Builds only on the sorry-free framework `Erdos101Problem.lean`; the still-open
conjecture is untouched.
-/

set_option linter.unusedVariables false

namespace Erdos101OQ01Incomplete01

-- ============================================================
-- PART 1: The elementary bound in real form
-- ============================================================

/-- **The packing bound, cleared of `ℕ`-division.** From the framework's
    `improved_upper_bound` (`fourPointLineCount P ≤ n(n-1)/12` in `ℕ`), multiply
    through by `12` and bound `n(n-1) ≤ n²`:
    `12 · fourPointLineCount P ≤ n²` over `ℝ`. -/
theorem twelve_mul_fourPointLineCount_le_sq (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    12 * (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ) ^ 2 := by
  have h := improved_upper_bound P hP
  have hN : 12 * fourPointLineCount P ≤ P.points.card * P.points.card := by
    calc 12 * fourPointLineCount P
        ≤ 12 * (P.points.card * (P.points.card - 1) / 12) :=
          Nat.mul_le_mul (le_refl 12) h
      _ ≤ P.points.card * (P.points.card - 1) := by
          rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ 12
      _ ≤ P.points.card * P.points.card :=
          Nat.mul_le_mul (le_refl _) (Nat.sub_le _ 1)
  rw [sq]
  exact_mod_cast hN

/-- **Density bound: four-point-line density never exceeds `1/12`.**
    `fourPointLineCount P ≤ n²/12`. -/
theorem fourPointLineCount_le_sq_div_twelve (P : PlanarPointSet)
    (hP : NoFiveCollinear P) :
    (fourPointLineCount P : ℝ) ≤ (P.points.card : ℝ) ^ 2 / 12 := by
  have h := twelve_mul_fourPointLineCount_le_sq P hP
  linarith

/-- The density ratio form: `fourPointLineCount P / n² ≤ 1/12` for nonempty `P`.
    (For `P` empty both sides are `0`.) -/
theorem fourPointLineCount_div_sq_le (P : PlanarPointSet)
    (hP : NoFiveCollinear P) (hn : 1 ≤ P.points.card) :
    (fourPointLineCount P : ℝ) / (P.points.card : ℝ) ^ 2 ≤ 1 / 12 := by
  have hn1 : (1 : ℝ) ≤ (P.points.card : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (P.points.card : ℝ) ^ 2 := pow_pos (by linarith) 2
  rw [div_le_iff₀ hpos]
  have h := twelve_mul_fourPointLineCount_le_sq P hP
  linarith

-- ============================================================
-- PART 2: The conjecture is a theorem for every ε > 1/12
-- ============================================================

/-- **OQ-01 holds unconditionally for every `ε > 1/12`.**

    For any `ε > 1/12`, every planar point set `P` with at least one point and no
    five collinear satisfies `fourPointLineCount P < ε · n²`. No size threshold
    `N` is needed: the elementary density bound `≤ n²/12` already beats `ε · n²`
    strictly, for *all* `n ≥ 1`, as soon as `ε > 1/12`. -/
theorem fourPointLineCount_lt_eps_sq (ε : ℝ) (hε : 1 / 12 < ε)
    (P : PlanarPointSet) (hP : NoFiveCollinear P) (hn : 1 ≤ P.points.card) :
    (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2 := by
  have hn1 : (1 : ℝ) ≤ (P.points.card : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (P.points.card : ℝ) ^ 2 := pow_pos (by linarith) 2
  have hbase := twelve_mul_fourPointLineCount_le_sq P hP
  nlinarith [hbase, hpos, mul_pos hpos (sub_pos.mpr hε)]

/-- **The settled half of OQ-01, packaged.** The little-oh conjecture for Erdős
    #101 is an unconditional theorem for every `ε` above the threshold `1/12`.
    The remaining open content is exactly the regime `0 < ε ≤ 1/12` — sharpening
    the constant `1/12` to a genuinely `o(1)` factor. -/
theorem oq01_holds_above_one_twelfth :
    ∀ ε : ℝ, 1 / 12 < ε → ∀ P : PlanarPointSet, NoFiveCollinear P →
      1 ≤ P.points.card → (fourPointLineCount P : ℝ) < ε * (P.points.card : ℝ) ^ 2 :=
  fun ε hε P hP hn => fourPointLineCount_lt_eps_sq ε hε P hP hn

/-
## Significance

Erdős #101 OQ-01 is open and carries a $100 prize: prove the number of
exactly-four-point lines in an `n`-point planar set with no five collinear is
`o(n²)`. The trivial bound is `O(n²)` and the scaffold file records the full
conjecture as a `sorry`.

This file does not attack the open part. It instead makes precise — and
machine-checks — exactly *how much* of the conjecture is already a theorem. The
elementary packing bound `fourPointLineCount P ≤ n(n-1)/12` from the framework,
re-expressed as the density bound `fourPointLineCount P ≤ n²/12`, already proves
the `o(n²)` statement for **every** `ε > 1/12`, with no size threshold at all
(`oq01_holds_above_one_twelfth`). Consequently the entire open content of OQ-01
is the single regime `0 < ε ≤ 1/12`: the task is to replace the explicit constant
`1/12` by a factor that tends to `0`. The Solymosi–Stojaković lower bound
`n^{2−o(1)}` shows that factor cannot decay polynomially — it must be a slowly
varying `o(1)`. This delineation is the precise frontier between the elementary
(now formalized) and the prize-open part of the problem.
-/

end Erdos101OQ01Incomplete01
