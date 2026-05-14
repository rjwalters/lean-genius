/-
# (q,t)-Multichoose: First Lean Skeleton (S2 ACT)
(arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02)

## OQ Statement

Parent (`arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03`) proves that
the q-multichoose coefficient is the Gaussian binomial. This sub-OQ asks
whether a Macdonald-style (q,t)-deformation exists that recovers q-multichoose
at `t = 1` and integer multichoose at `q = t = 1`.

This file ships the **S2 ACT skeleton**: definitions of `qtBinom` and
`qtMultichoose`, plus four boundary cases (k = 0 and k = 1, for each of
`qtBinom` and `qtMultichoose`) and the unconditional k-direction multiplicative
recurrence `qtBinom_succ`. The recurrence is the foundation for the
**k-direction telescoping ratio**
  `qtBinom q t N (k+1) / qtBinom q t N k = (1 - q^(N-k) t^k) / (1 - q^(k+1) t^k)`
recommended by S6 PREP (`2026-05-13-s06-...md`) as the clean S2-onwards
recurrence, replacing the Pascal-style form falsified at four data points.

## What this file is NOT

* No `at_t_eq_one` substitution theorem (S3 ACT target; Path A vs Path C
  decision per S4 PREP / S5 PREP).
* No `at_one_one` limit theorem (S4 ACT target; requires either L'Hôpital
  cancellation or RatFunc evaluation per S5 PREP).
* No Pascal-style recurrence (S6 PREP falsified it; the product formula
  factorises along `k`, not Pascal's two-direction).

## PREP cascade context

After S1 OBSERVE (PR #18327, 2026-05-12), five doc-only PREPs landed
without a Lean file:

| Iter | PR | Topic |
|------|----|-------|
| S2 PREP | #18382 | Pascal forms falsified at small cases |
| S3 PREP | #18558 | qtMC rational over Q(q,t); polynomial sub-lattice |
| S4 PREP | #18616 | `Field R` 0/0 trap; Paths A/B/C |
| S5 PREP | #18639 | `RatFunc.eval` rescues Path C, no `q ≠ 1` needed |
| S6 PREP | #18734 | Option α falsified; k-direction telescoping recommended |

The slug's `state.md` flagged this as the upper edge of doc-only PREP
backlog. This file ships the long-awaited Lean skeleton.

## Status

* Axioms: 0
* Sorries: 0
* Theorems: 5 (2 simp boundary, 1 single-factor evaluation, 1 multichoose
  reduction, 1 unconditional recurrence)

## Build status

Build pending (Docker daemon required per project convention; per CLAUDE.md
never invoke `lake build` directly). All five new lemmas use standard
`Finset.prod` API + `omega` for ℕ-index normalization; no novel tactics.
-/

import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03

namespace QtMultichooseCoefficients

open BigOperators

-- We work over a field so that the Macdonald rational product is well-typed.
-- `Field R` is the Path A choice from S4 PREP (cheapest of the three rescues;
-- Path B re-defines the function piecewise, Path C lifts to `RatFunc ℚ`).
variable {R : Type*} [Field R]

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- The **Macdonald (q,t)-binomial coefficient**, as a rational expression:
    `qtBinom q t N k := ∏ i ∈ Finset.range k, (1 - q^(N-i) t^i) / (1 - q^(i+1) t^i)`.

    Using the 0-indexed `Finset.range k` convention, the standard 1-indexed
    Macdonald product `∏_{i=1}^{k} (1 - q^{N+1-i} t^{i-1}) / (1 - q^{i} t^{i-1})`
    rewrites to `∏ i ∈ range k, (1 - q^(N-i) t^i) / (1 - q^(i+1) t^i)`.

    At `t = 1` (and `q ≠ 1` per Path A) reduces to `qBinom q N k`; the
    substitution proof is the S3 ACT target. -/
noncomputable def qtBinom (q t : R) (N k : ℕ) : R :=
  ∏ i ∈ Finset.range k, (1 - q ^ (N - i) * t ^ i) / (1 - q ^ (i + 1) * t ^ i)

/-- The **(q,t)-multichoose coefficient**: `qtMultichoose q t n k := qtBinom q t (n+k-1) k`.

    At `t = 1` recovers `qMultichoose q n k` (S3 ACT target); at `q = t = 1`
    recovers `Nat.multichoose n k` (S4 ACT target, via cancellation). -/
noncomputable def qtMultichoose (q t : R) (n k : ℕ) : R :=
  qtBinom q t (n + k - 1) k

-- ============================================================
-- SECTION II: Boundary cases (k = 0)
-- ============================================================

/-- Empty-product boundary: `qtBinom q t N 0 = 1`. -/
@[simp]
theorem qtBinom_zero_right (q t : R) (N : ℕ) : qtBinom q t N 0 = 1 := by
  simp [qtBinom]

/-- Empty-product boundary for `qtMultichoose`: `qtMultichoose q t n 0 = 1`. -/
@[simp]
theorem qtMultichoose_zero_right (q t : R) (n : ℕ) :
    qtMultichoose q t n 0 = 1 := by
  simp [qtMultichoose]

-- ============================================================
-- SECTION III: Boundary cases (k = 1)
-- ============================================================

/-- Single-factor evaluation: `qtBinom q t N 1 = (1 - q^N) / (1 - q)`.
    The result is independent of `t` because the product runs over a single
    term `i = 0`, in which `t^0 = 1`. -/
theorem qtBinom_one_right (q t : R) (N : ℕ) :
    qtBinom q t N 1 = (1 - q ^ N) / (1 - q) := by
  unfold qtBinom
  rw [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  simp

/-- `qtMultichoose q t n 1 = (1 - q^n) / (1 - q)`, also independent of `t`.
    Follows from `qtBinom_one_right` after normalising `n + 1 - 1 = n`. -/
theorem qtMultichoose_one_right (q t : R) (n : ℕ) :
    qtMultichoose q t n 1 = (1 - q ^ n) / (1 - q) := by
  simp only [qtMultichoose, show n + 1 - 1 = n from by omega]
  exact qtBinom_one_right q t n

-- ============================================================
-- SECTION IV: The k-direction multiplicative recurrence
-- ============================================================

/-- **k-direction multiplicative recurrence** (the foundational form, S6 PREP §0):

    `qtBinom q t N (k+1) = qtBinom q t N k * ((1 - q^(N-k) t^k) / (1 - q^(k+1) t^k))`.

    Unconditional — no hypothesis on `q`, `t`, `N`, or `k`. This is a direct
    application of `Finset.prod_range_succ` to the product-form definition.

    Dividing both sides by `qtBinom q t N k` (when nonzero) yields the
    **k-direction telescoping ratio** identity flagged by S6 PREP as the
    clean rational recurrence for `qtBinom`. The ratio form is the natural
    foundation for S3 (`at_t_eq_one`) and S4 (`at_one_one`): both follow by
    induction on `k`, using the parent's `qBinom_product` identity and
    Macdonald cancellation respectively. -/
theorem qtBinom_succ (q t : R) (N k : ℕ) :
    qtBinom q t N (k + 1) =
    qtBinom q t N k * ((1 - q ^ (N - k) * t ^ k) / (1 - q ^ (k + 1) * t ^ k)) := by
  unfold qtBinom
  rw [Finset.prod_range_succ]

end QtMultichooseCoefficients
