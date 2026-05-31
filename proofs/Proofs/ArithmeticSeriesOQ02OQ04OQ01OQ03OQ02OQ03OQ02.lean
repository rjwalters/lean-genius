/-
# (q,t)-Multichoose: S2 Skeleton + S3 ACT (t = 1 specialization)
(arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02)

## OQ Statement

Parent (`arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03`) proves that
the q-multichoose coefficient is the Gaussian binomial. This sub-OQ asks
whether a Macdonald-style (q,t)-deformation exists that recovers q-multichoose
at `t = 1` and integer multichoose at `q = t = 1`.

## Contents

**S2 ACT (researcher-9, 2026-05-13)**: definitions of `qtBinom` and
`qtMultichoose`, four boundary cases, and the unconditional k-direction
multiplicative recurrence `qtBinom_succ`.

**S3 ACT (researcher-1, 2026-05-30, this iteration)**: the t = 1 substitution
theorem `qtBinom_at_t_eq_one` and its `qtMultichoose` corollary. Both work
under Path A (S4 PREP) — hypothesis `q^(j+1) ≠ 1` for `j < k`, which keeps
the Macdonald denominators nonzero on the open dense set of non-roots-of-
unity. The proof uses a new private helper `qBinom_mult_recur` (a CommRing
multiplicative q-Pascal derived by subtracting `qBinom_pascal` and
`qBinom_pascal'`), bridged to the rational `qtBinom_succ` via `div_eq_iff`.

The k-direction recurrence
  `qtBinom q t N (k+1) = qtBinom q t N k · (1 - q^(N-k) t^k) / (1 - q^(k+1) t^k)`
(S6 PREP §0) is the foundation; specializing `t = 1` and using the new
CommRing multiplicative q-Pascal closes the gap to the parent's q-binomial.

## What this file still does NOT contain

* No `at_one_one` limit theorem (S4/S5 ACT target; requires either L'Hôpital
  cancellation or `RatFunc.eval` per S5 PREP — the (q,t) → (1,1) limit hits
  the removable 0/0 singularity that Path A side-steps).
* No Pascal-style recurrence (S6 PREP falsified it; the product formula
  factorises along `k`, not Pascal's two-direction).
* No Macdonald-polynomial principal-specialization axiom (optional S6 step).

## PREP cascade context

After S1 OBSERVE (PR #18327, 2026-05-12), five doc-only PREPs landed
without a Lean file (S2 PREP #18382, S3 PREP #18558, S4 PREP #18616,
S5 PREP #18639, S6 PREP #18734), then S2 ACT shipped the skeleton.
This iteration discharges the S3 ACT next-action listed in
`src/data/research/problems/arithmetic-series-oq-02-...-oq-02.json`.

## Status

* Axioms: 0
* Sorries: 0
* Theorems: 7 (2 simp boundary, 1 single-factor evaluation, 1 multichoose
  reduction, 1 unconditional k-direction recurrence, 2 S3 ACT
  specialization theorems)
* Lemmas (private): 1 (`qBinom_mult_recur`, CommRing multiplicative q-Pascal)

## Build status

Build pending (Docker daemon required per project convention; per CLAUDE.md
never invoke `lake build` directly). The S3 ACT additions use only standard
Mathlib tactics: `linear_combination`, `mul_div_assoc`, `div_eq_iff`, `omega`
— no novel proof machinery.
-/

import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03

namespace QtMultichooseCoefficients

open BigOperators QBinomialCoefficients QMultichooseCoefficients

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

-- ============================================================
-- SECTION V: S3 ACT — Specialization at t = 1
-- ============================================================

/-- **Helper (CommRing-level multiplicative q-Pascal)**:

    `qBinom q n (k+1) · (1 - q^(k+1)) = qBinom q n k · (1 - q^(n-k))`.

    Unconditional — holds over any `CommRing` (the `Field R` constraint of this
    file is only needed for the rational `qtBinom`). Derived by subtracting the
    two q-Pascal identities (first and second) which both expand
    `qBinom q (n+1) (k+1)`; the `q^(k+1)` and `q^(n-k)` weights cancel via
    `linear_combination`. Out-of-range `n < k`: both `qBinom` factors are zero. -/
private lemma qBinom_mult_recur (q : R) (n k : ℕ) :
    qBinom q n (k + 1) * (1 - q ^ (k + 1)) = qBinom q n k * (1 - q ^ (n - k)) := by
  by_cases hk : k + 1 ≤ n + 1
  · have h1 := qBinom_pascal q n k
    have h2 := qBinom_pascal' q n k hk
    linear_combination h1 - h2
  · push_neg at hk
    have hk' : n < k := by omega
    rw [qBinom_eq_zero_of_lt q n k hk', qBinom_eq_zero_of_lt q n (k + 1) (by omega)]
    ring

/-- **S3 ACT, foundational lemma**: the Macdonald `(q,t)`-binomial at `t = 1`
    equals the Gaussian q-binomial coefficient, under the non-degeneracy
    hypothesis `q^(j+1) ≠ 1` for `j < k` (Path A from S4 PREP — keeps the
    rational Macdonald denominators away from zero).

    Proof: induction on `k`. The base case is the empty product (= 1). The
    inductive step combines the k-direction recurrence `qtBinom_succ` (the
    Macdonald side) with the multiplicative q-Pascal recurrence
    `qBinom_mult_recur` (the Gaussian side), bridged by the field identity
    `a · (b/c) = d ↔ a · b = d · c` (when `c ≠ 0`). -/
theorem qtBinom_at_t_eq_one (q : R) (N : ℕ) :
    ∀ k, (∀ j, j < k → q ^ (j + 1) ≠ 1) → qtBinom q 1 N k = qBinom q N k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hq
    have ih' : qtBinom q 1 N k = qBinom q N k :=
      ih (fun j hj => hq j (by omega))
    have h_ne : (1 - q ^ (k + 1) : R) ≠ 0 := by
      intro h
      exact hq k (by omega) (sub_eq_zero.mp h).symm
    rw [qtBinom_succ, ih']
    simp only [one_pow, mul_one]
    rw [← mul_div_assoc, div_eq_iff h_ne]
    exact (qBinom_mult_recur q N k).symm

/-- **S3 ACT, headline theorem**: at `t = 1` the (q,t)-multichoose coefficient
    recovers the q-multichoose coefficient (the parent gallery entry's
    Gaussian-binomial q-analog of `Nat.multichoose`).

    The hypothesis `q^(j+1) ≠ 1` for `j < k` is the standard Path A
    non-degeneracy condition: for `q` not a root of unity of order ≤ k, the
    rational Macdonald product is well-defined and specialises cleanly at
    `t = 1`. Note that the parent's `qMultichoose q n k` is well-defined
    without this hypothesis (no division), so this theorem says the **rational
    Macdonald form** agrees with the **polynomial Gaussian form** at `t = 1` on
    the open dense set `{q : q^j ≠ 1 for 1 ≤ j ≤ k}`.

    Direct corollary of `qtBinom_at_t_eq_one` via the `n + k - 1` index shift
    common to both definitions. -/
theorem qtMultichoose_at_t_eq_one (q : R) (n k : ℕ)
    (hq : ∀ j, j < k → q ^ (j + 1) ≠ 1) :
    qtMultichoose q 1 n k = qMultichoose q n k := by
  unfold qtMultichoose qMultichoose
  exact qtBinom_at_t_eq_one q (n + k - 1) k hq

end QtMultichooseCoefficients
