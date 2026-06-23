/-
# (q,t)-Multichoose: S2 Skeleton + S3/S4/S5 ACT (polynomial sub-lattice qNumber bridges)
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

**S3 ACT (researcher-1, 2026-05-30)**: the t = 1 substitution theorem
`qtBinom_at_t_eq_one` and its `qtMultichoose` corollary. Both work
under Path A (S4 PREP) — hypothesis `q^(j+1) ≠ 1` for `j < k`, which keeps
the Macdonald denominators nonzero on the open dense set of non-roots-of-
unity. The proof uses a new private helper `qBinom_mult_recur` (a CommRing
multiplicative q-Pascal derived by subtracting `qBinom_pascal` and
`qBinom_pascal'`), bridged to the rational `qtBinom_succ` via `div_eq_iff`.

**S4 ACT (researcher-1, 2026-05-31)**: two complementary
formal facts about the polynomial sub-lattice and the `Field R` 0/0 trap:
* `qtMultichoose_two_two` — the unique "interior" t-cancellation at
  `(n, k) = (2, 2)`: `qtMultichoose q t 2 2 = (1 - q^3) / (1 - q)`,
  under the Path A guard `1 - q^2 t ≠ 0`. This is the only point in the
  S3 PREP polynomial sub-lattice (`{k ≤ 1} ∪ {(2,2)}`) that is genuinely
  interior; it falls out of `qtBinom_succ` after a single cancellation.
* `qtBinom_at_one_one_eq_zero` + `qtMultichoose_at_one_one_eq_zero` —
  the Lean `Field R` convention `(0 : R) / 0 = 0` collapses the joint
  `(q, t) = (1, 1)` substitution to **0** for any `k ≥ 1`, not the
  classical `Nat.multichoose n k`. Formalising the trap pins down why
  Path A's `q^(j+1) ≠ 1` hypothesis is mandatory and motivates the
  Path C (`RatFunc`) migration for future S5+ work.

**S5 ACT (researcher-1, 2026-06-01, this iteration)**: three polynomial-form
bridge lemmas that connect the rational Macdonald presentation of the
polynomial sub-lattice `{k ≤ 1} ∪ {(2, 2)}` (S4 ACT) to the parent's
polynomial `qNumber` presentation:
* `qtBinom_one_right_eq_qNumber` — at `k = 1`, the rational form
  `(1 - q^N) / (1 - q)` equals the polynomial `qNumber q N` provided
  `1 - q ≠ 0`. Proved by combining `qtBinom_one_right` with the parent's
  `qNumber_geometric`.
* `qtMultichoose_one_right_eq_qNumber` — corollary at `qtMultichoose` level.
* `qtMultichoose_two_two_eq_qNumber` — the unique "interior" polynomial
  sub-lattice point equals `qNumber q 3 = 1 + q + q²` provided
  `1 - q² t ≠ 0` and `1 - q ≠ 0`. Proved analogously via
  `qtMultichoose_two_two` + `qNumber_geometric` for `n = 3`.

Together, these make the polynomial sub-lattice characterisation **fully
polynomial**: every point in `{k ≤ 1} ∪ {(2, 2)}` is now formally
equated to a `qNumber` expression from the parent (which is itself a
visible polynomial in `q`), so that the polynomial-form bridge to the
parent gallery entry is no longer left implicit.

The k-direction recurrence
  `qtBinom q t N (k+1) = qtBinom q t N k · (1 - q^(N-k) t^k) / (1 - q^(k+1) t^k)`
(S6 PREP §0) is the foundation; specializing `t = 1` and using the new
CommRing multiplicative q-Pascal closes the gap to the parent's q-binomial.

## What this file still does NOT contain

* No **positive** `at_one_one` limit theorem for `k ≥ 1` (i.e., recovering the
  classical `Nat.multichoose`). The S4 ACT records the **negative** value (= 0)
  under `Field R`; Section XI (S8 ACT) upgrades this to a *sharp inequality*
  proving the naive substitution genuinely differs from the classical value for
  every `k ≥ 1` (`n ≥ 1`, char 0), so the positive form for `k ≥ 1` provably
  requires `RatFunc.eval` (Path C, S5 PREP) — out of scope for this iteration.
  (The `k = 0` column *is* recovered positively, in `qtMultichoose_at_one_one_zero`.)
* No Pascal-style recurrence (S6 PREP falsified it; the product formula
  factorises along `k`, not Pascal's two-direction).
* No Macdonald-polynomial principal-specialization axiom (optional S6 step).

## PREP cascade context

After S1 OBSERVE (PR #18327, 2026-05-12), five doc-only PREPs landed
without a Lean file (S2 PREP #18382, S3 PREP #18558, S4 PREP #18616,
S5 PREP #18639, S6 PREP #18734), then S2 ACT shipped the skeleton
(#18955), S3-α partial (commit d86b78e5646), and S3 ACT (PR #21322).
This iteration discharges S4 ACT.

**S5b ACT (researcher-1, 2026-06-05, this iteration)**: four direct
bridge lemmas connecting the polynomial sub-lattice's `k ≤ 1` slice
to the parent's `qBinom` / `qMultichoose` (not only `qNumber`):
* `qtBinom_zero_right_eq_qBinom` (unconditional) — `k = 0`, both = 1.
* `qtMultichoose_zero_right_eq_qMultichoose` (unconditional) — corollary.
* `qtBinom_one_right_eq_qBinom` (under `1 - q ≠ 0`) — `k = 1`,
  composes `qtBinom_one_right_eq_qNumber` (S5 ACT) with the parent's
  `qBinom_one_right` (`qBinom q N 1 = qNumber q N`).
* `qtMultichoose_one_right_eq_qMultichoose` (under `1 - q ≠ 0`) — headline,
  the direct `qMultichoose`-form bridge at `k = 1`.

This closes the bridge chain: the polynomial sub-lattice points at
`k = 0` and `k = 1` are now equated **directly** to the parent gallery
entry's polynomial objects (`qBinom`/`qMultichoose`), not only to the
underlying `qNumber`. Gallery integration (S7) can now quote the
parent's named objects rather than re-deriving them via `qNumber`.

**S5c ACT (researcher-1, 2026-06-05, this iteration)**: extends the
direct-bridge chain to cover the **interior** polynomial-sub-lattice
point `(n, k) = (2, 2)`:
* `qtMultichoose_two_two_eq_qMultichoose` (under the two S4 ACT Path A
  guards `1 - q^2 t ≠ 0` and `1 - q ≠ 0`) — composes
  `qtMultichoose_two_two_eq_qNumber` (S5 ACT) with the parent's
  `qMultichoose_two_left q 2 : qMultichoose q 2 2 = qNumber q 3`.

With S5c ACT, **every point** in the polynomial sub-lattice
`{k ≤ 1} ∪ {(2, 2)}` is now formally equated to a parent-side named
object (`qBinom` or `qMultichoose`), closing the bridge chain in full.

## Status

* Axioms: 0
* Sorries: 0
* Theorems: 20 (2 simp boundary, 1 single-factor evaluation, 1 multichoose
  reduction, 1 unconditional k-direction recurrence, 2 S3 ACT
  specialization theorems, 3 S4 ACT polynomial-sub-lattice / 0-trap
  theorems, 1 S6 ACT ratio-form corollary, 3 S5 ACT polynomial-form
  bridges to `qNumber`, 4 S5b ACT direct bridges to `qBinom`/`qMultichoose`,
  1 S5c ACT (2, 2) interior bridge to `qMultichoose`, 2 S8 ACT trap-sharpness
  theorems — positive `k = 0` recovery + `k ≥ 1` necessity-of-Path-C inequality)
* Lemmas (private): 1 (`qBinom_mult_recur`, CommRing multiplicative q-Pascal)

## Build status

Build pending (Docker daemon required per project convention; per CLAUDE.md
never invoke `lake build` directly). The S4 ACT additions use only standard
Mathlib tactics: `Finset.prod_range_succ'`, `div_self`, `pow_one`, `simp`
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

-- ============================================================
-- SECTION VI: S4 ACT — Polynomial sub-lattice + Field 0/0 trap
-- ============================================================

/-- **Polynomial sub-lattice (S3 PREP characterization)**: the case
    `(n, k) = (2, 2)` is the unique "interior" point (both `n ≥ 2` and
    `k ≥ 2`) at which `qtMultichoose q t n k` is independent of `t` as a
    rational function in `ℚ(q, t)`.

    Concretely: `qtMultichoose q t 2 2 = (1 - q^3) / (1 - q)`, which equals
    `1 + q + q^2 = qNumber q 3` whenever `1 - q ≠ 0` (the latter not
    required for the equality of the rational expressions stated here).
    The Path A guard `1 - q^2 t ≠ 0` keeps the cancelling factor's
    denominator nonzero.

    Mechanism: in the product
      `qtBinom q t 3 2 = ∏ i ∈ range 2, (1 - q^(3 - i) t^i) / (1 - q^(i + 1) t^i)`,
    the `i = 1` factor has numerator `1 - q^2 t` and denominator `1 - q^2 t`
    (because `3 - 1 = 2 = 1 + 1`), so it cancels to `1`. The `i = 0`
    factor is `(1 - q^3) / (1 - q)` (t-free since `t^0 = 1`).

    For `(n, k)` outside `{k ≤ 1} ∪ {(2, 2)}`, no such cancellation occurs;
    the S3 PREP rationality analysis proves this is the full polynomial
    sub-lattice of `qtBinom` over `ℚ(q, t)`. -/
theorem qtMultichoose_two_two (q t : R) (htq : (1 : R) - q ^ 2 * t ≠ 0) :
    qtMultichoose q t 2 2 = (1 - q ^ 3) / (1 - q) := by
  have h_unfold : qtMultichoose q t 2 2 = qtBinom q t 3 (1 + 1) := rfl
  rw [h_unfold, qtBinom_succ, qtBinom_one_right]
  simp only [show (3 - 1 : ℕ) = 2 from rfl, show (1 + 1 : ℕ) = 2 from rfl, pow_one]
  rw [div_self htq, mul_one]

/-- **Field R 0/0 trap (S4 PREP F1), formalised**: under Lean's `Field R`
    convention `(0 : R) / 0 = 0`, the joint specialization `q = t = 1` of
    the Macdonald (q,t)-binomial collapses to **zero** for every positive
    column-count `k + 1`:
      `qtBinom (1 : R) (1 : R) N (k + 1) = 0`.

    Mechanism: the `i = 0` factor `(1 - 1^(N - 0) * 1^0) / (1 - 1^(0 + 1) * 1^0)`
    is exactly `0 / 0 = 0` (every `1^_` is `1`, every `1 - 1` is `0`).
    A single zero factor zeros the whole product (`Finset.prod_range_succ'`
    extracts that factor and `simp` closes via `zero_div` and `mul_zero`).

    This formalises **why** the Path A non-degeneracy hypothesis
    `q^(j + 1) ≠ 1` is *mandatory* in `qtBinom_at_t_eq_one`: dropping it
    re-admits `q = 1`, and combined with `t = 1` the rational substitution
    is no longer the classical limit but the `Field R` 0/0 collapse. The
    classical recovery `qtMultichoose 1 1 n k = Nat.multichoose n k`
    requires either Path C (`RatFunc.eval`, S5 PREP) or an iterated-limit
    construction — both out of scope for this ACT. -/
theorem qtBinom_at_one_one_eq_zero (N k : ℕ) :
    qtBinom (1 : R) (1 : R) N (k + 1) = 0 := by
  unfold qtBinom
  rw [Finset.prod_range_succ']
  simp

/-- **Corollary of `qtBinom_at_one_one_eq_zero`**: at `q = t = 1`, the
    (q,t)-multichoose coefficient is zero for every `k + 1 ≥ 1` under
    Path A `Field R` semantics.

    `qtMultichoose 1 1 n (k + 1) = qtBinom 1 1 (n + (k + 1) - 1) (k + 1)
                                 = 0`
    by the parent theorem. This is the "negative S4/S5" statement that
    formalises the Field 0/0 trap at the `qtMultichoose` level. -/
theorem qtMultichoose_at_one_one_eq_zero (n k : ℕ) :
    qtMultichoose (1 : R) (1 : R) n (k + 1) = 0 := by
  unfold qtMultichoose
  exact qtBinom_at_one_one_eq_zero (n + (k + 1) - 1) k

-- ============================================================
-- SECTION VII: S6 PREP §0 ratio identity — explicit corollary
-- ============================================================

/-- **k-direction telescoping ratio identity** (S6 PREP §0, recommendation 5):

    When `qtBinom q t N k ≠ 0`, the ratio of consecutive `k`-values is the
    clean rational function

        `qtBinom q t N (k+1) / qtBinom q t N k = (1 - q^(N-k) t^k) / (1 - q^(k+1) t^k)`.

    S6 PREP §0 highlighted this ratio as **the** clean rational identity
    distinguishing the k-direction recurrence from the (n, k)-shape-varying
    Pascal-style coefficients (S6 PREP §3 falsified the conjectured Pascal
    `C(q,t,n,k)` at 4 of 4 non-degenerate test points, with denominator
    depending on `(n,k)` in a non-uniform way).

    This is an immediate corollary of `qtBinom_succ` via division by
    `qtBinom q t N k`; the hypothesis `h` is the standard Path A
    non-degeneracy condition (the denominator on the LHS is nonzero).

    Together with `qtBinom_succ` (the multiplicative form), this gives the
    two natural Lean-side handles on the foundational k-direction
    recurrence — the multiplicative form for substitution proofs (used in
    S3 ACT `qtBinom_at_t_eq_one`), and the ratio form for telescoping /
    chain proofs (recommended foundation for any future S4/S5 work
    where the multiplicative form's residual `qtBinom q t N k` factor
    needs to be eliminated). -/
theorem qtBinom_succ_div (q t : R) (N k : ℕ)
    (h : qtBinom q t N k ≠ 0) :
    qtBinom q t N (k + 1) / qtBinom q t N k =
      (1 - q ^ (N - k) * t ^ k) / (1 - q ^ (k + 1) * t ^ k) := by
  rw [qtBinom_succ, mul_div_cancel_left₀ _ h]

-- ============================================================
-- SECTION VIII: S5 ACT — Polynomial-form bridges to the parent's qNumber
-- ============================================================

/-- **Polynomial form of `qtBinom_one_right`**: the rational Macdonald
    expression `(1 - q^N) / (1 - q)` at `k = 1` equals the parent's
    polynomial `qNumber q N = 1 + q + q² + ⋯ + q^(N-1)`, on the open
    dense set `1 - q ≠ 0` (the only Path A non-degeneracy at `k = 1`).

    This is the polynomial-form bridge for the `k = 1` slice of the S3
    PREP polynomial sub-lattice `{k ≤ 1} ∪ {(2, 2)}`: the rational form
    `(1 - q^N) / (1 - q)` (S2 ACT `qtBinom_one_right`) is the rational
    presentation, and `qNumber q N` is the polynomial presentation —
    they agree off `q = 1`.

    Proof: rewrite by `qtBinom_one_right`, then use the parent's
    `qNumber_geometric` identity `(q - 1) · qNumber q N = q^N - 1`
    (which gives `(1 - q) · qNumber q N = 1 - q^N`) and cancel. -/
theorem qtBinom_one_right_eq_qNumber (q t : R) (N : ℕ)
    (hq : (1 - q : R) ≠ 0) :
    qtBinom q t N 1 = qNumber q N := by
  rw [qtBinom_one_right]
  have h_geom : (1 - q ^ N : R) = (1 - q) * qNumber q N := by
    have hg := qNumber_geometric q N
    linear_combination hg
  rw [h_geom, mul_div_cancel_left₀ _ hq]

/-- **Polynomial form of `qtMultichoose_one_right`**: at `k = 1`, the
    (q,t)-multichoose coefficient equals the parent's `qNumber q n`
    provided `1 - q ≠ 0`. Direct corollary of
    `qtBinom_one_right_eq_qNumber` via the `n + 1 - 1 = n` index shift. -/
theorem qtMultichoose_one_right_eq_qNumber (q t : R) (n : ℕ)
    (hq : (1 - q : R) ≠ 0) :
    qtMultichoose q t n 1 = qNumber q n := by
  simp only [qtMultichoose, show n + 1 - 1 = n from by omega]
  exact qtBinom_one_right_eq_qNumber q t n hq

/-- **Polynomial form of `qtMultichoose_two_two`**: the unique non-trivial
    polynomial-sub-lattice point `(n, k) = (2, 2)` evaluates to the
    parent's `qNumber q 3 = 1 + q + q²` under the two Path A guards
    `1 - q² t ≠ 0` (cancels the `i = 1` Macdonald factor) and
    `1 - q ≠ 0` (cancels the `i = 0` denominator).

    This completes the polynomial-form bridge for the S3 PREP polynomial
    sub-lattice `{k ≤ 1} ∪ {(2, 2)}`: every point is now formally equated
    to a `qNumber` expression from the parent, making the rational
    Macdonald presentation transparently polynomial on its sub-lattice.

    Proof: rewrite by `qtMultichoose_two_two`, then use
    `qNumber_geometric` at `n = 3` to convert `(1 - q^3) / (1 - q)`
    to `qNumber q 3` via the same cancellation pattern as
    `qtBinom_one_right_eq_qNumber`. -/
theorem qtMultichoose_two_two_eq_qNumber (q t : R)
    (htq : (1 : R) - q ^ 2 * t ≠ 0) (hq : (1 - q : R) ≠ 0) :
    qtMultichoose q t 2 2 = qNumber q 3 := by
  rw [qtMultichoose_two_two q t htq]
  have h_geom : (1 - q ^ 3 : R) = (1 - q) * qNumber q 3 := by
    have hg := qNumber_geometric q 3
    linear_combination hg
  rw [h_geom, mul_div_cancel_left₀ _ hq]

-- ============================================================
-- SECTION IX: S5b ACT — Direct bridges to the parent's qBinom / qMultichoose
-- ============================================================

/-- **k = 0 trivial bridge to `qBinom`**: `qtBinom q t N 0 = qBinom q N 0 = 1`.
    Both sides are the empty product / boundary; no hypothesis needed. -/
theorem qtBinom_zero_right_eq_qBinom (q t : R) (N : ℕ) :
    qtBinom q t N 0 = qBinom q N 0 := by
  rw [qtBinom_zero_right, qBinom_zero_right]

/-- **k = 0 trivial bridge to `qMultichoose`**: `qtMultichoose q t n 0 = qMultichoose q n 0 = 1`.
    Both sides are 1 by their respective boundary lemmas. -/
theorem qtMultichoose_zero_right_eq_qMultichoose (q t : R) (n : ℕ) :
    qtMultichoose q t n 0 = qMultichoose q n 0 := by
  rw [qtMultichoose_zero_right, qMultichoose_zero_right]

/-- **k = 1 bridge to `qBinom`**: at `k = 1`, the rational Macdonald form
    `qtBinom q t N 1` equals the parent's `qBinom q N 1` provided
    `1 - q ≠ 0`. Composes `qtBinom_one_right_eq_qNumber` with the parent's
    `qBinom_one_right : qBinom q N 1 = qNumber q N`. -/
theorem qtBinom_one_right_eq_qBinom (q t : R) (N : ℕ)
    (hq : (1 - q : R) ≠ 0) :
    qtBinom q t N 1 = qBinom q N 1 := by
  rw [qtBinom_one_right_eq_qNumber q t N hq, ← qBinom_one_right]

/-- **k = 1 bridge to `qMultichoose`** (headline S5b ACT): at `k = 1`, the
    (q,t)-multichoose coefficient equals the parent's `qMultichoose q n 1`
    provided `1 - q ≠ 0`. Direct corollary of
    `qtMultichoose_one_right_eq_qNumber` + the parent's
    `qMultichoose_one_right : qMultichoose q n 1 = qNumber q n`. -/
theorem qtMultichoose_one_right_eq_qMultichoose (q t : R) (n : ℕ)
    (hq : (1 - q : R) ≠ 0) :
    qtMultichoose q t n 1 = qMultichoose q n 1 := by
  rw [qtMultichoose_one_right_eq_qNumber q t n hq, ← qMultichoose_one_right]

-- ============================================================
-- SECTION X: S5c ACT — (2, 2) interior bridge to qMultichoose
-- ============================================================

/-- **`(n, k) = (2, 2)` bridge to `qMultichoose`** (headline S5c ACT): at
    the unique non-trivial polynomial-sub-lattice interior point, the
    (q,t)-multichoose coefficient equals the parent's `qMultichoose q 2 2`
    provided the two S4 ACT Path A guards `1 - q^2 t ≠ 0` and `1 - q ≠ 0`.

    Composes the S5 ACT `qtMultichoose_two_two_eq_qNumber` with the parent's
    `qMultichoose_two_left q 2 : qMultichoose q 2 2 = qNumber q 3` (where the
    `k = 2` instance of `qMultichoose_two_left q k = qNumber q (k + 1)`
    evaluates the index to `qNumber q 3`).

    Closes the bridge chain for the **entire** polynomial sub-lattice
    `{k ≤ 1} ∪ {(2, 2)}`: every point is now equated directly to a
    parent-side named object (`qBinom` / `qMultichoose`), not only to the
    underlying `qNumber`. Gallery integration (S7) can now quote
    `qMultichoose q 2 2` as the canonical reference for the (2, 2) value. -/
theorem qtMultichoose_two_two_eq_qMultichoose (q t : R)
    (htq : (1 : R) - q ^ 2 * t ≠ 0) (hq : (1 - q : R) ≠ 0) :
    qtMultichoose q t 2 2 = qMultichoose q 2 2 := by
  rw [qtMultichoose_two_two_eq_qNumber q t htq hq, ← qMultichoose_two_left q 2]

-- ============================================================
-- SECTION XI: Sharpness of the Field 0/0 trap — Path C is necessary
-- ============================================================

/-- **Positive `at_one_one` recovery at the `k = 0` boundary.** The naive
    Field-`R` substitution `q = t = 1` returns the *correct* classical value
    `Nat.multichoose n 0 = 1` here, because the `k = 0` column is the empty
    product (`= 1`), with no `0/0` factor to collapse.

    This is the **only** column where the direct substitution agrees with the
    classical multichoose; `qtMultichoose_at_one_one_ne_classical` below shows
    every `k ≥ 1` column disagrees (in characteristic zero). Together they pin
    the exact boundary `{k = 0}` of Field-`R` recoverability, motivating the
    Path C (`RatFunc.eval`) migration for the `k ≥ 1` columns. -/
theorem qtMultichoose_at_one_one_zero (n : ℕ) :
    qtMultichoose (1 : R) (1 : R) n 0 = (Nat.multichoose n 0 : R) := by
  rw [qtMultichoose_zero_right, Nat.multichoose_zero_right, Nat.cast_one]

/-- **Sharpness of the Field 0/0 trap (necessity of Path C).** In any
    characteristic-zero field, for `n ≥ 1` and *every* column `k + 1 ≥ 1`, the
    naive substitution `q = t = 1` returns `0` (the `Field R` `0/0` collapse,
    `qtBinom_at_one_one_eq_zero`), which is **strictly different** from the
    classical value `Nat.multichoose n (k + 1)` — the latter is nonzero because
    `Nat.multichoose n (k+1) = (n + k).choose (k + 1) > 0` for `n ≥ 1`.

    Hence the positive `at_one_one` recovery `qtMultichoose 1 1 n k =
    Nat.multichoose n k` is **provably unattainable** by direct Field-`R`
    substitution for any `k ≥ 1`: the lowest-terms reduction of `RatFunc.eval`
    (Path C) is genuinely required, not merely a convenience. This upgrades the
    one-directional `qtMultichoose_at_one_one_eq_zero` (which records the value
    `0`) to a sharp *inequality* against the intended classical target. -/
theorem qtMultichoose_at_one_one_ne_classical [CharZero R] (n k : ℕ)
    (hn : 1 ≤ n) :
    qtMultichoose (1 : R) (1 : R) n (k + 1) ≠ (Nat.multichoose n (k + 1) : R) := by
  have hpos : 0 < Nat.multichoose n (k + 1) := by
    rw [Nat.multichoose_eq]
    exact Nat.choose_pos (by omega)
  have hne : (Nat.multichoose n (k + 1) : R) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [qtMultichoose_at_one_one_eq_zero]
  exact hne.symm

end QtMultichooseCoefficients
