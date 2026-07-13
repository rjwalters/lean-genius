/-
# A q-analog of the Chung-Feller Theorem

## Research Problem: ballot-problem-oq-01-oq-04-oq-02

The classical Chung-Feller theorem (proved in `BallotProblemOQ01OQ04.lean` as
`ChungFeller.chung_feller_uniform`) says that, among the `C(2n,n)` balanced
lattice paths from `(0,0)` to `(2n,0)`, the number having exactly `k` upsteps
above the x-axis is the **same** for every `k ∈ {0,…,n}`.

This file records the natural *q-analog* / generating-function packaging of that
statement.  Introduce a formal variable `q` that tracks the Chung-Feller
statistic `upstepsAboveAxis` (the "type" of a path — the number of upsteps taken
while at non-negative height).  The **type generating polynomial**

  `Z_n(q) := ∑_{k=0}^{n} |{balanced paths of type k}| · q^k`

then *factors* as

  `Z_n(q) = N · (1 + q + q² + ⋯ + q^n) = N · [n+1]_q`,

where `N = |{balanced paths of type 0}|` is the common per-type count and
`[n+1]_q` is the `q`-integer.  Setting `q = 1` collapses this to the plain count
`Z_n(1) = (n+1)·N`, recovering that the balanced paths split into `n+1` equinumerous
type classes.

## Status

Fully machine-checked: **0 sorries, 0 axioms**.  The result is a corollary of the
verified uniform-distribution theorem `ChungFeller.chung_feller_uniform`,
reorganized as a `q`-generating-function identity.  The identity is stated over
an arbitrary commutative ring `R` for a generic element `q`, and specialized to
`Polynomial ℤ` with `q = X` to obtain the literal q-analog polynomial.

## References

- Chung, K.L. and Feller, W. (1949). On fluctuations in coin-tossing.
- MacMahon, P.A. Combinatory Analysis (q-analogs / q-integers `[m]_q`).
-/

import Proofs.BallotProblemOQ01OQ04

namespace ChungFellerQAnalog

open ChungFeller

/-- The number of balanced paths of length `2n` and Chung-Feller type `k`
    (i.e. with exactly `k` upsteps above the x-axis). -/
noncomputable def typeCount (n k : ℕ) : ℕ := Set.ncard (balancedPathsOfType n k)

/-- The `q`-integer `[m]_q = 1 + q + q² + ⋯ + q^{m-1}`. -/
def qNat {R : Type*} [CommRing R] (q : R) (m : ℕ) : R :=
  ∑ k ∈ Finset.range m, q ^ k

/-- **Chung-Feller uniformity in generating-function form.**

    Every type class `k ∈ {0,…,n}` has the same size as the class `k = 0`.
    This is a direct restatement of `chung_feller_uniform`, packaged for the
    `q`-analog below. -/
theorem typeCount_eq_zero (n k : ℕ) (hk : k ≤ n) :
    typeCount n k = typeCount n 0 := by
  unfold typeCount
  exact chung_feller_uniform n k 0 hk (Nat.zero_le n)

/-- **q-analog of the Chung-Feller theorem.**

    The type generating polynomial factors as the common per-type count times
    the `q`-integer `[n+1]_q`:

      `∑_{k=0}^{n} typeCount n k · q^k = typeCount n 0 · [n+1]_q`.

    Stated over an arbitrary commutative ring `R` and a generic element `q`;
    take `R = Polynomial ℤ`, `q = X` for the literal polynomial identity
    (`chung_feller_q_analog_poly`). -/
theorem chung_feller_q_analog {R : Type*} [CommRing R] (n : ℕ) (q : R) :
    ∑ k ∈ Finset.range (n + 1), (typeCount n k : R) * q ^ k
      = (typeCount n 0 : R) * qNat q (n + 1) := by
  rw [qNat, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [typeCount_eq_zero n k (by omega)]

/-- The literal q-analog polynomial identity in `Polynomial ℤ`, obtained by
    specializing `q = X`. -/
theorem chung_feller_q_analog_poly (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        (typeCount n k : Polynomial ℤ) * Polynomial.X ^ k
      = (typeCount n 0 : Polynomial ℤ) * qNat Polynomial.X (n + 1) :=
  chung_feller_q_analog n Polynomial.X

/-- Evaluating the `q`-integer `[m]_q` at `q = 1` gives `m`. -/
@[simp] theorem qNat_one {R : Type*} [CommRing R] (m : ℕ) :
    qNat (1 : R) m = (m : R) := by
  simp [qNat]

/-- **Specialization at `q = 1`: the total path count.**

    Collapsing the q-analog at `q = 1` recovers that the balanced paths of
    length `2n` split into `n+1` type classes of equal size:

      `∑_{k=0}^{n} typeCount n k = (n+1) · typeCount n 0`. -/
theorem chung_feller_total (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), typeCount n k = (n + 1) * typeCount n 0 := by
  rw [Finset.sum_congr rfl fun k hk =>
        typeCount_eq_zero n k (by rw [Finset.mem_range] at hk; omega)]
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end ChungFellerQAnalog
