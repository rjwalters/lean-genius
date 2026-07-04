/-
# Chebyshev–PNT Bridge OQ-03·OQ-01: The elementary θ ↔ π reduction

The Prime Number Theorem, `π(x) ~ x / log x`, is equivalent to its
Chebyshev-`θ` form, `θ(x) ~ x`, where

    θ(x) = ∑_{p ≤ x, p prime} log p .

The parent bridge (`ChebyshevPNTBridge.lean` and its open questions) proves the
*order of magnitude* `π(x) = Θ(x / log x)`; the sharp asymptotic constant `1`
(the actual PNT limit) needs the deep analytic input — either ζ non-vanishing
on `Re s = 1` (Wiener–Ikehara) or the Selberg symmetry formula — and is out of
reach on the pinned Mathlib.  This file isolates the **purely elementary half**:
the two-sided sandwich that transfers the asymptotic between `θ` and `π·log`,
so that `θ(x) ~ x ⟺ π(x) ~ x / log x`.  No analysis beyond monotonicity of
`log` and finite-sum manipulation is used — everything here is `0 sorry`,
`0 axiom`.

The two inequalities, valid for `2 ≤ y ≤ n`:

* **Upper** (`chebyshevTheta_le_primeCounting_mul_log`):

      θ(n) ≤ π(n) · log n .

  Each of the `π(n)` primes `p ≤ n` contributes `log p ≤ log n`.

* **Lower / threshold** (`primeCounting_le_add_chebyshevTheta_div_log`):

      π(n) ≤ y + θ(n) / log y .

  Only the primes `p ≤ y` (at most `y` of them) fail the bound `log y ≤ log p`;
  the rest each contribute at least `log y` to `θ(n)`, so their count
  `π(n) − π(y)` is `≤ θ(n) / log y`.

Together (`chebyshev_theta_primeCounting_sandwich`) they pin `π(n)·log n` to
`θ(n)` up to `O(y log n)` error, the standard partial-summation-free bridge.
Choosing e.g. `y = ⌊n / (log n)²⌋` collapses the error and yields the stated
equivalence of the normalised limits; that final `Tendsto` bookkeeping is left
to a consumer — the mathematical content is exactly these two inequalities.

**Status**: the elementary reduction is COMPLETE (0 sorries, 0 axioms).  The
deep PNT limit itself remains BLOCKED (needs Wiener–Ikehara / Selberg).
-/

import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Proofs.ChebyshevThetaFourPow
import Proofs.ChebyshevPNTBridge
import Proofs.ChebyshevPNTBridgeOQ05

open Finset
open ChebyshevThetaBound

namespace ChebyshevPNTBridgeOQ03OQ01

/-- `π(n)` counts exactly the primes in `range (n+1)`. -/
theorem primeCounting_eq_card (n : ℕ) :
    Nat.primeCounting n = (filter Nat.Prime (range (n + 1))).card := by
  unfold Nat.primeCounting Nat.primeCounting'
  exact Nat.count_eq_card_filter_range Nat.Prime (n + 1)

/-- **Upper half of the bridge.**  `θ(n) ≤ π(n) · log n`: each of the `π(n)`
primes `p ≤ n` contributes `log p ≤ log n` to `θ(n)`. -/
theorem chebyshevTheta_le_primeCounting_mul_log (n : ℕ) :
    chebyshevTheta n ≤ (Nat.primeCounting n : ℝ) * Real.log n := by
  rw [chebyshevTheta, primeCounting_eq_card]
  calc ∑ p ∈ filter (fun p => Nat.Prime p) (range (n + 1)), Real.log p
      ≤ ∑ _p ∈ filter (fun p => Nat.Prime p) (range (n + 1)), Real.log n := by
        apply Finset.sum_le_sum
        intro p hp
        rw [mem_filter, mem_range] at hp
        have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
        have hple : (p : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp hp.1
        exact Real.log_le_log hppos hple
    _ = ((filter (fun p => Nat.Prime p) (range (n + 1))).card : ℝ) * Real.log n := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The set of primes in `(y, n]`, i.e. `y < p ≤ n`. -/
private def tailPrimes (y n : ℕ) : Finset ℕ :=
  filter Nat.Prime (Ico (y + 1) (n + 1))

/-- The tail `∑_{y < p ≤ n} log p` is bounded above by `θ(n)`, since it is a
sub-sum of nonnegative terms. -/
theorem tail_sum_le_chebyshevTheta (y n : ℕ) :
    ∑ p ∈ tailPrimes y n, Real.log p ≤ chebyshevTheta n := by
  rw [chebyshevTheta]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [tailPrimes, mem_filter, mem_Ico] at hp
    rw [mem_filter, mem_range]
    exact ⟨by omega, hp.2⟩
  · intro p hp _
    rw [mem_filter, mem_range] at hp
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.2.one_lt.le
    exact Real.log_nonneg this

/-- **Lower / threshold half of the bridge.**  For `2 ≤ y ≤ n`,

    π(n) ≤ y + θ(n) / log y .

The primes `p > y` each contribute at least `log y` to `θ(n)`, so there are at
most `θ(n) / log y` of them; the remaining primes number `π(y) ≤ y`. -/
theorem primeCounting_le_add_chebyshevTheta_div_log
    (y n : ℕ) (hy : 2 ≤ y) (hyn : y ≤ n) :
    (Nat.primeCounting n : ℝ) ≤ (y : ℝ) + chebyshevTheta n / Real.log y := by
  have hlogy_pos : 0 < Real.log y := by
    apply Real.log_pos
    exact_mod_cast hy
  -- Tail count = π(n) - π(y), and this equals |tailPrimes y n|.
  have hcard : (tailPrimes y n).card = Nat.primeCounting n - Nat.primeCounting y := by
    have := ChebyshevPNTBridge.numPrimesAbove_eq y n hyn
    rw [ChebyshevPNTBridge.numPrimesAbove] at this
    rw [tailPrimes]; exact this
  have hmono : Nat.primeCounting y ≤ Nat.primeCounting n :=
    ChebyshevPNTBridgeOQ05.primeCounting_mono hyn
  -- π(n) = π(y) + |tail|  (as reals)
  have hsplit : (Nat.primeCounting n : ℝ)
      = (Nat.primeCounting y : ℝ) + ((tailPrimes y n).card : ℝ) := by
    rw [hcard]; push_cast [Nat.cast_sub hmono]; ring
  -- lower bound the tail sum: |tail| * log y ≤ ∑_{tail} log p ≤ θ(n)
  have hlb : ((tailPrimes y n).card : ℝ) * Real.log y
      ≤ ∑ p ∈ tailPrimes y n, Real.log p := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p hp
    rw [tailPrimes, mem_filter, mem_Ico] at hp
    have hypos : (0 : ℝ) < (y : ℝ) := by exact_mod_cast (by omega : 0 < y)
    have hyp : (y : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : y ≤ p)
    exact Real.log_le_log hypos hyp
  have htail : ((tailPrimes y n).card : ℝ) * Real.log y ≤ chebyshevTheta n :=
    le_trans hlb (tail_sum_le_chebyshevTheta y n)
  -- divide: |tail| ≤ θ(n) / log y
  have hdiv : ((tailPrimes y n).card : ℝ) ≤ chebyshevTheta n / Real.log y := by
    rw [le_div_iff₀ hlogy_pos]; exact htail
  -- π(y) ≤ y
  have hpy : (Nat.primeCounting y : ℝ) ≤ (y : ℝ) := by
    exact_mod_cast ChebyshevPNTBridge.primeCounting_le y
  rw [hsplit]
  have := add_le_add hpy hdiv
  linarith

/-- **The elementary θ ↔ π sandwich.**  For `2 ≤ y ≤ n`,

    θ(n) ≤ π(n) · log n     and     π(n) ≤ y + θ(n) / log y .

This is the analysis-free reduction underlying `θ(x) ~ x ⟺ π(x) ~ x/log x`. -/
theorem chebyshev_theta_primeCounting_sandwich
    (y n : ℕ) (hy : 2 ≤ y) (hyn : y ≤ n) :
    chebyshevTheta n ≤ (Nat.primeCounting n : ℝ) * Real.log n
      ∧ (Nat.primeCounting n : ℝ) ≤ (y : ℝ) + chebyshevTheta n / Real.log y :=
  ⟨chebyshevTheta_le_primeCounting_mul_log n,
   primeCounting_le_add_chebyshevTheta_div_log y n hy hyn⟩

end ChebyshevPNTBridgeOQ03OQ01
