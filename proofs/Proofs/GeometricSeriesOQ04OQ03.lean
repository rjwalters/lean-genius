import Proofs.GeometricSeriesOQ04
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-
# Gaussian (q-)Binomial Coefficients: q-Pascal, boundaries, and the classical limit

## What This Proves

Building on the quantum integer `[n]_q = ∑_{i<n} q^i` of the parent entry
(`GeometricSeriesOQ04.lean`), this file develops the **Gaussian (q-)binomial
coefficient** `qBinom q n k = [n choose k]_q` over an arbitrary commutative ring.

The coefficient is defined *by* the **q-Pascal recurrence**

  [n+1 choose k+1]_q  =  [n choose k]_q  +  q^{k+1} · [n choose k+1]_q,

so the recurrence is definitional (`rfl`).  On top of it we prove the structural
laws that characterise the Gaussian binomial:

1. **Boundary conditions**
   `qBinom_zero_right : [n choose 0]_q = 1`,
   `qBinom_self : [n choose n]_q = 1`,
   `qBinom_eq_zero_of_lt : n < k → [n choose k]_q = 0`.

2. **Bridge to the quantum integer** `qBinom_one_right : [n choose 1]_q = [n]_q`,
   which reuses the parent's `qNat` and the "prepend" recurrence `qNat_succ'`.

3. **Classical limit / counting interpretation** `qBinom_at_one`:
   at `q = 1` the Gaussian binomial degenerates to the ordinary binomial
   coefficient `[n choose k]_1 = C(n, k)`, which literally counts the
   `k`-element subsets of an `n`-set.  This is the `q = 1` shadow of
   subspace-counting over `𝔽_q`, and the honest "counting interpretation"
   deliverable for this entry.

An illustrative expansion `qBinom q 4 2 = 1 + q + 2q² + q³ + q⁴` is checked at
the end, exhibiting the Gaussian binomial as a genuine polynomial in `q` whose
`q = 1` value is `C(4,2) = 6`.

## The q-binomial theorem (Gauss / Rothe)

The headline consequence is now **formalized** at the end of this file
(`qBinomial_theorem`):

  `∏_{i<n} (1 + q^i · x) = ∑_{k≤n} q^{C(k,2)} · [n choose k]_q · x^k`.

It follows from the recurrence by induction on `n` (peel the first factor with
`Finset.prod_range_succ'`, re-substitute `x ↦ q·x`, match coefficients via the
functional recurrence `qbinomSum_succ`, which uses only q-Pascal I and the
identity `C(k+1,2) = C(k,2) + k`).  The **box-partition generating function**
`∑_{λ ⊆ (n-k)^k} q^{|λ|}` satisfies the same recurrence and is left as follow-up.

## Why Mathlib Doesn't Already Have This

Mathlib has `Nat.choose` and the geometric sum `geom_sum_mul`, but **no** named
Gaussian binomial, no q-Pascal recurrence and no q-binomial theorem (the
`Pochhammer` file only *mentions* q-binomials in a docstring).  Everything here
is bespoke.

## Honesty Note

These are standard, textbook q-analog identities (Andrews, *Theory of
Partitions*; Kac–Cheung, *Quantum Calculus*, Ch. 5–7).  The contribution is a
faithful, fully machine-checked Lean formalization of a structure Mathlib lacks,
not a new mathematical result.  All proofs are 0-axiom (only Lean's foundational
axioms).
-/

open Finset
open QuantumInteger

namespace GaussianBinomial

variable {R : Type*} [CommRing R]

/-- The **Gaussian (q-)binomial coefficient** `[n choose k]_q`, defined by the
q-Pascal recurrence.  At `q = 1` it degenerates to the ordinary `Nat.choose`. -/
def qBinom (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

@[simp] theorem qBinom_zero_right (q : R) (n : ℕ) : qBinom q n 0 = 1 := by
  cases n <;> rfl

@[simp] theorem qBinom_zero_succ (q : R) (k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/-- **q-Pascal recurrence** (definitional). -/
theorem qBinom_succ_succ (q : R) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- Above the diagonal the Gaussian binomial vanishes. -/
theorem qBinom_eq_zero_of_lt (q : R) : ∀ (n k : ℕ), n < k → qBinom q n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
      have h' : n < k := by omega
      rw [qBinom_succ_succ, qBinom_eq_zero_of_lt q n k h',
          qBinom_eq_zero_of_lt q n (k + 1) (by omega)]
      ring

/-- On the diagonal the Gaussian binomial is `1`. -/
@[simp] theorem qBinom_self (q : R) : ∀ (n : ℕ), qBinom q n n = 1
  | 0 => rfl
  | n + 1 => by
      rw [qBinom_succ_succ, qBinom_self q n, qBinom_eq_zero_of_lt q n (n + 1) (by omega)]
      ring

/-- Prepend form of the quantum-integer recurrence: `[n+1]_q = q·[n]_q + 1`
(peeling the *first* term of the geometric sum rather than the last). -/
theorem qNat_succ' (q : R) (n : ℕ) : qNat q (n + 1) = q * qNat q n + 1 := by
  have h : qNat q (n + 1) = (∑ i ∈ Finset.range n, q ^ (i + 1)) + q ^ 0 :=
    Finset.sum_range_succ' (fun i => q ^ i) n
  rw [h, pow_zero]
  simp only [qNat, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => by rw [pow_succ, mul_comm])

/-- **Bridge to the quantum integer**: `[n choose 1]_q = [n]_q`. -/
theorem qBinom_one_right (q : R) : ∀ (n : ℕ), qBinom q n 1 = qNat q n
  | 0 => by rw [qNat_zero]; rfl
  | n + 1 => by
      have hrec : qBinom q (n + 1) 1 = qBinom q n 0 + q ^ 1 * qBinom q n 1 :=
        qBinom_succ_succ q n 0
      rw [hrec, qBinom_zero_right, qBinom_one_right q n, pow_one, qNat_succ']
      ring

/-- **Classical limit / counting interpretation**: at `q = 1` the Gaussian
binomial is the ordinary binomial coefficient, which counts `k`-subsets of an
`n`-set. -/
theorem qBinom_at_one : ∀ (n k : ℕ), qBinom (1 : R) n k = (n.choose k : R)
  | _, 0 => by rw [qBinom_zero_right, Nat.choose_zero_right, Nat.cast_one]
  | 0, _ + 1 => by simp
  | n + 1, k + 1 => by
      rw [qBinom_succ_succ, qBinom_at_one n k, qBinom_at_one n (k + 1),
          one_pow, one_mul, Nat.choose_succ_succ, Nat.cast_add]

/-- Illustrative expansion: `[4 choose 2]_q = 1 + q + 2q² + q³ + q⁴`, a genuine
polynomial in `q`.  Its value at `q = 1` is `1 + 1 + 2 + 1 + 1 = 6 = C(4,2)`. -/
example (q : R) : qBinom q 4 2 = 1 + q + 2 * q ^ 2 + q ^ 3 + q ^ 4 := by
  simp only [qBinom]
  ring

/-! ### The q-binomial theorem (Gauss / Rothe) -/

/-- `(k+1).choose 2 = k.choose 2 + k`, the exponent recurrence used below. -/
theorem choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  have h : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
  rw [Nat.choose_one_right] at h
  omega

/-- The weighted sum `∑_{k≤n} q^{C(k,2)} · [n choose k]_q · x^k` appearing on the
right-hand side of the q-binomial theorem. -/
def qbinomSum (q x : R) (n : ℕ) : R :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k.choose 2) * qBinom q n k * x ^ k

/-- **Functional recurrence** `S_{n+1}(x) = (1 + x) · S_n(q·x)`, proved using
only q-Pascal I (`qBinom_succ_succ`) and vanishing above the diagonal. -/
theorem qbinomSum_succ (q x : R) (n : ℕ) :
    qbinomSum q x (n + 1) = (1 + x) * qbinomSum q (q * x) n := by
  have hbody : ∀ k, q ^ ((k + 1).choose 2) * qBinom q (n + 1) (k + 1) * x ^ (k + 1)
      = x * (q ^ (k.choose 2) * qBinom q n k * (q * x) ^ k)
        + q ^ (k.choose 2 + (2 * k + 1)) * qBinom q n (k + 1) * x ^ (k + 1) := by
    intro k
    rw [choose_two_succ, qBinom_succ_succ]
    ring
  have hg : ∀ k, q ^ ((k + 1).choose 2) * qBinom q n (k + 1) * (q * x) ^ (k + 1)
      = q ^ (k.choose 2 + (2 * k + 1)) * qBinom q n (k + 1) * x ^ (k + 1) := by
    intro k
    rw [choose_two_succ]
    ring
  have hsum_g : (∑ k ∈ Finset.range (n + 1),
        q ^ (k.choose 2) * qBinom q n k * (q * x) ^ k)
      = (∑ k ∈ Finset.range n,
          q ^ (k.choose 2 + (2 * k + 1)) * qBinom q n (k + 1) * x ^ (k + 1)) + 1 := by
    rw [Finset.sum_range_succ']
    simp only [hg]
    have h0 : q ^ ((0 : ℕ).choose 2) * qBinom q n 0 * (q * x) ^ 0 = 1 := by simp
    rw [h0]
  have hsum_h : (∑ k ∈ Finset.range (n + 1),
        q ^ (k.choose 2 + (2 * k + 1)) * qBinom q n (k + 1) * x ^ (k + 1))
      = (∑ k ∈ Finset.range n,
          q ^ (k.choose 2 + (2 * k + 1)) * qBinom q n (k + 1) * x ^ (k + 1)) := by
    rw [Finset.sum_range_succ, qBinom_eq_zero_of_lt q n (n + 1) (Nat.lt_succ_self n)]
    ring
  rw [qbinomSum, Finset.sum_range_succ']
  simp only [hbody]
  have h0 : q ^ ((0 : ℕ).choose 2) * qBinom q (n + 1) 0 * x ^ 0 = 1 := by simp
  rw [h0, Finset.sum_add_distrib, qbinomSum, add_mul, one_mul, Finset.mul_sum,
      hsum_g, hsum_h]
  ring

/-- **q-binomial theorem (Rothe's formula).**
`∏_{i<n} (1 + q^i · x) = ∑_{k≤n} q^{C(k,2)} · [n choose k]_q · x^k`.

Proved by induction on `n` (generalizing `x`): peel the *first* factor of the
product with `Finset.prod_range_succ'`, rewrite `q^{i+1}x = q^i(qx)` to invoke the
induction hypothesis at `q·x`, then close with the functional recurrence
`qbinomSum_succ`. -/
theorem qBinomial_theorem (q x : R) (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 + q ^ i * x)) = qbinomSum q x n := by
  induction n generalizing x with
  | zero => simp [qbinomSum]
  | succ n ih =>
    rw [Finset.prod_range_succ']
    simp only [show ∀ i, 1 + q ^ (i + 1) * x = 1 + q ^ i * (q * x) from
      fun i => by rw [pow_succ]; ring]
    rw [ih (q * x), pow_zero, one_mul, qbinomSum_succ]
    ring

end GaussianBinomial
