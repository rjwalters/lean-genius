/-
# AM-GM / Maclaurin OQ-03-OQ-02-OQ-02: the abstract log-concavity engine

## What This Proves

The heart of the derivation "Newton's inequalities ⟹ Maclaurin's inequalities" is a
purely combinatorial fact about **log-concave sequences** that has nothing to do with
symmetric polynomials. This file isolates that fact as a general, reusable tool.

Let `p : ℕ → ℝ` be a positive sequence with `p 0 = 1` that is **log-concave**:

  `p m · p (m+2) ≤ (p (m+1))²   for all m.`

Then:

1. `logConcave_pow_antitone` — the log-free, product-free multiplicative core:
   `p (k+1)^k ≤ (p k)^(k+1)` for all `k`.

2. `logConcave_root_antitone` — the "power means" `p_k^{1/k}` are non-increasing:
   `p (k+1)^{1/(k+1)} ≤ p k^{1/k}`.

Specialised to `p k = eₖ / C(n,k)` (whose log-concavity is exactly Newton's
inequality `newton_log_concavity` in `AmgmInequalityOQ02.lean`), statement 2 is
precisely Maclaurin's step `Mₖ ≥ Mₖ₊₁`. Stated abstractly here, the same engine
applies to *any* log-concave positive sequence — binomial coefficients, coefficients
of real-rooted polynomials, unimodal probability sequences, etc.

## Proof Strategy

`logConcave_pow_antitone` is proved by induction on `k`. The successor step raises the
log-concavity inequality `p m · p (m+2) ≤ p(m+1)²` to the power `m+1`, splits
`p(m+1)^{2(m+1)} = p(m+1)^m · p(m+1)^{m+2}`, feeds in the induction hypothesis
`p(m+1)^m ≤ (p m)^{m+1}` on one factor, and cancels the common positive factor
`(p m)^{m+1}`. Everything uses only `ℕ`-powers; no logarithms appear.

`logConcave_root_antitone` extracts the crossed roots via `rpow_cross`
(`b^s ≤ a^t ⟹ b^{1/t} ≤ a^{1/s}`).

No `sorry`, no axioms.
-/
import Mathlib

namespace MaclaurinLogConcave

open scoped Nat

/-- **The multiplicative log-concavity core.** For a positive log-concave sequence
`p` with `p 0 = 1`, one has `p (k+1)^k ≤ (p k)^(k+1)`. Proved by induction on `k` using
only natural-number powers (log- and product-free). -/
theorem logConcave_pow_antitone (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) :
    ∀ k : ℕ, (∀ j, j ≤ k + 1 → 0 < p j) →
      p (k + 1) ^ k ≤ p k ^ (k + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [hp0]
  | succ m ih =>
    intro hpos
    have IH := ih (fun j hj => hpos j (by omega))
    have hA : 0 < p m := hpos m (by omega)
    have hB : 0 < p (m + 1) := hpos (m + 1) (by omega)
    have hC : 0 < p (m + 2) := hpos (m + 2) (by omega)
    have hNewton : p m * p (m + 2) ≤ p (m + 1) ^ 2 := hlc m
    have hAC : (p m * p (m + 2)) ^ (m + 1) ≤ (p (m + 1) ^ 2) ^ (m + 1) :=
      pow_le_pow_left₀ (mul_nonneg hA.le hC.le) hNewton (m + 1)
    rw [mul_pow, ← pow_mul] at hAC
    have hsplit : p (m + 1) ^ (2 * (m + 1))
        = p (m + 1) ^ m * p (m + 1) ^ (m + 2) := by
      rw [← pow_add]; congr 1; omega
    have hIH2 : p (m + 1) ^ m * p (m + 1) ^ (m + 2)
        ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) :=
      mul_le_mul_of_nonneg_right IH (pow_nonneg hB.le _)
    have hcomb : p m ^ (m + 1) * p (m + 2) ^ (m + 1)
        ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) := by
      calc p m ^ (m + 1) * p (m + 2) ^ (m + 1)
            ≤ p (m + 1) ^ (2 * (m + 1)) := hAC
        _ = p (m + 1) ^ m * p (m + 1) ^ (m + 2) := hsplit
        _ ≤ p m ^ (m + 1) * p (m + 1) ^ (m + 2) := hIH2
    exact le_of_mul_le_mul_left hcomb (pow_pos hA _)

/-- If `b^s ≤ a^t` for positive reals and positive naturals, then taking the
appropriate crossed roots gives `b^(1/t) ≤ a^(1/s)`. -/
theorem rpow_cross {a b : ℝ} {s t : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hs : 0 < s) (ht : 0 < t) (h : b ^ s ≤ a ^ t) :
    b ^ ((1 : ℝ) / t) ≤ a ^ ((1 : ℝ) / s) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  have key : (b ^ s) ^ ((1 : ℝ) / (s * t)) ≤ (a ^ t) ^ ((1 : ℝ) / (s * t)) :=
    Real.rpow_le_rpow (pow_nonneg hb.le s) h (by positivity)
  have lhs : (b ^ s) ^ ((1 : ℝ) / (s * t)) = b ^ ((1 : ℝ) / t) := by
    rw [← Real.rpow_natCast b s, ← Real.rpow_mul hb.le]
    congr 1
    field_simp
  have rhs : (a ^ t) ^ ((1 : ℝ) / (s * t)) = a ^ ((1 : ℝ) / s) := by
    rw [← Real.rpow_natCast a t, ← Real.rpow_mul ha.le]
    congr 1
    field_simp
  rwa [lhs, rhs] at key

/-- **The root form (abstract Maclaurin monotonicity).** For a positive log-concave
sequence `p` with `p 0 = 1`, the `k`-th-root sequence `p_k^{1/k}` is non-increasing:
`p (k+1)^{1/(k+1)} ≤ p k^{1/k}` for every `k ≥ 1`.

Specialised to `p k = eₖ/C(n,k)`, this is Maclaurin's inequality `Mₖ ≥ Mₖ₊₁`. -/
theorem logConcave_root_antitone (p : ℕ → ℝ) (hp0 : p 0 = 1)
    (hpos : ∀ j, 0 < p j)
    (hlc : ∀ m, p m * p (m + 2) ≤ (p (m + 1)) ^ 2) (k : ℕ) (hk : 0 < k) :
    p (k + 1) ^ ((1 : ℝ) / (k + 1)) ≤ p k ^ ((1 : ℝ) / k) := by
  have hcore : p (k + 1) ^ k ≤ p k ^ (k + 1) :=
    logConcave_pow_antitone p hp0 hlc k (fun j _ => hpos j)
  have h1 : (0 : ℕ) < k + 1 := by omega
  simpa using rpow_cross (hpos k) (hpos (k + 1)) hk h1 hcore

end MaclaurinLogConcave
