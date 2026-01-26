/-!
# Erdős Problem #726 — Residues in the Upper Half Interval

**Conjecture (Erdős–Graham–Ruzsa–Straus, 1975):**
As n → ∞ over integers,
  Σ_{p ≤ n, n mod p ∈ (p/2, p)} 1/p ~ (log log n) / 2

Here n mod p ∈ (p/2, p) means the least nonneg. residue r of n mod p
satisfies p/2 < r < p.

By Mertens' theorem, Σ_{p ≤ n} 1/p ~ log log n. The conjecture says
that the "upper half" residues contribute exactly half of Mertens' sum.

**Status: OPEN.**

Reference: https://erdosproblems.com/726
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## Core Definitions -/

/-- Whether n mod p lies in the "upper half" interval (p/2, p).
    Equivalently, the least nonneg. residue r = n % p satisfies p/2 < r. -/
def isUpperHalfResidue (n p : ℕ) : Prop :=
  p / 2 < n % p

/-- The weighted sum: Σ_{p ≤ n, p prime, n mod p ∈ (p/2, p)} 1/p. -/
noncomputable def upperHalfSum (n : ℕ) : ℝ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ isUpperHalfResidue n p)
    |>.sum (fun p => (1 : ℝ) / p)

/-! ## Mertens' Theorem for Context -/

/-- Mertens' theorem: Σ_{p ≤ n} 1/p ~ log log n.
    The full sum over all primes ≤ n has this asymptotic. -/
axiom mertens_theorem :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |((Finset.Icc 2 n).filter Nat.Prime).sum (fun p => (1 : ℝ) / p)
        - Real.log (Real.log n)| < ε

/-! ## The Main Conjecture -/

/-- **Erdős–Graham–Ruzsa–Straus Conjecture (1975):**
    The sum over primes p ≤ n where n mod p ∈ (p/2, p) is
    asymptotically (log log n)/2. That is, exactly half of Mertens'
    sum comes from "upper half" residues. -/
axiom erdos_726_conjecture :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |upperHalfSum n - Real.log (Real.log n) / 2| < ε

/-! ## Heuristic Explanation -/

/-- For a random n, the residue n mod p is roughly uniform on {0,...,p-1}.
    The fraction of residues in (p/2, p) is approximately 1/2.
    So heuristically, Σ 1/p over upper-half primes ≈ (1/2) Σ 1/p ~ (log log n)/2.
    Making this rigorous requires controlling correlations between
    residues at different primes. -/
axiom heuristic_half_contribution :
    ∀ p : ℕ, p.Prime → 2 < p →
      (((Finset.Icc 0 (p - 1)).filter (fun r => p / 2 < r)).card : ℝ) / p =
        ((p - 1) / 2 : ℝ) / p

/-! ## Complementary Sum -/

/-- The "lower half" sum: residues in [0, p/2]. -/
noncomputable def lowerHalfSum (n : ℕ) : ℝ :=
  (Finset.Icc 2 n).filter (fun p => p.Prime ∧ ¬isUpperHalfResidue n p)
    |>.sum (fun p => (1 : ℝ) / p)

/-- The upper and lower half sums partition Mertens' sum. -/
axiom half_sums_partition (n : ℕ) :
    upperHalfSum n + lowerHalfSum n =
      ((Finset.Icc 2 n).filter Nat.Prime).sum (fun p => (1 : ℝ) / p)

/-- The conjecture implies the lower half also contributes ~ (log log n)/2.
    Both halves are asymptotically equal. -/
axiom lower_half_also_half :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      |lowerHalfSum n - Real.log (Real.log n) / 2| < ε

/-! ## Related Problems -/

/-- The Erdős–Graham–Ruzsa–Straus paper (1975) contains several
    related problems about the distribution of residues modulo primes.
    This is one of the more natural: does the "upper half" get its
    fair share of the Mertens sum? -/
axiom egrs_context :
    ∀ n : ℕ, 2 ≤ n →
      upperHalfSum n ≤ ((Finset.Icc 2 n).filter Nat.Prime).sum (fun p => (1 : ℝ) / p)
