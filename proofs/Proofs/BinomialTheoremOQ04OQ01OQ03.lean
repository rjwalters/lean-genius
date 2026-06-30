/-
# The Full q-Vandermonde Convolution for Gaussian Binomial Coefficients

Open Question: binomial-theorem-oq-04-oq-01-oq-03

The parent file `BinomialTheoremOQ02OQ02OQ01` (namespace `QBinomial`) built the
Gaussian binomial coefficient `qBinomial q n k` from the q-Pascal recurrence
  \binom{n+1}{k+1}_q = q^{k+1} \binom{n}{k+1}_q + \binom{n}{k}_q,
established the boundary/vanishing lemmas, and proved the two BASE CASES of the
q-Vandermonde convolution (m = 0 and n = 0).  Its "Open future work #1" was the
full inductive identity, which this file proves:

  **q-Vandermonde:**
    \binom{m+n}{r}_q = ∑_{k=0}^{r} q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q.

## Strategy

The crux is a new q-binomial identity, the **absorption / symmetry relation**

  (★)   (q^{k+1} - 1) · \binom{m}{k+1}_q = (q^{m-k} - 1) · \binom{m}{k}_q,

a q-analog of `(k+1)·C(m,k+1) = (m-k)·C(m,k)`.  We prove (★) by induction on m
using only the q-Pascal recurrence and the geometric-sum closed form
`qBinomial q n 1 = ∑_{i<n} q^i` (from the parent file).

The main theorem is then proved by induction on n.  In the inductive step we
expand `\binom{m+n+1}{r}_q` with q-Pascal, expand `\binom{n+1}{r-k}_q` inside the
target sum with q-Pascal, and reconcile the two via (★) applied term-by-term.

Everything is over a `CommRing` (the subtraction `q^j - 1` needs additive
inverses).  At `q = 1` this specializes to the classical Vandermonde identity.

**0 axioms, 0 sorries — fully verified in ZFC (Mathlib).**

## References
- Andrews, "The Theory of Partitions" (1976), Ch. 3
- Kac & Cheung, "Quantum Calculus" (2002), §6
- Stanley, "Enumerative Combinatorics" Vol. 1 (2nd ed., 2011), §1.7
-/

import Proofs.BinomialTheoremOQ02OQ02OQ01
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic

namespace BinomialTheoremOQ04OQ01OQ03

open Finset QBinomial

variable {R : Type*} [CommRing R]

-- ============================================================
-- PART 1: The q-binomial absorption identity (★)
-- ============================================================

/-- **q-binomial absorption identity**:
    `(q^{k+1} - 1) · \binom{m}{k+1}_q = (q^{m-k} - 1) · \binom{m}{k}_q`.

    This is the q-analog of the classical absorption identity
    `(k+1)·C(m,k+1) = (m-k)·C(m,k)`.  Proof is by induction on `m`,
    using the q-Pascal recurrence and the geometric-sum closed form
    `\binom{m+1}{1}_q = 1 + q + … + q^m`. -/
theorem qBinomial_absorption (q : R) (m : ℕ) :
    ∀ k, (q ^ (k + 1) - 1) * qBinomial q m (k + 1) =
        (q ^ (m - k) - 1) * qBinomial q m k := by
  induction m with
  | zero =>
    intro k
    -- LHS: qBinomial q 0 (k+1) = 0.  RHS: q^(0-k) = q^0 = 1, so factor is 0.
    simp
  | succ m ih =>
    intro k
    cases k with
    | zero =>
      -- (q - 1) · \binom{m+1}{1}_q = q^{m+1} - 1 via the geometric sum.
      rw [Nat.sub_zero, qBinomial_zero_right, mul_one, pow_one,
          qBinomial_one_eq_geom_sum, mul_comm, geom_sum_mul]
    | succ j =>
      -- Expand both q-binomials at the top level via q-Pascal.
      rw [qBinomial_succ_succ q m (j + 1), qBinomial_succ_succ q m j]
      -- (m+1) - (j+1) = m - j as an exponent.
      have hsub : (m + 1) - (j + 1) = m - j := by omega
      rw [hsub]
      have ih1 := ih (j + 1)
      have ih2 := ih j
      rcases lt_or_ge j m with hjm | hmj
      · -- Generic case j < m: m - j = (m - (j+1)) + 1, telescoping closes it.
        have hM : q ^ (m - j) = q ^ (m - (j + 1)) * q := by
          rw [← pow_succ]; congr 1; omega
        rw [hM] at ih2 ⊢
        linear_combination (q ^ (j + 1) * q) * ih1 + ih2
      · -- Degenerate case j ≥ m: the relevant q-binomials vanish, both sides 0.
        have hb : qBinomial q m (j + 1) = 0 :=
          qBinomial_eq_zero_of_lt q (by omega)
        have ha : qBinomial q m (j + 1 + 1) = 0 :=
          qBinomial_eq_zero_of_lt q (by omega)
        have hmj0 : m - j = 0 := by omega
        rw [ha, hb, hmj0]
        ring

-- ============================================================
-- PART 2: The full q-Vandermonde convolution
-- ============================================================

/-- **q-Vandermonde convolution** (full identity):

    `\binom{m+n}{r}_q = ∑_{k=0}^{r} q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q`.

    Proof by induction on `n`.  The base case `n = 0` is `qVandermonde_zero_right`
    from the parent file.  The inductive step expands `\binom{m+n+1}{r}_q` and the
    inner `\binom{n+1}{r-k}_q` via q-Pascal and reconciles the resulting sums with
    the absorption identity `qBinomial_absorption`. -/
theorem qVandermonde (q : R) (m : ℕ) : ∀ n r,
    qBinomial q (m + n) r =
      ∑ k ∈ range (r + 1),
        q ^ ((m - k) * (r - k)) * qBinomial q m k * qBinomial q n (r - k) := by
  intro n
  induction n with
  | zero =>
    intro r
    simpa using qVandermonde_zero_right q m r
  | succ n ih =>
    intro r
    cases r with
    | zero => simp
    | succ s =>
      have hmn : m + (n + 1) = (m + n) + 1 := by omega
      rw [hmn, qBinomial_succ_succ q (m + n) s, ih (s + 1), ih s, Finset.mul_sum]
      -- Expand the inner `qBinomial q (n+1) (s+1-k)` on the RHS via q-Pascal and
      -- peel boundary terms so both sides become sums of the same shape.
      -- RHS: split off k = s+1 and q-Pascal the rest.
      rw [Finset.sum_range_succ (fun k => q ^ ((m - k) * (s + 1 - k)) *
            qBinomial q m k * qBinomial q (n + 1) (s + 1 - k)) (s + 1)]
      -- the peeled RHS term k=s+1 is `qBinomial q m (s+1)`
      have hRpeel : q ^ ((m - (s + 1)) * (s + 1 - (s + 1))) * qBinomial q m (s + 1) *
          qBinomial q (n + 1) (s + 1 - (s + 1)) = qBinomial q m (s + 1) := by simp
      rw [hRpeel]
      -- q-Pascal inside the remaining RHS sum (range (s+1)): for k ≤ s
      have hRsum : ∑ k ∈ range (s + 1), q ^ ((m - k) * (s + 1 - k)) *
            qBinomial q m k * qBinomial q (n + 1) (s + 1 - k)
          = (∑ k ∈ range (s + 1), q ^ ((m - k) * (s + 1 - k)) * q ^ (s + 1 - k) *
              qBinomial q m k * qBinomial q n (s + 1 - k))
            + ∑ k ∈ range (s + 1), q ^ ((m - k) * (s + 1 - k)) *
              qBinomial q m k * qBinomial q n (s - k) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hks : k ≤ s := by have := Finset.mem_range.mp hk; omega
        have hpascal : qBinomial q (n + 1) (s + 1 - k)
            = q ^ (s + 1 - k) * qBinomial q n (s + 1 - k) + qBinomial q n (s - k) := by
          conv_lhs => rw [show s + 1 - k = (s - k) + 1 from by omega]
          rw [qBinomial_succ_succ q n (s - k), show (s - k) + 1 = s + 1 - k from by omega]
        rw [hpascal]; ring
      rw [hRsum]
      -- LHS: peel k=s+1 from the first (q^(s+1)-scaled) sum.
      rw [Finset.sum_range_succ (fun k => q ^ (s + 1) *
            (q ^ ((m - k) * (s + 1 - k)) * qBinomial q m k * qBinomial q n (s + 1 - k))) (s + 1)]
      have hLpeel : q ^ (s + 1) * (q ^ ((m - (s + 1)) * (s + 1 - (s + 1))) *
          qBinomial q m (s + 1) * qBinomial q n (s + 1 - (s + 1)))
          = q ^ (s + 1) * qBinomial q m (s + 1) := by simp
      rw [hLpeel]
      -- ===== Reconciliation via the absorption identity =====
      -- "High" sum (over B_n(s+1-k)): its k=0 term vanishes; reindex to range s.
      have hHQ :
          (∑ k ∈ range (s + 1), q ^ ((m - k) * (s + 1 - k)) * q ^ (s + 1 - k) *
              qBinomial q m k * qBinomial q n (s + 1 - k))
            - (∑ k ∈ range (s + 1), q ^ (s + 1) *
                (q ^ ((m - k) * (s + 1 - k)) * qBinomial q m k * qBinomial q n (s + 1 - k)))
          = ∑ k ∈ range s,
              q ^ ((m - (k + 1)) * (s - k)) * (q ^ (s - k) - q ^ (s + 1)) *
                qBinomial q m (k + 1) * qBinomial q n (s - k) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ' _ s]
        have hf0 : q ^ ((m - 0) * (s + 1 - 0)) * q ^ (s + 1 - 0) * qBinomial q m 0 *
              qBinomial q n (s + 1 - 0)
            - q ^ (s + 1) * (q ^ ((m - 0) * (s + 1 - 0)) * qBinomial q m 0 *
              qBinomial q n (s + 1 - 0)) = 0 := by simp only [Nat.sub_zero]; ring
        rw [hf0, add_zero]
        apply Finset.sum_congr rfl
        intro k hk
        rw [show s + 1 - (k + 1) = s - k from by omega]
        ring
      -- "Low" sum (over B_n(s-k)): peel its k=s term.
      have hLQ :
          (∑ k ∈ range (s + 1), q ^ ((m - k) * (s + 1 - k)) *
              qBinomial q m k * qBinomial q n (s - k))
            - (∑ k ∈ range (s + 1), q ^ ((m - k) * (s - k)) *
              qBinomial q m k * qBinomial q n (s - k))
          = (∑ k ∈ range s,
              (q ^ ((m - k) * (s + 1 - k)) - q ^ ((m - k) * (s - k))) *
                qBinomial q m k * qBinomial q n (s - k))
            + (q ^ (m - s) - 1) * qBinomial q m s := by
        rw [← Finset.sum_sub_distrib, Finset.sum_range_succ _ s]
        congr 1
        · apply Finset.sum_congr rfl; intro k hk; ring
        · rw [show s + 1 - s = 1 from by omega, show s - s = 0 from by omega]
          simp only [Nat.mul_zero, pow_zero, qBinomial_zero_right, mul_one]
          ring
      -- Termwise cancellation of the two range-s sums (uses absorption at k).
      have hterm : ∀ k ∈ range s,
          q ^ ((m - (k + 1)) * (s - k)) * (q ^ (s - k) - q ^ (s + 1)) *
              qBinomial q m (k + 1) * qBinomial q n (s - k)
          + (q ^ ((m - k) * (s + 1 - k)) - q ^ ((m - k) * (s - k))) *
              qBinomial q m k * qBinomial q n (s - k) = 0 := by
        intro k hk
        have hklt : k < s := Finset.mem_range.mp hk
        rcases lt_or_ge k m with hkm | hkm
        · have hpow1 : q ^ (s + 1) = q ^ (s - k) * q ^ (k + 1) := by
            rw [← pow_add]; congr 1; omega
          have hpow2 : q ^ ((m - (k + 1)) * (s - k)) * q ^ (s - k)
              = q ^ ((m - k) * (s - k)) := by
            rw [← pow_add]; congr 1
            have h1 : m - (k + 1) + 1 = m - k := by omega
            calc (m - (k + 1)) * (s - k) + (s - k)
                = (m - (k + 1) + 1) * (s - k) := by ring
              _ = (m - k) * (s - k) := by rw [h1]
          have hpow3 : q ^ ((m - k) * (s + 1 - k))
              = q ^ ((m - k) * (s - k)) * q ^ (m - k) := by
            rw [← pow_add]; congr 1
            have h2 : s + 1 - k = (s - k) + 1 := by omega
            rw [h2]; ring
          have hab := qBinomial_absorption q m k
          linear_combination
            (-(q ^ ((m - (k + 1)) * (s - k))) * qBinomial q m (k + 1) *
                qBinomial q n (s - k)) * hpow1
            + (qBinomial q m (k + 1) * qBinomial q n (s - k) * (1 - q ^ (k + 1))) * hpow2
            + (qBinomial q m k * qBinomial q n (s - k)) * hpow3
            + (-(q ^ ((m - k) * (s - k))) * qBinomial q n (s - k)) * hab
        · have hb1 : qBinomial q m (k + 1) = 0 := qBinomial_eq_zero_of_lt q (by omega)
          have hmk : m - k = 0 := by omega
          rw [hb1, hmk]; simp
      have hHL0 :
          (∑ k ∈ range s,
              q ^ ((m - (k + 1)) * (s - k)) * (q ^ (s - k) - q ^ (s + 1)) *
                qBinomial q m (k + 1) * qBinomial q n (s - k))
            + (∑ k ∈ range s,
              (q ^ ((m - k) * (s + 1 - k)) - q ^ ((m - k) * (s - k))) *
                qBinomial q m k * qBinomial q n (s - k)) = 0 := by
        rw [← Finset.sum_add_distrib, Finset.sum_eq_zero hterm]
      have habs : (q ^ (s + 1) - 1) * qBinomial q m (s + 1)
                = (q ^ (m - s) - 1) * qBinomial q m s := qBinomial_absorption q m s
      linear_combination -hHQ - hLQ - hHL0 + habs

/-- **Classical Vandermonde** as the `q = 1` specialization:
    `C(m+n, r) = ∑_{k=0}^{r} C(m,k) · C(n,r-k)` (cast into `R`). -/
theorem vandermonde_classical (m n r : ℕ) :
    ((m + n).choose r : R) =
      ∑ k ∈ range (r + 1), ((m.choose k : R) * (n.choose (r - k) : R)) := by
  have h := qVandermonde (1 : R) m n r
  simp only [one_pow, one_mul, qBinomial_at_one] at h
  exact h

end BinomialTheoremOQ04OQ01OQ03

/-!
## Summary

This file closes "Open future work #1" of `BinomialTheoremOQ02OQ02OQ01`: the full
q-Vandermonde convolution

  \binom{m+n}{r}_q = ∑_{k=0}^{r} q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q.

### Established results
- `qBinomial_absorption` — the q-binomial absorption identity
  `(q^{k+1}-1)·\binom{m}{k+1}_q = (q^{m-k}-1)·\binom{m}{k}_q`, a new piece of
  q-binomial infrastructure proved by induction on `m`.
- `qVandermonde` — the full q-Vandermonde convolution, by induction on `n`,
  reducing the inductive step to `qBinomial_absorption` term-by-term.
- `vandermonde_classical` — the `q = 1` specialization recovering the classical
  Vandermonde identity.

Theorems Proved: 3, Axioms: 0, Sorries: 0
-/

#check @BinomialTheoremOQ04OQ01OQ03.qBinomial_absorption
#check @BinomialTheoremOQ04OQ01OQ03.qVandermonde
#check @BinomialTheoremOQ04OQ01OQ03.vandermonde_classical
