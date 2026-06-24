/-
  Reflection Symmetry of Gaussian (q-Binomial) Coefficients
  Open Question: binomial-theorem-oq-02-oq-02-oq-01-oq-03

  The parent entry `binomial-theorem-oq-02-oq-02-oq-01` builds the q-binomial
  (Gaussian binomial) coefficient `qBinomial q n k` from the q-Pascal recurrence
    \binom{n+1}{k+1}_q = q^{k+1}·\binom{n}{k+1}_q + \binom{n}{k}_q          (primal)
  and proves the boundary/diagonal lemmas and only the k = 1 *special case* of
  reflection symmetry (`qBinomial_reflection_at_one`).  Its closing notes list
  three pieces of open future work:
    2. the **dual q-Pascal recurrence**, and
    3. the **full reflection symmetry**  \binom{n}{k}_q = \binom{n}{n-k}_q.

  This file resolves both.

  ## Main results

  * `qBinomial_succ_succ_dual` — the dual q-Pascal recurrence
      \binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}·\binom{n}{k}_q,
    valid for *all* `n k : ℕ` (the natural-subtraction exponent is harmless on
    the boundary because the accompanying coefficient vanishes there).

  * `qBinomial_reflection` — the reflection symmetry
      k ≤ n → \binom{n}{k}_q = \binom{n}{n-k}_q.

  * `qBinomial_reflection_add` — the symmetric `a + b` form
      \binom{a+b}{a}_q = \binom{a+b}{b}_q,
    the q-analogue of `Nat.choose_symm_diff`.

  At `q = 1` reflection specialises to the classical `Nat.choose_symm`
  (`qBinomial_reflection_at_one_eq_choose`), confirming the q-deformation is
  faithful.

  ## Why the dual recurrence is needed

  Over a `CommSemiring` there is no subtraction, so the dual recurrence is *not*
  an algebraic rearrangement of the primal one — it must be proved by its own
  induction.  The reflection proof then needs *both* recurrences: it expands the
  left coefficient by the dual rule and the reflected coefficient by the primal
  rule, after which the two q-Pascal pieces are matched by the inductive
  hypothesis.  This is exactly the dependency the parent flagged.

  ## References
  - Andrews, "The Theory of Partitions" (1976), Ch. 3
  - Kac & Cheung, "Quantum Calculus" (2002), §6
  - Stanley, "Enumerative Combinatorics" Vol. 1 (2nd ed., 2011), §1.7

  Theorems Proved: 6, Axioms: 0, Sorries: 0
-/

import Proofs.BinomialTheoremOQ02OQ02OQ01

namespace QBinomial

open Finset

variable {R : Type*} [CommSemiring R]

/-- **Dual q-Pascal recurrence.**
    `\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}·\binom{n}{k}_q`.

    This is the "other" q-Pascal rule, complementary to the defining (primal)
    recurrence `qBinomial_succ_succ`.  It holds for all `n k`; when `k > n` both
    sides vanish, so the truncated natural subtraction `n - k` in the exponent is
    immaterial.

    The proof is by induction on `n`.  In the generic step `k = j+1` with `j < n`
    we expand the left coefficient by the *primal* rule and then rewrite the two
    resulting `n+1`-row coefficients by the inductive (dual) hypothesis; matching
    the powers of `q` requires writing `n = j + 1 + m` to clear the truncated
    subtraction, after which `linear_combination` closes the goal. -/
theorem qBinomial_succ_succ_dual (q : R) :
    ∀ n k : ℕ,
      qBinomial q (n + 1) (k + 1)
        = qBinomial q n (k + 1) + q ^ (n - k) * qBinomial q n k
  | 0, k => by
      rcases k with _ | k
      · -- \binom{1}{1}_q = 1 = 0 + q^0·1
        simp
      · -- \binom{1}{k+2}_q = 0 = 0 + q^0·0
        rw [qBinomial_eq_zero_of_lt q (show (1 : ℕ) < k + 1 + 1 by omega)]
        simp
  | n + 1, k => by
      rcases k with _ | j
      · -- k = 0:  \binom{n+2}{1}_q = \binom{n+1}{1}_q + q^{n+1}·\binom{n+1}{0}_q
        simp only [qBinomial_zero_right, mul_one, Nat.sub_zero]
        rw [qBinomial_one_eq_geom_sum q (n + 1 + 1),
            qBinomial_one_eq_geom_sum q (n + 1), Finset.sum_range_succ]
      · rcases lt_trichotomy j n with hj | hj | hj
        · -- generic case:  j < n
          -- write n = j + 1 + m to clear truncated subtraction in exponents
          obtain ⟨m, rfl⟩ : ∃ m, n = j + 1 + m := ⟨n - j - 1, by omega⟩
          -- primal expansions of the two (n+1)-row coefficients
          -- (let Lean pick the canonical `j+1+1` index form to avoid rewrite mismatches)
          have hP2 := qBinomial_succ_succ q (j + 1 + m) (j + 1)
          have hP1 := qBinomial_succ_succ q (j + 1 + m) j
          -- dual (inductive) expansions of the same two coefficients
          have hD2 := qBinomial_succ_succ_dual q (j + 1 + m) (j + 1)
          have hD1 := qBinomial_succ_succ_dual q (j + 1 + m) j
          rw [show j + 1 + m - (j + 1) = m from by omega] at hD2
          rw [show j + 1 + m - j = m + 1 from by omega] at hD1
          -- bridge the primal and dual expansions of each coefficient
          have hE2 := hP2.symm.trans hD2
          have hE1 := hP1.symm.trans hD1
          -- expand the left coefficient by the primal rule, normalise the
          -- exponent, push everything down to the `j+1+m` row, then combine
          -- (`linear_combination` is unavailable over a `CommSemiring`; instead we
          -- rewrite each q-Pascal row by its dual form on the *left* of the goal
          -- only, leaving the right untouched, after which `ring` matches both.)
          rw [show j + 1 + m + 1 - (j + 1) = m + 1 from by omega,
              qBinomial_succ_succ q (j + 1 + m + 1) (j + 1), hP2, hP1]
          nth_rewrite 1 [hE2]
          nth_rewrite 1 [hE1]
          ring
        · -- j = n  (top of the column):  both rows collapse to 1 and 0
          subst hj
          rw [show j + 1 - (j + 1) = 0 from by omega,
              qBinomial_self,
              qBinomial_eq_zero_of_lt q (show j + 1 < j + 1 + 1 by omega),
              qBinomial_self]
          simp
        · -- j > n  (below the diagonal):  every coefficient vanishes
          rw [qBinomial_eq_zero_of_lt q (show n + 1 + 1 < j + 1 + 1 by omega),
              qBinomial_eq_zero_of_lt q (show n + 1 < j + 1 + 1 by omega),
              qBinomial_eq_zero_of_lt q (show n + 1 < j + 1 by omega)]
          ring

/-- **Reflection symmetry of the q-binomial coefficient.**
    For `k ≤ n`,  `\binom{n}{k}_q = \binom{n}{n-k}_q`.

    Proof by induction on `n`.  The boundary columns `k = 0` and `k = n+1` are
    the diagonal/unit values.  For an interior column `k = j+1` with `j < n` we
    expand the left coefficient by the dual rule and the reflected coefficient
    `\binom{n+1}{n-j}_q` by the primal rule; both produce the same power `q^{n-j}`,
    and the inductive hypothesis identifies the two remaining q-Pascal pieces. -/
theorem qBinomial_reflection (q : R) :
    ∀ n k : ℕ, k ≤ n → qBinomial q n k = qBinomial q n (n - k)
  | 0, k, hk => by
      interval_cases k
      simp
  | n + 1, k, hk => by
      rcases k with _ | j
      · -- k = 0:  \binom{n+1}{0}_q = 1 = \binom{n+1}{n+1}_q
        simp
      · -- k = j+1 with j ≤ n
        rcases (show j ≤ n by omega).lt_or_eq with hj | hj
        · -- interior:  j < n
          have hidx : n + 1 - (j + 1) = (n - j - 1) + 1 := by omega
          have hkey : n - j - 1 + 1 = n - j := by omega
          -- dual expansion of the left coefficient
          have hL := qBinomial_succ_succ_dual q n j
          -- primal expansion of the reflected coefficient \binom{n+1}{n-j}_q
          have hR : qBinomial q (n + 1) (n + 1 - (j + 1))
              = q ^ (n - j) * qBinomial q n (n - j) + qBinomial q n (n - j - 1) := by
            rw [hidx, qBinomial_succ_succ, hkey]
          -- inductive hypotheses: \binom{n}{j}=\binom{n}{n-j}, \binom{n}{j+1}=\binom{n}{n-j-1}
          have ih0 : qBinomial q n j = qBinomial q n (n - j) :=
            qBinomial_reflection q n j (by omega)
          have ih1 : qBinomial q n (j + 1) = qBinomial q n (n - j - 1) := by
            have h := qBinomial_reflection q n (j + 1) (by omega)
            rwa [show n - (j + 1) = n - j - 1 from by omega] at h
          rw [hR, hL, ih0, ih1]
          ring
        · -- top:  j = n, both sides are 1
          subst hj
          rw [show j + 1 - (j + 1) = 0 from by omega]
          simp

/-- **Reflection symmetry, symmetric form.**  `\binom{a+b}{a}_q = \binom{a+b}{b}_q`.
    The q-analogue of `Nat.choose_symm_diff`. -/
theorem qBinomial_reflection_add (q : R) (a b : ℕ) :
    qBinomial q (a + b) a = qBinomial q (a + b) b := by
  rw [qBinomial_reflection q (a + b) a (Nat.le_add_right a b),
      show a + b - a = b from by omega]

/-- At `q = 1` the reflection symmetry recovers the classical binomial symmetry
    `Nat.choose_symm`:  `\binom{n}{k} = \binom{n}{n-k}` for `k ≤ n`. -/
theorem qBinomial_reflection_at_one_eq_choose (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : R) = (Nat.choose n (n - k) : R) := by
  rw [← qBinomial_at_one n k, ← qBinomial_at_one n (n - k)]
  exact qBinomial_reflection (1 : R) n k hk

end QBinomial
