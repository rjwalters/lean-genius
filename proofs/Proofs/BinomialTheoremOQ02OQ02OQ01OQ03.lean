/-
  q-Binomial Reflection Symmetry and the Dual q-Pascal Rule
  Open Question: binomial-theorem-oq-02-oq-02-oq-01-oq-03

  The parent file `BinomialTheoremOQ02OQ02OQ01.lean` builds the Gaussian
  (q-)binomial coefficient `qBinomial q n k` from the q-Pascal recurrence

      \binom{n+1}{k+1}_q = q^{k+1}·\binom{n}{k+1}_q + \binom{n}{k}_q          (A)

  and lists three results as explicit *open future work*:
    (#2) the **dual q-Pascal rule**
         \binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}·\binom{n}{k}_q        (B)
    (#3) the **reflection symmetry**
         \binom{n}{k}_q = \binom{n}{n-k}_q                  for k ≤ n.

  This file proves both, plus the algebraic invariant that drives them:

    (RATIO)  (q^{k+1} − 1)·\binom{n}{k+1}_q = (q^{n-k} − 1)·\binom{n}{k}_q.

  All three are identities of polynomials in `q`. Because the proofs use the
  factors `q^j − 1` (genuine subtraction), they are stated over a `CommRing R` —
  covering ℤ[q], ℚ(q), ℝ, ℂ and every finite field, i.e. all settings in which
  Gaussian binomials are used. The parent's recurrence-defined `qBinomial`
  lives over a `CommSemiring`, so every parent lemma specializes here.

  ## Proof architecture

  * `qBinomial_ratio` (RATIO): induction on `n`. The boundary `k = 0` instance
    `(q−1)·\binom{n}{1}_q = q^n − 1` is precisely the telescoping geometric sum
    `geom_sum_mul`, using the parent's closed form `\binom{n}{1}_q = ∑_{i<n} q^i`.
    The inductive step expands both q-binomials with (A) and closes by a
    `linear_combination` of the two instances `RATIO(n, j)` and `RATIO(n, j+1)`.

  * `qBinomial_dual_pascal` (B): immediate from (A) + RATIO via `linear_combination`.

  * `qBinomial_reflection` (#3): induction on `n`. Expand `\binom{n+1}{j+1}_q`
    with (A) and `\binom{n+1}{(n+1)-(j+1)}_q` with the *dual* rule (B); the two
    expansions become equal after applying the inductive hypothesis — they differ
    only by `add_comm`. (So once (B) is available, reflection needs no further
    use of RATIO.)

  ## References
  - Andrews, "The Theory of Partitions" (1976), Ch. 3
  - Kac & Cheung, "Quantum Calculus" (2002), §6
  - Stanley, "Enumerative Combinatorics" Vol. 1 (2nd ed., 2011), §1.7
-/

import Mathlib.Algebra.Group.NatPowAssoc
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ02OQ01

namespace QBinomial

open Finset

variable {R : Type*} [CommRing R]

/-- **Ratio invariant.** For every `n, k`:
    `(q^{k+1} − 1)·\binom{n}{k+1}_q = (q^{n-k} − 1)·\binom{n}{k}_q`.

    This holds unconditionally (when `k ≥ n` both sides vanish, since the natural
    subtraction `n - k = 0` makes the right factor `q^0 − 1 = 0`). It is the
    algebraic engine behind both the dual q-Pascal rule and reflection symmetry.

    Proof by induction on `n`. The base instance `k = 0` is the telescoping
    geometric sum `(q − 1)(1 + q + ⋯ + q^{n-1}) = q^n − 1`. -/
theorem qBinomial_ratio (q : R) (n k : ℕ) :
    (q ^ (k + 1) - 1) * qBinomial q n (k + 1)
      = (q ^ (n - k) - 1) * qBinomial q n k := by
  induction n generalizing k with
  | zero => simp [qBinomial_zero_succ]
  | succ n IH =>
    rcases k with _ | j
    · -- k = 0 : telescoping geometric sum
      simp only [Nat.zero_add, pow_one, Nat.sub_zero, qBinomial_zero_right, mul_one]
      rw [qBinomial_one_eq_geom_sum, mul_comm, geom_sum_mul]
    · rcases le_or_gt (j + 1) n with hjn | hjn
      · -- interior: j + 1 ≤ n
        obtain ⟨p, rfl⟩ : ∃ p, n = j + 1 + p := ⟨n - (j + 1), by omega⟩
        have h1 := IH (j + 1)
        have h2 := IH j
        rw [show (j + 1 + p) - (j + 1) = p from by omega] at h1
        rw [show (j + 1 + p) - j = p + 1 from by omega] at h2
        rw [qBinomial_succ_succ q (j + 1 + p) (j + 1),
            qBinomial_succ_succ q (j + 1 + p) j,
            show (j + 1 + p + 1) - (j + 1) = p + 1 from by omega]
        linear_combination (q ^ (j + 2)) * h1 + h2
      · -- boundary: n < j + 1, both sides vanish
        rw [qBinomial_eq_zero_of_lt q (show n + 1 < j + 1 + 1 by omega),
            show (n + 1) - (j + 1) = 0 from by omega]
        simp

/-- **Dual q-Pascal rule** (parent open-work #2). For every `n, k`:
    `\binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}·\binom{n}{k}_q`.

    Where the defining recurrence (A) splits off the *largest* element, this dual
    form splits off the *smallest*. It is `(A)` reconciled with `qBinomial_ratio`. -/
theorem qBinomial_dual_pascal (q : R) (n k : ℕ) :
    qBinomial q (n + 1) (k + 1)
      = qBinomial q n (k + 1) + q ^ (n - k) * qBinomial q n k := by
  rw [qBinomial_succ_succ]
  linear_combination qBinomial_ratio q n k

/-- **Reflection symmetry** (parent open-work #3): `\binom{n}{k}_q = \binom{n}{n-k}_q`
    for `k ≤ n`. The q-analogue of `Nat.choose_symm`.

    Proof by induction on `n`: expand `\binom{n+1}{k}_q` with the ordinary
    recurrence (A) and `\binom{n+1}{(n+1)-k}_q` with the dual rule (B); after the
    inductive hypothesis both equal `q^{k}·\binom{n}{n-k}_q + \binom{n}{n-k-…}`,
    differing only by commutativity of addition. -/
theorem qBinomial_reflection (q : R) :
    ∀ (n k : ℕ), k ≤ n → qBinomial q n k = qBinomial q n (n - k)
  | 0, k, hk => by
      obtain rfl : k = 0 := by omega
      rfl
  | n + 1, k, hk => by
      rcases k with _ | j
      · -- k = 0 : \binom{n+1}{0}_q = 1 = \binom{n+1}{n+1}_q
        rw [qBinomial_zero_right, Nat.sub_zero, qBinomial_self]
      · rcases le_or_gt n j with hjn | hjn
        · -- j = n, i.e. k = n + 1 : both endpoints equal 1
          obtain rfl : j = n := by omega
          rw [qBinomial_self, Nat.sub_self, qBinomial_zero_right]
        · -- interior: j < n
          obtain ⟨p, rfl⟩ : ∃ p, n = j + 1 + p := ⟨n - (j + 1), by omega⟩
          have IHa := qBinomial_reflection q (j + 1 + p) (j + 1) (by omega)
          have IHb := qBinomial_reflection q (j + 1 + p) j (by omega)
          rw [show (j + 1 + p) - (j + 1) = p from by omega] at IHa
          rw [show (j + 1 + p) - j = p + 1 from by omega] at IHb
          rw [show (j + 1 + p + 1) - (j + 1) = p + 1 from by omega,
              qBinomial_succ_succ q (j + 1 + p) j,
              qBinomial_dual_pascal q (j + 1 + p) p,
              show (j + 1 + p) - p = j + 1 from by omega,
              IHa, IHb]
          ring

/-- At `q = 1` the reflection symmetry recovers the classical `Nat.choose`
    symmetry `\binom{n}{k} = \binom{n}{n-k}`, cast into `R`. -/
theorem qBinomial_choose_symm (n k : ℕ) (hk : k ≤ n) :
    (Nat.choose n k : R) = (Nat.choose n (n - k) : R) := by
  rw [← qBinomial_at_one n k, ← qBinomial_at_one n (n - k)]
  exact qBinomial_reflection (1 : R) n k hk

end QBinomial

/-!
## Summary

Resolves parent open-work items #2 (dual q-Pascal) and #3 (reflection symmetry),
together with the ratio invariant that powers them. Over any `CommRing`:

- `qBinomial_ratio`        : (q^{k+1}−1)·\binom{n}{k+1}_q = (q^{n-k}−1)·\binom{n}{k}_q
- `qBinomial_dual_pascal`  : \binom{n+1}{k+1}_q = \binom{n}{k+1}_q + q^{n-k}·\binom{n}{k}_q
- `qBinomial_reflection`   : \binom{n}{k}_q = \binom{n}{n-k}_q   (k ≤ n)
- `qBinomial_choose_symm`   : the q = 1 specialization is `Nat.choose` symmetry

Theorems Proved: 4, Axioms: 0, Sorries: 0
-/

#check @QBinomial.qBinomial_ratio
#check @QBinomial.qBinomial_dual_pascal
#check @QBinomial.qBinomial_reflection
#check @QBinomial.qBinomial_choose_symm
