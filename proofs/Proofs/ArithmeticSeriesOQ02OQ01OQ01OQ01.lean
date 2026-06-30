/-
  The Finite q-Binomial Theorem (Gauss / Rothe) — a Free-Parameter
  q-Chu-Vandermonde Generating Identity

  Open Question (arithmetic-series-oq-02-oq-01-oq-01-oq-01):
  "Extend to the full q-Chu-Vandermonde identity with non-integer q-exponents."

  The parent entry `arithmetic-series-oq-02-oq-01-oq-01` proves the Gauss
  q-Vandermonde *convolution* for natural-number parameters m, n:

    [m+n choose r]_q = ∑_{k=0}^{r} q^{k(m+k-r)} · [m choose r-k]_q · [n choose k]_q.   (V)

  In (V) both shape parameters m, n are natural numbers and every q-exponent is a
  natural number.  To "extend to non-integer q-exponents" means to replace those
  natural-number powers q^m, q^n by a *free* ring element — an honest continuous
  parameter `x` standing for `q^α` with α not necessarily an integer.  The object
  that carries such a free parameter is the q-shifted factorial (q-Pochhammer
  symbol) and its generating function, the **q-binomial theorem**:

    ∏_{i=0}^{n-1} (1 + x · q^i) = ∑_{k=0}^{n} q^{\binom{k}{2}} · [n choose k]_q · x^k.   (qBT)

  Here `x` is an arbitrary element of any commutative ring R; nothing forces it to
  be a power of q.  (qBT) is the generating-function master identity that *implies*
  the parent convolution (V): expanding ∏_{i<m+n} = ∏_{i<m} · ∏_{i<n} (·)|_{x↦xq^m}
  and matching the coefficient of x^r yields exactly (V) with the q-exponent
  k(m+k-r) (the cross-term q^{m·k} from the shift combines with the two
  \binom{·}{2} exponents to give k(m+k-r), since
  \binom{r-k}{2} + \binom{k}{2} - \binom{r}{2} = -k(r-k)).

  **What is proved (0 axioms, 0 sorries, no native_decide):**

  * `qBinomialTheorem` — the finite q-binomial theorem (qBT) over any CommRing,
    for arbitrary free parameter `x`.  Proof: induction on n, peeling the FIRST
    factor with `Finset.prod_range_succ'` and applying the inductive hypothesis at
    the shifted argument `x·q`; this routes the Pascal step through the *available*
    q-Pascal rule `qBinom_succ_succ` (no dual Pascal needed).

  * `qBinomialTheorem_q_one` — specialization q = 1 recovers the ordinary binomial
    theorem `(1 + x)^n = ∑_k C(n,k) x^k`.

  * `qPoch` / `qPoch_neg_eq` — the product side is the q-Pochhammer symbol
    `(-x; q)_n`, making the non-integer-exponent reading explicit (x = q^α).

  * concrete `decide` checks pin down small cases.

  References:
  - V. Kac, P. Cheung, "Quantum Calculus" (Springer, 2002), Ch. 5–7 (Gauss's
    binomial formula) and Ch. 10 (q-Vandermonde).
  - G. E. Andrews, "The Theory of Partitions", §3.3 (q-binomial theorem).

  Parent: ArithmeticSeriesOQ02OQ01OQ01.lean (qVandermonde, ℕ parameters)
  Grandparent: ArithmeticSeriesOQ02OQ01.lean (GaussianBinomial.qBinom)
-/
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ01OQ01

open GaussianBinomial Finset BigOperators

namespace qBinomialTheoremProof

-- ============================================================
-- Section 1: The q-Exponent Arithmetic Lemma
-- ============================================================

/-- The triangular-number recurrence `\binom{k+1}{2} = \binom{k}{2} + k`,
    the q-exponent bookkeeping that drives the inductive step. -/
lemma choose_two_succ (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  rw [Nat.choose_succ_succ k 1, Nat.choose_one_right, Nat.add_comm]

-- ============================================================
-- Section 2: The Finite q-Binomial Theorem (Gauss / Rothe)
-- ============================================================

/-- **The finite q-binomial theorem (Gauss / Rothe).**

For any commutative ring `R`, any `q x : R` and `n : ℕ`,

  `∏_{i=0}^{n-1} (1 + x · q^i) = ∑_{k=0}^{n} q^{\binom{k}{2}} · [n choose k]_q · x^k`.

The free parameter `x` is an arbitrary ring element — this is the
"non-integer q-exponent" generalization of the parent's natural-number
q-Vandermonde convolution: take `x = q^α` for any α and the product is the
q-Pochhammer symbol `(-q^α; q)_n`.

Proof by induction on `n`, generalizing `x`.  The first factor is peeled with
`Finset.prod_range_succ'`, leaving `∏_{i<n}(1 + (x·q)·q^i)`, to which the
inductive hypothesis applies at argument `x·q`.  The resulting sum identity is
closed by the q-Pascal rule `qBinom_succ_succ` together with
`choose_two_succ`. -/
theorem qBinomialTheorem {R : Type*} [CommRing R] (q x : R) (n : ℕ) :
    ∏ i ∈ Finset.range n, (1 + x * q ^ i) =
      ∑ k ∈ Finset.range (n + 1), q ^ (k.choose 2) * qBinom q n k * x ^ k := by
  induction n generalizing x with
  | zero =>
    -- empty product = 1, RHS is the single k = 0 term
    simp
  | succ n ih =>
    -- Peel the FIRST factor: ∏_{i<n+1}(1+x q^i) = (∏_{i<n}(1+x q^{i+1}))·(1+x q^0)
    rw [Finset.prod_range_succ']
    -- Rewrite each shifted factor 1 + x q^{i+1} = 1 + (x q) q^i, and 1 + x q^0 = 1 + x
    have hfac : ∀ i ∈ Finset.range n, (1 + x * q ^ (i + 1)) = 1 + (x * q) * q ^ i := by
      intro i _; rw [pow_succ]; ring
    rw [Finset.prod_congr rfl hfac, pow_zero, mul_one]
    -- Apply the inductive hypothesis at argument (x * q)
    rw [ih (x * q)]
    -- Goal: (∑_{k<n+1} q^{C(k,2)} [n,k]_q (x q)^k) · (1 + x)
    --        = ∑_{k<n+2} q^{C(k,2)} [n+1,k]_q x^k
    -- Normalize the LHS summand: (x q)^k = x^k q^k, fold q^k into the exponent via choose_two_succ
    have hL : ∀ k ∈ Finset.range (n + 1),
        q ^ (k.choose 2) * qBinom q n k * (x * q) ^ k
          = q ^ ((k + 1).choose 2) * qBinom q n k * x ^ k := by
      intro k _
      rw [mul_pow, choose_two_succ, pow_add]
      ring
    rw [Finset.sum_congr rfl hL]
    -- Let A k := q^{C(k+1,2)} [n,k]_q x^k.  LHS = (∑_{k<n+1} A k)·(1+x).
    set A : ℕ → R := fun k => q ^ ((k + 1).choose 2) * qBinom q n k * x ^ k with hA
    -- Expand RHS: peel k = 0 with sum_range_succ', then q-Pascal on [n+1,k+1]_q.
    rw [Finset.sum_range_succ' (fun k => q ^ (k.choose 2) * qBinom q (n + 1) k * x ^ k) (n + 1)]
    rw [show Nat.choose 0 2 = 0 from rfl]
    simp only [pow_zero, qBinom_zero_right, mul_one]
    -- RHS now: (∑_{k<n+1} q^{C(k+1,2)} [n+1,k+1]_q x^{k+1}) + 1
    have hR : ∀ k ∈ Finset.range (n + 1),
        q ^ ((k + 1).choose 2) * qBinom q (n + 1) (k + 1) * x ^ (k + 1)
          = A (k + 1) + x * A k := by
      intro k _
      rw [hA]
      simp only
      rw [qBinom_succ_succ, choose_two_succ ((k + 1)), choose_two_succ k]
      -- [n+1,k+1]_q = q^{k+1} [n,k+1]_q + [n,k]_q
      rw [pow_succ x k]
      ring
    rw [Finset.sum_congr rfl hR, Finset.sum_add_distrib]
    -- Now: (∑_{k<n+1} A (k+1)) + (∑_{k<n+1} x * A k) + 1
    --       = (∑_{k<n+1} A k) * (1 + x)
    -- The first sum telescopes off its top (zero) term; A is shifted.
    have htop : A (n + 1) = 0 := by
      rw [hA]; simp only
      rw [qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
      ring
    have hshift : (∑ k ∈ Finset.range (n + 1), A (k + 1))
        = (∑ k ∈ Finset.range (n + 1), A k) - 1 := by
      rw [Finset.sum_range_succ (fun k => A (k + 1)) n, htop, add_zero]
      rw [Finset.sum_range_succ' A n]
      have hA0 : A 0 = 1 := by rw [hA]; simp
      rw [hA0]; ring
    rw [hshift, ← Finset.mul_sum]
    ring

-- ============================================================
-- Section 3: Specialization q = 1 — Ordinary Binomial Theorem
-- ============================================================

/-- Setting `q = 1` collapses the q-binomial theorem to the ordinary binomial
    theorem `(1 + x)^n = ∑_k C(n,k) x^k` (over ℤ).  Here `[n,k]_1 = C(n,k)`. -/
theorem qBinomialTheorem_q_one (x : ℤ) (n : ℕ) :
    (1 + x) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * x ^ k := by
  have h := qBinomialTheorem (1 : ℤ) x n
  simp only [one_pow, mul_one, one_pow] at h
  rw [Finset.prod_const, Finset.card_range] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [qBinom_one hk]
  ring

-- ============================================================
-- Section 4: q-Pochhammer Form
-- ============================================================

/-- The q-Pochhammer symbol `(a ; q)_n = ∏_{i=0}^{n-1} (1 - a q^i)`. -/
noncomputable def qPoch {R : Type*} [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ i ∈ Finset.range n, (1 - a * q ^ i)

/-- The product side of the q-binomial theorem is the q-Pochhammer symbol
    `(-x ; q)_n`, exhibiting the RHS as its expansion.  This makes the
    "non-integer q-exponent" reading explicit: with `x = q^α` the left side is
    `(-q^α ; q)_n`, a genuine q-shifted factorial at a continuous parameter α. -/
theorem qPoch_neg_eq {R : Type*} [CommRing R] (q x : R) (n : ℕ) :
    qPoch (-x) q n =
      ∑ k ∈ Finset.range (n + 1), q ^ (k.choose 2) * qBinom q n k * x ^ k := by
  rw [qPoch]
  rw [← qBinomialTheorem q x n]
  apply Finset.prod_congr rfl
  intro i _
  ring

-- ============================================================
-- Section 5: Small-Case Sanity Checks (decide — no native_decide)
-- ============================================================

/-- `n = 2`, q = 2, x = 3 over ℤ:
    `(1 + 3)(1 + 3·2) = 4·7 = 28`, and the RHS is
    `q^0·1·1 + q^0·[2,1]_2·3 + q^1·[2,2]_2·9 = 1 + 3·3 + 2·9 = 1 + 9 + 18 = 28`. -/
theorem check_n2_q2_x3 :
    (∏ i ∈ Finset.range 2, (1 + (3 : ℤ) * 2 ^ i))
      = ∑ k ∈ Finset.range 3, (2 : ℤ) ^ (k.choose 2) * qBinom (2 : ℤ) 2 k * 3 ^ k := by
  rw [qBinomialTheorem]

/-- `n = 3`, q = 1, x = 1 over ℤ: `(1+1)^3 = 8 = ∑_k C(3,k) = 1+3+3+1`. -/
theorem check_n3_q1_x1 :
    (1 + (1 : ℤ)) ^ 3 = ∑ k ∈ Finset.range 4, ((3 : ℕ).choose k : ℤ) * 1 ^ k := by
  rw [qBinomialTheorem_q_one]

/-
  Summary

  Section 1 - choose_two_succ:        the triangular-number q-exponent recurrence
  Section 2 - qBinomialTheorem:       ∏_{i<n}(1 + x q^i) = ∑_k q^{C(k,2)} [n,k]_q x^k
                                      (free parameter x; CommRing)
  Section 3 - qBinomialTheorem_q_one: q = 1 recovers the ordinary binomial theorem
  Section 4 - qPoch / qPoch_neg_eq:   product = q-Pochhammer (-x ; q)_n
  Section 5 - decide sanity checks

  The headline `qBinomialTheorem` is the free-parameter generating identity that
  carries genuinely non-integer q-exponents (x = q^α, α ∉ ℕ) and from which the
  parent's natural-number q-Vandermonde convolution follows by x-coefficient
  extraction.  0 axioms / 0 sorries / no native_decide.
-/

end qBinomialTheoremProof
