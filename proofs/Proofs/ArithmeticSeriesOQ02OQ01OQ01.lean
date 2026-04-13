/-
  q-Vandermonde Identity

  Open Question (arithmetic-series-oq-02-oq-01-oq-01):
  "Prove the q-Vandermonde identity in Lean"

  The q-Vandermonde identity generalizes the classical Vandermonde convolution
  C(m+n, r) = ∑_k C(m, k) * C(n, r-k) to q-binomial coefficients:

    [m+n choose r]_q = ∑_{k=0}^{r} q^{k*(m+k-r)} * [m choose r-k]_q * [n choose k]_q

  Note: m+k-r and r-k use natural number subtraction (saturating at 0).
  Terms where m < r-k have [m choose r-k]_q = 0 by qBinom_eq_zero_of_lt, so
  the "wrong" q-exponent in those terms is harmless.

  **Proof**: Induction on m.
  - Base m=0: Only k=r contributes ([0 choose r-k]_q = 0 for k < r).
  - Step m+1, r+1:
    LHS Pascal: [m+n+1 choose r+1]_q = q^(r+1) * [m+n choose r+1]_q + [m+n choose r]_q
    By IH: = q^(r+1) * S(m,n,r+1) + S(m,n,r)

    RHS sum simplification uses:
    (1) Key ℕ identity: (m+1) + k - (r+1) = m + k - r  [by omega, since Nat.succ_sub_succ]
        So q^(k*(m+1+k-(r+1))) = q^(k*(m+k-r)) — the RHS sum becomes S(m+1,n,r+1) with
        exponents q^(k*(m+k-r)) * [m+1 choose r+1-k]_q * [n choose k]_q.
    (2) Pascal on [m+1 choose r+1-k]_q = q^(r+1-k) * [m choose r+1-k]_q + [m choose r-k]_q:
        Part A: q^(k*(m+k-r) + r+1-k) * [m choose r+1-k]_q = q^(r+1) * q^(k*(m+k-r-1)) * [m choose r+1-k]_q
                [using k*(m+k-r)+(r+1-k) = (r+1)+k*(m+k-r-1) as integers; for m+k<r+1, [m choose r+1-k]_q=0]
        Part B: q^(k*(m+k-r)) * [m choose r-k]_q * [n choose k]_q = S(m,n,r) term

  References:
  - V. Kac, P. Cheung, "Quantum Calculus" (Springer, 2002), Chapter 10
  - GaussianBinomial.qBinom from ArithmeticSeriesOQ02OQ01.lean
-/
import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ01

open GaussianBinomial Finset BigOperators

namespace qVandermondeProof

-- ============================================================
-- Section 1: Key Exponent Lemma for Part A
-- ============================================================

/-- Part A exponent identity: when m+k ≥ r+1,
    k*(m+k-r) + (r+1-k) = (r+1) + k*(m+k-(r+1)).
    This is the key algebraic identity enabling the inductive step.
    Proved by converting ℕ subtraction to ℤ arithmetic via `zify`. -/
lemma partA_exp (k r m : ℕ) (hm : r + 1 ≤ m + k) (hk : k ≤ r + 1) :
    k * (m + k - r) + (r + 1 - k) = (r + 1) + k * (m + k - (r + 1)) := by
  have h1 : r ≤ m + k := by omega
  zify [hm, hk, h1]
  ring

-- ============================================================
-- Section 2: Key ℕ Subtraction Identity
-- ============================================================

/-- The natural subtraction identity: m + 1 + k - (r + 1) = m + k - r.
    This follows from Nat.succ_sub_succ: (m+k+1) - (r+1) = m+k-r. -/
lemma succ_sub_succ_key (m k r : ℕ) : m + 1 + k - (r + 1) = m + k - r := by omega

-- ============================================================
-- Section 3: Part A Lemma
-- ============================================================

/-- Part A: The "q^(r-k) portion" of the Pascal expansion of [m+1 choose r+1-k]_q
    assembles into q^(r+1) * S(m, n, r+1). -/
lemma partA_eq {R : Type*} [CommRing R] (q : R) (m n r : ℕ) :
    ∑ k ∈ Finset.range (r + 2),
      q ^ (k * (m + k - r) + (r + 1 - k)) * qBinom q m (r + 1 - k) * qBinom q n k =
    q ^ (r + 1) * ∑ k ∈ Finset.range (r + 2),
      q ^ (k * (m + k - (r + 1))) * qBinom q m (r + 1 - k) * qBinom q n k := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  -- Case split: is m+k ≥ r+1?
  by_cases h : r + 1 ≤ m + k
  · -- Normal case: exponent identity holds, qBinom may be nonzero
    have heq : k * (m + k - r) + (r + 1 - k) = (r + 1) + k * (m + k - (r + 1)) :=
      partA_exp k r m h (by omega)
    rw [heq, pow_add]
    ring
  · -- Degenerate case: m+k < r+1, so r+1-k > m, so qBinom q m (r+1-k) = 0
    push_neg at h
    have hlt : m < r + 1 - k := by omega
    have hzero : qBinom q m (r + 1 - k) = 0 :=
      qBinom_eq_zero_of_lt q (by omega)
    simp [hzero]

-- ============================================================
-- Section 4: Part B Lemma
-- ============================================================

/-- Part B: The "[m choose r-k] portion" of the Pascal expansion uses the
    exponent identity m+1+k-(r+1) = m+k-r (in ℕ, by omega), giving back the S(m, n, r) sum. -/
lemma partB_eq_ih {R : Type*} [CommRing R] (q : R) (m n r : ℕ)
    (IH : qBinom q (m + n) r =
      ∑ k ∈ Finset.range (r + 1), q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k) :
    ∑ k ∈ Finset.range (r + 1),
      q ^ (k * (m + 1 + k - (r + 1))) * qBinom q m (r - k) * qBinom q n k =
    qBinom q (m + n) r := by
  rw [IH]
  apply Finset.sum_congr rfl
  intro k _
  -- key: m + 1 + k - (r + 1) = m + k - r in ℕ by succ_sub_succ
  have : m + 1 + k - (r + 1) = m + k - r := by omega
  rw [this]

-- ============================================================
-- Section 5: Pascal Expansion of Sum
-- ============================================================

/-- The key inductive step: expand [m+1 choose r+1-k]_q via Pascal to split
    the S(m+1, n, r+1) sum into Part A and Part B. -/
lemma sum_split_pascal {R : Type*} [CommRing R] (q : R) (m n r : ℕ) :
    ∑ k ∈ Finset.range (r + 2),
      q ^ (k * (m + k - r)) * qBinom q (m + 1) (r + 1 - k) * qBinom q n k =
    ∑ k ∈ Finset.range (r + 2),
      q ^ (k * (m + k - r) + (r + 1 - k)) * qBinom q m (r + 1 - k) * qBinom q n k +
    ∑ k ∈ Finset.range (r + 1),
      q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k := by
  -- For each k, expand qBinom q (m+1) (r+1-k) via Pascal's rule:
  -- k ≤ r: qBinom q (m+1) (r+1-k) = q^(r+1-k) * qBinom q m (r+1-k) + qBinom q m (r-k)
  -- k = r+1: qBinom q (m+1) 0 = 1, no Part B term
  have expand : ∀ k ∈ Finset.range (r + 2),
      q ^ (k * (m + k - r)) * qBinom q (m + 1) (r + 1 - k) * qBinom q n k =
      q ^ (k * (m + k - r) + (r + 1 - k)) * qBinom q m (r + 1 - k) * qBinom q n k +
      if k ≤ r then q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k else 0 := by
    intro k hk
    simp only [Finset.mem_range] at hk
    by_cases hkr : k ≤ r
    · simp only [hkr, ite_true]
      have hpascal : qBinom q (m + 1) (r + 1 - k) =
          q ^ (r + 1 - k) * qBinom q m (r + 1 - k) + qBinom q m (r - k) := by
        rw [show r + 1 - k = (r - k) + 1 from by omega]
        exact qBinom_succ_succ q m (r - k)
      rw [hpascal, pow_add]; ring
    · push_neg at hkr
      have hkeq : k = r + 1 := by omega
      subst hkeq
      have hnotleq : ¬(r + 1 ≤ r) := by omega
      simp only [hnotleq, ite_false, add_zero]
      have h0 : r + 1 - (r + 1) = 0 := by omega
      rw [h0, qBinom_zero_right, qBinom_zero_right]
      ring
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib]
  congr 1
  -- Simplify indicator sum over range(r+2) to a plain sum over range(r+1)
  rw [Finset.sum_range_succ]
  have hnotleq : ¬(r + 1 ≤ r) := by omega
  simp only [hnotleq, ite_false, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have hkr : k ≤ r := by omega
  simp only [hkr, ite_true]

-- ============================================================
-- Section 6: Main Theorem
-- ============================================================

/-- **q-Vandermonde Identity** (arithmetic-series-oq-02-oq-01-oq-01):
    [m+n choose r]_q = ∑_{k=0}^{r} q^{k*(m+k-r)} * [m choose r-k]_q * [n choose k]_q

    Proof by induction on m. The base m=0 reduces to [n choose r]_q directly.
    The step m+1 uses q-Pascal on the LHS and Pascal + Part A/B lemmas on the RHS. -/
theorem qVandermonde {R : Type*} [CommRing R] (q : R) (m n r : ℕ) :
    qBinom q (m + n) r =
    ∑ k ∈ Finset.range (r + 1),
      q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k := by
  induction m generalizing n r with
  | zero =>
    -- Base: m = 0. Only k = r contributes.
    simp only [zero_add]
    symm
    rw [Finset.sum_eq_single r]
    · -- k = r term
      simp
    · -- All k < r terms are 0
      intro k hk hkr
      simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
      have hrkpos : 0 < r - k := by omega
      obtain ⟨l, hl⟩ : ∃ l, r - k = l + 1 := ⟨r - k - 1, by omega⟩
      rw [hl, qBinom_zero_succ]
      ring
    · -- r is in range
      simp [Finset.mem_range]
  | succ m ih =>
    cases r with
    | zero =>
      -- r = 0: both sides are 1
      simp [qBinom_zero_right]
    | succ r =>
      -- r + 1: apply q-Pascal to LHS
      rw [show m + 1 + n = (m + n) + 1 from by ring]
      rw [qBinom_succ_succ]
      -- LHS = q^(r+1) * qBinom q (m+n) (r+1) + qBinom q (m+n) r
      rw [ih n (r + 1), ih n r]
      -- RHS: need to show the (m+1) sum = q^(r+1) * (m sum at r+1) + (m sum at r)
      -- Use the key identity: m + 1 + k - (r + 1) = m + k - r in ℕ
      have hexp : ∀ k : ℕ, k * (m + 1 + k - (r + 1)) = k * (m + k - r) := fun k => by
        congr 1; omega
      simp_rw [hexp]
      -- Now we have ∑ k, q^(k*(m+k-r)) * qBinom q (m+1) (r+1-k) * qBinom q n k
      -- Split into Part A + Part B
      rw [show ∑ k ∈ Finset.range (r + 1 + 1),
          q ^ (k * (m + k - r)) * qBinom q (m + 1) (r + 1 - k) * qBinom q n k =
          q ^ (r + 1) * ∑ k ∈ Finset.range (r + 1 + 1),
            q ^ (k * (m + k - (r + 1))) * qBinom q m (r + 1 - k) * qBinom q n k +
          ∑ k ∈ Finset.range (r + 1),
            q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k from by
        rw [sum_split_pascal, partA_eq]]

end qVandermondeProof
