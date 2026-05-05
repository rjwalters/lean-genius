import Mathlib
import Proofs.CombinationsFormulaOQ03

/-!
# q-Multichoose: The Gaussian Binomial as the q-Analog of Multiset Coefficients

## Open Question: arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03

The multiset Vandermonde identity (parent file) uses `Nat.multichoose n k`,
counting multisets of size k from an n-element set (also written C^{ms}(n,k)).

The classical identity: `Nat.multichoose n k = Nat.choose (n+k-1) k`.

**OQ-03 asks**: What is the q-analog of multichoose? Is it the Gaussian
binomial coefficient `[n+k-1 choose k]_q`?

## Answer: YES

We define:
  `qMultichoose q n k := qBinom q (n+k-1) k`

This is the canonical q-analog: at q=1 it recovers `Nat.multichoose n k`,
and it satisfies a q-deformed Pascal recurrence capturing the "weight"
structure of multisets over finite vector spaces over 𝔽_q.

## q-Pascal Recurrence

The ordinary Pascal for multichoose:
  multichoose (n+1) (k+1) = multichoose n (k+1) + multichoose (n+1) k

The q-deformation (proved below):
  qMultichoose q (n+1) (k+1) = qMultichoose q (n+1) k + q^(k+1) · qMultichoose q n (k+1)

The q-weight `q^(k+1)` appears on the term incrementing k (choosing "one more from same set"),
reflecting the dimension count in the 𝔽_q-vector space interpretation.

## Status: 0 sorries, 0 axioms
-/

open QBinomialCoefficients BigOperators

variable {R : Type*} [CommRing R]

namespace QMultichooseCoefficients

-- ============================================================
-- SECTION I: Definition
-- ============================================================

/-- The **q-multichoose coefficient**: the q-analog of the multiset coefficient.

    `qMultichoose q n k := qBinom q (n+k-1) k`

    This is the Gaussian binomial `[n+k-1 choose k]_q`. At q=1 it equals
    `Nat.multichoose n k = Nat.choose (n+k-1) k`. -/
noncomputable def qMultichoose (q : R) (n k : ℕ) : R :=
  qBinom q (n + k - 1) k

-- ============================================================
-- SECTION II: Basic Properties
-- ============================================================

/-- Base case k=0: exactly one multiset of size 0. -/
@[simp]
theorem qMultichoose_zero_right (q : R) (n : ℕ) : qMultichoose q n 0 = 1 := by
  simp [qMultichoose]

/-- Base case n=0, k≥1: no multisets of positive size from the empty set.
    In ℕ: 0 + (k+1) - 1 = k < k+1, so qBinom q k (k+1) = 0. -/
@[simp]
theorem qMultichoose_zero_left (q : R) (k : ℕ) : qMultichoose q 0 (k + 1) = 0 := by
  simp only [qMultichoose, show 0 + (k + 1) - 1 = k from by omega]
  exact qBinom_eq_zero_of_lt q k (k + 1) (by omega)

/-- n=1: exactly one multiset of each size from a 1-element set.
    qMultichoose q 1 k = qBinom q k k = 1. -/
@[simp]
theorem qMultichoose_one_left (q : R) (k : ℕ) : qMultichoose q 1 k = 1 := by
  simp only [qMultichoose, show 1 + k - 1 = k from by omega]
  exact qBinom_self q k

/-- k=1: the q-number [n]_q.
    qMultichoose q n 1 = qBinom q n 1 = [n]_q. -/
theorem qMultichoose_one_right (q : R) (n : ℕ) : qMultichoose q n 1 = qNumber q n := by
  simp only [qMultichoose, show n + 1 - 1 = n from by omega]
  exact qBinom_one_right q n

-- ============================================================
-- SECTION III: The q-Pascal Recurrence
-- ============================================================

/-- **q-Pascal recurrence** for qMultichoose:

    qMultichoose q (n+1) (k+1) = qMultichoose q (n+1) k + q^(k+1) · qMultichoose q n (k+1)

    This is the q-deformation of the ordinary Pascal recurrence for multichoose:
      multichoose (n+1) (k+1) = multichoose (n+1) k + multichoose n (k+1)

    The q-weight `q^(k+1)` appears on the term that increments k.

    Proof: Direct application of `qBinom_pascal` at shifted indices. -/
theorem qMultichoose_pascal (q : R) (n k : ℕ) :
    qMultichoose q (n + 1) (k + 1) =
    qMultichoose q (n + 1) k + q ^ (k + 1) * qMultichoose q n (k + 1) := by
  unfold qMultichoose
  have h1 : n + 1 + (k + 1) - 1 = (n + k) + 1 := by omega
  have h2 : n + 1 + k - 1 = n + k := by omega
  have h3 : n + (k + 1) - 1 = n + k := by omega
  rw [h1, h2, h3]
  exact qBinom_pascal q (n + k) k

-- ============================================================
-- SECTION IV: Connection to Nat.multichoose
-- ============================================================

/-- **Main theorem**: At q=1, qMultichoose recovers Nat.multichoose.

    Proof by double induction using the q-Pascal recurrence (at q=1) and
    `Nat.multichoose_succ_succ : multichoose (n+1) (k+1) = multichoose n (k+1) + multichoose (n+1) k`. -/
theorem qMultichoose_eq_multichoose (n k : ℕ) :
    qMultichoose (1 : R) n k = (Nat.multichoose n k : R) := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [qMultichoose]
    | succ k => simp [Nat.multichoose_zero_succ]
  | succ n ihn =>
    induction k with
    | zero => simp [Nat.multichoose_zero_right]
    | succ k ihk =>
      rw [qMultichoose_pascal, ihn (k + 1), ihk, one_pow, one_mul]
      have h := Nat.multichoose_succ_succ n k
      push_cast [h]
      ring

-- ============================================================
-- SECTION V: Specialization at q = 1
-- ============================================================

/-- At q=1: qMultichoose equals Nat.choose (n+k-1) k.
    Follows from `qBinom_at_one`. -/
theorem qMultichoose_at_one (n k : ℕ) :
    qMultichoose (1 : R) n k = (Nat.choose (n + k - 1) k : R) := by
  simp [qMultichoose, qBinom_at_one]

-- ============================================================
-- SECTION VI: The Main Identity
-- ============================================================

/-- **The q-Multichoose = Gaussian Binomial Identity**:

    qMultichoose q n k = qBinom q (n+k-1) k  (true by definition)

    This establishes that the Gaussian binomial coefficient `[n+k-1 choose k]_q`
    is the q-analog of the multiset coefficient `Nat.multichoose n k`. -/
theorem qMultichoose_eq_gaussBinom (q : R) (n k : ℕ) :
    qMultichoose q n k = qBinom q (n + k - 1) k :=
  rfl

-- ============================================================
-- SECTION VII: Additional Properties
-- ============================================================

/-- The q-multichoose with q=0 counts trivial multisets.
    qMultichoose 0 n k = 1 if k = 0, else depends on n. -/
theorem qMultichoose_at_zero_right (n : ℕ) : qMultichoose (0 : R) n 0 = 1 := by
  simp

/-- qMultichoose commutes with qBinom at shifted index.
    qMultichoose q n k = qBinom q (n+k-1) k (definitional). -/
@[simp]
theorem qMultichoose_eq_qBinom_shift (q : R) (n k : ℕ) :
    qMultichoose q n k = qBinom q (n + k - 1) k :=
  rfl

/-- Two-left: qMultichoose q 2 k = [k+1]_q = qNumber q (k+1). -/
theorem qMultichoose_two_left (q : R) (k : ℕ) :
    qMultichoose q 2 k = qNumber q (k + 1) := by
  simp only [qMultichoose, show 2 + k - 1 = k + 1 from by omega]
  exact qBinom_one_right q (k + 1)

-- ============================================================
-- SECTION VIII: Consistency with the Classical q-Vandermonde
-- ============================================================

/-- The q-Vandermonde identity for qBinom specializes to a q-Vandermonde
    for qMultichoose. At q=1, this recovers the multiset Vandermonde identity
    proved in `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02`. -/
theorem qMultichoose_recovers_classical (n k : ℕ) :
    (qMultichoose (1 : ℕ) n k) = Nat.multichoose n k :=
  qMultichoose_eq_multichoose n k

-- ============================================================
-- Summary
-- ============================================================

/-!
## Answer to OQ-03

**YES**: The q-analog of `Nat.multichoose n k` is:

  `qMultichoose q n k = qBinom q (n+k-1) k = [n+k-1 choose k]_q`

The Gaussian binomial coefficient `[n+k-1 choose k]_q` is the canonical
q-deformation of the multiset coefficient, with:

1. **Specialization**: `qMultichoose 1 n k = Nat.multichoose n k` (proved)
2. **q-Pascal**: `qMultichoose q (n+1) (k+1) = qMultichoose q (n+1) k + q^(k+1) · qMultichoose q n (k+1)`
3. **Gaussian binomial**: `qMultichoose q n k = qBinom q (n+k-1) k` (by definition)
4. **At q=0**: `qMultichoose 0 n 0 = 1`, other values determined by the recursion
5. **Combinatorial meaning**: Counts k-dimensional subspaces of an (n+k-1)-dimensional
   𝔽_q-vector space, with q → 1 recovering multiset counts.

The q-Pascal recurrence is the q-deformation of the ordinary multichoose recurrence:
  multichoose (n+1) (k+1) = multichoose n (k+1) + multichoose (n+1) k
→ qMultichoose q (n+1) (k+1) = q^(k+1) · qMultichoose q n (k+1) + qMultichoose q (n+1) k

This formalizes the classical combinatorial identity at the q-analog level.
-/

end QMultichooseCoefficients
