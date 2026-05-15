import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-
# q-Analog Binomial Coefficients (Gaussian Binomial Coefficients)

## What This Proves
The q-analog (or Gaussian) binomial coefficient [n choose k]_q is a polynomial in q
that generalizes the ordinary binomial coefficient C(n,k). When q = 1, the q-binomial
reduces to the ordinary binomial coefficient.

q-binomial coefficients arise naturally in:
- Counting subspaces of finite vector spaces over F_q
- Quantum group representations (the "q" in "quantum groups")
- q-series, basic hypergeometric series, and partition theory
- Combinatorics of lattice paths with weights

## Approach
- Define q-numbers [n]_q, q-factorials [n]_q!, and q-binomial coefficients [n choose k]_q
  over an arbitrary commutative ring R with parameter q : R
- Use the q-Pascal recurrence as the defining equation for q-binomials (avoids division)
- Prove key properties: boundary cases, geometric sum identity, product formula
- The specialization theorem [n,k]_1 = C(n,k) validates the generalization

## Status
- [x] q-number definition and properties
- [x] q-factorial definition and properties
- [x] q-binomial coefficient via q-Pascal recurrence
- [x] Boundary cases (k=0, k=n, k>n, k=1)
- [x] Geometric sum identity: (q-1)[n]_q = q^n - 1
- [x] q-number splitting: [a+b]_q = [a]_q + q^a · [b]_q
- [x] Specialization: q-numbers at q=1 give natural numbers
- [x] Specialization: q-factorials at q=1 give factorials
- [x] KEY: q-binomials at q=1 give ordinary binomial coefficients
- [x] Product formula: [n,k]_q · [k]_q! · [n-k]_q! = [n]_q!
- [x] Concrete verifications
- [x] Penultimate entry: [n+1 choose n]_q = [n+1]_q
- [x] Row absorption: [n,k]_q · [n-k]_q = [n,k+1]_q · [k+1]_q
- [x] SYMMETRY: [n,k]_q = [n,n-k]_q
- [x] Second q-Pascal: [n+1,k+1]_q = q^{n-k}·[n,k]_q + [n,k+1]_q
- [x] Column sum (q-hockey stick): ∑ q^{(k+1)(n-i)}·[i,k]_q = [n+1,k+1]_q
- [x] Classical hockey stick at q=1: ∑ C(i,k) = C(n+1,k+1)
- [x] Specialization at q=0: [n,k]_0 = 1 for k ≤ n

## Mathlib Dependencies
- `Mathlib.Data.Nat.Choose.Basic` : Ordinary binomial coefficients and Pascal's identity
- `Mathlib.Tactic` : Proof tactics (ring, push_cast, omega, etc.)

## Historical Note
q-analogs were introduced by Euler in his study of partitions and developed extensively
by Gauss (hence "Gaussian binomial coefficients"). The notation [n]_q for the q-number
1 + q + q² + ... + q^{n-1} reflects that as q → 1, [n]_q → n. The modern significance
of q-binomial coefficients stems from:
1. Gauss (1808): counting subspaces of vector spaces over finite fields F_q
2. Quantum groups (Drinfeld & Jimbo, 1985): q is the deformation parameter
3. Partition theory: connections to Rogers-Ramanujan identities

## Wiedijk's 100 Theorems: Extension of #58
-/

namespace QBinomialCoefficients

open Nat

variable {R : Type*} [CommRing R]

-- ============================================================
-- Part I: q-Numbers
-- ============================================================

/-- The q-analog of a natural number: [n]_q = 1 + q + q² + ... + q^{n-1}.
    When q = 1, this gives the natural number n.
    When q is a prime power, [n]_q = (q^n - 1)/(q - 1). -/
def qNumber (q : R) : ℕ → R
  | 0 => 0
  | n + 1 => 1 + q * qNumber q n

@[simp] theorem qNumber_zero (q : R) : qNumber q 0 = 0 := rfl

@[simp] theorem qNumber_one (q : R) : qNumber q 1 = 1 := by
  simp [qNumber]

/-- Recurrence: [n+1]_q = 1 + q · [n]_q. -/
theorem qNumber_succ (q : R) (n : ℕ) :
    qNumber q (n + 1) = 1 + q * qNumber q n := rfl

/-- [2]_q = 1 + q. -/
theorem qNumber_two (q : R) : qNumber q 2 = 1 + q := by
  simp [qNumber]

/-- **Geometric Sum Identity**: (q - 1) · [n]_q = q^n - 1.
    This is the algebraic identity underlying the classical formula
    [n]_q = (q^n - 1)/(q - 1) for invertible (q - 1). -/
theorem qNumber_geometric (q : R) : ∀ n : ℕ,
    (q - 1) * qNumber q n = q ^ n - 1
  | 0 => by simp
  | n + 1 => by
    rw [qNumber_succ, pow_succ]
    have : (q - 1) * (1 + q * qNumber q n) =
           (q - 1) + q * ((q - 1) * qNumber q n) := by ring
    rw [this, qNumber_geometric q n]; ring

/-- **Specialization at q = 1**: [n]_1 = n (as an element of R).
    q-numbers reduce to ordinary natural numbers when q = 1. -/
theorem qNumber_at_one : ∀ n : ℕ, qNumber (1 : R) n = (n : R)
  | 0 => by simp
  | n + 1 => by
    rw [qNumber_succ, one_mul, qNumber_at_one n]; push_cast; ring

/-- **q-Number Splitting**: [a + b]_q = [a]_q + q^a · [b]_q.
    The q-number of a sum splits into the first a terms of the
    geometric series plus q^a times the next b terms. -/
theorem qNumber_add (q : R) : ∀ (a b : ℕ),
    qNumber q (a + b) = qNumber q a + q ^ a * qNumber q b
  | 0, _ => by simp
  | a + 1, b => by
    rw [show a + 1 + b = (a + b) + 1 from by omega,
        qNumber_succ, qNumber_add q a b, qNumber_succ, pow_succ]; ring

-- ============================================================
-- Part II: q-Factorials
-- ============================================================

/-- The q-factorial: [n]_q! = [1]_q · [2]_q · ... · [n]_q.
    When q = 1, this gives the ordinary factorial n!. -/
def qFactorial (q : R) : ℕ → R
  | 0 => 1
  | n + 1 => qNumber q (n + 1) * qFactorial q n

@[simp] theorem qFactorial_zero (q : R) : qFactorial q 0 = 1 := rfl

@[simp] theorem qFactorial_one (q : R) : qFactorial q 1 = 1 := by
  simp [qFactorial, qNumber]

/-- Recurrence: [n+1]_q! = [n+1]_q · [n]_q!. -/
theorem qFactorial_succ (q : R) (n : ℕ) :
    qFactorial q (n + 1) = qNumber q (n + 1) * qFactorial q n := rfl

/-- **Specialization at q = 1**: [n]_1! = n!.
    q-factorials reduce to ordinary factorials when q = 1. -/
theorem qFactorial_at_one : ∀ n : ℕ, qFactorial (1 : R) n = (n.factorial : R)
  | 0 => by simp
  | n + 1 => by
    rw [qFactorial_succ, qNumber_at_one, qFactorial_at_one n,
        Nat.factorial_succ, Nat.cast_mul]

-- ============================================================
-- Part III: q-Binomial Coefficients (Gaussian Binomial Coefficients)
-- ============================================================

/-- The q-binomial coefficient (Gaussian binomial coefficient) [n choose k]_q.
    Defined via the q-Pascal recurrence:
      [n+1 choose k+1]_q = [n choose k]_q + q^{k+1} · [n choose k+1]_q

    Key interpretations:
    - Number of k-dimensional subspaces of F_q^n (when q is a prime power)
    - Structure constant in quantum group representations
    - Polynomial in q with non-negative integer coefficients -/
def qBinom (q : R) : ℕ → ℕ → R
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

/-- [n choose 0]_q = 1 for all n. -/
@[simp] theorem qBinom_zero_right (q : R) (n : ℕ) : qBinom q n 0 = 1 := by
  cases n <;> rfl

/-- [0 choose k+1]_q = 0. -/
@[simp] theorem qBinom_zero_succ (q : R) (k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/-- **q-Pascal Identity**: [n+1 choose k+1]_q = [n choose k]_q + q^{k+1} · [n choose k+1]_q.
    The factor q^{k+1} (rather than 1 in the classical case) is what makes
    q-binomials polynomials in q rather than constants. -/
theorem qBinom_pascal (q : R) (n k : ℕ) :
    qBinom q (n + 1) (k + 1) = qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/-- [n choose k]_q = 0 when k > n (same as classical). -/
theorem qBinom_eq_zero_of_lt (q : R) : ∀ (n k : ℕ), n < k → qBinom q n k = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [qBinom_pascal,
        qBinom_eq_zero_of_lt q n k (by omega),
        qBinom_eq_zero_of_lt q n (k + 1) (by omega)]; simp

/-- [n choose n]_q = 1 for all n and q (same as classical). -/
@[simp] theorem qBinom_self (q : R) : ∀ n : ℕ, qBinom q n n = 1
  | 0 => rfl
  | n + 1 => by
    rw [qBinom_pascal, qBinom_self q n,
        qBinom_eq_zero_of_lt q n (n + 1) (by omega)]; simp

/-- [n choose 1]_q = [n]_q: choosing one element gives the q-number.
    When q is a prime power, this counts the 1-dimensional subspaces
    (i.e., points of projective space PG(n-1, q)). -/
theorem qBinom_one_right (q : R) : ∀ n : ℕ, qBinom q n 1 = qNumber q n
  | 0 => by simp [qNumber]
  | n + 1 => by
    rw [qBinom_pascal, qBinom_zero_right, qBinom_one_right q n, qNumber_succ]; ring

-- ============================================================
-- Part IV: The Key Specialization Theorem
-- ============================================================

/-- **Specialization at q = 1**: [n choose k]_1 = C(n, k).

    This is the fundamental consistency theorem: when q = 1, the q-binomial
    coefficient reduces to the ordinary binomial coefficient. This validates
    the q-binomial as a genuine generalization of C(n,k).

    The proof uses the q-Pascal recurrence (with q=1, the factor q^{k+1}
    becomes 1) and the classical Pascal identity C(n+1,k+1) = C(n,k) + C(n,k+1). -/
theorem qBinom_at_one : ∀ (n k : ℕ), qBinom (1 : R) n k = (Nat.choose n k : R)
  | _, 0 => by simp
  | 0, k + 1 => by
    rw [qBinom_zero_succ, Nat.choose_eq_zero_of_lt (by omega : 0 < k + 1)]; simp
  | n + 1, k + 1 => by
    rw [qBinom_pascal, one_pow, one_mul,
        qBinom_at_one n k, qBinom_at_one n (k + 1),
        Nat.choose_succ_succ]; push_cast; ring

-- ============================================================
-- Part V: Product Formula
-- ============================================================

/-- **Product Formula**: [n choose k]_q · [k]_q! · [n-k]_q! = [n]_q!.

    This is the q-analog of the fundamental identity C(n,k) · k! · (n-k)! = n!.
    Equivalently: [n choose k]_q = [n]_q! / ([k]_q! · [n-k]_q!) when the
    q-factorials are invertible. -/
theorem qBinom_product (q : R) : ∀ (n k : ℕ), k ≤ n →
    qBinom q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n
  | _, 0, _ => by simp
  | 0, _ + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    have hkn : k ≤ n := by omega
    rw [show n + 1 - (k + 1) = n - k from by omega, qBinom_pascal, qFactorial_succ q k]
    -- Algebraic rearrangement to isolate IH terms
    have step1 :
      (qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)) *
      (qNumber q (k + 1) * qFactorial q k) * qFactorial q (n - k) =
      qNumber q (k + 1) * (qBinom q n k * qFactorial q k * qFactorial q (n - k)) +
      q ^ (k + 1) * qBinom q n (k + 1) *
      (qNumber q (k + 1) * qFactorial q k) * qFactorial q (n - k) := by ring
    rw [step1, qBinom_product q n k hkn]
    -- Handle second term by case split
    rcases Nat.eq_or_lt_of_le hkn with hkeq | hklt
    · -- Case k = n: second term vanishes since [n choose n+1]_q = 0
      rw [hkeq, qBinom_eq_zero_of_lt q n (n + 1) (by omega), show n - n = 0 from by omega]
      simp [qFactorial_succ]
    · -- Case k < n: use IH at (n, k+1)
      have hk1n : k + 1 ≤ n := hklt
      -- Decompose [n-k]_q! = [n-k]_q · [n-(k+1)]_q!
      have h_decomp : qFactorial q (n - k) =
          qNumber q (n - k) * qFactorial q (n - (k + 1)) := by
        have h1 : n - (k + 1) + 1 = n - k := by omega
        calc qFactorial q (n - k)
            = qFactorial q (n - (k + 1) + 1) := by rw [h1]
          _ = qNumber q (n - (k + 1) + 1) * qFactorial q (n - (k + 1)) :=
              qFactorial_succ q (n - (k + 1))
          _ = qNumber q (n - k) * qFactorial q (n - (k + 1)) := by rw [h1]
      rw [h_decomp]
      -- Rearrange to expose IH at (n, k+1)
      have step2 :
        q ^ (k + 1) * qBinom q n (k + 1) *
        (qNumber q (k + 1) * qFactorial q k) *
        (qNumber q (n - k) * qFactorial q (n - (k + 1))) =
        q ^ (k + 1) * qNumber q (n - k) *
        (qBinom q n (k + 1) * (qNumber q (k + 1) * qFactorial q k) *
         qFactorial q (n - (k + 1))) := by ring
      rw [step2]
      -- Reassemble qFactorial q (k+1) and apply IH
      rw [show qNumber q (k + 1) * qFactorial q k = qFactorial q (k + 1) from
          (qFactorial_succ q k).symm]
      rw [qBinom_product q n (k + 1) hk1n]
      -- Factor out qFactorial q n and use q-number splitting
      have step3 :
        qNumber q (k + 1) * qFactorial q n +
        q ^ (k + 1) * qNumber q (n - k) * qFactorial q n =
        (qNumber q (k + 1) + q ^ (k + 1) * qNumber q (n - k)) * qFactorial q n := by ring
      rw [step3, ← qNumber_add, show k + 1 + (n - k) = n + 1 from by omega]
      exact (qFactorial_succ q n).symm

-- ============================================================
-- Part VI: Concrete Verifications
-- ============================================================

section Verifications
variable (q : R)

/-- [2 choose 1]_q = 1 + q. -/
example : qBinom q 2 1 = 1 + q := by
  rw [qBinom_one_right, qNumber_succ, qNumber_succ, qNumber_zero]; ring

/-- [3 choose 1]_q = 1 + q + q². -/
example : qBinom q 3 1 = 1 + q + q ^ 2 := by
  rw [qBinom_one_right]; simp [qNumber]; ring

/-- [3 choose 2]_q = 1 + q + q² (same as [3 choose 1]_q, illustrating symmetry). -/
example : qBinom q 3 2 = 1 + q + q ^ 2 := by
  simp [qBinom]

/-- [4 choose 2]_q = 1 + q + 2q² + q³ + q⁴ = (1+q)(1+q+q²) (a "q-analog" of C(4,2)=6). -/
example : qBinom q 4 2 = 1 + q + 2 * q ^ 2 + q ^ 3 + q ^ 4 := by
  simp [qBinom]; ring

end Verifications

-- ============================================================
-- Part VII: Absorption Identity
-- ============================================================

/-- **q-Absorption Identity**:
    [n+1 choose k+1]_q · [k+1]_q = [n+1]_q · [n choose k]_q.

    This is the q-analog of the classical absorption identity
    C(n+1, k+1) · (k+1) = (n+1) · C(n, k), and is a fundamental
    tool in q-combinatorics. The proof uses induction on n,
    applying the q-Pascal recurrence at each step.

    Key algebraic steps in the inductive case:
    1. Expand qBinom(n+2, k+1) via Pascal
    2. Apply IH at (n, k) and (n, k-1) to simplify
    3. Recombine via Pascal backwards to close the induction -/
theorem qBinom_absorption (q : R) : ∀ (n k : ℕ), k ≤ n →
    qBinom q (n + 1) (k + 1) * qNumber q (k + 1) = qNumber q (n + 1) * qBinom q n k
  | 0, 0, _ => by simp [qBinom, qNumber]
  | n + 1, 0, _ => by
    simp [qBinom_one_right]
  | n + 1, k + 1, hk => by
    have hk' : k ≤ n := by omega
    rcases Nat.eq_or_lt_of_le (show k + 1 ≤ n + 1 from by omega) with hkeq | hklt
    · -- k + 1 = n + 1: both sides equal qNumber q (n+2)
      have hkn : k = n := by omega
      subst hkn
      simp [qBinom_self]
    · -- k + 1 < n + 1: general case
      have hk1 : k + 1 ≤ n := by omega
      have ih1 := qBinom_absorption q n k hk'
      have ih2 := qBinom_absorption q n (k + 1) hk1
      have pasc_n := qBinom_pascal q n k
      have qnum_k := qNumber_succ q (k + 1)
      have qnum_n := qNumber_succ q (n + 1)
      -- Expand qBinom and qNumber at the top level
      rw [qBinom_pascal q (n + 1) (k + 1), qnum_k, qnum_n]
      rw [qnum_k] at ih2
      -- Now all terms are in basic form; close by linear algebra
      linear_combination q * ih1 + q ^ (k + 2) * ih2 -
        q * qNumber q (n + 1) * pasc_n

/-- **q-Absorption at q = 1** verifies the classical identity:
    C(n+1, k+1) · (k+1) = (n+1) · C(n, k). -/
theorem absorption_at_one (n k : ℕ) (hk : k ≤ n) :
    Nat.choose (n + 1) (k + 1) * (k + 1) = (n + 1) * Nat.choose n k := by
  have h := qBinom_absorption (1 : ℤ) n k hk
  rw [qBinom_at_one, qBinom_at_one, qNumber_at_one, qNumber_at_one] at h
  exact_mod_cast h

-- ============================================================
-- Part VIII: Concrete Absorption Verifications
-- ============================================================

/-- Verification: [4,2]_q · [2]_q = [4]_q · [3,1]_q over ℤ at q = 2. -/
example : qBinom (2 : ℤ) 4 2 * qNumber (2 : ℤ) 2 = qNumber (2 : ℤ) 4 * qBinom (2 : ℤ) 3 1 := by
  native_decide

/-- Verification: [5,3]_q · [3]_q = [5]_q · [4,2]_q over ℤ at q = 2. -/
example : qBinom (2 : ℤ) 5 3 * qNumber (2 : ℤ) 3 = qNumber (2 : ℤ) 5 * qBinom (2 : ℤ) 4 2 := by
  native_decide

-- ============================================================
-- Part IX: Symmetry of q-Binomial Coefficients
-- ============================================================

/-- Adding q^n to [n]_q gives [n+1]_q: extends the geometric sum by one term. -/
theorem qNumber_add_pow (q : R) (n : ℕ) :
    qNumber q n + q ^ n = qNumber q (n + 1) := by
  rw [qNumber_succ]
  have h := qNumber_geometric q n
  linear_combination -h

/-- The penultimate entry: [n+1 choose n]_q = [n+1]_q.
    This is the q-analog of C(n+1, n) = n+1. -/
theorem qBinom_penult (q : R) : ∀ n : ℕ, qBinom q (n + 1) n = qNumber q (n + 1)
  | 0 => by simp [qBinom, qNumber]
  | n + 1 => by
    rw [qBinom_pascal, qBinom_self, mul_one, qBinom_penult q n, qNumber_add_pow]

/-- **Row Absorption Identity**: [n,k]_q · [n-k]_q = [n,k+1]_q · [k+1]_q.

    This relates adjacent entries in the same row of the q-Pascal triangle.
    The proof uses the q-Pascal recurrence to reduce to the inductive hypothesis,
    then applies q-number splitting [a+b]_q = [a]_q + q^a·[b]_q to show both
    sides equal [n-1,k]_q · [n]_q.

    This identity is the key tool for proving symmetry of q-binomials over
    arbitrary commutative rings (where cancellation is unavailable). -/
theorem qBinom_row_absorption (q : R) : ∀ (n k : ℕ), k + 1 ≤ n →
    qBinom q n k * qNumber q (n - k) = qBinom q n (k + 1) * qNumber q (k + 1)
  | 0, _, h => absurd h (by omega)
  | n + 1, k, hk => by
    rcases k with _ | k
    · -- k = 0: [n+1,0]·[n+1] = [n+1,1]·[1] = [n+1]
      simp [qBinom_zero_right, qBinom_one_right, qNumber_one]
    · -- k ≥ 1: k+1+1 ≤ n+1, so k+1 ≤ n
      rcases Nat.eq_or_lt_of_le (show k + 1 ≤ n from by omega) with hkeq | hklt
      · -- Boundary: k+1 = n, reduces to penultimate lemma
        subst hkeq
        rw [show k + 1 + 1 - (k + 1) = 1 from by omega]
        simp [qNumber_one, qBinom_self, qBinom_penult]
      · -- General: 1 ≤ k+1 < n, use IH at (n, k) and (n, k+1)
        have ih1 := qBinom_row_absorption q n k (by omega)
        have ih2 := qBinom_row_absorption q n (k + 1) (by omega)
        rw [show n + 1 - (k + 1) = n - k from by omega]
        rw [qBinom_pascal q n k, qBinom_pascal q n (k + 1)]
        -- Both sides reduce to qBinom q n (k+1) * qNumber q (n+1)
        -- via IH + q-number splitting
        have add1 : qNumber q (k + 1) + q ^ (k + 1) * qNumber q (n - k) =
            qNumber q (n + 1) := by
          rw [← qNumber_add]; congr 1; omega
        have add2 : qNumber q (k + 2) + q ^ (k + 2) * qNumber q (n - (k + 1)) =
            qNumber q (n + 1) := by
          rw [← qNumber_add]; congr 1; omega
        calc (qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)) * qNumber q (n - k)
            = qBinom q n k * qNumber q (n - k) +
              q ^ (k + 1) * qBinom q n (k + 1) * qNumber q (n - k) := by ring
          _ = qBinom q n (k + 1) * qNumber q (k + 1) +
              q ^ (k + 1) * qBinom q n (k + 1) * qNumber q (n - k) := by rw [ih1]
          _ = qBinom q n (k + 1) * (qNumber q (k + 1) +
              q ^ (k + 1) * qNumber q (n - k)) := by ring
          _ = qBinom q n (k + 1) * qNumber q (n + 1) := by rw [add1]
          _ = qBinom q n (k + 1) * (qNumber q (k + 2) +
              q ^ (k + 2) * qNumber q (n - (k + 1))) := by rw [add2]
          _ = qBinom q n (k + 1) * qNumber q (k + 2) +
              q ^ (k + 2) * qBinom q n (k + 1) * qNumber q (n - (k + 1)) := by ring
          _ = qBinom q n (k + 1) * qNumber q (k + 2) +
              q ^ (k + 2) * (qBinom q n (k + 2) * qNumber q (k + 2)) := by rw [mul_assoc, ih2]
          _ = (qBinom q n (k + 1) + q ^ (k + 2) * qBinom q n (k + 2)) *
              qNumber q (k + 2) := by ring

/-- **Symmetry**: [n,k]_q = [n,n-k]_q.

    The q-binomial coefficients are symmetric in k and n-k, generalizing
    the classical identity C(n,k) = C(n,n-k). Over an arbitrary commutative
    ring, this cannot be proved by "cancelling q-factorials" (zero divisors
    may exist). Instead, the proof combines:
    1. Induction on n with the q-Pascal recurrence,
    2. The row absorption identity to relate adjacent entries,
    3. The geometric sum formula to bridge power and q-number expressions.

    The key algebraic step reduces the symmetry condition to showing
    (q-1) · ([n,k]_q · [n-k]_q - [n,k+1]_q · [k+1]_q) = 0,
    which follows from row absorption. -/
theorem qBinom_symm (q : R) : ∀ (n k : ℕ), k ≤ n →
    qBinom q n k = qBinom q n (n - k)
  | _, 0, _ => by simp
  | 0, _ + 1, h => absurd h (by omega)
  | n + 1, k + 1, hk => by
    rw [show n + 1 - (k + 1) = n - k from by omega]
    rcases Nat.eq_or_lt_of_le (show k ≤ n from by omega) with rfl | hlt
    · simp -- k = n: both sides are 1
    · -- k < n, so n - k ≥ 1
      -- Expand LHS via Pascal
      rw [qBinom_pascal]
      -- Expand RHS via Pascal (rewrite n-k = (n-k-1)+1 first)
      conv_rhs => rw [show (n - k : ℕ) = (n - k - 1) + 1 from by omega]
      rw [qBinom_pascal]
      rw [show n - k - 1 + 1 = n - k from by omega]
      -- Apply symmetry IH to RHS terms
      have ih1 : qBinom q n (n - k - 1) = qBinom q n (k + 1) := by
        rw [qBinom_symm q n (n - k - 1) (by omega)]; congr 1; omega
      have ih2 : qBinom q n (n - k) = qBinom q n k := by
        rw [qBinom_symm q n (n - k) (by omega)]; congr 1; omega
      rw [ih1, ih2]
      -- Goal: qBinom q n k + q^(k+1) * qBinom q n (k+1)
      --     = qBinom q n (k+1) + q^(n-k) * qBinom q n k
      -- Follows from row absorption + geometric identity
      have ra := qBinom_row_absorption q n k (by omega)
      have g1 := qNumber_geometric q (n - k)
      have g2 := qNumber_geometric q (k + 1)
      linear_combination qBinom q n k * g1 - qBinom q n (k + 1) * g2 - (q - 1) * ra

-- ============================================================
-- Part X: Second q-Pascal Recurrence
-- ============================================================

/-- **Second q-Pascal Identity**:
    [n+1 choose k+1]_q = q^{n-k} · [n choose k]_q + [n choose k+1]_q.

    While the first q-Pascal identity weights the upper term by q^{k+1},
    this form weights the lower term by q^{n-k}. The two forms reflect
    the two ways of decomposing a subspace counting problem.

    Proof: Apply symmetry to reduce to the first Pascal identity. -/
theorem qBinom_pascal' (q : R) (n k : ℕ) (hk : k + 1 ≤ n + 1) :
    qBinom q (n + 1) (k + 1) = q ^ (n - k) * qBinom q n k + qBinom q n (k + 1) := by
  -- Use symmetry: [n+1,k+1] = [n+1,n-k]
  rw [qBinom_symm q (n + 1) (k + 1) hk, show n + 1 - (k + 1) = n - k from by omega]
  -- Apply first Pascal to [n+1,n-k]:
  -- Need n-k = (n-k-1)+1 or n-k = 0
  rcases Nat.eq_or_lt_of_le (show k ≤ n from by omega) with rfl | hlt
  · -- k = n (rfl substitutes n with k): [k+1, k-k] = q^(k-k) · [k,k] + [k,k+1] = 1 + 0
    simp [qBinom_eq_zero_of_lt q k (k + 1) (by omega)]
  · -- k < n: n-k ≥ 1, so write n-k = (n-k-1)+1
    conv_lhs => rw [show (n - k : ℕ) = (n - k - 1) + 1 from by omega]
    rw [qBinom_pascal, show n - k - 1 + 1 = n - k from by omega]
    -- [n,n-k-1] = [n,k+1] by symmetry
    rw [qBinom_symm q n (n - k - 1) (by omega), show n - (n - k - 1) = k + 1 from by omega]
    -- [n,n-k] = [n,k] by symmetry
    rw [qBinom_symm q n (n - k) (by omega), show n - (n - k) = k from by omega]
    ring

-- ============================================================
-- Part XI: Column Sum Identity (q-Hockey Stick)
-- ============================================================

/-- **q-Column Sum Identity** (q-Hockey Stick):
    ∑_{i=0}^{n} q^{(k+1)(n-i)} · [i choose k]_q = [n+1 choose k+1]_q.

    This is the q-analog of the classical hockey stick identity
    ∑_{i=k}^{n} C(i,k) = C(n+1, k+1). When q = 1, each term
    q^{(k+1)(n-i)} becomes 1 and we recover the classical sum.

    When q is a prime power, this counts (k+1)-dimensional subspaces
    of F_q^{n+1} by the position of a distinguished basis vector.

    The proof uses induction on n, splitting off the last term and
    factoring q^{k+1} from the remaining sum to apply the IH,
    then closing with the q-Pascal recurrence. -/
theorem qBinom_column_sum (q : R) (k : ℕ) : ∀ n : ℕ,
    ∑ i ∈ Finset.range (n + 1),
      q ^ ((k + 1) * (n - i)) * qBinom q i k = qBinom q (n + 1) (k + 1)
  | 0 => by
    simp only [Nat.zero_add, Finset.sum_range_one, Nat.sub_zero, Nat.mul_zero, pow_zero, one_mul]
    cases k with
    | zero => simp [qBinom]
    | succ k => simp [qBinom]
  | n + 1 => by
    -- Split off the last term (i = n+1)
    rw [Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.mul_zero, pow_zero, one_mul]
    -- Factor q^{k+1} from the remaining sum
    have h_factor : ∀ i ∈ Finset.range (n + 1),
        q ^ ((k + 1) * (n + 1 - i)) * qBinom q i k =
        q ^ (k + 1) * (q ^ ((k + 1) * (n - i)) * qBinom q i k) := by
      intro i hi
      have hi' : i ≤ n := by
        simp only [Finset.mem_range] at hi; omega
      -- v4.26.0: omega no longer treats `(k+1) * (n - i)` and `(k+1) * (n+1 - i)` as
      -- comparable atoms across nonlinear multiplication. Bridge via Nat.mul_succ.
      have h_exp : (k + 1) * (n + 1 - i) = (k + 1) * (n - i) + (k + 1) := by
        have h_sub : n + 1 - i = (n - i) + 1 := by omega
        rw [h_sub, Nat.mul_succ]
      rw [h_exp, pow_add]; ring
    rw [Finset.sum_congr rfl h_factor, ← Finset.mul_sum]
    -- Apply IH and Pascal
    rw [qBinom_column_sum q k n, add_comm]
    exact (qBinom_pascal q (n + 1) k).symm

/-- **Classical Hockey Stick at q=1**: ∑_{i=0}^{n} C(i,k) = C(n+1, k+1).
    Derived from the q-column sum identity by specializing at q = 1. -/
theorem hockey_stick_at_one (k n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), Nat.choose i k = Nat.choose (n + 1) (k + 1) := by
  have h := qBinom_column_sum (1 : ℤ) k n
  simp only [one_pow, one_mul] at h
  simp only [qBinom_at_one] at h
  exact_mod_cast h

-- ============================================================
-- Part XII: Specialization at q = 0
-- ============================================================

/-- **Specialization at q = 0**: [n choose k]_0 = 1 when k ≤ n.

    At q = 0, the q-Pascal recurrence becomes [n+1,k+1]_0 = [n,k]_0 + 0 = [n,k]_0
    since 0^{k+1} = 0. By induction, every q-binomial with k ≤ n equals 1.
    This reflects the fact that over F_1 (the "field with one element"),
    there is exactly one k-dimensional subspace of any n-dimensional space. -/
theorem qBinom_at_zero : ∀ (n k : ℕ), k ≤ n → qBinom (0 : R) n k = 1
  | _, 0, _ => by simp
  | 0, _ + 1, h => absurd h (by omega)
  | n + 1, k + 1, h => by
    rw [qBinom_pascal, qBinom_at_zero n k (by omega),
        zero_pow (by omega : k + 1 ≠ 0), zero_mul, add_zero]

-- ============================================================
-- Part XII: Symmetry Verifications
-- ============================================================

section SymmetryVerifications
variable (q : R)

/-- Symmetry verification: [4 choose 1]_q = [4 choose 3]_q. -/
example : qBinom q 4 1 = qBinom q 4 3 :=
  qBinom_symm q 4 1 (by omega)

/-- Symmetry verification: [5 choose 2]_q = [5 choose 3]_q. -/
example : qBinom q 5 2 = qBinom q 5 3 :=
  qBinom_symm q 5 2 (by omega)

/-- Row absorption verification: [4,1]·[3] = [4,2]·[2] over ℤ at q=2. -/
example : qBinom (2 : ℤ) 4 1 * qNumber (2 : ℤ) 3 = qBinom (2 : ℤ) 4 2 * qNumber (2 : ℤ) 2 := by
  native_decide

end SymmetryVerifications

-- ============================================================
-- Part XIII: q-Vandermonde Identity
-- ============================================================

/-- **q-Vandermonde Identity** (q-Chu-Vandermonde convolution):
    ∑_{j=0}^{k} q^{(k-j)(m-j)} · [m,j]_q · [n,k-j]_q = [m+n,k]_q.

    This is the q-analog of the classical Vandermonde identity
    ∑ C(m,j)·C(n,k-j) = C(m+n,k). When q is a prime power, it counts
    k-dimensional subspaces of F_q^{m+n} by decomposing according to
    their intersection with a fixed m-dimensional subspace.

    The proof uses induction on m. The key step expands [m+1,j+1]_q
    via the q-Pascal recurrence, splits the sum, applies the inductive
    hypothesis at (m,k) and (m,k+1), and closes with Pascal. -/
theorem qBinom_vandermonde (q : R) (n : ℕ) : ∀ (m k : ℕ),
    ∑ j ∈ Finset.range (k + 1),
      q ^ ((k - j) * (m - j)) * qBinom q m j * qBinom q n (k - j) = qBinom q (m + n) k
  | 0, k => by
    rw [zero_add]
    rw [Finset.sum_eq_single 0
      (fun j _ hj => by
        rcases j with _ | j
        · exact absurd rfl hj
        · simp [qBinom_zero_succ])
      (fun h => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ k)) h)]
    simp
  | m + 1, 0 => by
    simp
  | m + 1, k + 1 => by
    have ih_k := qBinom_vandermonde q n m k
    have ih_k1 := qBinom_vandermonde q n m (k + 1)
    -- Rewrite target via Pascal: [m+1+n,k+1] = [m+n,k] + q^{k+1}·[m+n,k+1]
    conv_rhs =>
      rw [show m + 1 + n = (m + n) + 1 from by omega, qBinom_pascal]
    rw [← ih_k, ← ih_k1]
    -- Peel off j=0 from LHS: ∑_{j=0}^{k+1} f(j) = f(0) + ∑_{j=0}^{k} f(j+1)
    rw [show k + 1 + 1 = 1 + (k + 1) from by omega, Finset.sum_range_add,
        Finset.sum_range_one]
    -- v4.26.0: `f 0` collapses to `q^... * 1 * qBinom q n (k+1)`; use `mul_one`
    -- (not `one_mul`) to drop the right-factor `* 1` so LHS f_0 matches RHS f_0
    -- after `h_exp0` and `congr 1` cancellation later.
    simp only [Nat.sub_zero, qBinom_zero_right, mul_one]
    -- Simplify subscripts in the shifted sum. v4.26.0: `Finset.sum_range_add` indexes
    -- the shifted sum as `f (1 + x)`, so h_simp's LHS is stated in `1 + j` form to match.
    -- The RHS produces `j + 1` form so subsequent `h_pascal` rewrites apply.
    have h_simp : ∀ j ∈ Finset.range (k + 1),
        q ^ ((k + 1 - (1 + j)) * (m + 1 - (1 + j))) *
          qBinom q (m + 1) (1 + j) * qBinom q n (k + 1 - (1 + j)) =
        q ^ ((k - j) * (m - j)) * qBinom q (m + 1) (j + 1) * qBinom q n (k - j) := by
      intro j hj
      have hj' : j < k + 1 := Finset.mem_range.mp hj
      -- v4.26.0: nested `congr 1` over a*b multiplication leaves omega with nonlinear
      -- atoms it can't relate. Discharge each linear equality independently.
      have h1 : k + 1 - (1 + j) = k - j := by omega
      have h2 : m + 1 - (1 + j) = m - j := by omega
      have h3 : (1 + j : ℕ) = j + 1 := Nat.add_comm 1 j
      rw [h1, h2, h3]
    rw [Finset.sum_congr rfl h_simp]
    -- Apply Pascal: [m+1,j+1] = [m,j] + q^{j+1}·[m,j+1]
    have h_pascal : ∀ j ∈ Finset.range (k + 1),
        q ^ ((k - j) * (m - j)) * qBinom q (m + 1) (j + 1) * qBinom q n (k - j) =
        q ^ ((k - j) * (m - j)) * qBinom q m j * qBinom q n (k - j) +
        q ^ ((k - j) * (m - j) + (j + 1)) * qBinom q m (j + 1) * qBinom q n (k - j) := by
      intro j _
      -- v4.26.0: `rw [add_mul]` no longer finds `(a + b) * c` under left-assoc `X * (a + b) * Y`.
      -- Split via pow_add on RHS, then close via ring distributivity.
      rw [qBinom_pascal q m j, pow_add q ((k - j) * (m - j)) (j + 1)]
      ring
    rw [Finset.sum_congr rfl h_pascal, Finset.sum_add_distrib]
    -- Now: q^{(k+1)(m+1)}·[n,k+1] + sum_first + sum_second = sum_k + q^{k+1}·sum_{k+1}
    -- where sum_first is exactly sum_k.
    -- Combine q^{(k+1)(m+1)}·[n,k+1] + sum_second into q^{k+1}·sum_{k+1}
    -- by expanding sum_{k+1} = (j=0 term) + ∑_{j=0}^{k} (shifted terms)
    conv_rhs =>
      arg 2; arg 2
      -- The earlier `rw [show k + 1 + 1 = 1 + (k + 1) ...]` already rewrote globally,
      -- so the RHS sum is `range (1 + (k+1))` here. No additional show-rewrite needed.
      rw [Finset.sum_range_add, Finset.sum_range_one]
      -- v4.26.0: `f 0` collapses to `q^... * 1 * qBinom q n (k+1)`; use `mul_one`
      -- (not `one_mul`) to remove the right-factor `* 1` so `h_exp0`'s pattern matches.
      simp only [Nat.sub_zero, qBinom_zero_right, mul_one]
    -- v4.26.0: bare `rw [mul_add]` fires on the Nat-level `(k+1) * (m+1) → (k+1)*m + (k+1)*1`
    -- in the LHS exponent before reaching the intended `q^(k+1) * (b + c)` on RHS. Pin the
    -- first argument so only the ring-level distribution at `q^(k+1)` fires.
    rw [mul_add (q ^ (k + 1))]
    -- RHS: sum_k + (q^{k+1}·q^{(k+1)m}·[n,k+1] + q^{k+1}·∑ shifted)
    -- First: q^{k+1}·q^{(k+1)m} = q^{(k+1)(m+1)}
    have h_exp0 : q ^ (k + 1) * (q ^ ((k + 1) * m) * qBinom q n (k + 1)) =
        q ^ ((k + 1) * (m + 1)) * qBinom q n (k + 1) := by
      rw [← mul_assoc, ← pow_add]; congr 1; ring
    rw [h_exp0]
    -- v4.26.0 rewrite: instead of `ring_nf + congr 1` (which leaves an unsolvable
    -- subgoal post-Mathlib commutativity normalization), prove the key sum identity
    -- directly and use `linear_combination` to close.
    -- Goal at this point: f_0 + sum_A + sum_B = sum_C + f_0 + q^(k+1) * sum_offset
    -- where sum_A = sum_C and sum_B = q^(k+1) * sum_offset.
    -- key's RHS uses `(1 + j)` form (not `(j + 1)`) so it matches the
    -- conv_rhs above whose `Finset.sum_range_add` expansion produced
    -- the shifted-sum indices in `1 + j` form. `ring` cannot bridge
    -- alpha-equivalent sums whose body indices differ syntactically.
    have key : ∑ j ∈ Finset.range (k + 1),
          q ^ ((k - j) * (m - j) + (j + 1)) * qBinom q m (j + 1) * qBinom q n (k - j) =
        q ^ (k + 1) * ∑ j ∈ Finset.range (k + 1),
          q ^ ((k + 1 - (1 + j)) * (m - (1 + j))) * qBinom q m (1 + j) *
            qBinom q n (k + 1 - (1 + j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < k + 1 := Finset.mem_range.mp hj
      -- Normalize `1 + j` → `j + 1` inside the RHS body so the per-j case
      -- analysis matches the same form on both sides.
      rw [show (1 + j : ℕ) = j + 1 from Nat.add_comm 1 j]
      by_cases hjm : j + 1 ≤ m
      · -- Exponents match when j+1 ≤ m
        -- v4.26.0: omega can't bridge `(k-j) * (m-j)` and `(k-j) * (m-(j+1))`
        -- because they're nonlinear atoms. Bridge manually via Nat.mul_succ.
        have h_exp : (k - j) * (m - j) + (j + 1) = (k + 1) + (k - j) * (m - (j + 1)) := by
          have hmj : m - j = (m - (j + 1)) + 1 := by omega
          rw [hmj, Nat.mul_succ]; omega
        have h_idx : k + 1 - (j + 1) = k - j := by omega
        rw [show q ^ ((k - j) * (m - j) + (j + 1)) = q ^ ((k + 1) + (k - j) * (m - (j + 1)))
          from by rw [h_exp], pow_add, h_idx]
        ring
      · -- When j+1 > m, [m,j+1] = 0 so both sides vanish
        have hzero : qBinom q m (j + 1) = 0 := qBinom_eq_zero_of_lt q m (j + 1) (by omega)
        simp [hzero]
    linear_combination key

/-- **Classical Vandermonde at q=1**: ∑ C(m,j)·C(n,k-j) = C(m+n,k).
    Derived from the q-Vandermonde identity by specializing at q = 1. -/
theorem vandermonde_at_one (m n k : ℕ) :
    ∑ j ∈ Finset.range (k + 1),
      Nat.choose m j * Nat.choose n (k - j) = Nat.choose (m + n) k := by
  have h := qBinom_vandermonde (1 : ℤ) n m k
  simp only [one_pow, one_mul, qBinom_at_one] at h
  exact_mod_cast h

end QBinomialCoefficients

-- ============================================================
-- Integer specialization verifications (outside namespace to avoid variable {R})
-- ============================================================

open QBinomialCoefficients in
/-- Verification: [5 choose 2]_1 = C(5,2) = 10 (over ℤ). -/
example : qBinom (1 : ℤ) 5 2 = 10 := by native_decide

open QBinomialCoefficients in
/-- Verification: [6 choose 3]_1 = C(6,3) = 20 (over ℤ). -/
example : qBinom (1 : ℤ) 6 3 = 20 := by native_decide

open QBinomialCoefficients in
/-- Verification: [10 choose 4]_1 = C(10,4) = 210 (over ℤ). -/
example : qBinom (1 : ℤ) 10 4 = 210 := by native_decide

open QBinomialCoefficients in
/-- Subspace counting: over F_2, the number of 1-dim subspaces of F_2^3 is [3]_2 = 7. -/
example : qNumber (2 : ℤ) 3 = 7 := by simp [qNumber]

open QBinomialCoefficients in
/-- Over F_3, the number of 1-dim subspaces of F_3^4 is [4]_3 = 40. -/
example : qNumber (3 : ℤ) 4 = 40 := by simp [qNumber]

open QBinomialCoefficients in
/-- Over F_2, [3 choose 1]_2 = 7 (points of PG(2,2), the Fano plane). -/
example : qBinom (2 : ℤ) 3 1 = 7 := by
  rw [qBinom_one_right]; simp [qNumber]

open QBinomialCoefficients in
/-- Over F_2, [4 choose 2]_2 = 35 (2-dim subspaces of F_2^4). -/
example : qBinom (2 : ℤ) 4 2 = 35 := by simp [qBinom]
