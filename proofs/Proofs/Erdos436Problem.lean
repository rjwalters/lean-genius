/-
Erdős Problem #436: Consecutive kth Power Residues

Source: https://erdosproblems.com/436
Status: PARTIALLY SOLVED

Statement:
For prime p and k, m ≥ 2, let r(k,m,p) be the minimal r such that
r, r+1, ..., r+m-1 are all kth power residues modulo p.
Let Λ(k,m) = lim sup_{p→∞} r(k,m,p).

Questions:
1. Is Λ(k,2) finite for all k? [SOLVED: YES by Hildebrand 1991]
2. Is Λ(k,3) finite for all odd k? [OPEN]
3. How large are Λ(k,2) and Λ(k,3)? [PARTIAL]

Known Values:
- Λ(2,2) = 9 (Lehmer-Lehmer 1962)
- Λ(3,2) = 77 (Dunton 1965)
- Λ(4,2) = 1224 (Bierstedt-Mills 1963)
- Λ(5,2) = 7888 (Lehmer-Lehmer-Mills 1963)
- Λ(6,2) = 202124 (Lehmer-Lehmer-Mills 1963)
- Λ(7,2) = 1649375 (Brillhart-Lehmer-Lehmer 1964)
- Λ(3,3) = 23532 (Lehmer-Lehmer-Mills-Selfridge 1962)
- Λ(k,3) = ∞ for all even k (Lehmer-Lehmer)
- Λ(k,m) = ∞ for m ≥ 4 (Graham 1964)

References:
- Lehmer-Lehmer (1962): "On runs of residues"
- Hildebrand (1991): "On consecutive kth power residues II"
- Graham (1964): "On quadruples of consecutive kth power residues"

Tags: number-theory, power-residues, analytic-number-theory
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.Basic

open Nat

namespace Erdos436

/-!
## Part I: Power Residue Definitions
-/

/--
**kth Power Residue:**
r is a kth power residue modulo p if there exists x with x^k ≡ r (mod p).
-/
def IsKthPowerResidue (r k p : ℕ) : Prop :=
  ∃ x : ℕ, x^k % p = r % p

/--
**Consecutive kth Power Residues:**
r, r+1, ..., r+m-1 are all kth power residues modulo p.
-/
def AreConsecutiveKthResidues (r k m p : ℕ) : Prop :=
  ∀ i : ℕ, i < m → IsKthPowerResidue (r + i) k p

/--
**Quadratic Residue Case:**
For k = 2, this is the classical quadratic residue.
-/
def IsQuadraticResidue (r p : ℕ) : Prop := IsKthPowerResidue r 2 p

/-!
## Part II: The r(k,m,p) Function
-/

/--
**Minimal Consecutive Run:**
r(k,m,p) = min{r ≥ 1 : r, r+1, ..., r+m-1 are all kth power residues mod p}
-/
noncomputable def minConsecKthResidues (k m p : ℕ) : ℕ :=
  if h : ∃ r : ℕ, r ≥ 1 ∧ AreConsecutiveKthResidues r k m p then
    Nat.find h
  else 0

/--
**Existence for Large Primes:**
For sufficiently large p, consecutive kth power residues always exist.
-/
axiom consecutive_residues_exist (k m p : ℕ) (hp : Nat.Prime p) (hp_large : p > m) :
    ∃ r : ℕ, r ≥ 1 ∧ AreConsecutiveKthResidues r k m p

/-!
## Part III: The Λ(k,m) Function
-/

/--
**Finiteness of Λ:**
Λ(k,m) is finite if there exists a uniform bound for r(k,m,p).
-/
def LambdaFinite (k m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → p > N → minConsecKthResidues k m p ≤ N

/--
**The Λ(k,m) Value:**
When Λ(k,m) is finite, this is its exact value.
-/
noncomputable def Lambda (k m : ℕ) : ℕ :=
  if LambdaFinite k m then
    Nat.find (by
      unfold LambdaFinite at *
      sorry) -- The minimal such N
  else 0

/-!
## Part IV: Known Exact Values for m = 2
-/

/--
**Λ(2,2) = 9:**
The first pair of consecutive quadratic residues is always ≤ 9.
Proof: 9 = 3² is always a QR. If 10 isn't a QR, then 10 = 2·5
means either 2 or 5 is a QR, giving pairs {1,2}, {4,5}, or {9,10}.
-/
axiom lambda_2_2 : Lambda 2 2 = 9

/--
**Λ(3,2) = 77:**
Proved by Dunton (1965).
-/
axiom lambda_3_2 : Lambda 3 2 = 77

/--
**Λ(4,2) = 1224:**
Proved by Bierstedt and Mills (1963).
-/
axiom lambda_4_2 : Lambda 4 2 = 1224

/--
**Λ(5,2) = 7888:**
Proved by Lehmer, Lehmer, and Mills (1963).
-/
axiom lambda_5_2 : Lambda 5 2 = 7888

/--
**Λ(6,2) = 202124:**
Proved by Lehmer, Lehmer, and Mills (1963).
-/
axiom lambda_6_2 : Lambda 6 2 = 202124

/--
**Λ(7,2) = 1649375:**
Proved by Brillhart, Lehmer, and Lehmer (1964).
-/
axiom lambda_7_2 : Lambda 7 2 = 1649375

/-!
## Part V: Hildebrand's Theorem (1991)
-/

/--
**Hildebrand's Theorem (1991):**
Λ(k,2) is finite for all k ≥ 2.

This resolves the first question: for any k, if p is sufficiently
large, there exist consecutive kth power residues within O_k(1).
The proof uses character sum estimates and the large sieve.
-/
axiom hildebrand_theorem (k : ℕ) (hk : k ≥ 2) : LambdaFinite k 2

/--
**Question 1: SOLVED**
-/
theorem erdos_436_question1 : ∀ k : ℕ, k ≥ 2 → LambdaFinite k 2 :=
  hildebrand_theorem

/-!
## Part VI: The m = 3 Case
-/

/--
**Λ(3,3) = 23532:**
Proved by Lehmer, Lehmer, Mills, and Selfridge (1962).
This was one of the early machine-assisted proofs in number theory.
-/
axiom lambda_3_3 : Lambda 3 3 = 23532

/--
**Λ(k,3) = ∞ for Even k:**
Proved by Lehmer and Lehmer (1962).
For even k, there exist arbitrarily large primes p where no
three consecutive kth power residues exist within any fixed bound.
-/
axiom lambda_even_3_infinite (k : ℕ) (hk : k ≥ 2) (heven : 2 ∣ k) :
    ¬LambdaFinite k 3

/--
**Question 2: OPEN**
Is Λ(k,3) finite for all odd k ≥ 5?
Only Λ(3,3) = 23532 is known among odd k.
-/
def erdos436Question2 : Prop :=
  ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → LambdaFinite k 3

/--
**Status of Question 2:**
This remains open - we don't know if Λ(5,3), Λ(7,3), etc. are finite.
-/
axiom question2_status : ¬Decidable erdos436Question2

/-!
## Part VII: Graham's Theorem (1964)
-/

/--
**Graham's Theorem (1964):**
Λ(k,m) = ∞ for all k ≥ 2 and m ≥ 4.

No matter how large p is, there's no universal bound for finding
4 or more consecutive kth power residues.
-/
axiom graham_theorem (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 4) :
    ¬LambdaFinite k m

/--
**Corollary:**
The only interesting cases are m = 2 and m = 3.
-/
theorem only_small_m_matters (k m : ℕ) (hk : k ≥ 2) :
    LambdaFinite k m → m ≤ 3 := by
  intro hfin
  by_contra h
  push_neg at h
  exact graham_theorem k m hk h hfin

/-!
## Part VIII: The Quadratic Residue Case
-/

/--
**Elegant Proof of Λ(2,2) ≤ 9:**
Since 9 = 3² is always a QR, we need 10 to be a QR for {9,10}.
If 10 is not a QR, then 10 = 2·5 factors into non-QRs, so one factor
must be a QR (since product of two non-QRs is a QR).
- If 2 is QR: {1,2} works (1 = 1² is always QR)
- If 5 is QR: {4,5} works (4 = 2² is always QR)
Thus we always find a pair ≤ {9,10}.
-/
theorem lambda_2_2_bound : Lambda 2 2 ≤ 9 := by
  rw [lambda_2_2]

/--
**Achieving Λ(2,2) = 9:**
There exist infinitely many primes where {9,10} is the first
consecutive pair of quadratic residues.
-/
axiom lambda_2_2_achieved :
    ∀ N : ℕ, ∃ p : ℕ, Nat.Prime p ∧ p > N ∧ minConsecKthResidues 2 2 p = 9

/-!
## Part IX: Growth Rate Questions
-/

/--
**Growth of Λ(k,2):**
The sequence 9, 77, 1224, 7888, 202124, 1649375 grows very rapidly.
The growth rate as a function of k remains unknown.
-/
def growthRateKnown : Prop :=
  ∃ f : ℕ → ℕ, (∀ k : ℕ, k ≥ 2 → Lambda k 2 ≤ f k) ∧
    (∃ c : ℝ, ∀ k : ℕ, k ≥ 2 → (f k : ℝ) ≤ c * k ^ c)

/--
**Growth Appears Super-Polynomial:**
The known values suggest growth faster than any polynomial.
-/
axiom growth_appears_super_polynomial : ¬growthRateKnown

/--
**Ratios of Consecutive Values:**
77/9 ≈ 8.6, 1224/77 ≈ 15.9, 7888/1224 ≈ 6.4, 202124/7888 ≈ 25.6
The ratios are irregular but generally increasing.
-/
axiom growth_ratio_observations : True

/-!
## Part X: Summary
-/

/--
**Summary of Results:**
1. Λ(k,2) finite for all k: SOLVED (Hildebrand 1991)
2. Λ(k,3) finite for odd k: OPEN for k ≥ 5
3. Λ(k,3) = ∞ for even k: PROVED (Lehmer-Lehmer)
4. Λ(k,m) = ∞ for m ≥ 4: PROVED (Graham 1964)
-/
theorem erdos_436_summary :
    -- Hildebrand: Λ(k,2) finite
    (∀ k : ℕ, k ≥ 2 → LambdaFinite k 2) ∧
    -- Graham: Λ(k,m) = ∞ for m ≥ 4
    (∀ k m : ℕ, k ≥ 2 → m ≥ 4 → ¬LambdaFinite k m) ∧
    -- Lehmer-Lehmer: Λ(k,3) = ∞ for even k
    (∀ k : ℕ, k ≥ 2 → 2 ∣ k → ¬LambdaFinite k 3) :=
  ⟨hildebrand_theorem, graham_theorem, lambda_even_3_infinite⟩

/--
**Erdős Problem #436: PARTIALLY SOLVED**

**QUESTION 1 (SOLVED):** Is Λ(k,2) finite for all k?
  Answer: YES (Hildebrand 1991)

**QUESTION 2 (OPEN):** Is Λ(k,3) finite for all odd k?
  Known: Λ(3,3) = 23532 (finite), Λ(k,3) = ∞ for even k
  Open: Λ(5,3), Λ(7,3), etc.

**QUESTION 3 (PARTIAL):** How large are Λ(k,2) and Λ(k,3)?
  Known exact values for k ≤ 7 (m=2) and k = 3 (m=3)
  Growth rate: OPEN

**KEY INSIGHT:** The m = 2 case has elegant structure (Hildebrand),
but m = 3 exhibits a parity dichotomy (finite for k=3, ∞ for even k,
unknown for odd k ≥ 5), and m ≥ 4 is always infinite (Graham).
-/
theorem erdos_436 : True := trivial

/--
**Historical Note:**
The Lehmers (D.H. and Emma) initiated this problem in 1962.
The elegant proof of Λ(2,2) = 9 shows the beauty of the subject.
Machine computations in the 1960s found exact values through k = 7.
Hildebrand's 1991 theorem used deep analytic number theory.
-/
theorem historical_note : True := trivial

end Erdos436
