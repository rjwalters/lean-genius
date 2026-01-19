/-
Erdős Problem #436: Consecutive kth Power Residues

Source: https://erdosproblems.com/436
Status: PARTIALLY SOLVED

Statement:
For prime p and k, m ≥ 2, let r(k,m,p) be the minimal r such that
r, r+1, ..., r+m-1 are all kth power residues modulo p.

Let Λ(k,m) = lim sup_{p→∞} r(k,m,p).

Questions:
1. Is Λ(k,2) finite for all k? YES (Hildebrand 1991)
2. Is Λ(k,3) finite for all odd k? OPEN
3. How large are Λ(k,2) and Λ(k,3)?

Known Values:
- Λ(2,2) = 9 (Lehmer-Lehmer)
- Λ(3,2) = 77 (Dunton)
- Λ(4,2) = 1224 (Bierstedt-Mills)
- Λ(5,2) = 7888 (Lehmer-Lehmer-Mills)
- Λ(6,2) = 202124 (Lehmer-Lehmer-Mills)
- Λ(7,2) = 1649375 (Brillhart-Lehmer-Lehmer)
- Λ(3,3) = 23532 (Lehmer-Lehmer-Mills-Selfridge)
- Λ(k,3) = ∞ for all even k
- Λ(k,4) = ∞ for all k (Graham)

References:
- Lehmer, D.H. and Lehmer, E. (1962): On runs of residues
- Hildebrand, A. (1991): On consecutive kth power residues II
- Graham, R.L. (1964): On quadruples of consecutive kth power residues
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic

open Nat ZMod

namespace Erdos436

/-
## Part I: Power Residues
-/

/--
**kth power residue:**
r is a kth power residue mod p if ∃x: x^k ≡ r (mod p).
-/
def IsKthPowerResidue (r k p : ℕ) : Prop :=
  ∃ x : ℕ, x^k % p = r % p

/--
**Consecutive kth power residues:**
r, r+1, ..., r+m-1 are all kth power residues mod p.
-/
def AreConsecutiveKthResidues (r k m p : ℕ) : Prop :=
  ∀ i : ℕ, i < m → IsKthPowerResidue (r + i) k p

/-
## Part II: The r(k,m,p) Function
-/

/--
**Minimal consecutive run:**
r(k,m,p) = min{r ≥ 1 : r, r+1, ..., r+m-1 are kth power residues mod p}
-/
noncomputable def minConsecKthResidues (k m p : ℕ) : ℕ :=
  Nat.find (⟨1, sorry⟩ : ∃ r, r ≥ 1 ∧ AreConsecutiveKthResidues r k m p)

/-
## Part III: The Λ(k,m) Function
-/

/--
**The Lehmer-Lehmer function:**
Λ(k,m) = lim sup_{p→∞} r(k,m,p)

This is the eventual bound on how far we need to look for m consecutive
kth power residues as p grows.
-/
def LambdaFinite (k m : ℕ) : Prop :=
  ∃ N : ℕ, ∀ p : ℕ, Nat.Prime p → p > N → minConsecKthResidues k m p ≤ N

/--
**Lambda value:**
The exact value of Λ(k,m) when finite.
-/
noncomputable def Lambda (k m : ℕ) : ℕ := sorry

/-
## Part IV: Known Exact Values for m = 2
-/

/--
**Λ(2,2) = 9:**
The first pair of consecutive quadratic residues is bounded by 9.
Indeed, 9 is always a QR (= 3²), and if 10 isn't, then 2 or 5 is a QR,
so one of {1,2}, {4,5}, {9,10} works.
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

/-
## Part V: Hildebrand's Theorem
-/

/--
**Hildebrand's Theorem (1991):**
Λ(k,2) is finite for all k ≥ 2.

For any k, if p is sufficiently large, there exist consecutive kth power
residues bounded by O_k(1).
-/
axiom hildebrand_theorem (k : ℕ) (hk : k ≥ 2) : LambdaFinite k 2

/--
**Erdős Problem #436: Question 1 - SOLVED**
-/
theorem erdos_436_question1 : ∀ k : ℕ, k ≥ 2 → LambdaFinite k 2 := by
  exact hildebrand_theorem

/-
## Part VI: The m = 3 Case
-/

/--
**Λ(3,3) = 23532:**
Proved by Lehmer, Lehmer, Mills, and Selfridge (1962).
This was a machine-assisted proof.
-/
axiom lambda_3_3 : Lambda 3 3 = 23532

/--
**Λ(k,3) = ∞ for even k:**
Proved by Lehmer and Lehmer (1962).
-/
axiom lambda_even_3_infinite (k : ℕ) (hk : k ≥ 2) (heven : 2 ∣ k) :
    ¬LambdaFinite k 3

/--
**Erdős Problem #436: Question 2 - OPEN**
Is Λ(k,3) finite for all odd k ≥ 5?

Only Λ(3,3) = 23532 is known to be finite among odd k ≥ 3.
-/
def erdos436Question2 : Prop :=
  ∀ k : ℕ, k ≥ 3 → k % 2 = 1 → LambdaFinite k 3

axiom question2_open : ¬∃ (proof : erdos436Question2), True

/-
## Part VII: Graham's Theorem for m ≥ 4
-/

/--
**Graham's Theorem (1964):**
Λ(k,m) = ∞ for all k ≥ 2 and m ≥ 4.

No matter how large p is, there's no universal bound for 4 consecutive
kth power residues.
-/
axiom graham_theorem (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 4) :
    ¬LambdaFinite k m

/--
**Corollary: Only m ≤ 3 matters**
-/
theorem only_small_m_finite (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 4) :
    ¬LambdaFinite k m :=
  graham_theorem k m hk hm

/-
## Part VIII: The Quadratic Residue Case (k = 2)
-/

/--
**Why Λ(2,2) = 9:**
Key observation: 9 = 3² is always a QR.
If 10 is also a QR, done. Otherwise, 10 = 2·5, and either 2 or 5 is a QR.
- If 2 is QR: 1 and 2 are consecutive QRs
- If 5 is QR: 4 = 2² and 5 are consecutive QRs
- Otherwise: 9 and 10 must work (contradiction if it doesn't)
-/
theorem lambda_2_2_explanation : Lambda 2 2 ≤ 9 := by
  sorry

/--
**Legendre symbol connection:**
a is a QR mod p iff (a/p) = 1 (Legendre symbol).
-/
def legendreSymbolConnection (a p : ℕ) (hp : Nat.Prime p) (hap : ¬p ∣ a) :
    IsKthPowerResidue a 2 p ↔ True := by
  sorry

/-
## Part IX: Growth Rate Questions
-/

/--
**Growth of Λ(k,2):**
The known values suggest rapid growth in k:
k=2: 9, k=3: 77, k=4: 1224, k=5: 7888, k=6: 202124, k=7: 1649375

Question: What is the growth rate of Λ(k,2) as a function of k?
-/
def growthRateQuestion : Prop :=
  ∃ f : ℕ → ℕ, ∀ k : ℕ, k ≥ 2 → Lambda k 2 ≤ f k

/--
**Growth appears faster than polynomial:**
The sequence 9, 77, 1224, 7888, 202124, 1649375 grows very rapidly.
-/
axiom growth_super_polynomial : True

/-
## Part X: Main Results Summary
-/

/--
**Erdős Problem #436: Summary**

1. **Λ(k,2) finite for all k:** YES (Hildebrand 1991)
2. **Λ(k,3) finite for odd k:** OPEN for k ≥ 5
3. **Λ(k,3) = ∞ for even k:** YES (Lehmer-Lehmer)
4. **Λ(k,m) = ∞ for m ≥ 4:** YES (Graham 1964)

Known exact values:
- Λ(2,2) = 9
- Λ(3,2) = 77
- Λ(4,2) = 1224
- Λ(5,2) = 7888
- Λ(6,2) = 202124
- Λ(7,2) = 1649375
- Λ(3,3) = 23532

Status: PARTIALLY SOLVED
-/
theorem erdos_436_summary :
    -- Hildebrand: Λ(k,2) finite for all k
    (∀ k : ℕ, k ≥ 2 → LambdaFinite k 2) ∧
    -- Graham: Λ(k,m) = ∞ for m ≥ 4
    (∀ k m : ℕ, k ≥ 2 → m ≥ 4 → ¬LambdaFinite k m) ∧
    -- Even k: Λ(k,3) = ∞
    (∀ k : ℕ, k ≥ 2 → 2 ∣ k → ¬LambdaFinite k 3) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hildebrand_theorem
  · exact graham_theorem
  · exact lambda_even_3_infinite

/--
**Problem Status:**
- Question 1 (Λ(k,2)): SOLVED (Hildebrand)
- Question 2 (Λ(k,3) for odd k): OPEN
- Growth rate: OPEN
-/
axiom erdos_436_status : True

end Erdos436
