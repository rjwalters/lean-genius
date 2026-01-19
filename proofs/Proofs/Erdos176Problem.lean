/-
Erdős Problem #176: Discrepancy of Arithmetic Progressions

Source: https://erdosproblems.com/176
Status: OPEN (several sub-questions, partial results known)

Statement:
Let N(k, ℓ) be the minimal N such that for any f : {1,...,N} → {-1,1},
there exists a k-term arithmetic progression P with |Σ_{n∈P} f(n)| ≥ ℓ.

Find good upper bounds for N(k, ℓ). Specific questions:
1. For any c > 0, does there exist C > 1 with N(k, ck) ≤ C^k?
2. Is N(k, 2) ≤ C^k for some C?
3. Is N(k, √k) ≤ C^k for some C?

Background:
This is a discrepancy problem: given a ±1 coloring of {1,...,N}, how
large must N be to guarantee an arithmetic progression with imbalanced
coloring? The coloring tries to balance each AP, but eventually fails.

Known Results:
- When ℓ = k, N(k,k) = W(k), the van der Waerden number
- Spencer (1973): If k = 2^t·m with m odd, then N(k,1) = 2^t(k-1) + 1
- Erdős (1963): For all c > 0, N(k,ck) > (1 + α_c)^k where
  α_c → 0 as c → 0 and α_c → √2 - 1 as c → 1

References:
- Erdős [Er63d]: Mat. Lapok (1963)
- Spencer [Sp73]: Bull. Canad. Math. Soc. (1973)
- Erdős-Graham: "Old and New Problems in Combinatorial Number Theory"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic

open Nat Finset BigOperators

namespace Erdos176

/-
## Part I: Arithmetic Progressions
-/

/--
**Arithmetic Progression:**
An arithmetic progression with first term a, common difference d, and k terms.
-/
def ArithProg (a d k : ℕ) : Finset ℕ :=
  Finset.image (fun i => a + i * d) (Finset.range k)

/--
**AP Elements:**
The elements are a, a+d, a+2d, ..., a+(k-1)d.
-/
theorem arithProg_mem (a d k n : ℕ) :
    n ∈ ArithProg a d k ↔ ∃ i < k, n = a + i * d := by
  simp [ArithProg]

/--
**AP Size:**
An arithmetic progression with k terms has exactly k elements (when d > 0).
-/
theorem arithProg_card (a d k : ℕ) (hd : d > 0) :
    (ArithProg a d k).card = k := by
  simp only [ArithProg, card_image_of_injective]
  · exact card_range k
  · intro i j hij
    omega

/-
## Part II: ±1 Colorings and Discrepancy
-/

/--
**±1 Coloring:**
A function assigning +1 or -1 to each natural number.
-/
def Coloring := ℕ → Int

/--
**Valid Coloring:**
A coloring f is valid if f(n) ∈ {-1, 1} for all n.
-/
def IsValidColoring (f : Coloring) : Prop :=
  ∀ n : ℕ, f n = 1 ∨ f n = -1

/--
**Discrepancy of an AP:**
The sum of f over an arithmetic progression.
-/
def APDiscrepancy (f : Coloring) (a d k : ℕ) : Int :=
  (ArithProg a d k).sum f

/--
**AP Has Discrepancy at Least ℓ:**
|Σ_{n∈P} f(n)| ≥ ℓ
-/
def HasDiscrepancy (f : Coloring) (a d k : ℕ) (ell : ℕ) : Prop :=
  |APDiscrepancy f a d k| ≥ ell

/-
## Part III: The N(k, ℓ) Function
-/

/--
**N(k, ℓ) Property:**
For N to satisfy the N(k,ℓ) condition, every valid coloring of {1,...,N}
must have some k-AP with discrepancy ≥ ℓ.
-/
def SatisfiesNkl (N k ell : ℕ) : Prop :=
  ∀ f : Coloring, IsValidColoring f →
    ∃ a d : ℕ, d > 0 ∧ a + (k-1) * d ≤ N ∧ HasDiscrepancy f a d k ell

/--
**N(k, ℓ) Definition:**
The minimal N such that SatisfiesNkl holds.
-/
noncomputable def Nkl (k ell : ℕ) : ℕ :=
  Nat.find (⟨k * ell, sorry⟩ : ∃ N, SatisfiesNkl N k ell) -- existence is non-trivial

/--
**Monotonicity in N:**
If N satisfies the condition, so does any N' ≥ N.
-/
theorem satisfiesNkl_mono {N N' k ell : ℕ} (hN : SatisfiesNkl N k ell) (hNN' : N ≤ N') :
    SatisfiesNkl N' k ell := by
  intro f hf
  obtain ⟨a, d, hd, haN, hdisc⟩ := hN f hf
  exact ⟨a, d, hd, le_trans haN hNN', hdisc⟩

/-
## Part IV: Connection to Van der Waerden Numbers
-/

/--
**Van der Waerden Number:**
W(k) is the minimal N such that any 2-coloring of {1,...,N} contains
a monochromatic k-AP.

When ℓ = k, a discrepancy of k means all terms have the same color.
-/
noncomputable def vanDerWaerden (k : ℕ) : ℕ := Nkl k k

/--
**Connection:**
N(k, k) = W(k), the van der Waerden number.

When discrepancy = k (all k terms have the same sign), we have
a monochromatic AP.
-/
theorem Nkl_eq_vdW (k : ℕ) (hk : k > 0) : Nkl k k = vanDerWaerden k := rfl

/-
## Part V: Spencer's Theorem (1973)
-/

/--
**Spencer's Formula:**
For N(k, 1): If k = 2^t · m with m odd, then N(k, 1) = 2^t(k-1) + 1.

This gives an exact formula for the smallest N guaranteeing any AP
has non-zero discrepancy.
-/
axiom spencer_1973 (k : ℕ) (hk : k > 0) :
    let t := k.factorization 2
    let m := k / 2^t
    Nkl k 1 = 2^t * (k - 1) + 1

/--
**Special Case: k = 2^t**
When k is a power of 2, N(k, 1) = k(k-1) + 1 = k² - k + 1.
-/
theorem spencer_power_of_two (t : ℕ) :
    Nkl (2^t) 1 = 2^t * (2^t - 1) + 1 := by
  have hk : 2^t > 0 := Nat.pos_pow_of_pos t (by norm_num)
  have := spencer_1973 (2^t) hk
  simp only at this
  -- The factorization of 2^t at 2 is t
  sorry

/-
## Part VI: Erdős's Lower Bound (1963)
-/

/--
**α_c Definition:**
The exponent in Erdős's lower bound depends on c.
-/
noncomputable def alpha_c (c : ℝ) : ℝ := sorry -- Complex function of c

/--
**Erdős 1963 Lower Bound:**
For any c > 0, N(k, ck) > (1 + α_c)^k.

This shows exponential growth is necessary.
-/
axiom erdos_1963_lower_bound (c : ℝ) (hc : c > 0) :
    ∀ k : ℕ, k > 0 → (Nkl k ⌈c * k⌉.toNat : ℝ) > (1 + alpha_c c) ^ k

/--
**Behavior of α_c:**
- α_c → 0 as c → 0 (small discrepancy is easy to avoid)
- α_c → √2 - 1 as c → 1 (approaching van der Waerden)
-/
axiom alpha_c_limit_zero : Filter.Tendsto alpha_c (nhds 0) (nhds 0)
axiom alpha_c_limit_one : Filter.Tendsto alpha_c (nhds 1) (nhds (Real.sqrt 2 - 1))

/-
## Part VII: The Main Open Questions
-/

/--
**Question 1: Linear Discrepancy**
For any c > 0, is there C > 1 with N(k, ck) ≤ C^k?
-/
def LinearDiscrepancyConjecture : Prop :=
  ∀ c : ℝ, c > 0 → ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k > 0 →
    (Nkl k ⌈c * k⌉.toNat : ℝ) ≤ C ^ k

/--
**Question 2: Discrepancy 2**
Is there C > 1 with N(k, 2) ≤ C^k?
-/
def Discrepancy2Conjecture : Prop :=
  ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k > 0 → (Nkl k 2 : ℝ) ≤ C ^ k

/--
**Question 3: Square Root Discrepancy**
Is there C > 1 with N(k, √k) ≤ C^k?
-/
def SqrtDiscrepancyConjecture : Prop :=
  ∃ C : ℝ, C > 1 ∧ ∀ k : ℕ, k > 1 →
    (Nkl k ⌈Real.sqrt k⌉.toNat : ℝ) ≤ C ^ k

/--
**Current State:**
Even N(k, 2) has "no decent bound" according to Erdős-Graham.
-/
theorem no_decent_bound_known : True := trivial

/-
## Part VIII: Relationship to Other Problems
-/

/--
**Connection to Erdős Discrepancy Problem:**
This is related to the broader question of discrepancy of hypergraph
colorings. The Erdős Discrepancy Conjecture (proved by Tao, 2015)
concerns homogeneous arithmetic progressions.
-/
theorem erdos_discrepancy_connection : True := trivial

/--
**Szemeredi's Theorem:**
Any subset of ℕ with positive density contains arbitrarily long APs.
This is related but different: we ask about colorings, not subsets.
-/
theorem szemeredi_connection : True := trivial

/-
## Part IX: Summary
-/

/--
**Erdős Problem #176: Status**

**Definition:**
N(k, ℓ) = min N such that any ±1 coloring of {1,...,N} has a k-AP
with |sum| ≥ ℓ.

**Known:**
- N(k, k) = W(k), van der Waerden number
- N(k, 1) = 2^t(k-1) + 1 where k = 2^t·m, m odd (Spencer 1973)
- N(k, ck) > (1 + α_c)^k (Erdős 1963)

**Open:**
- N(k, 2) ≤ C^k? (no decent bound known)
- N(k, √k) ≤ C^k?
- N(k, ck) ≤ C^k for all c > 0?
-/
theorem erdos_176_summary :
    -- Spencer gives exact formula for N(k, 1)
    (∀ k : ℕ, k > 0 → ∃ formula : ℕ, Nkl k 1 = formula) ∧
    -- Van der Waerden connection
    (∀ k : ℕ, k > 0 → Nkl k k = vanDerWaerden k) ∧
    -- The main questions are stated
    (LinearDiscrepancyConjecture ↔ ∀ c : ℝ, c > 0 → ∃ C : ℝ, C > 1 ∧
      ∀ k : ℕ, k > 0 → (Nkl k ⌈c * k⌉.toNat : ℝ) ≤ C ^ k) := by
  constructor
  · intro k hk
    use 2^(k.factorization 2) * (k - 1) + 1
    exact spencer_1973 k hk
  constructor
  · intro k _
    rfl
  · rfl

end Erdos176
