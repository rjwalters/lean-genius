/-
Erdős Problem #270: Irrationality of Product-Reciprocal Series

Source: https://erdosproblems.com/270
Status: DISPROVED (Crmarić-Kovač, 2025)

Statement:
Let f(n) → ∞ as n → ∞. Is it true that
    Σ_{n≥1} 1/((n+1)(n+2)⋯(n+f(n)))
is irrational?

Answer: NO (in the strongest sense!)

Crmarić and Kovač (2025) proved that for ANY α ∈ (0, ∞), there exists
f: ℕ → ℕ with f(n) → ∞ such that the sum equals α exactly.

This means:
- The sum can be rational (any positive rational)
- The sum can be irrational (any positive irrational)
- The sum can be transcendental (any positive transcendental)

The original question asked if the sum is ALWAYS irrational - the answer
is a resounding NO.

Special case f(n) = n:
Hansen (1975) showed Σ 1/C(2n,n) = 1/3 + 2π/3^(5/2) is transcendental.

Open question:
Is the sum always irrational when f is assumed to be NON-DECREASING?
Crmarić-Kovač show such sums form a set of Lebesgue measure zero.

References:
- Erdős-Graham (1980): Original problem
- Hansen [Ha75]: f(n) = n case is transcendental
- Crmarić-Kovač [CrKo25]: Disproof - any α ∈ (0,∞) is achievable
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real

open Real Nat

namespace Erdos270

/-
## Part I: The Product-Reciprocal Series

The series involves products (n+1)(n+2)⋯(n+f(n)) in the denominator.
-/

/--
**Rising Factorial (Pochhammer symbol):**
(n+1)(n+2)⋯(n+k) = (n+k)! / n!

This is the product from n+1 to n+k.
-/
def risingProduct (n k : ℕ) : ℕ :=
  if k = 0 then 1 else (List.range k).foldl (fun acc i => acc * (n + 1 + i)) 1

/--
**Series Term:**
The n-th term of the series is 1/((n+1)(n+2)⋯(n+f(n))).
-/
def seriesTerm (f : ℕ → ℕ) (n : ℕ) : ℝ :=
  if risingProduct n (f n) = 0 then 0
  else 1 / (risingProduct n (f n) : ℝ)

/--
**The Series:**
Σ_{n≥1} 1/((n+1)(n+2)⋯(n+f(n)))
-/
noncomputable def productReciprocalSeries (f : ℕ → ℕ) : ℝ :=
  ∑' n, seriesTerm f n

/-
## Part II: The Limit Condition

The function f must satisfy f(n) → ∞.
-/

/--
**f(n) → ∞:**
For every M, eventually f(n) > M.
-/
def TendsToInfinity (f : ℕ → ℕ) : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, f n > M

/--
**Non-decreasing:**
f(n+1) ≥ f(n) for all n.
-/
def IsNondecreasing (f : ℕ → ℕ) : Prop :=
  ∀ n : ℕ, f n ≤ f (n + 1)

/-
## Part III: The Original Conjecture (Disproved!)

Erdős and Graham conjectured the sum is always irrational.
-/

/--
**Original Conjecture (FALSE):**
For all f with f(n) → ∞, the sum is irrational.

Erdős and Graham wrote: "the answer is almost surely in the affirmative
if f(n) is assumed to be nondecreasing."
-/
def ErdosGrahamConjecture : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f → Irrational (productReciprocalSeries f)

/-
## Part IV: The Crmarić-Kovač Disproof (2025)

The conjecture is false in the strongest possible sense!
-/

/--
**Crmarić-Kovač Theorem (2025):**
For ANY positive real α, there exists f: ℕ → ℕ with f(n) → ∞
such that the series equals α exactly.

This completely disproves the conjecture - the series can be any
positive real number, rational or irrational.
-/
axiom crmaric_kovac_2025 :
    ∀ α : ℝ, α > 0 →
      ∃ f : ℕ → ℕ, TendsToInfinity f ∧ productReciprocalSeries f = α

/--
**Corollary: Rational Values Exist**
The series can equal any positive rational.
-/
theorem rational_values_exist :
    ∀ q : ℚ, q > 0 →
      ∃ f : ℕ → ℕ, TendsToInfinity f ∧ productReciprocalSeries f = (q : ℝ) := by
  intro q hq
  exact crmaric_kovac_2025 (q : ℝ) (by exact_mod_cast hq)

/--
**Corollary: The Conjecture is FALSE**
-/
theorem erdos_270_disproved : ¬ErdosGrahamConjecture := by
  intro hConj
  -- Take α = 1 (a rational number)
  obtain ⟨f, hf_inf, hf_eq⟩ := crmaric_kovac_2025 1 (by norm_num)
  -- By the conjecture, the series would be irrational
  have h_irr := hConj f hf_inf
  -- But the series equals 1, which is rational
  rw [hf_eq] at h_irr
  exact h_irr ⟨1, by norm_num⟩

/-
## Part V: The Special Case f(n) = n

When f(n) = n, we get the central binomial coefficient sum.
-/

/--
**Central Binomial Coefficient:**
C(2n, n) = (2n)! / (n!)²
-/
def centralBinomial (n : ℕ) : ℕ := Nat.choose (2 * n) n

/--
**Connection to Rising Product:**
1/C(2n,n) = n! / ((n+1)(n+2)⋯(2n)) = 1/((n+1)⋯(n+n))
-/
theorem central_binomial_connection (n : ℕ) (hn : n ≥ 1) :
    (centralBinomial n : ℝ)⁻¹ = seriesTerm (fun _ => n) n := by
  sorry -- Technical: involves factorial identities

/--
**Hansen's Constant:**
The sum Σ 1/C(2n,n) equals this transcendental number.
-/
noncomputable def hansenConstant : ℝ := 1/3 + 2 * Real.pi / (3 : ℝ)^(5/2 : ℝ)

/--
**Hansen's Theorem (1975):**
Σ_{n≥1} 1/C(2n,n) = 1/3 + 2π/3^(5/2)

This is a transcendental number!
-/
axiom hansen_1975 :
    (∑' n, (centralBinomial n : ℝ)⁻¹) = hansenConstant

/--
**Hansen's Constant is Transcendental:**
It involves π, which is transcendental.
-/
axiom hansen_transcendental : Transcendental ℚ hansenConstant

/-
## Part VI: The Non-decreasing Case (Still Open!)

The question becomes much harder for monotonic f.
-/

/--
**Nondecreasing Conjecture (OPEN):**
If f is nondecreasing AND f(n) → ∞, is the sum always irrational?

This remains an open problem even after Crmarić-Kovač!
-/
def NondecreasingConjecture : Prop :=
  ∀ f : ℕ → ℕ, TendsToInfinity f → IsNondecreasing f →
    Irrational (productReciprocalSeries f)

/--
**Measure Zero Result:**
The set of possible values for nondecreasing f has Lebesgue measure zero.

This is strong evidence that the nondecreasing case might always be irrational,
but it's not a proof!
-/
axiom nondecreasing_measure_zero :
    ∃ S : Set ℝ, (∀ f : ℕ → ℕ, TendsToInfinity f → IsNondecreasing f →
      productReciprocalSeries f ∈ S) ∧
      -- S has Lebesgue measure zero (stated informally)
      True

/-
## Part VII: Examples and Bounds
-/

/--
**Convergence:**
For any f with f(n) → ∞, the series converges.

Proof idea: Eventually f(n) ≥ 2, so terms are ≤ 1/((n+1)(n+2)) ∼ 1/n².
-/
axiom series_converges (f : ℕ → ℕ) (hf : TendsToInfinity f) :
    Summable (seriesTerm f)

/--
**Upper Bound:**
The series is bounded above by the convergent series Σ 1/n!.
-/
theorem series_upper_bound (f : ℕ → ℕ) (hf : TendsToInfinity f) :
    productReciprocalSeries f ≤ Real.exp 1 - 1 := by
  sorry -- Comparison with exponential series

/--
**Lower Bound:**
The series is positive.
-/
theorem series_positive (f : ℕ → ℕ) (hf : TendsToInfinity f) :
    productReciprocalSeries f > 0 := by
  sorry -- All terms are positive

/-
## Part VIII: Why the Construction Works

Intuition for Crmarić-Kovač.
-/

/--
**Construction Idea:**

To achieve sum = α:
1. Start with partial sum S_N < α
2. Choose f(N+1) large enough that the remaining terms are < α - S_N
3. But also small enough that f(N+1) ≤ f(N+2) would fail
4. The non-monotonicity is essential!

By carefully controlling f at each step, any target α can be achieved.
-/
theorem construction_idea : True := trivial

/--
**Why Non-decreasing is Hard:**

For non-decreasing f:
- Once f(n) is chosen, f(m) ≥ f(n) for all m > n
- This severely constrains the partial sums
- The achievable values form a "thin" set (measure zero)
-/
theorem nondecreasing_difficulty : True := trivial

/-
## Part IX: Summary
-/

/--
**Erdős Problem #270: DISPROVED**

**Original Question:**
For f(n) → ∞, is Σ 1/((n+1)⋯(n+f(n))) always irrational?

**Answer:** NO (Crmarić-Kovač, 2025)
In fact, for ANY α > 0, there exists f with the sum equal to α.

**Special Case (Hansen 1975):**
For f(n) = n, the sum = 1/3 + 2π/3^(5/2) is transcendental.

**Open Question:**
Is the sum always irrational when f is NON-DECREASING?
-/
theorem erdos_270_summary :
    -- The conjecture is false
    ¬ErdosGrahamConjecture ∧
    -- Any positive real is achievable
    (∀ α : ℝ, α > 0 → ∃ f : ℕ → ℕ, TendsToInfinity f ∧
      productReciprocalSeries f = α) ∧
    -- The f(n) = n case is transcendental
    Transcendental ℚ hansenConstant := by
  exact ⟨erdos_270_disproved, crmaric_kovac_2025, hansen_transcendental⟩

end Erdos270
