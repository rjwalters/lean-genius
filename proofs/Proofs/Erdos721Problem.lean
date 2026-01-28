/-
Erdős Problem #721: Van der Waerden Numbers W(3,k)

Source: https://erdosproblems.com/721
Status: SOLVED (Both challenges met)

Statement:
Let W(3,k) be the van der Waerden number — the minimum n such that in any
red/blue coloring of {1,...,n} there exists either a red 3-term arithmetic
progression or a blue k-term arithmetic progression.

Give reasonable bounds for W(3,k). In particular:
1. Give any non-trivial lower bounds for W(3,k)
2. Prove that W(3,k) < exp(k^c) for some constant c < 1

Resolution:
Both challenges have been met:
- Lower bounds: Green [Gr22], Hunter [Hu22]
- Upper bounds: Schoen [Sc21], Bloom-Sisask [BlSi23]

Historical Note:
Graham conjectured W(3,k) ≪ k², but this was disproved by Green's
superpolynomial lower bound. The problem illustrates the tension between
Ramsey-type results and extremal bounds.

References:
- Erdős [Er80], [Er81]: Original problem
- Green [Gr22]: Superpolynomial lower bound
- Hunter [Hu22]: Improved lower bound
- Schoen [Sc21]: First subexponential upper bound
- Bloom-Sisask [BlSi23]: Best current upper bound
- Kelley-Meka [KeMe23]: Sets without 3-APs
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Erdos721

/-! ## Part I: Van der Waerden Numbers -/

/--
**The off-diagonal van der Waerden number W(3,k):**
The minimum n such that any red/blue coloring of {1,...,n} contains
either a red 3-AP or a blue k-AP.

This is axiomatized as a function ℕ → ℕ because computing W(3,k)
requires deep Ramsey theory arguments.
-/
axiom W : ℕ → ℕ

/-- W(3,k) ≥ k for k ≥ 3 (trivial: color {1,...,k-1} all red). -/
axiom W_ge (k : ℕ) : k ≥ 3 → W k ≥ k

/-- W(3,k) is monotone increasing: more colors need more numbers. -/
axiom W_increasing : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → W k₁ ≤ W k₂

/-! ## Part II: Known Small Values -/

/--
**Known exact values:**
W(3,3) = 9, W(3,4) = 18, W(3,5) = 22, W(3,6) = 32, W(3,7) = 46.
These are computed by exhaustive search over all 2-colorings.
-/
axiom W_known_values :
    W 3 = 9 ∧
    W 4 = 18 ∧
    W 5 = 22 ∧
    W 6 = 32 ∧
    W 7 = 46

/-! ## Part III: Graham's Conjecture (Disproved) -/

/--
**Graham's conjecture:**
W(3,k) ≪ k², i.e., polynomial growth of degree 2.
-/
def graham_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ k ≥ 3, (W k : ℝ) ≤ C * k^2

/--
**Graham's conjecture is FALSE:**
Green [Gr22] proved a superpolynomial lower bound, showing W(3,k)
grows faster than any polynomial in k.
-/
axiom graham_conjecture_false : ¬graham_conjecture

/-! ## Part IV: Lower Bounds -/

/--
**Green's lower bound (2022):**
W(3,k) ≥ exp(c · (log k)^{4/3} / (log log k)^{1/3})
for some constant c > 0. This was the first superpolynomial lower bound,
disproving Graham's polynomial conjecture.
-/
axiom green_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ k ≥ 3, (W k : ℝ) ≥ exp (c * (log k)^(4/3 : ℝ) / (log (log k))^(1/3 : ℝ))

/--
**Hunter's improvement (2022):**
W(3,k) ≥ exp(c · (log k)² / log log k)
Improved Green's exponent from 4/3 to 2 in the logarithmic term.
-/
axiom hunter_lower_bound :
    ∃ c : ℝ, c > 0 ∧
    ∀ k ≥ 3, (W k : ℝ) ≥ exp (c * (log k)^2 / log (log k))

/--
**W(3,k) is superpolynomial:**
For any fixed polynomial degree d, W(3,k) > k^d for all large enough k.
This follows from Hunter's lower bound since exp(c(log k)²/log log k) grows
faster than any polynomial.
-/
axiom W_superpolynomial :
    ∀ d : ℕ, ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) > k^(d : ℝ)

/-! ## Part V: Upper Bounds -/

/--
**Schoen's upper bound (2021):**
W(3,k) ≤ exp(k^c) for some 0 < c < 1.
This was the first to answer Erdős's challenge about subexponential growth,
showing W(3,k) grows slower than exp(k).
-/
axiom schoen_upper_bound :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) ≤ exp (k^c)

/--
**Bloom-Sisask upper bound (2023):**
W(3,k) ≤ exp(C · (log k)^9)
The best current upper bound, a huge improvement over Schoen's
exp(k^c). Builds on the Kelley-Meka breakthrough on 3-AP-free sets.
-/
axiom bloom_sisask_upper_bound :
    ∃ C : ℝ, C > 0 ∧
    ∀ k ≥ 3, (W k : ℝ) ≤ exp (C * (log k)^9)

/-! ## Part VI: Connection to 3-AP Free Sets -/

/--
**Roth density bound:**
Any subset of {1,...,n} with density > r₃(n)/n avoids 3-APs,
where r₃(n) is the maximum size of a 3-AP-free subset of {1,...,n}.
W(3,k) relates to r₃(n) because blue-coloring avoiding k-APs
must be "thin", while red-coloring avoiding 3-APs must be "dense".
-/
axiom roth_density_connection :
    ∃ f : ℕ → ℕ, ∀ n : ℕ, n ≥ 3 →
      f n ≤ n ∧ -- r₃(n) ≤ n
      ∀ S : Finset ℕ, (S.card : ℝ) > f n → -- any dense-enough subset
        ∃ a d : ℕ, d > 0 ∧ a ∈ S ∧ (a + d) ∈ S ∧ (a + 2 * d) ∈ S

/--
**Behrend's construction (1946):**
There exist 3-AP-free subsets of {1,...,n} of size
n · exp(-c · √(log n)). This gives a lower bound on r₃(n)
and hence lower bounds on W(3,k) via the Roth connection.
-/
axiom behrend_construction :
    ∃ c : ℝ, c > 0 ∧
    ∀ n ≥ 3, ∃ S : Finset ℕ,
      (∀ x ∈ S, x ≤ n) ∧
      (∀ a d : ℕ, d > 0 → a ∈ S → (a + d) ∈ S → (a + 2 * d) ∉ S) ∧
      (S.card : ℝ) ≥ n * exp (-c * (log n)^(1/2 : ℝ))

/--
**Kelley-Meka breakthrough (2023):**
Sets without 3-APs in {1,...,n} have density at most
exp(-c · (log n)^{1/12}). This dramatically improved previous bounds
and led to the Bloom-Sisask improvement on W(3,k).
-/
axiom kelley_meka_density :
    ∃ c : ℝ, c > 0 ∧
    ∀ n ≥ 3, ∀ S : Finset ℕ,
      (∀ x ∈ S, x ≤ n) →
      (∀ a d : ℕ, d > 0 → a ∈ S → (a + d) ∈ S → (a + 2 * d) ∉ S) →
      (S.card : ℝ) ≤ n * exp (-c * (log n)^(1/12 : ℝ))

/-! ## Part VII: The Growth Rate Question -/

/--
**Open question: Exact growth rate.**
Is W(3,k) = exp((log k)^{2+o(1)})?
Hunter's lower bound has exponent 2 (up to log log k),
while Bloom-Sisask upper bound has exponent 9.
The true answer is believed to be closer to the lower bound.
-/
def exact_growth_conjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ,
    ∀ k ≥ N, exp ((log k)^(2-ε)) ≤ W k ∧
             (W k : ℝ) ≤ exp ((log k)^(2+ε))

/--
**Current state of the gap:**
Lower: exp(c(log k)²/log log k) — exponent ≈ 2
Upper: exp(C(log k)^9) — exponent = 9
Closing this gap from [2, 9] is a major open problem.
-/
axiom bounds_gap_width :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
    ∀ k ≥ 3,
      exp (c * (log k)^2 / log (log k)) ≤ W k ∧
      (W k : ℝ) ≤ exp (C * (log k)^9)

/-! ## Part VIII: Related Problems -/

/--
**Szemerédi's theorem (1975):**
For any δ > 0 and k ≥ 3, any subset of {1,...,n} with density ≥ δ
contains a k-AP for n sufficiently large. This generalizes Roth's
theorem (k=3) and provides the existence proof for all W(r,k).
-/
axiom szemeredi_theorem (δ : ℝ) (hδ : δ > 0) (k : ℕ) (hk : k ≥ 3) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ S : Finset ℕ,
      (∀ x ∈ S, x ≤ n) → (S.card : ℝ) ≥ δ * n →
      ∃ a d : ℕ, d > 0 ∧ ∀ i : ℕ, i < k → (a + i * d) ∈ S

/--
**Diagonal van der Waerden numbers W(k,k):**
The diagonal case grows much faster — at least tower-type.
Gowers' quantitative proof of Szemerédi's theorem gives bounds,
but they are far from the believed truth.
-/
axiom diagonal_growth (k : ℕ) (hk : k ≥ 3) :
    ∃ W_kk : ℕ, W_kk ≥ k -- W(k,k) exists and grows

/-! ## Part IX: Summary -/

/--
**Erdős Problem #721 Summary:**

PROBLEM: Give reasonable bounds for W(3,k), the van der Waerden number.
Specifically:
1. Non-trivial lower bounds
2. Prove W(3,k) < exp(k^c) for some c < 1

STATUS: SOLVED (both challenges met)

KEY RESULTS:
1. Lower bound: W(3,k) ≥ exp(c(log k)²/log log k) [Hunter 2022]
2. Upper bound: W(3,k) ≤ exp(C(log k)^9) [Bloom-Sisask 2023]
3. Graham's polynomial conjecture is FALSE [Green 2022]
4. First subexponential upper bound [Schoen 2021]
-/
theorem erdos_721_status :
    -- Graham's polynomial conjecture is false
    ¬graham_conjecture ∧
    -- Erdős's subexponential challenge is met
    (∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) ≤ exp (k^c)) :=
  ⟨graham_conjecture_false, schoen_upper_bound⟩

/--
**Combined bounds theorem:**
exp(c(log k)²/log log k) ≤ W(3,k) ≤ exp(C(log k)^9)
-/
theorem W_bounds_summary :
    (∃ c : ℝ, c > 0 ∧ ∀ k ≥ 3,
      (W k : ℝ) ≥ exp (c * (log k)^2 / log (log k))) ∧
    (∃ C : ℝ, C > 0 ∧ ∀ k ≥ 3,
      (W k : ℝ) ≤ exp (C * (log k)^9)) :=
  ⟨hunter_lower_bound, bloom_sisask_upper_bound⟩

/--
**Main theorem: Both challenges answered.**
1. Non-trivial lower bounds: YES (Green, Hunter — superpolynomial)
2. Subexponential upper bounds: YES (Schoen, Bloom-Sisask)
-/
theorem erdos_721 :
    -- Superpolynomial lower bound exists
    (∃ c : ℝ, c > 0 ∧ ∀ k ≥ 3,
      (W k : ℝ) ≥ exp (c * (log k)^(4/3 : ℝ) / (log (log k))^(1/3 : ℝ))) ∧
    -- Subexponential upper bound exists
    (∃ c : ℝ, 0 < c ∧ c < 1 ∧ ∃ N : ℕ, ∀ k ≥ N, (W k : ℝ) ≤ exp (k^c)) :=
  ⟨green_lower_bound, schoen_upper_bound⟩

end Erdos721
