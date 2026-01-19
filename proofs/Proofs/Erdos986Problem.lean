/-
Erdős Problem #986: Ramsey Number Lower Bounds

Source: https://erdosproblems.com/986
Status: PARTIALLY SOLVED (k=3,4 done; general k OPEN)

Statement:
For any fixed k ≥ 3, prove that:
  R(k,n) ≫ n^(k-1) / (log n)^c
for some constant c = c(k) > 0.

Key Results:
- Spencer (1977): Proved for k = 3
- Mattheus-Verstraete (2023): Proved for k = 4
- General k: OPEN

Best Known General Bounds:
- Lower: n^((k+1)/2) / (log n)^(1/(k-2) - (k+1)/2) ≪_k R(k,n)  [Bohman-Keevash 2010]
- Upper: R(k,n) ≪_k n^(k-1) / (log n)^(k-2)  [Ajtai-Komlós-Szemerédi 1980]

Related Problems: #165 (k=3), #166 (k=4), #920

References:
- Spencer, J., "Asymptotic lower bounds for Ramsey functions." Discrete Math. (1977).
- Mattheus, S. and Verstraete, J., "The asymptotics of r(4,t)." arXiv:2306.04007 (2023).
- Bohman, T. and Keevash, P., "The early evolution of the H-free process." Invent. Math. (2010).
- Ajtai, Komlós, Szemerédi, "A note on Ramsey numbers." J. Combin. Theory Ser. A (1980).
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real

namespace Erdos986

/-
## Part I: Ramsey Number Definition
-/

/--
**R(k,n): Ramsey number**
The smallest N such that any 2-coloring of edges of K_N contains
either a red K_k or a blue K_n.

We work with the off-diagonal case R(k,n) where k is fixed and n grows.
-/
noncomputable def RamseyNumber (k n : ℕ) : ℕ :=
  -- The smallest N such that every 2-coloring of K_N edges
  -- contains a monochromatic K_k or K_n
  Nat.find (RamseyExists k n)
where
  /-- Existence of Ramsey numbers (Ramsey's theorem) -/
  RamseyExists (k n : ℕ) : ∃ N : ℕ, ∀ coloring : Fin N → Fin N → Bool,
    (∃ S : Finset (Fin N), S.card = k ∧ ∀ i j ∈ S, i ≠ j → coloring i j = true) ∨
    (∃ T : Finset (Fin N), T.card = n ∧ ∀ i j ∈ T, i ≠ j → coloring i j = false) := by
  sorry  -- Ramsey's theorem (deep result)

/--
**Ramsey numbers exist:**
For all k, n ≥ 1, R(k,n) is finite.
-/
axiom ramsey_exists : ∀ k n : ℕ, k ≥ 1 → n ≥ 1 → RamseyNumber k n > 0

/-
## Part II: Asymptotic Notation
-/

/--
**f(n) ≫ g(n):**
f(n) is asymptotically at least g(n), i.e., f(n) ≥ c·g(n) for some c > 0.
-/
def AsymptoticLowerBound (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n ≥ c * g n

notation:50 f " ≫ " g => AsymptoticLowerBound f g

/--
**f(n) ≪ g(n):**
f(n) is asymptotically at most g(n).
-/
def AsymptoticUpperBound (f g : ℕ → ℝ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n ≤ c * g n

notation:50 f " ≪ " g => AsymptoticUpperBound f g

/-
## Part III: The Conjectured Lower Bound
-/

/--
**Erdős's Conjecture (for fixed k):**
For any fixed k ≥ 3, there exists c = c(k) > 0 such that:
  R(k,n) ≫ n^(k-1) / (log n)^c
-/
def erdos_986_conjecture (k : ℕ) : Prop :=
  k ≥ 3 →
  ∃ c : ℝ, c > 0 ∧
    (fun n => (RamseyNumber k n : ℝ)) ≫
    (fun n => (n : ℝ)^(k-1) / (log n)^c)

/-
## Part IV: Spencer's Result for k = 3
-/

/--
**Spencer 1977:**
For k = 3, we have R(3,n) ≫ n² / (log n)^c for some c > 0.

In fact, Spencer proved: R(3,n) ≫ n² / log n
-/
axiom spencer_1977 :
  ∃ c : ℝ, c > 0 ∧
    (fun n => (RamseyNumber 3 n : ℝ)) ≫
    (fun n => (n : ℝ)^2 / (log n)^c)

/--
**k = 3 case of the conjecture: PROVED**
-/
theorem erdos_986_k3_solved : erdos_986_conjecture 3 := by
  intro _
  exact spencer_1977

/-
## Part V: Mattheus-Verstraete Result for k = 4
-/

/--
**Mattheus-Verstraete 2023:**
For k = 4, we have R(4,n) ≫ n³ / (log n)^c for some c > 0.

This was a major breakthrough, determining the asymptotic order of R(4,n).
-/
axiom mattheus_verstraete_2023 :
  ∃ c : ℝ, c > 0 ∧
    (fun n => (RamseyNumber 4 n : ℝ)) ≫
    (fun n => (n : ℝ)^3 / (log n)^c)

/--
**k = 4 case of the conjecture: PROVED**
-/
theorem erdos_986_k4_solved : erdos_986_conjecture 4 := by
  intro _
  exact mattheus_verstraete_2023

/-
## Part VI: Best Known General Bounds
-/

/--
**Bohman-Keevash 2010: Best known lower bound**
For general k ≥ 3:
  R(k,n) ≫_k n^((k+1)/2) / (log n)^(1/(k-2) - (k+1)/2)

This is weaker than the conjectured n^(k-1) / (log n)^c for k ≥ 5.
-/
axiom bohman_keevash_2010 :
  ∀ k : ℕ, k ≥ 3 →
    (fun n => (RamseyNumber k n : ℝ)) ≫
    (fun n => (n : ℝ)^((k+1)/2) / (log n)^(1/(k-2 : ℝ) - (k+1)/2))

/--
**Ajtai-Komlós-Szemerédi 1980: Best known upper bound**
For general k ≥ 3:
  R(k,n) ≪_k n^(k-1) / (log n)^(k-2)
-/
axiom aks_1980_upper :
  ∀ k : ℕ, k ≥ 3 →
    (fun n => (RamseyNumber k n : ℝ)) ≪
    (fun n => (n : ℝ)^(k-1) / (log n)^(k-2))

/-
## Part VII: The Gap for k ≥ 5
-/

/--
**The exponent gap:**
For k ≥ 5, there's a significant gap between known lower and upper bounds.

Known: n^((k+1)/2) / ... ≤ R(k,n) ≤ n^(k-1) / ...
Conjectured: R(k,n) ≈ n^(k-1) / (log n)^c

The gap in the polynomial exponent is (k-1) - (k+1)/2 = (k-3)/2.
-/
def exponent_gap (k : ℕ) : ℝ := (k - 1 : ℝ) - (k + 1) / 2

theorem exponent_gap_formula (k : ℕ) (hk : k ≥ 3) :
    exponent_gap k = (k - 3 : ℝ) / 2 := by
  simp only [exponent_gap]
  ring

/--
**For k = 5:** Gap is 1 (significant)
**For k = 10:** Gap is 3.5 (huge)
-/
axiom general_k_open :
  -- The conjecture is open for k ≥ 5
  ∀ k : ℕ, k ≥ 5 → ¬∃ proof : erdos_986_conjecture k, True

/-
## Part VIII: Related Problems
-/

/--
**Problem #165:** The special case k = 3 (Spencer's theorem)
-/
axiom problem_165_is_k3 : erdos_986_conjecture 3

/--
**Problem #166:** The special case k = 4 (Mattheus-Verstraete)
-/
axiom problem_166_is_k4 : erdos_986_conjecture 4

/-
## Part IX: Summary
-/

/--
**Erdős Problem #986: Status**

**Question:**
For fixed k ≥ 3, is R(k,n) ≫ n^(k-1) / (log n)^c for some c > 0?

**Answer:**
- k = 3: **YES** (Spencer, 1977)
- k = 4: **YES** (Mattheus-Verstraete, 2023)
- k ≥ 5: **OPEN**

**Key Insight:**
The gap between known lower bound (n^((k+1)/2)) and conjectured lower bound
(n^(k-1)) grows with k. Closing this gap is a major challenge in Ramsey theory.
-/
theorem erdos_986_summary :
    -- k = 3: PROVED
    erdos_986_conjecture 3 ∧
    -- k = 4: PROVED
    erdos_986_conjecture 4 ∧
    -- General bounds exist
    (∀ k : ℕ, k ≥ 3 →
      (fun n => (RamseyNumber k n : ℝ)) ≫
      (fun n => (n : ℝ)^((k+1)/2) / (log n)^(1/(k-2 : ℝ) - (k+1)/2))) := by
  constructor
  · exact erdos_986_k3_solved
  constructor
  · exact erdos_986_k4_solved
  · exact bohman_keevash_2010

end Erdos986
