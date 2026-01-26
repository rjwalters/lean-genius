/-!
# Erdős Problem #1130 — Lagrange Basis Function Sums

For points x₁,...,xₙ ∈ [-1,1], the Lagrange basis polynomials l_k(x) satisfy
l_k(xⱼ) = δ_{kj}. Setting x₀ = -1, x_{n+1} = 1, define

  Υ(x₁,...,xₙ) = min_{0≤i≤n} max_{x∈[xᵢ,xᵢ₊₁]} Σ_k |l_k(x)|

Is Υ(x₁,...,xₙ) ≪ log n? Which points maximize Υ?

PROVED:
- Erdős: Υ < √n
- De Boor–Pinkus: optimal points equalize the sum across intervals
- Final result: Υ ≤ (2/π) log n + O(1)

Reference: https://erdosproblems.com/1130
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Lagrange Interpolation Basis -/

/-- Points x₁,...,xₙ in [-1,1] with x₀ = -1 and x_{n+1} = 1,
    ordered x₀ < x₁ < ... < x_{n+1} -/
structure InterpolationNodes (n : ℕ) where
  nodes : Fin n → ℝ
  in_interval : ∀ i, -1 ≤ nodes i ∧ nodes i ≤ 1
  ordered : ∀ i j : Fin n, i < j → nodes i < nodes j

/-- The Lagrange basis polynomial l_k(x) for node k:
    l_k(x) = ∏_{j≠k} (x - xⱼ)/(x_k - xⱼ) -/
noncomputable def lagrangeBasis (P : InterpolationNodes n) (k : Fin n) (x : ℝ) : ℝ :=
  Finset.univ.prod (fun j =>
    if j = k then 1
    else (x - P.nodes j) / (P.nodes k - P.nodes j))

/-- The Lebesgue function: Λ(x) = Σ_k |l_k(x)| -/
noncomputable def lebesgueFunction (P : InterpolationNodes n) (x : ℝ) : ℝ :=
  Finset.univ.sum (fun k => |lagrangeBasis P k x|)

/-! ## The Υ Functional -/

/-- The subinterval endpoints: x₀ = -1, x₁,...,xₙ, x_{n+1} = 1 -/
noncomputable def subintervalEndpoint (P : InterpolationNodes n) (i : Fin (n + 2)) : ℝ :=
  if i.val = 0 then -1
  else if i.val = n + 1 then 1
  else P.nodes ⟨i.val - 1, by omega⟩

/-- The maximum of the Lebesgue function on the i-th subinterval -/
noncomputable def maxLebesgueOnInterval (P : InterpolationNodes n) (i : Fin (n + 1)) : ℝ :=
  sSup {lebesgueFunction P x |
    (x : ℝ) (_ : subintervalEndpoint P ⟨i.val, by omega⟩ ≤ x)
    (_ : x ≤ subintervalEndpoint P ⟨i.val + 1, by omega⟩)}

/-- Υ(x₁,...,xₙ) = min over subintervals of the max Lebesgue function -/
noncomputable def upsilon (P : InterpolationNodes n) : ℝ :=
  sInf {maxLebesgueOnInterval P i | (i : Fin (n + 1))}

/-! ## Erdős's Initial Bound -/

/-- Erdős's bound: Υ < √n for all node configurations -/
axiom erdos_sqrt_bound (n : ℕ) (hn : 1 ≤ n) (P : InterpolationNodes n) :
  upsilon P < Real.sqrt (n : ℝ)

/-! ## The Logarithmic Bound (PROVED) -/

/-- The optimal bound: Υ ≤ (2/π) log n + O(1).
    This proves the Erdős conjecture that Υ ≪ log n. -/
axiom logarithmic_bound :
  ∃ C : ℝ, ∀ (n : ℕ) (hn : 2 ≤ n) (P : InterpolationNodes n),
    upsilon P ≤ 2 / Real.pi * Real.log (n : ℝ) + C

/-! ## De Boor–Pinkus Characterization -/

/-- De Boor–Pinkus: the points maximizing Υ equalize the max Lebesgue
    function across all subintervals -/
axiom deBoor_pinkus_optimal (n : ℕ) (hn : 2 ≤ n) :
  ∃ P : InterpolationNodes n,
    (∀ Q : InterpolationNodes n, upsilon Q ≤ upsilon P) ∧
    (∀ i j : Fin (n + 1),
      maxLebesgueOnInterval P i = maxLebesgueOnInterval P j)

/-! ## Erdős Problem 1130 (PROVED) -/

/-- Erdős Problem 1130 (PROVED): Υ(x₁,...,xₙ) = O(log n).
    The question of which points maximize Υ is answered by de Boor–Pinkus:
    the optimal configuration equalizes the Lebesgue function across intervals. -/
axiom ErdosProblem1130 :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (hn : 2 ≤ n) (P : InterpolationNodes n),
      upsilon P ≤ C * Real.log (n : ℝ)
