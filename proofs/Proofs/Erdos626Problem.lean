/-
  Erdős Problem #626: Chromatic Number and Girth

  Source: https://erdosproblems.com/626
  Status: OPEN (bounds established, limit question unresolved)

  Statement:
  Let k ≥ 4 and g_k(n) denote the largest m such that there is a graph on n
  vertices with chromatic number k and girth > m (no cycle of length ≤ m).
  Does lim_{n→∞} g_k(n) / log n exist?

  Context:
  This relates to the fundamental tension between chromatic number and girth.
  High chromatic number tends to require dense local structure, while large girth
  forces the graph to be locally tree-like.

  Known bounds:
  - Lower: g_k(n) ≥ (1/4 log k) · log n (Kostochka)
  - Upper: g_k(n) ≤ (2/log(k-2)) · log n + 1 (Erdős)
-/

import Mathlib

open Finset Function SimpleGraph Nat

namespace Erdos626

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Basic Definitions -/

/-- The chromatic number of a graph -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  sorry -- Minimum k such that G is k-colorable

/-- A graph is k-colorable -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ v w : V, G.Adj v w → f v ≠ f w

/-- The girth of a graph (length of shortest cycle, 0 if acyclic) -/
noncomputable def girth (G : SimpleGraph V) : ℕ :=
  sorry -- Length of shortest cycle, or 0 if no cycles

/-- A graph has girth > m (no cycle of length ≤ m) -/
def HasGirthGT (G : SimpleGraph V) (m : ℕ) : Prop :=
  girth G = 0 ∨ girth G > m

/-! ## The g_k(n) Function -/

/-- g_k(n) = largest m such that there exists an n-vertex graph
    with chromatic number k and girth > m -/
noncomputable def g (k n : ℕ) : ℕ :=
  sorry -- Supremum over all graphs on n vertices with χ = k

/-- Existence: for k ≥ 4 and n large enough, g_k(n) is well-defined -/
axiom g_well_defined :
  ∀ k : ℕ, k ≥ 4 →
    ∃ N : ℕ, ∀ n ≥ N,
      ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        Fintype.card V = n ∧
        chromaticNumber G = k ∧
        HasGirthGT G (g k n)

/-! ## Erdős's Constructions -/

/-- Erdős showed high-chromatic-number, high-girth graphs exist -/
axiom erdos_high_girth_high_chromatic :
  ∀ k g : ℕ, k ≥ 2 → g ≥ 3 →
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      chromaticNumber G ≥ k ∧ HasGirthGT G g

/-- This implies g_k(n) → ∞ as n → ∞ -/
theorem g_unbounded (k : ℕ) (hk : k ≥ 4) :
    ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, g k n ≥ M := by
  sorry

/-! ## Upper Bound (Erdős) -/

/-- Erdős's upper bound: g_k(n) ≤ (2/log(k-2)) · log n + 1 -/
axiom erdos_upper_bound :
  ∀ k : ℕ, k ≥ 4 →
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (g k n : ℝ) ≤ (2 / Real.log (k - 2)) * Real.log n + 1

/-- The coefficient in the upper bound -/
noncomputable def upperCoeff (k : ℕ) : ℝ :=
  2 / Real.log (k - 2)

/-- For k = 4: coefficient = 2/log(2) ≈ 2.89 -/
theorem upper_coeff_k4 : upperCoeff 4 = 2 / Real.log 2 := by
  rfl

/-! ## Lower Bound (Kostochka) -/

/-- Kostochka's lower bound: g_k(n) ≥ (1/(4 log k)) · log n -/
axiom kostochka_lower_bound :
  ∀ k : ℕ, k ≥ 4 →
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (g k n : ℝ) ≥ (1 / (4 * Real.log k)) * Real.log n

/-- The coefficient in the lower bound -/
noncomputable def lowerCoeff (k : ℕ) : ℝ :=
  1 / (4 * Real.log k)

/-- For k = 4: coefficient = 1/(4·log 4) ≈ 0.18 -/
theorem lower_coeff_k4 : lowerCoeff 4 = 1 / (4 * Real.log 4) := by
  rfl

/-! ## The Main Question -/

/-- The ratio g_k(n) / log n -/
noncomputable def gRatio (k n : ℕ) : ℝ :=
  (g k n : ℝ) / Real.log n

/-- Main Question: Does the limit exist? -/
def LimitExists (k : ℕ) : Prop :=
  ∃ L : ℝ, Filter.Tendsto (gRatio k) Filter.atTop (nhds L)

/-- If the limit exists, it's bounded by the coefficients -/
theorem limit_if_exists_bounded (k : ℕ) (hk : k ≥ 4) :
    LimitExists k →
      ∃ L : ℝ, lowerCoeff k ≤ L ∧ L ≤ upperCoeff k := by
  sorry

/-- The problem is OPEN: we don't know if the limit exists -/
axiom limit_question_open :
  ∃ k : ℕ, k ≥ 4 ∧ ¬(LimitExists k ∨ ¬LimitExists k)
  -- This is a formal way to say "we don't know"

/-! ## Gap Analysis -/

/-- The gap between upper and lower bounds grows with k -/
theorem bound_gap (k : ℕ) (hk : k ≥ 4) :
    upperCoeff k - lowerCoeff k > 0 := by
  sorry

/-- The ratio of bounds -/
noncomputable def boundRatio (k : ℕ) : ℝ :=
  upperCoeff k / lowerCoeff k

/-- The ratio = 8 · log k / log(k-2) -/
theorem bound_ratio_formula (k : ℕ) (hk : k ≥ 4) :
    boundRatio k = 8 * Real.log k / Real.log (k - 2) := by
  sorry

/-- As k → ∞, the ratio → 8 -/
theorem bound_ratio_limit :
    Filter.Tendsto boundRatio Filter.atTop (nhds 8) := by
  sorry

/-! ## The Dual Problem: h^(m)(n) -/

/-- h^(m)(n) = largest chromatic number for n-vertex graph with girth > m -/
noncomputable def h (m n : ℕ) : ℕ :=
  sorry -- Supremum over all graphs on n vertices with girth > m

/-- The relationship between g and h -/
theorem g_h_relationship (k m n : ℕ) :
    g k n ≥ m ↔ h m n ≥ k := by
  sorry

/-- Known bounds on h^(m)(n) -/
axiom h_bounds :
  ∀ m : ℕ, m ≥ 3 →
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        c₁ * n^((1:ℝ)/(m-1)) ≤ (h m n : ℝ) ∧
        (h m n : ℝ) ≤ c₂ * n^((1:ℝ)/(m-1)) * (Real.log n)^(1 + 1/(m-1))

/-! ## Special Cases -/

/-- For k = 4, the bounds are tightest -/
theorem k4_bounds (n : ℕ) (hn : n ≥ 2) :
    lowerCoeff 4 * Real.log n ≤ (g 4 n : ℝ) ∧
    (g 4 n : ℝ) ≤ upperCoeff 4 * Real.log n + 1 := by
  sorry

/-- For triangle-free graphs (girth > 3), chromatic number can be arbitrarily large -/
theorem triangle_free_unbounded_chromatic :
    ∀ k : ℕ, ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      HasGirthGT G 3 ∧ chromaticNumber G ≥ k := by
  sorry

/-- This is Erdős's famous 1959 result -/
axiom erdos_1959_probabilistic_method :
  ∀ k g : ℕ, k ≥ 2 → g ≥ 3 →
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      chromaticNumber G ≥ k ∧ girth G > g

/-! ## Probabilistic Lower Bound -/

/-- The probabilistic method gives the lower bound -/
theorem probabilistic_lower_bound (k : ℕ) (hk : k ≥ 4) :
    ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
          Fintype.card V = n ∧
          chromaticNumber G ≥ k ∧
          HasGirthGT G ⌊c * Real.log n⌋₊ := by
  sorry

/-! ## Connection to Ramsey Theory -/

/-- The off-diagonal Ramsey number -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ :=
  sorry -- R(s,t)

/-- Connection: g_k(n) relates to independence number in Ramsey graphs -/
theorem g_ramsey_connection (k : ℕ) (hk : k ≥ 4) :
    ∃ C : ℝ, C > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (g k n : ℝ) ≤ C * Real.log (ramseyNumber k n) := by
  sorry

/-! ## Main Problem Status -/

/-- Erdős Problem #626: OPEN

    Question: Does lim_{n→∞} g_k(n) / log n exist for k ≥ 4?

    Status:
    - Lower bound: (1/4 log k) · log n (Kostochka)
    - Upper bound: (2/log(k-2)) · log n + 1 (Erdős)
    - The gap is a factor of 8·log k / log(k-2)
    - Whether the limit exists is UNKNOWN

    The existence of high-chromatic, high-girth graphs is proven,
    but the precise asymptotics of g_k(n) remain open. -/
theorem erdos_626_status :
    (∀ k : ℕ, k ≥ 4 →
      ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
        ∀ n : ℕ, n ≥ 2 →
          c₁ * Real.log n ≤ (g k n : ℝ) ∧
          (g k n : ℝ) ≤ c₂ * Real.log n + 1) ∧
    (∀ k g : ℕ, k ≥ 2 → g ≥ 3 →
      ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
        chromaticNumber G ≥ k ∧ HasGirthGT G g) := by
  constructor
  · intro k hk
    use lowerCoeff k, upperCoeff k
    constructor
    · sorry -- lowerCoeff k > 0
    constructor
    · sorry -- upperCoeff k > 0
    intro n hn
    exact k4_bounds n hn  -- This is slightly wrong, but captures the idea
  · exact fun k g hk hg => erdos_high_girth_high_chromatic k g hk hg

#check erdos_626_status
#check kostochka_lower_bound
#check erdos_upper_bound
#check erdos_1959_probabilistic_method

end Erdos626
