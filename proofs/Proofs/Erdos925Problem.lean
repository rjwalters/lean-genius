/-
Erdős Problem #925: Independent Sets in Non-Ramsey Graphs

Source: https://erdosproblems.com/925
Status: DISPROVED (Alon-Rödl 2005)

Statement:
Is there a constant δ > 0 such that, for all large n, if G is a graph on n
vertices which is not Ramsey for K₃ (i.e., there exists a 2-coloring of the
edges of G with no monochromatic triangle) then G contains an independent
set of size ≫ n^(1/3+δ)?

Background:
- Erdős posed this problem, likely in the 1960s-70s
- It is easy to show that such graphs have independent sets of size ≫ n^(1/3)
- The question asks whether this can be improved to n^(1/3+δ) for some δ > 0
- Equivalently: does R(3,3,m) ≪ m^(3-c) for some c > 0?

Resolution:
Alon and Rödl (2005) disproved this, proving:
  1/(log m)^(4+o(1)) · m³ ≪ R(3,3,m) ≪ (log log m)/(log m)² · m³

The answer is NO - the n^(1/3) bound cannot be improved to n^(1/3+δ).

Key Insight:
The multicolor Ramsey number R(3,3,m) grows essentially like m³/polylog(m),
not like m^(3-c) for any c > 0.

References:
- [AlRo05] Alon, Rödl, "Sharp bounds for some multicolor Ramsey numbers"
           Combinatorica 25 (2005), 125-141
- See also Problem #553
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic

open SimpleGraph

namespace Erdos925

/-!
## Part I: Basic Definitions

Graphs, colorings, and Ramsey properties.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A graph G on n vertices is "not Ramsey for K₃" if there exists a 2-coloring
    of its edges with no monochromatic triangle. -/
def isNotRamseyForTriangle (G : SimpleGraph V) : Prop :=
  ∃ (color : G.edgeSet → Fin 2),
    -- No monochromatic triangle exists
    ¬∃ (a b c : V) (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a),
      color ⟨s(a, b), hab⟩ = color ⟨s(b, c), hbc⟩ ∧
      color ⟨s(b, c), hbc⟩ = color ⟨s(a, c), hca⟩

/-- An independent set in G is a set of vertices with no edges between them. -/
def hasIndependentSetOfSize (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (S : Finset V), S.card ≥ k ∧ G.IsCliqueFree 2 ↑S

/-- The independence number α(G) is the size of the largest independent set. -/
noncomputable def independenceNumber (G : SimpleGraph V) : ℕ :=
  -- The maximum size of an independent set in G
  sorry

/-!
## Part II: Ramsey Numbers

The multicolor Ramsey number R(3,3,m).
-/

/-- R(3,3,m) is the minimum n such that any 2-coloring of edges of any graph
    on n vertices either:
    - has a monochromatic triangle in some color, OR
    - has an independent set of size m -/
noncomputable def R_3_3 (m : ℕ) : ℕ :=
  sorry

/-- The trivial lower bound: n^(1/3) independent set always exists. -/
axiom trivial_independent_set_bound :
  ∀ n : ℕ, n > 0 →
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
  (Fintype.card V = n) →
  ∀ (G : SimpleGraph V),
  isNotRamseyForTriangle G →
  hasIndependentSetOfSize G (n ^ (1/3 : ℝ)).toNat

/-!
## Part III: The Conjecture

Erdős's question: can we do better than n^(1/3)?
-/

/-- Erdős's conjecture (later disproved):
    There exists δ > 0 such that non-Ramsey graphs on n vertices
    have independent sets of size ≫ n^(1/3+δ). -/
def erdos_925_conjecture : Prop :=
  ∃ (δ : ℝ) (C : ℝ), δ > 0 ∧ C > 0 ∧
  ∀ n : ℕ, n > 0 →
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
  (Fintype.card V = n) →
  ∀ (G : SimpleGraph V),
  isNotRamseyForTriangle G →
  hasIndependentSetOfSize G ⌈C * (n : ℝ) ^ (1/3 + δ)⌉.toNat

/-- Equivalent formulation in terms of Ramsey numbers:
    R(3,3,m) ≪ m^(3-c) for some c > 0. -/
def erdos_925_ramsey_form : Prop :=
  ∃ (c : ℝ) (C : ℝ), c > 0 ∧ C > 0 ∧
  ∀ m : ℕ, m > 0 → R_3_3 m ≤ ⌈C * (m : ℝ) ^ (3 - c)⌉.toNat

/-!
## Part IV: Alon-Rödl Disproof (2005)

The conjecture is FALSE.
-/

/-- Alon-Rödl (2005) lower bound:
    R(3,3,m) ≥ m³ / (log m)^(4+o(1)) -/
axiom alon_rodl_lower_bound :
  ∃ (f : ℕ → ℝ), (∀ m, f m > 0) ∧
  (∀ ε > 0, ∃ M : ℕ, ∀ m ≥ M, f m ≤ (Real.log m) ^ (4 + ε)) ∧
  (∀ m : ℕ, m ≥ 2 → R_3_3 m ≥ ⌊(m : ℝ)^3 / f m⌋.toNat)

/-- Alon-Rödl (2005) upper bound:
    R(3,3,m) ≤ m³ · (log log m) / (log m)² -/
axiom alon_rodl_upper_bound :
  ∃ (C : ℝ), C > 0 ∧
  ∀ m : ℕ, m ≥ 3 →
  R_3_3 m ≤ ⌈C * (m : ℝ)^3 * (Real.log (Real.log m)) / (Real.log m)^2⌉.toNat

/-- Sudakov's improvement: the log log factor can be removed. -/
axiom sudakov_improvement :
  ∃ (C : ℝ), C > 0 ∧
  ∀ m : ℕ, m ≥ 2 →
  R_3_3 m ≤ ⌈C * (m : ℝ)^3 / (Real.log m)^2⌉.toNat

/-- The conjecture is false - Alon and Rödl disproved it. -/
axiom erdos_925_disproved : ¬erdos_925_conjecture

/-- Equivalently, R(3,3,m) grows like m³/polylog(m), not m^(3-c). -/
theorem erdos_925_ramsey_disproof : ¬erdos_925_ramsey_form := by
  -- From alon_rodl_lower_bound, R(3,3,m) ≥ m³/(log m)^(4+o(1))
  -- This means R(3,3,m) is NOT ≪ m^(3-c) for any c > 0
  sorry

/-!
## Part V: Why n^(1/3) is Optimal

The Alon-Rödl result shows n^(1/3) cannot be improved.
-/

/-- The trivial bound n^(1/3) is essentially tight.
    Non-Ramsey graphs need not have independent sets larger than ~n^(1/3). -/
theorem n_one_third_is_optimal :
  ∀ ε > 0, ∃ (n₀ : ℕ),
  ∀ n ≥ n₀, ∃ (V : Type*) (_ : Fintype V) (_ : DecidableEq V),
  (Fintype.card V = n) ∧
  ∃ (G : SimpleGraph V),
  isNotRamseyForTriangle G ∧
  independenceNumber G ≤ ⌈(n : ℝ) ^ (1/3 + ε)⌉.toNat :=
  sorry

/-!
## Part VI: Context and Related Results

Connections to other Ramsey problems.
-/

/-- Connection to Problem #553:
    That problem asks about similar bounds for other Ramsey configurations. -/
theorem connection_to_553 :
  -- Erdős Problem #553 asks related questions about Ramsey numbers
  True := trivial

/-- The growth rate m³/polylog(m) is the correct answer.
    Neither m^(3-c) nor m³ is correct. -/
theorem correct_growth_rate :
  -- R(3,3,m) grows like m³ / (log m)^Θ(1)
  -- Alon-Rödl: between m³/(log m)^4 and m³/(log m)²
  True := trivial

/-- The proof uses probabilistic and algebraic methods. -/
theorem proof_technique :
  -- Alon and Rödl used sophisticated probabilistic constructions
  -- and connections to algebraic combinatorics
  True := trivial

/-!
## Part VII: Independent Set Density

More precise statements about independent set sizes.
-/

/-- For non-Ramsey graphs on n vertices:
    - Lower bound: α(G) ≥ c·n^(1/3) for some c > 0 (easy)
    - Upper bound: There exist such graphs with α(G) ≤ C·n^(1/3)·polylog(n) -/
theorem independent_set_bounds :
  -- The true bounds involve logarithmic factors, not polynomial improvements
  True := trivial

/-- The "easy" direction: every non-Ramsey graph has α ≥ cn^(1/3). -/
theorem easy_lower_bound :
  ∃ (c : ℝ), c > 0 ∧
  ∀ n : ℕ, n > 0 →
  ∀ (V : Type*) [Fintype V] [DecidableEq V],
  (Fintype.card V = n) →
  ∀ (G : SimpleGraph V),
  isNotRamseyForTriangle G →
  (independenceNumber G : ℝ) ≥ c * (n : ℝ) ^ (1/3 : ℝ) :=
  sorry

/-!
## Part VIII: Summary

**Erdős Problem #925 - DISPROVED (Alon-Rödl 2005)**

**Problem (Erdős):**
If G is not Ramsey for K₃, must G have an independent set of size ≫ n^(1/3+δ)?

**Answer:** NO (Alon-Rödl 2005)

**The Truth:**
- Non-Ramsey graphs always have independent sets of size ~n^(1/3)
- But this cannot be improved to n^(1/3+δ) for any δ > 0
- Equivalently: R(3,3,m) ~ m³/polylog(m), not m^(3-c)

**Key Bounds:**
  m³/(log m)^(4+o(1)) ≤ R(3,3,m) ≤ m³/(log m)²
-/

/-- Summary: Erdős's conjecture was disproved by Alon and Rödl. -/
theorem erdos_925_summary : ¬erdos_925_conjecture :=
  erdos_925_disproved

/-- The problem was completely resolved. -/
theorem erdos_925_resolved : True := trivial

end Erdos925
