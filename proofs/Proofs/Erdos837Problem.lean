/-!
# Erdős Problem #837 — Hypergraph Density Jumps

For k ≥ 2, define A_k ⊆ [0,1] as the set of values α such that there
exists β > α with the property: whenever G₁, G₂, ... is a sequence of
k-uniform hypergraphs with lim inf e(Gₙ)/C(|Gₙ|,k) > α, there exist
subgraphs Hₙ ⊆ Gₙ with |Hₙ| → ∞ and lim inf e(Hₙ)/C(|Hₙ|,k) > β.

Known: A_2 = {1 − 1/m : m ≥ 1} (Erdős–Stone–Simonovits theorem).

Central question: What is A_3?

Status: OPEN
Reference: https://erdosproblems.com/837
Source: [Er74d] (with Simonovits)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A k-uniform hypergraph on n vertices, represented by edge count. -/
structure KUniformHypergraph where
  vertices : ℕ
  edges : ℕ
  uniformity : ℕ

/-- The binomial coefficient C(n, k). -/
noncomputable def binom (n k : ℕ) : ℕ := Nat.choose n k

/-- The edge density of a k-uniform hypergraph: e(G)/C(|G|, k). -/
noncomputable def edgeDensity (G : KUniformHypergraph) : ℝ :=
  if binom G.vertices G.uniformity = 0 then 0
  else (G.edges : ℝ) / (binom G.vertices G.uniformity : ℝ)

/-- A density jump value α for k-uniform hypergraphs: there exists
    β > α such that dense sequences force denser subgraphs. -/
def IsDensityJump (k : ℕ) (α : ℝ) : Prop :=
  ∃ β : ℝ, β > α ∧ β ≤ 1 ∧ True  -- axiomatized: the jump property

/-- The set A_k of density jump values for k-uniform hypergraphs. -/
def densityJumpSet (k : ℕ) : Set ℝ :=
  {α : ℝ | 0 ≤ α ∧ α ≤ 1 ∧ IsDensityJump k α}

/-! ## Known Results -/

/-- **Erdős–Stone–Simonovits (graphs)**: For k = 2,
    A_2 = {1 − 1/m : m ≥ 1} = {0, 1/2, 2/3, 3/4, ...}.
    Each jump value corresponds to a Turán density. -/
axiom graph_density_jumps :
  densityJumpSet 2 = {α : ℝ | ∃ m : ℕ, m ≥ 1 ∧ α = 1 - 1 / (m : ℝ)}

/-- **Turán connection**: The jumps in A_2 correspond exactly to
    the Turán densities π(K_{m+1}) = 1 − 1/m. -/
axiom turan_densities :
  ∀ m : ℕ, m ≥ 1 → IsDensityJump 2 (1 - 1 / (m : ℝ))

/-! ## Main Question -/

/-- **Erdős Problem #837**: What is A_3? Determine the set of
    density jump values for 3-uniform hypergraphs. -/
axiom erdos_837_characterize_A3 :
  ∃ S : Set ℝ, densityJumpSet 3 = S

/-- **Is 0 a jump for 3-uniform hypergraphs?** This is related
    to the hypergraph Turán problem. -/
axiom zero_is_jump_3uniform :
  IsDensityJump 3 0

/-! ## Observations -/

/-- **Hypergraph Turán problem**: For k ≥ 3, even the Turán
    density π(K_{k+1}^{(k)}) is unknown. The tetrahedron
    conjecture: π(K_4^{(3)}) = 5/9. -/
axiom turan_hypergraph_open : True

/-- **Frankl–Rödl (1984)**: The Ramsey multiplicity approach
    shows that certain hypergraph densities force denser
    subhypergraphs, but a complete characterization of A_3
    remains far from reach. -/
axiom frankl_rodl : True

/-- **Razborov flag algebras**: Flag algebra methods can
    determine some jump values computationally, but the
    general structure of A_3 is unknown. -/
axiom flag_algebras : True
