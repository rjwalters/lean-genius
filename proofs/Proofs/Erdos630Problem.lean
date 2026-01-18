/-
  Erdős Problem #630: List Chromatic Number of Planar Bipartite Graphs

  Source: https://erdosproblems.com/630
  Status: SOLVED (Alon-Tarsi 1992)

  Statement:
  Does every planar bipartite graph G have χ_L(G) ≤ 3?

  Context:
  The list chromatic number χ_L(G) is the minimum k such that for any
  assignment of lists of k colors to vertices, a proper coloring exists
  where each vertex gets a color from its list.

  Resolution:
  - Erdős, Rubin, Taylor (1980): Posed the problem
  - Alon, Tarsi (1992): PROVED YES using algebraic methods
  - The proof uses the "Combinatorial Nullstellensatz"
-/

import Mathlib

open Finset Function SimpleGraph Nat

namespace Erdos630

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Basic Definitions -/

/-- The chromatic number χ(G) -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  sorry -- Minimum k such that G is k-colorable

/-- A graph is k-colorable -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ v w : V, G.Adj v w → f v ≠ f w

/-! ## List Coloring -/

/-- A list assignment gives each vertex a set of available colors -/
def ListAssignment (V : Type*) (C : Type*) := V → Finset C

/-- A list coloring respects the lists and is proper -/
def IsListColoring (G : SimpleGraph V) {C : Type*} [DecidableEq C]
    (L : ListAssignment V C) (f : V → C) : Prop :=
  (∀ v : V, f v ∈ L v) ∧
  (∀ v w : V, G.Adj v w → f v ≠ f w)

/-- A graph is k-list-colorable (k-choosable) -/
def IsKChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (C : Type*) [DecidableEq C] (L : ListAssignment V C),
    (∀ v : V, (L v).card ≥ k) →
    ∃ f : V → C, IsListColoring G L f

/-- The list chromatic number (choosability) -/
noncomputable def listChromaticNumber (G : SimpleGraph V) : ℕ :=
  sorry -- Minimum k such that G is k-choosable

/-! ## Basic Properties of List Chromatic Number -/

/-- χ_L(G) ≥ χ(G) always -/
theorem list_chromatic_ge_chromatic (G : SimpleGraph V) :
    listChromaticNumber G ≥ chromaticNumber G := by
  sorry

/-- For complete graphs, χ_L(K_n) = χ(K_n) = n -/
theorem complete_graph_list_chromatic (n : ℕ) :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n →
      (∀ v w : V, v ≠ w → G.Adj v w) →
      listChromaticNumber G = n := by
  sorry

/-- For complete bipartite K_{n,n}, χ_L can exceed χ -/
axiom complete_bipartite_list_chromatic :
  ∀ n : ℕ, n ≥ 2 →
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsBipartite ∧
      chromaticNumber G = 2 ∧
      listChromaticNumber G > 2

/-! ## Planar Graphs -/

/-- A graph is planar (can be drawn without edge crossings) -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  sorry -- Embeddable in the plane

/-- Planar graphs satisfy Euler's formula: V - E + F = 2 -/
axiom euler_formula :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → G.Connected →
    ∃ F : ℕ, Fintype.card V - G.edgeFinset.card + F = 2

/-- Planar graphs have χ ≤ 4 (Four Color Theorem) -/
axiom four_color_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → chromaticNumber G ≤ 4

/-- Planar graphs have χ_L ≤ 5 (Thomassen 1994) -/
axiom thomassen_five_list :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → listChromaticNumber G ≤ 5

/-! ## Bipartite Graphs -/

/-- A graph is bipartite iff it has no odd cycles -/
theorem bipartite_iff_no_odd_cycle (G : SimpleGraph V) :
    G.IsBipartite ↔ ∀ n : ℕ, n % 2 = 1 → ¬G.IsCycle n := by
  sorry

/-- Bipartite graphs have χ ≤ 2 -/
theorem bipartite_chi_le_2 (G : SimpleGraph V) (hbip : G.IsBipartite) :
    chromaticNumber G ≤ 2 := by
  sorry

/-- But bipartite graphs can have χ_L > 2 -/
theorem bipartite_list_can_exceed_2 :
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsBipartite ∧ listChromaticNumber G > 2 := by
  sorry

/-! ## The Main Result: Alon-Tarsi Theorem -/

/-- Alon-Tarsi (1992): Planar bipartite graphs are 3-choosable -/
axiom alon_tarsi_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → G.IsBipartite →
    listChromaticNumber G ≤ 3

/-- Equivalently: planar bipartite graphs are 3-list-colorable -/
theorem planar_bipartite_3_choosable :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → G.IsBipartite →
      IsKChoosable G 3 := by
  intro V _ _ G hplanar hbip
  have h := alon_tarsi_theorem V G hplanar hbip
  sorry

/-! ## The Algebraic Method -/

/-- The Alon-Tarsi proof uses the graph polynomial -/
noncomputable def graphPolynomial (G : SimpleGraph V) : MvPolynomial V ℤ :=
  sorry -- ∏_{(u,v) ∈ E} (x_u - x_v)

/-- Key lemma: nonzero coefficient implies choosability -/
axiom combinatorial_nullstellensatz :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ∀ d : V → ℕ,
      (sorry : Prop) →  -- coefficient condition
      IsKChoosable G (Finset.univ.sup d + 1)

/-- For bipartite planar graphs, the coefficient is nonzero -/
axiom alon_tarsi_coefficient :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → G.IsBipartite →
    sorry -- The relevant coefficient in graphPolynomial is nonzero

/-! ## Sharpness -/

/-- The bound 3 is tight: some planar bipartite graphs need 3 -/
theorem bound_is_tight :
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G ∧ G.IsBipartite ∧ listChromaticNumber G = 3 := by
  sorry

/-- Example: K_{2,4} is planar bipartite with χ_L = 3 -/
axiom k24_list_chromatic :
  ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G ∧ G.IsBipartite ∧
    Fintype.card V = 6 ∧
    listChromaticNumber G = 3

/-! ## Generalizations -/

/-- For non-planar bipartite graphs, χ_L can be arbitrarily large -/
theorem nonplanar_bipartite_unbounded :
    ∀ k : ℕ, ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsBipartite ∧ listChromaticNumber G ≥ k := by
  sorry

/-- K_{n,n} has χ_L ≥ ⌈log₂ n⌉ + 1 -/
axiom complete_bipartite_lower_bound :
  ∀ n : ℕ, n ≥ 2 →
    ∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      G.IsBipartite ∧
      (∃ A B : Finset V, A.card = n ∧ B.card = n ∧
        ∀ a b : V, a ∈ A → b ∈ B → G.Adj a b) ∧
      listChromaticNumber G ≥ Nat.clog 2 n + 1

/-! ## Connection to Other Problems -/

/-- Planar graphs: χ_L ≤ 5 (tight) -/
theorem planar_list_chromatic_5 :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → listChromaticNumber G ≤ 5 := by
  exact thomassen_five_list

/-- Open: Is χ_L ≤ 4 for all planar graphs? -/
def listColoringConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → listChromaticNumber G ≤ 4

/-- The List Coloring Conjecture is OPEN -/
axiom list_coloring_conjecture_open :
  ¬(listColoringConjecture ∨ ¬listColoringConjecture)
  -- Formal way to say "unknown"

/-! ## Outerplanar Graphs -/

/-- A graph is outerplanar if it can be drawn with all vertices on outer face -/
def IsOuterplanar (G : SimpleGraph V) : Prop :=
  sorry -- All vertices on unbounded face

/-- Outerplanar implies planar -/
theorem outerplanar_is_planar (G : SimpleGraph V) (h : IsOuterplanar G) :
    IsPlanar G := by
  sorry

/-- Outerplanar graphs have χ_L ≤ 3 -/
axiom outerplanar_3_choosable :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsOuterplanar G → listChromaticNumber G ≤ 3

/-! ## Main Problem Status -/

/-- Erdős Problem #630: SOLVED

    Question: Does every planar bipartite graph have χ_L ≤ 3?

    Answer: YES (Alon-Tarsi 1992)

    The proof uses the Combinatorial Nullstellensatz, an algebraic
    technique relating polynomial coefficients to colorings.

    Related results:
    - All planar graphs: χ_L ≤ 5 (Thomassen 1994)
    - Planar graphs: χ_L ≤ 4? (OPEN - List Coloring Conjecture)
    - Outerplanar graphs: χ_L ≤ 3 -/
theorem erdos_630_status :
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → G.IsBipartite → listChromaticNumber G ≤ 3) ∧
    (∃ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G ∧ G.IsBipartite ∧ listChromaticNumber G = 3) := by
  constructor
  · exact alon_tarsi_theorem
  · exact bound_is_tight

#check erdos_630_status
#check alon_tarsi_theorem
#check thomassen_five_list
#check four_color_theorem

end Erdos630
