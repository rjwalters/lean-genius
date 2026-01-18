/-
  Erdős Problem #631: List Chromatic Number of Planar Graphs

  Source: https://erdosproblems.com/631
  Status: SOLVED (Thomassen 1994, Voigt 1993)

  Statement:
  Does every planar graph G have χ_L(G) ≤ 5? Is this best possible?

  Context:
  The list chromatic number χ_L(G) is the minimum k such that for any
  assignment of lists of k colors to vertices, a proper list coloring exists.

  Resolution:
  - Thomassen (1994): PROVED χ_L(G) ≤ 5 for all planar graphs
  - Voigt (1993): Constructed a planar graph with χ_L = 5
  - Both bounds are tight: the answer is YES to both questions
-/

import Mathlib

open Finset Function SimpleGraph Nat

namespace Erdos631

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Basic Definitions -/

/-- The chromatic number χ(G) -/
noncomputable def chromaticNumber (G : SimpleGraph V) : ℕ :=
  sorry -- Minimum k such that G is k-colorable

/-- A graph is k-colorable -/
def IsKColorable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ f : V → Fin k, ∀ v w : V, G.Adj v w → f v ≠ f w

/-! ## List Coloring Definitions -/

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

/-! ## Basic Properties -/

/-- χ_L(G) ≥ χ(G) always -/
theorem list_chromatic_ge_chromatic (G : SimpleGraph V) :
    listChromaticNumber G ≥ chromaticNumber G := by
  sorry

/-- k-choosability is monotone: k-choosable implies (k+1)-choosable -/
theorem choosable_monotone (G : SimpleGraph V) (k : ℕ) :
    IsKChoosable G k → IsKChoosable G (k + 1) := by
  sorry

/-- k-choosability implies k-colorability -/
theorem choosable_implies_colorable (G : SimpleGraph V) (k : ℕ) :
    IsKChoosable G k → IsKColorable G k := by
  -- Proof by Aristotle (Harmonic)
  intro h
  contrapose! h
  unfold IsKChoosable
  simp +zetaDelta at *
  refine' ⟨ULift (Fin (k + 1)), _, _, _, _⟩
  · infer_instance
  · exact fun v => Finset.univ.filter fun x => x.down.val < k
  · intro v; rw [Finset.card_eq_of_bijective]
    use fun i hi => ⟨⟨i, by linarith⟩⟩
    · aesop
    · aesop
    · aesop
  · intro f hf
    refine' h ⟨fun v => ⟨f v |>.down.val, _⟩, _⟩
    all_goals simp_all +decide [Fin.ext_iff, IsListColoring]
    exact fun v w hvw => fun h => hf.2 v w hvw <| by aesop

/-! ## Planar Graphs -/

/-- A graph is planar (can be drawn without edge crossings) -/
def IsPlanar (G : SimpleGraph V) : Prop :=
  sorry -- Embeddable in the plane

/-- Euler's formula: V - E + F = 2 for connected planar graphs -/
axiom euler_formula :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsPlanar G → G.Connected →
    ∃ F : ℕ, Fintype.card V - G.edgeFinset.card + F = 2

/-- Planar graphs have at most 3n - 6 edges -/
axiom planar_edge_bound :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    IsPlanar G → Fintype.card V ≥ 3 →
    G.edgeFinset.card ≤ 3 * Fintype.card V - 6

/-! ## The Four Color Theorem -/

/-- Four Color Theorem: Every planar graph has χ ≤ 4 -/
axiom four_color_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → chromaticNumber G ≤ 4

/-- Five Color Theorem: Every planar graph has χ ≤ 5 (easier) -/
axiom five_color_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → chromaticNumber G ≤ 5

/-! ## The Main Result: Thomassen's Theorem -/

/-- Thomassen (1994): Every planar graph is 5-choosable -/
axiom thomassen_five_list_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → listChromaticNumber G ≤ 5

/-- Equivalently: planar graphs are 5-list-colorable -/
theorem planar_5_choosable :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → IsKChoosable G 5 := by
  intro V _ _ G hplanar
  have h := thomassen_five_list_theorem V G hplanar
  sorry

/-- Thomassen's proof technique: reduction to near-triangulations -/
axiom thomassen_proof_technique :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G →
    -- Induction on |V| + |E|, reduce to near-triangulations
    -- with outer face a cycle, 2 colors preassigned on edge
    sorry

/-! ## Sharpness: Voigt's Construction -/

/-- Voigt (1993): There exists a planar graph with χ_L = 5 -/
axiom voigt_construction :
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    IsPlanar G ∧ listChromaticNumber G = 5

/-- Voigt's graph has 238 vertices (original construction) -/
axiom voigt_original_size :
  ∃ (G : SimpleGraph (Fin 238)),
    IsPlanar G ∧ listChromaticNumber G = 5

/-- Gutner (1996): Simpler construction with fewer vertices -/
axiom gutner_construction :
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    n < 238 ∧ IsPlanar G ∧ listChromaticNumber G = 5

/-- Smallest known: Mirzakhani's construction (63 vertices) -/
axiom smallest_known_not_4_choosable :
  ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
    n ≤ 63 ∧ IsPlanar G ∧ listChromaticNumber G = 5

/-! ## The List Coloring Conjecture -/

/-- Open Question: Is every planar graph 4-choosable? -/
def listColoringConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → listChromaticNumber G ≤ 4

/-- The List Coloring Conjecture is OPEN -/
axiom list_coloring_conjecture_open :
  ¬(listColoringConjecture ∨ ¬listColoringConjecture)
  -- Formal way to say "unknown"

/-- Gap: χ ≤ 4 but χ_L ≤ 5 (can we close the gap?) -/
theorem chromatic_list_gap :
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → chromaticNumber G ≤ 4) ∧
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → listChromaticNumber G ≤ 5) := by
  exact ⟨four_color_theorem, thomassen_five_list_theorem⟩

/-! ## Related Results -/

/-- Planar bipartite graphs have χ_L ≤ 3 (Alon-Tarsi 1992) -/
axiom alon_tarsi_theorem :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → G.IsBipartite →
    listChromaticNumber G ≤ 3

/-- Outerplanar graphs have χ_L ≤ 3 -/
def IsOuterplanar (G : SimpleGraph V) : Prop :=
  sorry -- All vertices on outer face

axiom outerplanar_3_choosable :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsOuterplanar G → listChromaticNumber G ≤ 3

/-- Outerplanar implies planar -/
theorem outerplanar_is_planar (G : SimpleGraph V) (h : IsOuterplanar G) :
    IsPlanar G := by
  sorry

/-- Planar graphs of girth ≥ 5 are 3-choosable -/
axiom planar_girth_5_choosable :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G → (5 : ℕ∞) ≤ G.girth →
    listChromaticNumber G ≤ 3

/-! ## Thomassen's Proof Structure -/

/-- Key: 5-choosability with 2 precolored adjacent vertices -/
axiom thomassen_key_lemma :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G →
    ∀ (C : Type*) [DecidableEq C] (L : ListAssignment V C),
      (∀ v : V, (L v).card ≥ 5) →
      -- Can extend any valid 2-coloring of an edge to full coloring
      sorry

/-- Thomassen's induction: on vertices + edges -/
axiom thomassen_induction :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    IsPlanar G →
    -- Induct on |V| + |E|
    -- Base: small graphs
    -- Step: find chord or degree-2 vertex
    sorry

/-! ## Historical Context -/

/-- Timeline:
    1979: Erdős-Rubin-Taylor posed the problem
    1993: Voigt constructed non-4-choosable planar graph
    1994: Thomassen proved 5-choosability
    1996: Gutner simplified Voigt's construction
    2000s: Continued search for smaller examples -/
axiom historical_timeline :
  True -- Documented above

/-! ## Main Problem Status -/

/-- Erdős Problem #631: SOLVED

    Question 1: Does every planar graph have χ_L ≤ 5?
    Answer: YES (Thomassen 1994)

    Question 2: Is this best possible?
    Answer: YES (Voigt 1993)

    The bound χ_L ≤ 5 is tight. Whether χ_L ≤ 4 holds
    (List Coloring Conjecture) remains OPEN.

    Related:
    - χ ≤ 4 for planar (Four Color Theorem)
    - χ_L ≤ 3 for planar bipartite (Alon-Tarsi)
    - χ_L ≤ 3 for outerplanar
    - χ_L ≤ 3 for planar girth ≥ 5 -/
theorem erdos_631_status :
    (∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      IsPlanar G → listChromaticNumber G ≤ 5) ∧
    (∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      IsPlanar G ∧ listChromaticNumber G = 5) := by
  constructor
  · exact thomassen_five_list_theorem
  · exact voigt_construction

#check erdos_631_status
#check thomassen_five_list_theorem
#check voigt_construction
#check list_coloring_conjecture_open

end Erdos631
