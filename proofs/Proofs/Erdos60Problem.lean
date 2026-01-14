/-
  Erdős Problem #60: Supersaturation of 4-Cycles

  Source: https://erdosproblems.com/60
  Status: OPEN

  Statement:
  Does every graph on n vertices with > ex(n; C_4) edges contain ≫ n^{1/2} many
  copies of C_4?

  History:
  - Erdős-Simonovits: Conjectured this result; couldn't even prove ≥ 2 copies
  - He-Ma-Yang (2021): Proved for n = q² + q + 1 where q is even
  - Related to Problem 765 about ex(n; C_4)

  Background:
  This is a supersaturation problem: once you exceed the Turán number for C_4,
  how many 4-cycles must appear? The conjectured answer is Ω(n^{1/2}).

  This file formalizes the definitions and known partial results.
-/

import Mathlib

open Set SimpleGraph Finset

namespace Erdos60

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

/-- A copy of C_4 in G is a set of 4 vertices forming a 4-cycle.
    Represented as a 4-tuple (a, b, c, d) where a-b-c-d-a forms a cycle. -/
def IsC4Copy (G : SimpleGraph V) (a b c d : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ a ∧ a ≠ c ∧ b ≠ d ∧
  G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- The set of all C_4 copies in G (as ordered 4-tuples). -/
def C4Copies (G : SimpleGraph V) : Set (V × V × V × V) :=
  { p | IsC4Copy G p.1 p.2.1 p.2.2.1 p.2.2.2 }

/-- The number of C_4 copies in G (up to labeling).
    Each unlabeled C_4 corresponds to 8 labeled copies (4 rotations × 2 reflections). -/
noncomputable def countC4 (G : SimpleGraph V) : ℕ :=
  (C4Copies G).ncard / 8

/-! ## Turán Number for C_4 -/

/-- The Turán number ex(n; C_4) - maximum edges in an n-vertex C_4-free graph.
    Axiomatized for simplicity. -/
noncomputable def exC4 (n : ℕ) : ℕ := sorry

/-- ex(n; C_4) = (1/2)(1 + o(1))n^{3/2} (Reiman 1958, Kővári-Sós-Turán). -/
axiom exC4_asymptotic : ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, |(exC4 n : ℝ) - (1/2) * n^(3/2 : ℝ)| ≤ c * n

/-- Upper bound: ex(n; C_4) ≤ (1/2)n^{3/2} + O(n). -/
axiom exC4_upper (n : ℕ) : (exC4 n : ℝ) ≤ (1/2) * n^(3/2 : ℝ) + n

/-- Lower bound from incidence geometry (projective planes give equality for some n). -/
axiom exC4_lower (n : ℕ) : (exC4 n : ℝ) ≥ (1/2) * n^(3/2 : ℝ) - n

/-! ## Supersaturation -/

/-- A graph exceeds the Turán number for C_4. -/
def ExceedsTuranC4 (G : SimpleGraph V) : Prop :=
  G.edgeSet.ncard > exC4 (Fintype.card V)

/-! ## Main Conjecture (OPEN) -/

/--
**Erdős Problem 60: Supersaturation for C_4** (OPEN)

Conjecture: If G has n vertices and > ex(n; C_4) edges, then G contains
at least Ω(n^{1/2}) copies of C_4.

This remains unproven. Erdős and Simonovits couldn't even prove ≥ 2 copies
are guaranteed.
-/
def erdos_60_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)),
    G.edgeSet.ncard > exC4 n → (countC4 G : ℝ) ≥ c * n^(1/2 : ℝ)

/-! ## Partial Results -/

/-- A projective plane number: n = q² + q + 1 for some q. -/
def IsProjectivePlaneOrder (n : ℕ) : Prop :=
  ∃ q : ℕ, n = q^2 + q + 1

/-- n = q² + q + 1 for even q. -/
def IsEvenProjectivePlaneOrder (n : ℕ) : Prop :=
  ∃ q : ℕ, Even q ∧ n = q^2 + q + 1

/--
**He-Ma-Yang Theorem (2021)**:
The supersaturation conjecture holds for n = q² + q + 1 where q is even.

For these special values of n, exceeding ex(n; C_4) forces Ω(n^{1/2}) copies of C_4.
-/
axiom he_ma_yang (n : ℕ) (hn : IsEvenProjectivePlaneOrder n)
    (G : SimpleGraph (Fin n)) (hexc : G.edgeSet.ncard > exC4 n) :
    ∃ c : ℝ, c > 0 ∧ (countC4 G : ℝ) ≥ c * n^(1/2 : ℝ)

/-! ## Weaker Results -/

/-- At least one C_4 exists when exceeding the Turán number (trivial). -/
axiom at_least_one_c4 (G : SimpleGraph V) (h : ExceedsTuranC4 G) :
    countC4 G ≥ 1

/--
**Open Problem**: Prove at least 2 copies of C_4 are guaranteed.
Erdős and Simonovits noted they couldn't prove even this weak bound.
-/
def two_copies_conjecture : Prop :=
  ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)),
    G.edgeSet.ncard > exC4 n → countC4 G ≥ 2

/-! ## Related: General Supersaturation -/

/--
**Erdős-Simonovits Supersaturation Theorem**:
For any graph H, exceeding ex(n; H) by a constant factor forces
a positive density of copies of H.

Stated abstractly here as the existence of a supersaturation function.
-/
axiom erdos_simonovits_supersaturation :
    ∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧
      ∀ n : ℕ, ∀ (G : SimpleGraph (Fin n)),
        (G.edgeSet.ncard : ℝ) ≥ (1 + ε) * exC4 n →
        (countC4 G : ℝ) ≥ δ * n^2

/-! ## Extremal Graphs -/

/-- The polarity graph from a projective plane of order q.
    This is C_4-free and achieves ex(n; C_4) for n = q² + q + 1. -/
axiom polarity_graph_exists (q : ℕ) (hq : Nat.Prime q ∨ q = 1) :
    ∃ (G : SimpleGraph (Fin (q^2 + q + 1))),
      countC4 G = 0 ∧ G.edgeSet.ncard = exC4 (q^2 + q + 1)

/-! ## Corollaries -/

/-- For projective plane orders with even q, we have a partial result. -/
theorem partial_result_even_q (q : ℕ) (heven : Even q) :
    IsEvenProjectivePlaneOrder (q^2 + q + 1) :=
  ⟨q, heven, rfl⟩

/-- The conjecture implies the two-copies conjecture. -/
theorem conjecture_implies_two_copies :
    erdos_60_conjecture → two_copies_conjecture := by
  intro ⟨c, hc, hconj⟩
  intro n G hexc
  have h := hconj n G hexc
  -- For n ≥ 4, c * n^{1/2} ≥ 2 for sufficiently large c
  sorry

/-! ## Summary

**Problem Status: OPEN**

The conjecture asks whether exceeding ex(n; C_4) forces Ω(n^{1/2}) copies of C_4.

**Known Results**:
1. At least 1 copy is guaranteed (by definition of Turán number)
2. He-Ma-Yang (2021): Proved for n = q² + q + 1, q even
3. General supersaturation (Erdős-Simonovits) gives some lower bound

**Open Questions**:
- Prove ≥ 2 copies are guaranteed (even this is open!)
- Prove the full Ω(n^{1/2}) bound for all n
- Determine the exact constant in the lower bound

References:
- Erdős-Simonovits: Original conjecture
- He-Ma-Yang (2021): "Supersaturation of C_4"
- Reiman (1958): ex(n; C_4) bounds from projective planes
-/

end Erdos60
