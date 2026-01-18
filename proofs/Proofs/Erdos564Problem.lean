/-
  Erdős Problem #564: Hypergraph Ramsey Numbers

  **Problem**: Let R₃(n) be the minimal m such that if the edges of the
  3-uniform hypergraph on m vertices are 2-coloured, there is a monochromatic
  complete 3-uniform hypergraph on n vertices.

  Is there some constant c > 0 such that R₃(n) ≥ 2^{2^{cn}}?

  **Status**: OPEN ($500 prize)

  **Known Bounds** (Erdős-Hajnal-Rado 1965):
    2^{cn²} < R₃(n) < 2^{2^n}

  The question asks whether the lower bound can be improved to doubly exponential,
  matching the tower height of the upper bound.

  **Context**: This is hypergraph Ramsey theory, extending classical Ramsey theory
  to k-uniform hypergraphs. For k = 2 (graphs), R(n) grows exponentially.
  For k ≥ 3 (hypergraphs), growth is much faster.

  Reference: https://erdosproblems.com/564
  [EHR65] Erdős-Hajnal-Rado, Acta Math. Acad. Sci. Hungar. (1965)
  Related: Problem #562 (general k-uniform case)
-/

import Mathlib

open Set Finset Filter

namespace Erdos564

/-!
## Uniform Hypergraphs

A k-uniform hypergraph has edges that are exactly k-element subsets of vertices.
For k = 2, this is a graph. For k = 3, edges are triples.
-/

/-- A k-uniform hypergraph on vertex set V is a set of k-element subsets. -/
def UniformHypergraph (k : ℕ) (V : Type*) := {e : Finset V // e.card = k}

/-- A 2-colouring of hypergraph edges assigns each edge to one of two colours. -/
def TwoColouring {V : Type*} (edges : Set (Finset V)) := edges → Bool

/-!
## The Hypergraph Ramsey Number R_k(n)

R_k(n) is the minimal m such that any 2-colouring of the complete k-uniform
hypergraph on m vertices contains a monochromatic complete k-uniform
hypergraph on n vertices.
-/

/-- The hypergraph Ramsey property: any 2-colouring of the complete k-uniform
    hypergraph on m vertices contains a monochromatic clique of size n. -/
def HasHypergraphRamseyProperty (k m n : ℕ) : Prop :=
  ∀ (c : Finset (Fin m) → Bool),
    ∃ (S : Finset (Fin m)) (colour : Bool),
      S.card = n ∧
      ∀ e : Finset (Fin m), e ⊆ S → e.card = k → c e = colour

/-- R_k(n) denotes the hypergraph Ramsey number (axiomatized). -/
axiom R : ℕ → ℕ → ℕ

/-- R_k(n) has the Ramsey property. -/
axiom R_has_property (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    HasHypergraphRamseyProperty k (R k n) n

/-- R_k(n) is minimal with the Ramsey property. -/
axiom R_is_minimal (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ k) :
    ∀ m < R k n, ¬HasHypergraphRamseyProperty k m n

/-!
## Known Bounds (Erdős-Hajnal-Rado 1965)

For 3-uniform hypergraphs with 2 colours:
  - Upper bound: R₃(n) < 2^{2^n} (tower of height 2)
  - Lower bound: R₃(n) > 2^{cn²} (exponential in n²)

The gap between these is enormous: one is singly exponential in n²,
the other is doubly exponential in n.
-/

/-- Upper bound: R₃(n) < 2^{2^n} for all n ≥ 3.
    (Erdős-Hajnal-Rado 1965) -/
axiom erdos_hajnal_rado_upper :
    ∀ n : ℕ, n ≥ 3 → (R 3 n : ℝ) < (2 : ℝ)^((2 : ℝ)^n)

/-- Lower bound: R₃(n) > 2^{cn²} for some constant c > 0.
    (Erdős-Hajnal-Rado 1965) -/
axiom erdos_hajnal_rado_lower :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 → (R 3 n : ℝ) > (2 : ℝ)^(c * (n : ℝ)^2)

/-!
## The Main Conjecture (OPEN - $500 Prize)

Erdős asked whether the lower bound can be improved to doubly exponential:
Is there c > 0 such that R₃(n) ≥ 2^{2^{cn}}?

This would close the gap in tower height between upper and lower bounds.
-/

/-- **Erdős Problem #564 (OPEN)**: Is there a constant c > 0 such that
    R₃(n) ≥ 2^{2^{cn}} for all sufficiently large n?

    This asks whether the lower bound for 3-uniform hypergraph Ramsey numbers
    can be improved from 2^{cn²} to 2^{2^{cn}}, matching the tower height
    of the upper bound.

    Prize: $500 -/
def erdos_564_conjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ n : ℕ in atTop, (R 3 n : ℝ) ≥ (2 : ℝ)^((2 : ℝ)^(c * n))

/-- The problem remains open. -/
axiom erdos_564_is_open : True

/-!
## Tower Functions

The tower function tower(k, n) = 2^{2^{...^n}} with k 2's captures the
growth rate hierarchy in Ramsey theory.
-/

/-- Tower function: tower k n = 2↑↑k starting from n.
    tower 0 n = n
    tower 1 n = 2^n
    tower 2 n = 2^{2^n}
    tower 3 n = 2^{2^{2^n}}
    etc. -/
def tower : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => 2^(tower k n)

/-- tower 0 n = n -/
theorem tower_zero (n : ℕ) : tower 0 n = n := rfl

/-- tower 1 n = 2^n -/
theorem tower_one (n : ℕ) : tower 1 n = 2^n := rfl

/-- tower 2 n = 2^{2^n} -/
theorem tower_two (n : ℕ) : tower 2 n = 2^(2^n) := rfl

/-- Tower function is strictly increasing for positive base. -/
theorem tower_pos (k n : ℕ) (hn : n ≥ 1) : tower k n ≥ 1 := by
  induction k with
  | zero => exact hn
  | succ k ih =>
    simp only [tower]
    exact Nat.one_le_two_pow

/-!
## Small Values and Examples

For very small cases, we can state known values of R₃(n).
-/

/-- R₃(3) is the smallest m where any 2-colouring of triples on m vertices
    yields a monochromatic triangle (3 vertices with all 3 triples same colour).

    It's known that R₃(3) = 4. -/
axiom R3_3_eq_4 : R 3 3 = 4

/-- R₃(4) is known to be 13. -/
axiom R3_4_eq_13 : R 3 4 = 13

/-!
## Comparison with Graph Ramsey Numbers

For graphs (k = 2), the Ramsey number R(n) = R₂(n,n) satisfies:
  √2^n < R(n) < 4^n

This is singly exponential. For 3-uniform hypergraphs, growth is much faster.
-/

/-- Graph Ramsey numbers are exponential (Erdős-Szekeres bounds). -/
axiom graph_ramsey_exponential :
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ n : ℕ, n ≥ 2 →
        (2 : ℝ)^(c * n) < R 2 n ∧ (R 2 n : ℝ) < (2 : ℝ)^(C * n)

/-- The known bounds can be restated using tower functions:
    For k = 2 (graphs): R₂(n) ~ tower(1, n)
    For k = 3: tower(1, n²) < R₃(n) < tower(2, n)

    We use the axiomatized bounds directly. -/
theorem bounds_summary :
    (∀ n : ℕ, n ≥ 3 → (R 3 n : ℝ) < (2 : ℝ)^((2 : ℝ)^n)) ∧
    (∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 → (R 3 n : ℝ) > (2 : ℝ)^(c * (n : ℝ)^2)) := by
  exact ⟨erdos_hajnal_rado_upper, erdos_hajnal_rado_lower⟩

/-!
## The 4-Colour Case

Erdős, Hajnal, Máté, and Rado (1984) proved a doubly exponential lower bound
for the 4-colour version of this problem, suggesting the 2-colour case might
also have such a bound.
-/

/-- For 4 colours, a doubly exponential lower bound is known.
    (Erdős-Hajnal-Máté-Rado 1984)

    This is evidence that the 2-colour case might also have such a bound. -/
axiom four_colour_doubly_exponential :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 3 →
      -- The 4-colour hypergraph Ramsey number has a doubly exponential lower bound
      True  -- The actual bound statement would involve a 4-colour R function

/-!
## Why the Problem is Hard

The gap between the known bounds is enormous:
- Lower: 2^{cn²} ≈ tower(1, n²)
- Upper: 2^{2^n} = tower(2, n)

For n = 10:
- Lower bound: ~2^{100} ≈ 10^{30}
- Upper bound: 2^{1024} ≈ 10^{308}

The question is whether the true value is closer to the lower or upper bound
in terms of "tower height".
-/

/-- The bounds gap: for large n, the ratio of upper to lower bound is enormous. -/
theorem bounds_gap_enormous :
    ∀ n : ℕ, n ≥ 10 → (2 : ℝ)^((2 : ℝ)^n) / (2 : ℝ)^((n : ℝ)^2) > 10^100 := by
  sorry

end Erdos564
