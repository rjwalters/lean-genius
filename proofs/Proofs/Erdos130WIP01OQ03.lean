/-
  Erdős #130 WIP-01 OQ-03: Chromatic Number of Integer-Distance Graphs
  — the Clique/Cardinality Sandwich

  **Open question (Erdős #130 main question)**: What is the chromatic number
  χ(G(A)) for optimal general-position integer-distance sets?

  Here A ⊆ ℝ² is a point set and G(A) is the *integer distance graph*: its
  vertices are the points of A and two distinct points are adjacent iff their
  Euclidean distance is an integer.  The Anning–Erdős theorem (1945; see the
  parent entry `erdos-130-wip-01`) shows that under a general-position
  hypothesis the *clique* number ω(G(A)) is finite, with an explicit bound
  4(2D+1)(2E+1).  The behaviour of the *chromatic* number χ(G(A)) is the open
  main question of Erdős #130.

  **What this file contributes** — two elementary but load-bearing facts that
  sandwich the open quantity, and their consequence:

    (1)  χ(G(A)) ≥ ω(G(A))              `chromatic_ge_clique`
         Every proper colouring uses at least as many colours as the largest
         clique — a clique is a set of pairwise-adjacent vertices, so a proper
         colouring must be injective on it (pigeonhole).

    (2)  χ(G(A)) ≤ |A|                  `chromatic_le_card`
         Colouring the |A| vertices with distinct colours is proper, because
         edges only join *distinct* vertices.

    (3)  Consequence `chromatic_finite`:
         For a *finite* general-position integer-distance set, the chromatic
         number is finite (bounded by |A|), and it is bounded below by the
         clique number.  Combined with the Anning–Erdős clique bound this
         locates χ(G(A)) in the window  ω ≤ χ ≤ |A| ≤ 4(2D+1)(2E+1).

  The graph-theoretic definitions mirror those of the companion problem file
  `Erdos130Problem.lean` (`Point2`, `IsIntegerDist`, `IntDistEdge`,
  `IsProperColoring`, `ChromaticAtMost`, `HasClique`) so the results transfer
  directly; they are restated here to keep the file self-contained.

  References:
  - Anning, N. & Erdős, P. (1945): "Integral Distances", Bull. Amer. Math. Soc. 51
  - Erdős problem #130: https://erdosproblems.com/130
-/

import Mathlib

namespace Erdos130.OQ03

/-! ## Graph-theoretic setup (mirrors `Erdos130Problem.lean`) -/

/-- A point in the plane. -/
structure Point2 where
  x : ℝ
  y : ℝ

/-- Squared Euclidean distance between two points. -/
noncomputable def distSq (p q : Point2) : ℝ :=
  (p.x - q.x) ^ 2 + (p.y - q.y) ^ 2

/-- Two points are at integer distance (their squared distance is a perfect
    square of a natural number). -/
def IsIntegerDist (p q : Point2) : Prop :=
  ∃ n : ℕ, distSq p q = (n : ℝ) ^ 2

/-- The edge relation of the integer distance graph `G(A)`: two distinct points
    of `A` are joined iff they are at integer distance. -/
def IntDistEdge (A : Set Point2) (p q : Point2) : Prop :=
  p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ IsIntegerDist p q

/-- A proper `k`-colouring of `G(A)`: adjacent vertices get distinct colours. -/
def IsProperColoring (A : Set Point2) (k : ℕ) (c : Point2 → Fin k) : Prop :=
  ∀ p q : Point2, IntDistEdge A p q → c p ≠ c q

/-- `χ(G(A)) ≤ k`: there is a proper `k`-colouring. -/
def ChromaticAtMost (A : Set Point2) (k : ℕ) : Prop :=
  ∃ c : Point2 → Fin k, IsProperColoring A k c

/-- `G(A)` has a clique of size `k`: a `k`-element subset of `A` whose points
    are pairwise at integer distance. -/
def HasClique (A : Set Point2) (k : ℕ) : Prop :=
  ∃ S : Finset Point2, S.card = k ∧
    (∀ p ∈ S, p ∈ A) ∧
    (∀ p q : Point2, p ∈ S → q ∈ S → p ≠ q → IsIntegerDist p q)

/-! ## (1) Lower bound: χ(G(A)) ≥ ω(G(A))

A proper colouring must assign distinct colours to the vertices of any clique,
so it is injective on the clique; pigeonhole then forces at least `k` colours. -/

/-- **Clique lower bound.** If `G(A)` contains a clique of size `k` and admits a
    proper `k'`-colouring, then `k ≤ k'`.  Equivalently, `ω(G(A)) ≤ χ(G(A))`. -/
theorem chromatic_ge_clique (A : Set Point2) (k k' : ℕ)
    (hclique : HasClique A k) (hcol : ChromaticAtMost A k') : k ≤ k' := by
  obtain ⟨S, hcard, hSA, hSpair⟩ := hclique
  obtain ⟨c, hc⟩ := hcol
  -- A proper colouring is injective on the clique `S`.
  have hInjOn : (S : Set Point2).InjOn c := by
    intro p hp q hq hcpq
    by_contra hpq
    have hpS : p ∈ S := hp
    have hqS : q ∈ S := hq
    exact hc p q ⟨hSA p hpS, hSA q hqS, hpq, hSpair p q hpS hqS hpq⟩ hcpq
  -- Injective map `S → Fin k'`, so `|S| ≤ k'`.
  have hmaps : Set.MapsTo c (S : Set Point2) (Finset.univ : Finset (Fin k')) :=
    fun p _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hle : S.card ≤ (Finset.univ : Finset (Fin k')).card :=
    Finset.card_le_card_of_injOn c hmaps hInjOn
  rwa [hcard, Finset.card_univ, Fintype.card_fin] at hle

/-! ## (2) Upper bound: χ(G(A)) ≤ |A|

Colouring the `|A|` vertices with pairwise distinct colours is proper, because
the edge relation only relates *distinct* vertices. -/

/-- **Any injective colouring is proper.** Since edges join only distinct
    vertices, giving every vertex a distinct colour never violates properness. -/
theorem injective_coloring_proper (A : Set Point2) (k : ℕ) (c : Point2 → Fin k)
    (hinj : Function.Injective c) : IsProperColoring A k c := by
  intro p q hedge hcpq
  exact hedge.2.2.1 (hinj hcpq)

/-- **Cardinality upper bound.** A finite, nonempty set of vertices can be
    properly coloured with `|A|` colours: index the vertices by `Fin |A|`. -/
theorem chromatic_le_card (A : Finset Point2) (hne : A.Nonempty) :
    ChromaticAtMost (↑A) A.card := by
  classical
  obtain ⟨a₀, ha₀⟩ := hne
  -- `A.equivFin : A ≃ Fin A.card` indexes the vertices; extend to all of ℝ²
  -- by sending non-vertices to a fixed colour (harmless: they carry no edges).
  refine ⟨fun p => if h : p ∈ A then A.equivFin ⟨p, h⟩ else A.equivFin ⟨a₀, ha₀⟩, ?_⟩
  intro p q hedge hcpq
  obtain ⟨hpA, hqA, hpq, _⟩ := hedge
  rw [Finset.mem_coe] at hpA hqA
  simp only [dif_pos hpA, dif_pos hqA] at hcpq
  have hsub : (⟨p, hpA⟩ : {x // x ∈ A}) = ⟨q, hqA⟩ := A.equivFin.injective hcpq
  exact hpq (congrArg Subtype.val hsub)

/-! ## (3) Consequence: χ(G(A)) is finite and sandwiched between ω and |A| -/

/-- **The sandwich.** For a finite, nonempty general-position integer-distance
    set, every clique size `k` satisfies `k ≤ χ ≤ |A|`: concretely, if `G(A)`
    has a clique of size `k` then `k ≤ A.card`, and `G(A)` is `A.card`-colourable.
    This places the open chromatic number in the window `ω ≤ χ ≤ |A|`. -/
theorem chromatic_finite (A : Finset Point2) (hne : A.Nonempty) (k : ℕ)
    (hclique : HasClique (↑A) k) :
    k ≤ A.card ∧ ChromaticAtMost (↑A) A.card := by
  have hcol := chromatic_le_card A hne
  exact ⟨chromatic_ge_clique (↑A) k A.card hclique hcol, hcol⟩

/-! ## A concrete lower bound

Any explicit triangle with pairwise integer distances (e.g. a `3–4–5` right
triangle) is a clique of size 3, forcing at least 3 colours. -/

/-- The three vertices of a `3–4–5` right triangle. -/
def P₀ : Point2 := ⟨0, 0⟩
def P₁ : Point2 := ⟨3, 0⟩
def P₂ : Point2 := ⟨0, 4⟩

/-- Integer distance is symmetric (squared distance is symmetric). -/
theorem isIntegerDist_symm {p q : Point2} (h : IsIntegerDist p q) :
    IsIntegerDist q p := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  have : distSq q p = distSq p q := by simp only [distSq]; ring
  rw [this, hn]

/-- All three pairwise distances of the `3–4–5` triangle are integers. -/
theorem triangle_345_integer_dists :
    IsIntegerDist P₀ P₁ ∧ IsIntegerDist P₀ P₂ ∧ IsIntegerDist P₁ P₂ := by
  refine ⟨⟨3, ?_⟩, ⟨4, ?_⟩, ⟨5, ?_⟩⟩ <;>
    · simp only [distSq, P₀, P₁, P₂]; norm_num

/-- The three vertices are pairwise distinct. -/
theorem triangle_345_distinct : P₀ ≠ P₁ ∧ P₀ ≠ P₂ ∧ P₁ ≠ P₂ := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro h
      simp only [P₀, P₁, P₂, Point2.mk.injEq] at h
      norm_num at h

/-- The `3–4–5` triangle is a clique of size 3 in its own integer distance
    graph, so any proper colouring needs at least 3 colours: `χ ≥ 3`.
    A concrete lower bound witnessing that χ(G(A)) can exceed 2. -/
theorem triangle_345_needs_three_colors (k' : ℕ)
    (hcol : ChromaticAtMost ({P₀, P₁, P₂} : Set Point2) k') : 3 ≤ k' := by
  classical
  obtain ⟨d01, d02, d12⟩ := triangle_345_integer_dists
  obtain ⟨h01, h02, h12⟩ := triangle_345_distinct
  apply chromatic_ge_clique ({P₀, P₁, P₂} : Set Point2) 3 k' _ hcol
  refine ⟨{P₀, P₁, P₂}, ?_, ?_, ?_⟩
  · -- |{P₀,P₁,P₂}| = 3
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact ⟨h01, h02⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]; exact h12),
        Finset.card_singleton]
  · -- all three points lie in the vertex set
    intro p hp
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Finset.mem_insert, Finset.mem_singleton] using hp
  · -- pairwise integer distances
    intro p q hp hq hpq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hpq
        | exact d01
        | exact d02
        | exact d12
        | exact isIntegerDist_symm d01
        | exact isIntegerDist_symm d02
        | exact isIntegerDist_symm d12

end Erdos130.OQ03

#print axioms Erdos130.OQ03.chromatic_finite
#print axioms Erdos130.OQ03.triangle_345_needs_three_colors
