/-
  Aristotle targets for Erdos207Problem
  Routine supporting lemmas for automated proof search.
  See Erdos207Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT erdos207Conjecture: existential (Aristotle cannot construct STS)
  - NOT girth_3_iff_pasch_free: complex combinatorial equivalence
  - Girth ≥ 2 for any Steiner triple system: provable from STS uniqueness
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)

  Included targets (1):
  - sts_has_girth_at_least_2_ari: every STS has girth ≥ 2

  NOT included:
  - erdos207Conjecture: requires existence of high-girth STS (Aristotle skips)
  - girth_3_iff_pasch_free: needs full Pasch configuration analysis
-/
import Mathlib
import Proofs.Erdos207Problem

namespace Erdos207ProblemAristotle

open Erdos207 Finset

/-
## Section: Girth ≥ 2 for Steiner Triple Systems

HasGirthAtLeast H 2 says: for any S ⊆ H.edges with S.card = 2,
the union of the two edges (vertexSpan S) has ≥ 5 vertices.

Key argument:
- Two distinct edges e₁, e₂ in a STS each have 3 vertices
- If they shared ≥ 2 vertices a, b, the STS property ∃! triple through {a,b}
  would force e₁ = e₂, contradicting distinctness
- So they share ≤ 1 vertex: |e₁ ∪ e₂| ≥ 3 + 3 - 1 = 5

Key Mathlib lemmas:
- Finset.card_eq_two: S.card = 2 ↔ ∃ a b, a ≠ b ∧ S = {a, b}
- Finset.card_union_add_card_inter: |A ∪ B| + |A ∩ B| = |A| + |B|
- Finset.biUnion_pair: ({e₁, e₂}.biUnion id) = e₁ ∪ e₂
-/

/-- Every Steiner triple system has girth at least 2.
    Any two distinct edges share at most 1 vertex (by the unique-triple property),
    so their union has at least 3 + 3 - 1 = 5 vertices. -/
theorem sts_has_girth_at_least_2_ari {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph3 V) (hSTS : IsSteinerTripleSystem H) :
    HasGirthAtLeast H 2 := by
  sorry

end Erdos207ProblemAristotle
