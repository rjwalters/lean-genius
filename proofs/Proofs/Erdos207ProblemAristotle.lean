/-
  Aristotle targets for Erdos207Problem
  Routine supporting lemmas for automated proof search.
  See Erdos207Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT erdos207Conjecture: existential (Aristotle cannot construct STS)
  - NOT girth_3_iff_pasch_free: complex combinatorial equivalence
  - Girth ≥ 2 for any Steiner triple system: provable from STS uniqueness
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

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
  intro S hS₁ hS₂ hS₃
  obtain ⟨e₁, e₂, he₁, he₂, h_distinct, rfl⟩ : ∃ e₁ e₂ : Finset V,
      e₁ ∈ H.edges ∧ e₂ ∈ H.edges ∧ e₁ ≠ e₂ ∧ S = {e₁, e₂} := by
    have hScard : S.card = 2 := le_antisymm hS₃ hS₂
    rw [Finset.card_eq_two] at hScard
    obtain ⟨e₁, e₂, hne, rfl⟩ := hScard
    exact ⟨e₁, e₂, hS₁ (by simp), hS₁ (by simp), hne, rfl⟩
  have h_inter : (e₁ ∩ e₂).card ≤ 1 := by
    contrapose! h_distinct
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp h_distinct
    have hUniq := hSTS a b hab
    have h1 : edgeContainsPair e₁ a b :=
      ⟨(Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp hb).1, hab⟩
    have h2 : edgeContainsPair e₂ a b :=
      ⟨(Finset.mem_inter.mp ha).2, (Finset.mem_inter.mp hb).2, hab⟩
    exact hUniq.unique ⟨he₁, h1⟩ ⟨he₂, h2⟩
  have hc1 : e₁.card = 3 := H.uniform e₁ he₁
  have hc2 : e₂.card = 3 := H.uniform e₂ he₂
  have hcard := Finset.card_union_add_card_inter e₁ e₂
  have hScard2 : ({e₁, e₂} : Finset (Finset V)).card = 2 := Finset.card_pair h_distinct
  have hspan : vertexSpan ({e₁, e₂} : Finset (Finset V)) = (e₁ ∪ e₂).card := by
    simp [vertexSpan, Finset.biUnion_insert, Finset.singleton_biUnion]
  rw [hspan, hScard2]
  omega

end Erdos207ProblemAristotle
