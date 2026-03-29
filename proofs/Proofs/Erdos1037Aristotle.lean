/-
  Aristotle targets for Erdős Problem #1037
  Routine supporting lemmas for automated proof search.
  See Erdos1037Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture (Chen-Erdős, disproved)
  - Routine graph theory facts: handshake lemma, degree bounds, pigeonhole
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1037Aristotle

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

-- Routine: Handshake lemma — sum of degrees equals twice the number of edges
-- This is Mathlib's SimpleGraph.sum_degrees_eq_twice_card_edges
theorem degree_sum_eq_twice_edges :
    (Finset.univ.sum (fun v => G.degree v)) = 2 * G.edgeFinset.card :=
  SimpleGraph.sum_degrees_eq_twice_card_edges G

-- Routine: Maximum degree in a simple graph is at most n-1
theorem degree_le_card_sub_one (v : V) :
    G.degree v ≤ Fintype.card V - 1 := by
  have h := G.degree_lt_card v  -- G.degree v < Fintype.card V
  omega

-- Routine: Number of distinct degree values is at most n
-- (image of univ has card ≤ card univ)
theorem distinctDegrees_le_card :
    (Finset.univ.image (fun v => G.degree v)).card ≤ Fintype.card V := by
  calc (Finset.univ.image (fun v => G.degree v)).card
      ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

-- Routine: If every value appears at most k times among n elements,
-- then there are at least ⌈n/k⌉ distinct values (pigeonhole)
theorem pigeonhole_distinct_count (f : V → ℕ) (k : ℕ) (hk : k ≥ 1)
    (h : ∀ d : ℕ, (Finset.univ.filter (fun v => f v = d)).card ≤ k) :
    (Finset.univ.image f).card ≥ Fintype.card V / k := by
  -- Partition univ by fibers of f: |V| = ∑_{d ∈ image f} |f⁻¹(d)|
  -- Each fiber has ≤ k elements, so |V| ≤ k * |image f|
  -- Hence |image f| ≥ |V|/k
  by_contra hlt; push_neg at hlt
  have : Fintype.card V ≤ k * (Finset.univ.image f).card := by
    calc Fintype.card V = Finset.univ.card := (Finset.card_univ).symm
      _ = (Finset.univ.biUnion (fun d => Finset.univ.filter (fun v => f v = d))).card := by
            congr 1; ext v; simp
      _ ≤ (Finset.univ.image f).sum (fun d => (Finset.univ.filter (fun v => f v = d)).card) := by
            rw [← Finset.card_biUnion]; apply Finset.card_le_card
            · intro v hv; simp at hv ⊢; exact ⟨f v, Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, hv⟩
            · intro d₁ _ d₂ _ hne; exact Finset.disjoint_filter.mpr (fun v _ h1 h2 => hne (h1 ▸ h2))
      _ ≤ (Finset.univ.image f).sum (fun _ => k) :=
            Finset.sum_le_sum (fun d _ => h d)
      _ = k * (Finset.univ.image f).card := by simp [Finset.sum_const, Nat.smul_one_eq_cast]
  have : Fintype.card V / k ≤ (Finset.univ.image f).card := Nat.div_le_of_le_mul this
  omega

-- Routine: Degree values range in {0, ..., n-1}
theorem degree_range :
    Finset.univ.image (fun v => G.degree v) ⊆ Finset.range (Fintype.card V) := by
  intro d hd
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd
  obtain ⟨v, rfl⟩ := hd
  exact Finset.mem_range.mpr (G.degree_lt_card v)

-- Routine: The complement graph has degree (n-1) - deg_G(v)
-- Aristotle target: needs SimpleGraph.degree_compl or manual neighborFinset argument
theorem complement_degree (v : V) :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  simp [SimpleGraph.degree_compl]

-- Routine: If every degree appears at most twice and degrees ∈ {0,...,n-1},
-- then the number of distinct degrees ≤ n, and n ≤ 2 * distinctDegrees
theorem limited_mult_bound_from_pigeonhole
    (h : ∀ d : ℕ, (Finset.univ.filter (fun v => G.degree v = d)).card ≤ 2) :
    Fintype.card V ≤ 2 * (Finset.univ.image (fun v => G.degree v)).card := by
  have := pigeonhole_distinct_count G (fun v => G.degree v) 2 (by omega) h
  omega

-- Routine: 3/4 > 2/3 (comparing optimal bounds)
theorem three_fourths_gt_two_thirds : (3 : ℝ) / 4 > 2 / 3 := by norm_num

end Erdos1037Aristotle
