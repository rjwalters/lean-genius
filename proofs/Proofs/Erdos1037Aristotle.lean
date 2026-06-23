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
  have hself : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
  have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
    intro u hu
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rintro rfl
    exact hself hu
  calc G.degree v
      = (G.neighborFinset v).card := rfl
    _ ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
    _ = Fintype.card V - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]

-- Routine: Number of distinct degree values is at most n
-- (image of univ has card ≤ card univ)
theorem distinctDegrees_le_card :
    (Finset.univ.image (fun v => G.degree v)).card ≤ Fintype.card V := by
  calc (Finset.univ.image (fun v => G.degree v)).card
      ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

-- Routine: If every value appears at most k times among n elements,
-- then there are at least ⌈n/k⌉ distinct values (pigeonhole).
-- Proof partitions the universe fiberwise by f via
-- `Finset.card_eq_sum_card_fiberwise`.
theorem pigeonhole_distinct_count (f : V → ℕ) (k : ℕ) (hk : k ≥ 1)
    (h : ∀ d : ℕ, (Finset.univ.filter (fun v => f v = d)).card ≤ k) :
    (Finset.univ.image f).card ≥ Fintype.card V / k := by
  suffices Fintype.card V ≤ k * (Finset.univ.image f).card by
    calc Fintype.card V / k
        ≤ (k * (Finset.univ.image f).card) / k := Nat.div_le_div_right this
      _ = (Finset.univ.image f).card := Nat.mul_div_cancel_left _ (by omega)
  have hmem : ∀ v ∈ (Finset.univ : Finset V), f v ∈ Finset.univ.image f :=
    fun v _ => Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  calc Fintype.card V
      = (Finset.univ : Finset V).card := (Finset.card_univ).symm
    _ = ∑ d ∈ Finset.univ.image f, (Finset.univ.filter (fun v => f v = d)).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _ ∈ Finset.univ.image f, k := Finset.sum_le_sum (fun d _ => h d)
    _ = (Finset.univ.image f).card * k := by rw [Finset.sum_const, smul_eq_mul]
    _ = k * (Finset.univ.image f).card := mul_comm _ _

-- Routine: Degree values range in {0, ..., n-1}.
-- We compose `degree_le_card_sub_one` with `Nat.lt_of_le_pred` to recover the
-- strict `< Fintype.card V` form needed for `Finset.mem_range`.
theorem degree_range :
    Finset.univ.image (fun v => G.degree v) ⊆ Finset.range (Fintype.card V) := by
  intro d hd
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hd
  obtain ⟨v, rfl⟩ := hd
  rw [Finset.mem_range]
  -- G.degree v ≤ n - 1, and n ≥ 1 since there is at least one vertex v.
  have hle : G.degree v ≤ Fintype.card V - 1 := degree_le_card_sub_one G v
  have hn1 : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

-- Routine: The complement graph has degree (n-1) - deg_G(v)
-- Aristotle target: needs SimpleGraph.degree_compl or manual neighborFinset argument
theorem complement_degree (v : V) :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  simp only [SimpleGraph.degree]
  have hv_G : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
  have hv_C : v ∉ Gᶜ.neighborFinset v := Gᶜ.notMem_neighborFinset_self v
  have hunion : Gᶜ.neighborFinset v ∪ G.neighborFinset v = Finset.univ.erase v := by
    ext w
    simp only [Finset.mem_union, SimpleGraph.mem_neighborFinset, SimpleGraph.compl_adj,
               Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro (⟨hvw, _⟩ | hadj)
      · exact hvw.symm
      · exact (G.ne_of_adj hadj).symm
    · intro hwv
      by_cases h : G.Adj v w
      · exact Or.inr h
      · exact Or.inl ⟨hwv.symm, h⟩
  have hdisj : Disjoint (Gᶜ.neighborFinset v) (G.neighborFinset v) := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    rw [SimpleGraph.mem_neighborFinset] at hw1 hw2
    rw [SimpleGraph.compl_adj] at hw1
    exact hw1.2 hw2
  have hcard := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at hcard
  omega

-- Routine: If every degree appears at most twice and degrees ∈ {0,...,n-1},
-- then the number of distinct degrees ≤ n, and n ≤ 2 * distinctDegrees.
-- k = 2 specialization of `pigeonhole_distinct_count` applied to G.degree.
theorem limited_mult_bound_from_pigeonhole
    (h : ∀ d : ℕ, (Finset.univ.filter (fun v => G.degree v = d)).card ≤ 2) :
    Fintype.card V ≤ 2 * (Finset.univ.image (fun v => G.degree v)).card := by
  have hmem : ∀ v ∈ (Finset.univ : Finset V),
              G.degree v ∈ Finset.univ.image (fun v => G.degree v) :=
    fun v _ => Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  calc Fintype.card V
      = (Finset.univ : Finset V).card := (Finset.card_univ).symm
    _ = ∑ d ∈ Finset.univ.image (fun v => G.degree v),
          (Finset.univ.filter (fun v => G.degree v = d)).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _ ∈ Finset.univ.image (fun v => G.degree v), 2 :=
        Finset.sum_le_sum (fun d _ => h d)
    _ = (Finset.univ.image (fun v => G.degree v)).card * 2 := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * (Finset.univ.image (fun v => G.degree v)).card := mul_comm _ _

-- Routine: 3/4 > 2/3 (comparing optimal bounds)
theorem three_fourths_gt_two_thirds : (3 : ℝ) / 4 > 2 / 3 := by norm_num

end Erdos1037Aristotle
