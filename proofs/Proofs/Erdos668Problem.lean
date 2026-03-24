/-
Erdos Problem #668: Unit Distance Configurations

Source: https://erdosproblems.com/668
Status: OPEN

Statement:
Let u(n) denote the maximum number of unit distances among n points in the plane.
Let f(n) denote the number of incongruent point configurations that achieve u(n).

Does f(n) -> infinity as n -> infinity?
Is f(n) > 1 for all n > 3?

Background:
This problem explores the uniqueness or multiplicity of extremal configurations
for the classical unit distance problem. While Erdos Problem #90 asks for u(n)
itself, this problem asks how many distinct (up to congruence) configurations
achieve this maximum.

Known Results:
- f(4) = 1: The unique configuration is two equilateral triangles sharing an edge
- Computational evidence suggests f(n) = 1 for 5 <= n <= 21 (though only graph
  isomorphism was checked, not full congruence)

References:
- Erdos (original problem)
- Engel, Hammond-Lee, Su, Varga, Zsamboki [EHSVZ25]: Computational evidence
- Alexeev, Mixon, Parshall [AMP25]: Additional computational work
-/

import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Topology.MetricSpace.Isometry

open Set Metric Finset

namespace Erdos668

/-- The plane as a type -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Two points are at unit distance if their Euclidean distance is exactly 1. -/
def isUnitPair (p q : Plane) : Prop := dist p q = 1

/-- The set of ordered unit distance pairs in a point set. -/
def unitDistancePairs (S : Finset Plane) : Set (Plane × Plane) :=
  {pq | pq.1 ∈ S ∧ pq.2 ∈ S ∧ pq.1 ≠ pq.2 ∧ isUnitPair pq.1 pq.2}

/-- The number of unit distance pairs in a point set (counting unordered pairs).
    Uses Set.ncard to avoid decidability issues with dist on real plane. -/
noncomputable def unitDistanceCount (S : Finset Plane) : ℕ :=
  Set.ncard (unitDistancePairs S) / 2

/-- u(n) is the maximum number of unit distances achievable by n points. -/
noncomputable def u (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ S : Finset Plane, S.card = n ∧ unitDistanceCount S = k}

/-- A point set S is extremal if it achieves u(|S|) unit distances. -/
def isExtremal (S : Finset Plane) : Prop :=
  unitDistanceCount S = u S.card

/-- The set of n-point extremal configurations. -/
def extremalConfigs (n : ℕ) : Set (Finset Plane) :=
  {S : Finset Plane | S.card = n ∧ isExtremal S}

/-- Two finite point sets are congruent if some isometry maps one onto the other. -/
def areCongruent (S T : Finset Plane) : Prop :=
  ∃ φ : Plane ≃ᵢ Plane, (∀ p ∈ S, φ p ∈ T) ∧ (∀ q ∈ T, ∃ p ∈ S, φ p = q)

/-- Congruence is reflexive. -/
theorem congruent_refl (S : Finset Plane) : areCongruent S S := by
  refine ⟨IsometryEquiv.refl Plane, fun p hp => ?_, fun q hq => ⟨q, hq, ?_⟩⟩
  · simpa using hp
  · rfl

/-- Congruence is symmetric. -/
theorem congruent_symm {S T : Finset Plane} (h : areCongruent S T) :
    areCongruent T S := by
  obtain ⟨φ, hST, hTS⟩ := h
  refine ⟨φ.symm, fun q hq => ?_, fun p hp => ?_⟩
  · obtain ⟨p, hp, hpq⟩ := hTS q hq
    rw [← hpq, IsometryEquiv.symm_apply_apply]
    exact hp
  · exact ⟨φ p, hST p hp, φ.symm_apply_apply p⟩

/-- Congruence is transitive. -/
theorem congruent_trans {S T U : Finset Plane}
    (h₁ : areCongruent S T) (h₂ : areCongruent T U) : areCongruent S U := by
  obtain ⟨φ, hST, hTS⟩ := h₁
  obtain ⟨ψ, hTU, hUT⟩ := h₂
  refine ⟨φ.trans ψ, fun p hp => ?_, fun u hu => ?_⟩
  · simp only [IsometryEquiv.trans_apply]
    exact hTU (φ p) (hST p hp)
  · obtain ⟨t, ht, htu⟩ := hUT u hu
    obtain ⟨s, hs, hst⟩ := hTS t ht
    exact ⟨s, hs, by simp [IsometryEquiv.trans_apply, hst, htu]⟩

/-- An isometry maps unit pairs to unit pairs. -/
theorem isUnitPair_of_isometry (φ : Plane ≃ᵢ Plane) {p q : Plane}
    (h : isUnitPair p q) : isUnitPair (φ p) (φ q) := by
  unfold isUnitPair at *
  rw [φ.dist_eq]
  exact h

/-- Congruence preserves unit distance count. -/
theorem congruent_unitDistanceCount {S T : Finset Plane}
    (h : areCongruent S T) (hcard : S.card = T.card) :
    unitDistanceCount S = unitDistanceCount T := by
  obtain ⟨φ, hST, hTS⟩ := h
  unfold unitDistanceCount
  suffices Set.ncard (unitDistancePairs S) = Set.ncard (unitDistancePairs T) by
    rw [this]
  -- The pair map (p, q) ↦ (φ p, φ q) is injective (since φ is an isometry equiv)
  have hΦ_inj : Function.Injective (fun pq : Plane × Plane => (φ pq.1, φ pq.2)) := by
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ heq
    simp only [Prod.mk.injEq] at heq
    exact Prod.ext (φ.injective heq.1) (φ.injective heq.2)
  -- The pair map sends unitDistancePairs S onto unitDistancePairs T
  have himg : (fun pq : Plane × Plane => (φ pq.1, φ pq.2)) '' unitDistancePairs S =
      unitDistancePairs T := by
    ext ⟨a, b⟩
    simp only [Set.mem_image, Prod.exists, unitDistancePairs, Set.mem_setOf_eq, Prod.mk.injEq]
    constructor
    · rintro ⟨p, q, ⟨hp, hq, hne, hdist⟩, rfl, rfl⟩
      exact ⟨hST p hp, hST q hq, fun h => hne (φ.injective h),
        isUnitPair_of_isometry φ hdist⟩
    · rintro ⟨ha, hb, hne, hdist⟩
      obtain ⟨p, hp, rfl⟩ := hTS a ha
      obtain ⟨q, hq, rfl⟩ := hTS b hb
      refine ⟨p, q, ⟨hp, hq, fun hpq => hne (congrArg (⇑φ) hpq), ?_⟩, rfl, rfl⟩
      unfold isUnitPair at hdist ⊢
      rwa [← φ.dist_eq]
  rw [← himg, Set.ncard_image_of_injective _ hΦ_inj]

/-- Congruence preserves extremality. -/
theorem congruent_preserves_extremal {S T : Finset Plane}
    (h : areCongruent S T) (hcard : S.card = T.card)
    (hS : isExtremal S) : isExtremal T := by
  unfold isExtremal at *
  rw [← hcard, ← congruent_unitDistanceCount h hcard]
  exact hS

/-- The congruence setoid on finite point sets. -/
noncomputable def congruenceSetoid : Setoid (Finset Plane) where
  r := areCongruent
  iseqv := {
    refl := congruent_refl
    symm := congruent_symm
    trans := congruent_trans
  }

/-- f(n) is the number of congruence classes of n-point extremal configurations. -/
noncomputable def f (n : ℕ) : ℕ :=
  Set.ncard (Quotient.mk congruenceSetoid '' extremalConfigs n)

/-- f(4) = 1: The unique extremal 4-point configuration is two equilateral
    triangles sharing an edge. -/
axiom f_four : f 4 = 1

/-- Any two 4-point extremal configurations are congruent. -/
axiom four_config_unique (S T : Finset Plane) :
    S.card = 4 → T.card = 4 → isExtremal S → isExtremal T → areCongruent S T

/-- u(4) = 5: Four points in the plane can have at most 5 unit distances. -/
axiom u_four : u 4 = 5

/-- For 5 <= n <= 21, computational evidence shows f(n) >= 1. -/
axiom computational_evidence :
  ∀ n : ℕ, 5 ≤ n → n ≤ 21 → f n ≥ 1

/-- Question 1: Does f(n) tend to infinity as n tends to infinity? -/
def question_one : Prop :=
  ∀ M : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n ≥ M

/-- Question 2 (original): Is f(n) > 1 for all n > 3?
    Note: f(4) = 1, so this is false as stated. -/
def question_two : Prop :=
  ∀ n : ℕ, n > 3 → f n > 1

/-- Question 2 (modified): Is f(n) > 1 for all sufficiently large n? -/
def question_two_modified : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, n ≥ N → f n > 1

/-- Question 2 is false as originally stated (since f(4) = 1). -/
theorem question_two_false : ¬ question_two := by
  intro h
  have h4 := h 4 (by omega)
  have := f_four
  omega

/-- For any n >= 1, at least one n-point extremal configuration exists. -/
axiom extremalConfigs_nonempty (n : ℕ) (hn : n ≥ 1) : (extremalConfigs n).Nonempty

/-- u(n) >= n - 1 for n >= 2. -/
axiom u_lower_bound (n : ℕ) (hn : n ≥ 2) : u n ≥ n - 1

/-- u(n) < c * n^(4/3) for some constant c > 0 (Spencer-Szemeredi-Trotter). -/
axiom u_upper_bound : ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 2 → (u n : ℝ) < c * n ^ (4/3 : ℝ)

/-- Summary: f(4) = 1 and the 4-point extremal configuration is unique. -/
theorem erdos_668_summary :
    f 4 = 1 ∧
    (∀ S T : Finset Plane, S.card = 4 → T.card = 4 → isExtremal S → isExtremal T →
      areCongruent S T) :=
  ⟨f_four, four_config_unique⟩

/-- The set of congruence classes of n-point extremal configurations is finite.
    This is a combinatorial geometry fact: for each n, there are finitely many
    distinct unit-distance graphs on n vertices, and each graph type admits finitely
    many non-congruent realizations achieving u(n) unit distances. -/
axiom extremalQuotient_finite (n : ℕ) :
  Set.Finite (Quotient.mk congruenceSetoid '' extremalConfigs n)

/-- f(n) >= 1 for all n >= 1 (at least one extremal configuration exists).
    Uses extremalConfigs_nonempty (at least one extremal config exists) and
    extremalQuotient_finite (the quotient set is finite, so ncard is correct). -/
theorem f_pos (n : ℕ) (hn : n ≥ 1) : f n ≥ 1 := by
  unfold f
  have hne := extremalConfigs_nonempty n hn
  have hfin := extremalQuotient_finite n
  have hne' : (Quotient.mk congruenceSetoid '' extremalConfigs n).Nonempty :=
    hne.image _
  have hpos := (Set.ncard_pos hfin).mpr hne'
  omega

end Erdos668
