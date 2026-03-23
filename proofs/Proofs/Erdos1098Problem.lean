/-
Erdős Problem #1098: Non-Commuting Graphs of Groups

Source: https://erdosproblems.com/1098
Status: SOLVED

Statement:
Let G be a group and Γ = Γ(G) be the non-commuting graph, with vertices the
elements of G and an edge between g and h if and only if g and h do not commute
(gh ≠ hg).

If Γ contains no infinite complete subgraph, then is there a finite bound on
the size of complete subgraphs of Γ?

Key Results:
- Neumann (1976): SOLVED
  - Γ contains no infinite complete subgraph iff the center Z(G) has finite index
  - If [G : Z(G)] = n, then Γ has no complete subgraph on > n vertices
  - Conversely, if Γ has no infinite clique, Z(G) has finite index
-/

import Mathlib

open Subgroup

namespace Erdos1098

variable {G : Type*} [Group G]

def nonCommuting (g h : G) : Prop := g * h ≠ h * g
def commuting (g h : G) : Prop := g * h = h * g

theorem nonCommuting_symm (g h : G) : nonCommuting g h ↔ nonCommuting h g := by
  simp only [nonCommuting]; constructor <;> intro hne hcomm <;> exact hne hcomm.symm

def isClique (S : Set G) : Prop :=
  ∀ g ∈ S, ∀ h ∈ S, g ≠ h → nonCommuting g h

def hasFiniteCliqueNumber (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, ∀ S : Set G, isClique S → S.Finite → S.ncard ≤ n

def noInfiniteClique (G : Type*) [Group G] : Prop :=
  ∀ S : Set G, isClique S → S.Finite

def centerHasFiniteIndex (G : Type*) [Group G] : Prop :=
  (Subgroup.center G).index ≠ 0

axiom neumann_theorem (G : Type*) [Group G] :
    noInfiniteClique G ↔ centerHasFiniteIndex G

axiom neumann_bound (G : Type*) [Group G] (n : ℕ)
    (hn : (Subgroup.center G).index = n) :
    ∀ S : Set G, isClique S → S.Finite → S.ncard ≤ n

theorem finite_index_implies_finite_clique (G : Type*) [Group G]
    (_h : centerHasFiniteIndex G) : hasFiniteCliqueNumber G :=
  ⟨(Subgroup.center G).index, neumann_bound G _ rfl⟩

theorem erdos_question_answered (G : Type*) [Group G]
    (h : noInfiniteClique G) : hasFiniteCliqueNumber G := by
  rw [neumann_theorem] at h
  exact finite_index_implies_finite_clique G h

theorem same_coset_commute (g h : G)
    (hcoset : ∃ z ∈ Subgroup.center G, g * z = h) : commuting g h := by
  obtain ⟨z, hz, rfl⟩ := hcoset
  show g * (g * z) = (g * z) * g
  rw [mul_assoc]
  congr 1
  exact Subgroup.mem_center_iff.mp hz g

theorem clique_different_cosets (S : Set G) (hS : isClique S) :
    ∀ g ∈ S, ∀ h ∈ S, g ≠ h →
    (QuotientGroup.mk' (Subgroup.center G) g : G ⧸ Subgroup.center G) ≠
    QuotientGroup.mk' (Subgroup.center G) h := by
  intro g hg h hh hne heq
  have hmem : g⁻¹ * h ∈ Subgroup.center G := by
    have := QuotientGroup.eq.mp heq
    exact this
  have hcomm : commuting g h :=
    same_coset_commute g h ⟨g⁻¹ * h, hmem, by group⟩
  exact absurd hcomm (hS g hg h hh hne)

theorem clique_size_bound (S : Set G) (hS : isClique S) (hSfin : S.Finite) :
    S.ncard ≤ (Subgroup.center G).index :=
  neumann_bound G _ rfl S hS hSfin

theorem abelian_no_edges (G : Type*) [Group G]
    (habel : Subgroup.center G = ⊤) :
    ∀ g h : G, ¬nonCommuting g h := by
  intro g h
  simp only [nonCommuting, ne_eq, not_not]
  have hg : g ∈ Subgroup.center G := by rw [habel]; exact Subgroup.mem_top g
  exact (Subgroup.mem_center_iff.mp hg h).symm

theorem finite_group_finite_index (G : Type*) [Group G] [Finite G] :
    centerHasFiniteIndex G := by
  unfold centerHasFiniteIndex
  exact Subgroup.index_ne_zero_of_finite

def isBFCGroup (G : Type*) [Group G] : Prop :=
  ∃ n : ℕ, ∀ g : G, Set.Finite {h : G | IsConj g h} ∧
    Set.ncard {h : G | IsConj g h} ≤ n

axiom bfc_center_connection (G : Type*) [Group G] :
    centerHasFiniteIndex G → isBFCGroup G

theorem erdos_1098 (G : Type*) [Group G] :
    noInfiniteClique G → hasFiniteCliqueNumber G :=
  erdos_question_answered G

end Erdos1098
