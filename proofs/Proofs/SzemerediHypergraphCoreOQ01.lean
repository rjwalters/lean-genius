/-
  Simplicial Complex Infrastructure for Hypergraph Regularity
  Open Question OQ-01 from SzemerediHypergraphCore

  Defines the core structures for Gowers (2007) hypergraph regularity:
  - SimplicialComplex: downward-closed family of finite vertex sets
  - kFaces: all faces of a given size
  - CompleteKLinks: k-subsets fully supported by the complex
  - relativeDensity: density of a k-graph conditioned on the complex
  - IsGowersRegular: Gowers ε-regularity relative to a complex

  This fills the gap identified in SzemerediHypergraphCore.lean, where
  naive IsHypergraphRegular was shown insufficient and the full Gowers
  relative regularity was listed as a follow-up direction.

  Key insight: CompleteKLinks T = the k-set T where every nonempty
  strict subset of size < k is a face of the complex. This generalizes
  "both endpoints in the edge set" from graph regularity.

  References:
  - Gowers, W.T. (2007). Annals of Mathematics 166(3), 897–946.
  - Nagle, B., Rödl, V., Schacht, M. (2006). RSA 28(2), 113–179.
-/
import Mathlib

namespace Szemeredi.Hypergraph

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

-- Local copy of UHypergraph from SzemerediHypergraphCore (parent has build errors)
private structure UHypergraph (V : Type*) (k : ℕ) where
  edges : Finset (Finset V)
  uniform : ∀ e ∈ edges, e.card = k

private def UHypergraph.empty (V : Type*) [DecidableEq V] (k : ℕ) : UHypergraph V k where
  edges := ∅
  uniform := by simp

-- ═══════════════════════════════════════════════════════════════════
-- PART I: SIMPLICIAL COMPLEX
-- ═══════════════════════════════════════════════════════════════════

/-- A simplicial complex on vertex set V: a downward-closed family of
    nonempty finite vertex sets (faces).

    In Gowers (2007), the relevant complex is a k-complex: a system of
    j-uniform hypergraphs for j = 1,...,k-1 with downward closure.
    This definition captures that structure for arbitrary degree truncations. -/
structure SimplicialComplex (V : Type*) [DecidableEq V] where
  faces : Finset (Finset V)
  nonempty_faces : ∀ σ ∈ faces, σ.Nonempty
  downward : ∀ σ ∈ faces, ∀ τ : Finset V, τ ⊆ σ → τ.Nonempty → τ ∈ faces

/-- The faces of a simplicial complex of size exactly k. -/
def SimplicialComplex.kFaces (C : SimplicialComplex V) (k : ℕ) : Finset (Finset V) :=
  C.faces.filter (fun σ => σ.card = k)

/-- The complete simplicial complex on V: all nonempty subsets are faces. -/
noncomputable def SimplicialComplex.complete (V : Type*) [DecidableEq V] [Fintype V] :
    SimplicialComplex V where
  faces := Finset.univ.powerset.filter Finset.Nonempty
  nonempty_faces := fun σ hσ => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at hσ; exact hσ.2
  downward := fun σ hσ τ hτs hτne => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at *
    exact ⟨hτs.trans hσ.1, hτne⟩

/-- The full simplex on a finite set S ⊆ V: all nonempty subsets of S. -/
noncomputable def SimplicialComplex.fullSimplex (S : Finset V) :
    SimplicialComplex V where
  faces := S.powerset.filter Finset.Nonempty
  nonempty_faces := fun σ hσ => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at hσ; exact hσ.2
  downward := fun σ hσ τ hτs hτne => by
    simp only [Finset.mem_filter, Finset.mem_powerset] at *
    exact ⟨hτs.trans hσ.1, hτne⟩

/-- C' is a sub-complex of C if all faces of C' are faces of C. -/
def SimplicialComplex.IsSubcomplex (C' C : SimplicialComplex V) : Prop :=
  C'.faces ⊆ C.faces

/-- A face of a sub-complex is a face of the ambient complex. -/
theorem SimplicialComplex.IsSubcomplex.mem_faces {C C' : SimplicialComplex V}
    (h : C'.IsSubcomplex C) {σ : Finset V} (hσ : σ ∈ C'.faces) : σ ∈ C.faces :=
  h hσ

-- ═══════════════════════════════════════════════════════════════════
-- PART II: COMPLETE K-LINKS
-- ═══════════════════════════════════════════════════════════════════

/-- The complete k-links of a simplicial complex C: the set of k-element
    vertex sets T such that every nonempty proper subset of T (of size < k)
    is a face of C.

    These are the k-simplices "supported by" the complex — the candidate
    edges for a k-graph relative to C.

    For k=2: complete 2-links are pairs {u,v} where {u} and {v} are faces.
    For k=3: complete 3-links are triples {u,v,w} where all singletons
             and pairs {u,v},{u,w},{v,w} are faces of C.

    For the full Gowers (2007) regularity, we only need the (k-1)-links
    of the (k-1)-complex to count the "potential k-edges". -/
noncomputable def CompleteKLinks (C : SimplicialComplex V) (k : ℕ) :
    Finset (Finset V) :=
  (Finset.univ.powerset).filter (fun T =>
    T.card = k ∧
    ∀ τ : Finset V, τ ⊆ T → τ.Nonempty → τ.card < k → τ ∈ C.faces)

/-- Every complete k-link has exactly k vertices. -/
theorem CompleteKLinks.card_eq {C : SimplicialComplex V} {k : ℕ} {T : Finset V}
    (hT : T ∈ CompleteKLinks C k) : T.card = k := by
  simp only [CompleteKLinks, Finset.mem_filter, Finset.mem_powerset] at hT
  exact hT.2.1

/-- If T is a complete k-link and τ ⊊ T is nonempty with |τ| < k, then τ ∈ C. -/
theorem CompleteKLinks.subset_mem_faces {C : SimplicialComplex V} {k : ℕ} {T : Finset V}
    (hT : T ∈ CompleteKLinks C k) {τ : Finset V}
    (hτ : τ ⊆ T) (hτne : τ.Nonempty) (hτk : τ.card < k) : τ ∈ C.faces := by
  simp only [CompleteKLinks, Finset.mem_filter, Finset.mem_powerset] at hT
  exact hT.2.2 τ hτ hτne hτk

/-- The complete k-links of the full simplex on S are the k-subsets of S.
    This shows that when the complex is "complete" over S, all k-subsets of S
    are candidates, recovering the naive k-partite density. -/
theorem CompleteKLinks_fullSimplex (S : Finset V) (k : ℕ) (hk : 2 ≤ k) :
    CompleteKLinks (SimplicialComplex.fullSimplex S) k =
    S.powerset.filter (fun T => T.card = k) := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powerset]
  constructor
  · intro hT
    constructor
    · -- T ⊆ S: every singleton {v} ⊆ T is a face of fullSimplex S, so {v} ⊆ S, so v ∈ S
      intro v hv
      have hface := CompleteKLinks.subset_mem_faces hT
        (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
        (by simp; omega)
      simp only [SimplicialComplex.fullSimplex, Finset.mem_filter, Finset.mem_powerset] at hface
      exact hface.1 (Finset.mem_singleton_self v)
    · exact CompleteKLinks.card_eq hT
  · intro ⟨hTS, hTk⟩
    simp only [CompleteKLinks, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.subset_univ _, hTk, fun τ hτT hτne hτk => ?_⟩
    simp only [SimplicialComplex.fullSimplex, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hτT.trans hTS, hτne⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART III: RELATIVE DENSITY
-- ═══════════════════════════════════════════════════════════════════

/-- The density of a k-uniform hypergraph H relative to a simplicial complex C:
    the fraction of complete k-links of C that are edges of H.

    This is the central quantity in Gowers (2007) hypergraph regularity.

    d(H | C) = |edges(H) ∩ CompleteKLinks(C, k)| / |CompleteKLinks(C, k)|

    When C is the complete complex, this reduces to ordinary edge density.
    Gowers's regularity requires density to be stable under restriction
    to "dense" sub-complexes. -/
noncomputable def relativeDensity {k : ℕ}
    (H : UHypergraph V k) (C : SimplicialComplex V) : ℚ :=
  if (CompleteKLinks C k).card = 0 then 0
  else ((CompleteKLinks C k).filter (· ∈ H.edges)).card / (CompleteKLinks C k).card

/-- Relative density is non-negative. -/
theorem relativeDensity_nonneg {k : ℕ}
    (H : UHypergraph V k) (C : SimplicialComplex V) :
    0 ≤ relativeDensity H C := by
  unfold relativeDensity
  split_ifs
  · exact le_refl 0
  · positivity

/-- Relative density is at most 1. -/
theorem relativeDensity_le_one {k : ℕ}
    (H : UHypergraph V k) (C : SimplicialComplex V) :
    relativeDensity H C ≤ 1 := by
  unfold relativeDensity
  split_ifs with h
  · exact zero_le_one
  · have hpos : (0 : ℚ) < (CompleteKLinks C k).card := by
      exact_mod_cast Nat.pos_of_ne_zero h
    rw [div_le_one hpos]
    exact_mod_cast Finset.card_filter_le _ _

/-- Relative density of the empty hypergraph is 0. -/
theorem relativeDensity_empty {k : ℕ} (C : SimplicialComplex V) :
    relativeDensity (UHypergraph.empty V k) C = 0 := by
  unfold relativeDensity
  split_ifs
  · rfl
  · simp [UHypergraph.empty]

/-- Relative density is 1 when H contains all complete k-links. -/
theorem relativeDensity_eq_one {k : ℕ}
    (H : UHypergraph V k) (C : SimplicialComplex V)
    (hlinks : 0 < (CompleteKLinks C k).card)
    (hfull : ∀ T ∈ CompleteKLinks C k, T ∈ H.edges) :
    relativeDensity H C = 1 := by
  unfold relativeDensity
  have hne : (CompleteKLinks C k).card ≠ 0 := Nat.pos_iff_ne_zero.mp hlinks
  simp only [if_neg hne]
  have hfilt : (CompleteKLinks C k).filter (· ∈ H.edges) = CompleteKLinks C k := by
    ext T; simp only [Finset.mem_filter]
    exact ⟨And.left, fun h => ⟨h, hfull T h⟩⟩
  rw [hfilt]
  exact div_self (by exact_mod_cast hne)

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: GOWERS ε-REGULARITY
-- ═══════════════════════════════════════════════════════════════════

/-- A sub-complex C' of C is δ-dense at level j if C' contains at least
    a δ-fraction of the j-faces of C. -/
def IsDenseAtLevel (C C' : SimplicialComplex V) (j : ℕ) (δ : ℚ) : Prop :=
  C'.IsSubcomplex C ∧
  (δ * (C.kFaces j).card : ℚ) ≤ (C'.kFaces j).card

/-- Gowers (2007) ε-regularity for k-uniform hypergraphs:
    H is ε-regular relative to C if for every δ > 0 and every
    sub-complex C' of C that is δ-dense at the (k-1)-level,
    the relative density changes by at most ε.

    This is the key definition enabling the hypergraph counting lemma
    and the multidimensional Szemerédi theorem.

    Compare to graph ε-regularity (SzemerediCore.IsEpsilonRegular):
    there, density is stable when restricting to large vertex subsets.
    Here, density is stable when restricting to a dense sub-complex. -/
def IsGowersRegular {k : ℕ}
    (H : UHypergraph V k) (C : SimplicialComplex V) (eps : ℚ) : Prop :=
  ∀ (C' : SimplicialComplex V) (δ : ℚ),
    0 < δ →
    IsDenseAtLevel C C' (k - 1) δ →
    |relativeDensity H C - relativeDensity H C'| ≤ eps

/-- The empty hypergraph is ε-regular relative to any complex (density is always 0). -/
theorem isGowersRegular_empty {k : ℕ} (C : SimplicialComplex V) (eps : ℚ) (heps : 0 ≤ eps) :
    IsGowersRegular (UHypergraph.empty V k) C eps := by
  intro C' δ _hδ _hdense
  simp [relativeDensity_empty, abs_zero]
  exact heps

-- ═══════════════════════════════════════════════════════════════════
-- PART V: KEY THEOREMS (OPEN / LONG PROOFS)
-- ═══════════════════════════════════════════════════════════════════

/-- The hypergraph regularity lemma (Gowers 2007, Rödl–Skokan 2004):
    For every ε > 0 and k ≥ 2, every k-uniform hypergraph on n vertices
    admits a simplicial complex C such that H is ε-Gowers-regular relative to C.

    The bound on |kFaces| is a tower-type function of ε.
    This is the main theorem enabling the multidimensional Szemerédi theorem.

    Formal proof is a major open challenge for this Lean formalization. -/
theorem hypergraph_regularity_lemma (k : ℕ) (hk : 2 ≤ k) (eps : ℚ) (heps : 0 < eps) :
    ∃ (T : ℕ), ∀ (H : UHypergraph V k),
    ∃ (C : SimplicialComplex V),
      IsGowersRegular H C eps ∧
      (C.kFaces (k - 1)).card ≤ T := by
  sorry

end Szemeredi.Hypergraph
