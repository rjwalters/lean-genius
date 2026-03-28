import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-
# Erdős Problem #1022: Property B and Sparse Set Families

## Problem Statement

Is there a function c(t) → ∞ (as t → ∞) such that every family F of sets,
each of size ≥ t, satisfying the sparsity condition
  "for every finite set X, at most c(t)·|X| members of F are subsets of X"
has **Property B** (i.e., admits a 2-coloring where no set in F is monochromatic)?

## Known Results

- c(2) = 1 works (Lovász, 1968): if every edge has ≥ 2 elements and
  every vertex appears in ≤ |V| hyperedges, then Property B holds.
- Property B is equivalent to 2-colorability of hypergraphs.
- For uniform hypergraphs of size t, Erdős (1963) showed random 2-coloring
  works when the number of edges is < 2^{t-1}.

## Formalization

We formalize Property B for finite set families on a finite ground set,
state the conjecture, and prove basic structural results.

Reference: https://erdosproblems.com/1022
-/

open Finset

namespace Erdos1022

variable {α : Type*} [DecidableEq α]

-- ══════════════════════════════════════════════════════════════════
-- § 1: Property B (2-Colorability)
-- ══════════════════════════════════════════════════════════════════

/-- A family F of sets has **Property B** if there exists a 2-coloring of the
    ground set such that no member of F is monochromatic.
    Equivalently: ∃ S such that every F_i intersects both S and its complement. -/
def HasPropertyB [Fintype α] (F : Finset (Finset α)) : Prop :=
  ∃ S : Finset α, ∀ f ∈ F, (f ∩ S).Nonempty ∧ (f \ S).Nonempty

/-- The empty family trivially has Property B. -/
theorem hasPropertyB_empty [Fintype α] : HasPropertyB (∅ : Finset (Finset α)) :=
  ⟨∅, fun f hf => absurd hf (Finset.not_mem_empty f)⟩

/-- Property B is monotone: subsets of Property B families have Property B. -/
theorem hasPropertyB_subset [Fintype α] {F G : Finset (Finset α)}
    (hFG : F ⊆ G) (hG : HasPropertyB G) : HasPropertyB F :=
  let ⟨S, hS⟩ := hG; ⟨S, fun f hf => hS f (hFG hf)⟩

-- ══════════════════════════════════════════════════════════════════
-- § 2: Definitions
-- ══════════════════════════════════════════════════════════════════

/-- Every member of F has cardinality at least t. -/
def AllSizeAtLeast (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ f ∈ F, t ≤ f.card

/-- The sparsity condition: for every subset X of the ground set,
    the number of members of F contained in X is at most c · |X|. -/
def IsSparse [Fintype α] (F : Finset (Finset α)) (c : ℕ) : Prop :=
  ∀ X : Finset α, (F.filter (· ⊆ X)).card ≤ c * X.card

-- ══════════════════════════════════════════════════════════════════
-- § 3: The Conjecture
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1022** (OPEN): There exists a function c : ℕ → ℕ
    tending to infinity such that every c(t)-sparse family of sets of
    size ≥ t has Property B. -/
axiom erdos_1022_conjecture :
  ∃ c : ℕ → ℕ,
    (∀ M : ℕ, ∃ t₀ : ℕ, ∀ t : ℕ, t ≥ t₀ → c t ≥ M) ∧
    (∀ (α : Type) [DecidableEq α] [Fintype α] (F : Finset (Finset α)) (t : ℕ),
      AllSizeAtLeast F t → IsSparse F (c t) → HasPropertyB F)

-- ══════════════════════════════════════════════════════════════════
-- § 4: Basic Properties
-- ══════════════════════════════════════════════════════════════════

/-- 0-sparse families have only empty sets as members. -/
theorem sparse_zero_forces_empty [Fintype α] (F : Finset (Finset α))
    (hF : IsSparse F 0) (f : Finset α) (hf : f ∈ F) : f = ∅ := by
  by_contra hne
  have : f ∈ F.filter (· ⊆ f) := Finset.mem_filter.mpr ⟨hf, Finset.Subset.refl f⟩
  have hb := hF f
  simp only [Nat.zero_mul] at hb
  exact absurd (Finset.card_pos.mpr ⟨f, this⟩) (by omega)

/-- A family of sets of size ≥ 1 cannot be 0-sparse (unless empty). -/
theorem not_sparse_zero_of_nonempty_member [Fintype α] (F : Finset (Finset α))
    (hF : ∃ f ∈ F, f.Nonempty) : ¬IsSparse F 0 := by
  intro h0
  obtain ⟨f, hf, hne⟩ := hF
  exact absurd (sparse_zero_forces_empty F h0 f hf) (Finset.nonempty_iff_ne_empty.mp hne)

end Erdos1022
