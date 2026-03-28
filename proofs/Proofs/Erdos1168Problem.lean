/-
Erdős Problem #1168: Negative Partition Relation for ℵ_{ω+1}

Source: https://erdosproblems.com/1168
Status: OPEN
Reference: [Va99, 7.80]

Statement:
Prove that ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)_{ℵ₀}²
without assuming the generalised continuum hypothesis (GCH).

That is: there exists a coloring of pairs from ℵ_{ω+1} using countably many
colors such that:
(1) Color 0 has no homogeneous set of cardinality ℵ_{ω+1}
(2) Each color i ≥ 1 has no monochromatic triangle (3-clique)

Context:
- Under GCH, this follows from classical Erdős–Hajnal–Rado results
  on negative partition relations for successor cardinals.
- The problem asks for a ZFC-only proof (without GCH).
- ℵ_ω is singular (cofinality ω), making its successor ℵ_{ω+1} a
  successor of a singular cardinal — a setting where pcf theory
  (Shelah) provides powerful ZFC combinatorial tools.

Tags: set-theory, ramsey-theory
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

open Cardinal Ordinal

namespace Erdos1168

/- ## Part I: The Cardinals -/

/-- The cardinal ℵ_ω: the supremum of {ℵ_n : n < ω}. -/
noncomputable def aleph_omega : Cardinal := Cardinal.aleph Ordinal.omega0

/-- The cardinal ℵ_{ω+1}: the successor of ℵ_ω. -/
noncomputable def aleph_omega_succ : Cardinal := Cardinal.aleph (Ordinal.omega0 + 1)

/- ## Part II: Multi-Color Partition Relation

The partition relation κ → (α₀, α₁, …)²_c means:
for any c-coloring of pairs from κ, some color i has a
homogeneous set of size αᵢ.

We use ℕ-indexed colors (countably many). -/

/-- A set S is homogeneous for color i under coloring f:
    all pairs of distinct elements in S are colored i. -/
def IsHomogeneous {V : Type*} (f : V → V → ℕ) (S : Set V) (i : ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b = i

/-- The countable-color partition relation:
    κ → (targets)²_ℵ₀ means for any ℕ-coloring of pairs from a type
    of cardinality κ, some color i has a homogeneous set of
    cardinality ≥ targets(i). -/
def partitionRelation (κ : Cardinal) (targets : ℕ → Cardinal) : Prop :=
  ∀ (V : Type*) (_ : #V = κ) (f : V → V → ℕ),
    ∃ (i : ℕ) (S : Set V), #S ≥ targets i ∧ IsHomogeneous f S i

/- ## Part III: The Problem Statement -/

/-- The target function for Erdős #1168:
    - Color 0: must avoid homogeneous set of size ℵ_{ω+1}
    - All other colors: must avoid triangles (size 3) -/
noncomputable def targets : ℕ → Cardinal
  | 0 => aleph_omega_succ
  | _ + 1 => 3

/-- **Erdős Problem #1168 (OPEN):**
    ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, 3, …)²_{ℵ₀}

    There exists a coloring of pairs from ℵ_{ω+1} using countably many
    colors such that color 0 has no homogeneous set of size ℵ_{ω+1},
    and each other color has no monochromatic triangle.

    The challenge is to prove this in ZFC without assuming GCH. -/
def erdos_1168_conjecture : Prop := ¬ partitionRelation aleph_omega_succ targets

/- ## Part IV: Known Results -/

/-- Under GCH, Erdős–Hajnal–Rado theory establishes negative partition
    relations for successor cardinals. The result follows from the
    stepping-up lemma applied at ℵ_ω. -/
axiom erdos_1168_under_gch :
    (∀ κ : Cardinal.{0}, 2 ^ κ = Order.succ κ) →
    ¬ partitionRelation aleph_omega_succ targets

/-- Under GCH, the open conjecture holds. -/
theorem gch_implies_conjecture (hgch : ∀ κ : Cardinal.{0}, 2 ^ κ = Order.succ κ) :
    erdos_1168_conjecture :=
  erdos_1168_under_gch hgch

/- ## Part V: Structural Observations -/

/-- The empty set is vacuously homogeneous for any color. -/
theorem empty_homogeneous {V : Type*} (f : V → V → ℕ) (i : ℕ) :
    IsHomogeneous f ∅ i :=
  fun a ha => absurd ha (Set.not_mem_empty a)

/-- A singleton is homogeneous for any color. -/
theorem singleton_homogeneous {V : Type*} (f : V → V → ℕ) (v : V) (i : ℕ) :
    IsHomogeneous f {v} i := by
  intro a ha b hb hab
  rw [Set.mem_singleton_iff] at ha hb
  exact absurd (ha.trans hb.symm) hab

/-- Homogeneity is monotone: if S is homogeneous and T ⊆ S, then T is homogeneous. -/
theorem IsHomogeneous.subset {V : Type*} {f : V → V → ℕ} {S T : Set V}
    {i : ℕ} (hS : IsHomogeneous f S i) (hTS : T ⊆ S) : IsHomogeneous f T i :=
  fun a ha b hb hab => hS a (hTS ha) b (hTS hb) hab

/-- The partition relation is antimonotone in the targets:
    if targets' ≤ targets pointwise and the relation holds for targets,
    then it holds for targets'. -/
theorem partitionRelation.mono_targets {κ : Cardinal}
    {t₁ t₂ : ℕ → Cardinal} (h : ∀ i, t₂ i ≤ t₁ i)
    (hp : partitionRelation κ t₁) : partitionRelation κ t₂ := by
  intro V hV f
  obtain ⟨i, S, hS, hH⟩ := hp V hV f
  exact ⟨i, S, le_trans (h i) hS, hH⟩

/-
## Summary

**Erdős Problem #1168: OPEN**

**Question:** Prove ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, 3, …)²_{ℵ₀} in ZFC.

**Known:**
1. Under GCH, the result follows from Erdős–Hajnal–Rado theory
2. ℵ_ω is singular (cofinality ω), making pcf theory applicable
3. Shelah's pcf theory provides ZFC tools for successor-of-singular

**Axioms (1):**
- erdos_1168_under_gch: GCH-conditional version (known result)

**Open Conjecture:**
- erdos_1168_conjecture: the main open problem (defined as Prop)

**Proved (5):**
- gch_implies_conjecture: GCH implies the conjecture
- empty_homogeneous, singleton_homogeneous: basic homogeneity facts
- IsHomogeneous.subset: homogeneity is monotone under subsets
- partitionRelation.mono_targets: partition relation antimonotone in targets
-/

end Erdos1168
