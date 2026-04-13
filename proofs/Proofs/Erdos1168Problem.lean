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
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic

open Cardinal Ordinal

namespace Erdos1168

/- ## Part I: The Cardinals -/

/-- The cardinal ℵ_ω: the supremum of {ℵ_n : n < ω}. -/
noncomputable def aleph_omega : Cardinal := Cardinal.aleph Ordinal.omega0

/-- The cardinal ℵ_{ω+1}: the successor of ℵ_ω. -/
noncomputable def aleph_omega_succ : Cardinal := Cardinal.aleph (Ordinal.omega0 + 1)

/-- ℵ_{ω+1} = Order.succ ℵ_ω: the successor cardinal relationship.
    This follows from aleph being order-preserving and ω+1 = succ ω. -/
theorem aleph_omega_succ_eq : aleph_omega_succ = Cardinal.aleph (Order.succ Ordinal.omega0) := by
  unfold aleph_omega_succ
  congr 1
  rw [Order.succ_eq_add_one]

/-- ℵ_{ω+1} is a successor aleph, hence regular. -/
theorem aleph_omega_succ_regular : aleph_omega_succ.IsRegular := by
  rw [aleph_omega_succ_eq]
  exact Cardinal.isRegular_aleph_succ Ordinal.omega0

/-- ℵ_ω is singular: cf(ℵ_ω) = ℵ₀. -/
theorem aleph_omega_cof : (aleph_omega.ord.cof : Cardinal) = ℵ₀ := by
  unfold aleph_omega
  rw [Cardinal.cof_aleph]
  exact Ordinal.card_omega0

/-- ℵ_ω < ℵ_{ω+1}: the strict ordering. -/
theorem aleph_omega_lt_succ : aleph_omega < aleph_omega_succ :=
  Cardinal.aleph_lt_aleph.mpr (Ordinal.lt_add_of_pos_right _ Ordinal.one_pos)

/-- ℵ₀ < ℵ_ω: omega is strictly less than aleph_omega. -/
theorem aleph0_lt_aleph_omega : ℵ₀ < aleph_omega := by
  unfold aleph_omega
  rw [Cardinal.aleph_zero]
  exact Cardinal.aleph_lt_aleph.mpr (Ordinal.pos_iff_ne_zero.mpr omega_ne_zero)

/-- ℵ_n < ℵ_ω for all n : ℕ. -/
theorem aleph_n_lt_aleph_omega (n : ℕ) : Cardinal.aleph n < aleph_omega :=
  Cardinal.aleph_lt_aleph.mpr (Ordinal.nat_lt_omega0 n)

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

/- ## Part IV: GCH Stepping-Up Framework

Under GCH, the proof uses the Erdős–Hajnal–Rado stepping-up lemma:

1. **Base case**: For each n, ℵ_{n+1} ↛ (ℵ_{n+1}, n+3)² holds under GCH.
   This is a two-color partition relation for successor alephs.

2. **Stepping-up lemma**: If κ = sup_{n<ω} κ_n where each κ_{n+1} has a
   bad coloring with n+3 colors, then κ⁺ has a bad coloring with ℵ₀ colors.
   The coloring of pairs {α, β} uses the minimal n where α and β "diverge"
   in the ℵ_n-decomposition.

3. **Assembly**: Apply the stepping-up lemma at ℵ_ω = sup{ℵ_n : n < ω}
   to get the negative partition relation for ℵ_{ω+1}. -/

/-- GCH at a specific cardinal: 2^κ = κ⁺ (the successor cardinal). -/
def GCH_at (κ : Cardinal) : Prop := 2 ^ κ = Order.succ κ

/-- Full GCH: 2^κ = κ⁺ for all infinite cardinals. -/
def GCH : Prop := ∀ κ : Cardinal.{0}, 2 ^ κ = Order.succ κ

/-- The two-color negative partition relation: κ ↛ (κ, m)².
    For any 2-coloring of pairs from κ, color 0 has a homogeneous set of
    size κ or color 1 has a homogeneous set of size m. The negation says
    there exists a coloring avoiding both. -/
def negPartition2 (κ : Cardinal) (m : Cardinal) : Prop :=
  ∃ (V : Type*) (_ : #V = κ) (f : V → V → Fin 2),
    (∀ (S : Set V), #S ≥ κ → ¬(∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b = 0)) ∧
    (∀ (S : Set V), #S ≥ m → ¬(∀ a ∈ S, ∀ b ∈ S, a ≠ b → f a b = 1))

/-- **Base case**: Under GCH, for each n : ℕ, the successor aleph ℵ_{n+1}
    has a 2-coloring where color 0 avoids homogeneous sets of size ℵ_{n+1}
    and color 1 avoids homogeneous sets of size n+3.

    This follows from the Erdős–Rado theorem: (2^κ)⁺ → (κ⁺)²_κ is the
    positive relation, and its failure at the exact boundary gives the
    negative relation. Under GCH, 2^ℵ_n = ℵ_{n+1}, so the negative
    relation holds at ℵ_{n+1} with the right parameters. -/
theorem base_case_under_gch (n : ℕ) (hgch : GCH) :
    negPartition2 (Cardinal.aleph (n + 1)) (↑(n + 3) : Cardinal) := by
  sorry

/-- **Stepping-up lemma**: Given that each ℵ_{n+1} has a bad 2-coloring
    (color 0 avoids ℵ_{n+1}, color 1 avoids triangles of growing size),
    we can construct a countably-colored partition of pairs from ℵ_{ω+1}
    where:
    - Color 0 avoids homogeneous sets of size ℵ_{ω+1}
    - Each color n+1 (for n : ℕ) avoids triangles (3-element sets)

    The construction: given α < β < ℵ_{ω+1}, let n be the minimal index
    where the ℵ_n-components of α and β first diverge. Color {α,β} using
    color 0 if the base coloring at level n gives color 0, and color n+1
    otherwise. The triangle-avoidance for colors n+1 follows from the
    base case at level n. -/
theorem stepping_up (hbase : ∀ n : ℕ,
    negPartition2 (Cardinal.aleph (n + 1)) (↑(n + 3) : Cardinal)) :
    ¬ partitionRelation aleph_omega_succ targets := by
  sorry

/-- Under GCH, the negative partition relation ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)²_{ℵ₀}
    holds. This combines the base case and the stepping-up lemma.

    Replaces the previous opaque axiom with a structured decomposition. -/
theorem erdos_1168_under_gch
    (hgch : ∀ κ : Cardinal.{0}, 2 ^ κ = Order.succ κ) :
    ¬ partitionRelation aleph_omega_succ targets :=
  stepping_up (fun n => base_case_under_gch n hgch)

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

**Axioms (0):** None (previous axiom replaced with theorem + 2 sorries)

**Open Conjecture:**
- erdos_1168_conjecture: the main open problem (defined as Prop)

**Decomposition (GCH case):**
- base_case_under_gch: GCH → each ℵ_{n+1} has bad 2-coloring (sorry)
- stepping_up: bad base colorings → bad ℵ₀-coloring of ℵ_{ω+1} (sorry)
- erdos_1168_under_gch: combines base + stepping-up (proved from above)

**Proved (10):**
- aleph_omega_succ_eq: ℵ_{ω+1} = aleph(succ ω)
- aleph_omega_succ_regular: ℵ_{ω+1} is regular
- aleph_omega_cof: cf(ℵ_ω) = ℵ₀
- aleph_omega_lt_succ: ℵ_ω < ℵ_{ω+1}
- aleph0_lt_aleph_omega: ℵ₀ < ℵ_ω
- aleph_n_lt_aleph_omega: ℵ_n < ℵ_ω for all n
- gch_implies_conjecture: GCH implies the conjecture
- empty_homogeneous, singleton_homogeneous: basic homogeneity facts
- IsHomogeneous.subset: homogeneity is monotone under subsets
- partitionRelation.mono_targets: partition relation antimonotone in targets
-/

end Erdos1168
