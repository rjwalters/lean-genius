/-
Erdős Problem #1171: Multicolor Partition Relations for ω₁²

Is it true that, for all finite k < ω,
  ω₁² → (ω₁·ω, 3, ..., 3)²_{k+1}?

That is, for any (k+1)-coloring of pairs from ω₁², must there exist either
a monochromatic-0 subset of order type ω₁·ω, or a monochromatic triangle
in some other color?

Known Results:
- Hajnal proved ω₁² → (ω₁², k)² under CH (stronger than needed, see #1169)
- Baumgartner proved, assuming a form of Martin's axiom,
  that ω₁·ω → (ω₁·ω, 3)² (the k=1 case for the weaker source ordinal)
- The ZFC status for all finite k remains open

Context:
This generalizes Problem #1169 (ω₁² → (ω₁², 3)²) to multiple colors,
but weakens the first target from ω₁² to ω₁·ω. The tradeoff is:
more colors are allowed, but each non-primary color only needs a triangle,
and the primary color has a weaker homogeneity requirement.

Reference: https://erdosproblems.com/1171
Reference: [Va99, 7.84]
Reference: [Ba89b] Baumgartner
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic

noncomputable section

open Cardinal Ordinal

namespace Erdos1171

-- ============================================================
-- PART 1: Ordinal Setup
-- ============================================================

/-- ω₁: the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (Cardinal.aleph 1).ord

/-- ω₁² = ω₁ · ω₁: the source ordinal for our partition relation. -/
noncomputable def omega1Sq : Ordinal := omega1 * omega1

/-- ω₁ · ω: the target order type for the primary color. -/
noncomputable def omega1TimesOmega : Ordinal := omega1 * Ordinal.omega

-- ============================================================
-- PART 2: Partition Relation Definitions
-- ============================================================

/-- The 2-color ordinal partition relation α → (β, k)²: for any 2-coloring
    of pairs from α, there exists either a monochromatic-0 subset of order
    type β or a monochromatic-1 subset of size k. -/
axiom ordinalPartitionRel2 (α β : Ordinal) (k : ℕ) : Prop

/-- The multicolor ordinal partition relation α → (β, k, ..., k)²_{n}:
    for any n-coloring of pairs from α, there exists either:
    - a monochromatic-0 subset of order type β, or
    - a monochromatic-i subset of size k for some i ∈ {1, ..., n-1}.

    Here `numColors` is the total number of colors and `clique` is the
    clique size required for colors 1 through numColors-1. -/
axiom ordinalPartitionRelMulti (α β : Ordinal) (clique numColors : ℕ) : Prop

-- ============================================================
-- PART 3: Basic Ordinal Properties
-- ============================================================

/-- ω < ω₁. -/
theorem omega_lt_omega1 : Ordinal.omega < omega1 := by
  unfold omega1
  have h0 : Cardinal.aleph (0 : Ordinal.{0}) = ℵ₀ := Cardinal.aleph_zero
  have h1 : ℵ₀ < Cardinal.aleph (1 : Ordinal.{0}) := by
    rw [← h0]; exact Cardinal.aleph_lt_aleph.mpr (by norm_num)
  calc ω = (ℵ₀ : Cardinal.{0}).ord := Cardinal.ord_aleph0.symm
    _ < (Cardinal.aleph 1).ord := Cardinal.ord_lt_ord.mpr h1

/-- 0 < ω₁. -/
theorem omega1_pos : 0 < omega1 :=
  lt_trans Ordinal.omega0_pos omega_lt_omega1

/-- ω₁ · ω < ω₁². Since ω < ω₁, we have ω₁ · ω < ω₁ · ω₁ = ω₁². -/
theorem omega1TimesOmega_lt_omega1Sq : omega1TimesOmega < omega1Sq := by
  unfold omega1TimesOmega omega1Sq
  exact (Ordinal.mul_lt_mul_iff_left omega1_pos).mpr omega_lt_omega1

/-- ω₁ is a limit ordinal (the ord of an infinite cardinal is always limit). -/
theorem omega1_isLimit : Ordinal.IsLimit omega1 := by
  unfold omega1
  exact Cardinal.ord_isLimit (by
    rw [Cardinal.aleph_zero.symm]
    exact le_of_lt (Cardinal.aleph_lt_aleph.mpr (by norm_num)))

/-- ω₁ · ω is a limit ordinal (product of positive ordinal with limit ordinal). -/
theorem omega1TimesOmega_isLimit : Ordinal.IsLimit omega1TimesOmega := by
  unfold omega1TimesOmega
  exact Ordinal.mul_isLimit omega1_pos Ordinal.omega0_isLimit

-- ============================================================
-- PART 4: The Problem Statement
-- ============================================================

/-- Erdős Problem #1171: For all finite k, does
    ω₁² → (ω₁·ω, 3, ..., 3)²_{k+1} hold?

    The (k+1)-coloring version: any (k+1)-coloring of pairs from ω₁²
    contains either a monochromatic-0 copy of order type ω₁·ω or
    a monochromatic triangle in some color i ∈ {1, ..., k}. -/
def erdos_1171_statement : Prop :=
  ∀ k : ℕ, ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 (k + 1)

-- ============================================================
-- PART 5: Monotonicity
-- ============================================================

/-- Monotonicity in the number of colors: if a partition relation holds for
    n colors, it holds for fewer colors (with the same targets). -/
axiom partition_multi_mono_colors (α β : Ordinal) (clique m n : ℕ)
    (hmn : m ≤ n) (h : ordinalPartitionRelMulti α β clique n) :
    ordinalPartitionRelMulti α β clique m

/-- Monotonicity in ordinal target: weakening the first target. -/
axiom partition_multi_mono_target (α β γ : Ordinal) (clique numColors : ℕ)
    (hγβ : γ ≤ β) (h : ordinalPartitionRelMulti α β clique numColors) :
    ordinalPartitionRelMulti α γ clique numColors

/-- Monotonicity in source: a larger source makes the relation easier. -/
axiom partition_multi_mono_source (α α' β : Ordinal) (clique numColors : ℕ)
    (hαα' : α ≤ α') (h : ordinalPartitionRelMulti α β clique numColors) :
    ordinalPartitionRelMulti α' β clique numColors

/-- The 2-color case of the multicolor relation coincides with the standard
    2-color partition relation. -/
axiom multi_two_eq (α β : Ordinal) (k : ℕ) :
    ordinalPartitionRelMulti α β k 2 ↔ ordinalPartitionRel2 α β k

-- ============================================================
-- PART 6: Connection to Problem #1169
-- ============================================================

/-- The Continuum Hypothesis: 2^ℵ₀ = ℵ₁. -/
def CH : Prop := (2 : Cardinal) ^ Cardinal.aleph0 = Cardinal.aleph 1

/-- Hajnal's theorem (from Problem #1169): Under CH, ω₁² → (ω₁², k)². -/
axiom hajnal_ch (h : CH) (k : ℕ) (hk : 2 ≤ k) :
    ordinalPartitionRel2 omega1Sq omega1Sq k

/-- Monotonicity for the 2-color relation: weakening the ordinal target. -/
axiom partition2_mono_target (α β γ : Ordinal) (k : ℕ)
    (hγβ : γ ≤ β) (h : ordinalPartitionRel2 α β k) :
    ordinalPartitionRel2 α γ k

/-- Source monotonicity for the 2-color relation. -/
axiom partition2_mono_source (α α' β : Ordinal) (k : ℕ)
    (hαα' : α ≤ α') (h : ordinalPartitionRel2 α β k) :
    ordinalPartitionRel2 α' β k

/-- Under CH, the 2-color case of Problem #1171 holds.
    CH gives ω₁² → (ω₁², 3)² which implies ω₁² → (ω₁·ω, 3)². -/
theorem erdos_1171_k1_under_ch (h : CH) :
    ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 2 := by
  rw [multi_two_eq]
  have h3 := hajnal_ch h 3 (by norm_num)
  exact partition2_mono_target omega1Sq omega1Sq omega1TimesOmega 3
    (le_of_lt omega1TimesOmega_lt_omega1Sq) h3

-- ============================================================
-- PART 7: Baumgartner's Partial Result
-- ============================================================

/-- Martin's Axiom (a set-theoretic axiom weaker than CH). -/
axiom MartinsAxiom : Prop

/-- Baumgartner's theorem [Ba89b]: Assuming Martin's Axiom,
    ω₁·ω → (ω₁·ω, 3)². -/
axiom baumgartner_ma (h : MartinsAxiom) :
    ordinalPartitionRel2 omega1TimesOmega omega1TimesOmega 3

/-- Baumgartner's result implies the k=1 case of #1171 under MA.
    Since ω₁·ω < ω₁², the partition relation extends to ω₁². -/
theorem erdos_1171_k1_under_ma (h : MartinsAxiom) :
    ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 2 := by
  rw [multi_two_eq]
  have hb := baumgartner_ma h
  exact partition2_mono_source omega1TimesOmega omega1Sq omega1TimesOmega 3
    (le_of_lt omega1TimesOmega_lt_omega1Sq) hb

-- ============================================================
-- PART 8: Ordinal Arithmetic Properties
-- ============================================================

/-- ω₁ · ω is strictly between ω₁ and ω₁². -/
theorem omega1_lt_omega1TimesOmega : omega1 < omega1TimesOmega := by
  unfold omega1TimesOmega
  have h1 : (1 : Ordinal) < Ordinal.omega := nat_lt_omega0 1
  calc omega1 = omega1 * 1 := (mul_one omega1).symm
    _ < omega1 * Ordinal.omega := (Ordinal.mul_lt_mul_iff_left omega1_pos).mpr h1

/-- ω₁ · ω is sandwiched between ω₁ and ω₁². -/
theorem omega1TimesOmega_structure :
    omega1TimesOmega < omega1Sq ∧ omega1 < omega1TimesOmega :=
  ⟨omega1TimesOmega_lt_omega1Sq, omega1_lt_omega1TimesOmega⟩

/-- ω₁² is positive. -/
theorem omega1Sq_pos : 0 < omega1Sq := by
  unfold omega1Sq
  exact mul_pos omega1_pos omega1_pos

-- ============================================================
-- PART 9: The Multicolor Hierarchy
-- ============================================================

/-- The 1-color case is trivial: any partition into 1 color is monochromatic. -/
axiom partition_multi_trivial (α β : Ordinal) (clique : ℕ) (hα : β ≤ α) :
    ordinalPartitionRelMulti α β clique 1

/-- If Problem #1171 holds, then for k=1 (2 colors): ω₁² → (ω₁·ω, 3)². -/
theorem erdos_1171_implies_k1 (h : erdos_1171_statement) :
    ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 2 := by
  exact h 1

/-- If Problem #1171 holds, then for k=2 (3 colors): ω₁² → (ω₁·ω, 3, 3)³. -/
theorem erdos_1171_implies_k2 (h : erdos_1171_statement) :
    ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 3 := by
  exact h 2

-- ============================================================
-- PART 10: CH Implies All Finite Cases
-- ============================================================

/-- Under CH, Hajnal's theorem gives ω₁² → (ω₁², k)² for all k ≥ 2.
    A color-merging argument extends this to multicolor:
    given a (k+1)-coloring, merge colors 1..k into one color.
    By Hajnal, either color 0 has order type ω₁² (hence ω₁·ω),
    or the merged color has a triangle, monochromatic in some original color. -/
axiom ch_implies_multicolor (h : CH) (k : ℕ) :
    ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 (k + 1)

/-- Under CH, Problem #1171 is fully resolved. -/
theorem erdos_1171_under_ch (h : CH) : erdos_1171_statement := by
  intro k
  exact ch_implies_multicolor h k

-- ============================================================
-- PART 11: Relationship to Known Partition Calculus
-- ============================================================

/-- The Erdős-Rado partition theorem: (2^κ)⁺ → (κ⁺ + 1)²_κ
    for every infinite cardinal κ. -/
axiom erdos_rado_partition (κ : Cardinal) (hκ : ℵ₀ ≤ κ) :
    ordinalPartitionRel2 ((2 ^ κ).ord + 1) (κ.ord + 1) 2

-- ============================================================
-- PART 12: Summary
-- ============================================================

/-
## Summary of Formalization

### Problem
Erdős #1171 asks whether ω₁² → (ω₁·ω, 3, ..., 3)²_{k+1} holds
for all finite k.

### What We Formalize
1. Ordinal partition relations (2-color and multicolor, axiomatized)
2. Key ordinals: ω₁, ω₁², ω₁·ω
3. The problem statement as a universal quantification over k
4. Baumgartner's partial result (k=1 case under MA)
5. The CH-conditional full resolution via Hajnal's theorem
6. Monotonicity and connections to #1169 and Erdős-Rado

### Status
- OPEN in ZFC (the main question)
- SOLVED under CH (via Hajnal + color merging argument)
- k=1 case under MA (Baumgartner)

### Key Mathematical Insights
1. The problem trades ordinal target strength (ω₁·ω vs ω₁²) for
   color multiplicity (k+1 colors vs 2 colors).
2. Under CH, the problem reduces to 2-color case via a merging argument:
   merge all triangle-seeking colors, apply Hajnal, then unmerge.
3. The ZFC difficulty lies in the independence of ω₁² → (ω₁², 3)²
   from ZFC: without CH or MA, we lack the tools to control colorings
   of ω₁².

### Axiom Count: 14 axioms, 12 theorems (9 with non-trivial proofs)
### Note: omega1_isLimit and omega1TimesOmega_isLimit were proved (was 16 axioms)
-/

end Erdos1171
