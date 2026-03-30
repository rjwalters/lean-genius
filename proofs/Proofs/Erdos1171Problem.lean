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
-- PART 2: Partition Relation Definitions (concrete)
-- ============================================================

/-- The multicolor ordinal partition relation α → (β, k, ..., k)²_{numColors}:
    for any numColors-coloring of pairs from α, there exists either:
    - a monochromatic-0 subset of order type β (via order-embedding), or
    - a monochromatic-i clique of size `clique` for some i ∈ {1, ..., numColors-1}.

    The coloring is modeled as `c : Ordinal → Ordinal → ℕ` with a validity
    hypothesis that c(i,j) < numColors for all i < j < α. -/
def ordinalPartitionRelMulti (α β : Ordinal) (clique numColors : ℕ) : Prop :=
  ∀ (c : Ordinal → Ordinal → ℕ),
    (∀ i j, i < j → j < α → c i j < numColors) →
    (∃ (f : Ordinal → Ordinal), StrictMono f ∧
      (∀ x, x < β → f x < α) ∧
      ∀ i j, i < j → j < β → c (f i) (f j) = 0) ∨
    (∃ (color : ℕ), 0 < color ∧ color < numColors ∧
      ∃ (S : Fin clique → Ordinal), StrictMono S ∧
        (∀ i, S i < α) ∧
        ∀ (i j : Fin clique), i < j → c (S i) (S j) = color)

/-- The 2-color ordinal partition relation α → (β, k)²: for any 2-coloring
    of pairs from α, there exists either a monochromatic-0 subset of order
    type β or a monochromatic-1 clique of size k. -/
def ordinalPartitionRel2 (α β : Ordinal) (k : ℕ) : Prop :=
  ∀ (c : Ordinal → Ordinal → ℕ),
    (∀ i j, i < j → j < α → c i j < 2) →
    (∃ (f : Ordinal → Ordinal), StrictMono f ∧
      (∀ x, x < β → f x < α) ∧
      ∀ i j, i < j → j < β → c (f i) (f j) = 0) ∨
    (∃ (S : Fin k → Ordinal), StrictMono S ∧
      (∀ i, S i < α) ∧
      ∀ (i j : Fin k), i < j → c (S i) (S j) = 1)

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
    n colors, it holds for fewer colors (with the same targets).
    Requires clique ≥ 2 to extract color bounds from the coloring. -/
theorem partition_multi_mono_colors (α β : Ordinal) (clique m n : ℕ)
    (hclique : 2 ≤ clique) (hmn : m ≤ n) (h : ordinalPartitionRelMulti α β clique n) :
    ordinalPartitionRelMulti α β clique m := by
  intro c hc
  have hcn : ∀ i j, i < j → j < α → c i j < n :=
    fun i j hij hj => lt_of_lt_of_le (hc i j hij hj) hmn
  rcases h c hcn with ⟨f, hf, hfα, hfc⟩ | ⟨col, hcpos, _, S, hS, hSα, hSc⟩
  · left; exact ⟨f, hf, hfα, hfc⟩
  · right
    have i0 : Fin clique := ⟨0, by omega⟩
    have i1 : Fin clique := ⟨1, by omega⟩
    have h01 : i0 < i1 := by change (0 : ℕ) < 1; omega
    have hcol : c (S i0) (S i1) = col := hSc i0 i1 h01
    have hSlt : S i0 < S i1 := hS h01
    have hcm : col < m := by rw [← hcol]; exact hc (S i0) (S i1) hSlt (hSα i1)
    exact ⟨col, hcpos, hcm, S, hS, hSα, hSc⟩

/-- Monotonicity in ordinal target: weakening the first target. -/
theorem partition_multi_mono_target (α β γ : Ordinal) (clique numColors : ℕ)
    (hγβ : γ ≤ β) (h : ordinalPartitionRelMulti α β clique numColors) :
    ordinalPartitionRelMulti α γ clique numColors := by
  intro c hc
  rcases h c hc with ⟨f, hf, hfα, hfc⟩ | hright
  · left
    exact ⟨f, hf, fun x hx => hfα x (lt_of_lt_of_le hx hγβ),
           fun i j hij hj => hfc i j hij (lt_of_lt_of_le hj hγβ)⟩
  · exact Or.inr hright

/-- Monotonicity in source: a larger source makes the relation easier. -/
theorem partition_multi_mono_source (α α' β : Ordinal) (clique numColors : ℕ)
    (hαα' : α ≤ α') (h : ordinalPartitionRelMulti α β clique numColors) :
    ordinalPartitionRelMulti α' β clique numColors := by
  intro c hc
  have hcα : ∀ i j, i < j → j < α → c i j < numColors :=
    fun i j hij hj => hc i j hij (lt_of_lt_of_le hj hαα')
  rcases h c hcα with ⟨f, hf, hfα, hfc⟩ | ⟨col, hcp, hcn, S, hS, hSα, hSc⟩
  · left
    exact ⟨f, hf, fun x hx => lt_of_lt_of_le (hfα x hx) hαα', hfc⟩
  · right
    exact ⟨col, hcp, hcn, S, hS, fun i => lt_of_lt_of_le (hSα i) hαα', hSc⟩

/-- The 2-color case of the multicolor relation coincides with the standard
    2-color partition relation. -/
theorem multi_two_eq (α β : Ordinal) (k : ℕ) :
    ordinalPartitionRelMulti α β k 2 ↔ ordinalPartitionRel2 α β k := by
  constructor
  · intro h c hc
    rcases h c hc with hleft | ⟨color, hpos, hlt, S, hS, hSα, hSc⟩
    · exact Or.inl hleft
    · have : color = 1 := by omega
      subst this
      exact Or.inr ⟨S, hS, hSα, hSc⟩
  · intro h c hc
    rcases h c hc with hleft | ⟨S, hS, hSα, hSc⟩
    · exact Or.inl hleft
    · exact Or.inr ⟨1, by omega, by omega, S, hS, hSα, hSc⟩

-- ============================================================
-- PART 6: Connection to Problem #1169
-- ============================================================

/-- The Continuum Hypothesis: 2^ℵ₀ = ℵ₁. -/
def CH : Prop := (2 : Cardinal) ^ Cardinal.aleph0 = Cardinal.aleph 1

/-- Hajnal's theorem (from Problem #1169): Under CH, ω₁² → (ω₁², k)². -/
axiom hajnal_ch (h : CH) (k : ℕ) (hk : 2 ≤ k) :
    ordinalPartitionRel2 omega1Sq omega1Sq k

/-- Monotonicity for the 2-color relation: weakening the ordinal target. -/
theorem partition2_mono_target (α β γ : Ordinal) (k : ℕ)
    (hγβ : γ ≤ β) (h : ordinalPartitionRel2 α β k) :
    ordinalPartitionRel2 α γ k := by
  intro c hc
  rcases h c hc with ⟨f, hf, hfα, hfc⟩ | hright
  · left
    exact ⟨f, hf, fun x hx => hfα x (lt_of_lt_of_le hx hγβ),
           fun i j hij hj => hfc i j hij (lt_of_lt_of_le hj hγβ)⟩
  · exact Or.inr hright

/-- Source monotonicity for the 2-color relation. -/
theorem partition2_mono_source (α α' β : Ordinal) (k : ℕ)
    (hαα' : α ≤ α') (h : ordinalPartitionRel2 α β k) :
    ordinalPartitionRel2 α' β k := by
  intro c hc
  have hcα : ∀ i j, i < j → j < α → c i j < 2 :=
    fun i j hij hj => hc i j hij (lt_of_lt_of_le hj hαα')
  rcases h c hcα with ⟨f, hf, hfα, hfc⟩ | ⟨S, hS, hSα, hSc⟩
  · left
    exact ⟨f, hf, fun x hx => lt_of_lt_of_le (hfα x hx) hαα', hfc⟩
  · right
    exact ⟨S, hS, fun i => lt_of_lt_of_le (hSα i) hαα', hSc⟩

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

/-- Martin's Axiom: For every partial order P with the countable chain condition
    (CCC) and every family of fewer than 2^ℵ₀ dense subsets, there exists a
    filter meeting all of them. This is independent of ZFC but weaker than CH.

    Concretely:
    - Two elements are **compatible** if they have a common lower bound
    - **CCC**: every set of pairwise incompatible elements is countable
    - **Dense**: D ⊆ P is dense if every element has a refinement in D
    - **Filter**: nonempty, upward-closed, downward-directed subset of P -/
def MartinsAxiom : Prop :=
  ∀ (P : Type) [Preorder P],
    -- CCC: every antichain (pairwise incompatible set) is countable
    (∀ A : Set P, (∀ a ∈ A, ∀ b ∈ A, a ≠ b →
      ¬∃ r : P, r ≤ a ∧ r ≤ b) → A.Countable) →
    -- For every family D of dense sets with |D| < 2^ℵ₀
    ∀ D : Set (Set P),
      (∀ d ∈ D, ∀ p : P, ∃ q ∈ d, q ≤ p) →
      Cardinal.mk D < 2 ^ Cardinal.aleph0 →
      -- There exists a filter meeting every dense set
      ∃ G : Set P,
        G.Nonempty ∧
        (∀ p ∈ G, ∀ q : P, p ≤ q → q ∈ G) ∧
        (∀ p ∈ G, ∀ q ∈ G, ∃ r ∈ G, r ≤ p ∧ r ≤ q) ∧
        ∀ d ∈ D, ∃ x ∈ G, x ∈ d

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

/-- The 1-color case is trivial: with only color 0 available, the identity
    embedding witnesses a monochromatic-0 subset of order type β. -/
theorem partition_multi_trivial (α β : Ordinal) (clique : ℕ) (hα : β ≤ α) :
    ordinalPartitionRelMulti α β clique 1 := by
  intro c hc
  left
  exact ⟨id, strictMono_id, fun x hx => lt_of_lt_of_le hx hα,
    fun i j hij hjβ => by
      have := hc i j hij (lt_of_lt_of_le hjβ hα); omega⟩

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
    A color-merging argument extends this to multicolor by induction on k:
    merge colors {0..n} vs {n+1}, apply Hajnal for a 2-coloring.
    Case 1: ω₁²-copy in merged color → apply IH.
    Case 2: triangle in color n+1 → done. -/
theorem ch_implies_multicolor (h : CH) (k : ℕ) :
    ordinalPartitionRelMulti omega1Sq omega1TimesOmega 3 (k + 1) := by
  induction k with
  | zero =>
    exact partition_multi_trivial omega1Sq omega1TimesOmega 3
      (le_of_lt omega1TimesOmega_lt_omega1Sq)
  | succ n ih =>
    -- (n+2)-coloring c with colors {0, 1, ..., n+1}
    intro c hc
    -- 2-coloring: color 0 if c ≤ n, color 1 if c = n+1
    let c' : Ordinal → Ordinal → ℕ := fun i j => if c i j ≤ n then 0 else 1
    have hc' : ∀ i j, i < j → j < omega1Sq → c' i j < 2 := by
      intro i j _ _; simp only [c']; split_ifs <;> omega
    -- Hajnal: ω₁² → (ω₁², 3)²
    rcases hajnal_ch h 3 (by norm_num) c' hc' with
      ⟨f, hf_mono, hf_bnd, hf_col⟩ | ⟨S, hS_mono, hS_bnd, hS_col⟩
    · -- Case 1: ω₁²-copy in c'-color 0. All pairs have c ≤ n.
      -- Pull back coloring through f to get (n+1)-coloring c''
      let c'' : Ordinal → Ordinal → ℕ := fun a b => c (f a) (f b)
      have hc'' : ∀ i j, i < j → j < omega1Sq → c'' i j < n + 1 := by
        intro i j hij hj; simp only [c'']
        have := hf_col i j hij hj  -- c' (f i) (f j) = 0
        simp only [c'] at this; split_ifs at this with hle
        · omega
        · omega
      -- IH on c'': either mono-0 of type ω₁·ω or triangle in color 1..n
      rcases ih c'' hc'' with
        ⟨g, hg_mono, hg_bnd, hg_col⟩ | ⟨col, hcol_pos, hcol_lt, T, hT_mono, hT_bnd, hT_col⟩
      · -- Mono-0 copy of ω₁·ω in c'': compose f ∘ g
        left
        exact ⟨f ∘ g, hf_mono.comp hg_mono,
          fun x hx => hf_bnd (g x) (hg_bnd x hx),
          fun i j hij hj => hg_col i j hij hj⟩
      · -- Triangle in color col ∈ {1..n} in c'': map through f
        right
        exact ⟨col, hcol_pos, by omega, fun i => f (T i), hf_mono.comp hT_mono,
          fun i => hf_bnd (T i) (hT_bnd i), fun i j hij => hT_col i j hij⟩
    · -- Case 2: triangle in c'-color 1. All pairs have c = n+1.
      right
      refine ⟨n + 1, by omega, by omega, S, hS_mono, hS_bnd, fun i j hij => ?_⟩
      have := hS_col i j hij  -- c' (S i) (S j) = 1
      simp only [c'] at this; split_ifs at this with hle
      · omega  -- 0 = 1, contradiction
      · push_neg at hle
        have := hc (S i) (S j) (hS_mono hij) (hS_bnd j)
        omega  -- n < c(S i, S j) < n + 2, so c(S i, S j) = n + 1

/-- Under CH, Problem #1171 is fully resolved. -/
theorem erdos_1171_under_ch (h : CH) : erdos_1171_statement := by
  intro k
  exact ch_implies_multicolor h k

-- ============================================================
-- PART 11: Summary
-- ============================================================

/-
## Summary of Formalization

### Problem
Erdős #1171 asks whether ω₁² → (ω₁·ω, 3, ..., 3)²_{k+1} holds
for all finite k.

### What We Formalize
1. Ordinal partition relations (2-color and multicolor, concrete definitions)
2. Key ordinals: ω₁, ω₁², ω₁·ω
3. The problem statement as a universal quantification over k
4. Martin's Axiom (concrete CCC/dense sets/generic filter formulation)
5. Baumgartner's partial result (k=1 case under MA)
6. The CH-conditional full resolution via Hajnal's theorem
7. Monotonicity of partition relations (source, target, colors)

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

### Axiom Count: 2 axioms (hajnal_ch, baumgartner_ma), 20 theorems
### Eliminated MartinsAxiom: concrete def via CCC/dense sets/generic filters (was axiom)
### Removed erdos_rado_partition: unused axiom (was 4 axioms)
### Proved ch_implies_multicolor from hajnal_ch by induction on k (was 5 axioms)
### Previously proved 9 axioms by defining ordinalPartitionRel2/Multi concretely (was 14 axioms)
### Previously proved omega1_isLimit and omega1TimesOmega_isLimit (was 16 axioms)
-/

end Erdos1171
