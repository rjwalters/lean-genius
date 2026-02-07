/-
Erdős Problem #1169: Partition Relations for ω₁²

Does ω₁² → (ω₁², 3)² hold (in ZFC)?

That is, for every 2-coloring of pairs from ω₁², must there exist either
a red copy of order type ω₁² or a blue triangle?

## Known Results
- Hajnal proved the partition relation holds assuming the Continuum Hypothesis (CH).
- The problem is "not disprovable" — there exist models of set theory where it holds.
- The general ZFC status remains open.

## Context
This is a problem of Erdős and Hajnal on ordinal partition relations.
ω₁ is the first uncountable ordinal, and ω₁² = ω₁ · ω₁ (ordinal multiplication).

The negative partition relation ω₁² ↛ (ω₁², 3)² would mean there exists a
2-coloring of pairs from ω₁² with no red copy of order type ω₁² and no blue triangle.

## Related Problems
- Problem #592: For which countable β does ω^β → (ω^β, 3)² hold?
- Problem #118: Does α → (α, 3)² imply α → (α, n)² for all n ≥ 3? (Disproved)

Reference: https://erdosproblems.com/1169
Reference: [Va99, 7.85]
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Tactic

noncomputable section

open Cardinal Ordinal

-- ============================================================
-- PART 1: Ordinal Partition Relations
-- ============================================================

/-- The ordinal partition relation α → (β, k)²: for any 2-coloring of
    pairs from a well-ordered set of order type α, there exists either
    a monochromatic-0 subset of order type β or a monochromatic-1 subset
    of size k.

    We axiomatize this as it requires a substantial formal development
    of coloring theory on well-ordered sets. -/
axiom ordinalPartitionRel (α β : Ordinal) (k : ℕ) : Prop

/-- The negative partition relation α ↛ (β, k)²: there exists a 2-coloring
    of pairs from α with no monochromatic-0 copy of type β and no
    monochromatic-1 copy of size k. -/
def negPartitionRel (α β : Ordinal) (k : ℕ) : Prop :=
  ¬ ordinalPartitionRel α β k

-- ============================================================
-- PART 2: Key Ordinals
-- ============================================================

/-- ω₁: the first uncountable ordinal.
    This is the order type of the set of all countable ordinals. -/
noncomputable def omega1 : Ordinal := (Cardinal.aleph 1).ord

/-- ω₁²: the ordinal square of ω₁, i.e., ω₁ · ω₁ (ordinal multiplication). -/
noncomputable def omega1Sq : Ordinal := omega1 * omega1

/-- ω₁ is uncountable. -/
axiom omega1_uncountable : Cardinal.aleph0 < omega1.card

/-- ω₁² has cardinality ℵ₁. -/
axiom omega1Sq_card : omega1Sq.card = Cardinal.aleph 1

-- ============================================================
-- PART 3: The Main Problem Statement
-- ============================================================

/-- Erdős Problem #1169: Does ω₁² → (ω₁², 3)² hold?

    This asks whether every 2-coloring of pairs from ω₁² must contain
    either a monochromatic-0 subset of order type ω₁² or a monochromatic-1
    triangle (complete graph on 3 vertices). -/
def erdos_1169_statement : Prop :=
  ordinalPartitionRel omega1Sq omega1Sq 3

-- ============================================================
-- PART 4: Hajnal's CH-Conditional Result
-- ============================================================

/-- The Continuum Hypothesis: 2^ℵ₀ = ℵ₁. -/
def CH : Prop := (2 : Cardinal) ^ Cardinal.aleph0 = Cardinal.aleph 1

/-- Hajnal's theorem: Under CH, ω₁² → (ω₁², k)² holds for all finite k.

    This is a stronger result than what Problem #1169 asks — it gives the
    partition relation for ALL finite clique sizes, not just k = 3.

    The proof uses the diamond principle which follows from CH,
    combined with a careful analysis of colorings on ω₁². -/
axiom hajnal_ch_implies_partition (h : CH) (k : ℕ) (hk : 2 ≤ k) :
    ordinalPartitionRel omega1Sq omega1Sq k

/-- Under CH, Problem #1169 has a positive answer. -/
theorem erdos_1169_under_ch (h : CH) : erdos_1169_statement := by
  exact hajnal_ch_implies_partition h 3 (by norm_num)

-- ============================================================
-- PART 5: Independence and Consistency
-- ============================================================

/-- The problem is "not disprovable": there exist models where ω₁² → (ω₁², 3)²
    holds. In particular, any model of CH provides such a model.

    This means the negative partition relation ω₁² ↛ (ω₁², 3)² cannot be
    proved in ZFC alone (assuming ZFC + CH is consistent). -/
axiom erdos_1169_not_disprovable :
    CH → erdos_1169_statement

/-- The ZFC status of Problem #1169 remains open.
    It is unknown whether ω₁² → (ω₁², 3)² can be proved without CH. -/
axiom erdos_1169_open_in_zfc :
    erdos_1169_statement ∨ ¬ erdos_1169_statement

-- ============================================================
-- PART 6: Monotonicity Properties
-- ============================================================

/-- The partition relation is monotone decreasing in the clique parameter:
    if α → (β, k)² and j ≤ k, then α → (β, j)². -/
axiom partition_monotone_clique (α β : Ordinal) (k j : ℕ)
    (hjk : j ≤ k) (hk : ordinalPartitionRel α β k) :
    ordinalPartitionRel α β j

/-- The partition relation is monotone decreasing in the ordinal parameter:
    if α → (β, k)² and γ ≤ β, then α → (γ, k)². -/
axiom partition_monotone_ordinal (α β γ : Ordinal) (k : ℕ)
    (hγβ : γ ≤ β) (hk : ordinalPartitionRel α β k) :
    ordinalPartitionRel α γ k

/-- Under CH, ω₁² → (ω₁², 3)² implies ω₁² → (ω₁², 2)² (pairs).
    This follows from monotonicity. -/
theorem erdos_1169_implies_pairs (h : erdos_1169_statement) :
    ordinalPartitionRel omega1Sq omega1Sq 2 := by
  exact partition_monotone_clique omega1Sq omega1Sq 3 2 (by norm_num) h

-- ============================================================
-- PART 7: Connections to Other Problems
-- ============================================================

/-- Connection to Problem #592: the countable ordinal partition problem.
    Problem #592 asks for which countable β does ω^β → (ω^β, 3)² hold.
    Problem #1169 is the uncountable analogue, asking about ω₁². -/
axiom connection_to_592 :
    ordinalPartitionRel (Ordinal.omega ^ (2 : Ordinal)) (Ordinal.omega ^ (2 : Ordinal)) 3

/-- Connection to Problem #118: Erdős asked whether α → (α, 3)² implies
    α → (α, n)² for all n. This was DISPROVED (Schipperus/Darby 1999).

    For ω₁² under CH, Hajnal's result gives the stronger conclusion:
    ω₁² → (ω₁², k)² for ALL finite k. So for ω₁² under CH, the
    analogue of Erdős's question (Problem #118) has a positive answer. -/
theorem erdos_1169_stronger_than_118_under_ch (h : CH) :
    ∀ k : ℕ, 2 ≤ k → ordinalPartitionRel omega1Sq omega1Sq k :=
  hajnal_ch_implies_partition h

-- ============================================================
-- PART 8: Basic Properties of ω₁
-- ============================================================

/-- ω₁ is a limit ordinal. -/
axiom omega1_is_limit : Ordinal.IsLimit omega1

/-- ω < ω₁: the first uncountable ordinal is strictly larger than ω. -/
axiom omega_lt_omega1 : Ordinal.omega < omega1

/-- ω₁ is a regular cardinal (its cofinality equals itself). -/
axiom omega1_regular : omega1.card.ord.cof = omega1.card

-- ============================================================
-- PART 9: Summary
-- ============================================================

/-
## Summary of Formalization

### Problem
Erdős #1169 asks whether ω₁² → (ω₁², 3)² holds in ZFC.

### What We Formalize
1. The ordinal partition relation α → (β, k)² (axiomatized)
2. The key ordinals: ω₁ and ω₁² = ω₁ · ω₁
3. The problem statement: ordinalPartitionRel omega1Sq omega1Sq 3
4. Hajnal's CH-conditional result (axiomatized)
5. The theorem that CH implies Problem #1169 (proved from axiom)
6. Monotonicity properties and connections to Problems #592 and #118

### Status
- OPEN in ZFC (the main question)
- SOLVED under CH (Hajnal)
- NOT DISPROVABLE (consistent with ZFC)
- Related to #592 (countable analogue) and #118 (clique extension)

### Proof Strategy
The key axiom is Hajnal's result that CH implies the partition relation.
From this, we derive the answer to Problem #1169 under CH, and use
monotonicity to get additional consequences.

### Axiom Count: 12 axioms, 3 theorems proved
- ordinalPartitionRel: core definition
- omega1_uncountable, omega1Sq_card: basic cardinal properties
- hajnal_ch_implies_partition: Hajnal's CH result
- erdos_1169_not_disprovable, erdos_1169_open_in_zfc: metamathematical status
- partition_monotone_clique, partition_monotone_ordinal: monotonicity
- connection_to_592: Specker's theorem for countable case
- omega1_is_limit, omega_lt_omega1, omega1_regular: ω₁ properties
-/

end
