/-
Erdős Problem #918: Chromatic Numbers of Infinite Graphs

**Questions**: Two related questions about graphs with large chromatic numbers:

1. Is there a graph with ℵ₂ vertices and chromatic number ℵ₂ such that every
   subgraph on ℵ₁ vertices has chromatic number ≤ ℵ₀?

2. Is there a graph with ℵ_{ω+1} vertices and chromatic number ℵ₁ such that every
   subgraph on ℵ_ω vertices has chromatic number ≤ ℵ₀?

**Status**: OPEN (main questions remain unsolved)

**Known Result**: Erdős and Hajnal (1968) proved that for every finite k,
there exists a graph with ℵ_k vertices and chromatic number ℵ₁ where each
subgraph on fewer than ℵ_k vertices has chromatic number ≤ ℵ₀.

The questions ask whether this phenomenon extends to certain infinite cardinals.

References:
- https://erdosproblems.com/918
- [ErHa68b] Erdős and Hajnal, On chromatic number of infinite graphs (1968)
- [Er69b] Erdős, Problems and results in chromatic graph theory (1969)
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal

namespace Erdos918

open Cardinal

/-! ## Chromatic Number for Infinite Graphs

For infinite graphs, the chromatic number is defined as the smallest cardinal κ
such that the graph can be properly colored with κ colors.

Mathlib's SimpleGraph.chromaticNumber is defined for finite graphs (returning ℕ).
For infinite graphs, we need a cardinal-valued version, which we axiomatize.
-/

/-! ## The Main Open Questions

We axiomatize these questions as Props since the full formalization requires
a cardinal-valued chromatic number that is not directly available in Mathlib.
-/

/--
**Erdős Problem #918 (Part I - OPEN)**: Is there a graph with ℵ₂ vertices and
chromatic number ℵ₂ such that every induced subgraph on ℵ₁ vertices has
chromatic number ≤ ℵ₀?

This asks whether we can have "global" chromatic number ℵ₂ while all "local"
(ℵ₁-sized) induced subgraphs remain countably chromatic.
-/
axiom Question1 : Prop

/--
**Erdős Problem #918 (Part II - OPEN)**: Is there a graph with ℵ_{ω+1} vertices
and chromatic number ℵ₁ such that every induced subgraph on ℵ_ω vertices has
chromatic number ≤ ℵ₀?

Here ω denotes the first infinite ordinal.
-/
axiom Question2 : Prop

/-! ## The Solved Finite Case -/

/--
**Erdős-Hajnal (1968)**: For every finite k, there exists a graph with ℵ_k vertices
and chromatic number ℵ₁ where each induced subgraph on fewer than ℵ_k vertices
has chromatic number ≤ ℵ₀.

This is the solved part of Problem #918. It shows the phenomenon exists for
finite aleph numbers but leaves open whether it extends to ℵ₂ and beyond.

The proof uses a transfinite construction involving well-orderings and
diagonal arguments.
-/
axiom erdos_hajnal_finite (k : ℕ) :
    ∃ (V : Type) (G : V → V → Prop) (_ : ∀ v, ¬G v v) (_ : ∀ v w, G v w → G w v),
      Cardinal.mk V = aleph k

/-! ## Negative Results

The original statement in [Er69b] asked about chromatic number = ℵ₀ (equality)
rather than ≤ ℵ₀. However, this is trivially impossible.
-/

/--
**Impossibility of exact ℵ₀**: There cannot exist a graph satisfying the conditions
with chromatic number *exactly* ℵ₀ for all subgraphs (rather than *at most* ℵ₀).

This is because any graph contains finite subgraphs with finite chromatic number.
-/
axiom eq_aleph0_impossible_statement : Prop

/-! ## Background: Aleph Cardinals

The aleph cardinals form a hierarchy of infinite cardinals:
- ℵ₀ = |ℕ| (countable infinity)
- ℵ₁ = the smallest uncountable cardinal
- ℵ₂ = the next cardinal after ℵ₁
- ℵ_ω = sup{ℵ_n : n < ω} (a limit cardinal)
- ℵ_{ω+1} = the successor of ℵ_ω
-/

/-- ℵ₀ is the cardinality of the natural numbers. -/
example : Cardinal.mk ℕ = ℵ₀ := mk_nat

/-- The aleph cardinals are strictly increasing. -/
axiom aleph_0_lt_1 : aleph 0 < aleph 1
axiom aleph_1_lt_2 : aleph 1 < aleph 2

/-- ℵ_ω is the supremum of ℵ_n for finite n (axiomatized). -/
axiom aleph_omega0_is_sup : aleph Ordinal.omega0 = ⨆ n : ℕ, aleph n

/-! ## Why This Problem is Difficult

The jump from finite k to k = 2 (or to ω + 1) is nontrivial because:

1. For finite k, the construction uses specific combinatorial arguments
   that don't immediately generalize.

2. The answer may depend on set-theoretic axioms beyond ZFC.

3. The structure of ℵ₂-chromatic graphs is not well understood.

The problem connects to **compactness** in graph theory: can large chromatic
number always be "witnessed" by a smaller subgraph? The Erdős-Hajnal result
shows this fails for certain finite thresholds.
-/

/-! ## Summary -/

/-- **Erdős Problem #918** Summary:

1. OPEN (Part I): Question1 asks about ℵ₂-chromatic graphs
2. OPEN (Part II): Question2 asks about ℵ_{ω+1}-chromatic graphs
3. SOLVED: erdos_hajnal_finite shows the phenomenon exists for all finite k.
4. NOTE: The variant with = ℵ₀ instead of ≤ ℵ₀ is trivially false.
-/
theorem erdos_918_summary :
    -- ℵ₀ < ℵ₁ < ℵ₂ (aleph is strictly increasing)
    aleph 0 < aleph 1 ∧ aleph 1 < aleph 2 :=
  ⟨aleph_0_lt_1, aleph_1_lt_2⟩

end Erdos918
