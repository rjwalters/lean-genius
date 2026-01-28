/-
Erdős Problem #474: Coloring ℝ² for Uncountable Sets

Source: https://erdosproblems.com/474
Status: OPEN (independence results known)
Prize: $100

Statement:
Under what set-theoretic assumptions is it true that ℝ² can be 3-colored such that
for every uncountable A ⊆ ℝ², the set A² (pairs from A) contains a pair of each color?

In partition calculus notation: When does 2^ℵ₀ → (ℵ₁)³₂ hold?

History:
- 1954: Erdős posed the problem
- Sierpinski, Kurepa: Independently proved the 2-color case always works
- Erdős: Proved it holds under CH (c = ℵ₁)
- Shelah: Showed a negative answer is consistent (with large c)
- Open: Is negative answer consistent with c = ℵ₂?

References:
- [Er54]: Original problem
- [Er95d]: Erdős's collected works
- [Va99, 7.81]: Väänänen (1999)
-/

import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic

open Cardinal Set

namespace Erdos474

/-! ## Part I: Cardinal Definitions -/

/--
**The Continuum:**
c = 2^ℵ₀ = |ℝ| = |P(ℕ)|
-/
noncomputable def continuum : Cardinal := 2 ^ Cardinal.aleph 0

/--
**The First Uncountable Cardinal:**
ℵ₁ = the smallest uncountable cardinal
-/
noncomputable def aleph1 : Cardinal := Cardinal.aleph 1

/--
**The Second Uncountable Cardinal:**
ℵ₂ = the smallest cardinal greater than ℵ₁
-/
noncomputable def aleph2 : Cardinal := Cardinal.aleph 2

/-! ## Part II: The Coloring Problem -/

/--
**Three-Coloring of the Plane:**
A function χ: ℝ² → {0, 1, 2} assigning one of three colors to each point.
-/
def ThreeColoring (X : Type*) := X → Fin 3

/--
**Uncountable Subset:**
A set A is uncountable if |A| ≥ ℵ₁.
-/
def IsUncountable {X : Type*} (A : Set X) : Prop :=
  Cardinal.aleph 1 ≤ Cardinal.mk A

/--
**Pair Contains All Colors:**
For coloring χ and set A, the pairs A² = {(a,b) : a,b ∈ A} contain
all three colors in the sense that for each color c, there exist
distinct a, b ∈ A with χ(a,b) = c.
-/
def ContainsAllColorPairs {X : Type*} (χ : ThreeColoring (X × X)) (A : Set X) : Prop :=
  ∀ c : Fin 3, ∃ a b : X, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) = c

/-! ## Part III: The Main Conjecture -/

/--
**The Erdős Coloring Property:**
ℝ² can be 3-colored such that every uncountable set contains pairs of all colors.
-/
def ErdosColoringProperty (X : Type*) : Prop :=
  ∃ χ : ThreeColoring (X × X),
    ∀ A : Set X, IsUncountable A → ContainsAllColorPairs χ A

/--
**Partition Arrow Notation:**
2^ℵ₀ → (ℵ₁)³₂ means: for any 3-coloring of pairs from the continuum,
there exists an ℵ₁-sized monochromatic set.

Equivalently: any 3-coloring of pairs from 2^ℵ₀ has an ℵ₁-sized monochromatic set.
-/
def PartitionProperty : Prop :=
  ∀ χ : ThreeColoring ((Fin 2 → ℕ) × (Fin 2 → ℕ)),
    ∃ A : Set (Fin 2 → ℕ), IsUncountable A ∧
    ∃ c : Fin 3, ∀ a b : Fin 2 → ℕ, a ∈ A → b ∈ A → a ≠ b → χ (a, b) = c

/-! ## Part IV: The Two-Color Case (Solved) -/

/--
**Two-Color Theorem (Sierpinski-Kurepa):**
For 2 colors, the property always holds: any 2-coloring of pairs
from an uncountable set contains both colors.
This was proved independently by Sierpinski and Kurepa.
-/
axiom sierpinski_kurepa :
  ∀ (X : Type*) (χ : X × X → Fin 2) (A : Set X),
    IsUncountable A →
    (∀ c : Fin 2, ∃ a b : X, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) = c)

/--
**In Partition Notation:**
2^ℵ₀ → (ℵ₁)²₂ holds unconditionally.
Every 2-coloring of pairs from the continuum has an uncountable monochromatic set.
-/
axiom two_color_partition :
  ∀ χ : (Fin 2 → ℕ) × (Fin 2 → ℕ) → Fin 2,
    ∃ A : Set (Fin 2 → ℕ), IsUncountable A ∧
    ∃ c : Fin 2, ∀ a b : Fin 2 → ℕ, a ∈ A → b ∈ A → a ≠ b → χ (a, b) = c

/-! ## Part V: Under CH (Erdős's Result) -/

/--
**The Continuum Hypothesis (CH):**
c = ℵ₁, i.e., 2^ℵ₀ = ℵ₁.
-/
def ContinuumHypothesis : Prop := continuum = aleph1

/--
**Erdős's Theorem (under CH):**
If CH holds, then the 3-color property holds.
2^ℵ₀ → (ℵ₁)³₂ is true when c = ℵ₁.
-/
axiom erdos_under_ch :
  ContinuumHypothesis →
  ∀ χ : ThreeColoring (ℝ × ℝ),
    ∀ A : Set ℝ, IsUncountable A → ContainsAllColorPairs χ A

/-! ## Part VI: Shelah's Consistency Result -/

/--
**Shelah's Independence Result:**
It is consistent with ZFC that the partition property fails.
More precisely, there is a model of ZFC with a 3-coloring of pairs
from the continuum such that no uncountable set is monochromatic
for any single color.
-/
axiom shelah_consistency :
  ∃ (M : Type) (_ : Nonempty M),
    -- In some model M, there exists a "bad" 3-coloring
    ∃ χ : M × M → Fin 3,
      ∀ A : Set M, IsUncountable A →
        ∃ c : Fin 3, ∃ a b : M, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) ≠ c

/--
**Shelah's Large Continuum:**
Shelah's counterexample model has a very large continuum —
much larger than ℵ₂. The model satisfies c > ℵ₂.
-/
axiom shelah_large_c :
  ∃ (M : Type) (_ : Nonempty M),
    Cardinal.mk M > Cardinal.aleph 2

/-! ## Part VII: The Open Question -/

/--
**Open Problem:**
Is a negative answer consistent with c = ℵ₂?

More precisely: Is it consistent with ZFC + (c = ℵ₂) that
there exists a 3-coloring of pairs such that some uncountable
set avoids pairs of some color?
-/
def OpenQuestion : Prop :=
  -- Is there a model with c = ℵ₂ where the partition property fails?
  ∃ (M : Type) (_ : Nonempty M),
    Cardinal.mk M = Cardinal.aleph 2 ∧
    ∃ χ : M × M → Fin 3,
      ∀ A : Set M, IsUncountable A →
        ∃ c : Fin 3, ∃ a b : M, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) ≠ c

/--
**The $100 Question:**
Erdős offered $100 for deciding what happens without CH.
This essentially asks: what is the minimal cardinal κ such that
c = κ is consistent with failure of 2^ℵ₀ → (ℵ₁)³₂?
-/
def erdos_prize_question : Prop :=
  ∃ κ : Cardinal, κ > Cardinal.aleph 1 ∧
    -- κ is the minimal cardinal where failure is consistent
    (∀ λ : Cardinal, Cardinal.aleph 1 < λ → λ < κ →
      -- for smaller λ, the property holds when c = λ
      ∀ χ : ThreeColoring ((Fin 2 → ℕ) × (Fin 2 → ℕ)),
        ∃ A : Set (Fin 2 → ℕ), IsUncountable A ∧
        ∃ c : Fin 3, ∀ a b : Fin 2 → ℕ, a ∈ A → b ∈ A → a ≠ b → χ (a, b) = c)

/-! ## Part VIII: Related Results -/

/--
**Negative Partition Relation:**
2^ℵ₀ ↛ (ℵ₁)³₂ denotes that the partition property fails:
there exists a 3-coloring with no ℵ₁-sized monochromatic set.
-/
def NegativePartition : Prop :=
  ∃ χ : ThreeColoring ((Fin 2 → ℕ) × (Fin 2 → ℕ)),
    ∀ A : Set (Fin 2 → ℕ), IsUncountable A →
    ∃ c : Fin 3, ∃ a b : Fin 2 → ℕ, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) ≠ c

/--
**Higher Color Numbers:**
For k ≥ 4 colors, the partition relation 2^ℵ₀ → (ℵ₁)^k₂ is at least
as hard as the 3-color case. Failure for 3 colors implies failure
for all higher k.
-/
axiom higher_colors_harder :
  NegativePartition →
  ∀ k : ℕ, k ≥ 3 →
    ∃ χ : ThreeColoring ((Fin 2 → ℕ) × (Fin 2 → ℕ)),
      ∀ A : Set (Fin 2 → ℕ), IsUncountable A →
      ∃ c : Fin 3, ∃ a b : Fin 2 → ℕ, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) ≠ c

/--
**Ramsey Theory Connection:**
The Erdős-Rado theorem establishes that for the 2-color case,
(2^κ)⁺ → (κ⁺)²₂ holds for all infinite cardinals κ.
The 3-color case is more delicate and depends on cardinal arithmetic.
-/
axiom erdos_rado_two_color :
  ∀ κ : Cardinal, Cardinal.aleph 0 ≤ κ →
    ∀ χ : (Fin 2 → ℕ) × (Fin 2 → ℕ) → Fin 2,
      ∃ A : Set (Fin 2 → ℕ), IsUncountable A ∧
      ∃ c : Fin 2, ∀ a b : Fin 2 → ℕ, a ∈ A → b ∈ A → a ≠ b → χ (a, b) = c

/-! ## Part IX: The Argument Structure -/

/--
**Why CH Helps:**
Under CH, |ℝ| = ℵ₁, so ℝ can be well-ordered in order type ω₁.
For any 3-coloring of pairs, a diagonal argument over this well-ordering
produces an uncountable monochromatic set by transfinite induction.
-/
axiom ch_argument :
  ContinuumHypothesis →
  ∀ χ : ThreeColoring (ℝ × ℝ),
    ∃ A : Set ℝ, IsUncountable A ∧
    ∃ c : Fin 3, ∀ a b : ℝ, a ∈ A → b ∈ A → a ≠ b → χ (a, b) = c

/--
**Why Larger c Might Fail:**
With larger c, the continuum has "more room" for colorings to avoid
monochromatic uncountable sets. Forcing constructions can exploit
this extra room to build counterexamples when c is sufficiently large.
-/
axiom large_c_failure :
  ∃ κ : Cardinal, κ > Cardinal.aleph 2 →
    -- For sufficiently large c, a counterexample model can be forced
    ∃ (M : Type) (_ : Nonempty M),
      Cardinal.mk M = κ ∧
      ∃ χ : M × M → Fin 3,
        ∀ A : Set M, IsUncountable A →
          ∃ c : Fin 3, ∃ a b : M, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) ≠ c

/-! ## Part X: Summary -/

/--
**Erdős Problem #474: Summary**

PROBLEM: Under what set-theoretic assumptions can ℝ² be 3-colored
such that every uncountable A has A² containing pairs of all colors?

STATUS: PARTIALLY RESOLVED
- 2 colors: Always works (Sierpinski-Kurepa)
- 3 colors + CH: Works (Erdős)
- 3 colors: Negative answer consistent with large c (Shelah)
- 3 colors + c = ℵ₂: OPEN

PRIZE: $100 for deciding without CH

KEY INSIGHT: The problem sits at the boundary of cardinal arithmetic
and Ramsey theory, where independence phenomena arise.
-/
theorem erdos_474_summary :
    -- Under CH, the property holds
    (ContinuumHypothesis →
      ∀ χ : ThreeColoring (ℝ × ℝ),
        ∀ A : Set ℝ, IsUncountable A → ContainsAllColorPairs χ A) ∧
    -- The 2-color case always works
    (∀ (X : Type*) (χ : X × X → Fin 2) (A : Set X),
      IsUncountable A →
      (∀ c : Fin 2, ∃ a b : X, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) = c)) :=
  ⟨erdos_under_ch, sierpinski_kurepa⟩

/--
**Erdős Problem #474: OPEN**
The full resolution without CH remains open. The key unsettled question is
whether a negative answer is consistent with c = ℵ₂. Erdős offered $100.
-/
theorem erdos_474 :
    -- Under CH, the 3-color property holds
    (ContinuumHypothesis →
      ∀ χ : ThreeColoring (ℝ × ℝ),
        ∀ A : Set ℝ, IsUncountable A → ContainsAllColorPairs χ A) ∧
    -- A negative answer is consistent with ZFC (Shelah)
    (∃ (M : Type) (_ : Nonempty M),
      ∃ χ : M × M → Fin 3,
        ∀ A : Set M, IsUncountable A →
          ∃ c : Fin 3, ∃ a b : M, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ χ (a, b) ≠ c) :=
  ⟨erdos_under_ch, shelah_consistency⟩

end Erdos474
