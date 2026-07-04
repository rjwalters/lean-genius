/-
Baire-Category Generalization of Uncountability:
Every nonempty complete metric space with no isolated points is uncountable.

**Open Question (algebraic-numbers-countable-oq-02-oq-02-oq-03)**:
The gallery's `algebraic-numbers-countable` entry (and its sibling
`oq-02-oq-02`, Cantor's 1874 nested-interval argument) shows that ℝ is
uncountable. What is the RIGHT level of generality for that phenomenon?

The answer is topological, not arithmetic: uncountability of ℝ is a special
case of the fact that any nonempty complete metric space without isolated
points (a *perfect* space) is uncountable. The reals inherit uncountability
purely because they are complete, connected, and have more than one point —
no special feature of the real line is needed.

**What This Proves** (0 axioms):
1. `card_nat_bool` — #(ℕ → Bool) = 𝔠 (the Cantor space has continuum cardinality)
2. `nat_bool_uncountable` — the Cantor space `ℕ → Bool` is uncountable
3. `perfect_nonempty_uncountable` — any nonempty perfect subset of a complete
   metric space is uncountable (the core theorem, subtype form)
4. `perfectSpace_uncountable` — a nonempty complete metric space with no
   isolated points is uncountable (main theorem, whole-space form)
5. `uncountable_of_connected` — a nonempty complete metric space that is
   connected and nontrivial is uncountable (corollary)
6. `real_uncountable` — ℝ is uncountable (recovered from the general theorem)

**Proof Strategy**:
The engine is Mathlib's `Perfect.exists_nat_bool_injection`: a nonempty perfect
set `C` in a complete metric space admits a continuous injection from the Cantor
space `ℕ → Bool`. Since `#(ℕ → Bool) = 2^ℵ₀ = 𝔠 > ℵ₀`, the Cantor space is
uncountable, and an injection out of an uncountable type forces the target to be
uncountable as well. The construction of the injection is a Cantor scheme: split
`C` into two disjoint nonempty perfect pieces of small diameter, recurse along a
binary address `ℕ → Bool`, and take the (necessarily unique, by completeness)
point in the nested intersection.

This is exactly the mechanism behind the classical Baire-category corollary that
a nonempty perfect Polish space is uncountable; here it is packaged for the
metric setting directly.

References:
- Mathlib: `Perfect.exists_nat_bool_injection` (Topology/MetricSpace/Perfect.lean)
- Kechris, A. "Classical Descriptive Set Theory" (1995), §6.A (perfect sets and
  the Cantor–Bendixson theorem): a nonempty perfect Polish space has cardinality 𝔠.
- Sibling `algebraic-numbers-countable-oq-02-oq-02`: Cantor's 1874 nested-interval
  proof of ℝ uncountability — the ℝ-specific instance of this general theorem.
-/

import Mathlib

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace BaireCategoryUncountable

open Cardinal Set Function

/-- The Cantor space `ℕ → Bool` has continuum cardinality: `#(ℕ → Bool) = 2^ℵ₀ = 𝔠`. -/
theorem card_nat_bool : #(ℕ → Bool) = 𝔠 := by
  rw [Cardinal.mk_arrow, Cardinal.mk_bool, Cardinal.mk_nat, Cardinal.lift_two,
    Cardinal.lift_aleph0, Cardinal.two_power_aleph0]

/-- The Cantor space `ℕ → Bool` is uncountable. -/
theorem nat_bool_uncountable : Uncountable (ℕ → Bool) := by
  rw [← Cardinal.aleph0_lt_mk_iff, card_nat_bool]
  exact Cardinal.aleph0_lt_continuum

/-- **Core theorem (subtype form).** Any nonempty perfect subset of a complete metric
space is uncountable. The injection from the (uncountable) Cantor space is supplied
by `Perfect.exists_nat_bool_injection`. -/
theorem perfect_nonempty_uncountable {X : Type*} [MetricSpace X] [CompleteSpace X]
    {C : Set X} (hC : Perfect C) (hne : C.Nonempty) : Uncountable ↥C := by
  obtain ⟨f, hrange, -, hinj⟩ := hC.exists_nat_bool_injection hne
  haveI : Uncountable (ℕ → Bool) := nat_bool_uncountable
  -- Lift the injection `f : (ℕ → Bool) → X` to land in the subtype `↥C`.
  let g : (ℕ → Bool) → C := fun x => ⟨f x, hrange (mem_range_self x)⟩
  have hg : Function.Injective g := fun a b h => hinj (congrArg Subtype.val h)
  -- An injection out of the uncountable Cantor space forces `↥C` uncountable.
  exact hg.uncountable

/-- **Main theorem (whole-space form).** A nonempty complete metric space with no
isolated points (i.e. a `PerfectSpace`) is uncountable. -/
theorem perfectSpace_uncountable {X : Type*} [MetricSpace X] [CompleteSpace X]
    [Nonempty X] [PerfectSpace X] : Uncountable X := by
  haveI : Uncountable (ℕ → Bool) := nat_bool_uncountable
  obtain ⟨f, -, -, hinj⟩ :=
    (PerfectSpace.univ_perfect (α := X)).exists_nat_bool_injection Set.univ_nonempty
  exact hinj.uncountable

/-- **Corollary.** A nonempty complete metric space that is connected and has more
than one point is uncountable. (A connected `T1` space with two distinct points is
automatically perfect, so this follows from the main theorem.) -/
theorem uncountable_of_connected {X : Type*} [MetricSpace X] [CompleteSpace X]
    [Nonempty X] [ConnectedSpace X] [Nontrivial X] : Uncountable X :=
  perfectSpace_uncountable

/-- **Application.** The classical result: ℝ is uncountable, recovered as the
instance of the general theorem at the complete, connected, nontrivial metric
space `ℝ`. -/
theorem real_uncountable : Uncountable ℝ :=
  uncountable_of_connected

end BaireCategoryUncountable
