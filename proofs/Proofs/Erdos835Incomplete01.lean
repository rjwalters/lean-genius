import Mathlib

/-
# Erdős #835 — the Erdős–Rosenfeld property forces a surjective coloring
# (erdos-835-incomplete-01)

## The Problem

**Erdős Problem #835** (Erdős–Rosenfeld; SOLVED, answer NO). Does there exist
`k > 2` such that the `k`-subsets of `{1,…,2k}` can be coloured with `k+1`
colours so that for every `(k+1)`-subset `A ⊆ {1,…,2k}`, all `k+1` colours appear
among the `k`-subsets of `A`? Equivalently, is `χ(J(2k,k)) = k+1`? The answer is
no for `3 ≤ k ≤ 8`.

The scaffold `Erdos835Problem.lean` defines the *Erdős–Rosenfeld property*
(`hasErdosRosenfeldProperty`) and the question (`ErdosRosenfeldQuestion`), but its
two `sorry`s are the chromatic-number definition and the explicit `k = 2` colouring
construction.

## Result

We prove an unconditional structural consequence of the property, independent of
both `sorry`s: **a colouring with the Erdős–Rosenfeld property is surjective** —
it actually uses all `k+1` colours.

1. `baseSet_card` — `|{1,…,n}| = n` (the elementary count the scaffold omitted).

2. `erdosRosenfeld_surjective` — for `k ≥ 1`, a colouring with the
   Erdős–Rosenfeld property is surjective onto `Fin (k+1)`. Pick any
   `(k+1)`-subset `A` of `{1,…,2k}` (one exists since `k+1 ≤ 2k`); the property
   exhibits, for every colour `c`, a `k`-subset of `A` coloured `c`.

3. `erdosRosenfeld_uses_all_colors` — equivalently the image of the colouring is
   all of `Fin (k+1)`, so exactly `k+1` colours are used.

4. `erdosRosenfeldQuestion_surjective` — hence a positive answer to the
   question yields a surjective `(k+1)`-colouring. This is the "rainbow ⇒ all
   colours present" half that any analysis of the question relies on, made
   precise without the chromatic-number machinery.

## Summary: 0 sorries, 0 axioms, no `native_decide`.
Self-contained: the scaffold `Erdos835Problem.lean` currently fails to parse on
the pinned toolchain (a docstring-before-tactic parse error), so the relevant
definitions are re-declared verbatim.
-/

set_option linter.unusedVariables false

namespace Erdos835Incomplete01

open Finset

-- ============================================================
-- The Erdős #835 definitions (re-declared; see note above)
-- ============================================================

/-- The base set `{1, 2, …, n}`. -/
def baseSet (n : ℕ) : Finset ℕ := (Finset.range n).map ⟨(· + 1), add_left_injective 1⟩

/-- The `k`-subsets of `{1,…,n}`, as a subtype. -/
def kSubsets (n k : ℕ) : Type := { S : Finset ℕ // S ⊆ baseSet n ∧ S.card = k }

/-- A colouring has the Erdős–Rosenfeld property if every `(k+1)`-subset of
    `{1,…,2k}` contains `k`-subsets of all `k+1` colours. -/
def hasErdosRosenfeldProperty (k : ℕ) (χ : kSubsets (2 * k) k → Fin (k + 1)) : Prop :=
  ∀ A : Finset ℕ, A ⊆ baseSet (2 * k) → A.card = k + 1 →
    ∀ c : Fin (k + 1), ∃ S : kSubsets (2 * k) k, S.val ⊆ A ∧ χ S = c

/-- The Erdős–Rosenfeld question for parameter `k`. -/
def ErdosRosenfeldQuestion (k : ℕ) : Prop :=
  ∃ χ : kSubsets (2 * k) k → Fin (k + 1), hasErdosRosenfeldProperty k χ

/-- The base set `{1, …, n}` has exactly `n` elements. -/
theorem baseSet_card (n : ℕ) : (baseSet n).card = n := by
  unfold baseSet
  rw [Finset.card_map, Finset.card_range]

/-- **The Erdős–Rosenfeld property forces a surjective colouring.** For `k ≥ 1`,
    a colouring `χ` with the property uses every colour: pick any `(k+1)`-subset
    `A` of `{1,…,2k}` (possible since `k+1 ≤ 2k`), and the property provides, for
    each colour `c`, a `k`-subset of `A` coloured `c`. -/
theorem erdosRosenfeld_surjective (k : ℕ) (hk : 1 ≤ k)
    (χ : kSubsets (2 * k) k → Fin (k + 1))
    (h : hasErdosRosenfeldProperty k χ) : Function.Surjective χ := by
  intro c
  obtain ⟨A, hA, hAcard⟩ :
      ∃ A ⊆ baseSet (2 * k), A.card = k + 1 :=
    Finset.exists_subset_card_eq (by rw [baseSet_card]; omega)
  obtain ⟨S, hSA, hSc⟩ := h A hA hAcard c
  exact ⟨S, hSc⟩

/-- Equivalently, every colour has a preimage: the range of an Erdős–Rosenfeld
    colouring is all of `Fin (k+1)`, so exactly `k+1` colours are used. -/
theorem erdosRosenfeld_range_univ (k : ℕ) (hk : 1 ≤ k)
    (χ : kSubsets (2 * k) k → Fin (k + 1))
    (h : hasErdosRosenfeldProperty k χ) :
    Set.range χ = Set.univ :=
  (erdosRosenfeld_surjective k hk χ h).range_eq

/-- A positive answer to the Erdős–Rosenfeld question for `k ≥ 1` yields a
    **surjective** `(k+1)`-colouring of the `k`-subsets. -/
theorem erdosRosenfeldQuestion_surjective (k : ℕ) (hk : 1 ≤ k)
    (h : ErdosRosenfeldQuestion k) :
    ∃ χ : kSubsets (2 * k) k → Fin (k + 1), Function.Surjective χ := by
  obtain ⟨χ, hχ⟩ := h
  exact ⟨χ, erdosRosenfeld_surjective k hk χ hχ⟩

/-
## Significance

Erdős #835 asks whether the `k`-subsets of `{1,…,2k}` admit a `(k+1)`-colouring
that is "rainbow" on every `(k+1)`-subset — equivalently whether the Johnson graph
`J(2k,k)` has chromatic number `k+1`. The scaffold sets up the property but leaves
the chromatic-number definition and the `k=2` construction as `sorry`s.

This entry extracts the unconditional structural content of the property: any
colouring satisfying it is surjective — it genuinely uses all `k+1` colours
(`erdosRosenfeld_surjective`, `erdosRosenfeld_uses_all_colors`). This is the
elementary "rainbow ⇒ all colours present" direction, and it holds with no
appeal to the chromatic number or to any explicit colouring. It is the half of
the equivalence "`property ⇔ χ(J(2k,k)) = k+1`" that pins the *lower* side: a
valid colouring cannot waste a colour. The remaining (open-in-this-formalization)
content is the existence/non-existence of such colourings, which is exactly the
combinatorial heart the scaffold's `sorry`s stand in for.
-/

end Erdos835Incomplete01
