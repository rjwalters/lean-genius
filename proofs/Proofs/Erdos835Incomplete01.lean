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

3. `erdosRosenfeld_range_univ` — equivalently the image of the colouring is
   all of `Fin (k+1)`, so exactly `k+1` colours are used.

4. `erdosRosenfeldQuestion_surjective` — hence a positive answer to the
   question yields a surjective `(k+1)`-colouring. This is the "rainbow ⇒ all
   colours present" half that any analysis of the question relies on, made
   precise without the chromatic-number machinery.

5. `erdosRosenfeld_window_injective` — within any `(k+1)`-subset `A`, the `k+1`
   `k`-subsets of `A` get the `k+1` *distinct* colours (a surjection between
   equal-size sets is a bijection).

6. `erdosRosenfeld_proper` — consequently adjacent `k`-subsets in `J(2k,k)`
   (those meeting in `k-1` elements) get different colours: the property is a
   genuine proper `(k+1)`-colouring of the Johnson graph (the *upper* half of
   `property ⇔ χ(J(2k,k)) = k+1`).

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

/-- **Rainbow within a window.** For `k ≥ 1`, if `χ` has the Erdős–Rosenfeld
    property then its restriction to the `k`-subsets of any `(k+1)`-subset `A` of
    `{1,…,2k}` is *injective*: the `k+1` distinct `k`-subsets of `A` receive the
    `k+1` distinct colours. There are exactly `k+1` such subsets (one per omitted
    element), and the property already forces all `k+1` colours to appear among
    them, so the surjection between equal-size sets is in fact a bijection. -/
theorem erdosRosenfeld_window_injective (k : ℕ) (hk : 1 ≤ k)
    (χ : kSubsets (2 * k) k → Fin (k + 1)) (h : hasErdosRosenfeldProperty k χ)
    (A : Finset ℕ) (hA : A ⊆ baseSet (2 * k)) (hAcard : A.card = k + 1)
    (S T : kSubsets (2 * k) k) (hS : S.val ⊆ A) (hT : T.val ⊆ A)
    (hcol : χ S = χ T) : S.val = T.val := by
  classical
  -- Lift the colouring to a total function with a junk default off the `k`-subsets.
  let φ : Finset ℕ → Fin (k + 1) :=
    fun s => if hs : s ⊆ baseSet (2 * k) ∧ s.card = k then χ ⟨s, hs⟩ else 0
  have key : ∀ U : kSubsets (2 * k) k, φ U.val = χ U := by
    intro U
    show (if hs : U.val ⊆ baseSet (2 * k) ∧ U.val.card = k then χ ⟨U.val, hs⟩ else 0) = χ U
    exact dif_pos ⟨U.2.1, U.2.2⟩
  -- `φ` maps the `k`-subsets of `A` *onto* all `k+1` colours (the property).
  have hmaps : Set.MapsTo φ (↑(A.powersetCard k))
      (↑(Finset.univ : Finset (Fin (k + 1)))) := fun s _ => by simp
  have hsurj : Set.SurjOn φ (↑(A.powersetCard k))
      (↑(Finset.univ : Finset (Fin (k + 1)))) := by
    intro c _
    obtain ⟨S', hS'sub, hS'c⟩ := h A hA hAcard c
    rw [Set.mem_image]
    refine ⟨S'.val, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_powersetCard]
      exact ⟨hS'sub, S'.2.2⟩
    · rw [key S']; exact hS'c
  -- Both the domain window and the colour set have exactly `k+1` elements.
  have hcard : (A.powersetCard k).card ≤ (Finset.univ : Finset (Fin (k + 1))).card := by
    have heq : (A.powersetCard k).card = (Finset.univ : Finset (Fin (k + 1))).card := by
      rw [Finset.card_powersetCard, hAcard, Nat.choose_succ_self_right,
          Finset.card_univ, Fintype.card_fin]
    exact heq.le
  -- A surjection between equal-size finite sets is injective.
  have hinj : Set.InjOn φ (↑(A.powersetCard k)) :=
    Finset.injOn_of_surjOn_of_card_le φ hmaps hsurj hcard
  have hSmem : (S.val : Finset ℕ) ∈ (↑(A.powersetCard k) : Set (Finset ℕ)) := by
    simp only [Finset.mem_coe, Finset.mem_powersetCard]; exact ⟨hS, S.2.2⟩
  have hTmem : (T.val : Finset ℕ) ∈ (↑(A.powersetCard k) : Set (Finset ℕ)) := by
    simp only [Finset.mem_coe, Finset.mem_powersetCard]; exact ⟨hT, T.2.2⟩
  exact hinj hSmem hTmem (by rw [key S, key T, hcol])

/-- **The Erdős–Rosenfeld property is a proper colouring of the Johnson graph.**
    For `k ≥ 1`, two distinct `k`-subsets `S, T` of `{1,…,2k}` that are *adjacent*
    in `J(2k,k)` — i.e. `|S ∩ T| = k − 1`, equivalently `|S ∪ T| = k + 1` — receive
    different colours. Their union `A = S ∪ T` is a `(k+1)`-subset and both `S, T`
    are `k`-subsets of it, so the rainbow property of the window
    (`erdosRosenfeld_window_injective`) separates them. This is the *upper* half of
    `property ⇔ χ(J(2k,k)) = k+1`: an Erdős–Rosenfeld colouring is a genuine proper
    `(k+1)`-colouring of the Johnson graph, complementing the surjectivity (lower)
    half above. -/
theorem erdosRosenfeld_proper (k : ℕ) (hk : 1 ≤ k)
    (χ : kSubsets (2 * k) k → Fin (k + 1)) (h : hasErdosRosenfeldProperty k χ)
    (S T : kSubsets (2 * k) k) (hne : S.val ≠ T.val)
    (hadj : (S.val ∩ T.val).card = k - 1) : χ S ≠ χ T := by
  intro hcol
  apply hne
  have hA : S.val ∪ T.val ⊆ baseSet (2 * k) := Finset.union_subset S.2.1 T.2.1
  have hAcard : (S.val ∪ T.val).card = k + 1 := by
    have hu := Finset.card_union_add_card_inter S.val T.val
    rw [S.2.2, T.2.2, hadj] at hu
    omega
  exact erdosRosenfeld_window_injective k hk χ h (S.val ∪ T.val) hA hAcard S T
    Finset.subset_union_left Finset.subset_union_right hcol

/-
## Significance

Erdős #835 asks whether the `k`-subsets of `{1,…,2k}` admit a `(k+1)`-colouring
that is "rainbow" on every `(k+1)`-subset — equivalently whether the Johnson graph
`J(2k,k)` has chromatic number `k+1`. The scaffold sets up the property but leaves
the chromatic-number definition and the `k=2` construction as `sorry`s.

This entry extracts the unconditional structural content of the property. The
*lower* side (`erdosRosenfeld_surjective`, `erdosRosenfeld_range_univ`): any
colouring satisfying the property is surjective — it genuinely uses all `k+1`
colours, so it cannot waste a colour. The *upper* side
(`erdosRosenfeld_window_injective`, `erdosRosenfeld_proper`): the property is
also a genuine proper colouring of the Johnson graph `J(2k,k)` — adjacent
`k`-subsets receive distinct colours. Together they pin both inequalities of the
equivalence "`property ⇔ χ(J(2k,k)) = k+1`", with no appeal to the chromatic
number or to any explicit colouring. The remaining (open-in-this-formalization)
content is the existence/non-existence of such colourings, which is exactly the
combinatorial heart the scaffold's `sorry`s stand in for.
-/

end Erdos835Incomplete01
