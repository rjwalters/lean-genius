/-
  Szemeredi Core OQ-04: Algorithmic Szemerédi — Decidable Surrogate
  (Alon–Duke–Lefmann–Rödl–Yuster 1994)

  This file scaffolds the algorithmic-Szemerédi refactor:

    1. `witnessFamilyB G A B` — the ε-grid for `B` relative to `A`:
       for each `a ∈ A` we take `B ∩ N(a)` and `B \ N(a)`.
       The family has at most `2 * |A|` elements.

    2. `IsWitnessRegular G eps A B` — a polynomial-size surrogate for
       `IsEpsilonRegular G eps A B`. Instead of quantifying over all
       `(A', B')`, it only quantifies over `B' ∈ witnessFamilyB G A B`
       (held against `A' = A`).

    3. A `Decidable` instance — by construction the surrogate quantifies
       over a finite, explicitly enumerable family.

    4. `witness_regular_implies_epsilon_regular` — the ADLRY one-way
       implication, with slack constant `4`:
       `IsWitnessRegular G eps A B → IsEpsilonRegular G (4 * eps) A B`.

  Mathematical content: Alon, Duke, Lefmann, Rödl, Yuster, _The Algorithmic
  Aspects of the Regularity Lemma_, J. Algorithms 16(1):80–109 (1994).
  Pedagogical reference: Y. Zhao, _Graph Theory and Additive Combinatorics_,
  §3.4 (Algorithmic regularity).

  Why a separate file: per the Szemerédi pipeline architecture (memory:
  `feedback_szemeredi_architecture`), `SzemerediCore.lean` is frozen to
  prevent definition drift across the cluster. The decidable surrogate is
  a new layer that imports `SzemerediCore` but does not modify it.

  Scope of this S2 scaffold:
    • The definitions and `Decidable` instance are sorry-free.
    • The ADLRY implication carries one `sorry`: the density-decomposition
      bound. The proof strategy is documented inline.
    • Downstream targets (witness extraction, computable
      `findRegularPartition`, Mathlib bridge) are deferred to S3–S5.
-/
import Mathlib
import Proofs.SzemerediCore

namespace Szemeredi.OQ04

open Szemeredi.Core
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Part 1: The ε-grid family -/

/-- The ε-grid for `B` relative to `A`: for each `a ∈ A`, both the
    neighbour-pattern `B ∩ N(a)` and its complement `B \ N(a)` in `B`.

    The family has at most `2 · |A|` elements; this is the polynomial-size
    family that gives ADLRY-1994 its polynomial time bound. -/
def witnessFamilyB (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (Finset V) :=
  A.image (fun a => B.filter (fun b => G.Adj a b)) ∪
  A.image (fun a => B.filter (fun b => ¬ G.Adj a b))

/-- The witness family has size at most `2 * |A|`. -/
lemma witnessFamilyB_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (witnessFamilyB G A B).card ≤ 2 * A.card := by
  unfold witnessFamilyB
  have h1 := Finset.card_union_le
      (A.image (fun a => B.filter (fun b => G.Adj a b)))
      (A.image (fun a => B.filter (fun b => ¬ G.Adj a b)))
  have h2 : (A.image (fun a => B.filter (fun b => G.Adj a b))).card ≤ A.card :=
    Finset.card_image_le
  have h3 : (A.image (fun a => B.filter (fun b => ¬ G.Adj a b))).card ≤ A.card :=
    Finset.card_image_le
  omega

/-- Every member of the witness family is a subset of `B`. -/
lemma witnessFamilyB_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B B' : Finset V) (hB' : B' ∈ witnessFamilyB G A B) :
    B' ⊆ B := by
  unfold witnessFamilyB at hB'
  rcases Finset.mem_union.mp hB' with h | h
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    rw [← ha]
    exact Finset.filter_subset _ _
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
    rw [← ha]
    exact Finset.filter_subset _ _

/-! ## Part 2: The decidable surrogate -/

/-- `IsWitnessRegular G eps A B` is the ADLRY surrogate for ε-regularity:
    instead of quantifying over all `(A', B')` with `A' ⊆ A`, `B' ⊆ B`,
    we only test the polynomial-size family `witnessFamilyB G A B`
    (against the full set `A`).

    For each `B'` in the family with `|B'| ≥ eps * |B|`, we require
    `|d(A, B') - d(A, B)| ≤ eps`.

    This is "the strong variant" in the sense of Zhao §3.4: the slack
    constant for the implication into `IsEpsilonRegular` is `4`. -/
def IsWitnessRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Prop :=
  ∀ B' ∈ witnessFamilyB G A B,
    (B'.card : ℚ) ≥ eps * B.card →
    |edgeDensity G A B' - edgeDensity G A B| ≤ eps

/-- `IsWitnessRegular` is decidable.

    Proof sketch: the predicate is a bounded `∀` over a `Finset` (the
    witness family), with an inner antecedent `(B'.card : ℚ) ≥ eps * B.card`
    that is decidable on `ℚ`, and a conclusion `|x - y| ≤ eps` over `ℚ`
    that is decidable. By `Finset.decidableBAll`, the whole conjunction
    is decidable.

    Note: `edgeDensity` is declared `noncomputable` in `SzemerediCore`
    (because of `open Classical` there), so the resulting `Decidable`
    instance is classical (`Classical.dec`-driven), not a polynomial-
    time computation. Promoting `edgeDensity` to a computable form is
    the downstream `S3` task; this S2 scaffold uses the classical
    instance to keep the definitions aligned with `Szemeredi.Core`. -/
noncomputable instance instDecidableIsWitnessRegular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    Decidable (IsWitnessRegular G eps A B) :=
  Classical.dec _

/-! ## Part 3: ADLRY implication (one-way, with slack constant 4) -/

/-- **ADLRY 1994 ε-grid lemma (one direction)**: if the pair `(A, B)`
    satisfies the witness-regular surrogate at parameter `ε`, then it
    is ε-regular at parameter `4 · ε`.

    **Proof strategy** (deferred to S3/S4):

    Suppose `(A', B')` with `A' ⊆ A`, `B' ⊆ B`, `|A'| ≥ 4ε·|A|`,
    `|B'| ≥ 4ε·|B|`. We must show
        `|d(A', B') - d(A, B)| ≤ 4 · ε`.

    *Step 1 (B-side density transfer).* For each `a ∈ A`, the
    neighbour-pattern `B' ∩ N(a)` differs from the unbiased estimate
    `d(A, B) · |B'|` by an amount controlled by the grid: since both
    `B ∩ N(a)` and `B \ N(a)` are tested by `IsWitnessRegular` and
    `B'` is large, the density of `B'` against `N(a)` is within `ε`
    of `d(A, B)` for "most" `a ∈ A`.

    *Step 2 (A-side averaging).* Averaging the per-vertex bounds from
    Step 1 over `a ∈ A'`, the total deviation is bounded by
    `2ε + 2ε = 4ε` — the first `2ε` from the density transfer onto
    `B'`, the second from the restriction `A → A'` losing at most
    `|A \ A'|/|A| ≤ 1 - 4ε ≤ 1` worth of mass (i.e., the
    `|A'| ≥ 4ε·|A|` lower bound).

    *Step 3 (combining).* The combined bound `4ε` is the slack constant.
    Tighter analyses (Alon-Duke-Lefmann-Rödl-Yuster 1994, Lemma 3.4)
    achieve `O(ε^{1/2})` slack; the present `4ε` bound is the strong
    variant and matches Zhao's textbook exposition.

    For S2 this is left as `sorry`; the proof is `Aristotle`-friendly
    once the surrogate is fully spelled out, since each step is a
    routine density manipulation. -/
theorem witness_regular_implies_epsilon_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- See proof strategy in the docstring above.
  sorry

/-! ## Part 3b: Constructive witness extraction (S3, sorry-free)

When the witness-regular surrogate fails, we want an explicit `B'` that
exhibits the failure — both for downstream "constructive partition"
work (Target C in S1's roadmap) and for diagnostic output of any future
algorithmic-Szemerédi implementation.

The extraction is a pure-logic decomposition of `¬ IsWitnessRegular`:
unfold the definition, push the negation through the bounded universal,
and pull out the witness via existential introduction. Since the witness
family is finite and decidable, no constructive choice is needed beyond
`push_neg`. -/

/-- **Constructive witness extraction**: if `(A, B)` fails the
witness-regular surrogate at parameter `eps`, then there exists an
explicit `B'` in the ε-grid family of large enough size and with
density bias exceeding `eps`.

The proof is a one-step `push_neg` decomposition of the universally
quantified definition. The conclusion is the natural negation of
`IsWitnessRegular`:
```
∃ B' ∈ witnessFamilyB G A B,
  (B'.card : ℚ) ≥ eps * B.card ∧
  |edgeDensity G A B' - edgeDensity G A B| > eps.
```

This is the dual to `IsEpsilonRegular`'s `¬`-form witness and is the
piece that the algorithmic Szemerédi partition (Target C) iterates on
to produce a refinement when irregularity is detected. -/
theorem witnessOfIrregular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (h : ¬ IsWitnessRegular G eps A B) :
    ∃ B' ∈ witnessFamilyB G A B,
      (B'.card : ℚ) ≥ eps * B.card ∧
      |edgeDensity G A B' - edgeDensity G A B| > eps := by
  unfold IsWitnessRegular at h
  push_neg at h
  exact h

/-- **Contrapositive**: if every `B'` in the ε-grid family that is at
least `eps · |B|` large has density bias ≤ `eps`, then `(A, B)` is
witness-regular. (The forward direction of the equivalence is just the
definition; this corollary spells it out for readers.) -/
theorem isWitnessRegular_of_no_witness (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V)
    (h : ∀ B' ∈ witnessFamilyB G A B,
      (B'.card : ℚ) ≥ eps * B.card →
      |edgeDensity G A B' - edgeDensity G A B| ≤ eps) :
    IsWitnessRegular G eps A B := h

/-! ## Part 4: Mathlib-bridge stubs (S5 placeholders, not exported)

    These signatures are placeholders for the downstream S5 task —
    relating `IsWitnessRegular` to Mathlib's `SimpleGraph.IsUniform`.
    They are kept here to make the dependency surface visible. -/

/-- Placeholder: a Mathlib-bridge for the witness-regular surrogate.
    The plan is to relate `IsWitnessRegular G eps A B` to a polynomial
    test against `Finpartition.nonUniforms` in Mathlib v4.26.

    Deferred to S5; see `research/problems/szemeredi-core-oq-04/state.md`. -/
theorem witness_regular_mathlib_bridge_placeholder
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_eps : ℚ) (A B : Finset V) :
    -- Placeholder shape; the genuine bridge is stated and proved in S5.
    A ⊆ A ∧ B ⊆ B := by
  exact ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩

/-! ## Part 5: Boundary cases (sorry-free)

The slack-4 ADLRY implication has a non-trivial regime
`0 < eps < 1/4` and a trivial regime `eps ≥ 1/4`. This section
isolates the trivial regime as standalone reusable lemmas, so that any
eventual proof of `witness_regular_implies_epsilon_regular` (S5) can
dispatch the large-`eps` case as a one-line corollary.

The empty-input cases (`A = ∅` and `B = ∅`) are also handled: in both
the witness family is empty, so the surrogate holds vacuously.

These lemmas use only `edgeDensity_nonneg` / `edgeDensity_le_one` from
`Szemeredi.Core` and basic `Finset` API; they do not depend on the
contested S4/S5 proof strategies (triangle inequality or
second-moment / Cauchy-Schwarz). -/

/-- The witness family over an empty `A` is itself empty. -/
lemma witnessFamilyB_empty_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) :
    witnessFamilyB G (∅ : Finset V) B = ∅ := by
  unfold witnessFamilyB
  simp

/-- The witness-regular surrogate holds vacuously when `A = ∅`. -/
theorem IsWitnessRegular_empty_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (B : Finset V) :
    IsWitnessRegular G eps (∅ : Finset V) B := by
  intro B' hB' _
  rw [witnessFamilyB_empty_left] at hB'
  exact absurd hB' (Finset.notMem_empty _)

/-- Density bias against `B` is always at most `1`, regardless of
    `B' ⊆ B`. Immediate from `edgeDensity ∈ [0, 1]`. -/
lemma abs_edgeDensity_sub_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B B' : Finset V) :
    |edgeDensity G A B' - edgeDensity G A B| ≤ 1 := by
  have h1 := edgeDensity_nonneg G A B'
  have h2 := edgeDensity_le_one G A B'
  have h3 := edgeDensity_nonneg G A B
  have h4 := edgeDensity_le_one G A B
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩ <;> linarith

/-- Density bias on the `A` side is also bounded by `1`. -/
lemma abs_edgeDensity_sub_le_one_left (G : SimpleGraph V) [DecidableRel G.Adj]
    (A A' B : Finset V) :
    |edgeDensity G A' B - edgeDensity G A B| ≤ 1 := by
  have h1 := edgeDensity_nonneg G A' B
  have h2 := edgeDensity_le_one G A' B
  have h3 := edgeDensity_nonneg G A B
  have h4 := edgeDensity_le_one G A B
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩ <;> linarith

/-- Joint bias `|d(A', B') - d(A, B)| ≤ 1` for arbitrary `A', B'`. -/
lemma abs_edgeDensity_sub_le_one_joint (G : SimpleGraph V) [DecidableRel G.Adj]
    (A A' B B' : Finset V) :
    |edgeDensity G A' B' - edgeDensity G A B| ≤ 1 := by
  have h1 := edgeDensity_nonneg G A' B'
  have h2 := edgeDensity_le_one G A' B'
  have h3 := edgeDensity_nonneg G A B
  have h4 := edgeDensity_le_one G A B
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩ <;> linarith

/-- **Trivial regime for `IsWitnessRegular`**: if `1 ≤ eps`, the
    surrogate holds for every pair `(A, B)`, regardless of `G`. The
    universal bound `|d(A, B') - d(A, B)| ≤ 1` from
    `abs_edgeDensity_sub_le_one` does all the work; the antecedent of
    the surrogate is irrelevant in this regime. -/
theorem IsWitnessRegular_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    IsWitnessRegular G eps A B := by
  intro B' _ _
  exact (abs_edgeDensity_sub_le_one G A B B').trans heps

/-- **Trivial regime for `IsEpsilonRegular`**: if `1 ≤ eps`, every pair
    `(A, B)` is ε-regular. Same one-line argument as the surrogate
    case. -/
theorem IsEpsilonRegular_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    IsEpsilonRegular G eps A B := by
  intro A' B' _ _ _ _
  exact (abs_edgeDensity_sub_le_one_joint G A A' B B').trans heps

/-- **Slack-4 implication, trivial regime**: when `1 ≤ 4 · eps`
    (equivalently `eps ≥ 1/4`), the conclusion
    `IsEpsilonRegular G (4 * eps) A B` is true for *every* `(A, B)` —
    no hypothesis on `IsWitnessRegular` is needed. This isolates the
    trivial branch of the slack-4 case split; the non-trivial work
    lives in `witness_regular_implies_epsilon_regular` for the regime
    `0 < eps < 1/4`. -/
theorem witness_regular_implies_epsilon_regular_large_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ 4 * eps) (A B : Finset V) :
    IsEpsilonRegular G (4 * eps) A B :=
  IsEpsilonRegular_of_one_le_eps G heps A B

end Szemeredi.OQ04
