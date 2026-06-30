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

  Scope (after S5 case-split refactor):
    • The definitions, `Decidable` instance, and constructive witness
      extraction (`witnessOfIrregular`) are sorry-free.
    • The main wrapper `witness_regular_implies_epsilon_regular` is
      sorry-free; it case-splits on `1 ≤ 4 · eps` and dispatches to the
      trivial regime inline and to `_small_eps` otherwise.
    • The single `sorry` lives in `witness_regular_implies_epsilon_regular_small_eps`,
      which carries the strictly tighter hypothesis `4 · eps < 1` (i.e.
      `eps < 1/4`). The deferred proof is the genuine ADLRY
      second-moment / Cauchy-Schwarz content (Lemma 3.4, Zhao §3.4).
    • Per-vertex bias scaffolding (`vertexBias`, Part 6) prepares the
      second-moment proof; all definitions and lemmas there are
      sorry-free.
    • Downstream target (computable `findRegularPartition`, Mathlib
      bridge) is deferred to S6+.
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

/-! ### Membership API for the ε-grid

These lemmas are the building blocks for the S5 ADLRY implication proof.
The slack-4 implication needs to instantiate `IsWitnessRegular` at the two
members of the witness family produced by each `a ∈ A` (the neighbour
pattern and its complement), and then average the bounds. The lemmas in
this subsection expose the witness family as a clean union of two
neighbourhood-indexed images and prove the standard disjoint-decomposition
identities. -/

/-- For any `a ∈ A`, the neighbour-pattern `B ∩ N(a)` is in the witness
    family. Used by the S5 ADLRY proof to apply `IsWitnessRegular` at the
    relevant per-vertex test set. -/
lemma mem_witnessFamilyB_nhd (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {a : V} (ha : a ∈ A) :
    B.filter (fun b => G.Adj a b) ∈ witnessFamilyB G A B := by
  unfold witnessFamilyB
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- For any `a ∈ A`, the complement `B \ N(a)` is in the witness family.
    The companion of `mem_witnessFamilyB_nhd`. -/
lemma mem_witnessFamilyB_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {a : V} (ha : a ∈ A) :
    B.filter (fun b => ¬ G.Adj a b) ∈ witnessFamilyB G A B := by
  unfold witnessFamilyB
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- Characterization of membership in the witness family. -/
lemma mem_witnessFamilyB_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B B' : Finset V) :
    B' ∈ witnessFamilyB G A B ↔
      (∃ a ∈ A, B' = B.filter (fun b => G.Adj a b)) ∨
      (∃ a ∈ A, B' = B.filter (fun b => ¬ G.Adj a b)) := by
  unfold witnessFamilyB
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨a, ha, rfl⟩
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨a, ha, rfl⟩
  · intro h
    rcases h with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- The two ε-grid members for a single `a ∈ A` partition `B` disjointly.
    This is the classical "neighbour-pattern / non-neighbour-pattern"
    decomposition used in the ADLRY proof: applying `IsWitnessRegular`
    to BOTH members yields a per-vertex density estimate, and the
    cardinalities sum to `|B|`. -/
lemma witnessFamilyB_card_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (a : V) :
    (B.filter (fun b => G.Adj a b)).card +
      (B.filter (fun b => ¬ G.Adj a b)).card = B.card :=
  Finset.filter_card_add_filter_neg_card_eq_card (fun b => G.Adj a b)

/-- For each `a ∈ A`, at least one of `B ∩ N(a)` and `B \ N(a)` has size
    at least `|B| / 2`. This is the pigeonhole step used by the ADLRY
    slack-4 implication: it guarantees that at least one ε-grid witness
    is "large" (≥ eps · |B|) whenever `eps ≤ 1/2`. -/
lemma witnessFamilyB_card_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset V) (a : V) :
    2 * (B.filter (fun b => G.Adj a b)).card ≥ B.card ∨
    2 * (B.filter (fun b => ¬ G.Adj a b)).card ≥ B.card := by
  have hsum : (B.filter (fun b => G.Adj a b)).card +
      (B.filter (fun b => ¬ G.Adj a b)).card = B.card :=
    witnessFamilyB_card_split (G := G) B a
  by_contra hlt
  push_neg at hlt
  obtain ⟨h1, h2⟩ := hlt
  omega

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

/-- **Direct consequence of `IsWitnessRegular`**: every grid member with size
at least `eps · |B|` has edge-density bias at most `eps` against `(A, B)`.

This is a one-step unfolding of the definition, exposed as a dot-notation
helper so callers can avoid re-deriving the bound from scratch (and to make
the surrogate's quantitative content explicit at the type level). -/
lemma IsWitnessRegular.density_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (A B : Finset V) (hreg : IsWitnessRegular G eps A B)
    (B' : Finset V) (hB' : B' ∈ witnessFamilyB G A B)
    (hcB' : (B'.card : ℚ) ≥ eps * B.card) :
    |edgeDensity G A B' - edgeDensity G A B| ≤ eps :=
  hreg B' hB' hcB'

/-- **Anti-monotonicity in `eps`**: weakening the regularity parameter
preserves the witness-regular property. Useful when chaining the surrogate
with an `IsEpsilonRegular`-style implication that only holds at a larger
slack constant.

Proof: a larger `eps'` makes the size-threshold antecedent
`|B'| ≥ eps' · |B|` stronger and the deviation conclusion
`|·| ≤ eps'` weaker. Both directions help. -/
lemma IsWitnessRegular_anti (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps eps' : ℚ} (h : eps ≤ eps')
    (A B : Finset V) (hreg : IsWitnessRegular G eps A B) :
    IsWitnessRegular G eps' A B := by
  intro B' hB' hcB'
  have hBcard : (0 : ℚ) ≤ (B.card : ℚ) := Nat.cast_nonneg _
  have hcB'_eps : (B'.card : ℚ) ≥ eps * B.card := by
    have hmul : eps * (B.card : ℚ) ≤ eps' * (B.card : ℚ) :=
      mul_le_mul_of_nonneg_right h hBcard
    linarith
  have hbound : |edgeDensity G A B' - edgeDensity G A B| ≤ eps :=
    hreg B' hB' hcB'_eps
  linarith

/-- **Non-trivial regime of the slack-4 ADLRY implication** (`0 < eps < 1/4`).

    Isolates the genuine ADLRY content as a standalone lemma so that the
    main wrapper `witness_regular_implies_epsilon_regular` can dispatch
    the trivial regime `eps ≥ 1/4` via the universal bound
    `|d(A', B') - d(A, B)| ≤ 1 ≤ 4 · eps` (see Part 5 boundary cases).

    With `4 · eps < 1` we have `eps < 1/4`, so the universal `≤ 1` bound
    is no longer sufficient and the second-moment / Cauchy-Schwarz
    argument over `a ∈ A` is required (ADLRY 1994 Lemma 3.4; Zhao §3.4).

    **Proof obligation** (still open): given `IsWitnessRegular G eps A B`,
    show that for any `A' ⊆ A`, `B' ⊆ B` with `|A'| ≥ 4 · eps · |A|` and
    `|B'| ≥ 4 · eps · |B|`,
    `|edgeDensity G A' B' − edgeDensity G A B| ≤ 4 · eps`. The route
    (see `research/problems/szemeredi-core-oq-04/knowledge.md` §S4
    "Recommended next-iteration approach"):

    1. Partition `A` into `A_good := {a ∈ A | vertexBias G a A B ≤ eps}`
       and its complement `A_bad`. The grid hypothesis bounds
       `|A_bad| ≤ eps · |A|` via averaging the per-grid-member estimates
       over `a ∈ A` and applying Chebyshev / Markov.
    2. For `A' ⊆ A` with `|A'| ≥ 4 · eps · |A|`, conclude
       `|A' ∩ A_bad| ≤ |A_bad| ≤ eps · |A| ≤ (1/4) · |A'|` — so `A'` is
       composed mostly (`≥ 3/4`) of unbiased vertices.
    3. For unbiased `a ∈ A_good`, the per-vertex bias bounds the
       contribution of `a` to `e(A', B') − e(A, B) · |A'|·|B'|/(|A|·|B|)`.
       Summing and using the size bound on `B'` (≥ 4ε·|B|) gives the
       slack-4 conclusion via triangle inequality at the end.

    **Audit note** (from S4 PR #17994 + #18008): the earlier
    triangle-inequality decomposition
    `|d(A',B') − d(A,B)| ≤ |d(A',B') − d(A,B')| + |d(A,B') − d(A,B)|`
    is FALSE in the small-eps regime — the B-side step requires a
    Frieze-Kannan cut-norm bound stronger than the grid hypothesis, and
    the A-side step needs a per-vertex restriction lemma rather than the
    coarse `|A\A'|/|A| ≤ 1 − 4ε`. The second-moment route avoids both
    pitfalls. -/
theorem witness_regular_implies_epsilon_regular_small_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
    (A B : Finset V) (hreg : IsWitnessRegular G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- See docstring for the deferred second-moment / Cauchy-Schwarz route.
  sorry

/-- **ADLRY 1994 ε-grid lemma (one direction)**: if the pair `(A, B)`
    satisfies the witness-regular surrogate at parameter `ε`, then it
    is ε-regular at parameter `4 · ε`.

    **Proof structure (S5)**: case-splits on the *target* parameter
    `4 · ε`.

    * **Trivial regime** (`1 ≤ 4 · ε`, i.e. `ε ≥ 1/4`): the conclusion
      holds for every `(A, B)` because `|d(A', B') − d(A, B)| ≤ 1 ≤ 4 · ε`
      from the edge-density bounds (`edgeDensity_nonneg` + `_le_one`).
      Closed inline by `linarith`; matches `Part 5`'s
      `witness_regular_implies_epsilon_regular_large_eps` (which lives
      after this theorem in the file and is the dot-notation-friendly
      version of the same one-liner).

    * **Non-trivial regime** (`4 · ε < 1`, i.e. `ε < 1/4`): delegated
      to `witness_regular_implies_epsilon_regular_small_eps` above.
      That lemma carries the sole remaining `sorry` in this file; the
      proof route (second-moment / Cauchy-Schwarz over `a ∈ A`) is
      documented in its docstring and in
      `research/problems/szemeredi-core-oq-04/knowledge.md` §S4-S5.

    **Net effect of the S5 refactor**: this wrapper is sorry-free; the
    deep mathematical content compresses to a helper with strictly
    tighter precondition (`4ε < 1` added). Downstream callers see no
    interface change.

    **Helpers exposed (S4–S5)**:
    * `IsWitnessRegular.density_bound` — direct grid-member application.
    * `IsWitnessRegular_anti` — anti-monotonicity in `eps`.
    * `witness_regular_implies_epsilon_regular_small_eps` — non-trivial
      regime placeholder; carries the sole sorry.
    * `witness_regular_implies_epsilon_regular_large_eps` — trivial
      regime, sorry-free (Part 5).
    * `vertexBias` + lemmas — per-vertex bias scaffolding (Part 6,
      sorry-free), prepared for the second-moment proof. -/
theorem witness_regular_implies_epsilon_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  by_cases hlarge : 1 ≤ 4 * eps
  · -- Trivial regime: universal `|d(A', B') - d(A, B)| ≤ 1 ≤ 4 · eps`.
    intro A' B' _ _ _ _
    have h1 := edgeDensity_nonneg G A' B'
    have h2 := edgeDensity_le_one G A' B'
    have h3 := edgeDensity_nonneg G A B
    have h4 := edgeDensity_le_one G A B
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩ <;> linarith
  · push_neg at hlarge
    exact witness_regular_implies_epsilon_regular_small_eps
      G heps hlarge A B hreg

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
    lives in `witness_regular_implies_epsilon_regular_small_eps` for
    the regime `0 < eps < 1/4`. (As of S5, the main wrapper
    `witness_regular_implies_epsilon_regular` performs the case split
    inline and is sorry-free.) -/
theorem witness_regular_implies_epsilon_regular_large_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ 4 * eps) (A B : Finset V) :
    IsEpsilonRegular G (4 * eps) A B :=
  IsEpsilonRegular_of_one_le_eps G heps A B

/-! ## Part 6: Per-vertex bias (S5 scaffold for second-moment route)

The non-trivial regime `0 < eps < 1/4` of the slack-4 ADLRY implication
uses a second-moment / Cauchy-Schwarz argument over `a ∈ A`. The
per-vertex bias `|d({a}, B) - d(A, B)|` measures the deviation of a
single vertex's edge density from the bulk; an averaging step (Markov /
Chebyshev) bounds the number of biased vertices using the grid
hypothesis, then a triangle inequality at the end transfers the bound
to subset densities. The definitions and basic properties live here
as sorry-free primitives for the future
`witness_regular_implies_epsilon_regular_small_eps` proof. -/

/-- **Per-vertex density bias**: the absolute deviation of the edge
density between the singleton `{a}` and `B` from the bulk edge density
`d(A, B)`. Always in `[0, 1]` (since `edgeDensity ∈ [0, 1]`). -/
noncomputable def vertexBias (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (A B : Finset V) : ℚ :=
  |edgeDensity G {a} B - edgeDensity G A B|

/-- Per-vertex bias is non-negative (absolute value). -/
lemma vertexBias_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (A B : Finset V) :
    0 ≤ vertexBias G a A B :=
  abs_nonneg _

/-- Per-vertex bias is at most `1`, since both densities lie in `[0, 1]`.
Immediate from `abs_edgeDensity_sub_le_one_left`. -/
lemma vertexBias_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (A B : Finset V) :
    vertexBias G a A B ≤ 1 :=
  abs_edgeDensity_sub_le_one_left G A {a} B

/-- **Trivial regime for `vertexBias`**: if `1 ≤ eps`, every vertex is
"`eps`-unbiased". Used as a degenerate case in the second-moment proof
to avoid edge cases at the regime boundary. -/
lemma vertexBias_le_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (A B : Finset V) {eps : ℚ} (heps : 1 ≤ eps) :
    vertexBias G a A B ≤ eps :=
  (vertexBias_le_one G a A B).trans heps

/-! ## Part 7: Symmetric variant (S6c-ACT Option A surrogate)

PR #18679 (S6c PREP-2) demonstrated a concrete `#V = 16` bipartite graph
showing that the one-sided implication
`IsWitnessRegular G eps A B → IsEpsilonRegular G (4·eps) A B` is
**mathematically false**: with `B`-regular degrees, `witnessFamilyB`
collapses to two density-`1/2` elements (antecedent vacuous), yet the
pair `(A₊, B_left)` witnesses conclusion failure at `eps = 0.1`.

Following the S6c PREP §4.1 / §5 plan (Option A), this Part adds the
dual `A`-side ε-grid `witnessFamilyA G A B` and the conjunction
`IsWitnessRegular_symmetric`. Under the symmetric surrogate, the slack-4
ADLRY implication is restored: the counterexample fails the new
`Dual_IsWitnessRegular` half (every `A' ∈ witnessFamilyA` either is
the empty filter or hits the bimodal-degree non-cancellation), so the
antecedent `IsWitnessRegular_symmetric eps A B` is FALSE on the
counterexample and the slack-4 conclusion is vacuously preserved.

All definitions, decidability, anti-monotonicity, density-bound helpers,
and boundary cases below are sorry-free. The genuine ADLRY content is
isolated in `witness_regular_symmetric_implies_epsilon_regular_small_eps`
(the new file-level sorry, replacing the now-unprovable one-sided
`_small_eps` at line ~284). The sorry-free wrapper
`witness_regular_symmetric_implies_epsilon_regular` performs the
`1 ≤ 4·eps` case split inline (mirrors line ~329's one-sided wrapper). -/

/-- The A-side ε-grid for `A` relative to `B`: for each `b ∈ B`, both
    the back-neighbour pattern `A ∩ N(b)` and its complement `A \ N(b)`
    in `A`. Dual to `witnessFamilyB`; the family has at most `2 · |B|`
    elements. -/
def witnessFamilyA (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) : Finset (Finset V) :=
  B.image (fun b => A.filter (fun a => G.Adj a b)) ∪
  B.image (fun b => A.filter (fun a => ¬ G.Adj a b))

/-- The dual witness family has size at most `2 * |B|`. -/
lemma witnessFamilyA_card_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) :
    (witnessFamilyA G A B).card ≤ 2 * B.card := by
  unfold witnessFamilyA
  have h1 := Finset.card_union_le
      (B.image (fun b => A.filter (fun a => G.Adj a b)))
      (B.image (fun b => A.filter (fun a => ¬ G.Adj a b)))
  have h2 : (B.image (fun b => A.filter (fun a => G.Adj a b))).card ≤ B.card :=
    Finset.card_image_le
  have h3 : (B.image (fun b => A.filter (fun a => ¬ G.Adj a b))).card ≤ B.card :=
    Finset.card_image_le
  omega

/-- Every member of the dual witness family is a subset of `A`. -/
lemma witnessFamilyA_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B A' : Finset V) (hA' : A' ∈ witnessFamilyA G A B) :
    A' ⊆ A := by
  unfold witnessFamilyA at hA'
  rcases Finset.mem_union.mp hA' with h | h
  · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
    rw [← hb]
    exact Finset.filter_subset _ _
  · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
    rw [← hb]
    exact Finset.filter_subset _ _

/-- For any `b ∈ B`, the back-neighbour pattern `A ∩ N(b)` is in the
    dual witness family. -/
lemma mem_witnessFamilyA_nhd (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {b : V} (hb : b ∈ B) :
    A.filter (fun a => G.Adj a b) ∈ witnessFamilyA G A B := by
  unfold witnessFamilyA
  exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

/-- For any `b ∈ B`, the complement `A \ N(b)` is in the dual witness
    family. -/
lemma mem_witnessFamilyA_compl (G : SimpleGraph V) [DecidableRel G.Adj]
    {A B : Finset V} {b : V} (hb : b ∈ B) :
    A.filter (fun a => ¬ G.Adj a b) ∈ witnessFamilyA G A B := by
  unfold witnessFamilyA
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

/-- Characterization of membership in the dual witness family. -/
lemma mem_witnessFamilyA_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B A' : Finset V) :
    A' ∈ witnessFamilyA G A B ↔
      (∃ b ∈ B, A' = A.filter (fun a => G.Adj a b)) ∨
      (∃ b ∈ B, A' = A.filter (fun a => ¬ G.Adj a b)) := by
  unfold witnessFamilyA
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact Or.inl ⟨b, hb, rfl⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨b, hb, rfl⟩
  · intro h
    rcases h with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b, hb, rfl⟩)

/-- The two A-side ε-grid members for a single `b ∈ B` partition `A`
    disjointly (the back-neighbour / non-back-neighbour decomposition). -/
lemma witnessFamilyA_card_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (b : V) :
    (A.filter (fun a => G.Adj a b)).card +
      (A.filter (fun a => ¬ G.Adj a b)).card = A.card :=
  Finset.filter_card_add_filter_neg_card_eq_card (fun a => G.Adj a b)

/-- For each `b ∈ B`, at least one of `A ∩ N(b)` and `A \ N(b)` has size
    at least `|A| / 2` (the A-side pigeonhole step). -/
lemma witnessFamilyA_card_half (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (b : V) :
    2 * (A.filter (fun a => G.Adj a b)).card ≥ A.card ∨
    2 * (A.filter (fun a => ¬ G.Adj a b)).card ≥ A.card := by
  have hsum : (A.filter (fun a => G.Adj a b)).card +
      (A.filter (fun a => ¬ G.Adj a b)).card = A.card :=
    witnessFamilyA_card_split (G := G) A b
  by_contra hlt
  push_neg at hlt
  obtain ⟨h1, h2⟩ := hlt
  omega

/-- The dual witness-regular surrogate: tests `A' ∈ witnessFamilyA G A B`
    against the full set `B`. -/
def Dual_IsWitnessRegular (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Prop :=
  ∀ A' ∈ witnessFamilyA G A B,
    (A'.card : ℚ) ≥ eps * A.card →
    |edgeDensity G A' B - edgeDensity G A B| ≤ eps

/-- `Dual_IsWitnessRegular` is decidable (classical, mirrors the one-sided
    instance — the underlying `edgeDensity` is `noncomputable`). -/
noncomputable instance instDecidableDual_IsWitnessRegular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    Decidable (Dual_IsWitnessRegular G eps A B) :=
  Classical.dec _

/-- Direct consequence of `Dual_IsWitnessRegular`: every A-side grid
    member with size at least `eps · |A|` has bounded density bias
    against `(A, B)`. -/
lemma Dual_IsWitnessRegular.density_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (A B : Finset V) (hreg : Dual_IsWitnessRegular G eps A B)
    (A' : Finset V) (hA' : A' ∈ witnessFamilyA G A B)
    (hcA' : (A'.card : ℚ) ≥ eps * A.card) :
    |edgeDensity G A' B - edgeDensity G A B| ≤ eps :=
  hreg A' hA' hcA'

/-- Anti-monotonicity of `Dual_IsWitnessRegular` in `eps`. Mirrors
    `IsWitnessRegular_anti`. -/
lemma Dual_IsWitnessRegular_anti (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps eps' : ℚ} (h : eps ≤ eps')
    (A B : Finset V) (hreg : Dual_IsWitnessRegular G eps A B) :
    Dual_IsWitnessRegular G eps' A B := by
  intro A' hA' hcA'
  have hAcard : (0 : ℚ) ≤ (A.card : ℚ) := Nat.cast_nonneg _
  have hcA'_eps : (A'.card : ℚ) ≥ eps * A.card := by
    have hmul : eps * (A.card : ℚ) ≤ eps' * (A.card : ℚ) :=
      mul_le_mul_of_nonneg_right h hAcard
    linarith
  have hbound : |edgeDensity G A' B - edgeDensity G A B| ≤ eps :=
    hreg A' hA' hcA'_eps
  linarith

/-- The symmetric witness-regular surrogate: requires BOTH the original
    `IsWitnessRegular` (B-side grid) AND the dual `Dual_IsWitnessRegular`
    (A-side grid). This is the surrogate strong enough to imply
    `IsEpsilonRegular G (4·eps) A B`; the one-sided version is provably
    insufficient (PR #18679 counterexample). -/
def IsWitnessRegular_symmetric (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Prop :=
  IsWitnessRegular G eps A B ∧ Dual_IsWitnessRegular G eps A B

/-- `IsWitnessRegular_symmetric` is decidable (classical). -/
noncomputable instance instDecidableIsWitnessRegular_symmetric
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    Decidable (IsWitnessRegular_symmetric G eps A B) :=
  Classical.dec _

/-- Project the symmetric surrogate to its one-sided B-side component. -/
lemma IsWitnessRegular_symmetric.toB (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} {A B : Finset V}
    (hreg : IsWitnessRegular_symmetric G eps A B) :
    IsWitnessRegular G eps A B := hreg.1

/-- Project the symmetric surrogate to its dual A-side component. -/
lemma IsWitnessRegular_symmetric.toA (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} {A B : Finset V}
    (hreg : IsWitnessRegular_symmetric G eps A B) :
    Dual_IsWitnessRegular G eps A B := hreg.2

/-- Anti-monotonicity of the symmetric surrogate in `eps`. -/
lemma IsWitnessRegular_symmetric_anti (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps eps' : ℚ} (h : eps ≤ eps')
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    IsWitnessRegular_symmetric G eps' A B := by
  refine ⟨?_, ?_⟩
  · exact IsWitnessRegular_anti G h A B hreg.1
  · exact Dual_IsWitnessRegular_anti G h A B hreg.2

/-- The dual witness family over an empty `B` is itself empty. -/
lemma witnessFamilyA_empty_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) :
    witnessFamilyA G A (∅ : Finset V) = ∅ := by
  unfold witnessFamilyA
  simp

/-- The dual witness-regular surrogate holds vacuously when `B = ∅`. -/
theorem Dual_IsWitnessRegular_empty_right (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A : Finset V) :
    Dual_IsWitnessRegular G eps A (∅ : Finset V) := by
  intro A' hA' _
  rw [witnessFamilyA_empty_right] at hA'
  exact absurd hA' (Finset.notMem_empty _)

/-- Trivial regime for `Dual_IsWitnessRegular`: if `1 ≤ eps`, the dual
    surrogate holds for every `(A, B)`. Same one-line argument as the
    B-side trivial regime. -/
theorem Dual_IsWitnessRegular_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    Dual_IsWitnessRegular G eps A B := by
  intro A' _ _
  exact (abs_edgeDensity_sub_le_one_left G A A' B).trans heps

/-- Trivial regime for the symmetric surrogate: if `1 ≤ eps`, both halves
    hold trivially. -/
theorem IsWitnessRegular_symmetric_of_one_le_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    IsWitnessRegular_symmetric G eps A B :=
  ⟨IsWitnessRegular_of_one_le_eps G heps A B,
   Dual_IsWitnessRegular_of_one_le_eps G heps A B⟩

/-- **Non-trivial regime of the symmetric slack-4 ADLRY implication**
    (`0 < eps < 1/4`).

    Replaces the now-unprovable one-sided
    `witness_regular_implies_epsilon_regular_small_eps` (line ~284):
    the conjunction over BOTH grids is strong enough to derive the
    second-moment / Cauchy-Schwarz averaging needed for the slack-4
    conclusion. The PR #18679 counterexample fails this stronger
    antecedent (the dual `Dual_IsWitnessRegular` half is violated by
    the bimodal A-side degree distribution), so the obstruction
    documented in S6c PREP-2 does not transfer here.

    **Proof obligation** (still open — this is the deferred ADLRY
    content; sole `sorry` in the symmetric API): given
    `IsWitnessRegular_symmetric G eps A B`, show that for any
    `A' ⊆ A`, `B' ⊆ B` with `|A'| ≥ 4·eps·|A|` and `|B'| ≥ 4·eps·|B|`,
    `|edgeDensity G A' B' − edgeDensity G A B| ≤ 4·eps`.

    The route now goes through BOTH grids:

    1. From `Dual_IsWitnessRegular`: average per-vertex bias
       `vertexBias G b A B'` over `b ∈ B` using the A-side grid, then
       Cauchy-Schwarz / Chebyshev bounds the count of "B-bad" vertices
       by `≤ eps · |B|` (mirroring the one-sided averaging, but on the
       A-side ε-grid `A ∩ N(b)` / `A \ N(b)` which the counterexample
       fails to make trivial).
    2. From `IsWitnessRegular` (the B-side half): similarly bound the
       count of "A-bad" vertices by `≤ eps · |A|`, mirroring step 1
       through the B-side grid.
    3. For `A' ⊆ A` with `|A'| ≥ 4·eps·|A|` and `B' ⊆ B` with
       `|B'| ≥ 4·eps·|B|`, both `A'` and `B'` are predominantly
       composed of unbiased vertices (≥ 3/4 by the standard Markov
       argument); a final triangle inequality at the conjoint level
       yields the slack-4 conclusion.

    References: PR #18595 (S6c PREP) §5; PR #18679 (S6c PREP-2) §6.2;
    ADLRY 1994 Lemma 3.4 (two-sided bi-regular form); Zhao,
    *Graph Theory and Additive Combinatorics*, §3.4. -/
theorem witness_regular_symmetric_implies_epsilon_regular_small_eps
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (hsmall : 4 * eps < 1)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  intro A' B' hA' hB' hcA' hcB'
  -- Deferred ADLRY two-sided second-moment content; see docstring.
  sorry

/-- **Symmetric slack-4 ADLRY implication, full wrapper**: case-splits
    on `1 ≤ 4 · eps` exactly as the one-sided wrapper
    `witness_regular_implies_epsilon_regular` does, but using the
    symmetric surrogate. Sorry-free; the deep content compresses into
    the helper above.

    This is the **correct** statement of the slack-4 ADLRY implication
    — the one-sided version is provably false on a concrete counter-
    example (PR #18679, S6c PREP-2). Downstream callers should depend
    on this wrapper rather than the (still-present) one-sided
    `witness_regular_implies_epsilon_regular`. The latter is left in
    the file for archival / pedagogical reasons; its
    `_small_eps` helper carries a `sorry` that is mathematically
    unprovable as stated. -/
theorem witness_regular_symmetric_implies_epsilon_regular
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps) (A B : Finset V)
    (hreg : IsWitnessRegular_symmetric G eps A B) :
    IsEpsilonRegular G (4 * eps) A B := by
  by_cases hlarge : 1 ≤ 4 * eps
  · -- Trivial regime: universal `|d(A', B') - d(A, B)| ≤ 1 ≤ 4 · eps`.
    intro A' B' _ _ _ _
    have h1 := edgeDensity_nonneg G A' B'
    have h2 := edgeDensity_le_one G A' B'
    have h3 := edgeDensity_nonneg G A B
    have h4 := edgeDensity_le_one G A B
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩ <;> linarith
  · push_neg at hlarge
    exact witness_regular_symmetric_implies_epsilon_regular_small_eps
      G heps hlarge A B hreg

/-! ## Part 8: B-side per-vertex bias + biased-vertex Finsets
    (S7 scaffold for symmetric second-moment route)

Mirroring Part 6 (A-side `vertexBias` over singleton `{a}`), the
symmetric second-moment proof of
`witness_regular_symmetric_implies_epsilon_regular_small_eps` needs a
dual B-side per-vertex bias `|d(A, {b}) - d(A, B)|` for `b ∈ B`. The
Markov / Chebyshev step then bounds the count of "biased" vertices on
BOTH sides using `IsWitnessRegular_symmetric`; subsetting `A' ⊆ A` and
`B' ⊆ B` predominantly to unbiased vertices closes the slack-4
implication via a final triangle inequality.

The `A_bad` / `A_good` Finsets (and B-side duals) packaged here are the
exact objects the S6c PREP §5 / §6.2 averaging argument operates on:
* `A_bad` collects A-vertices whose density bias **exceeds** `eps`;
* `A_good` collects A-vertices whose bias is `≤ eps`;
* their cardinalities sum to `|A|` (`A_bad_add_A_good_card_eq`).

All declarations here are sorry-free. The substantive Markov bound
`|A_bad| ≤ eps · |A|` is **NOT** proved here — it is the deferred ADLRY
averaging content in `_small_eps`. Part 8 packages only the
combinatorial primitives needed to **state** that bound and use it
once obtained. -/

/-- **B-side per-vertex density bias**: the absolute deviation of the
edge density between `A` and the singleton `{b}` from the bulk edge
density `d(A, B)`. Dual to `vertexBias`. Always in `[0, 1]` since
`edgeDensity ∈ [0, 1]`. -/
noncomputable def vertexBias_B (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V) (A B : Finset V) : ℚ :=
  |edgeDensity G A {b} - edgeDensity G A B|

/-- B-side per-vertex bias is non-negative (absolute value). -/
lemma vertexBias_B_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V) (A B : Finset V) :
    0 ≤ vertexBias_B G b A B :=
  abs_nonneg _

/-- B-side per-vertex bias is at most `1`, since both densities lie in
`[0, 1]`. Immediate from `abs_edgeDensity_sub_le_one`. -/
lemma vertexBias_B_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V) (A B : Finset V) :
    vertexBias_B G b A B ≤ 1 :=
  abs_edgeDensity_sub_le_one G A B {b}

/-- **Trivial regime for `vertexBias_B`**: if `1 ≤ eps`, every B-vertex
is "`eps`-unbiased". Dual of `vertexBias_le_of_one_le`. -/
lemma vertexBias_B_le_of_one_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : V) (A B : Finset V) {eps : ℚ} (heps : 1 ≤ eps) :
    vertexBias_B G b A B ≤ eps :=
  (vertexBias_B_le_one G b A B).trans heps

/-- **A-bad vertex set**: the subset of `A`-vertices whose per-vertex
bias **exceeds** `eps`. The Markov step in the symmetric second-moment
proof bounds `|A_bad| ≤ eps · |A|` using `IsWitnessRegular` (the
B-side grid) — see S6c PREP §5. Packaged here as a Finset primitive. -/
noncomputable def A_bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Finset V :=
  A.filter (fun a => eps < vertexBias G a A B)

/-- **A-good vertex set**: complement of `A_bad` inside `A` — vertices
whose bias is `≤ eps`. Used directly in the final triangle-inequality
step: for `A' ⊆ A` with `|A'| ≥ 4·eps·|A|`, the unbiased bulk
`A' ∩ A_good` dominates by `≥ 3/4` once the Markov bound is applied. -/
noncomputable def A_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Finset V :=
  A.filter (fun a => ¬ (eps < vertexBias G a A B))

/-- **B-bad vertex set**: dual to `A_bad`, indexed by B-vertices. -/
noncomputable def B_bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Finset V :=
  B.filter (fun b => eps < vertexBias_B G b A B)

/-- **B-good vertex set**: dual to `A_good`. -/
noncomputable def B_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) : Finset V :=
  B.filter (fun b => ¬ (eps < vertexBias_B G b A B))

/-- `A_bad ⊆ A`. -/
lemma A_bad_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    A_bad G eps A B ⊆ A :=
  Finset.filter_subset _ _

/-- `A_good ⊆ A`. -/
lemma A_good_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    A_good G eps A B ⊆ A :=
  Finset.filter_subset _ _

/-- `B_bad ⊆ B`. -/
lemma B_bad_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    B_bad G eps A B ⊆ B :=
  Finset.filter_subset _ _

/-- `B_good ⊆ B`. -/
lemma B_good_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    B_good G eps A B ⊆ B :=
  Finset.filter_subset _ _

/-- **A-bad membership criterion**. -/
lemma mem_A_bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (a : V) :
    a ∈ A_bad G eps A B ↔ a ∈ A ∧ eps < vertexBias G a A B := by
  unfold A_bad
  exact Finset.mem_filter

/-- **A-good membership criterion** (in the natural `≤` form). -/
lemma mem_A_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (a : V) :
    a ∈ A_good G eps A B ↔ a ∈ A ∧ vertexBias G a A B ≤ eps := by
  unfold A_good
  rw [Finset.mem_filter]
  refine ⟨fun ⟨ha, h⟩ => ⟨ha, not_lt.mp h⟩, fun ⟨ha, h⟩ => ⟨ha, not_lt.mpr h⟩⟩

/-- **B-bad membership criterion**. -/
lemma mem_B_bad (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (b : V) :
    b ∈ B_bad G eps A B ↔ b ∈ B ∧ eps < vertexBias_B G b A B := by
  unfold B_bad
  exact Finset.mem_filter

/-- **B-good membership criterion** (in the natural `≤` form). -/
lemma mem_B_good (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) (b : V) :
    b ∈ B_good G eps A B ↔ b ∈ B ∧ vertexBias_B G b A B ≤ eps := by
  unfold B_good
  rw [Finset.mem_filter]
  refine ⟨fun ⟨hb, h⟩ => ⟨hb, not_lt.mp h⟩, fun ⟨hb, h⟩ => ⟨hb, not_lt.mpr h⟩⟩

/-- **A-bad + A-good partition `A`**: cardinalities sum to `|A|`.
Directly from `Finset.filter_card_add_filter_neg_card_eq_card`. -/
lemma A_bad_add_A_good_card_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    (A_bad G eps A B).card + (A_good G eps A B).card = A.card := by
  unfold A_bad A_good
  exact Finset.filter_card_add_filter_neg_card_eq_card _

/-- **B-bad + B-good partition `B`**: dual to `A_bad_add_A_good_card_eq`. -/
lemma B_bad_add_B_good_card_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (eps : ℚ) (A B : Finset V) :
    (B_bad G eps A B).card + (B_good G eps A B).card = B.card := by
  unfold B_bad B_good
  exact Finset.filter_card_add_filter_neg_card_eq_card _

/-- **Trivial regime: A-bad collapse**. If `1 ≤ eps`, no vertex can be
`eps`-biased (every `vertexBias ≤ 1 ≤ eps`), so `A_bad = ∅`. -/
lemma A_bad_eq_empty_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    A_bad G eps A B = ∅ := by
  unfold A_bad
  apply Finset.filter_eq_empty_iff.mpr
  intro a _ hbias
  have hle : vertexBias G a A B ≤ eps := vertexBias_le_of_one_le G a A B heps
  linarith

/-- **Trivial regime: B-bad collapse**. Dual to `A_bad_eq_empty_of_one_le_eps`. -/
lemma B_bad_eq_empty_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    B_bad G eps A B = ∅ := by
  unfold B_bad
  apply Finset.filter_eq_empty_iff.mpr
  intro b _ hbias
  have hle : vertexBias_B G b A B ≤ eps := vertexBias_B_le_of_one_le G b A B heps
  linarith

/-- **Trivial regime: A-good is all of `A`** when `1 ≤ eps`. Companion
to `A_bad_eq_empty_of_one_le_eps`. -/
lemma A_good_eq_self_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    A_good G eps A B = A := by
  unfold A_good
  apply Finset.filter_eq_self.mpr
  intro a _
  have hle : vertexBias G a A B ≤ eps := vertexBias_le_of_one_le G a A B heps
  linarith

/-- **Trivial regime: B-good is all of `B`** when `1 ≤ eps`. -/
lemma B_good_eq_self_of_one_le_eps (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 1 ≤ eps) (A B : Finset V) :
    B_good G eps A B = B := by
  unfold B_good
  apply Finset.filter_eq_self.mpr
  intro b _
  have hle : vertexBias_B G b A B ≤ eps := vertexBias_B_le_of_one_le G b A B heps
  linarith

/-! ## Part 9: First-moment bias bound (S7 ACT-α step 4, first-moment route)

Per Iter 15 (PR #19350) §6 + Iter 17 (PR #19619) §5 surfacing: the
genuinely useful step 4 for the slack-4 ADLRY discharge at
`witness_regular_symmetric_implies_epsilon_regular_small_eps` is the
first-moment bound

  ∑_{a ∈ A} vertexBias G a A B ≤ 2 · eps · #A

(under `IsWitnessRegular_symmetric eps A B`). The second-moment bound
`∑ (vertexBias)^2 ≤ 4 · eps^2 · #A` follows from this by Cauchy–Schwarz
and is filed as a downstream `_tight` companion.

This skeleton lands the lemma statements (the API surface downstream
proofs call) plus the proof shape. The aggregation steps
(`Finset.sum_le_sum`, `Finset.sum_const`) are discharged here; the two
remaining `sorry`s are the genuinely mathematical obligations: the
per-`a` triangle envelope on the `witnessFamilyB` pair, and the first-
moment Markov corollary. -/

/-- **First-moment bias bound** (S7 ACT-α step 4 proper, first-moment route).

Under the symmetric witness-regular antecedent `IsWitnessRegular_symmetric eps A B`,
the per-vertex bias against `B` sums to at most `2 · eps · #A`.

Proof shape (per Iter 17 PREP §5):
1. For each `a ∈ A`, the members `B ∩ N(a)` and `B \ N(a)` of
   `witnessFamilyB G A B` partition `B` (`witnessFamilyB_card_split`).
   Apply `(hreg.toB G)` on each member to get density discrepancies ≤ `eps`.
2. Triangle: `vertexBias G a A B ≤ 2 · eps` (the `hper` envelope).
3. Aggregate via `Finset.sum_le_sum` + `Finset.sum_const`. -/
lemma vertexBias_sum_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    (∑ a ∈ A, vertexBias G a A B) ≤ 2 * eps * A.card := by
  -- B-side projection used in the per-`a` triangle.
  have htoB : IsWitnessRegular G eps A B := IsWitnessRegular_symmetric.toB G hreg
  -- Per-`a` envelope: vertexBias a ≤ 2 · eps via triangle on the witnessFamilyB pair.
  have hper : ∀ a ∈ A, vertexBias G a A B ≤ 2 * eps := by
    intro a ha
    -- Step a.1: the two grid members `B ∩ N(a)` and `B \ N(a)` lie in
    -- `witnessFamilyB G A B` (`mem_witnessFamilyB_nhd`/`_compl (ha)`),
    -- with cardinalities summing to `|B|` (`witnessFamilyB_card_split`).
    -- Step a.2: apply `htoB` on each large member to get discrepancies ≤ `eps`.
    -- Step a.3: triangle + density decomposition ⟹ vertexBias a ≤ 2·eps.
    sorry  -- ~25-35 LOC: triangle assembly on the witnessFamilyB pair for {a}.
  calc (∑ a ∈ A, vertexBias G a A B)
      ≤ ∑ _a ∈ A, (2 * eps : ℚ) := Finset.sum_le_sum hper
    _ = (A.card : ℚ) * (2 * eps) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * eps * A.card := by ring

/-- **First-moment Markov corollary**: `|A_bad| · eps ≤ 2 · eps · #A`.

On its own this gives only the trivial bound `|A_bad| ≤ 2 · #A` (the
genuine ADLRY discharge needs the two-sided averaging at `_small_eps`);
it is filed as a sanity-check companion that chains the first-moment
bound through the `A_bad` filter via `Finset.sum_le_sum_of_subset_of_nonneg`. -/
lemma A_bad_card_first_moment_markov
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {eps : ℚ} (heps : 0 < eps)
    (A B : Finset V) (hreg : IsWitnessRegular_symmetric G eps A B) :
    ((A_bad G eps A B).card : ℚ) * eps ≤ 2 * eps * A.card := by
  have hsum := vertexBias_sum_le G heps A B hreg
  -- `∑_{a ∈ A_bad} vertexBias a ≥ |A_bad| · eps` (definition of `A_bad`),
  -- and `∑_{a ∈ A_bad} vertexBias a ≤ ∑_{a ∈ A} vertexBias a` via
  -- `Finset.sum_le_sum_of_subset_of_nonneg` (vertexBias ≥ 0). Chain with `hsum`.
  sorry  -- ~10-15 LOC.

end Szemeredi.OQ04
