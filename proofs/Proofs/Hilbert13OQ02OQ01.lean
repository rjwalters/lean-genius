/-
# Hilbert's 13th Problem — OQ-02 / OQ-01
## Discrete spaces are zero-dimensional (a concrete value for the covering dimension)

The parent file `Hilbert13OQ02.lean` defines a clean, universe-safe Lebesgue covering
dimension `covDimLE X n` (every finite open cover admits a finite open refinement of order
`≤ n+1`) and proves it is a *topological invariant*, so that the Kolmogorov–Arnold superposition
term count `2·dim(X)+1` is presentation-independent. But the only space it actually *computes*
the dimension of is a subsingleton (`covDimLE_of_subsingleton`).

This file supplies the first nontrivial computation:

> **Every discrete space has covering dimension `0`.** (`covDimLE_of_discrete`)

This is the classical fact that a discrete space is `0`-dimensional. The proof is a clean
*disjointification*: given any finite open cover `cover : Fin m → Set X`, replace each set by
its "least-index" part
`V i = { x | x ∈ cover i ∧ ∀ j, x ∈ cover j → i ≤ j }`,
i.e. `x ∈ V i` exactly when `i` is the **smallest** index whose cover set contains `x`. The `V i`
are pairwise disjoint (so the cover has order `≤ 1 = 0 + 1`), they still cover `X` (every point
has a least containing index, found via `Finset.min'`), and each `V i ⊆ cover i` (a refinement).
The single place discreteness enters is openness: `V i` is generally a finite intersection of a
cover set with complements of cover sets, which is open **only because every subset of a discrete
space is open** (`isOpen_discrete`). That is exactly why the statement fails for, e.g., `ℝⁿ`.

As corollaries we recover the parent's `covDimLE_of_subsingleton` (a subsingleton space is
discrete) and record the general monotonicity `covDimLE_of_le` in the dimension bound.

## Results (0 axioms, 0 sorries)
* `covDimLE_succ` / `covDimLE_of_le` — monotonicity of the dimension bound (`≤` version).
* `covDimLE_of_discrete` — **every discrete space is `0`-dimensional** (headline).
* `covDimLE_of_subsingleton` — recovered as a corollary (subsingleton ⟹ discrete).

## References
- Engelking, R. "Dimension Theory" (discrete spaces are zero-dimensional).
- Kolmogorov, A.N. (1957) / Sternfeld, Y. (1985) — the `2n+1` superposition term count.
-/

import Mathlib

namespace Hilbert13OQ02OQ01

variable {X : Type*} [TopologicalSpace X]

/-! ## Covering-dimension API (re-stated, self-contained — matches `Hilbert13OQ02.lean`) -/

/-- The order of a cover at a point: how many cover sets contain it. -/
noncomputable def coverOrderAt {ι : Type*} (sets : ι → Set X) (x : X) : ℕ :=
  {i | x ∈ sets i}.ncard

/-- A cover has order `≤ n + 1` if every point lies in at most `n + 1` of its sets. -/
def coverOrderAtMost {ι : Type*} (sets : ι → Set X) (n : ℕ) : Prop :=
  ∀ x : X, coverOrderAt sets x ≤ n + 1

/-- `B` refines `A` if every set of `B` sits inside some set of `A`. -/
def IsRefinement {ι₁ ι₂ : Type*} (A : ι₁ → Set X) (B : ι₂ → Set X) : Prop :=
  ∀ j : ι₂, ∃ i : ι₁, B j ⊆ A i

/-- Covering dimension `≤ n`: every finite open cover has a finite open refinement of order
    `≤ n + 1`. -/
def covDimLE (X : Type*) [TopologicalSpace X] (n : ℕ) : Prop :=
  ∀ (m : ℕ) (cover : Fin m → Set X),
    (∀ i, IsOpen (cover i)) → (∀ x : X, ∃ i, x ∈ cover i) →
    ∃ (p : ℕ) (refine : Fin p → Set X),
      (∀ j, IsOpen (refine j)) ∧
      (∀ x : X, ∃ j, x ∈ refine j) ∧
      IsRefinement cover refine ∧
      coverOrderAtMost refine n

/-! ## Part I: Monotonicity in the bound -/

/-- Covering dimension is monotone in the bound: `dim X ≤ n ⟹ dim X ≤ n + 1`. -/
theorem covDimLE_succ {n : ℕ} (h : covDimLE X n) : covDimLE X (n + 1) := by
  intro m cover hopen hcov
  obtain ⟨p, refine, hro, hrc, href, hord⟩ := h m cover hopen hcov
  exact ⟨p, refine, hro, hrc, href, fun x => Nat.le_succ_of_le (hord x)⟩

/-- General monotonicity: `dim X ≤ n` and `n ≤ N` give `dim X ≤ N`. -/
theorem covDimLE_of_le {n N : ℕ} (hnN : n ≤ N) (h : covDimLE X n) : covDimLE X N := by
  induction N, hnN using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact covDimLE_succ ih

/-! ## Part II: Discrete spaces are zero-dimensional (headline) -/

/-- **Every discrete space has covering dimension `0`.**

    Given a finite open cover `cover`, define the "least-index" refinement
    `V i = { x | x ∈ cover i ∧ ∀ j, x ∈ cover j → i ≤ j }`. The sets `V i` are pairwise disjoint
    (each point belongs to `V i` only for its least covering index `i`), they cover `X`
    (`Finset.min'` selects that least index), and `V i ⊆ cover i`. Openness of each `V i` is the
    only step that uses discreteness: every subset of a discrete space is open. -/
theorem covDimLE_of_discrete [DiscreteTopology X] : covDimLE X 0 := by
  intro m cover _ hcov
  classical
  -- The least-index disjointification of the cover.
  set V : Fin m → Set X :=
    fun i => {x | x ∈ cover i ∧ ∀ j, x ∈ cover j → i ≤ j} with hV
  refine ⟨m, V, ?_, ?_, ?_, ?_⟩
  · -- Open: every subset of a discrete space is open.
    intro i; exact isOpen_discrete (V i)
  · -- Cover: each point has a least covering index.
    intro x
    obtain ⟨i, hi⟩ := hcov x
    have hTne : (Finset.univ.filter (fun j => x ∈ cover j)).Nonempty :=
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
    refine ⟨(Finset.univ.filter (fun j => x ∈ cover j)).min' hTne, ?_, ?_⟩
    · have hmem := (Finset.univ.filter (fun j => x ∈ cover j)).min'_mem hTne
      rw [Finset.mem_filter] at hmem
      exact hmem.2
    · intro j hxj
      exact Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hxj⟩)
  · -- Refinement: `V i ⊆ cover i`.
    intro i
    exact ⟨i, fun x hx => hx.1⟩
  · -- Order `≤ 1`: the `V i` are pairwise disjoint, so each point lies in at most one.
    intro x
    by_cases hx : ∃ i, x ∈ V i
    · obtain ⟨i₀, hi₀⟩ := hx
      have hsub : {i | x ∈ V i} ⊆ {i₀} := by
        intro i hi
        rw [Set.mem_setOf_eq] at hi
        rw [Set.mem_singleton_iff]
        have h1 : i ≤ i₀ := hi.2 i₀ hi₀.1
        have h2 : i₀ ≤ i := hi₀.2 i hi.1
        exact le_antisymm h1 h2
      calc coverOrderAt V x
            = {i | x ∈ V i}.ncard := rfl
        _ ≤ ({i₀} : Set (Fin m)).ncard := Set.ncard_le_ncard hsub (Set.finite_singleton i₀)
        _ = 1 := Set.ncard_singleton i₀
    · have hempty : {i | x ∈ V i} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr (fun i hi => hx ⟨i, hi⟩)
      have : coverOrderAt V x = 0 := by rw [coverOrderAt, hempty, Set.ncard_empty]
      rw [this]; exact Nat.zero_le 1

/-! ## Part III: Corollary — subsingleton spaces (recovering the parent's base case) -/

/-- A subsingleton space is discrete: with at most one point, every subset is `∅` or `univ`,
    both of which are open in any topology. -/
theorem covDimLE_of_subsingleton [Subsingleton X] : covDimLE X 0 := by
  have hdisc : DiscreteTopology X := by
    rw [discreteTopology_iff_forall_isOpen]
    intro s
    rcases Set.eq_empty_or_nonempty s with h | ⟨a, ha⟩
    · rw [h]; exact isOpen_empty
    · have : s = Set.univ := Set.eq_univ_of_forall fun b => Subsingleton.elim b a ▸ ha
      rw [this]; exact isOpen_univ
  exact covDimLE_of_discrete

/-! ## Summary

Proved here (0 axioms, 0 sorries):
* `covDimLE_succ`, `covDimLE_of_le` — monotonicity of the covering-dimension bound.
* `covDimLE_of_discrete` — **every discrete space is zero-dimensional** (the first nontrivial,
  non-subsingleton computation in this covering-dimension framework).
* `covDimLE_of_subsingleton` — recovered as a corollary, since a subsingleton space is discrete.

The genuinely open OQ-02 (the *computational* complexity of producing a KA superposition for an
effectively-presented continuous function) remains untouched; this file only adds verified
structural facts about the dimension that controls the `2n+1` term count.
-/

end Hilbert13OQ02OQ01
