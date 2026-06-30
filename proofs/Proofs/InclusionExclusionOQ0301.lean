import Proofs.InclusionExclusionOQ03
import Mathlib.Tactic

/-
# Fast Zeta Transform Correctness: Folding the SOS Step Computes the Subset Sum

## Research Problem: inclusion-exclusion-oq-03-oq-01
(parent open question #1 of `inclusion-exclusion-oq-03`)

The parent entry defines the single-element "sum over subsets" (SOS) update step

  (ζ_a f)(S) = f(S) + f(S \ {a})   if a ∈ S,     f(S)   if a ∉ S

and proves its two pointwise laws (`zetaStep_mem`, `zetaStep_not_mem`), but stops
short of proving that *iterating* the step over every element reproduces the full
zeta transform

  (ζ f)(S) = ∑_{T ⊆ S} f(T).

This file closes that gap: the correctness theorem of the O(n·2ⁿ) fast subset-sum
dynamic program (Yates / "sum over subsets" DP), which underlies fast subset
convolution, the Björklund–Husfeldt–Kaski–Koivisto "Fourier meets Möbius"
algorithm, and many exponential-time exact algorithms.

## Main results (0 axioms, 0 sorries)
- `zetaFoldList_apply` — the **partial-sweep invariant**: after folding the step
  over a duplicate-free list `l`, the running array at `S` equals
  `∑_{T : S \ l.toFinset ⊆ T ⊆ S} f(T)` — exactly the subsets of `S` that agree
  with `S` outside the already-processed elements `l`.
- `zetaFold_eq_zetaTransform` — specializing the invariant to `l = univ.toList`
  collapses the constraint `S \ univ = ∅` and yields the full transform:
  `zetaFold f = zetaTransform f`.
- `zetaFold_apply` — the pointwise corollary `zetaFold f S = ∑_{T ⊆ S} f(T)`.
- `mobius_inverts_zetaFold` — combined with the parent's Möbius inversion, the
  fast fold is inverted by the Möbius transform: `μ (zetaFold f) = f`.

## References
- Yates (1937); Knuth, TAOCP vol. 4A §7.1.3 (the SOS DP).
- Björklund, Husfeldt, Kaski, Koivisto (2007), "Fourier Meets Möbius".
-/

set_option linter.unusedVariables false

namespace IEOQ03

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================================
-- The fold of the single-element SOS step
-- ============================================================

/-- Fold the single-element SOS step `zetaStep` over a list of elements.
    `zetaFoldList [a₁, …, aₙ] f = ζ_{a₁} (ζ_{a₂} (⋯ (ζ_{aₙ} f)))`. -/
noncomputable def zetaFoldList (l : List α) (f : SubsetFn α) : SubsetFn α :=
  l.foldr zetaStep f

/-- The fast zeta transform: fold the SOS step over *every* element of the type. -/
noncomputable def zetaFold (f : SubsetFn α) : SubsetFn α :=
  zetaFoldList Finset.univ.toList f

-- ============================================================
-- The partial-sweep invariant
-- ============================================================

/-- **Partial-sweep invariant.** After folding the SOS step over a duplicate-free
    list `l`, the value stored at `S` is the sum of `f` over exactly those subsets
    `T ⊆ S` that agree with `S` on the *un*processed elements, i.e. that contain
    `S \ l.toFinset`.

    Processing one more (fresh) element `a ∈ S` relaxes the constraint by one
    coordinate: it lets `T` either keep `a` (the `f S` branch) or drop it (the
    `f (S.erase a)` branch), which is precisely the SOS recurrence. -/
theorem zetaFoldList_apply (f : SubsetFn α) :
    ∀ (l : List α), l.Nodup → ∀ S : Finset α,
      zetaFoldList l f S
        = ∑ T ∈ S.powerset.filter (fun T => S \ l.toFinset ⊆ T), f T := by
  intro l
  induction l with
  | nil =>
    intro _ S
    -- l = [] : only T = S survives (constraint S ⊆ T together with T ⊆ S)
    simp only [zetaFoldList, List.foldr_nil, List.toFinset_nil, Finset.sdiff_empty]
    have hfilter : S.powerset.filter (fun T => S ⊆ T) = {S} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
      exact ⟨fun ⟨h1, h2⟩ => le_antisymm h1 h2, fun h => ⟨h.le, h.ge⟩⟩
    rw [hfilter, Finset.sum_singleton]
  | cons a rest ih =>
    intro hnd S
    rw [List.nodup_cons] at hnd
    obtain ⟨ha_rest, hrest_nd⟩ := hnd
    have ha_fin : a ∉ rest.toFinset := by rwa [List.mem_toFinset]
    have htf : (a :: rest).toFinset = insert a rest.toFinset := by
      simp [List.toFinset_cons]
    -- one fold step
    have hstep : zetaFoldList (a :: rest) f S
        = zetaStep a (zetaFoldList rest f) S := by
      simp [zetaFoldList, List.foldr_cons]
    rw [hstep]
    by_cases haS : a ∈ S
    · -- a ∈ S : the SOS recurrence splits the target sum by membership of a.
      rw [zetaStep_mem a _ S haS, ih hrest_nd S, ih hrest_nd (S.erase a),
          htf, Finset.sdiff_insert]
      -- a is forced into S \ rest.toFinset (it is in S and not yet processed)
      have hmemD : a ∈ S \ rest.toFinset := by
        rw [Finset.mem_sdiff]; exact ⟨haS, ha_fin⟩
      -- (S.erase a) \ rest.toFinset = (S \ rest.toFinset).erase a
      have hE : (S.erase a) \ rest.toFinset = (S \ rest.toFinset).erase a := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_erase]; tauto
      -- P1 (keep a) = (target).filter (a ∈ ·)
      have hP1 : S.powerset.filter (fun T => S \ rest.toFinset ⊆ T)
          = (S.powerset.filter (fun T => (S \ rest.toFinset).erase a ⊆ T)).filter
              (fun T => a ∈ T) := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset]
        constructor
        · rintro ⟨hTS, hsub⟩
          exact ⟨⟨hTS, (Finset.erase_subset _ _).trans hsub⟩, hsub hmemD⟩
        · rintro ⟨⟨hTS, hsub⟩, haT⟩
          refine ⟨hTS, ?_⟩
          rw [← Finset.insert_erase hmemD, Finset.insert_subset_iff]
          exact ⟨haT, hsub⟩
      -- P2 (drop a) = (target).filter (a ∉ ·)
      have hP2 : (S.erase a).powerset.filter (fun T => (S.erase a) \ rest.toFinset ⊆ T)
          = (S.powerset.filter (fun T => (S \ rest.toFinset).erase a ⊆ T)).filter
              (fun T => ¬ a ∈ T) := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase, hE]
        tauto
      rw [hP1, hP2]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    · -- a ∉ S : processing a leaves S untouched; the constraint is unchanged.
      rw [zetaStep_not_mem a _ S haS, ih hrest_nd S, htf, Finset.sdiff_insert,
          Finset.erase_eq_of_notMem (by rw [Finset.mem_sdiff]; tauto)]

-- ============================================================
-- Correctness of the fast zeta transform
-- ============================================================

/-- **Fast zeta transform correctness.** Folding the single-element SOS step over
    every element of the (finite) ground type computes the full zeta transform:
    `zetaFold f = zetaTransform f`. This is the correctness statement of the
    O(n·2ⁿ) fast subset-sum dynamic program. -/
theorem zetaFold_eq_zetaTransform (f : SubsetFn α) :
    zetaFold f = zetaTransform f := by
  ext S
  rw [zetaFold, zetaFoldList_apply f Finset.univ.toList (Finset.nodup_toList _), zetaTransform]
  have huniv : (Finset.univ.toList).toFinset = (Finset.univ : Finset α) := by
    ext x; simp
  have hfilter : S.powerset.filter (fun T => S \ (Finset.univ.toList).toFinset ⊆ T)
      = S.powerset := by
    apply Finset.filter_true_of_mem
    intro T _
    have : S \ (Finset.univ.toList).toFinset = ∅ := by
      rw [huniv]
      exact Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ S)
    rw [this]
    exact Finset.empty_subset T
  rw [hfilter]

/-- Pointwise form of the correctness theorem. -/
theorem zetaFold_apply (f : SubsetFn α) (S : Finset α) :
    zetaFold f S = ∑ T ∈ S.powerset, f T := by
  rw [zetaFold_eq_zetaTransform]; rfl

/-- The fast fold and the Möbius transform are an inverse transform pair:
    Möbius inversion (from the parent) recovers `f` from the fast fold. -/
theorem mobius_inverts_zetaFold (f : SubsetFn α) :
    mobiusTransform (zetaFold f) = f := by
  rw [zetaFold_eq_zetaTransform]; exact mobius_inverts_zeta f

end IEOQ03
