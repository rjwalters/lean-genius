/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerNDimMathlib

/-!
# Signed CellComplex: ℤ-valued sign with interior-door cancellation

Answers **OQ-04** of `sperner-ndim-mathlib-oq-01`: generalize the abstract
`CellComplex` framework to *signed* cell complexes (oriented chains), with
adjacent facets carrying opposite (±1) signs and summing to 0.

## Why ℤ, not `ZMod 2`?

The naive `ZMod 2`-valued sign with `sign_adj : sign s k + sign s' k' = 1`
is mathematically vacuous as an orientation tracker: `ZMod 2` collapses
signs to a `Bool`-valued "differs on adjacency" labeling (witness:
`ZMod.neg_eq_self_mod_two`). The classical signed-chain boundary
`∂σ = ∑ (-1)^i ∂_i σ` lives over ℤ (or ℚ); in `ZMod 2` it collapses to
the parent's unsigned door count.

This file uses ℤ-valued signs with `sign_adj : sign s k + sign s' k' = 0`,
which is the genuine orientation-preserving boundary condition. The signed
interior-doors theorem then closes via `Finset.sum_involution`.

## Main definitions

* `SpernerAbstract.Signed.SignedCellComplex`: a `CellComplex` enriched
  with per-facet `±1` signs satisfying `sign_adj : sum = 0`.
* `SignedCellComplex.signedAdjMap`: lift of the parent's adjacency map to
  the signed signature.
* `SignedCellComplex.signedDoorCount`: signed door count
  (∑ of facet signs over door facets, in ℤ).

## Main theorem

* `signed_interior_doors_sum_zero`: ∑ over interior doors of
  `K.sign p.1 p.2` equals `0` in ℤ — the signed analog of the parent's
  `interior_doors_even`. Closes via `Finset.sum_involution` applied to
  `signedAdjMap` with cancellation from `sign_adj`.

## Tags

Sperner, signed cell complex, oriented chain complex, ℤ-valued sign,
boundary cancellation, Finset.sum_involution
-/

set_option linter.unusedVariables false

namespace SpernerAbstract
namespace Signed

open Finset BigOperators

/--
A **signed cell complex**: the unsigned parent `CellComplex` enriched
with a per-facet ±1 sign field, subject to the adjacency-orientation
coherence `sign s k + sign s' k' = 0` whenever `adj s k = some (s', k')`.

This is the ℤ-valued (rather than `ZMod 2`-valued) signed structure;
see the file header for why ℤ is the right ground ring.
-/
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0

namespace SignedCellComplex

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- A signed facet value is nonzero: `sign s k ∈ {±1}` ⟹ `sign s k ≠ 0`. -/
lemma sign_ne_zero (K : SignedCellComplex V d)
    (s : K.Simplex) (k : Fin (d + 1)) : K.sign s k ≠ 0 := by
  rcases K.sign_pm_one s k with h | h
  · rw [h]; exact one_ne_zero
  · rw [h]; decide

/-- The signed adjacency map: at an interior facet `(s, k)` with
`adj s k = some (s', k')`, return `(s', k')`; at a boundary facet, stay
put. (Identical to the parent's private `adjMap`, lifted to a public name
for use in this file's signed-cancellation theorem.) -/
def signedAdjMap (K : SignedCellComplex V d)
    (p : K.Simplex × Fin (d + 1)) : K.Simplex × Fin (d + 1) :=
  match K.adj p.1 p.2 with
  | some (s', k') => (s', k')
  | none => p

/-- The signed door count: sum of facet signs over door facets (in ℤ). -/
def signedDoorCount (K : SignedCellComplex V d) (c : V → Fin (d + 1)) : ℤ :=
  ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2),
        K.sign p.1 p.2

/-- Helper: the door predicate transfers across an adjacency.
(Re-proves the parent's `private door_transfer_one_dir` for this file's
public use.) -/
private lemma door_transfer_signed_one_dir (K : SignedCellComplex V d)
    (c : V → Fin (d + 1))
    {s : K.Simplex} {k : Fin (d + 1)} {s' : K.Simplex} {k' : Fin (d + 1)}
    (hvert : (Finset.univ.erase k).image (K.vertices s) =
             (Finset.univ.erase k').image (K.vertices s'))
    (h : isDoorAt c K.toCellComplex s k) :
    isDoorAt c K.toCellComplex s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : K.vertices s i ∈ (Finset.univ.erase k').image (K.vertices s') := by
    rw [← hvert]
    exact Finset.mem_image.mpr
      ⟨i, Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := Finset.mem_image.mp hmem
  exact ⟨i', (Finset.mem_erase.mp hi'_mem).1, by rw [hi'_eq]; exact hi_eq⟩

/-- Helper: `signedAdjMap` is an involution on interior facets
(those with `K.adj ≠ none`). Extracted as a standalone lemma so the
main theorem's `invol` case avoids a dependent-type generalize failure
on the membership proof. -/
private lemma signedAdjMap_invol (K : SignedCellComplex V d)
    (p : K.Simplex × Fin (d + 1)) (hadj : K.adj p.1 p.2 ≠ none) :
    signedAdjMap K (signedAdjMap K p) = p := by
  cases hadj_eq : K.adj p.1 p.2 with
  | none => exact absurd hadj_eq hadj
  | some sk =>
    obtain ⟨s', k'⟩ := sk
    have hadj_back := K.adj_symm p.1 p.2 s' k' hadj_eq
    simp only [signedAdjMap, hadj_eq, hadj_back]

/--
**Signed interior doors cancel**: summing `K.sign p.1 p.2` over all
interior door facets — i.e., pairs `(s, k)` with `isDoorAt c K s k` and
`K.adj s k ≠ none` — gives `0` in ℤ.

The cancellation is direct from `sign_adj`; the involution is
`signedAdjMap`; the discharge is via `Finset.sum_involution`.
-/
theorem signed_interior_doors_sum_zero (K : SignedCellComplex V d)
    (c : V → Fin (d + 1)) :
    ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0 := by
  set S : Finset (K.Simplex × Fin (d + 1)) :=
    Finset.univ.filter fun p =>
      isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none with hS_def
  -- Use the dependent-argument `Finset.sum_involution`.
  refine Finset.sum_involution
    (fun (p : K.Simplex × Fin (d + 1)) (_hp : p ∈ S) => signedAdjMap K p)
    ?cancel ?fpf ?gmem ?invol
  -- Cancellation: K.sign p + K.sign (signedAdjMap K p) = 0
  case cancel =>
    intro p hp
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_hdoor, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      show K.sign p.1 p.2 +
            K.sign (signedAdjMap K p).1 (signedAdjMap K p).2 = 0
      simp only [signedAdjMap, hadj_eq]
      exact K.sign_adj p.1 p.2 s' k' hadj_eq
  -- Fixed-point-free at nonzero values: f p ≠ 0 → signedAdjMap K p ≠ p
  case fpf =>
    intro p hp _hne
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_hdoor, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      show signedAdjMap K p ≠ p
      simp only [signedAdjMap, hadj_eq]
      intro heq
      exact K.adj_ne p.1 p.2 s' k' hadj_eq
        (congr_arg Prod.fst heq).symm
  -- Domain preservation: signedAdjMap K p ∈ S
  case gmem =>
    intro p hp
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back := K.adj_symm p.1 p.2 s' k' hadj_eq
      have hvert := K.adj_vertices p.1 p.2 s' k' hadj_eq
      refine ⟨?_, ?_⟩
      · show isDoorAt c K.toCellComplex (signedAdjMap K p).1 (signedAdjMap K p).2
        simp only [signedAdjMap, hadj_eq]
        exact door_transfer_signed_one_dir K c hvert hdoor
      · show K.adj (signedAdjMap K p).1 (signedAdjMap K p).2 ≠ none
        simp only [signedAdjMap, hadj_eq]
        rw [hadj_back]
        exact Option.noConfusion
  -- Involution: signedAdjMap K (signedAdjMap K p) = p
  case invol =>
    intro p hp
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact signedAdjMap_invol K p hp.2

end SignedCellComplex

end Signed
end SpernerAbstract
