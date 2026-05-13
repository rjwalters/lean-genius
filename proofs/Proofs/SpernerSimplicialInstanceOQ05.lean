/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Proofs.SpernerSimplicialInstance

/-!
# Computable Witness Extractor for the Sperner Simplicial Instance (OQ-05, Candidate C1)

This file implements the simplest of the three candidates in the
`sperner-simplicial-instance-oq-05` open-question dossier: a brute-force,
`Decidable`-driven witness extractor for a panchromatic cell of a
Sperner-coloured triangulation.

The mathematical content is shallow: every step is forced by the existing
`Triangulation.cellFintype` + `CellComplex.decidableIsPanchromatic` instances.
The value is that we now have a `def : Triangulation V n → (V → Fin (n+1))
→ Option T.Cell` that *names* a witness, plus a totality theorem grounded
in `Triangulation.sperner`.

## Scope and honesty

- Not Scarf's algorithm — this is brute-force `O(|T.Cell|)`, not the
  `O(door-path-length)` Scarf pivot. The eventual Scarf walk lives in
  candidate C2 (see `sessions/2026-05-13-s2-prep-c2-1d-scarf-walk.md`).
- Not a Scarf reference replacement — `BrouwerFixedPointOQ04OQ04.lean:244`
  still has `axiom scarf_approx_fixed_point`. (C2) is the eventual
  replacement target.
- Not generalisable to a `noncomputable`-free `AbstractSimplicialData` —
  that requires Candidate C3 (see `sessions/2026-05-12-s2-prep-c3-...`).

## Status

- 0 sorries
- 0 new axioms
- 3 theorems (brute-force `def` + characterisation + totality)
- 1 `decide` smoke-test on `intervalTriangulation 3`

## References

- S1 OBSERVE: PR #18200 (researcher-11, 2026-05-12).
- S2 PREP C1 (this candidate, scaffold): PR #18459 (researcher-9).
- S2 PREP C3 (cascade audit): PR #18392.
- S2 PREP C2-1d: PR #18489.
- S2 PREP-D (Mathlib API audit + bridge): PR #18534.
- S3 PREP (SHA-pin audit): PR #18712.
- PREP-D §4.1 supplies the verified Mathlib-name corrections applied below
  (`Finset.toList_eq_nil`, `Finset.Nonempty.toList_ne_nil`,
  `Finset.nonempty_iff_ne_empty`), replacing the PREP-C1 fallback chain.

## Mathlib bearer lines (at the build-pinned SHAs)

PREP-D #18534 and S2 ACT #18648 cited bearer lines against Mathlib HEAD
(2026-05-13). PR #18712 re-verified each lemma at the `lake-manifest.json`
pinned SHA `2df2f015...` (Mathlib v4.26.0, 2025-12-13) and the
`lean-toolchain` tag `v4.26.0` (Lean commit `d8204c9f...`). Lemma **names**
resolve at both SHAs, so this file builds correctly at the pinned SHAs;
only the **line citations** in the merged PREP-D / ACT memos drifted.
The bearer lines below are verified-correct at the SHAs this proof
actually compiles against:

- `Mathlib/Data/Finset/Basic.lean:512` — `Finset.toList_eq_nil`
- `Mathlib/Data/Finset/Basic.lean:521` — `Finset.Nonempty.toList_ne_nil`
- `Mathlib/Data/Finset/Empty.lean:148`  — `Finset.nonempty_iff_ne_empty`
- `Init/Data/List/Lemmas.lean:937`       — `List.mem_of_head?`
-/

namespace SpernerSimplicialInstanceOQ05

open CellComplex Triangulation Finset

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-- **Brute-force panchromatic-cell finder.**

Given a triangulation `T` and a colouring `c`, return *some* panchromatic
cell if one exists, by enumerating `T.Cell`'s `Fintype` and filtering on
the `Decidable` predicate `CellComplex.IsPanchromatic c T.toCellComplex`.
Returns `none` iff no panchromatic cell exists.

The choice of "first" panchromatic cell is in the order of
`T.cellFintype.elems.toList`, which is implementation-specific. Downstream
consumers should use the membership characterisation
`findPanchromaticBrute_isSome_iff` rather than relying on a specific order. -/
def findPanchromaticBrute
    (T : Triangulation V n) (c : V → Fin (n + 1)) :
    Option T.Cell :=
  (Finset.univ.filter
    (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList.head?

/-- **Characterisation of the brute-force finder via membership.**

`findPanchromaticBrute` returns `some _` iff a panchromatic cell exists.
The proof uses the verified Mathlib names `Finset.toList_eq_nil` and
`Finset.Nonempty.toList_ne_nil` (per PREP-D §4.1). -/
theorem findPanchromaticBrute_isSome_iff
    (T : Triangulation V n) (c : V → Fin (n + 1)) :
    (findPanchromaticBrute T c).isSome ↔
    ∃ s : T.Cell, IsPanchromatic c T.toCellComplex s := by
  unfold findPanchromaticBrute
  constructor
  · -- toList.head? = some _ ⇒ list nonempty ⇒ filter nonempty ⇒ ∃ panchromatic
    intro h
    have hlist_ne : (Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList ≠ [] := by
      intro hnil
      simp [hnil] at h
    have hfilter_ne : (Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      exact hlist_ne (Finset.toList_eq_nil.mpr hempty)
    obtain ⟨s, hs⟩ := hfilter_ne
    rw [Finset.mem_filter] at hs
    exact ⟨s, hs.2⟩
  · -- ∃ panchromatic ⇒ filter nonempty ⇒ list nonempty ⇒ head? = some _
    rintro ⟨s, hs⟩
    have hmem : s ∈ Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s) := by
      rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hs⟩
    have hne : (Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).Nonempty :=
      ⟨s, hmem⟩
    have hlist_ne : (Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList ≠ [] :=
      hne.toList_ne_nil
    cases hlist : (Finset.univ.filter
        (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList with
    | nil => exact absurd hlist hlist_ne
    | cons _ _ => simp [List.head?]

/-- **`some` consumes a panchromatic cell.**

If `findPanchromaticBrute` returns `some s`, then `s` is in fact
panchromatic. This is the supplementary lemma from PREP-C1 §2 that gives
downstream consumers the witness property without relying on enumeration
order. -/
theorem findPanchromaticBrute_eq_some_imp_panchromatic
    (T : Triangulation V n) (c : V → Fin (n + 1)) (s : T.Cell)
    (heq : findPanchromaticBrute T c = some s) :
    IsPanchromatic c T.toCellComplex s := by
  unfold findPanchromaticBrute at heq
  have hmem : s ∈ (Finset.univ.filter
      (fun s : T.Cell => IsPanchromatic c T.toCellComplex s)).toList :=
    List.mem_of_head? heq
  rw [Finset.mem_toList, Finset.mem_filter] at hmem
  exact hmem.2

/-- **Totality of the brute-force finder under boundary-door parity.**

If the boundary doors of `T` under colouring `c` are odd, then
`findPanchromaticBrute T c` returns `some` cell. Existence of a
panchromatic witness follows from `Triangulation.sperner`. -/
theorem findPanchromaticBrute_isSome_of_boundary_odd
    (T : Triangulation V n) (c : V → Fin (n + 1))
    (hbdry : Odd (Finset.univ.filter
      (fun p : T.Cell × Fin (n + 1) =>
        IsDoor c T.toCellComplex p.1 p.2 ∧
        T.adj p.1 p.2 = none)).card) :
    (findPanchromaticBrute T c).isSome := by
  rw [findPanchromaticBrute_isSome_iff]
  exact Triangulation.sperner T c hbdry

end SpernerSimplicialInstanceOQ05

/-! ## Demo: brute-force finder on a 3-segment interval triangulation

A non-trivial Sperner colouring on `intervalTriangulation 3 (by norm_num)`
with `c(n) = if n ≤ 1 then 0 else 1`:

- Cell 0 has vertices `{0, 1}` → both colour `0` → NOT panchromatic.
- Cell 1 has vertices `{1, 2}` → colours `{0, 1}` → **panchromatic**.
- Cell 2 has vertices `{2, 3}` → both colour `1` → NOT panchromatic.

So `∃ s, IsPanchromatic c (intervalTriangulation 3 ...).toCellComplex s`
holds, witnessed by `s = 1`. The smoke-test below uses `decide` rather
than `#eval`, since `decide` provides a kernel-level proof object while
`#eval` produces no proof obligation. -/

example : ∃ s : Fin 3, CellComplex.IsPanchromatic
    (fun n : ℕ => if n ≤ 1 then (0 : Fin 2) else 1)
    (Triangulation.intervalTriangulation 3 (by norm_num)).toCellComplex s := by
  refine ⟨1, ?_⟩
  decide
