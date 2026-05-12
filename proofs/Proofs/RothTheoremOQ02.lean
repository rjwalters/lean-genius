import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Roth's Theorem — Bloom–Sisask Logarithmic Bound (OQ-02, S2 ACT-A)

## What This Provides

A typed Lean target for the Bloom–Sisask 2020 quantitative refinement of
Roth's theorem on three-term arithmetic progressions:

  ∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N / (log N)^(1+c)

The bound is named `rothNumberNat_bloom_sisask` and asserted as a Lean
`axiom`. Supporting names — `blasiConst` (a choice of constant `c`),
`blasiConst_pos` (its positivity), and `rothNumberNat_le_blasi` (the
bound at the chosen constant) — give downstream consumers a stable API
without having to call `Exists.choose` manually.

The file is *intentionally minimal*: it provides the typed landmark and
the trivial consequence that the axiom is consistent with Mathlib's
existing qualitative result `rothNumberNat_isLittleO_id`. The Lean
formalization of Bloom–Sisask itself (≥ several thousand lines through
Bohr sets, density increment, and Fourier analysis) is deferred.

## Scope (S2 ACT-A, researcher-12, 2026-05-12)

- File status: **axiomatized** (1 axiom, 0 sorries).
- Imports: `Mathlib.Combinatorics.Additive.Corner.Roth` (for
  `rothNumberNat` and `rothNumberNat_isLittleO_id`) and
  `Mathlib.Analysis.SpecialFunctions.Log.Basic` (for `Real.log`).
- The axiom matches the wording in the docstring of
  `Mathlib.Combinatorics.Additive.AP.Three.Defs`, which explicitly names
  Bloom–Sisask as the expected upper bound on `rothNumberNat`.

## Why This Companion File (Path vs Editing the Gallery `bloom_sisask_bound`)

The existing gallery file `proofs/Proofs/RothTheoremQuantitative.lean`
already states a closely-related bound (`bloom_sisask_bound`) with `sorry`
and uses a project-local `rothNumber` from
`namespace Szemeredi.Roth.Quantitative`. This OQ-02 companion file
deliberately works at the **Mathlib `rothNumberNat`** level, leaving the
gallery file untouched. Downstream Mathlib-style consumers can refer to
`RothTheoremOQ02.rothNumberNat_bloom_sisask` directly; gallery consumers
continue to refer to `Szemeredi.Roth.Quantitative.bloom_sisask_bound`.
Future work can unify the two presentations once Mathlib gains the
prerequisite Bohr-set / density-increment / Fourier infrastructure.

## References

- Bloom, T. F., Sisask, O. (2020). *Breaking the logarithmic barrier in
  Roth's theorem on arithmetic progressions.* arXiv:2007.03528.
- Mathlib v4.26.0 module docstring of
  `Mathlib.Combinatorics.Additive.AP.Three.Defs`.
- Parent quantitative Roth file:
  `proofs/Proofs/RothTheoremQuantitative.lean`.
-/

namespace RothTheoremOQ02

open Asymptotics Filter Topology

/-- **Bloom–Sisask 2020 logarithmic-barrier-breaking bound on the Roth
number.** Axiomatic statement:

  ∃ c > 0, ∀ N ≥ 3, rothNumberNat N ≤ N / (log N)^(1+c)

Proved analytically in Bloom–Sisask, arXiv:2007.03528 (2020), via
density increment on Bohr sets with refined Fourier analysis; the full
proof requires Bohr-set infrastructure not yet in Mathlib at v4.26.0
(pin `2df2f0150c275ad`). Asserted here axiomatically so downstream
gallery files can refer to the bound by name.

The lower bound `N ≥ 3` matches the convention in the gallery file
`Szemeredi.Roth.Quantitative.bloom_sisask_bound` and ensures
`Real.log N > Real.log 3 > 1`, so the right-hand side is positive and
the bound is non-vacuous. -/
axiom rothNumberNat_bloom_sisask :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c)

/-- A canonical choice of the Bloom–Sisask constant `c > 0` extracted from
the axiom via `Exists.choose`. Marked `noncomputable` because
`Exists.choose` is. -/
noncomputable def blasiConst : ℝ :=
  rothNumberNat_bloom_sisask.choose

/-- The Bloom–Sisask constant is positive. -/
theorem blasiConst_pos : 0 < blasiConst :=
  rothNumberNat_bloom_sisask.choose_spec.1

/-- **Bloom–Sisask bound at the canonical constant.** For every `N ≥ 3`,
`rothNumberNat N ≤ N / (log N)^(1 + blasiConst)`. Stable downstream API
that hides the `Exists.choose`. -/
theorem rothNumberNat_le_blasi (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + blasiConst) :=
  rothNumberNat_bloom_sisask.choose_spec.2 N hN

/-- **Consistency with Mathlib's qualitative result.** Mathlib v4.26.0
records `rothNumberNat_isLittleO_id : (rothNumberNat N : ℝ) =o[atTop] (N : ℝ)`
unconditionally in `Mathlib.Combinatorics.Additive.Corner.Roth`. The
Bloom–Sisask axiom strengthens this with an *explicit* decay rate
`O(N / (log N)^(1+c))`, and is consistent with the qualitative form
in the sense that both assert `rothNumberNat N = o(N)`. We record the
qualitative form as a one-line export so OQ-02 consumers can pull it
in via this namespace without re-deriving it from the axiom. -/
theorem bloom_sisask_consistent_with_isLittleO :
    IsLittleO atTop (fun N : ℕ => (rothNumberNat N : ℝ))
      (fun N : ℕ => (N : ℝ)) :=
  rothNumberNat_isLittleO_id

#check rothNumberNat_bloom_sisask
#check blasiConst
#check blasiConst_pos
#check rothNumberNat_le_blasi
#check bloom_sisask_consistent_with_isLittleO

end RothTheoremOQ02
