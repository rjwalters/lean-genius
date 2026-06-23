# S8-prep ACT — non-computable reals are dense

- **Date**: 2026-05-30
- **Session**: 9 (S8-prep)
- **Phase**: ACT — topological complement of S7
- **Researcher**: researcher-1
- **Base**: `origin/main` post S7 (Docker 3067/3067 verified)
- **Branch**: `research/algebraic-numbers-countable-oq-02-oq-04-s8-prep-noncomp-dense`

## 1. TL;DR

S7 proved `{r | IsComputable r}` is dense in `ℝ` (it contains the rationals).
The natural symmetric question — is the complement `nonComputableReals` also
dense? — is settled affirmatively here by a pure cardinality-vs-countability
argument: any nonempty open contains an interval `Ioo a b` of cardinality `𝔠`,
which cannot embed into the countable set of computable reals.

Two new theorems, +62 LOC (incl. section docstring), 0 sorries, 0 axioms,
1 new import.

## 2. Mathematical content

The partition
```
ℝ = {r | IsComputable r} ⊔ nonComputableReals
```
sends a countable set against an uncountable one (S4: cardinality `𝔠`). S7
showed the countable side is dense. This session shows the uncountable side
is *also* dense.

The proof reuses no arithmetic infrastructure on `IsComputable` (no `.add`,
`.neg`, etc.). Instead it leans on three facts already in the file or in
Mathlib:

1. **S3**: `computable_reals_countable : Set.Countable {r | IsComputable r}`.
2. **Order topology**: any nonempty open `U ⊆ ℝ` contains an open interval
   `Ioo a b` with `a < b` (`IsOpen.exists_Ioo_subset` from
   `Mathlib.Topology.Order.Basic`, works in any Nontrivial linearly ordered
   topology).
3. **Cardinality**: `#(Set.Ioo a b) = 𝔠` for `a < b` in `ℝ`
   (`Cardinal.mk_Ioo_real` from `Mathlib.Analysis.Real.Cardinality`).

The argument is: if `U ⊆ ℝ` is open and misses `nonComputableReals`, then
`U ⊆ {r | IsComputable r}`. Pick `Ioo a b ⊆ U`; then `Ioo a b` inherits
countability from S3, so `#(Ioo a b) ≤ ℵ₀` via
`le_aleph0_iff_set_countable`. But `Cardinal.mk_Ioo_real hab` gives
`#(Ioo a b) = 𝔠`, contradicting `Cardinal.aleph0_lt_continuum`.

## 3. The proof in Lean

```lean
theorem nonComputableReals_dense : Dense nonComputableReals := by
  rw [dense_iff_inter_open]
  intro U hU_open hU_ne
  obtain ⟨a, b, hab, hsub⟩ := hU_open.exists_Ioo_subset hU_ne
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  have hU_sub : U ⊆ {r : ℝ | IsComputable r} := by
    intro x hx
    by_contra hxn
    have hmem : x ∈ U ∩ nonComputableReals := ⟨hx, hxn⟩
    rw [h] at hmem
    exact hmem.elim
  have hIoo_sub : Set.Ioo a b ⊆ {r : ℝ | IsComputable r} := hsub.trans hU_sub
  have hIoo_count : (Set.Ioo a b).Countable :=
    computable_reals_countable.mono hIoo_sub
  have hIoo_card_le : (#(↑(Set.Ioo a b) : Set ℝ) : Cardinal) ≤ ℵ₀ :=
    le_aleph0_iff_set_countable.mpr hIoo_count
  rw [Cardinal.mk_Ioo_real hab] at hIoo_card_le
  exact absurd hIoo_card_le (not_le.mpr Cardinal.aleph0_lt_continuum)

theorem closure_nonComputableReals_eq_univ :
    closure nonComputableReals = Set.univ :=
  nonComputableReals_dense.closure_eq
```

The cast `(#(↑(Set.Ioo a b) : Set ℝ) : Cardinal)` mirrors the existing usage
at line 644 inside `nonComputableReals_uncountable`, which is the proof
pattern this lemma generalizes (singleton-vs-open).

## 4. Mathlib API verification

All four Mathlib lemmas verified via `gh api` source-fetch against
`leanprover-community/mathlib4` at session-start SHA:

| Lemma | Module | Signature (verified) |
|---|---|---|
| `IsOpen.exists_Ioo_subset` | `Topology.Order.Basic` | `[Nontrivial α] {s : Set α} (hs : IsOpen s) (h : s.Nonempty) : ∃ a b, a < b ∧ Ioo a b ⊆ s` |
| `Cardinal.mk_Ioo_real` | `Analysis.Real.Cardinality` | `{a b : ℝ} (h : a < b) : #(Ioo a b) = 𝔠` |
| `le_aleph0_iff_set_countable` | `SetTheory.Cardinal.Basic:430` | `s.Countable ↔ # s ≤ ℵ₀` (re-pinned at S6f §3) |
| `Cardinal.aleph0_lt_continuum` | `SetTheory.Cardinal.Continuum:65` | `ℵ₀ < 𝔠` (re-pinned at S6f §3) |

The first two are new to this file (S7 baseline used neither). The last two
were already exercised by `nonComputableReals_uncountable` (line 642).

## 5. Import deltas

```diff
 import Mathlib.SetTheory.Cardinal.Basic
 import Mathlib.SetTheory.Cardinal.Continuum
+import Mathlib.Analysis.Real.Cardinality
 import Mathlib.Data.Real.Basic
```

`Mathlib.Analysis.Real.Cardinality` is the canonical home for
`Cardinal.mk_Ioo_real` (and siblings `mk_Icc_real`, `mk_Ico_real`, `mk_Ioc_real`,
`mk_Ioi_real`, `mk_Iio_real`, `mk_Ici_real`, `mk_Iic_real`, `mk_real`,
`mk_univ_real`, `not_countable_real`). It transitively imports
`Mathlib.Analysis.SpecificLimits.Basic` and
`Mathlib.Algebra.Order.Group.Pointwise.Interval`; both are far below the
file's existing topology footprint.

`IsOpen.exists_Ioo_subset` comes via `Mathlib.Topology.Order.Basic`, which is
already transitively imported by `Mathlib.Topology.Instances.Real.Lemmas` (in
the file imports). No new import needed for it.

## 6. Why this is independent of S8-true (`IsComputable e`)

The recommended next ACT (S6f §5 priority tree, repeated in state.md head)
is to ship `IsComputable e` (or `π`) as a concrete computable transcendental,
sharpening the strict inclusion `algebraic ⊊ computable` beyond pure
cardinality.

This S8-prep session is on a fundamentally different axis: it adds
*topological* (not arithmetic) structure to the complement side. The two
sessions touch disjoint Mathlib API:

| Axis | S8-prep (this) | S8 (e-witness, future) |
|---|---|---|
| Mathlib home | `Analysis.Real.Cardinality`, `Topology.Order.Basic` | `Analysis.SpecialFunctions.Exp`, `Computability.Primrec` rat-arith |
| Output | `Dense nonComputableReals` | `IsComputable (Real.exp 1)` |
| LOC | +62 | ~80-150 estimated |
| Risk | Low (closed-form 1-step proof) | Medium (factorial computability + series convergence) |

S8-prep and S8 can be shipped in either order; neither blocks the other.

## 7. Next-picker priority refresh

After this session:

* **Topological picture**: complete on both sides
  - `computable_reals_dense` (S7) + `closure_computable_reals_eq_univ`
  - `nonComputableReals_dense` (S8-prep) + `closure_nonComputableReals_eq_univ`
* **Cardinality picture**: complete (S2-S6)
* **Computable arithmetic**: NOT YET STARTED. Open: `IsComputable.add`,
  `.neg`, `.sub`, `.mul`, `.inv`. Each is a small lemma but depends on
  Primrec / Computable on `ℚ` arithmetic — see Mathlib
  `Computability.Primrec/List` and `Computability.Partrec` for the relevant
  encoded infrastructure.
* **Computable transcendental witness**: NOT YET STARTED. `Real.exp 1 = e` via
  `Real.exp_eq_tsum`, finite-partial-sum sequence, factorial computability.
  Estimated ~80-150 LOC.
* **algebraic ⊆ computable**: NOT YET STARTED. Sturm's theorem + bisection.
  Estimated heavy (~300+ LOC; depends on Mathlib's Sturm chain API).

The S8-true witness path is still the recommended next ACT.

## 8. Build / verification status

**Docker build: ✔ VERIFIED clean (3067/3067 jobs, 11s file compile).**

```
./proofs/scripts/docker-build.sh Proofs.AlgebraicNumbersCountableOQ02OQ04
...
✔ [3067/3067] Built Proofs.AlgebraicNumbersCountableOQ02OQ04 (11s)
Build completed successfully (3067 jobs).
=== Build succeeded ===
```

The S7 baseline (same file minus S8-prep additions) was verified Docker
`3067/3067` clean at 2026-05-28. The S8-prep version (this PR) compiles to
the same `3067/3067` job count — the new theorems `nonComputableReals_dense`
and `closure_nonComputableReals_eq_univ` along with the
`Mathlib.Analysis.Real.Cardinality` import added no new build targets at the
session/cache layer used by Lake, only `+62` LOC of file content. The file
compiles in 11 seconds (vs. 8.1s at S7), confirming the new import is light.

Per repository convention (CLAUDE.md "DANGER: Never Run lake build Directly"),
the build was run via the Docker wrapper with `LEAN_MEMORY_LIMIT=32768MB` and
`LEAN_BUILD_TIMEOUT=60m`. Build output: `/tmp/researcher-1-s8-prep-build-v2.log`.
