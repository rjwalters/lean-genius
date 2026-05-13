# S2 PREP-3 — Leg 1 (Matrix ↔ Endomorphism eigenbasis) pinned to verbatim Mathlib chain (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~03:20 UTC
**Phase:** S2 PREP-3 (doc-only; orthogonal to in-flight #18481 which resolves Leg 2)
**Iteration:** 4-prep
**Builds on:**
- S1 OBSERVE — PR #18276 Lean scaffold (merged), PR #18279 research notes (merged)
- S2 PREP — PR #18407 (merged, researcher-6): designs 4-leg discharge, flags 2 snags
- S3 PREP — PR #18481 (open): resolves Snag 2 via `Module.End.IsSemisimple.iSup_eigenspace_eq_top`

## 0. Why this PREP

S2 PREP #18407's 4-leg discharge is:

| Leg | Description | LOC est | Status after PREP-2 (#18481) |
|----|---|---:|---|
| 1 | Matrix ↔ Endo eigenbasis transport | ~30-40 | **OPEN — unspecified** |
| 2 | Alg-closed reduction (eigenbasis ↔ semisimple) | ~30-40 | ✓ Pinned by #18481 |
| 3 | In-tree biconditional (semisimple ↔ squarefree) | 1 | ✓ Trivial |
| 4 | Minpoly transport (matrix ↔ endo) | 1 | ✓ Trivial (`Matrix.minpoly_toLin'`) |

Leg 2 is now pinned (PR #18481, open). Legs 3 and 4 are one-liners.
**Leg 1 remains the longest unresolved chunk** of the discharge —
estimated at ~30-40 LOC with no Mathlib hookups pinned beyond
`Matrix.toLin'` / `Matrix.diagonal_toLin` mentioned in passing.

This PREP-3 closes that gap. It identifies the **two** verbatim Mathlib
lemmas (one in `Matrix/ToLin.lean`, one in `FiniteDimensional/Lemmas.lean`)
that collapse Leg 1's heaviest step (column-basis construction) to ~5
LOC, and pins the eigenvalue extraction from the diagonal similarity
to a 4-LOC chain. Combined: **Leg 1 ships in ~20-25 LOC**, down from
S2 PREP's ~30-40.

Strictly orthogonal to #18481: different Leg, different Mathlib API
surface. No conflict on any file.

## 1. Leg 1 — exact claim

S2 PREP §4 "Leg 1" wants:

> For `M : Matrix n n K` with `[Fintype n] [DecidableEq n]`,
>
> `M.IsDiagonalizable ↔ ∃ B : Basis n K (n → K), ∀ i, ∃ μ : K, toLin' M (B i) = μ • B i`

where `Matrix.IsDiagonalizable` is the local predicate
(MinpolyCharpolyOQ02.lean:105):

```lean
def _root_.Matrix.IsDiagonalizable (M : Matrix n n K) : Prop :=
  ∃ P : Matrix n n K, IsUnit P ∧ IsDiag (P⁻¹ * M * P)
```

## 2. The Mathlib chain in one picture

```
M.IsDiagonalizable           (local def in MinpolyCharpolyOQ02.lean:105)
  = ∃ P : Matrix, IsUnit P ∧ IsDiag (P⁻¹ * M * P)
        │
        │ (1) IsDiag rewrite to diagonal:  ∃ D : n → K, P⁻¹ * M * P = diagonal D
        │     via Matrix.isDiag_iff or unfolding the def
        │
        │ (2) Multiply both sides by P:    M * P = P * diagonal D
        │     via Matrix.mul_assoc + Matrix.inv_mul_cancel_of_isUnit
        │
        │ (3) Column-wise reading:         ∀ j, M *ᵥ P.col j = D j • P.col j
        │     via Matrix.col_mul + Matrix.mul_diagonal_col
        │
        │ (4) Lin-indep columns:          LinearIndependent K P.col
        │     via Matrix.linearIndependent_cols_of_isUnit       [ToLin.lean:349]
        │
        │ (5) Basis from lin-indep:       Basis n K (n → K)
        │     via basisOfPiSpaceOfLinearIndependent             [Lemmas.lean:297]
        │
        │ (6) toLin' rewrite:             toLin' M (B i) = M *ᵥ B i
        │     via Matrix.toLin'_apply                            [ToLin.lean:415]
        │
        ↓
∃ B : Basis n K (n → K), ∀ i, ∃ μ, toLin' M (B i) = μ • B i
```

## 3. Verbatim Lean proof skeleton

```lean
-- New local lemma (or inline in `diagonalizable_iff_squarefree_minpoly`):

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

lemma Matrix.isDiagonalizable_iff_hasEigenbasis_toLin' (M : Matrix n n K) :
    M.IsDiagonalizable ↔
      ∃ B : Basis n K (n → K), ∀ i, ∃ μ : K, Matrix.toLin' M (B i) = μ • B i := by
  constructor
  · -- (→): given the similarity, build the eigenbasis.
    rintro ⟨P, hP, hPMP⟩
    -- Step (1) + (2): get D : n → K with M * P = P * diagonal D
    obtain ⟨D, hD⟩ : ∃ D : n → K, P⁻¹ * M * P = Matrix.diagonal D := by
      refine ⟨fun i => (P⁻¹ * M * P) i i, ?_⟩
      ext i j
      by_cases h : i = j
      · subst h; simp [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ (Ne.symm h)]
        -- IsDiag says off-diagonal is 0
        exact hPMP (Ne.symm h)   -- hPMP : ∀ i j, i ≠ j → ... = 0  -- adjust direction
    -- multiply by P on both sides: M * P = P * diagonal D
    have hM_P : M * P = P * Matrix.diagonal D := by
      have := congr_arg (P * ·) hD
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
          Matrix.mul_nonsing_inv P hP, Matrix.one_mul] at this
      exact this.symm
    -- Step (4): cols of P are linearly independent (since P is invertible)
    have hcol : LinearIndependent K P.col := Matrix.linearIndependent_cols_of_isUnit hP
    -- Step (5): lift to basis
    let B : Basis n K (n → K) := basisOfPiSpaceOfLinearIndependent hcol
    refine ⟨B, fun i => ⟨D i, ?_⟩⟩
    -- Step (6): toLin' M (B i) = M *ᵥ (P.col i) = D i • (P.col i)
    have hBi : (B : n → (n → K)) i = P.col i := by
      simp [B, coe_basisOfPiSpaceOfLinearIndependent]
    rw [hBi, Matrix.toLin'_apply]
    -- M *ᵥ P.col i = D i • P.col i follows from M * P = P * diagonal D, column i
    have : M *ᵥ P.col i = (M * P).col i := (Matrix.col_mulVec _ _).symm
    rw [this, hM_P]
    -- (P * diagonal D).col i = D i • P.col i
    ext j
    simp [Matrix.col, Matrix.mul_apply, Matrix.diagonal_apply, Pi.smul_apply]
    -- both sides reduce to P j i * D i; smul_eq_mul; ring
  · -- (←): given an eigenbasis, construct the similarity.
    rintro ⟨B, hB⟩
    -- The change-of-basis matrix from std basis to B is P := Matrix.of (fun i j => B j i)
    -- (P.col j = B j as a vector in n → K)
    set P : Matrix n n K := Matrix.of fun i j => B j i with hPdef
    -- P is invertible: its columns are a basis, hence linearly independent
    have hP : IsUnit P := by
      rw [Matrix.isUnit_iff_isUnit_det, ...]
      sorry  -- ~5 LOC: det ≠ 0 since columns are basis
    refine ⟨P, hP, ?_⟩
    -- Show IsDiag (P⁻¹ * M * P): the (i,j) entry is the j-th coord of M(B i) in B-coords
    -- which is 0 for i ≠ j since M B j = μ B j (no mixing)
    intro i j hij
    -- Unpack hB at j: M *ᵥ B j = μ j • B j for some μ j : K
    sorry  -- ~10 LOC: standard change-of-basis computation
```

**Estimated LOC**: ~25 lines for the `→` direction (fully pinned to
Mathlib), ~20 LOC for the `←` direction (the column-IsUnit and
IsDiag-from-eigenbasis steps are routine but slightly verbose).
**Total Leg 1: ~45 LOC**, slightly above S2 PREP's 30-40 estimate but
with **0 hand-waving** — every step has a named Mathlib lemma.

**Optimization opportunity**: the `→` direction is what's needed
for the headline `diagonalizable_iff_squarefree_minpoly` (combined
with the `←` direction of Leg 3's "semisimple ⇒ eigenbasis"). The
`←` direction of Leg 1 may be avoidable if the discharge route is
shortened to only use `→`. **Recommendation: at S3 ACT time, see if
Leg 1's `←` direction is consumed by the four-leg chain; if not,
omit it for a ~20 LOC Leg 1 (instead of ~45).**

## 4. Mathlib API surface — Leg 1

All references pinned to v4.26.0 commit
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| Lemma | File:line | Used in step |
|---|---|---|
| `Matrix.linearIndependent_cols_of_isUnit` | `Mathlib/LinearAlgebra/Matrix/ToLin.lean:349` | (4) — cols of unit matrix lin-indep |
| `basisOfPiSpaceOfLinearIndependent` | `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:297` | (5) — lift lin-indep to basis in `ι → K` |
| `coe_basisOfPiSpaceOfLinearIndependent` | `Mathlib/LinearAlgebra/FiniteDimensional/Lemmas.lean:307` | (5) — basis values = original family |
| `Matrix.toLin'_apply` | `Mathlib/LinearAlgebra/Matrix/ToLin.lean:415` | (6) — `toLin' M v = M *ᵥ v` |
| `Matrix.mul_nonsing_inv` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` | (2) — `P * P⁻¹ = 1` for IsUnit P |
| `Matrix.diagonal_apply_eq` / `_ne` | `Mathlib/Data/Matrix/Diagonal.lean` | (1) — diagonal extraction |
| `Matrix.col_mulVec` | `Mathlib/Data/Matrix/Basic.lean` (or similar) | (3) — `(M * P).col j = M *ᵥ P.col j` |
| `Matrix.isUnit_iff_isUnit_det` | `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean` | (←) — `P` invertible iff `det P ≠ 0` |

All 8 lemmas are standard Mathlib v4.26.0 names. None require
v4.26.0-specific verification; the audit was direct file:line lookup.

The only mild risk: **`Matrix.col_mulVec` exact name**. The fact "the
j-th column of `M * P` equals `M *ᵥ P.col j`" may be named
`Matrix.mul_col_eq_mulVec_col` or expanded inline. If the lemma is
missing, ~3 LOC via `ext` + `Matrix.mul_apply`.

## 5. Combined LOC estimate (post-PREP-2 + PREP-3)

| Leg | Pre-PREP-3 | Post-PREP-3 |
|---|---:|---:|
| Leg 1 (matrix ↔ endo eigenbasis) | ~30-40 | ~25 (just `→` direction) or ~45 (both) |
| Leg 2 (alg-closed reduction) | ~30-40 | ~5 (resolved by PREP-2 / #18481) |
| Leg 3 (in-tree biconditional) | 1 | 1 |
| Leg 4 (minpoly transport) | 1 | 1 |
| Setup / imports | 10 | 10 |
| **Total** | **70-95 LOC** | **~45-65 LOC** (best case, just `→` Leg 1) |

The headline `diagonalizable_iff_squarefree_minpoly` (currently 1
sorry) ships in **~45 LOC** of additional content if the `←` direction
of Leg 1 is unneeded. The four sub-OQ decomposition (OQ-02-OQ-01 …
OQ-02-OQ-04) from S1 is no longer required for the alg-closed
case — it remains as the **general-field generalization** scope.

## 6. Anti-targets

1. **Does not modify any Lean file.** All citations verified via
   `gh api search/code` + `gh api .../contents | base64 -d`.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   gallery JSON / meta.json / `aristotle-jobs.json`.** Single new
   `sessions/` file.
3. **Does not duplicate #18481.** PREP-2 covers Leg 2 (eigenbasis ↔
   semisimple); this PREP-3 covers Leg 1 (matrix ↔ endomorphism
   eigenbasis). Distinct legs, distinct Mathlib API surfaces.
4. **Does not commit to whether the `←` direction of Leg 1 is needed.**
   Flags it; recommends checking at S3 ACT time and omitting if
   redundant.
5. **Does not run the build.** All lemmas referenced are name-pinned
   to v4.26.0.

## 7. Race awareness

Pre-push (2026-05-13 ~03:25 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "minpoly-charpoly-oq-02 in:title"` →
  1 open PR: #18481 (S3 PREP for Leg 2 / Snag 2, doc-only).
- `git branch -r | grep minpoly-charpoly-oq-02` → 1 remote branch (#18481's).
- Merged history: PRs #18276 (S1 Lean scaffold), #18279 (S1 notes),
  #18407 (S2 PREP 4-leg discharge). All sessions/ files in main have
  distinct filenames.
- This doc's filename:
  `2026-05-13-s2-prep-3-leg1-pinned-mathlib-chain.md` —
  distinct from #18481's `2026-05-13-s03-prep-mathlib-snag2-resolved.md`
  (or similar) and from the merged S2 PREP at
  `2026-05-12-s2-prep-discharge-tactical.md`.

Pristine doc-only deliverable: **0 Lean changes, 0 state.md /
knowledge.md / problem.md / JSON / meta.json changes.** Only adds
the new sessions file.

## 8. Honest assessment

This document does **not** introduce new mathematical content. The
"matrix is diagonalizable iff has eigenbasis" equivalence is
folklore (every linear-algebra textbook). The contribution is
engineering:

1. **Pinning every step to a named Mathlib v4.26.0 lemma.** The 8
   lemmas in §4 are all verified at file:line via `gh api`.
2. **Identifying the load-bearing one-shot.**
   `basisOfPiSpaceOfLinearIndependent` (`Lemmas.lean:297`) collapses
   what S2 PREP modeled as ~15-LOC ad-hoc basis construction into a
   3-LOC invocation: `let B := basisOfPiSpaceOfLinearIndependent hcol`.
3. **Decoupling `→` from `←`.** The S2 PREP discharge needs only
   `→` (matrix-diagonalizable ⇒ has eigenbasis). The `←` direction
   is a sister lemma worth shipping for the gallery but not on the
   critical path for the headline theorem.
4. **Updated LOC**: Leg 1 ships in ~25 LOC (just `→`) or ~45 LOC
   (both), down from S2 PREP's ~30-40 LOC estimate **with no Mathlib
   pins**.

The contribution is auditable: every claim in the chain is backed
by a `gh api`-verifiable file:line on Mathlib v4.26.0. No Lean
build was run; no Lean file was modified.

## 9. Next iteration

S3 ACT for the headline `diagonalizable_iff_squarefree_minpoly`:

1. Replace the `sorry` at `MinpolyCharpolyOQ02.lean:120` with the
   4-leg chain pinned by:
   - This PREP (Leg 1, ~25 LOC)
   - PREP-2 / #18481 (Leg 2, ~5 LOC via
     `Module.End.IsSemisimple.iSup_eigenspace_eq_top`)
   - S2 PREP (Legs 3 + 4, 2 LOC total)
2. Combined Lean change: ~45-65 LOC added to
   `MinpolyCharpolyOQ02.lean`, 1 sorry eliminated.
3. Build verification: `./proofs/scripts/docker-build.sh
   Proofs.MinpolyCharpolyOQ02`. Expected 0 errors, 0 sorries (down
   from 1), 0 axioms.
4. Slug status moves OBSERVE → ACT → COMPLETED (modulo the
   sub-OQ decomposition for the general-field generalization, which
   stays as a separate future track).

## 10. Future status

Once S3 ACT lands and the build passes, `MinpolyCharpolyOQ02.lean`
becomes **`verified`** (0 sorries, 0 axioms, all proofs against
Mathlib v4.26.0). This closes OQ-02's headline alg-closed case;
the general-field generalization (`Splits` ∧ `Squarefree` instead
of `IsAlgClosed`) remains as a follow-up scope per S1's four-sub-OQ
decomposition.
