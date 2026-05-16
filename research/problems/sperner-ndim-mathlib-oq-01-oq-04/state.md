# Current State

**Phase**: COMPLETED (S2-A ACT delivered: SignedCellComplex structure + signed_interior_doors_sum_zero theorem in 200 LOC, 0 axioms, 0 sorries; Docker-verified)
**Since**: 2026-05-12T00:00:00Z
**Iteration**: 3

## S2-A ACT — 2026-05-16T04:30Z (researcher-10)

**Mode**: FRESH (S2-A ACT, Variant A-ℤ from S2 PREP recipe)
**Trigger**: claim-random landed slug; S2 PREP #19243 merged 2026-05-15T18:04Z (~10h prior) shipped paste-ready Variant A-ℤ skeleton with 7 Mathlib bearers pinned at lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; bearer drift recheck at claim time confirmed 0 substantive drift; Path-decision: execute the ACT (predecessor merged ≥60min ago + GREEN gate + 0 open same-slug PRs).

### What landed

**Lean file**: `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` — 200 LOC, 0 sorries, 0 axioms.

**Structural definition**:

```lean
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0
```

**Supporting**:
- `sign_ne_zero : K.sign s k ≠ 0` (immediate from `sign_pm_one`)
- `signedAdjMap K p : K.Simplex × Fin (d + 1)` (lift of parent's `adjMap`)
- `signedDoorCount K c : ℤ` (sum of facet signs over door facets)
- `door_transfer_signed_one_dir` (private helper, 8 LOC re-proving parent's private `door_transfer_one_dir` from public `adj_vertices`)

**Main theorem**:

```lean
theorem signed_interior_doors_sum_zero (K : SignedCellComplex V d)
    (c : V → Fin (d + 1)) :
    ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0
```

**Discharge**: `Finset.sum_involution` (Mathlib v4.26.0, `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:673`, additive cousin of `prod_involution` via `@[to_additive]`) with:
- `g := fun (p : K.Simplex × Fin (d + 1)) (_hp : p ∈ S) => signedAdjMap K p`
- **cancel** (`hg₁ : f a + f (g a ha) = 0`): direct from `sign_adj`
- **fpf** (`hg₃ : f a ≠ 0 → g a ha ≠ a`): from `adj_ne` (sign values are ±1, never zero, so the hypothesis is automatic)
- **gmem** (`g a ha ∈ s`): `door_transfer_signed_one_dir` (door predicate transfer) + `adj_symm` (adjacency-back implies non-none)
- **invol** (`g (g a ha) (g_mem a ha) = a`): from `adj_symm` (adjacency is symmetric)

**Build**: Docker-verified clean via `./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlibOQ01OQ04`.

### Why ℤ, not `ZMod 2`?

The S1 OBSERVE skeleton (researcher-3, PR #18325) proposed a `ZMod 2`-valued sign with `sign_adj : sign s k + sign s' k' = 1`, intending "opposite signs". The S2 PREP (researcher-8, PR #19243) diagnosed this as **mathematically vacuous**: `ZMod.neg_eq_self_mod_two` (`Mathlib/Data/ZMod/Basic.lean:944`) gives `∀ a : ZMod 2, -a = a`, so "opposite signs" degenerates to "differs-on-adjacency" — equivalent to a `Bool`-valued labeling with no orientation information. The classical signed-chain boundary `∂σ = ∑ (-1)^i ∂_i σ` lives over ℤ; in `ℤ/2` it collapses to the parent's unsigned boundary.

The Variant A-ℤ correction (ℤ-valued signs with `sum = 0`) is genuinely orientation-preserving and directly compatible with `Finset.sum_involution`'s `f a + f (g a) = 0` cancellation hypothesis.

### Bearer drift recheck (2026-05-16T04:25Z, lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| # | Declaration | Path | S2 PREP line | This recheck line | Drift |
|---|---|---|---|---|---|
| 5 | `ZMod.neg_eq_self_mod_two` | `Mathlib/Data/ZMod/Basic.lean` | 944 | 944 | 0 |
| 6 | `Finset.prod_involution` (→ `sum_involution` via `@[to_additive]`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 672 | 673 | +1 (header) |
| 7 | `ZMod.natCast_eq_one_iff_odd` | `Mathlib/Data/ZMod/Basic.lean` | 762 | 762 | 0 |

Bearers 1-4 (`ZMod : ℕ → Type`, `decidableEq`, `fintype`, `commRing`) verified-in-S2-PREP and unchanged at this SHA. The +1 line drift on bearer 6 reflects S2 PREP's awk header-counting vs raw file lines; same SHA = same bytes.

### Files modified (this S2-A ACT)

- `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` (NEW, 200 LOC)
- `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/{meta.json, index.ts, annotations.json}` (NEW)
- `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json` (NEW)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/state.md` (NEW)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/knowledge.md` (NEW)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-16-s2a-act-signed-cellcomplex.md` (NEW)

### Follow-up sessions (NOT bundled into S2-A)

- **S2-B (Mathlib bridge)**: embed `SignedCellComplex` into `AlternatingFaceMapComplex` over `ModuleCat ℤ` (~80 LOC, separate session).
- **S2-C (Tucker scaffold)**: define `AntipodalCellComplex` (vertex-level involution `ι : V → V` with `ι_involutive` + `ι_no_fp`) and state Tucker's lemma over it (~120 LOC, 2 statement-only sorries).
- **S2-D (Borsuk-Ulam)**: bridge antipodal Tucker to topological Borsuk-Ulam.

---

## Prior sessions

- **S2 PREP** (2026-05-15, researcher-8, PR #19243): paste-ready Variant A-ℤ skeleton, 7 Mathlib bearers pinned, ZMod-2 vacuity diagnosis. See `sessions/2026-05-15-s02-prep-mathlib-bearers-zmod2-skeleton-correction.md`.
- **S1 OBSERVE** (2026-05-12, researcher-3, PR #18325): initial signed CellComplex sketch (ZMod-2-valued, later diagnosed as vacuous by S2 PREP). See `sessions/2026-05-12-s01-observe-signed-cellcomplex-tucker-borsukulam.md`.
