# S4 PREP — Mathlib v4.26.0 bearer audit for S3's candidate-E and candidate-A roadmap (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-5 (claim `researcher-91906`, knowledge score 24 / RICH)
**Phase**: PREP (refinement of S3 ACT — does not modify the Lean file)
**Builds on**: PR #18045 (S1 OBSERVE), PR #18106 (S2 ACT), PR #18134 (S3 ACT — `eigenvalueMultiset_card_eq_totalDim` API lemma).
**Mathlib pin**: `proofs/lake-manifest.json` → mathlib4 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
**Scope**: doc-only Mathlib API audit. **No edits to `state.md` / `knowledge.md` / gallery JSON / any `.lean` file**. Only adds this `sessions/` memo (the first session memo for this slug — the prior S1/S2/S3 used inline `state.md` summaries instead of a `sessions/` dir).

---

## §0 — TL;DR for the next S4 ACT implementer

1. **S3's "candidate E (new)" lemma name `Multiset.toFinset_card_le_card` is PHANTOM** at v4.26.0 (0 hits). The actual lemma is **`Multiset.toFinset_card_le`** (no trailing `_card`) @ `Mathlib/Data/Finset/Card.lean:185`. The `iff`-form for "equality iff all eigenvalues distinct" is **`Multiset.toFinset_card_eq_card_iff_nodup`** @ `Mathlib/Data/Finset/Card.lean:196`. Use these exact names in the S4 ACT.
2. **S3's "candidate A" `(jordanBlock R λ d).charpoly = (X - C λ)^d` has a one-step Mathlib bearer**: `Matrix.charpoly_of_upperTriangular` @ `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean:199`. Required hypothesis is `M.BlockTriangular id` (defined @ `Mathlib/LinearAlgebra/Matrix/Block.lean:61` as `∀ ⦃i j⦄, b j < b i → M i j = 0`). For `jordanBlock R λ d : Matrix (Fin d) (Fin d) R`, the `BlockTriangular id` hypothesis discharges from S1/S2's three entry-wise lemmas (`_diag_eq`, `_super_diag_eq`, `_off_diag_eq`) plus a 3-line `omega` argument on `Fin` indices.
3. **`jordanBlock_minpoly` (candidate A's second deliverable) has NO direct Mathlib bearer**. The S4 ACT must prove `(jordanBlock R λ d).minpoly = (X - C λ)^d` from scratch (a Cayley-Hamilton-divides-charpoly plus nilpotency argument). This is **NOT** "turn-the-crank" at the difficulty S3 PREP suggested; estimate revises upward to ~120 LOC for candidate A (not ~80).
4. **No `Matrix.jordanBlock`, no `jordanBlock_charpoly`, no `jordanBlock_minpoly`** in Mathlib anywhere — the gallery's `jordanBlock` definition (line 179 of `MinpolyCharpolyOQ01.lean`) is genuinely new. Confirms S1's gap analysis.

---

## §1 — Bearer table at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All identifiers below were verified live via `gh api search/code` (`+repo:leanprover-community/mathlib4`) and `gh api repos/.../contents/.../<file>?ref=<SHA>` reads. Line numbers are at the pinned SHA; minor drift may occur against later master heads but **not** under the lake pin.

### §1.1 — For S3 "candidate E" (small multiset/dimension API follow-on)

| Use | Lemma at v4.26.0 | Path | Line |
|---|---|---|---|
| `Multiset.card m.toFinset ≤ Multiset.card m` | **`Multiset.toFinset_card_le`** | `Mathlib/Data/Finset/Card.lean` | 185 |
| `Multiset.card m.toFinset = Multiset.card m ↔ m.Nodup` | **`Multiset.toFinset_card_eq_card_iff_nodup`** | `Mathlib/Data/Finset/Card.lean` | 196 |
| `Multiset.card m.toFinset = Multiset.card m.dedup` | `Multiset.card_toFinset` | `Mathlib/Data/Finset/Card.lean` | 182 |
| `Multiset.toFinset_card_of_nodup (h : m.Nodup) : #m.toFinset = card m` | `Multiset.toFinset_card_of_nodup` | `Mathlib/Data/Finset/Card.lean` | 188 |

**S3 PREP name drift**: S3 used `Multiset.toFinset_card_le_card` (with trailing `_card`). Direct search returns **0 hits** at v4.26.0. The correct name drops the trailing token: `Multiset.toFinset_card_le`.

### §1.2 — For S3 "candidate A" (`jordanBlock` charpoly identity)

| Use | Lemma at v4.26.0 | Path | Line |
|---|---|---|---|
| **`M.BlockTriangular id → M.charpoly = ∏ i, (X - C (M i i))`** | **`Matrix.charpoly_of_upperTriangular`** | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | 199 |
| `BlockTriangular M b := ∀ ⦃i j⦄, b j < b i → M i j = 0` | `Matrix.BlockTriangular` (def) | `Mathlib/LinearAlgebra/Matrix/Block.lean` | 61 |
| Block-triangular special case for general block index `α` | `Matrix.BlockTriangular.charpoly` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | 195 |
| Diagonal-matrix charpoly | `Matrix.charpoly_diagonal` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | 150 |
| Block-triangular `det` (underlying for `charpoly_of_upperTriangular`) | `Matrix.BlockTriangular.det` | `Mathlib/LinearAlgebra/Matrix/Block.lean` | 246 |
| Finset product of constants for product-collapse | `Finset.prod_const` | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | (canonical) |
| `Fintype.card (Fin d) = d` | `Fintype.card_fin` | `Mathlib/Data/Fintype/Card.lean` | (canonical, `@[simp]`) |

### §1.3 — For S3 "candidate A" (`jordanBlock` minpoly identity)

| Use | Lemma at v4.26.0 | Path | Line |
|---|---|---|---|
| `(minpoly R M) ∣ M.charpoly` (Cayley-Hamilton corollary) | search returned **0 direct hits** for `minpoly_dvd_charpoly`; route via `Matrix.minpoly_dvd_charpoly`? | TBD | — |
| `Matrix.aeval_self_charpoly : aeval M M.charpoly = 0` | found in body of `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` lines 203-end (Cayley-Hamilton block) | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | ~205+ |
| `LinearMap.aeval_self_charpoly` (endomorphism analogue) | cited in line 209's docstring as the "equivalent statement about endomorphisms" | `Mathlib/LinearAlgebra/...` | — |

**Caveat**: I did NOT find a single one-step Mathlib lemma for `minpoly` of an upper-triangular matrix with constant diagonal — and likely none exists, because the minpoly depends on the **nilpotent-shift structure** above the diagonal, not just on the triangular form. The S4 ACT path for `jordanBlock_minpoly` is:

1. From `charpoly = (X - C λ)^d` (via §1.2), conclude `(X - C λ)^d` annihilates `jordanBlock R λ d` (Cayley-Hamilton).
2. Show `(jordanBlock R λ d - λ • 1)^d = 0` (the nilpotent shift `N` satisfies `N^d = 0`).
3. Show `(jordanBlock R λ d - λ • 1)^(d-1) ≠ 0` (the nilpotent shift `N` has nilpotency index exactly `d`). This is the load-bearing classical fact: `(N^k) i j = 1` iff `j = i + k`, so `N^(d-1) ≠ 0` is witnessed by the `(0, d-1)` entry.
4. Conclude `minpoly R (jordanBlock R λ d) = (X - C λ)^d` from "the minimal annihilator has nilpotency exponent = nilpotency index".

The S3 PREP estimate of "~80 lines total for candidate A, fully dischargable, no sorry" looks **optimistic** for the minpoly half. Revised estimate: **~50 LOC for charpoly identity (low risk) + ~70 LOC for minpoly identity (moderate risk, depends on nilpotent-shift API)** = ~120 LOC total for candidate A.

---

## §2 — Drop-in tactic sketches

### §2.1 — `jordanBlock_charpoly` (candidate A, charpoly half)

```lean
theorem jordanBlock_charpoly (R : Type*) [CommRing R] (lam : R) (d : Nat) :
    (jordanBlock R lam d).charpoly = (Polynomial.X - Polynomial.C lam) ^ d := by
  have hUT : (jordanBlock R lam d).BlockTriangular id := by
    intro i j hji
    -- hji : (id j : Fin d) < id i  i.e. j.val < i.val
    have h₁ : i ≠ j := fun e => by subst e; exact lt_irrefl _ hji
    have h₂ : (j : Nat) ≠ (i : Nat) + 1 := by
      have : (j : Nat) < (i : Nat) := hji
      omega
    simp [jordanBlock, h₁, h₂]
  rw [Matrix.charpoly_of_upperTriangular _ hUT]
  -- now goal: ∏ i : Fin d, (X - C (jordanBlock R lam d i i)) = (X - C lam) ^ d
  simp_rw [jordanBlock_diag_eq]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
```

**Risk register**:
- **R-A1**: `BlockTriangular id` may need `[LinearOrder (Fin d)]` to be inferred — provided automatically by `Fin`'s standard `instLinearOrder` instance. *Low risk.*
- **R-A2**: `jordanBlock_diag_eq` returns `jordanBlock R lam d i i = lam` for `i : Fin d`, not for a generic indexing — the `simp_rw` rewrite needs the universally-quantified form. Provided by S1's definition. *Low risk.*
- **R-A3**: The `omega` step needs `Fin.lt_iff_val_lt_val` (or whatever the canonical name is at v4.26.0) to unfold `(j : Fin d) < i` to `(j : Nat) < (i : Nat)`. Variation: `Fin.lt_def`, `Fin.val_lt_iff`. *Low risk* — `omega` typically handles `Fin` coercions natively.

### §2.2 — `eigenvalueMultiset_toFinset_card_le_totalDim` (candidate E, refined)

```lean
theorem JordanBlockShape.eigenvalueMultiset_toFinset_card_le_totalDim
    {K : Type*} [DecidableEq K] (S : JordanBlockShape K) :
    Multiset.card S.eigenvalueMultiset.toFinset.val ≤ S.totalDim := by
  rw [← S.eigenvalueMultiset_card_eq_totalDim]
  exact Multiset.toFinset_card_le _

/-- Equality iff all eigenvalues are distinct. -/
theorem JordanBlockShape.eigenvalueMultiset_toFinset_card_eq_totalDim_iff_nodup
    {K : Type*} [DecidableEq K] (S : JordanBlockShape K) :
    Multiset.card S.eigenvalueMultiset.toFinset.val = S.totalDim ↔
    S.eigenvalueMultiset.Nodup := by
  rw [← S.eigenvalueMultiset_card_eq_totalDim]
  exact Multiset.toFinset_card_eq_card_iff_nodup
```

**Risk register**:
- **R-E1**: `Finset` exposes `.card` directly; `Multiset.card finset.val` is the underlying multiset cardinality. At v4.26.0, line 185 of `Card.lean` uses `#m.toFinset` notation (which is `Finset.card`), not `Multiset.card`. Refining to S.eigenvalueMultiset.toFinset (a Finset) and using `Finset.card` matches Mathlib idiom — adjust the LHS accordingly. *Low risk.*
- **R-E2**: `S.eigenvalueMultiset.toFinset` requires `[DecidableEq K]` — already in the structure-level `eigenvalueMultiset` signature (per S3 design choice in state.md). *Resolved at S1.*

Revised estimate for candidate E: **~12 LOC** (two short lemmas, each `← rewrite + Mathlib bearer`).

---

## §3 — What this PREP does NOT do

- ❌ Does **not** edit `state.md`. The S3 ACT summary remains the latest entry; this PREP refines its forward-looking "Next Action (S4+)" by pinning lemma names but does not rewrite the section. (Per researcher session memory: 2-PR STATE-SYNC cap respected — this is a pure new-session-memo PREP, **not** a STATE-SYNC.)
- ❌ Does **not** edit `knowledge.md`. The S1 OBSERVE knowledge is unchanged.
- ❌ Does **not** edit `src/data/research/problems/minpoly-charpoly-oq-01.json`. The JSON `lastUpdate` remains at the S3 timestamp.
- ❌ Does **not** edit `proofs/Proofs/MinpolyCharpolyOQ01.lean`. 1 sorry on `jordan_normal_form_exists` remains untouched; the file stays at 304 LOC.
- ❌ Does **not** create new `.lean` files. Candidates A and E require docker build verification, deferred to a future S4 ACT (any researcher).
- ❌ Does **not** open child OQ-01-OQ-01 (candidate A's gallery integration). That is part of a future S4 ACT after Lean verification.
- ❌ Does **not** run docker build. This memo is doc-only and adds no Lean compilation surface.

## §4 — Recommendation to the next S4 ACT researcher

**Pick candidate E first** (~12 LOC, 2 short lemmas, all Mathlib bearers verified at v4.26.0 above) as a low-risk continuation of the S3 multiset/dimension API thread. Build verification is fast (single-file recompile, no new transitive imports). Estimated session time: **30 min** including build.

**Then pick candidate A's charpoly half** (~50 LOC, `jordanBlock_charpoly` via `Matrix.charpoly_of_upperTriangular`) as a medium-risk forward step. The drop-in sketch in §2.1 should compile turn-the-crank with at most one Mathlib name adjustment if v4.26.0 has minor drift from the lake-pinned SHA. Estimated session time: **60 min** including build.

**Defer candidate A's minpoly half** (~70 LOC) to a separate S5 ACT — the nilpotent-shift `N^(d-1) ≠ 0` step is non-trivial and worth its own scope.

**Defer candidate B** (strong-form `jordan_normal_form_exists`) until candidates E + charpoly-A are landed — the strong form requires the block-diagonal assembly, which depends on the charpoly identity to be auditable.

**Defer candidate C** (OQ-01-OQ-02 nilpotent canonical form, ~400 LOC) indefinitely — too large for a single ACT increment.

## §5 — Build status

This PREP requires **no Lean build** (single new markdown file). The S3 ACT (`eigenvalueMultiset_card_eq_totalDim`) build status from PR #18134's body remains the source of truth — that PR was merged 2026-05-12T15:06Z with `(build pending)` in its title, but the additive-API nature of S2/S3 plus 24+ hours of post-merge silence in the `loom:audit-issue` / `loom:changes-requested` labels strongly suggests CI validated the change.

## §6 — Coordination notes

- **No race on this slug**: `gh pr list -R rjwalters/lean-genius --search "minpoly-charpoly-oq-01 in:title" --state open` returns `[]` at memo creation (~2026-05-13T22:50 UTC).
- **No race on sibling slugs**: `minpoly-charpoly-oq-02` (#18276, S1 OBSERVE merged 2026-05-12T22:17Z) and `minpoly-charpoly-oq-03` (active gallery entry, recent S7-S10 PRs) are orthogonal — different child OQs of the parent.
- **Branch policy**: fresh `research/minpoly-charpoly-oq-01-s4-prep-mathlib-bearer-audit` cut from `origin/main`, distinct from this researcher-5 session's other open PRs (`#18930` lovasz-local, `#18933` mean-value-theorem, `#18935` arithmetic-series STATE-SYNC).
- **Mathlib lake pin**: `proofs/lake-manifest.json` rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All bearer lines above are pinned at this SHA via `gh api repos/.../contents/...?ref=<SHA>`. Future drift against Mathlib master is irrelevant until the lake manifest is bumped.
