# Session 2026-05-16 S2-A ACT — Variant A-ℤ signed CellComplex (200 LOC, 0 axioms, 0 sorries)

**Mode**: FRESH (S2-A ACT)
**Researcher**: researcher-10
**Outcome**: ACT — SignedCellComplex structure + signed_interior_doors_sum_zero
theorem shipped in 200 LOC with 0 axioms and 0 sorries, Docker-verified.

## 1. Pick-time context

Pre-claim probe at 2026-05-16 ~04:25 UTC (current time):

- Pool: 23 available, 538 in-progress, 1675 completed, 24 graduated.
- claim-random returned `sperner-ndim-mathlib-oq-01-oq-04`.
- Open same-slug PRs at claim: **0** (verified via
  `gh pr list --repo rjwalters/lean-genius --search "sperner-ndim-mathlib-oq-01-oq-04 in:title" --state open`).
- Predecessor PRs (this slug):
  - **#18325** (S1 OBSERVE, researcher-3, 2026-05-12, MERGED)
  - **#19243** (S2 PREP, researcher-8, 2026-05-15 22:57Z drain wave, MERGED ~10h prior to this ACT) — paste-ready Variant A-ℤ skeleton, 7 Mathlib bearers pinned, ZMod-2 vacuity diagnosis.
- Lake-pinned Mathlib SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), **unchanged since S2 PREP** (≥10h pin stability).

**Decision per memory feedback `_postship_pivot_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act.md`**:
0 open same-slug PRs + peer PREP merged ≥60min ago + §6 GREEN gate + §4
drop-in skeleton + paste-ready Variant A-ℤ recipe → execute the ACT
(rather than release-exit or stage another PREP).

## 2. Bearer drift recheck (2026-05-16T04:25Z)

All bearers verified at lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Declaration | Path | S2 PREP line | This recheck line | Drift |
|---|---|---|---|---|---|
| 5 | `ZMod.neg_eq_self_mod_two` | `Mathlib/Data/ZMod/Basic.lean` | 944 | 944 | 0 |
| 6 | `Finset.prod_involution` (→ `sum_involution` via `@[to_additive]`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 672 | 673 | +1 (header context, same SHA = same bytes) |
| 7 | `ZMod.natCast_eq_one_iff_odd` | `Mathlib/Data/ZMod/Basic.lean` | 762 | 762 | 0 |

Bearers 1-4 (`ZMod : ℕ → Type` and instances) verified-in-S2-PREP and
unchanged at this SHA. 0 substantive drift; bearer pin stability holds.

## 3. The Variant A-ℤ implementation

### 3.1 Structural definition

```lean
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0
```

Three new fields beyond `CellComplex V d`:
- `sign : Simplex → Fin (d + 1) → ℤ` (per-facet ℤ-valued sign);
- `sign_pm_one : sign s k = 1 ∨ sign s k = -1` (±1 valuation);
- `sign_adj : adj s k = some (s', k') → sign s k + sign s' k' = 0`
  (genuine "negatives" coherence).

### 3.2 Supporting lemmas and definitions

- `sign_ne_zero (K : SignedCellComplex V d) (s : K.Simplex)
  (k : Fin (d + 1)) : K.sign s k ≠ 0` — immediate from `sign_pm_one`.
- `signedAdjMap (K : SignedCellComplex V d)
  (p : K.Simplex × Fin (d + 1)) : K.Simplex × Fin (d + 1)` — lift of
  the parent's private `adjMap`. At an interior facet, follow the
  adjacency; at a boundary facet, stay put.
- `signedDoorCount (K : SignedCellComplex V d) (c : V → Fin (d + 1))
  : ℤ` — sum of facet signs over door facets.
- `door_transfer_signed_one_dir` (private, ~8 LOC) — re-proves the
  parent's private `door_transfer_one_dir` directly from the public
  `adj_vertices` axiom (no parent surgery needed).

### 3.3 Main theorem

```lean
theorem signed_interior_doors_sum_zero (K : SignedCellComplex V d)
    (c : V → Fin (d + 1)) :
    ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0
```

**Discharge**: `Finset.sum_involution` applied with
`g := fun (p : K.Simplex × Fin (d + 1)) (_hp : p ∈ S) => signedAdjMap K p`.

Four obligations, dispatched as named cases:
- `case cancel` (`hg₁ : f a + f (g a ha) = 0`): direct from `sign_adj`
  after `cases hadj_eq : K.adj p.1 p.2`.
- `case fpf` (`hg₃ : f a ≠ 0 → g a ha ≠ a`): from `K.adj_ne` after the
  same `cases hadj_eq`. (The `f a ≠ 0` hypothesis is automatic since
  signs are ±1, never 0.)
- `case gmem` (`g a ha ∈ s`): two parts — door predicate transfer via
  `door_transfer_signed_one_dir` (using `K.adj_vertices`), and
  non-`none` adjacency via `K.adj_symm`.
- `case invol` (`g (g a ha) (g_mem a ha) = a`): from `K.adj_symm` after
  the `cases`/`simp` chain.

The proof structure closely mirrors the parent's `interior_doors_even`
(`SpernerNDimMathlib.lean:368-407`); we replace the parity-of-cardinality
conclusion with the additive-zero conclusion, using `Finset.sum_involution`
in place of `even_card_fpf_invol`.

## 4. Why ℤ, not `ZMod 2`?

The S1 OBSERVE skeleton (researcher-3, PR #18325) proposed a
`ZMod 2`-valued sign with `sign_adj : sign s k + sign s' k' = 1`,
intending "opposite signs". The S2 PREP (researcher-8, PR #19243)
diagnosed this as **mathematically vacuous**:

- `ZMod.neg_eq_self_mod_two` (`Mathlib/Data/ZMod/Basic.lean:944`,
  `@[simp]`): `∀ a : ZMod 2, -a = a`. Therefore "opposite signs"
  (`sign s k = -sign s' k'`) degenerates to "identical signs"
  (`sign s k = sign s' k'`).
- The `sum = 1` coherence then degenerates to "differs-on-adjacency",
  a `Bool`-valued labeling with no orientation information.
- Under `Finset.sum_involution`, the cancellation hypothesis requires
  `f a + f (g a ha) = 0`. Pairs satisfying `sign s k + sign s' k' = 1`
  do **not** cancel — they sum to `1`.
- The classical signed-chain boundary `∂σ = ∑ (-1)^i ∂_i σ` lives
  over ℤ; in `ℤ/2` it collapses to the parent's unsigned boundary.

The Variant A-ℤ correction (ℤ-valued signs with `sum = 0`) is
genuinely orientation-preserving and directly compatible with
`Finset.sum_involution`'s additive cancellation.

## 5. Build verification

`./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlibOQ01OQ04`
→ build clean (cache download + Lake compile, no Lean errors).
This builds the new file transitively alongside its parent
`Proofs.SpernerNDimMathlib` (~521 LOC), so the build also serves as a
v4.26.0 buildability confirmation for the parent (the S2 PREP §4 had
flagged this as "UNKNOWN; pre-edit Docker baseline required"). **Parent
clean at v4.26.0 lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.**

## 6. Files modified

| File | Status | Notes |
|---|---|---|
| `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` | NEW (200 LOC) | Main deliverable. 0 axioms, 0 sorries. |
| `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/meta.json` | NEW | Gallery entry; 3 theorems / 3 definitions metadata. |
| `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/index.ts` | NEW | Gallery TS shim, mirrors sibling oq-01 structure. |
| `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/annotations.json` | NEW | Empty `[]` placeholder. |
| `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json` | NEW | Research-side problem JSON (phase: COMPLETED). |
| `research/problems/sperner-ndim-mathlib-oq-01-oq-04/state.md` | NEW | Phase head + S2-A ACT narrative. |
| `research/problems/sperner-ndim-mathlib-oq-01-oq-04/knowledge.md` | NEW | Summary + resolved approach + recent sessions index. |
| `research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-16-s2a-act-signed-cellcomplex.md` | NEW (this file) | Session memo. |

**Net delta**: +1 Lean file (200 LOC, 0 axioms, 0 sorries) + 4 gallery
files + 3 research-state files + 1 session memo. **No edits** to the
parent `SpernerNDimMathlib.lean` or any sibling file.

## 7. Conflict-free guarantees

- **0 open same-slug PRs at claim time** (verified via `gh pr list`).
- **No edits** to `proofs/Proofs/SpernerNDimMathlib.lean` (parent),
  `proofs/Proofs/SpernerNDimMathlibOQ01.lean`, or
  `proofs/Proofs/SpernerNDimMathlibOQ02.lean` (siblings).
- The new file lives at a slug-specific path
  (`proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean`) created in this PR.
- The gallery / research / sessions / state files all live under
  `…/sperner-ndim-mathlib-oq-01-oq-04/…` (slug-specific directories
  created in this PR).
- The research-side `currentState` is owned by this PR; no concurrent
  STATE-SYNC PR for this slug exists.

## 8. Honesty assessment

This session:

- **Implements** the S2 PREP's recommended Variant A-ℤ skeleton in 200
  LOC. The structural definition is genuinely new (no equivalent
  `SignedCellComplex` over ℤ exists in either Mathlib or the prior
  gallery).
- **Discharges** the single `signed_interior_doors_sum_zero` sorry
  cleanly via `Finset.sum_involution`. The proof mirrors the parent's
  established `interior_doors_even` structure modulo the additive-vs-
  parity conclusion. The book-keeping is ~30 LOC, well within the S2
  PREP's estimated ~30-40 LOC range.
- **Does not claim** Tucker's lemma, Borsuk-Ulam, or any chain-complex-
  level result. Those remain explicit follow-up sessions (S2-B / S2-C /
  S2-D).
- **Confirms** parent buildability at the lake-pinned Mathlib v4.26.0
  SHA (resolving the S2 PREP §4 "UNKNOWN" caveat).

The mathematical contribution is structural / foundational (it provides
the right substrate for signed equivariant Sperner / Tucker / Borsuk-Ulam
follow-ups) rather than a deep new theorem in its own right. The
discharge is a 30-LOC application of an existing Mathlib hammer
(`Finset.sum_involution`); the novelty is in the structural choice (ℤ
over `ZMod 2`) justified by the vacuity diagnosis.

## 9. Time budget

- Pick + bearer recheck + parent buildability check: ~10 min.
- Lean file authoring (200 LOC, paste-ready from S2 PREP): ~10 min.
- Gallery / research / state authoring: ~15 min.
- Docker build (cold cache + parent + new file): ~5-15 min.
- PR creation: ~5 min.

**Total**: ~45-60 min (within the S2 PREP's estimated ~45-90 min budget).

## 10. Follow-up sessions (NOT bundled into S2-A)

- **S2-B (Mathlib bridge)**: embed `SignedCellComplex` into Mathlib's
  `AlternatingFaceMapComplex` over `ModuleCat ℤ` (~80 LOC, separate
  session).
- **S2-C (Tucker scaffold)**: define `AntipodalCellComplex` (vertex-
  level involution `ι : V → V` with `ι_involutive` + `ι_no_fp`) and
  state Tucker's lemma over it (~120 LOC, 2 statement-only sorries
  expected).
- **S2-D (Borsuk-Ulam bridge)**: connect antipodal Tucker to the
  topological Borsuk-Ulam statement.
