# Session 21 — S2-D ACT: genuine ℓ² lift, VERIFIED (researcher-3, 2026-07-23)

**Mode.** ACT (`.lean` + JSON + docs). **Outcome: COMPLETED, 0-axiom VERIFIED.**

## 1. What shipped

Executed the S2-D recipe from the Session-20 doc §4 (with v4.31 API
adjustments) and **Docker-verified the whole file** — the sole reason the
problem was `blocked` was that the Session-20 S2-C transport core had never
been built (2026-06-13 Docker blackout). Docker is back up on the host.

Added to `proofs/Proofs/ShapleyFolkmanOQ01.lean` (namespace
`ShapleyFolkmanOQ01`, before `end`):

| Decl | Role |
|------|------|
| `ιN (N)` | injective linear embedding `EuclideanSpace ℝ (Fin N) →ₗ[ℝ] lp (fun _:ℕ => ℝ) 2`, `∑ i, lp.lsingle 2 i.val (v i)` |
| `ιN_apply_coord` | `(ιN N v) j.val = v j` — coordinate-preserving |
| `ιN_injective` | injectivity (one-coordinate evaluation) |
| `shapley_folkman_excess_unbounded_in_lp` | **capstone**: `∀ K, ∃ N (D : Decomposition … over ℓ² subsets), D.excessIndices.card > K` |

New import: `Mathlib.Analysis.Normed.Lp.lpSpace`.

**Build:** `docker-build.sh Proofs.ShapleyFolkmanOQ01` at
`leanprover/lean4:v4.31.0` — `✔ Built (8577 jobs)`, 0 sorries, 0 axioms.
Only warnings are pre-existing `EuclideanSpace.single_apply` deprecations at
lines 257/259 (unrelated to this session, in `tight_excess_count`).

## 2. Mathematical content

`shapley_folkman_excess_unbounded_in_lp` takes the finite-dimensional
tightness family `S i = {0, eᵢ}` with target `x = ½ ∑ eᵢ`
(whose every decomposition has `excessIndices.card = N`,
`tight_excess_count`) and pushes it forward along the injective embedding
`ιN` via the `Decomposition.map` transport core (S2-C). Because `ιN` is
injective, `map_excessIndices_card_of_injective` gives that the image
decomposition `(midpointDecomp (K+1)).map (ιN (K+1))` still has excess card
`= K+1 > K`. The image family lives in the **genuine** infinite-dimensional
Hilbert space `ℓ² = lp (fun _:ℕ => ℝ) 2`.

Since `Module.finrank ℝ ℓ² = 0`, this simultaneously (i) refutes the literal
`card ≤ Module.finrank` parent bound in ℓ² and (ii) shows no *fixed finite*
bound survives. Combined with the finite-dim results (S2-A, S2-B1), the
negative answer to OQ-01 is now machine-verified end to end: the
`FiniteDimensional` hypothesis of `shapley_folkman` is essential.

## 3. v4.31 API notes (recipe drift from v4.26.0 pins)

- **`lp.single_apply_self` / `lp.single_apply_ne` need `(E := fun _:ℕ => ℝ)`.**
  The `E : α → Type*` family is a higher-order metavariable that cannot be
  inferred from the value argument `v i : ℝ` (unifying `?E i =?= ℝ` is
  ambiguous); the goal's concrete `lp` type does not back-propagate through
  `exact`. Supplying `E` explicitly fixes it.
- **`PiLp.add_apply` / `PiLp.smul_apply` are still `rfl`** and fire; the
  `map_add'`/`map_smul'` fields close with `rw [← Finset.sum_add_distrib];
  Finset.sum_congr … rw [PiLp.add_apply, map_add]` and the `smul` analog. The
  original recipe's one-line `simp only [PiLp.add_apply, map_add,
  Finset.sum_add_distrib]` left `X = X` unclosed under v4.31 — the explicit
  `sum_congr` form is robust.
- **EuclideanSpace coordinate access displays as `v.ofLp i`** (WithLp
  refactor) but behaves as `v i`.
- `ιN_apply_coord` closes via `simp only [ιN, LinearMap.coe_mk,
  AddHom.coe_mk, lp.coeFn_sum, Finset.sum_apply]` then
  `Finset.sum_eq_single j` + `single_apply_self`/`single_apply_ne` +
  `Fin.val_injective` — no `Fintype.sum_ite_eq` needed (that route hit a
  stuck `AddCommMonoid` metavariable).

## 4. Race-safety log

- Worktree reaped once mid-session by the janitor (before any edit);
  recreated at `/Volumes/Stripe/lean-genius/researcher-3` off `origin/main`.
- Branch `research/shapley-folkman-oq-01-s2d-lp2-lift` off `origin/main`
  (feature/researcher-3 was 3605 commits behind — not used).
- Pre-PR: no open OQ01 PRs; `check-superseded.sh` run before opening.

## 5. Status

**COMPLETED — OQ-01 answered NO, machine-verified (0 axioms, 0 sorries).**
No follow-up OQ generated: the negative answer is complete, and the only open
direction (positive Aumann/Lyapunov analog) needs new Mathlib measure-theory
infrastructure and belongs to a separate problem, not a child of this OQ.
