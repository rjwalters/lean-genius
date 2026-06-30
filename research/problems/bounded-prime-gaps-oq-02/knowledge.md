# bounded-prime-gaps-oq-02 — knowledge

Elliott–Halberstam conjecture, formalized axiom-free as a level-of-distribution
hierarchy (`Proofs/BoundedPrimeGapsOQ02.lean`). Verified: 0 axioms, 0 sorries,
0 native_decide. EH itself is NOT axiomatized — the discrepancy functional and its
structural properties enter only as per-theorem hypotheses.

## Session 2026-06-27 (researcher-1) — phase ACT, SOLVED entry, looked outward

Added the **finite dyadic chain** generalization of the two-band ascent:

- `EHAtLevel_discrepancySum_up_chain` (abstract weight `f`): for a monotone level
  sequence `L : ℕ → ℝ`, EH at base `L 0` + an EH-type bound on every consecutive band
  `L k → L (k+1)` ⟹ EH at every `L n`. Proof: induction on `n`, iterating the
  single-band `EHAtLevel_discrepancySum_up` via `hmono (Nat.le_succ k)`.
- `EHAtLevel_vonMangoldt_up_chain`: the genuine specialization to `vonMangoldtWeight`
  (matching the file's abstract+genuine pairing pattern).

The `n = 2` case recovers `EHAtLevel_discrepancySum_up_split`. This is the
arbitrarily-many-blocks form of dyadic decomposition of the modulus range — the genuine
analytic strategy uses `≍ log x` blocks, not two, so the prior two-band lemma was only
the first nontrivial instance.

File (after session 2026-06-27): 585 lines, 34 theorems, 12 defs, 0 axioms/sorries.

## Session 2026-06-28 (researcher-3) — explicit equipartition chain

Instantiated the abstract finite chain at the explicit arithmetic level sequence
`L k = θ₀ + k·δ` (`δ ≥ 0`) — the "explicit dyadic chain" flagged as an outward
direction:

- `EHAtLevel_discrepancySum_up_arith` (abstract weight): EH at base `θ₀` + EH-type
  bound on each equal step `θ₀ + k·δ → θ₀ + (k+1)·δ` ⟹ EH at `θ₀ + n·δ` for all `n`.
  `Monotone L` is discharged from `δ ≥ 0`. Choosing `δ = (θ-θ₀)/n` reaches any target
  `θ ≥ θ₀` in `n` equal blocks — the concrete equipartition form.
- `EHAtLevel_vonMangoldt_up_arith`: the genuine von-Mangoldt specialization.

GOTCHA: stating hband with `θ₀ + (k+1)*δ` elaborates to `θ₀ + (↑k+1)*δ`, but the
chain lemma's `L (k+1)` is `θ₀ + ↑(k+1)*δ`. Bridge when applying the chain:
`refine … (fun k A hA => ?_); simpa only [Nat.cast_succ] using hband k A hA`.

File now: 623 lines, 36 theorems, 12 defs, 0 axioms/sorries.

## Session 2026-06-28 (researcher-1) — target-θ wrapper (packaged equipartition)

Closed the "target-θ wrapper" outward direction flagged in the prior session: package
the arith chain so the caller names the *endpoint* `θ` and the block count `n`, with the
`θ₀ + n·δ = θ` algebra discharged internally (`δ := (θ-θ₀)/n`).

- `EHAtLevel_discrepancySum_up_target` (abstract weight `f`): `n ≥ 1`, `θ₀ ≤ θ`, EH at base
  `θ₀`, plus an EH-type bound on each of the `n` equal sub-bands `θ₀+k·δ → θ₀+(k+1)·δ`
  ⟹ EH at the *exact* target `θ` (not the cosmetic `θ₀+n·δ`). Proof: `set δ := (θ-θ₀)/n`,
  derive `hδ ≥ 0` from `θ₀ ≤ θ` (div_nonneg + positivity), apply the arith chain at `n`,
  then `rwa [heq]` with `heq : θ₀ + n·δ = θ`.
- `EHAtLevel_vonMangoldt_up_target`: genuine von-Mangoldt specialization (one-line
  delegation).

GOTCHA: `heq` proof — `rw [hδdef]; field_simp` does NOT close `θ₀ + n·((θ-θ₀)/n) = θ`; it
clears the division to leave `θ₀ + (θ-θ₀) = θ`, which then needs a trailing `ring`. So
`by rw [hδdef]; field_simp; ring`. `field_simp` picks up `hn' : (↑n:ℝ) ≠ 0` from context
(supply it explicitly via `Nat.cast_ne_zero.mpr hn.ne'`).

File now: 661 lines, 38 theorems, 12 defs, 0 axioms/0 sorries. Verified offline
`lake env lean` EXIT 0; both new theorems `#print axioms` = {propext, Classical.choice,
Quot.sound} only.

## Verification gotchas (2026-06-27 session)
- Docker build infra was DOWN (containerd `meta.db` I/O error). Verified instead via
  `cd proofs && LAKE_UNSAFE=1 lake env lean Proofs/BoundedPrimeGapsOQ02.lean` (EXIT 0).
  Local oleans live at `proofs/.lake/packages/mathlib/.lake/build/lib/lean/`; toolchain
  v4.26.0 matches local `lean`.
- The remote `feature/researcher-1` branch is badly stale/divergent (501 commits, and the
  BPG files are DELETED on it). PR from a fresh branch off `origin/main` instead.
- The worktree's checked-out file was an OLDER version than `main` (main already had the
  whole `vonMangoldtWeight` section). Re-apply edits onto main's current file, not the
  worktree's stale copy.

## Possible further outward directions (not done)
- Bridge the band-bound hypothesis form to `EHAtLevel (fun _ x => discrepancyBand …) ·`
  to unify it with the convex-cone lemmas.
- Finset/list-indexed (non-ℕ) chain version.
- A target-θ wrapper `EHAtLevel … θ` that picks `δ = (θ-θ₀)/n` internally and proves
  `θ₀ + n·δ = θ` (the arith chain `EHAtLevel_discrepancySum_up_arith` already gives the
  content; this would just package the algebra).
