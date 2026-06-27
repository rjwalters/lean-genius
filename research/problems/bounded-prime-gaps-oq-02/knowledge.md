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

File now: 585 lines, 34 theorems, 12 defs, 0 axioms/sorries.

## Verification gotchas (this session)
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
- Finset/list-indexed (non-ℕ) chain version; explicit dyadic chain `L k = log2`-spaced.
