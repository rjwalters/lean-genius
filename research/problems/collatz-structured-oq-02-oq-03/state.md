# Research State: collatz-structured-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-08T00:00:00Z
**Iteration**: 9

## Iteration 9 (researcher-4, 2026-07-08, VERIFIED via docker-build, PR #36029)
Added two decide-FREE Part III structural lemmas for the orbit minimum, each the
full-trajectory generalization of an existing `k ≤ 1` fact:
- `colMin_le_iterate (n k) : colMin n ≤ collatz^[k] n` — the orbit minimum bounds
  EVERY orbit value (not just the start `n`); one line `Nat.sInf_le ⟨k, rfl⟩`,
  generalizes `colMin_le_self` (k=0).
- `colMin_le_colMin_iterate (n k) : colMin n ≤ colMin (collatz^[k] n)` — the orbit
  minimum is non-increasing along the whole trajectory; induction on k via
  `colMin_le_collatz`, generalizes `colMin_le_collatz` (k=1).
Together: `colMin n ≤ colMin (collatz^[k] n) ≤ collatz^[k] n`. File 1801→1820 lines,
0 sorries, 1 axiom (`tao_2019`) unchanged; NO `decide`/`native_decide`, so first-try
green docker-build (7743 jobs, exit 0) — no exit-135 risk (contrast iter 8's decide
crashes). meta.json synced (theoremCount 64→66).

## Iteration 8 (researcher-9, 2026-07-08, VERIFIED via docker-build)
Added `autoDropCert_colMin_lt`: the general bridge from the Part VII turnkey certificate
to the Part III orbit minimum. Any residue class `r (mod 2^b)` accepted by `autoDropCert`
now yields `colMin n < n` for all `n ≡ r (mod 2^b)` in one line — composing
`autoDropCert_attainsBelow` (Part VII) with `attainsBelow_colMin_lt` (Part III). This
replaces the last hand-written layer of Part III: the per-residue `mod_*_colMin_lt`
corollaries (`mod_sixteen_three_colMin_lt`, `mod_thirtytwo_eleven_colMin_lt`,
`mod_onetwentyeight_seven_colMin_lt`, …) are now uniform, needing no trajectory chase.
File 1783→1801 lines, 0 sorries, 1 axiom (`tao_2019`) unchanged; new lemma introduces no
axiom and no `decide`.

**Build note:** `docker-build` verified the lemma (7743 jobs). Inline `example`s that added
extra `autoDropCert _ _ = (by decide)` calls reproducibly crashed the Lean kernel with a
line-less exit 135 (SIGBUS, 128+7) even at concurrency 0 — the pristine file already carries
several heavy `autoDropCert` kernel `decide` reductions and one more tips total kernel memory
over the edge. Dropped the illustrative examples; the general lemma builds cleanly. (Distinct
from volume-corruption 135, which self-heals on retry — this one was deterministic and cured
only by removing the extra `decide`.)

## Previous Focus (Iteration 7)
ACT — completed de-risk **component (1)**: the residue-drop engine now AUTO-DERIVES the
parity vector from `(b, r)` for power-of-two moduli (`deriveVec`/`autoDropCert`), so the
caller supplies only the modulus exponent and residue, not a hand-built vector. Built
offline (Docker unresponsive), REAL_EXIT=0, axiom-free (`propext, Quot.sound`; kernel
`decide`, not `native_decide`).

## Active Approach
Deep result stays a single documented axiom (`tao_2019`); the elementary residue-dynamics
core is now a fully turnkey decidable engine. `deriveVec` simulates the affine pair from
`(2^b, r)` reading each forced parity off the constant `d`; `affValidB_deriveVec` proves
the derived vector is unconditionally valid; `autoDropCert_attainsBelow` certifies a
residue family in one `by decide`.

## Attempt Count
- Total attempts: 6
- Approaches tried: statement + explicit families; n≡1 mod 4 family; colMin bridge;
  mod-16/32/128 refinements; general density lemma + decidable `dropCert` (vector supplied);
  **auto-derived parity vector `deriveVec`/`autoDropCert` (this session — no vector supplied)**

## Blockers
- Full proof of Tao (2019) remains BLOCKED (3-adic transport/concentration + Fourier; >> 1000 lines).
- Build host: Docker `docker info` hangs (unresponsive). Verified offline via
  `LAKE_UNSAFE=1 ./bin/lake env lean` against the worktree's cached Mathlib oleans (REAL_EXIT 0).
- **Worktree hazard**: a hard reset (`git reset --hard HEAD`) ran mid-session and wiped
  uncommitted edits. Commit immediately after editing in this worktree.

## Next Action
Remaining genuine lever: a *uniform* drop theorem (one inductive statement covering all
determined classes through the `3^a < 2^b` criterion), then Terras/Korec natural-density-1
stopping time toward Tao's bound. Further dyadic density levels (mod 256+) are diminishing
returns. Tao axiom stays BLOCKED.

## Deliverable (this session)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` — Part VII added (1468→1568 lines, 52→54
theorems, 10→12 defs, 1 axiom unchanged, 0 sorries):
- `deriveVec` (auto-derives the residue-determined parity vector from `(b, r)`);
- `affValidB_deriveVec` (the derived vector is unconditionally a valid `AffValid` certificate);
- `autoDropCert` / `autoDropCert_attainsBelow` (one-line residue-family certification from
  `(b, r)` alone), validated on `n≡3 (mod 16)`, `n≡11 (mod 32)`, `n≡7 (mod 128)`.
Verified REAL_EXIT 0 offline; new theorems axiom-free (`propext, Quot.sound`).
