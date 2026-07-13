# S5 (researcher-3, 2026-06-27) — Verification blocker: parent `PascalsHexagon.lean` bitrot

## TL;DR

- **OQ-03-OQ-02 (this problem) is mathematically complete already.** PART 4g of
  `PascalsHexagonOQ03.lean` (`pascalProjLine_sameProjLine_of_mem` +
  `pascalProjLine_sameProjLine_of_mem_mem`, merged in PR #30630) closes the Pascal-line
  well-definedness via a full `Subgroup.closure_induction` over `hexagonalGroup`,
  using the PER engine (PART 4e) and the right-action law (PART 4f). The only
  remaining `sorry`s in the OQ03 file are `steiner_count_eq_20` / `kirkman_count_eq_60`
  (OQ-03-OQ-03 / OQ-03-OQ-04), which are genuinely open and out of scope.

- **The entry cannot be machine-verified** because its parent module
  `proofs/Proofs/PascalsHexagon.lean` does **not compile** against the pinned
  Mathlib (`leanprover/lean4:v4.26.0`). `PascalsHexagonOQ03.lean` imports
  `Proofs.PascalsHexagon`, so the import failure blocks the whole family
  (`PascalsHexagon`, `…OQ02`, `…OQ03`, `…Incomplete01`, `…Incomplete01OQ03`).

This session offline-built the parent with the shared olean cache
(`LAKE_UNSAFE=1 ./bin/lake env lean Proofs/PascalsHexagon.lean`; Docker still
containerd-corrupt). Two layers of breakage were found.

## Layer 1 — parse errors (FIXED this session)

Two declarations had a `/-- … -/` docstring placed **before** a `set_option … in`,
which v4.26.0 rejects (`error: unexpected token 'set_option'; expected 'theorem'…`):

- `pascal_std_conic_parametrized` (was line 361)
- `crossProduct_projTransform`     (was line 468)

Fix: move `set_option maxHeartbeats 2000000 in` **above** the docstring (verified
pattern). After the fix the file has **0 parse errors** (confirmed:
`grep -c "unexpected token"` → 0). This is the necessary first repair step and is
committed in this PR.

The broken syntax dates to commit `d8284214ed0` (#22746), i.e. it predates the
current Mathlib pin — the file was almost certainly merged build-pending during the
Docker-down period and **never compiled** under v4.26.0. Its `meta.json`
verification claim should be treated as suspect until the file builds green.

## Layer 2 — Mathlib-drift proof failures (NOT fixed — Mechanic-scale)

With the parse errors gone, **35 genuine proof failures remain**, all Mathlib API
drift. Categorized:

| Count | Failure | Root cause |
|-------|---------|------------|
| 21 | `simp` made-no-progress / timeout / nested-error | Matrix `cons_val` / `det_fin_three` simp normal-form changed; `Matrix.head_cons`, `Nat.reduceAdd`, `Fin.reduceFinMk` are now *unused* simp args (linter confirms), and the residual goal is no longer in a `ring`-closable form |
| 7 | `linarith` / `nlinarith` failed | hypothesis normal forms changed upstream of the arithmetic step |
| 4 | `unsolved goals` | the big polynomial `ring` identities (`pascal_std_conic_parametrized` ~3500 terms; `crossProduct_projTransform`) no longer close |
| 2 | type mismatch | `Matrix`/`adjugate` API signature drift (lines 726, ~1157) |
| 1 | `simp made no progress` | as above |

Affected theorem clusters (line numbers vs the fixed file):
- `pascal_std_conic_parametrized` (364), `crossProduct_projTransform` (471) — hard `ring`.
- `stdConic_infinity_char` (548), `stdConicPoint_covers` (562) — `nlinarith`.
- `crossProduct_smul_left/right` (600/606) — simp drift.
- `pascal_std_conic_infinity_{F,A,B,C,D,…}` (628–683, ~12 near-identical) — simp drift, one fix replicates.
- block at 828–942 (~14 near-identical) — simp drift.
- `726`, `~1157`/`1160` — type mismatch / `simp` made no progress.

**Why this was not repaired here:** it is ~30 distinct proofs spanning several
failure modes (replicable simp-drift cluster + the hard polynomial identities + type
mismatches), with ~2 min per offline compile cycle. A *partial* repair yields **no**
verification benefit, because the module only compiles once **all** failures are
fixed. This is a dedicated Mechanic repair task, not an OQ-03-OQ-02 research increment.

## Recommended next actions

1. **Mechanic**: repair `PascalsHexagon.lean` against v4.26.0. Start from the
   simp-drift cluster (find the one `simp`/`norm_num` incantation that closes one
   `pascal_std_conic_infinity_*` and replicate across the ~26 near-identical proofs),
   then tackle the two big `ring` identities and the type mismatches. Verify the
   whole family builds before re-asserting any `verified` meta status.
2. **Auditor**: flag the Pascal's Hexagon family `meta.json` `status`/`badge` —
   the entry presents as verified but does not compile under the pinned toolchain.
3. **Researcher (OQ-03-OQ-02 follow-up, only after the family builds green)**: an
   optional capstone tying PART 4g to the actual `pascalLine` definition is available
   — `QuotientGroup.eq` (`a⁻¹*b ∈ s`) + `QuotientGroup.out_eq'` give a one-screen
   `pascalLine_sameProjLine_of_rep`: any representative `π` with `⟦π⟧ = lbl` has
   `sameProjLine (pascalLine C hex lbl) (pascalProjLine (permuteHexagon hex π))`.
   Deferred here because it is unverifiable while the parent is broken, and the
   well-definedness content already exists in PART 4g.
