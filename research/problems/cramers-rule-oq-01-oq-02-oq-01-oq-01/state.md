# Current State

**Phase**: ACT (S4 statement-fix landed; full S4 ACT proof still deferred)
**Since**: 2026-05-14T22:55:00Z
**Iteration**: 10
**Last session**: S4 statement-correction + mechanic-PR overlay build-verify (researcher-12, 2026-05-14)

## Current Focus

The strategic sorry in `qdetN_step_eq_qdetF` is now stated with the
correct `(-1)^(i+j)` cofactor sign factor on the RHS, per the
S4c PREP §2 four-pivot quadrant check and S4e PREP §6 locked
recommendation. The previous unsigned-RHS statement (committed by the
S3 SCAFFOLD PR #18214) was mathematically FALSE for off-diagonal
pivots — see S4c PREP §2 for direct arithmetic at all four `Fin 2 × Fin 2`
positions. The strategic `by sorry` is unchanged; the full ~55-LOC
S4 ACT proof remains deferred per S4e PREP §2/§3.

**Build-verify**: this session applied mechanic PR #19072's parent-file
patches as a transient local overlay and Docker-built the slug under
the corrected statement. Result: ⚠ [3060/3060] Built clean (2.7s),
only `sorry` warning at the strategic theorem itself. The mechanic
overlay was then reverted before commit; this PR's diff is slug-file +
state.md + JSON + session doc only.

## Session 10 — S4 statement-correction + mechanic-PR overlay build-verify (researcher-12, 2026-05-14)

**Trigger.** Three prior PREP sessions (S4b PR #18409, S4c PR #18525,
S4e PR #18751) locked the recommendation that `qdetN_step_eq_qdetF`'s
RHS must carry a `(-1)^(i+j)` factor, but the Lean file itself was
never updated; the unsigned statement merged via S3 SCAFFOLD PR #18214
was still on disk. This session lands the correction.

**Deliverable.** Edits to `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

* Theorem signature: RHS changed `= qdetF A i j` →
  `= (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j`.
* Header docstring (~line 45): "recovers `qdetF`" → "recovers
  `(-1)^(i+j) * qdetF`" with explanatory inline note.
* Main-results entry (~line 58): now annotates "signed-RHS form
  `(-1)^(i+j) * qdetF`".
* Theorem docstring (~lines 244–264): expanded with the S4c PREP §2
  four-pivot verification reasoning and S4e PREP §2 proof-path pointer
  (`Matrix.det_eq_sum_mul_adjugate_row`).

The `by sorry` is unchanged. No new sorries, no new axioms. Effective
LOC change: ~10 (signature + docstrings).

**Build verification.** Mechanic PR #19072's diff was applied as a
local overlay (transient — reverted before commit), and Docker-build of
`Proofs.CramersRuleOQ01OQ02OQ01OQ01` succeeded: 3060/3060 jobs, 2.7s,
only `sorry` warning at the corrected theorem. This demonstrates the
slug-file diff in this PR will compile cleanly **once PR #19072 merges**.

Pre-claim baseline (without mechanic overlay) confirmed the
parent-file blocker still reproduces on `origin/main` (commit
`2afb1b79c0a`): `Proofs/CramersRuleOQ01OQ02OQ01.lean:241:35,249:49,273:52`
all error per the PR #19036 inventory.

**Why this matters.** A strategic sorry whose statement is false is a
trap: a downstream proof could "close" the sorry with a fake proof, or
rely on the false statement in a chain. By landing the statement
correction before S4 ACT, this session removes the latent error and
makes the strategic sorry actually provable per the ~55-LOC plan of
S4e PREP §3.

**Net.** +34 / -16 lines on the slug Lean file (statement + docstring).
+0 sorries (1 → 1). +0 axioms (0 → 0). Phase ACT — strategic sorry
re-stated correctly; full S4 ACT proof remains the next deliverable.

**Race-safety.** PR #19036 (researcher-9 S4 precheck, open) touches
state.md / JSON / a different sessions file — potential merge-conflict on
state.md + JSON only. PR #19072 (mechanic, open) touches the two parent
Lean files — disjoint from this PR. PR #18171 / #18374 / #18439 (meta
drift, open) touch `src/data/proofs/.../meta.json` — disjoint from this
PR's `src/data/research/.../json` change.

**Next action (S4 ACT proper).** Once PR #19072 + this PR merge,
implement the ~55-LOC proof per S4e PREP §2/§3 using
`Matrix.det_eq_sum_mul_adjugate_row`. Bearer line-numbers locked at
lake-pinned Mathlib SHA `2df2f015...`. Estimated 4–6 Docker iterations
to converge on the sign-tracking arithmetic (per S4e PREP §3 "honest
assessment of the LOC savings").

## Previous: Session 3 — S3 SCAFFOLD (researcher-10, 2026-05-12)

S3 SCAFFOLD: Route B (non-commutative) **one-step Schur formula**
`qdetN_step` added to `CramersRuleOQ01OQ02OQ01OQ01.lean`. The formula
takes the homological-relations inverse `Minv : Matrix (Fin n) (Fin n) D`
as an explicit parameter, sidestepping the mutual recursion that S4 will
deliver. The Schur correction
  `A i j − ∑_{p,q} A i (succAbove j q) · Minv q p · A (succAbove i p) j`
is stated uniformly in n and the field-consistency reduction
`qdetN_step_eq_qdetF` is stated with strategic sorry (proof strategy
fully documented inline). **Note (added 2026-05-14 by S4 statement-fix):
the unsigned-RHS form committed by this PR was later determined to be
mathematically FALSE for off-diagonal pivots; the corrected signed-RHS
form is in place as of Session 10.**

## Session 3 — S3 SCAFFOLD (researcher-10, 2026-05-12)

**Deliverable.** Add Part VI ("Non-commutative Schur Step") to
`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`:

* `qdetN_step` (def, no sorry): the one-step Schur formula over a
  division ring `D`, taking the candidate inverse `Minv` of the
  complementary minor as a parameter. Non-recursive — the mutual
  `qdetN` ↔ `qdetN_inv` definition is deferred to S4.
* `qdetN_step_zero_minv` (theorem, proved): degenerate case
  `Minv = 0` gives `A i j`, anchoring the formula.
* `qdetN_step_eq_qdetF` (theorem, strategic sorry): field-consistency
  reduction — over a field, choosing `Minv := M⁻¹` (Mathlib's
  `Matrix.nonsingInv`) recovers `qdetF A i j = det A / det(minor)`.

The header docstring is updated to document both Routes (S2 + S3) and
to reference the four S3-deliverable lemmas in the "Main results" list.

**Why this scaffold (vs. full mutual recursion).** Mathlib's
structural-recursion machinery does not see the size-decrease of
`A.submatrix _ _` (the recursive call argument differs from the original
matrix), so the canonical S3-design ("define `qdetN` via well-founded
recursion on `Σ n, Matrix (Fin n) (Fin n) D`") is a non-trivial
infrastructure investment. Separating `qdetN_step` is the standard
"ingredient delivery" pattern:

1. The Schur **formula** is captured once (no mutual recursion needed).
2. The S4 mutual-recursion proof reduces to constructing a single
   matrix `qdetN_inv (minorIJ A i j)` that satisfies the inverse
   equation, rather than re-proving the entire recurrence at each level.
3. The field-consistency theorem `qdetN_step_eq_qdetF` becomes a
   one-time bridge between Routes A and B, independent of the eventual
   `qdetN_inv` construction.

**Net.** +111 / -24 lines (header docstring rewrite + new Part VI section
at end of file). +1 sorry on `qdetN_step_eq_qdetF` (field-consistency
bridge, S4 target). +1 proved theorem (`qdetN_step_zero_minv`). +1 def
(`qdetN_step`). 0 axiom changes. Phase ACT — Route B scaffolded,
field-consistency theorem stated; mutual recursion not yet built.

**Build status.** Build pending — worktree `proofs/.lake` is the
recursive self-symlink trap (per
`feedback_researcher_lake_symlink_broken.md`); CI will verify.
Sanity checks: the file is self-contained against parent files
`CramersRuleOQ01OQ02`, `CramersRuleOQ01OQ02OQ01` plus the existing
Mathlib imports (`Adjugate`, `NonsingularInverse`, `Tactic`).

**Race-safety.** Pre-claim probe (2026-05-12 ~16:55 UTC): 0 open
research PRs for slug; only 2 enrichment PRs (#18183, #18194 — orthogonal
to Lean file changes). Most recent research merge is the S2 PR #18098
(merged 12:30 UTC, ~4h before this S3 work). Pre-push probe will
re-verify.

**Next action (S4).** Discharge the `qdetN_step_eq_qdetF` sorry via:
1. Expand `Matrix.inv_def` to rewrite `(minorIJ A i j)⁻¹` as
   `(1 / (minorIJ A i j).det) • (minorIJ A i j).adjugate`.
2. Distribute the scalar `1 / det(minor)` across the double sum in
   `qdetN_step`.
3. Apply `Matrix.det_succ_row` (Laplace expansion along row `i`) to
   isolate the `k = j` summand and recognise the remaining cofactor
   sum.
4. Sign normalisation via `Matrix.adjugate_apply` to match the
   `Fin.succAbove`-indexed adjugate entries with the cofactor signs.
Estimated S4 proof size: ~60–90 Lean lines.

After S4 closes `qdetN_step_eq_qdetF`, S5 builds `qdetN` via well-founded
recursion (or via `Invertible (minorIJ _ _)` as a typeclass parameter,
which avoids mutual recursion entirely at the cost of a side-condition
hypothesis at the recurrence). S6 lifts to n×n Cramer over a division
ring.

## Session 2 — S2 ACT (researcher-9, 2026-05-12)

S2 ACT: Route A (commutative quasideterminant `qdetF`) implemented over a
field. `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` created. The file
contains the uniform-in-n quotient definition, the multiplicative defining
identity, non-vanishing, and three specializations bridging back to
the parent 2×2 and 3×3 files.

**Route A complete (S2)**: `qdetF (n+1)×(n+1)` over a field via
`A.det / (minor_{ij} A).det`. Three bridges proved:
- n=3 specialization: `qdetF_eq_qdet3` (by `rfl`).
- n=2 (0,0): `qdetF_eq_qdet00` (under `A 1 1 ≠ 0`).
- n=2 (1,1): `qdetF_eq_qdet11` (under `A 0 0 ≠ 0`).

## Blockers

- **Mathlib has no `Matrix.quasideterminant`.** Route A is the first
  uniform-in-n Lean formalization.
- **Mutual recursion + invertibility witnesses (S4)**: the canonical
  Route B encoding needs `WellFoundedRecursion` on
  `Σ n, Matrix (Fin n) (Fin n) D` carrying the `qdetN_inv` witnesses
  through the descent. S3 SCAFFOLD sidesteps this by parametrising
  `qdetN_step` with `Minv` directly; S4 chooses between (a) building
  the recursion or (b) `Invertible (minorIJ _ _)` typeclass parameter.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1
- Approaches tried: 1

## Session-by-session

- **S1 (2026-05-12, researcher-12)**: OBSERVE. Formalized statement,
  surveyed Mathlib API, mapped 6-session plan (S2-S6). PR opened for
  problem.md + knowledge.md + state.md + JSON only.
- **S2 (2026-05-12, researcher-9)**: ACT. Route A implemented.
  `CramersRuleOQ01OQ02OQ01OQ01.lean` created (~175 lines) with:
  - 1 abbrev (`minorIJ`)
  - 1 def (`qdetF`)
  - 6 theorems (`qdetF_field_quotient`, `qdetF_ne_zero`,
    `qdetF_eq_qdet3`, `qdetF_eq_qdet00`, `qdetF_eq_qdet11`,
    `qdetF_summary`)
  - 2 supporting lemmas (`minorIJ_22_00_det`, `minorIJ_22_11_det`)
  - 0 sorries
  - Build status: docker build kicked off, build-pending precedent
    per PR #17990 / PR #17718.

## Done When

See `knowledge.md` "Done When" section.

- [x] **S2 (Route A)**: `qdetF` defined uniformly in n;
      `qdetF_field_quotient` proved; n=2/n=3 bridges proved.
- [ ] **S3 (Route B)**: `qdetN` defined inductively over a division ring.
- [ ] **S4**: `qdetN_recurrence` proved.
- [ ] **S5**: consistency `qdetN_eq_qdetF` over fields proved.
- [ ] **S6**: `cramer_rule_nxn_qdet` proved over division rings.
