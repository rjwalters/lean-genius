# Research State: minkowski-theorem-oq-02-oq-03

## Current State
**Phase**: S5-a ACT (latest Lean — `shearM` + `shearM_lowerTriangular`
+ `shearM_det` merged via PR #18975, build pending) — S5 PREP-2 (latest
doc-only — Mathlib bearer audit, PR #18622) — **S5-b ACT pending**
(Tv0 / Tv_succ + h_eq preimage), **S5-c ACT pending** (volume assembly),
**S6 ACT pending** (Minkowski assembly + integer-coordinate extraction).
**Path**: full
**Since**: 2026-05-12
**Last Updated**: 2026-05-14 (Session 8, researcher-5, STATE-SYNC after #18975 S5-a)
**Iteration**: 7

## Lean status at HEAD
`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (252 LOC, 0 sorries, 0
axioms; counts at #18975 merge — build verification of post-S5-a chain
pending Docker CI on the `proofs/.lake` infra repair):

| Lemma                          | Statement                                                  | Status                                  |
| ------------------------------ | ---------------------------------------------------------- | --------------------------------------- |
| `dirichletSetN`                | n-dim Cassels parallelepiped (Fin (n+1) → ℝ)               | def in place (S2)                       |
| `dirichletSetN_symmetric`      | Central symmetry about origin                              | sorry-free, 0 axioms (S2)               |
| `dirichletSetN_measurable`     | Lebesgue measurable (open set + iInter)                    | sorry-free, 0 axioms (S3)               |
| `dirichletSetN_convex`         | Convex (linear preimages of `Ioo` + `convex_iInter`)       | sorry-free, 0 axioms (S4)               |
| `shearM`                       | `(n+1) × (n+1)` shear matrix `(1, α) ⊕ (-I_n)`             | def in place (S5-a, PR #18975)          |
| `shearM_lowerTriangular`       | `BlockTriangular toDual` form (Mathlib `det_of_lowerTriangular` bearer) | sorry-free, 0 axioms (S5-a, PR #18975) |
| `shearM_det`                   | `(shearM α).det = (-1)^n` (via lowerTriangular + Fin.prod_univ_succ) | sorry-free, 0 axioms (S5-a, PR #18975) |
| `dirichletSetN_volume`         | Volume = `2^(n+1)(Qⁿ+1)/Qⁿ`                                | **S5-b/-c ACT pending**                 |
| `simultaneous_dirichlet_…`     | Assembly + integer extraction                              | **S6 ACT pending**                      |

## Merged PRs (chronological)

| PR     | Phase             | Author        | Merged (UTC)         | Files touched                                                                                                                  |
| ------ | ----------------- | ------------- | -------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| #18339 | S1 OBSERVE        | researcher-1  | 2026-05-12 22:39:38  | `problem.md`, `knowledge.md`, `state.md` (seeker stub → S1 entry), research JSON, `sessions/2026-05-12-s01-observe.md`           |
| #18419 | S5 PREP           | researcher-11 | 2026-05-13 00:51:28  | `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`                                                                   |
| #18511 | S6 PREP           | researcher-1  | 2026-05-13 03:11:07  | `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`                                                                    |
| #18551 | S2 ACT            | researcher-1  | 2026-05-13 03:49:30  | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (new, +117 LOC: def + symmetry), `sessions/2026-05-13-s2-act-…md`                |
| #18613 | S3 + S4 ACT       | researcher-3  | 2026-05-13 06:23:30  | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+72 LOC: measurable + convex), `sessions/2026-05-13-s3-s4-act-…md`              |
| #18622 | S5 PREP-2         | researcher-5  | 2026-05-13 06:50:27  | `sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md`                                                                        |
| #18967 | STATE-SYNC        | researcher-12 | 2026-05-14 (early)   | `state.md` (Session 7), research JSON (Session 7 refresh)                                                                      |
| #18975 | S5-a ACT          | (researcher)  | 2026-05-14           | `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+63 LOC: `shearM` def + `shearM_lowerTriangular` + `shearM_det = (-1)^n`)        |

## Session 8 — STATE-SYNC after #18975 S5-a ACT (researcher-5, 2026-05-14)

**Mode.** Doc-only. No Lean edits.

**Why STATE-SYNC.** PR #18975 ("S5-a ACT — shearM def + lowerTriangular
+ det = (-1)^n") merged on 2026-05-14 after Session 7's STATE-SYNC
(PR #18967, also 2026-05-14, doc-only). The S5-a ACT advanced
`MinkowskiTheoremOQ02OQ03.lean` from 189 → 252 LOC, adding three
sorry-free / axiom-free declarations (`shearM` def, `shearM_lowerTriangular`,
`shearM_det = (-1)^n`). state.md's "Current State" / "Lean status at
HEAD" / "Merged PRs" / "Next-ACT candidates" sections and the research
JSON `currentState.focus` / `nextAction` / `knowledge.progressSummary`
fields still describe the pre-S5-a state. Live Lean source counts
diverge from JSON `currentState.focus` (189 LOC claim) by +63 LOC.

**Drift surface.**

* `currentState.phase` (`"ACT"`): unchanged — still appropriate.
* `currentState.iteration` (6): bumped to 7 to reflect Session 8.
* `currentState.focus`: rewritten to record #18975's three new
  declarations and the surviving S5-b/S5-c/S6 backlog.
* `currentState.nextAction`: narrowed from "S5 ACT (volume calculation),
  narrowest entry point S5-a" to "S5-b (Tv0/Tv_succ + h_eq preimage)"
  since S5-a is now landed.
* `knowledge.progressSummary`: refreshed to add #18975 ahead of the
  existing chronology.
* `leanFiles`: the file's JSON entry for `MinkowskiTheoremOQ02OQ03.lean`
  was previously *missing entirely* — the JSON `leanFiles` array
  contained only OQ02 + OQ02OQ01 entries despite OQ02OQ03 having
  shipped since #18551. Session 8 adds the missing entry with
  `lineCount: 252 / theoremCount: 4 / defCount: 2 / axiomCount: 0 /
  sorryCount: 0` (the count splits `def shearM` + `def dirichletSetN`
  into the `defCount` bucket and counts `shearM_*` + `dirichletSetN_*_*`
  in `theoremCount`).

**Counts on file at #18975 merge:**

* `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`: 252 LOC, 4 theorems +
  2 `def`s, 0 sorries, 0 axioms.
* No change to gallery `meta.json` (`src/data/proofs/minkowski-theorem-oq-02-oq-03/meta.json`
  was last touched independently and its leanFiles count is auditor-
  invisible).

### Next-ACT candidates (refresh)

`S5-a` row in the candidates table is now landed (PR #18975). Remaining
entries unchanged from Session 7:

* **S5-b ACT** (Tv0 / Tv_succ + `h_eq` preimage, ~50 LOC, recommended
  entry point) — substantively bears on the chain
  `dirichletSetN_volume → shearM⁻¹ image factorisation → preimage
  measurability + volume identity`.
* **S5-c ACT** (volume assembly, ~80 LOC) — depends on S5-b.
* **S6 ACT** (`simultaneous_dirichlet_from_minkowski`, ~80-120 LOC)
  — depends on S5-c plus the integer-coordinate extraction sub-ACT
  (S6 PREP, PR #18511).

### Honest-status block

* **Mathematical progress in this PR**: zero — STATE-SYNC catches the
  books up to #18975 without adding theorems, definitions, sorries,
  or axioms.
* **Build status**: unchanged. #18975 shipped "(build pending)" per
  the active build-pending convention; the post-S5-a chain (`shearM`
  + `shearM_lowerTriangular` + `shearM_det`) remains gated on Docker
  CI green for the `proofs/.lake` infra repair (orthogonal mechanic
  infra task).
* **Pre-claim cross-checks** (per researcher anti-patterns memory):
  worktree synced to `origin/main` BEFORE reading state (avoided
  stale-iter trap); fresh topic branch off `origin/main` (avoided
  open-PR contamination); 2nd STATE-SYNC this session (within the
  2-per-session cap — first was S23 PREP for `minkowski-theorem-oq-04`,
  which is *not* STATE-SYNC since it shipped a new spec doc).

----

## Session 7 — STATE-SYNC: align state.md + JSON with 5-PR backlog (researcher-12, 2026-05-13)

**Mode.** Doc-only (no `.lean` changes, no `problem.md` / `knowledge.md`
changes).

**Trigger.** `state.md` was last updated at the end of Session 1 (S1
OBSERVE, PR #18339), declaring `Phase: OBSERVE` and `Next Action: S2-A`.
Five subsequent PRs have since merged on `main` (S5 PREP #18419, S6 PREP
#18511, S2 ACT #18551, S3 + S4 ACT #18613, S5 PREP-2 #18622) without a
`state.md` refresh in any of them; the JSON sidecar
`src/data/research/problems/minkowski-theorem-oq-02-oq-03.json` was
similarly frozen at S1. Future claimants reading `state.md` would
believe `MinkowskiTheoremOQ02OQ03.lean` does not yet exist.

**Outcome.** This STATE-SYNC PR:

1. Promotes the **Phase** header to reflect the actual highest Lean
   ACT (`S4`) and the latest doc-only PREP (`S5 PREP-2`).
2. Bumps **Iteration** from 1 to 6 (one per merged PR after S1).
3. Adds a **Lean status table** documenting all 6 lemmas (4 shipped,
   2 pending).
4. Adds a **Merged PRs table** with PR #, phase, author, UTC timestamp,
   and the actual files-touched diff each shipped.
5. Adds **Session-log entries** below for sessions 2-6 (one paragraph
   each, citing the canonical session-file in `sessions/`).
6. Adds **Open questions — PREP coverage** cross-reference linking
   each S1 OBSERVE shortlist item to its PREP/ACT memo.
7. Adds **Next-ACT candidates** table with LOC estimate, risk, and
   pre-staging status for S5 ACT (volume) and S6 ACT (assembly).
8. Updates the JSON sidecar's `currentState.phase`, `iteration`,
   `focus`, `nextAction`, `knowledge.progressSummary`,
   `knowledge.builtItems`, and `updatedAt`.

**No Lean / problem / knowledge changes.** Pure doc sync.

**Build status.** No `.lean` changes; no Docker build attempted or
needed.

## Session 6 — S5 PREP-2: Mathlib bearer audit + CRITICAL erratum (researcher-5, 2026-05-13, PR #18622)

Doc-only memo in `sessions/2026-05-13-s5-prep-2-mathlib-bearer-audit.md`.
Closes 4 honest gaps flagged in S5 PREP (§9 of the predecessor) by
verifying Mathlib bearers at the locked pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):

- **CRITICAL ERRATUM** in S5 PREP §3.1: `shearM_lowerTriangular` was
  stated as `BlockTriangular id` (upper-triangular condition). The
  corrected signature is `BlockTriangular (toDual : Fin (n+1) →
  (Fin (n+1))ᵒᵈ)`, matching `Mathlib/LinearAlgebra/Matrix/Block.lean`
  `det_of_lowerTriangular` at line 291. The bug would have surfaced
  as a unification failure at S5 ACT.
- `Fin.prod_univ_succ` verified at `Mathlib/Algebra/BigOperators/Fin.lean:76`.
- `Finset.prod_const_neg_one_eq_pow` confirmed **absent**; two-line
  `prod_const + card_univ + Fintype.card_fin` chain is canonical.
- `Finset.sum_ite_eq'` verified at `…/Piecewise.lean:152`, with explicit
  `Tv_succ` proof template (~15 LOC, two variants offered).
- `Real.map_matrix_volume_pi_eq_smul_volume_pi` namespace surfaced;
  `open Real` required (parent OQ-01 has it at line 32).
- `[DecidableEq ι]` requirement surfaced: `inferInstance` for `Fin (n+1)`.
- Risk register: 10/10 resolved (vs. 4 in S5 PREP).
- Revised S5 ACT LOC estimate: ~160 (down from 180).

## Session 5 — S3 + S4 ACT: measurable + convex (researcher-3, 2026-05-13, PR #18613)

Lean ACT in `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (+72 LOC, 0
sorries, 0 axioms). Doc in
`sessions/2026-05-13-s3-s4-act-measurable-convex.md`.

- **`dirichletSetN_measurable`** (~16 LOC): rewrites
  `dirichletSetN n α Q` as the intersection of a coordinate preimage of
  `Ioo` (for the `|v 0|` clause) with `⋂ i : Fin n` over preimages of
  `Ioo` under continuous functionals (for the `|α i * v 0 - v i.succ|`
  clauses), then closes via `(isOpen_Ioo.preimage …).inter
  (isOpen_iInter_of_finite …)`.
- **`dirichletSetN_convex`** (~14 LOC): same intersection structure,
  swapping topology for `LinearMap.proj` algebra and
  `convex_Ioo.linear_preimage` / `convex_iInter`.

Both are verbatim n-dim generalisations of the parent OQ-01's
analogues. Lean file at 189 LOC after merge.

## Session 4 — S2 ACT: dirichletSetN def + symmetry (researcher-1, 2026-05-13, PR #18551)

Lean ACT in `proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` (new file,
+117 LOC, 0 sorries, 0 axioms). Doc in
`sessions/2026-05-13-s2-act-dirichletSetN-def-symmetric.md`.

- **`dirichletSetN n α Q`** (def): the Cassels-parallelepiped
  `{v : Fin (n+1) → ℝ | |v 0| < Qⁿ + 1 ∧ ∀ i, |α i * v 0 - v i.succ| <
  1/Q}`, indexed by `Fin (n+1)` with `v 0` reserved as the
  common-denominator coordinate.
- **`dirichletSetN_symmetric`** (~9 LOC of proof): `v ∈ S → -v ∈ S`,
  one of the 3 Minkowski hypotheses. Generalises parent OQ-01's
  `dirichletSet_symmetric` by replacing the single `i = 1` clause
  with `∀ i : Fin n`.

## Session 3 — S6 PREP: Minkowski assembly + integer-coordinate extraction roadmap (researcher-1, 2026-05-12, PR #18511)

Doc-only memo in `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`.
Decomposes the assembly step into 5 stages (mirroring parent OQ's
`dirichlet_approximation_from_minkowski` at `MinkowskiTheoremOQ02.lean:182`):

1. Apply `MinkowskiProved.minkowski_integer_lattice_proved (n+1)` to
   `dirichletSetN n α Q`, supplying the four hypotheses (symmetry,
   measurability, convexity, volume threshold).
2. Extract integer coordinates `(q, p) ∈ Fin (n+1) → ℤ` from the
   lattice-point existential via the (n+1)-dim analogue of parent's
   `stdLattice2_coords`.
3. Parse the parallelepiped membership: `q := |v 0|`, `p i := v i.succ`
   (modulo sign on `v 0`).
4. Show `q ≠ 0` from non-triviality of the lattice point.
5. Discharge the conclusion bounds `1 ≤ q ≤ Qⁿ` and `|α i · q - p i| <
   1/Q`.

Identifies parent's `stdLattice2_coords` as the (n+1)-dim analogue
target (currently only stated for `n = 1`); flags it as the one piece
of new infrastructure beyond S2-S5.

## Session 2 — S5 PREP: shear-map volume calculation (researcher-11, 2026-05-12, PR #18419)

Doc-only memo in `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`.
Decomposes the n-dim volume calculation into 4 mechanical pieces
(mirroring parent OQ-01's `dirichletSet_volume`):

- **shearM definition**: `Matrix (Fin (n+1)) (Fin (n+1)) ℝ` with
  column 0 = `Fin.cases (1 : ℝ) α` (first column carries α₀…α_{n-1});
  off-column-0 diagonal = -1.
- **shearM_det = (-1)ⁿ**: via `det_of_lowerTriangular` + diagonal
  product collapse.
- **T_image_is_rectangle**: image of `dirichletSetN` under `M.toLin'`
  is the open box `(-(Qⁿ+1), Qⁿ+1) × (-1/Q, 1/Q)ⁿ`.
- **dirichletSetN_volume**: chain
  `volume S = ENNReal.ofReal (|det M|⁻¹) · volume rect = volume rect =
  2(Qⁿ+1) · (2/Q)ⁿ`.

S5 PREP-2 (Session 6 above) closes the 4 honest gaps flagged here.

## Session 1 — S1 OBSERVE: literature audit + Mathlib API survey + S2 shortlist (researcher-1, 2026-05-12, PR #18339)

Doc-only deliverable in `sessions/2026-05-12-s01-observe.md`. Filled
the seeker-init `problem.md` / `knowledge.md` / `state.md` skeletons.
Surveyed Mathlib for the n-dim geometry-of-numbers infrastructure used
by parent `MinkowskiTheoremOQ02.lean` and axiom-free sibling
`MinkowskiTheoremOQ02OQ01.lean`. Found:

- **`MinkowskiProved.minkowski_integer_lattice_proved`** at
  `MinkowskiFundamentalTheorem.lean:638` already stated for arbitrary
  `n` (hypothesis `(2 : ENNReal) ^ n < volume s`); the n-dim Minkowski
  step is free.
- **`map_matrix_volume_pi_eq_smul_volume_pi`** (used in
  `MinkowskiTheoremOQ02OQ01.lean:103`) stated for any `Fin n`; the
  shear-map step generalises.
- The three measure-theoretic axioms in parent OQ have axiom-free
  analogs in OQ-01 whose proof patterns lift to arbitrary `n`.

Recommended construction (Cassels 1957, Theorem I.II.A): the
parallelepiped `dirichletSetN α Q` defined above + lower-triangular
shear with `|det T| = 1` mapping to `(-(Qⁿ+1), Qⁿ+1) × (-1/Q, 1/Q)ⁿ`,
volume `2(Qⁿ+1) · (2/Q)ⁿ = 2^(n+1)(Qⁿ+1)/Qⁿ > 2^(n+1)`. Three S2 ACT
targets shortlisted (narrowest first): symmetric (~10 LOC), measurable
(~30 LOC), convex (~30 LOC). All three have since shipped (S2 ACT,
S3 + S4 ACT).

## Active Approach
**Approach A (Cassels 1957 parallelepiped)** — verbatim n-dim
generalisation of `MinkowskiTheoremOQ02OQ01.lean`'s 1D axiom-free
proof, using `Fin (n+1)`-indexed parallelepiped and lower-triangular
shear matrix.

Three of the four Minkowski hypotheses (symmetry, measurability,
convexity) are sorry-free, axiom-free, and merged. The remaining
volume hypothesis is the hardest step but fully pre-staged in S5 PREP
+ S5 PREP-2; assembly into `simultaneous_dirichlet_from_minkowski` is
pre-staged in S6 PREP.

## Attempt Count
- Total attempts: 7 (six merged PRs + this STATE-SYNC)
- Current approach attempts: 7 (all Approach A)
- Approaches tried: 1

## Blockers
None identified. All Mathlib bearers for S5 ACT verified by S5 PREP-2;
the `(n+1)`-dim analogue of parent's `stdLattice2_coords` (needed for
S6 ACT) is the one piece of new infrastructure required and is
roadmapped in S6 PREP.

## Open questions — PREP coverage cross-reference

| S1 OBSERVE shortlist item        | PREP coverage         | ACT status        |
| -------------------------------- | --------------------- | ----------------- |
| `dirichletSetN` def              | (S1 sketch)           | Shipped (PR #18551, S2 ACT)  |
| `dirichletSetN_symmetric`        | (S1 sketch)           | Shipped (PR #18551, S2 ACT)  |
| `dirichletSetN_measurable`       | (S1 sketch, OQ-01 ref) | Shipped (PR #18613, S3 ACT) |
| `dirichletSetN_convex`           | (S1 sketch, OQ-01 ref) | Shipped (PR #18613, S4 ACT) |
| `dirichletSetN_volume`           | PR #18419 (S5 PREP) + PR #18622 (S5 PREP-2 bearer audit) | **Pending S5 ACT** |
| `simultaneous_dirichlet_from_minkowski` | PR #18511 (S6 PREP assembly roadmap) | **Pending S6 ACT** |
| `stdLattice (n+1) → ℤ` extraction | PR #18511 (S6 PREP §4) | **Pending — depends on S5 ACT, may slot into S6 ACT or its own S6-α ACT** |

## Next-ACT candidates (in dependency order)

| Candidate                              | LOC est. | Risk   | Pre-staging                | Notes                                                                                                                          |
| -------------------------------------- | -------- | ------ | -------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| **S5 ACT** `dirichletSetN_volume`      | ~110 remaining | medium | S5 PREP (§3 templates) + S5 PREP-2 (10/10 risks resolved, BlockTriangular erratum fixed) | S5-a **DONE** (PR #18975: shearM def + lowerTriangular + det = (-1)^n, +63 LOC). Remaining chunks: (S5-b) Tv0 / Tv_succ + h_eq preimage (~50 LOC); (S5-c) volume assembly (~80 LOC). |
| **S6 ACT** `simultaneous_dirichlet_from_minkowski` | ~80-120  | medium | PR #18511 (S6 PREP) | Depends on S5 ACT for the volume hypothesis. The `stdLattice (n+1) → ℤ` extraction is a sibling sub-ACT that may slot into S6 ACT or split off as S6-α. |

The lowest-risk S5 ACT entry point is **S5-a** (shearM def +
`shearM_lowerTriangular` with the corrected `BlockTriangular toDual`
signature + `shearM_det = (-1)ⁿ`). All three are independent of
`dirichletSetN`; they live at the matrix layer and can be merged
without touching the existing 4 lemmas.

## Next Action

**Researcher's choice**: pick one of S5-b / S5-c / S6 (S5-a landed via
PR #18975, 2026-05-14). The narrowest next entry point is **S5-b**
(Tv0 / Tv_succ + `h_eq` preimage, ~50 LOC), all bearers verified in
S5 PREP-2 §2-§4 and S5 PREP §3.

After S5 ACT lands:
- **S6 ACT (or S6-α)**: integer-coordinate extraction via
  `(n+1)`-dim analogue of parent OQ's `stdLattice2_coords`.
- **S6 ACT (final)**: `simultaneous_dirichlet_from_minkowski`
  assembly (parent OQ's 5-step pattern from
  `MinkowskiTheoremOQ02.lean:182`).
