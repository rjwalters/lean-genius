# Research State: product-of-segments-of-chords-oq-03

> **S18 ACT (2026-07-24, researcher-1): HEADLINE IFF PROVEN — file now
> 0 sorries / 0 axioms, 265 → 542 LOC, post-change docker build GREEN
> (3038 jobs, 0 warnings, 2026-07-24).**
> `concyclicityDet_eq_zero_iff_concyclic` is fully proven; the S2 placeholder
> `(hNonCollinear : True)` is REPLACED by the genuine hypothesis
> `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)` (with the placeholder the (⟹)
> direction is false — distinct collinear points have Δ = 0 with no circle),
> and the declaration MOVED from Part 4 (old line 119) to a new Part 12 at
> end of file (its proof consumes Parts 5–11). New material: Part 9
> `collinearityDet` + bridge `collinear_of_collinearityDet_eq_zero`
> (`collinear_iff_of_mem`, coordinate-ratio scalars, `Fin.forall_fin_two`
> instead of `fin_cases` to keep ring atoms literal); Part 10 explicit Cramer
> circumcenter (`circumcenter_spec` pure-coords via the
> division-free `bisector_to_dist` + deterministic denominator clearing —
> field_simp on the squared quotients fails, see knowledge.md item 2;
> `exists_circumcircle` on `Vec2` with center
> `WithLp.toLp 2 ![O₀, O₁]`, `0 < r` from non-collinearity); Part 11 exact
> cofactor decomposition `Δ = e₁M₁ − e₂M₂ + e₃M₃ − e₄M₄`
> (`concyclicityDetCoords_circle_decomp`, S7b simp set + `ring`, passed
> first try) and `fourth_point_on_circle` (`linear_combination` with the
> three explicit minor coefficients ⇒ `e₄·M₄ = 0`). The old plan's
> `Matrix.cramer`-API route was NOT needed — explicit quotient formulas
> are shorter. Baseline v4.31 docker check at HEAD was GREEN
> before edits (only the expected L119 sorry warning).
> **Next: S5-bridge session** (signed chord-product ⟹ Δ = 0, consuming the
> merged Parts 6–7 helpers + S12-§3.2 closed-form witness), then **S6 parent
> integration** (replace `converse_product_implies_concyclic_axiom` in the
> parent, gallery axiomatized → verified — the parent axiom's hypothesis
> must become the *signed* product per the S9 counterexample, plus a
> non-collinearity side condition). Pool status blocked → in-progress
> (Docker healthy again). See
> `sessions/2026-07-24-s18-act-headline-iff-proven.md`.

## Current State (pre-S18, retained for ledger)

**Phase**: BLOCKED (S18, verification blackout 2026-06-13) — no build-free
work remains. S17 STATE-SYNC (#23000) already brought the registry current;
file is 265 LOC, **1 genuine sorry** (line 125, the (⟹) Cramer direction of
the headline iff), 0 axioms on origin/main; the (⟸) half is proven
unconditionally as `concyclic_implies_concyclicityDet_zero`. The single open
sorry is build-dependent ACT (Cramer paste, ~80 LOC) and both verification
routes are down this session (docker daemon down + Aristotle MCP 404).
Flagged blocked (status active→blocked) to stop claim churn during the
blackout. **Re-open when Docker recovers**: discharge the (⟹) sorry via
`Matrix.cramer` on the implicit-circle system, then
`./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`.

### Prior (pre-blackout): ACT (S17 STATE-SYNC 2026-06-13 — registry catch-up after two
untracked Lean merges; S7b ACT shipped the two numeric lemmas PR #22967;
the **easy direction `concyclic_implies_concyclicityDet_zero` is now PROVEN
standalone** PR #22917; S16 ACT shipped `coord_of_smul_diff` 2026-06-01)
**Path**: full
**Since**: 2026-06-13 (S17 STATE-SYNC — Docker-down build-free iteration:
fixed the Δ = −8 → −6 numerical error in knowledge.md and synced the ledger)
**Iteration**: 17 (S1 OBSERVE + S2 SCAFFOLD + S3-S5 PREP + S6 STATE-SYNC +
S7 ACT + S7b ACT + S8-S10 PREP + S11 STATE-SYNC + S12-S14 PREP + S15 ACT +
S16 ACT + easy-direction ACT + S17 STATE-SYNC)

### S17 STATE-SYNC (researcher-2, 2026-06-13, this PR)

Build-free registry catch-up. Two Lean PRs merged since the S11-era state.md
was written but neither updated `state.md` / JSON:

- **S7b ACT (#22967)** — reinstated the two numeric sanity lemmas
  (`concyclicityDetCoords_unit_circle = 0`, `concyclicityDetCoords_off_circle
  = -6`) via `Matrix.det_succ_row_zero` + `Matrix.det_fin_three`. This
  surfaced that the S1/S2 doc figure **Δ = -8 was wrong; the correct value is
  -6** (now machine-checked).
- **easy-direction ACT (#22917)** — proved
  `concyclic_implies_concyclicityDet_zero` **unconditionally** (no
  non-degeneracy hypothesis): concyclic ⟹ Δ = 0, via the explicit kernel
  vector `(1, -2O₀, -2O₁, O₀²+O₁²-r²)` and `Matrix.exists_mulVec_eq_zero_iff`.
  This discharges the **(⟸) half** of the headline iff sorry — only the
  (⟹) Cramer direction remains.

Plus S15 ACT (`signed_inner_product_to_scalar` + `_coord`, `norm_sub_sq_coord`)
and S16 ACT (`coord_of_smul_diff`) which the S11 ledger predates.

**Verification note:** Docker daemon is down (2026-06-13), so this iteration
is deliberately build-free — doc/registry only, no Lean edit. The Δ = -6
correction is independently hand-verified (row-reduce + col-4 cofactor) and
already machine-checked by the merged #22967 lemma.

## Current Focus

**S16 ACT (researcher-1, 2026-06-01, this PR)** — ships
`coord_of_smul_diff`, the coordinate-substitution lemma that turns
the abstract `Vec2` chord-collinearity hypothesis
`R - P = t • (Q - P)` into the per-coordinate identity
`R i = P i + t * (Q i - P i)` for any `i : Fin 2`. Proof is a clean
`PiLp.sub_apply + PiLp.smul_apply + smul_eq_mul + linarith` chain
(found `PiLp.sub_apply` at `Mathlib/Analysis/Normed/Lp/PiLp.lean:114`
and `PiLp.smul_apply` at `:118`).

Net delta vs S15: **+30 LOC, +1 lemma** (184 → 214). Docker-verified
**3058 jobs clean** (warning at line 103 is the pre-existing
placeholder `sorry` on `concyclicityDet_eq_zero_iff_concyclic`).
**0 axioms, 1 sorry (pre-existing, unchanged).**

Why this slice: S15 §5 prescribed an S16 ACT paste with four `have`
substitution steps (`hB0/hB1/hD0/hD1`) inlined into the same theorem
as the cofactor + `linear_combination`. The risky polynomial-witness
step has **four hypothesised failure modes** (S14 §4.4). Rather than
gamble all four on a single iteration, S16 ACT extracts the
substitution boilerplate as a reusable lemma so S17 ACT can focus
exclusively on the polynomial step. The lemma collapses all four
S15-§5 `have`s to four `coord_of_smul_diff … 0/1` applications.

**S17 ACT now owes only the cofactor + `linear_combination`**, with
no substitution boilerplate. Estimated ~35-45 LOC (was ~50 LOC).

### Historical Focus (S11 STATE-SYNC, retained for ledger)


**S11 STATE-SYNC (researcher-1, 2026-05-15, this PR)** — registry
refresh after three doc-only PREPs (S8 #19231, S9 #19246, S10 #19312)
landed without touching `state.md` / JSON. The post-S7 state.md
shipped by PR #19096 (merged 22:59:25Z) is **already stale relative
to the post-S10 plan**:

- **S8 PREP** (#19231, researcher-9, merged 18:04:50Z) — Mathlib
  v4.26.0 bearer re-verification at pin `2df2f015…`. Confirmed
  `Matrix.det_fin_four` does **not exist anywhere in Mathlib4**
  (global authenticated `gh api` code search); reorganised S4 ACT
  recommendation from Path B → **Patched Path A** (column-update via
  `det_updateCol_add_smul_self ×3 + det_eq_zero_of_column_eq_zero`);
  corrected one bearer typo in S3 PREP §6
  (`sqrt_eq_iff_sq_eq` → `sqrt_eq_iff_eq_sq`).

- **S9 PREP** (#19246, researcher-8, merged 18:03:50Z) — supplied a
  **concrete counterexample to the parent axiom under the unsigned
  chord-product hypothesis** that S3/S4/S5 PREP assumed:
  `P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)` ⇒ `PA·PB=PC·PD=2`
  but `Δ=12≠0`. Recommended **Option A** signed inner-product
  hypothesis `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ` which collapses S5 PREP's
  case-(a)/(b) split to a single scalar equation
  `t·‖A-P‖² = s·‖C-P‖²` (no `False.elim` branch).

- **S10 PREP** (#19312, researcher-3, merged 22:55:32Z) — synthesised
  S8 + S9 into a **unified S5 ACT skeleton**
  `concyclicityDet_eq_zero_of_signed_chord_product` (~25-35 LOC,
  Option A × Path α `det_succ_row_zero + det_fin_three`); pinned 10
  new inner-product bearer rows
  (`real_inner_self_eq_norm_sq` at `Basic.lean:384`,
  `PiLp.inner_apply` at `PiL2.lean:98` is `rfl`, etc.); staged the
  S6 ACT 4-step decision tree (parent axiom signature swap →
  caller update → S3/S4/S5 ACT chain → parent gallery `meta.json`
  update).

This S11 STATE-SYNC refreshes `state.md` + JSON, re-confirms the
lake-manifest pin is unchanged (`2df2f015…`, **0 substantive bearer
drift since S8 wrote**), and pins the post-S10 Next Action. The
**ACT-readiness verdict remains GREEN** (S10 §14).

### S7 ACT BUILD-VERIFY recap (last Lean diff, retained for reference)

The first Docker baseline of `Proofs/ProductOfSegmentsOfChordsOQ03.lean`
after 4 consecutive build-pending / doc-only PRs surfaced **two
v4.26.0 surface regressions**:

1. **Import path change**: `Mathlib.Data.Matrix.Notation` →
   `Mathlib.LinearAlgebra.Matrix.Notation` (1-LOC swap on line 3).

2. **`Matrix.det_fin_four` does not exist at v4.26.0** (verified
   missing across all of Mathlib4 by S8 §1.1 global code search; S2
   SCAFFOLD author's `simp [Matrix.det_fin_four]; ring` `example`s
   never compiled). The det-expansion ladder stops at
   `Matrix.det_fin_three`; the recursive `Matrix.det_succ_row_zero`
   is the only 4×4 route.

S7 ACT delivered: 1-LOC import patch + removal of two broken
`example` blocks (no downstream consumer). The file now
Docker-builds clean (3058 jobs, single `sorry` warning at line 109
on the headline iff theorem).

## Lean status (S17 STATE-SYNC snapshot, 2026-06-13)

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **265 LOC, 1
sorry, 0 axioms** (origin/main as of PR #22917; S7b #22967 + easy-direction
#22917 + S15/S16 lemmas all merged since the S11 snapshot below). Decls now
present beyond the S11 baseline:

| Decl | Status |
|------|--------|
| `concyclicityDetCoords_unit_circle` (= 0) | Proven (S7b, #22967) |
| `concyclicityDetCoords_off_circle` (= -6) | Proven (S7b, #22967) — corrects the S1 doc figure -8 |
| `norm_sub_sq_coord` | Proven (S15) |
| `signed_inner_product_to_scalar` / `_coord` | Proven (S15) |
| `coord_of_smul_diff` | Proven (S16) |
| `concyclic_implies_concyclicityDet_zero` | **Proven unconditionally (easy direction, #22917)** — the (⟸) half of the iff |
| `concyclicityDet_eq_zero_iff_concyclic` | **1 sorry** at line 125 — only the (⟹) Cramer direction now genuinely open; the (⟸) branch can cite `concyclic_implies_concyclicityDet_zero` |

### Historical: post-S7 BUILD-VERIFY snapshot (S11-era, superseded above)

`proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean` — **111 LOC, 1
sorry, 0 axioms** (Docker-verified after S7 patch):

| Decl                                            | Status                         |
|-------------------------------------------------|--------------------------------|
| `Vec2` (abbrev)                                 | Sealed; `EuclideanSpace ℝ (Fin 2)` |
| `concyclicityDetCoords` (def)                   | Sealed; `Matrix.det !![...]` 4×4 in raw coords |
| `concyclicityDet` (def)                         | Sealed; `Vec2`-wrapped form    |
| Numerical examples (unit-square Δ = 0, perturbed Δ = -6) | **Re-added in S7b ACT (PR #22967)** via `det_succ_row_zero` + `det_fin_three`; the S1/S2 figure Δ = -8 was a hand-computation slip (correct value -6, machine-checked). |
| `concyclicityDet_eq_zero_iff_concyclic`         | **1 sorry** at line 109 (the headline iff) — placeholder `(hNonCollinear : True)` to be replaced per S3 PREP §1.b (post-S8 §4 corrections) |

Parent file `proofs/Proofs/ProductOfSegmentsOfChords.lean` — **541
LOC, 0 sorries, 1 axiom**: `converse_product_implies_concyclic_axiom`
at line 468 (the discharge target). After S3-S5 ACT land + S6 ACT
swaps the axiom signature to Option A (S9 §5; S10 §5 step 6a) and
discharges it (S10 §5 step 6c), parent `axiomCount` drops 1 → 0 and
`status` flips `"axiomatized"` → `"verified"`.

## Ledger (S1 → S11)

| PR     | Iter | Date / UTC          | Author        | Phase / scope                                                       |
|--------|-----:|---------------------|---------------|---------------------------------------------------------------------|
| #18231 |   1  | 2026-05-12 18:17    | researcher-11 | S1 OBSERVE — power-of-a-point ↔ 4×4 concyclicity-determinant bridge |
| #18380 |   2  | 2026-05-12 23:43    | researcher-3  | S2 SCAFFOLD — `concyclicityDet` + Vec2 wrapper + 2 numerical examples (build pending) |
| #18466 |   3  | 2026-05-13 02:19    | researcher-9  | S3 PREP — Cramer's rule discharge design for (⇐), +307 LOC doc-only |
| #18474 |   4  | 2026-05-13 02:30    | researcher-12 | S4 PREP — concyclic → Δ = 0 direction (doc-only)                    |
| #18553 |   5  | 2026-05-13 03:50    | researcher-5  | S5 PREP — chord-product → Δ = 0 bridge strategy (doc-only)          |
| #18977 |   6  | 2026-05-14 03:03    | researcher-9  | S6 STATE-SYNC — doc-only refresh of state.md + JSON                 |
| #19096 |   7  | 2026-05-15 22:59    | researcher-12 | S7 ACT BUILD-VERIFY — Mathlib v4.26.0 import unblocker (3058 jobs clean) |
| #19231 |   8  | 2026-05-15 18:04    | researcher-9  | S8 PREP — Mathlib v4.26.0 bearer re-verification + corrected S3/S4/S5 ACT skeleton (doc-only) |
| #19246 |   9  | 2026-05-15 18:03    | researcher-8  | S9 PREP — concrete `Δ=12≠0` counterexample to parent axiom + Option A signed-hypothesis recovery (doc-only) |
| #19312 |  10  | 2026-05-15 22:55    | researcher-3  | S10 PREP — ACT-readiness gate harmonizing S8 bearer corrections × S9 Option A (doc-only) |
| (this) |  11  | 2026-05-15 ~23:52   | researcher-1  | S11 STATE-SYNC — refresh state.md + JSON after S8 / S9 / S10 PREPs (doc-only) |

S3, S4, S5, S6, S8, S9, S10, S11 are all **doc-only** (no Lean
changes). S7 ACT BUILD-VERIFY remains the only Lean diff since S2
SCAFFOLD: a 1-LOC import-path swap + removal of two
`Matrix.det_fin_four`-dependent `example`s that never compiled.
**Note on merge interleaving**: #19312 (S10 PREP) merged at 22:55:32Z,
**4 minutes before** #19096 (S7 ACT BUILD-VERIFY) at 22:59:25Z, so
S10's anti-target of `state.md` / JSON applies to the *pre-#19096*
state.md; post-#19096 the state.md was rewritten but did not catch
up with S8/S9/S10 — closed by this S11.

## The discharge plan, consolidated (post-S10 harmonization)

Per S3-S5 PREP × S8 bearer corrections × S9 Option A × S10 unified
skeleton, the headline `sorry` decomposes into **three concrete ACT
iterations** plus a final parent-axiom discharge. The post-S10
harmonised plan replaces S3/S4/S5 PREP's unsigned chord-product
hypothesis (disproved by S9 §2's `Δ=12≠0` counterexample) with S9's
**Option A signed inner-product hypothesis**:

| Sub-task | Source                                 | Direction                                                        | Est. LOC |
|----------|----------------------------------------|------------------------------------------------------------------|---------:|
| S3 ACT   | S3 PREP #18466 §2-§5 (post-S8 §4 bearer fix) | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r, ‖P_i - O‖ = r` via `Matrix.cramer` (`cramer_apply` is `rfl`) | ~80-90 |
| S4 ACT   | S4 PREP #18474 §3 (post-S8 §5.2 Path A) | (⇒) `concyclic → Δ = 0` via column-update (`det_updateCol_add_smul_self ×3 + det_eq_zero_of_column_eq_zero`) | ~35-40 |
| S5 ACT   | S5 PREP #18553 §4.3 case (a) × S9 §5 Option A × S10 §4.1 skeleton | Signed inner-product → Δ = 0 (`concyclicityDet_eq_zero_of_signed_chord_product`) | ~25-35 |
| S6 ACT   | S10 §5 (synthesis × axiom discharge)   | Parent axiom signature swap → caller update → S3-S5 ACT chain → parent `meta.json` `axiomCount` 1 → 0 | ~25-40 |

**Total picker-estimated ACT LOC (post-S10)**: ~165-205 across S3-S6
(matches the original ~170 ballpark; S5 ACT slimmed by ~15 LOC via
Option A's case-(b) elimination; S4 ACT grew by ~5-10 LOC via
column-update vs row-reduction; S3 ACT unchanged; S6 ACT grew by
~15-30 LOC via axiom-signature swap + caller update).

### S3 PREP key decisions (PR #18466)

- **Non-collinearity hypothesis**: Choice 1b (algebraic 2×2
  determinant, `(P₂ 0 - P₃ 0) * (P₁ 1 - P₃ 1) ≠ (P₁ 0 - P₃ 0) *
  (P₂ 1 - P₃ 1)`) recommended over `Mathlib.Collinear` or
  `LinearIndependent` — more directly usable by Cramer.
- **Implicit-circle parametrization**: `x² + y² + Dx + Ey + F = 0`,
  with `(D, E, F)` as the Cramer unknowns; center `O := (-D/2, -E/2)`
  and radius `r := √(D²/4 + E²/4 - F)`.
- **Anticipated friction points** (S3 PREP §5):
  - `Vec2 = EuclideanSpace ℝ (Fin 2)` ↔ `Fin 2 → ℝ` interconversion.
  - `‖·‖` on `EuclideanSpace` (PiLp 2) vs raw L²-norm.
  - `Real.sqrt` positivity from non-degeneracy of the linear system.

### S4 PREP key decision (PR #18474)

- Choice A (iff packaging) recommended over Choice B (separate
  auxiliary theorem) — discharge S3's "(⇐) sorry" inline as part of
  the original `iff` theorem. S4 ACT closes the second half.

### S5 PREP key chain (PR #18553)

- Algebraic identity: subtract row j from row i in Δ replaces the
  first column entry with `‖P_i‖² - ‖P_j‖² = (P_i - P_j) · (P_i + P_j)`.
- When chord directions are collinear through P, this becomes a
  scalar multiple along chord normals, and chord-product equality
  forces a row dependency by Vieta on the chord quadratic.
- **Post-S9 correction:** the unsigned hypothesis form S5 PREP
  originally used is disproved by S9 §2's `Δ=12≠0` counterexample at
  `P=(0,0), A=(1,0), B=(-2,0), C=(0,1), D=(0,2)` (where
  `PA·PB=PC·PD=2` but `Δ=12`). The post-S10 §3-§4 skeleton uses
  Option A's signed inner-product hypothesis, which collapses the
  case (a)/(b) split entirely.

### S8 PREP key corrections (PR #19231)

- **`Matrix.det_fin_four` confirmed missing across all of Mathlib4**
  (S8 §1.1 global authenticated `gh api` code search returned 0
  matches). The det-expansion ladder stops at `det_fin_three`;
  4×4 routes must go via `det_succ_row_zero`.
- **S4 ACT recommendation flipped**: Path B (row-reduction) → **Patched
  Path A** (column-update via `det_updateCol_add_smul_self ×3 +
  det_eq_zero_of_column_eq_zero`). S8 §5.2 spells out the bearer chain.
- **S3 PREP §6 bearer typo corrected**: `sqrt_eq_iff_sq_eq` →
  `sqrt_eq_iff_eq_sq` (the actual Mathlib name at pin).
- **Bearer line-number pin-down**: S8 §2 catalogues live line numbers
  for 22 bearers across 4 Mathlib files at SHA `2df2f015…`. S10 §2
  re-verified; this S11 §2 re-confirms manifest unchanged.

### S9 PREP key decisions (PR #19246)

- **Concrete counterexample to the parent axiom** under the unsigned
  chord-product hypothesis: `P=(0,0), A=(1,0), B=(-2,0), C=(0,1),
  D=(0,2)` ⇒ `PA·PB = 1·2 = 2 = 1·2 = PC·PD` but `Δ = 12 ≠ 0`. The
  unsigned hypothesis is **not strong enough** to imply concyclicity;
  the S3/S4/S5 PREP-as-written discharge plan was mathematically
  unsound.
- **Option A recommendation**: replace the unsigned hypothesis with
  the **signed inner-product** form
  `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ`. Under chord-collinearity
  `B-P = t·(A-P)`, `D-P = s·(C-P)`, this collapses to the **single
  scalar equation** `t·‖A-P‖² = s·‖C-P‖²` (signed; no sign-case
  split). The case-(b) `False.elim` branch in S5 PREP §2.1 becomes
  unreachable by construction.
- **Parent axiom signature must change** (line 468 + line 481
  caller) before S6 ACT discharge.

### S10 PREP key synthesis (PR #19312)

- **Unified S5 ACT skeleton**
  `concyclicityDet_eq_zero_of_signed_chord_product` (S10 §4.1, ~25-35
  LOC, Option A × Path α `det_succ_row_zero + det_fin_three`).
  Closing `linear_combination` witness left as intentional placeholder
  (the S5 ACT picker owes ~30-60 min pencil work).
- **10 new inner-product bearer rows** pinned (S10 §3.3): chief among
  them `real_inner_self_eq_norm_sq` at `Basic.lean:384`,
  `PiLp.inner_apply` at `PiL2.lean:98` (`rfl`).
- **S6 ACT 4-step decision tree** (S10 §5): 6a restate axiom (Option A);
  6b update one downstream caller (only line 481 known); 6c chain
  S3-S5 ACT and discharge (~10 LOC); 6d gallery `meta.json`
  `axiomCount` 1 → 0.
- **ACT-readiness verdict: GREEN** (S10 §14). Re-confirmed by this S11.

## Previous Focus

(See PREP ledger above — every PREP entry was a `sessions/*.md`
addition with no Lean diff. The last Lean diff was PR #19096 on
2026-05-15 (S7 ACT BUILD-VERIFY).)

## Active Approach

**Next concrete action is an ACT iteration**, not another PREP. After
6 PREP-only PRs (S3/S4/S5 designs; S8 bearer audit; S9
counterexample-driven signature shift; S10 harmonized skeleton) plus
2 STATE-SYNCs (S6, this S11) and 1 ACT (S7 BUILD-VERIFY), the
discharge route is **fully specified** for copy-into-Lean under the
**post-S9 Option A signed-inner-product hypothesis**. The S3-S5 ACT
order can proceed in parallel; S6 ACT (parent axiom discharge)
requires S3-S5 ACT first (S10 §5 pre-flight requirement).

## Blockers

- **None.** S7 ACT BUILD-VERIFY unblocked the Mathlib v4.26.0 import
  regression (3058-job clean baseline). S8 unblocked the
  `det_fin_four` fictitious-bearer regression. S9 unblocked the
  unsigned-hypothesis mathematical-unsoundness regression. S10
  unblocked the S8-vs-S9 contradiction regression. This S11 closes
  the doc-staleness regression on `state.md` / JSON.
- **Mathematical strategy** is unblocked. The approach is purely
  algebraic and does not depend on `Affine.Simplex.circumcenter`
  (which would otherwise require bridging `Vec2 := EuclideanSpace ℝ
  (Fin 2)` with `Affine.Simplex` API).
- **ACT-readiness verdict (post-S10, re-confirmed at S11):** GREEN.
  lake-manifest pin `2df2f015…` is unchanged since S8 wrote (zero
  substantive bearer drift over ~31 hours wall-clock).

## Next Action

**S17 ACT × Cofactor + `linear_combination`** — paste the
`concyclicityDet_eq_zero_of_signed_chord_product` theorem (~35-45 LOC
post-S16): pull S16's `coord_of_smul_diff` to produce the four
substitution facts (`hB0/hB1/hD0/hD1`), pull
`signed_inner_product_to_scalar_coord` (S15) for the scalar identity,
then `unfold concyclicityDet concyclicityDetCoords`, `Matrix.det_succ_row_zero`,
`Fin.sum_univ_succ` + `Matrix.det_fin_three` for cofactor expansion,
and finish with `linear_combination
((t − 1)*(s − 1)*((A 0 − P 0)*(C 1 − P 1) − (A 1 − P 1)*(C 0 − P 0)))
* h_scalar`. The witness coefficient is unchanged from
S12 §3.2 / S14 §2.4 (re-verified against the S9 §2 counterexample).

S14 §4.4 lists four failure modes for the `linear_combination` step
that may need fallback handling:
1. Sign drift on the witness coefficient (try the negated form).
2. PiLp-vs-Pi simp-set staleness (use `show` to peel coercions before
   the cofactor expansion).
3. `simp` normalising the cofactor expression into a form
   `linear_combination` can't unify (use `simp only [...]` with an
   explicit lemma list, not `simp`).
4. `maxHeartbeats` exhaustion (raise via `set_option
   maxHeartbeats 800000` or split the polynomial into named
   sub-identities).

### Historical Next Action (S11 STATE-SYNC, retained for ledger)

**S5 ACT × Option A × Path α (S11-era recommended highest-leverage pick)** —
paste the S10 §4.1 unified skeleton
`concyclicityDet_eq_zero_of_signed_chord_product` (~25-35 LOC).
Signed inner-product hypothesis `⟪A-P, B-P⟫_ℝ = ⟪C-P, D-P⟫_ℝ`
collapses S5 PREP §4.3's case (a)/(b) split to a single scalar
equation `t·‖A-P‖² = s·‖C-P‖²`; closes via `det_succ_row_zero +
det_fin_three` cofactor expansion + S5 PREP §4.3 case (a) algebra
witness for `linear_combination`. The S5 ACT picker owes ~30-60 min
pencil work for the witness coefficients (S10 §11 honesty note).

A small follow-up **S7b ACT** can re-add the two unit-square /
perturbed-square numerical sanity checks using
`Matrix.det_succ_row_zero` + `Matrix.det_fin_three` expansion (or
`Matrix.det_eq_zero_of_row_eq` for the Δ = 0 case — rows 1+3 = rows
2+4 gives an immediate row dependency). This is optional / cosmetic
and does not block S3-S6 ACT.

Suggested order (post-S10):

1. **S5 ACT first × Option A × Path α** (highest-leverage pick,
   ~25-35 LOC): paste S10 §4.1 skeleton; derive `linear_combination`
   witness from S5 PREP §4.3 case (a). Closes the chord-product →
   Δ = 0 bridge directly under Option A.

2. **S4 ACT × Patched Path A** (~35-40 LOC; orthogonal to S5, S10
   §4.3): close the (⇒) direction `concyclic → Δ = 0` via column-update
   (`det_updateCol_add_smul_self ×3 + det_eq_zero_of_column_eq_zero`)
   per S8 §5.2.

3. **S3 ACT × Cramer (post-S8 §4)** (~80-90 LOC; orthogonal to S5,
   S10 §4.4): replace the `(hNonCollinear : True)` placeholder with
   the algebraic 2×2 non-collinearity (Choice 1b); discharge the (⇐)
   direction via `Matrix.cramer` (`cramer_apply` is `rfl` at pin)
   per S3 PREP §2-§3 with S8 bearer corrections.

4. **S6 ACT — 4-step parent axiom discharge** (S10 §5, ~25-40 LOC):
   - **6a**: Restate parent axiom (line 468) and theorem (line 481)
     under Option A signed hypothesis.
   - **6b**: Update one downstream caller (only `converse_product_implies_concyclic`
     at line 481 known).
   - **6c**: Chain S3-S5 ACT and discharge the restated axiom
     (~10 LOC assembly).
   - **6d**: Update parent gallery `src/data/proofs/product-of-segments-of-chords/meta.json`:
     `axiomCount` 1 → 0; `status` toward `"verified"`.

5. **Build via Docker wrapper**:
   `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChordsOQ03`
   AND `./proofs/scripts/docker-build.sh Proofs.ProductOfSegmentsOfChords`.

Expected S3-S6 ACT chain (post-S10 footprint): **~165-205 LOC, 1
sorry → 0, parent `axiomCount` 1 → 0**.

## Subsequent Plan

| Session | Goal | Lines | Sorries |
|---------|------|-------|---------|
| S2 (done)            | Define `concyclicityDet`, state main theorem with sorry | 106 | +1 |
| S3 PREP (done)       | Cramer (⇐) design memo (doc-only) | +307 doc | 0 |
| S4 PREP (done)       | Row-reduction (⇒) design memo (doc-only) | +200 doc | 0 |
| S5 PREP (done)       | Chord-product → Δ = 0 bridge memo (doc-only) | +180 doc | 0 |
| S6 STATE-SYNC (done) | Doc-only refresh of state.md + JSON | 0 Lean | 0 |
| S7 ACT BUILD-VERIFY (done) | v4.26.0 import unblocker + dead-example removal | -3 net Lean, +18 doc | 0 |
| S8 PREP (done)       | Mathlib v4.26.0 bearer re-verification + S4 ACT Path A switch (doc-only) | 0 Lean, +860 doc | 0 |
| S9 PREP (done)       | `Δ=12≠0` counterexample + Option A signed hypothesis recovery (doc-only) | 0 Lean, +620 doc | 0 |
| S10 PREP (done)      | ACT-readiness gate: harmonized S5 ACT skeleton + S6 ACT 4-step tree (doc-only) | 0 Lean, +860 doc | 0 |
| **S11 STATE-SYNC** (this) | Doc-only refresh of state.md + JSON after S8/S9/S10 | 0 Lean, +500 doc | 0 |
| **S5 ACT** (pending, recommended next) | Signed inner-product → Δ = 0 (`concyclicityDet_eq_zero_of_signed_chord_product`, S10 §4.1 skeleton) | ~25-35 | -1 if standalone; -0+0 if iff-packaged |
| **S4 ACT** (pending) | (⇒) `concyclic → Δ = 0` via Patched Path A column-update | ~35-40 | -1 (packaging-dependent) |
| **S3 ACT** (pending) | (⇐) `Δ = 0 ∧ non-collinear → ∃ O r ...` via Cramer (`cramer_apply` is `rfl`) | ~80-90 | -0+0 (close 1, open 1 if iff-packaged; or close 1 if standalone) |
| **S6 ACT** (pending) | Parent axiom signature swap (Option A) + caller update + S3-S5 ACT chain + parent gallery `meta.json` `axiomCount` 1 → 0 | ~25-40 | parent ax 1 → 0 |
| S7b ACT (optional) | Re-add 2 numerical sanity checks via `det_succ_row_zero` / row-dep | ~15 | 0 |

Total after S6 (post-S10 footprint): **~165-205 LOC** of new Lean
content (atop S2's 111 LOC post-S7), parent axiom discharged. The S5
ACT slimmed by ~15 LOC vs the pre-S10 plan (Option A's case-(b)
elimination); S4 ACT grew by ~5-10 LOC (column-update vs row-reduction);
S6 ACT grew by ~15-30 LOC (axiom signature swap + caller update).

## Attempt Counts

- Total iterations: 11 (S1, S2, S3, S4, S5, S6, S7, S8, S9, S10, S11)
- Lean iterations: 2 (S2 SCAFFOLD PR #18380; S7 ACT BUILD-VERIFY PR #19096)
- PREP iterations: 6 (S3 / S4 / S5 / S8 / S9 / S10)
- STATE-SYNC iterations: 2 (S6, S11 — this PR)
- ACT iterations: 1 (S7 — build unblocker; S3-S6 ACT still pending)
- Approaches tried:
  - S1 OBSERVE (researcher-11, 2026-05-12): determinant-criterion ↔
    power-of-a-point bridge; numerical Δ = 0 / Δ = -6 verification
    (S1 wrote -8 — a hand slip; corrected at S17).
  - S2 SCAFFOLD (researcher-3, 2026-05-12): `concyclicityDet` def +
    `Vec2` wrapper + 2 numerical examples (build pending — assumed
    `Matrix.det_fin_four` exists, which it doesn't).
  - S3 PREP (researcher-9, 2026-05-13): Cramer's rule discharge
    design for (⇐); 3-friction-point map (Vec2 ↔ Fin 2 → ℝ,
    `‖·‖` on EuclideanSpace, Real.sqrt positivity).
  - S4 PREP (researcher-12, 2026-05-13): (⇒) direction via row
    reduction; Choice A (iff packaging) recommended.
  - S5 PREP (researcher-5, 2026-05-13): chord-product → Δ = 0
    bridge via row-subtract identity + chord_roots_product Vieta.
  - S6 STATE-SYNC (researcher-9, 2026-05-14): doc-only refresh of
    state.md / JSON.
  - S7 ACT BUILD-VERIFY (researcher-12, 2026-05-15): Mathlib v4.26.0
    import unblocker (1-LOC path swap) + removal of two
    `Matrix.det_fin_four`-dependent dead `example`s; Docker-verified
    3058 jobs clean.
  - S8 PREP (researcher-9, 2026-05-15): Mathlib v4.26.0 bearer
    re-verification at pin `2df2f015…`; `det_fin_four` confirmed
    missing across all of Mathlib4; S4 ACT recommendation flipped
    from Path B → Patched Path A.
  - S9 PREP (researcher-8, 2026-05-15): concrete `Δ=12≠0`
    counterexample to parent axiom under unsigned chord-product
    hypothesis; **Option A** signed inner-product hypothesis
    recommended.
  - S10 PREP (researcher-3, 2026-05-15): synthesis of S8 + S9 into
    unified S5 ACT skeleton (Option A × Path α `det_succ_row_zero +
    det_fin_three`); 10 inner-product bearer rows pinned; S6 ACT
    4-step decision tree staged; ACT-readiness verdict GREEN.
  - S11 STATE-SYNC (researcher-1, 2026-05-15, this PR): doc-only
    refresh of state.md + JSON after S8/S9/S10 PREPs; manifest pin
    re-verified unchanged; 0 substantive bearer drift since S8.

## Open files

- `problem.md` — full formal statement, Mathlib API map (S1).
- `knowledge.md` — S1 mathematical landscape + numerical
  verification.
- `state.md` — this file (refreshed S11).
- `sessions/2026-05-13-s3-prep-cramer-design.md` (S3 PREP)
- `sessions/2026-05-13-s04-prep-concyclic-implies-det-zero.md` (S4 PREP)
- `sessions/2026-05-13-s5-prep-chord-product-to-det-zero-bridge.md` (S5 PREP)
- `sessions/2026-05-14-s6-state-sync-prep-backlog.md` (S6 STATE-SYNC)
- `sessions/2026-05-14-s7-act-build-verify-mathlib-v426-import-unblocker.md` (S7 ACT)
- `sessions/2026-05-14-s8-prep-mathlib-v426-bearer-reverify.md` (S8 PREP)
- `sessions/2026-05-14-s9-prep-axiom-counterexample-and-sign-recovery.md` (S9 PREP)
- `sessions/2026-05-15-s10-prep-act-readiness-gate-post-s8-s9.md` (S10 PREP)
- `sessions/2026-05-15-s11-state-sync-post-s8-s9-s10.md` — added by this PR.

## S11 STATE-SYNC Deliverable (this PR)

Doc-only refresh; 0 Lean changes; closes the post-S7 doc-staleness
window after three sibling PREPs (S8 / S9 / S10) merged without
touching `state.md` / JSON. Manifest pin `2df2f015…` re-verified
unchanged since S8 wrote (~31 hours wall-clock, 0 substantive bearer
drift; 1 line-number nit carried from S10 §2.1).

Files touched (3):

- `research/problems/product-of-segments-of-chords-oq-03/state.md` —
  this refresh: Current State / Current Focus / Lean status / Ledger /
  discharge plan / S5 PREP+S8 PREP+S9 PREP+S10 PREP key sections /
  Active Approach / Blockers / Next Action / Subsequent Plan /
  Attempt Counts / Open files.
- `src/data/research/problems/product-of-segments-of-chords-oq-03.json` —
  `currentState.{since,iteration,focus,nextAction,attemptCounts}`,
  `knowledge.progressSummary`, `knowledge.nextSteps`, `lastUpdatedAt`;
  plus drift fixes on `leanFiles[0].lineCount` 542 → 541,
  `leanFiles[2].lineCount` 112 → 111,
  `leanFiles[2].sorryCount` 3 → 1.
- `research/problems/product-of-segments-of-chords-oq-03/sessions/2026-05-15-s11-state-sync-post-s8-s9-s10.md` —
  new session log (this STATE-SYNC).

No Lean file edited. No build invocation. No parent-gallery
`meta.json` edit. Docker build status carried over from S7 ACT
BUILD-VERIFY (#19096, merged 22:59:25Z): **3058 jobs clean** at line
109 single-sorry warning.

## S7 ACT BUILD-VERIFY Deliverable (retained for ledger continuity)

The S7 ACT BUILD-VERIFY iteration (PR #19096, researcher-12,
merged 2026-05-15T22:59:25Z) was **the first Lean diff since S2 SCAFFOLD**:

- 0 new theorems
- 0 new sorries (count unchanged at 1)
- 0 axiom changes (count unchanged at 0)
- 1 Lean file modified (import path + 2 dead examples removed)

Lean diff summary:

| File | Change |
|------|--------|
| `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:3` | `Mathlib.Data.Matrix.Notation` → `Mathlib.LinearAlgebra.Matrix.Notation` |
| `proofs/Proofs/ProductOfSegmentsOfChordsOQ03.lean:69-89` | Two `example`s using `Matrix.det_fin_four` (which does not exist in Mathlib v4.26.0) excised; replaced with a `/-! ## Part 3 -/` doc block explaining the regression and the S7b ACT follow-up. |

Docker build for S7: **3058 jobs clean** (only the expected `sorry`
warning at line 109 on the headline iff theorem). Parent file
`proofs/Proofs/ProductOfSegmentsOfChords.lean` does NOT import
`Mathlib.Data.Matrix.Notation` so is unaffected by this regression.

## References

- Parent file: `proofs/Proofs/ProductOfSegmentsOfChords.lean:468`
  (`converse_product_implies_concyclic_axiom` — the discharge target).
- Parent gallery: `src/data/proofs/product-of-segments-of-chords/`.
- Parent openQuestion #3: `meta.json:conclusion.openQuestions[2]`.
- See `problem.md` for full formal statement.
- See `knowledge.md` for Mathlib API survey and proof strategy.
- PR #19096 (S7 ACT BUILD-VERIFY): Mathlib v4.26.0 import unblocker; 3058 jobs clean.
- PR #19231 (S8 PREP): Mathlib v4.26.0 bearer re-verification; `det_fin_four` confirmed missing; S4 Path A switch.
- PR #19246 (S9 PREP): `Δ=12≠0` counterexample; Option A signed inner-product hypothesis.
- PR #19312 (S10 PREP): ACT-readiness gate; unified S5 ACT skeleton; S6 ACT 4-step decision tree.
- This PR (S11 STATE-SYNC): doc-only refresh of state.md + JSON; manifest pin re-verified unchanged; ACT-readiness GREEN re-confirmed.
