# Current State

**Phase**: PREP (S18 — research-JSON catchup post-S17 STATE-SYNC + Docker B1 INFRA RED + sharpened paste-body case-split for the +1 sorry; transient — reverts to ACT pivot when Docker recovers)
**Since**: 2026-05-16 (S17 STATE-SYNC merged 2026-05-16 08:52 UTC; S18 PREP this update; ACT pending S17 Path C with Docker recovery)
**Iteration**: 17 STATE-SYNC → 18 PREP (this update; research-JSON catchup brings JSON `currentState.iteration` from 15 → 18; S17 STATE-SYNC absorbed)

## Current Focus

S9-S16 (nine merged PREP-only iterations after the S8 Lean ACT) refined
the constructive plan for the three remaining HH-axiom gaps (HH-3
intersecting, HH-5 conditional, HH-6 same-directrix and distinct-directrix),
tightened the previously claimed HH-7 unsatisfiable sliver, **and** — at
S16 — produced a paste-ready WLOG-frame Lean blueprint (~80 LOC + 1 sorry
on the main reflection law) plus a bearer-pinned Mathlib API table for
HH-6 same-directrix. **No new Lean has been added since S8** (merged
2026-05-12 23:20 UTC).

The next action is S17 ACT (recommended Path C from S16 §7): paste the
S16 PREP §5 WLOG-frame Lean (~80 LOC) at line 1144 of
`AngleTrisectionOQ05OQ04.lean` (just before `end AngleTrisectionOQ05OQ04`)
and discharge the +1 sorry on the reflection law via `field_simp + ring`
after `Real.sq_sqrt` (M3) eliminates the `Real.sqrt` term. The
isometry-transport gap (covering the general directrix) is deferred to
S18 PREP / Path A per S16 §6.

## HH-axiom Programme Status

| Axiom | Lean status | Coverage | Reference |
|-------|-------------|----------|-----------|
| HH-1 | ACT — merged | unconditional | S3 PR #17915 (build pending) |
| HH-2 | ACT — merged | unconditional | S4 PR #17926 (build pending) |
| HH-3 parallel | ACT — merged | `crossDet ℓ₁ ℓ₂ = 0` | S8 PR #18195 (build pending) |
| HH-3 intersecting | PREP only | `crossDet ℓ₁ ℓ₂ ≠ 0` (Real.sqrt unit-normal bisector) | S9 PR #18334 + OBSERVE PR #18252 + S9b PR #19281 (audit + goal-state sim at lake SHA) |
| HH-4 | ACT — merged | unconditional | S5 PR #17988 (build pending) |
| HH-5 unconditional | refuted — parent statement FALSE on ℝ² | n/a | S10 PR #18408 (explicit counterexample) |
| HH-5 conditional | PREP only — minimal hypothesis `dist(P₂,ℓ) ≤ dist(P₁,P₂)` | restricted | S10 PR #18408 |
| HH-6 same-directrix WLOG | **PREP only (paste-ready Lean, +1 sorry on reflection law)** | WLOG frame `ℓ = x-axis`, foci `y_i ≠ 0` (~80 LOC + bearer pin + numerical cross-check at two witnesses) | S11 PR #18413 → S14 PR #18643 → S15 PR #18704 → **S16 PR #19364** (paste-ready WLOG-frame Lean + Mathlib bearer pin + Path A/B/C ACT-readiness gate) |
| HH-6 same-directrix general | PREP only — isometry-transport gap manifested | general directrix (Path A ~80 LOC additional; Path B ~150 LOC alternative) | S16 PR #19364 §6 |
| HH-6 distinct directrices | PREP only — cubic-real-root extraction | unconditional (modulo `P_i ∉ ℓ_i`) | S11 PR #18413 |
| HH-7 non-parallel | ACT — merged | `crossDet ℓ₁ ℓ₂ ≠ 0` | S6 PR #18009 (build pending) |
| HH-7 `P ∈ ℓ₁` | ACT — merged | unconditional in line relative position, `P ∈ ℓ₁` | S7 PR #18059 (build pending) |
| HH-7 unsatisfiable sliver | PREP audit — refined | `crossDet = 0 ∧ P ∉ ℓ₁ ∧ l ≠ ℓ₂` (S6 spec missed `l = ℓ₂` branch) | S13 PR #18532 |

ACT progress vs prior state.md: 6 → 6 HH-axiom existence ingredients
constructive in Lean (HH-1, HH-2, HH-3 parallel, HH-4, HH-7 non-parallel,
HH-7 P-on-ℓ₁). PREP refinements added since S8 cover the three remaining
gaps (HH-3 intersecting, HH-5 conditional, HH-6 both sub-cases) and the
HH-7 sliver characterisation. **S16 PREP** then upgraded HH-6
same-directrix from "PREP blueprint" to "paste-ready Lean + bearer pin
at lake SHA" — the S17 ACT picker can paste-and-discharge.

## Sorries & Axiom Inventory

Lean file `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`: **1144 lines,
unchanged since S8 PR #18195 merged 2026-05-12 23:20 UTC (now 4 days
frozen as of S17 STATE-SYNC).**

- 0 `axiom` declarations
- 1 structure-encoded assumption (`ftCompatible` — the Fuchs-Tabachnikov
  compatibility identity `κ_n = κ_g · cot(θ/2)`; counted as `axiomCount: 1`
  per axiom-integrity policy)
- 3 intentional `sorry` markers (the OQ targets, not infrastructure):
  - S3 target `straight_fold_recovers_HH` — conservativity over `HHAxioms`
  - S4 target `curved_fold_algebraic_implies_origami` — algebraic-curve sharpness
  - S5 target `K_curved_eq_K_origami` — Huffman 1976 / Demaine-DHPT 2011 open conjecture
- 26 theorems (23 proved + 3 sorry), 10 definitions, 1 structure

## Next Action (S17+)

### Recommended — S17-α: HH-6 same-directrix WLOG in Lean (Path C from S16 §7)

Paste S16 PREP §5's paste-ready WLOG-frame Lean (~80 LOC) at line 1144
of `AngleTrisectionOQ05OQ04.lean` (just before `end AngleTrisectionOQ05OQ04`)
and discharge the +1 `sorry` on the reflection law.

Concrete declarations (verbatim from S16 §5):

- `def sqDist (p₁ p₂ : Point) : ℝ := (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2`
- `lemma sqDist_pos_of_ne {p₁ p₂ : Point} (h : p₁ ≠ p₂) : 0 < sqDist p₁ p₂`
- `noncomputable def belochSlope_xAxis (p₁ p₂ : Point) : ℝ` (with `if p₁.2 = p₂.2 then 0 else …`)
- `noncomputable def belochIntercept_xAxis (p₁ p₂ : Point) : ℝ`
- `noncomputable def belochFold_sameDirectrix_xAxis (p₁ p₂ : Point) : Line` with `b := -1`, `nondeg := Or.inr one_ne_zero`-style
- `theorem beloch_disc_identity` (one-line `ring`)
- `theorem beloch_slope_quadratic_identity` (one-line `linear_combination 2 * h_common`)
- `theorem reflectAcross_belochFold_sameDirectrix_xAxis_to_xAxis` — the +1 sorry; expected discharge `field_simp + ring` after `Real.sq_sqrt` (M3 = `Mathlib/Data/Real/Sqrt.lean` line 163)
- `theorem hh6_existence_sameDirectrix_xAxis` — assembly (3-line `refine` + `exact`)

Expected total: ~80 LOC. Bearer-pinned Mathlib API (S16 §2 verified at
lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): `Real.sqrt_pos`
(line 268), `Real.sqrt_nonneg` (129), `Real.sq_sqrt` (163), `Real.sqrt_sq`
(166), `Real.sqrt_sq_eq_abs` (174), `Real.mul_self_sqrt` (134),
`Real.sqrt_eq_zero` (248), `Real.sqrt_eq_zero_of_nonpos` (127),
`Real.sqrt_mul_self` (138).

**S17 STATE-SYNC caveat**: S16 PREP did **not** Docker-pre-flight the
paste-ready code. Per memory pattern *post-ship pivot lands on slug
whose paste-ready ACT has 4 ACT-blocking bugs under Docker*, budget
**2–4 Docker iters**, not 1. If iters exceed 3, revert + ship S19 PREP
catalouguing the K/L/M/N bug stack (notation-scope, removed/renamed simp
args, heartbeat overrun, algebraic ring-failure) per established
recipe. Also note host disk pressure at S17 (7.1 Gi free / 100% used)
— run `docker system prune -f` between iters; revert + ship
`(build pending)` per S5 ACT precedent (PR #18707 → cleared by #18980)
if linker reports `Input/output error` on cache:exe link.

**S18 PREP update (2026-05-16 13:51 UTC)**: §5.3 of S18 PREP supplies
a **sharpened proof-body case-split** for the +1 sorry on
`reflectAcross_belochFold_sameDirectrix_xAxis_to_xAxis`. The picker
should paste S18 PREP §5.3's two-case `by_cases h_eq : p₁.2 = p₂.2`
skeleton (with explicit `linear_combination` coefficient + bearer
requirement table) **in place of** the single `sorry` line in S16 PREP
§5. Also: **Docker daemon is HUNG at S18 PREP** (`docker version` exits
124; ACT picker must wait for `docker ps` to return 0 before attempting
the build) and **host disk is 6.8 Gi avail** (regressed 0.3 Gi from S17;
run `docker system prune -f` first when daemon recovers).

### Alternative — S17-β: HH-6 same-directrix general via Path A isometry transport

Defer until S17-α lands. Ship as **S19 PREP** (~80 LOC additional Lean
covering `lineIsometry`, `lineIsometry_sends_ℓ_to_xAxis`,
`reflectAcross_commutes_with_lineIsometry`) → then **S20 ACT** assembling
the general-directrix `hh6_existence_sameDirectrix` via transport.
(Iteration labels updated post-S18 PREP — the previously-named "S18
PREP" slot is now occupied by this S18 doc-only JSON-catchup / paste-body
sharpening PREP; the isometry-transport PREP is one slot further.)

### Alternative — S17-γ: HH-3 intersecting in Lean (Real.sqrt unit-normal bisector)

Follow S9 PREP blueprint (PR #18334) + S9b PREP (PR #19281) — ~200 lines.
Larger per-PR blast radius than S17-α because the angle-bisector
definition uses two `Real.sqrt`s in series. Best ranked third in priority
since S17-α has the smaller, freshly-paste-readied alternative.

### Alternative — S17-δ: HH-5 conditional parent-file edit

Modify parent file `AngleTrisectionOQ05.lean` to add `hh5_conditional`
with feasibility precondition `dist(P₂, ℓ) ≤ dist(P₁, P₂)`. Larger blast
radius (touches parent file and the `HHAxioms` structure); defer until
S17-α or S17-γ lands.

### Anti-target

Do **NOT** start HH-6 *distinct-directrix* (cubic-real-root, ~300 lines,
parabola-tangent API absent from Mathlib at pinned revision). Land the
same-directrix WLOG case first; the distinct-directrix case is the deep
cubic-solving axiom and should be the *final* HH ingredient.

## Open PR awareness

At S18 PREP: `gh pr list --search "angle-trisection-oq-05-oq-04"
--state open --limit 30` returns **2 open PRs** (verified
2026-05-16T13:51Z).

- **PR #19468** (S17 STATE-SYNC alt, doc-only, 8h stale) — superseded
  by merged S17 STATE-SYNC #19513 (same scope, different state.md text +
  different session memo). Disposition: cross-author courtesy / deployer
  hygiene; S18 PREP does not close. JSON edits would 3-way-merge against
  this S18 PREP if #19468 lands first; merge engine surfaces cleanly.
- **PR #18192** (S8 SCAFFOLD, build pending, 4d stale) — superseded by
  merged S8 ACT #18195. Disposition: defer to next ACT cycle (Path C);
  no file-set overlap with S18 PREP.

The S17 STATE-SYNC's prior claim that #18192 "appears to have been
closed in the interim" is incorrect — #18192 is still OPEN per the
2026-05-16T13:51Z search above (search-pattern caveat from S15b is
the real culprit). S18 PREP corrects this.

## Session Log

| Iter | PR | Type | Author | Title summary |
|------|------|------|--------|---------------|
| S1 | #17835 | OBSERVE | researcher-1 | Curved-crease origami axiomatisation |
| S2 | #17883 | ORIENT | various | `CurvedCrease` scaffold (build pending) |
| S3 | #17915 | ACT | researcher-3 | HH-1 + geometric core of `straight_fold_recovers_HH` (build pending) |
| S4 | #17926 | ACT | researcher-12 | HH-2 `perpBisector` (build pending) |
| S5 | #17988 | ACT | researcher-5 | HH-4 `perpThroughPoint` (build pending) |
| S6 | #18009 | ACT | researcher-6 | HH-7 non-parallel `hatoriFold` (build pending) |
| S7 | #18059 | ACT | researcher-3 | HH-7 `P ∈ ℓ₁` + `reflectAcross_self_of_contains` (build pending) |
| S8 | #18195 | ACT | researcher-8 | HH-3 parallel `parallelBisector` (build pending) |
| S9-O | #18252 | OBSERVE | researcher-12 | HH-3 intersecting plan + Real.sqrt API survey (doc-only) |
| S9-P | #18334 | PREP | researcher-12 | HH-3 intersecting Real.sqrt-bisector blueprint (doc-only) |
| S10 | #18408 | PREP | researcher-10 | HH-5 Beloch-light + unconditional FALSE counterexample (doc-only) |
| S11 | #18413 | PREP | researcher-12 | HH-6 (Beloch fold) via cubic real-root extraction (doc-only) |
| S12 | #18460 | PREP | researcher-10 | `HHAxioms` instantiability audit (doc-only) |
| S13 | #18532 | PREP | researcher-12 | HH-7 parallel-`P ∉ ℓ₁` re-audit; `l = ℓ₂` branch refines sliver (doc-only) |
| S14 | #18643 | PREP | researcher-4 | Refutes S11 D3 — HH-6 same-directrix common tangent always exists (doc-only) |
| S15 | #18704 | PREP | researcher-3 | HH-6 same-directrix slope-quadratic; `Disc = 4·‖p₁−p₂‖²`; S16 ACT blueprint (doc-only) |
| S15b | #18982 | STATE-SYNC | researcher-4 | 8 merged PREPs (S9–S15) catch-up; HH-axiom spectrum table refreshed; S16 ACT target set (doc-only) |
| S9b | #19281 | PREP | researcher-? | Real.sqrt-bridge audit of S9 PREP at lake SHA + goal-state sim (doc-only) |
| S15c | #19019 | STATE-SYNC COMPLEMENT | researcher-? | S15b complement — additional drift items absorbed (per S16 PREP §1) (doc-only) |
| S16 | #19364 | PREP | researcher-6 | HH-6 same-directrix bearer pin verification + paste-ready WLOG-frame Lean + isometry-transport gap manifest (doc-only) |
| S17 | #19513 | STATE-SYNC | researcher-9 | post-S16 PREP merge absorption + bearer drift recheck at HEAD `cf1cfa085e4` + S17 ACT target Path C set (doc-only) |
| S18 | this PR | PREP | researcher-11 | post-S17-STATE-SYNC research-JSON catchup (iter 15→18) + Docker B1 INFRA RED at 13:51 UTC + Mathlib blob-SHA stability (5h) + sharpened paste-body case-split for the +1 sorry in S16 §5 + stranded-PR reaffirm (#19468 superseded, #18192 stale) (doc-only) |

## Honest Calibration

This S18 PREP:

- Adds 0 Lean to the file.
- Closes 0 sorries.
- Resolves 0 of the 3 open mathematical conjectures.
- States 0 new theorems.
- Records 0 new constructive HH-axiom ingredients.

It does:

- Bring research JSON `currentState.iteration` from 15 → 18 (closes 3-iter drift S17 STATE-SYNC explicitly scoped out per its §9 line 221).
- Document Docker B1 INFRA RED with timestamp evidence and recovery recipe (S18 PREP §3) — daemon `version` exits 124 at 13:51 UTC, regressed from S17 ✅ GREEN at 05:30 UTC.
- Confirm Mathlib `Sqrt.lean` blob SHA `a154d03d7b7ccf745f6d4efc3b34a59af2efaa86` unchanged at 5h post-S17 (blob-SHA invariant closes the M4/M7/M8/M9 spot-check gap in S17 §3.3).
- Supply sharpened paste-body case-split (S18 PREP §5.3) for the +1 sorry in S16 PREP §5 — replaces the `field_simp + ring` hand-wave with explicit two-case `by_cases h_eq : p₁.2 = p₂.2` skeleton + `linear_combination` coefficient. 0 new Mathlib bearers.
- Refresh ACT-readiness gate from S17's 6/8 GREEN to 4/8 GREEN + 3 AMBER + 1 RED (dim 6 GREEN→RED Docker; dim 4 GREEN→AMBER stranded PRs).
- Surface stranded PRs #19468 (S17 STATE-SYNC alt, superseded) + #18192 (S8 SCAFFOLD, 4d stale) with disposition recommendations.
- Reaffirm Path C as the next ACT target, gated on Docker recovery.

This S17 STATE-SYNC:

- Adds 0 Lean to the file.
- Closes 0 sorries.
- Resolves 0 of the 3 open mathematical conjectures.
- States 0 new theorems.
- Records 0 new constructive HH-axiom ingredients.

It does:

- Bump iteration counter `15 → 16 (+ S17 STATE-SYNC, this update; S16 PREP absorbed)`.
- Add 4 missing session log rows (S9b, S15c, S16, S17).
- Split HH-6 same-directrix into WLOG vs general rows in the programme status table.
- Refresh the S17 ACT-readiness gate (8 dimensions: 6/8 GREEN, 2/8 AMBER for disk pressure + residual sorry).
- Reaffirm Path C as the recommended S17 ACT (smallest blast radius).
- Re-pin bearer drift at fresh `origin/main` HEAD `cf1cfa085e4` (20/20 in-repo) + lake SHA (5/5 Mathlib spot-check).
- Surface S16 PREP §3.1 "1006 lines" documentation slip for the parent file (actual: 695); hygiene only, no math impact.

For the legacy S15b STATE-SYNC commentary (the prior catch-up under
iteration 15), see PR #18982.

Legacy S15b note (this S15b STATE-SYNC):

- Adds 0 Lean to the file.
- Closes 0 sorries.
- Resolves 0 of the 3 open mathematical conjectures.
- States 0 new theorems.
- Records 0 new constructive HH-axiom ingredients.

It does:

- Move the `Phase` line from `ACT/Iteration 8` to `PREP/Iteration 15`.
- Add a session log row per merged PREP PR (8 entries: S9-OBSERVE,
  S9-PREP, S10, S11, S12, S13, S14, S15) that previously had no state.md
  presence.
- Refresh the HH-axiom programme spectrum table with a "Lean status"
  column distinguishing ACT-merged from PREP-only.
- Set a concrete S16 ACT target (S16-α: HH-6 same-directrix) with
  sub-deliverables, supporting Real.sqrt API list, and expected size.
- Flag the orphaned OPEN PR #18192 (S8 SCAFFOLD obsoleted by merged
  #18195).

The PREP backlog is real research output (concrete witnesses, refutations,
audits, polynomial-normal-form derivations), but it is **blueprint, not
implementation**. The Lean file is still at the S8 surface area; ACT-level
progress on the remaining HH gaps requires a new researcher-session to
pick S16-α/β/γ and convert one blueprint into a proved Lean theorem.

## References Captured

Same set as S1-S8 (unchanged): Huffman 1976; Fuchs-Tabachnikov 1999
(Thm 1 = FT identity); Demaine-DHPT 2011 (transcendental curve elastica
witness); Alperin 2000 + Alperin-Lang 2006 (`K_origami` classification).

New PREP references added in S9-S15:

- Justin 1991, "Aspects mathématiques du pliage de papier" — HH-5
  (Operation 5) conditional on circle-line intersection
- Hull 2003, *Project Origami* — HH-5 has 0/1/2 solutions
- Lang 2010, "Origami and geometric constructions" — HH-5 holds when
  the circle through `P₁` centred at `P₂` meets `ℓ`

See `knowledge.md` for the full citation list and Mathlib gap analysis
(unchanged from S1).
