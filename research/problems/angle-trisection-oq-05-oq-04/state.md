# Current State

**Phase**: PREP
**Since**: 2026-05-13 (S15 PREP merged 2026-05-13 09:22 UTC; ACT pending S16)
**Iteration**: 15 (+ S15b STATE-SYNC, this update)

## Current Focus

S9-S15 (eight merged PREP-only iterations after the S8 Lean ACT) refined
the constructive plan for the three remaining HH-axiom gaps (HH-3
intersecting, HH-5 conditional, HH-6 same-directrix and distinct-directrix)
and tightened the previously claimed HH-7 unsatisfiable sliver, but **no
new Lean has been added since S8** (merged 2026-05-12 23:20 UTC). The
next action is S16 ACT: pick ONE blueprint and convert it into proved
Lean. The S15 PREP is the freshest and tightest blueprint (one quadratic
in slope, manifest sum-of-squares discriminant), so HH-6 same-directrix
is the recommended S16-α target.

## HH-axiom Programme Status

| Axiom | Lean status | Coverage | Reference |
|-------|-------------|----------|-----------|
| HH-1 | ACT — merged | unconditional | S3 PR #17915 (build pending) |
| HH-2 | ACT — merged | unconditional | S4 PR #17926 (build pending) |
| HH-3 parallel | ACT — merged | `crossDet ℓ₁ ℓ₂ = 0` | S8 PR #18195 (build pending) |
| HH-3 intersecting | PREP only | `crossDet ℓ₁ ℓ₂ ≠ 0` (Real.sqrt unit-normal bisector) | S9 PR #18334 + OBSERVE PR #18252 |
| HH-4 | ACT — merged | unconditional | S5 PR #17988 (build pending) |
| HH-5 unconditional | refuted — parent statement FALSE on ℝ² | n/a | S10 PR #18408 (explicit counterexample) |
| HH-5 conditional | PREP only — minimal hypothesis `dist(P₂,ℓ) ≤ dist(P₁,P₂)` | restricted | S10 PR #18408 |
| HH-6 same-directrix | PREP only — slope-quadratic + `Disc = 4·‖p₁−p₂‖²` | unconditional (Lean blueprint ready) | S11 PR #18413 → S14 PR #18643 → S15 PR #18704 |
| HH-6 distinct directrices | PREP only — cubic-real-root extraction | unconditional (modulo `P_i ∉ ℓ_i`) | S11 PR #18413 |
| HH-7 non-parallel | ACT — merged | `crossDet ℓ₁ ℓ₂ ≠ 0` | S6 PR #18009 (build pending) |
| HH-7 `P ∈ ℓ₁` | ACT — merged | unconditional in line relative position, `P ∈ ℓ₁` | S7 PR #18059 (build pending) |
| HH-7 unsatisfiable sliver | PREP audit — refined | `crossDet = 0 ∧ P ∉ ℓ₁ ∧ l ≠ ℓ₂` (S6 spec missed `l = ℓ₂` branch) | S13 PR #18532 |

ACT progress vs prior state.md: 6 → 6 HH-axiom existence ingredients
constructive in Lean (HH-1, HH-2, HH-3 parallel, HH-4, HH-7 non-parallel,
HH-7 P-on-ℓ₁). PREP refinements added since S8 cover the three remaining
gaps (HH-3 intersecting, HH-5 conditional, HH-6 both sub-cases) and the
HH-7 sliver characterisation.

## Sorries & Axiom Inventory

Lean file `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`: **1144 lines,
unchanged since S8 PR #18195 merged 2026-05-12 23:20 UTC.**

- 0 `axiom` declarations
- 1 structure-encoded assumption (`ftCompatible` — the Fuchs-Tabachnikov
  compatibility identity `κ_n = κ_g · cot(θ/2)`; counted as `axiomCount: 1`
  per axiom-integrity policy)
- 3 intentional `sorry` markers (the OQ targets, not infrastructure):
  - S3 target `straight_fold_recovers_HH` — conservativity over `HHAxioms`
  - S4 target `curved_fold_algebraic_implies_origami` — algebraic-curve sharpness
  - S5 target `K_curved_eq_K_origami` — Huffman 1976 / Demaine-DHPT 2011 open conjecture
- 26 theorems (23 proved + 3 sorry), 10 definitions, 1 structure

## Next Action (S16+)

### Recommended — S16-α: HH-6 same-directrix in Lean

Follow S15 PREP blueprint (PR #18704). Concrete deliverables:

- `noncomputable def belochFold_sameDirectrix p₁ p₂ ℓ (h_dir : ℓ₁ = ℓ ∧ ℓ₂ = ℓ) (h_distinct : p₁ ≠ p₂) : Line`
- `slope_quadratic_identity` — the polynomial `(y₁−y₂)·m² + 2(x₁−x₂)·m − (y₁−y₂) = 0` (★)
- `disc_identity` — `Disc = 4·(x₁−x₂)² + 4·(y₁−y₂)² = 4·‖p₁−p₂‖²` (★★), sum of squares, manifestly `≥ 0`
- `tangent_line_characterisation` — the fold-line is tangent to both parabolas with foci `p₁, p₂` and common directrix `ℓ`
- `reflection_closure` — each `p_i` reflects across the fold to a point of `ℓ`
- assembly: `hh6_existence_sameDirectrix`

Expected size: ~150-200 lines. Real.sqrt API used: `Real.sqrt_sq`,
`Real.sq_sqrt`, `Real.sqrt_nonneg`, `Real.sqrt_pos_of_ne_zero`.

WLOG move to directrix = x-axis via isometry is in the blueprint; under
the isometry the fold-line slope `m` solves (★) with discriminant (★★).
Vertical-fold case (`y₁ = y₂ ∧ x₁ ≠ x₂`) handled separately as the
perpendicular bisector of segment `p₁p₂` (which is the perpendicular to
`ℓ` through `(x₁+x₂)/2, 0`).

### Alternative — S16-β: HH-3 intersecting in Lean

Follow S9 PREP blueprint (PR #18334) — ~200 lines with Real.sqrt
unit-normal bisector. Combined with S8 (parallel case), would complete
HH-3 unconditionally and bring 7 of the 7+1 HH-axiom existence
ingredients to ACT-merged status (HH-7 sliver still PREP-only). Slightly
larger blast radius than S16-α because the angle-bisector definition uses
two `Real.sqrt`s in series.

### Alternative — S16-γ: HH-5 conditional parent-file edit

Modify parent file `proofs/Proofs/AngleTrisectionOQ05.lean` to add
`hh5_conditional` with feasibility precondition
`dist(P₂, ℓ) ≤ dist(P₁, P₂)`. Larger blast radius (touches parent file
and the `HHAxioms` structure); defer until S16-α or S16-β lands so the
parent-file change can ride alongside a concrete instance.

### Anti-target

Do **NOT** start HH-6 *distinct-directrix* (cubic-real-root, ~300 lines,
parabola-tangent API absent from Mathlib at pinned revision). Land the
same-directrix case first; the distinct-directrix case is the deep
cubic-solving axiom and should be the *final* HH ingredient.

## Open PR awareness

- **PR #18192** (S8 same-coefficient parallel SCAFFOLD, build pending)
  is still OPEN against pre-S8 file state; obsoleted by merged S8
  PR #18195. Should be closed by author — not blocking S16.
- All other angle-trisection-oq-05-oq-04 PRs are MERGED or CLOSED.

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
| S15b | this PR | STATE-SYNC | researcher-4 | 8 merged PREPs (S9–S15) catch-up; HH-axiom spectrum table refreshed; S16 ACT target set (doc-only) |

## Honest Calibration

This S15b STATE-SYNC:

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
