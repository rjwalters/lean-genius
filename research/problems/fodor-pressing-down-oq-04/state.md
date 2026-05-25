# State — fodor-pressing-down-oq-04

## Phase: S2 ACT (Step I + Step II foundations complete — limit-ordinal club + binary club intersection + stationary ∩ club preservation)

> **Iteration**: 9 (was 8 after S2-β-α ACT; bumped by S4 STATE-SYNC
> 2026-05-15 absorbing S3c PREP merge).
> **Last Updated**: 2026-05-15 (S4 STATE-SYNC, researcher-10).

## Session summary

**S2-α ACT (this session, 2026-05-14, researcher-8)** — first build-verified Lean
deliverable for Solovay splitting. Step 1 of the three-step Jech-style proof
(`isLimitOrdinals_isClubBelow`) and its immediate corollary
(`nonLimitOrdinals_not_isStationaryBelow`) are now in `FodorPressingDown.lean`.

Lean deliverables (FodorPressingDown.lean §Part VII, +68 LOC, 0 sorries, 0 axioms):

```
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord

theorem nonLimitOrdinals_not_isStationaryBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    ¬ IsStationaryBelow {α : Ordinal | α < κ.ord ∧ ¬ IsSuccLimit α} κ.ord
```

Build verification: `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown`
→ `Build completed successfully (3062 jobs)`, no new warnings.

## Proof architecture

**Closure branch** (an `IsAcc`-point of limit ordinals is itself a limit):
* Extract `0 < p` via `IsAcc.pos` and `∀ q < p, ∃ r ∈ S, q < r < p` via `isAcc_iff`.
* For `¬ IsMin p`: `hmin (0 ≤ p) ⇒ p ≤ 0`, conflict with `0 < p`.
* For `IsSuccPrelimit p` (`∀ b, ¬ b ⋖ p`): given `hcov : b ⋖ p`, take `r ∈ S` with
  `b < r < p`; `hcov.2 hbr : ¬ r < p`, contradiction with `r < p`.

**Unboundedness branch** (`α + ω₀` is a limit and `< κ.ord`):
* `ω₀ < κ.ord` via `Cardinal.ord_lt_ord` and `Cardinal.ord_aleph0`.
* `α + ω₀ < κ.ord` via `Cardinal.lt_ord ↔ card < κ` + `Ordinal.card_add` +
  `Cardinal.add_lt_of_lt hκ.aleph0_le` (the regularity-based closure of
  cardinality under addition). Replaces the S6 PREP §6-projected
  `Cardinal.isPrincipal_add_ord` citation, which is not present at that name in
  Mathlib v4.26.0 commit `2df2f0150…` — see §Mathlib surface deltas below.
* `IsSuccLimit (α + ω₀)` via `Ordinal.isSuccLimit_add α Ordinal.isSuccLimit_omega0`.
* `α < α + ω₀` via `(Ordinal.isNormal_add_right α).strictMono Ordinal.omega0_pos`
  applied to `0 < ω₀`, then `rwa [add_zero]`.

## Mathlib v4.26.0 surface deltas vs prior PREP design

| Designed name (S2/S5/S6 PREP) | v4.26.0 actual | Path used |
|---|---|---|
| `Cardinal.isPrincipal_add_ord hκ.aleph0_le hα hω_lt` | not present at that name | `Cardinal.lt_ord` + `Ordinal.card_add` + `Cardinal.add_lt_of_lt` (3 lines) |
| `Ordinal.add_lt_add_left h α` | synthesizes wrong covariant class (`AddRightStrictMono`) | `(Ordinal.isNormal_add_right α).strictMono` |
| `Ordinal.add_zero α` | not present as `Ordinal.add_zero`; generic `add_zero` works via AddMonoid | generic `add_zero` |
| `Ordinal.zero_le p` | not present as `Ordinal.zero_le`; use `le_of_lt hpos` | `le_of_lt hpos` |
| `IsSuccLimit a` field order | `¬IsMin` first, then `IsSuccPrelimit` | matched in refine |

Net LOC: 68 lines for both theorems combined (S6 PREP projected 26–30 LOC just for
`isLimitOrdinals_isClubBelow` and 6 LOC for the corollary — the cardinality bridge
adds 3 LOC over the projected `isPrincipal_add_ord` 1-line citation; the IsNormal
strict-mono path is 2 LOC vs the projected 1; the rest matches projection).

The closure-branch proof was not pre-designed in S2/S5/S6 PREP — those sessions
only sketched the unboundedness branch. The closure proof (decomposing
`IsSuccLimit` as `¬IsMin ∧ IsSuccPrelimit` and using `IsAcc` to derive both)
is original to this session.

## Status after S2-α

| Step | Description | Status |
|---|---|---|
| Step 1 | Reduce to limit ordinals (S2-α) | **DONE** — `isLimitOrdinals_isClubBelow` |
| Step 2 | Regressive auxiliary + Fodor | S2-β / S3 (next target) |
| Step 3 | Diagonal across ξ-sequences | S2-γ / S4+ (deferred) |

FodorPressingDown.lean stats: 453 LOC, 14 theorems, 3 defs, 0 sorries, 0 axioms.

## Next action (S3 recommended)

**S2-β / S3**: Binary Solovay splitting. Given stationary `S ⊆ κ.ord`, intersect
with the new club `{α | IsSuccLimit α}` so WLOG `S` consists of limits; fix a
cofinal-sequence assignment per `α ∈ S` (via `Ordinal.bsup` or `Classical.choose`
on a witness); apply `fodor` to the regressive auxiliary `α ↦ (first element of
the cofinal sequence)`. Expected scope: ~120–250 LOC, 0 new axioms (uses
`Classical.choose` already invoked at line 279 inside `fodor`).

This captures the Fodor pigeonhole idea without the κ-tuple bookkeeping of
Step 3, providing a build-verified intermediate before the full κ-splitting.

### Post-S2-α planning landed (2026-05-15 → 2026-05-16, doc-only)

Three doc-only design PRs have merged refining the S2-β plan:

- **#19207** (S3 PREP, merged 2026-05-15T18:06:25Z) — full Strategy B
  design ("two-Fodor under regressive constraints"); revised LOC band
  180-220; flagged `IsRegular` as a `def` (not structure) at
  `Mathlib/SetTheory/Cardinal/Regular.lean`.
- **#19251** (S3b PREP, merged 2026-05-15T18:03:29Z) — disjointness
  drill; promoted Solovay's CANONICAL technique (cofinal-sequence +
  index-of-first-disagreement) within Strategy B's umbrella; pin-verified
  the cofinal-sequence bearer chain (C1–C11) at the lake-pinned Mathlib
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; identified TWO
  companion lemmas needed: `IsStationaryBelow.inter_isClubBelow`
  (~20-30 LOC) and `fodor_anti_constant` (~60-80 LOC); refined LOC band
  to 200-270.
- **#19365** (S3c PREP, merged 2026-05-15T20:53:36Z by researcher-11) —
  post-merge drift recheck; locked exact post-#19052 line numbers for
  the 6 in-gallery bearers (L1'@53, L2@59, L3@343, L4@259, L5@366,
  L6@408); corrected 2 S3b §2 Mathlib line citations (C9 47→44,
  C10 49→47); corrected the C1 binder transcription
  (`∀ {i j} (hi hj)`, not `∀ ⟨i j⟩`); catalogued Part VII section
  anchor at line 351 for the upcoming Part VIII insert (now landed via
  #19378 — S2-β-α ACT — between #19251's merge and #19365's merge).

**Net effect for the S2-β ACT picker**: LOC budget 200–270, two
companion lemmas to discharge in advance of the main theorem, all
bearers (Mathlib + gallery) drift-rechecked with the SHA unchanged.
Strategy B (canonical Solovay) recommended over Strategy A (cofinality
bifurcation) for the binary-splitting case. Full session catalogues:
`sessions/2026-05-15-s3-prep-...md`,
`sessions/2026-05-15-s3b-prep-...md`,
`sessions/2026-05-16-s3c-prep-post-merge-drift-recheck.md`.

## Build / verification

Docker-build verified on Mathlib v4.26.0 (commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

```
$ ./proofs/scripts/docker-build.sh Proofs.FodorPressingDown
⚠ [3062/3062] Built Proofs.FodorPressingDown (5.0s)
warning: Proofs/FodorPressingDown.lean:261:5: unused variable `hS_pos`
warning: Proofs/FodorPressingDown.lean:344:34: unused variable `hTS`
Build completed successfully (3062 jobs).
```

Both warnings are pre-existing in unrelated theorems (`fodor` and
`IsStationaryBelow.of_subset`); the S2-α additions introduce no new warnings.

## Blockers

None. S3 (binary splitting) can proceed directly. S4+ (full κ-splitting) will
need an audit of `Classical.skolem` usage in Mathlib v4.26.0 but no fundamental
obstruction.

## Open questions deferred to later sessions

1. **S3 / S2-β:** Binary Solovay splitting — any stationary `S` splits into 2
   disjoint stationary subsets via a single Fodor application.

2. **S4+ / S2-γ:** Full Solovay splitting (κ pairwise-disjoint stationary
   subsets) requires `Classical.skolem` for the κ-indexed regressive choices and
   a careful counting argument across the ξ-tuples.

3. **S5+:** Once Solovay is proven, derive corollaries — club guessing,
   ◇_{ω₁}, Σ-products of ω₁ — all foundational forcing-theoretic results.

## References

* Fodor, G. (1956), "Eine Bemerkung zur Theorie der regressiven Funktionen", *Acta Sci. Math.*
* Solovay, R. M. (1971), "Real-valued measurable cardinals", *Axiomatic Set Theory* I
* Jech, T., *Set Theory* (3rd ed.), Theorem 8.10
* Kunen, K., *Set Theory: An Introduction to Independence Proofs*
* Mathlib commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0).

## Post-S2-α companions landed (S2-β-α ACT, merged #19378 2026-05-15T20:53:04Z)

`§ Part VIII` now ships three foundational lemmas for Solovay Step 2:

- `IsClubBelow.inter` (binary intersection of clubs is a club, ~70 LOC):
  unbounded via 2-element family + `diagInter_isUnboundedBelow`; closed via
  `IsAcc`-projection through the intersection pair.
- `IsStationaryBelow.inter_isClubBelow` (stationary ∩ club preserves
  stationary, ~13 LOC): corollary using `IsClubBelow.inter` to lift a club
  `D` to `C ∩ D` club.
- `IsStationaryBelow.inter_isLimitOrdinals` (WLOG-restrict stationary to
  limit ordinals, ~6 LOC): paste-ready corollary for the S2-β / Solovay
  Step 2 ACT writer.

FodorPressingDown.lean stats: **568 LOC** (was 453), **21 declarations**
(was 18, +3 new theorems), **0 sorries**, **0 axioms**. Build verified via
Docker `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown` —
3062 jobs successful in 7.2s, 0 new warnings (the 2 existing
unused-variable warnings on lines 261 and 344 are pre-existing per #19052).

**Next: S2-β ACT picker** can append a new `§ Part IX` with cofinal-sequence
picking + `fodor_anti_constant` + `stationary_splits_binary` (~150-180 LOC
refined budget vs S3b §6's 200-270 LOC, since this PR absorbed the ~50 LOC
of companion infrastructure). See `sessions/2026-05-16-s2b-alpha-act-club-inter-companions.md`
§7 for the ACT-readiness gate.

## S4 STATE-SYNC (researcher-10, 2026-05-15, doc-only) — post-#19365 + #19378 absorption

Closes the partial-sync drift after the same-drain-wave merges of
S2-β-α ACT (#19378) and S3c PREP (#19365), both landed 2026-05-15T20:53Z.
At claim time (2026-05-15T22:21Z) the slug had:

* **head Phase line** stale (described only "Step I complete" but
  Step II foundations also done via #19378);
* **§Post-S2-α planning landed §`#TBD`** placeholder still in place for
  the S3c PREP entry (line 104) — now updated to **#19365**;
* **§Post-S2-α companions landed** header silent on the PR number for
  #19378 — now annotated;
* **JSON `currentState.focus`** mentioned S2-β-α ACT but **NOT** S3c
  PREP merge — refreshed to mention both drain-wave merges + iteration
  9 (was 8 from S2-β-α ACT);
* **JSON `lastUpdate`** stale (2026-05-16T02:00:00Z but written at S2-β-α
  ACT timestamp) — refreshed.

**Conflict-free guarantee.** Only `state.md` (4 small in-place edits) +
JSON (`currentState` head + `lastUpdate`) + a new `sessions/2026-05-15-s4-state-sync-post-drain.md`.
**Zero** Lean / lake / lakefile / problem.md / knowledge.md changes.
Compatible with the next S2-β ACT (Part IX) regardless of who picks it
up: the in-place state.md edits add no new section, so the S2-β ACT
just appends a `## Post-S2-β-α + S3c append landed (S2-β ACT, …)` per
the existing chronological-append convention.

**0-drift bearer recheck (spot-check, conflict-free with #19365 §2).**
Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and gallery
`FodorPressingDown.lean` are both unchanged since the S3c PREP audit at
~20:53Z. No re-verification needed beyond #19365's table; all 6 in-gallery
bearers (L1'@53, L2@59, L3@343, L4@259, L5@366, L6@408) and 11 Mathlib
bearers (C1–C11 at corrected lines per S3c) remain valid for the S2-β
ACT picker.

See `sessions/2026-05-15-s4-state-sync-post-drain.md` for the full §
catalogue (drift items, conflict-free guarantee, bearer-spot-check
delta).

## S2-β-β ACT landed (researcher-1, 2026-05-24, +86 LOC Lean, build-verified)

`§ Part IX` now ships cofinal-sequence head infrastructure for Solovay Step 2:

- `cofHead : Ordinal → Ordinal` (noncomputable def, ~6 LOC): picks the 0-th
  element of a chosen fundamental sequence (via `Classical.choose` on
  `Ordinal.exists_fundamental_sequence`) when `0 < α.cof.ord`; falls back to
  `0` otherwise. Junk fallback only fires at `α = 0` (per `cof_eq_zero ↔ a = 0`).
- `cofHead_lt` (~10 LOC): regressivity on positive limits. Proof bridges
  `IsSuccLimit α → 0 < α.cof.ord` via `aleph0_le_cof.mpr` + `Cardinal.ord_le_ord` +
  `Cardinal.ord_aleph0` + `Ordinal.omega0_pos` (same idiom as S2-α's `hω_lt` at
  line 390-392), then invokes `IsFundamentalSequence.lt` directly.
- `exists_cofHead_constant_stationary` (~12 LOC): Fodor's first application via
  `cofHead`. Three-hypothesis discharger for the explicit `fodor` signature
  (`hS_pos` via `IsSuccLimit.bot_lt`; `h_lt_κord` via `cofHead_lt` + transitivity;
  `h_reg` direct).
- `exists_cofHead_constant_stationary_of_stationary` (~9 LOC): convenience form
  absorbing `IsStationaryBelow.inter_isLimitOrdinals` (Part VIII) inside the
  signature. The recommended entry point for the next ACT picker.

FodorPressingDown.lean stats: **654 LOC** (was 568), **24 declarations**
(was 20: +3 theorems +1 noncomputable def), **0 sorries**, **0 axioms**. Build
verified via Docker `./proofs/scripts/docker-build.sh Proofs.FodorPressingDown`
— **3062 jobs successful in 23s**, 0 new warnings (the 2 existing
unused-variable warnings on lines 261 and 344 are pre-existing per #19052).

**Next: S2-β-γ ACT picker** can append a new `§ Part X` with `fodor_anti_constant`
(~60-80 LOC) using the same `Classical.choose`-on-`exists_fundamental_sequence`
picker pattern at index 1, plus a second Fodor application on the
stationary subset `S ∩ cofHead⁻¹{β}` produced by `exists_cofHead_constant_stationary`.
The hypothesis structure is `IsStationaryBelow ({α ∈ S | g₀ α = β₀ ∧ g₁ α = β₁}) ∧
IsStationaryBelow ({α ∈ S | g₀ α ≠ β₀ ∨ g₁ α ≠ β₁})` for some β₀, β₁; the
technical heart is showing the second set is stationary (canonical Solovay
index-of-first-disagreement argument).

**S2-β-δ ACT picker** (after S2-β-γ) can then ship `stationary_splits_binary`
(~50-80 LOC) by composing Part VIII + Part IX + Part X via Disjoint packaging.

See `sessions/2026-05-24-s2b-beta-act-cofhead-infrastructure.md` for the full
§ catalogue: bearer table (8 confirmed at SHA `2df2f015...`, no absences),
refined LOC budget (~115-170 remaining for `fodor_anti_constant` +
`stationary_splits_binary`), and the §4.2 outline mapping for Steps (b)+(d).

Iteration 9 → 10.
