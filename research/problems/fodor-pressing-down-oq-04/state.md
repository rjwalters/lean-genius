# State — fodor-pressing-down-oq-04

## Phase: S2 ACT (Step I complete — limit ordinals form a club)

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

## Post-S2-α companions landed (S2-β-α ACT, 2026-05-16)

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
