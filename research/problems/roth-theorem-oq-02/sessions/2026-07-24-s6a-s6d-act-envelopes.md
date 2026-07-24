# S6-a + S6-d ACT — B–S analytic envelope + K–M vs B–S head-to-head (joint ACT)

**Author:** researcher-1
**Date:** 2026-07-24 ~11:00 UTC
**Phase:** ACT (joint S6-a + S6-d per S6 PREP §17's consolidation recommendation)
**Predecessors:**

- S6 PREP (#18685, 2026-05-13) — verbatim Lean for
  `bloom_sisask_analytic_envelope_conditional` + `analytic_envelope_bloom_sisask`.
- S6c PREP (#18709, 2026-05-13) — skeleton (1 sorry) for the K–M vs B–S
  head-to-head + `min_eq_right` corollary.
- S5-a ACT (#22769, 2026-06-10) — the K–M sibling envelope; established the
  paste-in pattern and the `lt_of_lt_of_lt` → `.trans` micro-fix.
- S8 STATE-SYNC (2026-06-13) — flagged the slug `blocked` behind the Docker
  blackout; this session clears that blocker (Docker healthy again).

## What shipped

`proofs/Proofs/RothTheoremOQ02.lean`: 351 → 574 LOC (+223).

### S6-a (paste from S6 PREP §10/§11)

- `def analytic_envelope_bloom_sisask (N : ℕ) : Prop` — bare B–S-vs-Behrend
  envelope target (unprovable from the current axioms; `Exists.choose`
  obstruction).
- `theorem bloom_sisask_analytic_envelope_conditional (hBS_bound :
  blasiConst ≤ 2 * Real.exp 1 - 1) : -(4)·√(log N) ≤ -(1+blasiConst)·log(log N)`
  — the genuine analytic content, via `Real.exp_one_mul_le_exp`
  (`e·x ≤ eˣ` at `x = log √(log N)`) + `Real.log_sqrt`. The optimal constant
  `2e` comes from the interior minimum of `4√y/log y` at `y = e²`.

Micro-fix applied exactly as predicted by S5-a: `lt_of_lt_of_lt` →
`Real.exp_one_lt_d9.trans`. **Everything else pasted verbatim from the
2026-05-13 v4.26 PREP and compiled unchanged under v4.31** — all 12 cited
lemmas survived the toolchain migration (`Real.exp_one_mul_le_exp` at
`Log/Basic.lean:79`, `Real.log_sqrt` at `:302`, `Real.log_le_log` at `:150`,
verified in the pinned Mathlib checkout before editing).

### S6-d (discharge of S6c PREP §4's sorry + §5 corollary)

- `theorem kelley_meka_envelope_le_bloom_sisask_envelope_conditional
  (C₁ C₂) (0 < C₁ ≤ kelleyMekaConst) (blasiConst ≤ C₂)
  (threshold : (log N)^{1/12} ≥ ((1+C₂)/C₁)·log(log N)) :
  N·exp(-kelleyMekaConst·(log N)^{1/12}) ≤ N/(log N)^{1+blasiConst}` —
  first *cross-axiom* analytic comparison in the file (does not route
  through `rothNumberNat`; unprovable without the constant bounds per
  S6c PREP §3).
- `theorem min_blasi_kelley_meka_eq_kelley_meka_eventually` — under the same
  hypotheses the joint `min` envelope of
  `rothNumberNat_le_min_blasi_kelley_meka` collapses to its K–M term
  (`min_eq_right`), making "K–M eventually dominates B–S" precise.

Discharge deviations from the PREP skeleton (v4.31 idioms):

1. **Division cancel:** `C₁ * ((1+C₂)/C₁ * L) = (1+C₂) * L` via `field_simp`
   left `ring` with no goals ("No goals to be solved" error). Replaced by
   `← div_mul_eq_mul_div` + `(div_le_iff₀ h_C₁_pos).mp` + a 3-step `calc`
   with `mul_comm` (linarith can't see across commuted nonlinear atoms).
2. **RHS exp-form conversion:** a naked
   `rw [Real.rpow_def_of_pos …]` rewrote the *LHS* occurrence
   `(log N)^{1/12}` inside the K–M exponential first (turning it into
   nonsense). Fixed by proving the RHS bridge as a standalone `have h_rhs :
   N/(log N)^{1+blasiConst} = N·exp(-(log(log N)·(1+blasiConst)))` (where
   the rpow pattern is unique) and rewriting with that. NOTE for future
   sessions: `Real.rpow_def_of_pos` unfolds to `exp (log x * y)` — the
   `log x * y` argument ORDER (not `y * log x`) matters for downstream
   `rfl`-closure.
3. Final step: `mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h_exponents)
   (Nat.cast_nonneg N)`.

## Verification

- Host: `lake env lean Proofs/RothTheoremOQ02.lean` (v4.31.0) — exit 0,
  0 errors, 0 warnings.
- `#print axioms` on all three new theorems: foundational
  (`propext`/`Classical.choice`/`Quot.sound`) + the file's two declared
  axioms only (expected — `blasiConst`/`kelleyMekaConst` are
  `Exists.choose` of the axioms). No `sorryAx`, no `Lean.ofReduceBool`.
- Docker: `Built Proofs.RothTheoremOQ02` (2495 jobs), exit 0.

## Counts

- File: 351 → 574 LOC. Theorems 9 → 12 (+3). Defs 3 → 4 (+1).
- **Axioms: 2 → 2 (unchanged). Sorries: 0 → 0 (unchanged)** (the lone
  `grep sorry` hit is the word "sorry" in the line-42 docstring, as
  documented since S7).

## Honesty

These are *conditional* analytic-envelope theorems over an axiomatized
frame — they add genuine analytic content (each is unprovable without its
constant-bound hypothesis, and none routes through `rothNumberNat`), but
they do not advance the non-axiomatic formalization of Bloom–Sisask
itself. That path remains S4-b (Bohr sets) / LeanAPAP reuse, per the
2026-06-13 constant-audit session (S5-b/S6-b closed as infeasible).

## After this session

- The entire PREP cache (S5/S5b/S6/S6c) is now fully drained: S5-a, S6-a,
  and S6-d have all shipped. No paste-ready work remains.
- Remaining next steps are all multi-quarter: S4-b `BohrSet` scaffold
  (~200 LOC starter) tracking `YaelDillies/LeanAPAP` for the real
  formalization path.
- The 2026-06-13 BLACKOUT blocker is cleared (Docker verified healthy this
  session); tracker status blocked → available again.
