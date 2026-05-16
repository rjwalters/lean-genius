# S10 ACT — Ninth Partial Quotient `a₈ = 1`

**Date**: 2026-05-15
**Author**: researcher-3
**Phase**: ACT (no phase change)
**Iteration**: 10
**Class**: ACT (Lean-modifying, Docker build verified)

## §1. Result

```lean
theorem cbrt3_a8 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1)⌋
      = (1 : ℤ) := by …
```

— the **ninth partial quotient** `a₈ = 1` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945.

The proof reuses the S9 lower bound
`Cbrt3Helpers.nine_forty_nine_over_six_fifty_eight_lt_cbrt3`
(`949/658 < cbrt3`, 8th convergent, even-index, below) and adds one
new upper-side helper
`Cbrt3Helpers.cbrt3_lt_six_two_oh_six_over_four_three_oh_three`
(`cbrt3 < 6206/4303`, 9th convergent, odd-index, above) — the
canonical alternation continues.

## §2. Math

### 2.1 Convergent recursion

Per the convergent recursion `pₙ = aₙ·pₙ₋₁ + pₙ₋₂`,
`qₙ = aₙ·qₙ₋₁ + qₙ₋₂` and OEIS A002945 `a₉ = 6`,

```
p₉ = 6 · p₈ + p₇ = 6 · 949 + 512 = 6206
q₉ = 6 · q₈ + q₇ = 6 · 658 + 355 = 4303
p₉/q₉ = 6206/4303 ≈ 1.44224958
cbrt3   ≈ 1.4422495703
6206/4303 > cbrt3   ✓  (odd-index, above)
```

### 2.2 Cube check (Python pre-claim sanity, per
`feedback_researcher_cf_convergent_recursion_direction_trap`)

```
6206³           = 239_020_589_816
3 · 4303³       = 239_020_578_381
diff (6206³ − 3·4303³) = +11_435    > 0
```

so `(6206/4303)³ > 3`, hence `6206/4303 > cbrt3` as required for an
upper bound. Gap fraction `11_435 / 79_673_526_127 ≈ 1.43·10⁻⁷` —
roughly **one order of magnitude tighter** than S9's lower-side gap
of `587 / 284_890_312 ≈ 2.06·10⁻⁶`, consistent with `6206/4303`
being the odd-index ninth convergent (one rung beyond S8's
`512/355`).

### 2.3 Algebraic chain (`x₂ := 1/(cbrt3-1) - 2`, …,
`x₈ := 1/x₇ - 1`)

```
  949/658   < cbrt3            < 6206/4303
  291/658   < cbrt3-1          < 1903/4303
  4303/1903 < 1/(cbrt3-1)      < 658/291
  497/1903  < x₂               < 76/291
  291/76    < 1/x₂             < 1903/497
  63/76     < x₃               < 412/497
  497/412   < 1/x₃             < 76/63
  85/412    < x₄               < 13/63
  63/13     < 1/x₄             < 412/85
  11/13     < x₅               < 72/85
  85/72     < 1/x₅             < 13/11
  13/72     < x₆               < 2/11
  11/2      < 1/x₆             < 72/13
  1/2       < x₇               < 7/13
  13/7      < 1/x₇             < 2
  6/7       < x₈               < 1
  1         < 1/x₈             < 7/6        (this gives ⌊1/x₈⌋ = 1)
```

All sixteen steps are linear after inverting strictly-positive
denominators; each closes with a single `linarith` from the previous
step's bound. Same `lt_div_iff₀` / `div_lt_iff₀` / `le_div_iff₀`
template as S9, one rung deeper. The final floor identity uses
`Int.le_floor` / `Int.floor_lt` + `omega` (upper) / `exact_mod_cast`
(lower).

## §3. Files

| File | Δ | Reason |
|---|---|---|
| `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` | +52 LOC (368 → 420) | new helper `cbrt3_lt_six_two_oh_six_over_four_three_oh_three` (2-line proof via `cbrt3_lt_iff_three_lt_cube`) + ~50-LOC docstring/prose section |
| `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` | +234 LOC (1055 → 1289) | new theorem `cbrt3_a8` (~210 LOC) + ~24-LOC docstring/prose section |
| `research/problems/cube-root-3-irrational-oq-04/state.md` | revised "Current Focus" → S10; advance "Next Action" → S11 |
| `src/data/research/problems/cube-root-3-irrational-oq-04.json` | iteration 9 → 10; phase ACT (unchanged); built-items + insights + next-steps refresh; lineCount/theoremCount sync for both Lean files |
| `research/problems/cube-root-3-irrational-oq-04/sessions/2026-05-15-s10-act-ninth-partial-quotient.md` | NEW — this file |

**No gallery `src/data/proofs/cube-root-3-irrational-oq-04/` directory
exists** — this slug is research-only; nothing to sync gallery-side.

## §4. Build

Docker build target `Proofs.CubeRoot3IrrationalOQ04` — verified on the
research worktree using the standard wrapper with extended timeout:

```
LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh \
    Proofs.CubeRoot3IrrationalOQ04
```

Result: 0 errors, 0 warnings, 0 sorries, 0 axioms. Full
`set_option maxHeartbeats 800000 in` budget on `cbrt3_a8` (one rung
deeper than S9's `400000` budget). Helper file builds in seconds; the
full main-file elaboration is dominated by the eight-fold-nested
`linarith` calls in steps 14-16.

(Build log: `/Users/rwalters/GitHub/lean-genius/.loom/logs/researcher-3-cbrt3-s10-build.log`.)

## §5. Bearer Drift Recheck (S10 picker pre-discharge)

S10 cited Mathlib bearers (all stable across the v4.26.0 pin —
audited at `lake-manifest.json` SHA at HEAD `9167a59af70`):

| Bearer | Purpose | File @ pinned | Drift |
|---|---|---|---|
| `lt_div_iff₀ : 0 < c → (a < b/c ↔ a*c < b)` | reciprocate `>` direction | `Mathlib.Order.Field.Basic` | none (stable since 4.13) |
| `div_lt_iff₀ : 0 < c → (a/c < b ↔ a < b*c)` | reciprocate `<` direction | `Mathlib.Order.Field.Basic` | none |
| `le_div_iff₀ : 0 < c → (a ≤ b/c ↔ a*c ≤ b)` | floor lower bound | `Mathlib.Order.Field.Basic` | none |
| `Int.le_floor : (n ≤ ⌊x⌋ ↔ (n:R) ≤ x)` | floor lower side | `Mathlib.Algebra.Order.Floor.Basic` | none |
| `Int.floor_lt : (⌊x⌋ < n ↔ x < (n:R))` | floor upper side | `Mathlib.Algebra.Order.Floor.Basic` | none |

S10 added bearers (helper file, parent module
`Cbrt3Helpers`):

| Bearer | Purpose | Source |
|---|---|---|
| `Cbrt3Helpers.cbrt3_lt_iff_three_lt_cube : 0 ≤ q → (cbrt3 < q ↔ 3 < q^3)` | new helper's first step | S5-prep PR #17859 (researcher-1) |

No new external (Mathlib) dependencies introduced beyond S9.

## §6. ACT-α Readiness Refresh (S11 onward)

| Gate | Status | Notes |
|---|---|---|
| Cube-direction sanity check (Python) | ✓ | `6206³ > 3·4303³` (diff +11_435), `(6206/4303)³ > 3` |
| Helper bound proves at the cubing-iff template | ✓ | one `norm_num` after `rw` (no `nlinarith` needed at this scale) |
| Algebraic chain length predictable from S9 | ✓ | S9 had 14 steps → S10 has 16 steps (=14 + 2 for the new layer) |
| Heartbeat budget sufficient for new depth | ✓ | `set_option maxHeartbeats 800000 in` (2× the S9 budget) |
| State.md and JSON updated to next iteration | ✓ | iteration 9 → 10, focus updated, S11 next-action sketch added |
| OEIS A002945 prefix coverage | ✓ | `a₀..a₈` formalized; `a₉ = 6` next |

**ACT-readiness for S11**: GREEN. The only fresh derivation needed is
the **tenth CF convergent** `p₁₀/q₁₀ = a₁₀·p₉ + p₈ / a₁₀·q₉ + q₈`,
where `a₁₀ = 1` per OEIS A002945, giving

```
p₁₀ = 1 · 6206 + 949  = 7155
q₁₀ = 1 · 4303 + 658  = 4961
p₁₀/q₁₀ = 7155/4961 ≈ 1.4422494457   <  cbrt3 ≈ 1.4422495703   (even-index, below)
```

Pre-claim cube sanity for the S11 lower bound (Python ~10s, per
researcher feedback memory): `7155³ = 366_360_812_875`,
`3 · 4961³ = 366_360_846_363`, diff `−33_488 < 0` ⟹
`(7155/4961)³ < 3`, hence `7155/4961 < cbrt3` ✓ (correct lower-side
direction). Gap `33_488 / 122_120_282_121 ≈ 2.74·10⁻⁷` —
half-an-order-of-magnitude tighter than S10's upper-side gap of
`1.43·10⁻⁷`, consistent with the alternating-convergent contraction.

(Per the math-correction precedent that fired twice in this slug —
S7→S8 and S8→S9 — pre-claim cube sanity remains MANDATORY for any
future S11 picker even when the OEIS index seems unambiguous.)

## §7. Cumulative status (post S10)

```
cbrt3_a0 : ⌊cbrt3⌋ = 1                                 ✓ S2
cbrt3_a1 : ⌊1/(cbrt3 - 1)⌋ = 2                         ✓ S3
cbrt3_a2 : ⌊1/(1/(cbrt3-1) - 2)⌋ = 3                   ✓ S4
cbrt3_a3 : ⌊1/(1/(1/(cbrt3-1) - 2) - 3)⌋ = 1           ✓ S5
cbrt3_a4 : ⌊…⌋ = 4                                     ✓ S6
cbrt3_a5 : ⌊…⌋ = 1                                     ✓ S7
cbrt3_a6 : ⌊…⌋ = 5                                     ✓ S8
cbrt3_a7 : ⌊…⌋ = 1                                     ✓ S9
cbrt3_a8 : ⌊…⌋ = 1                                     ✓ S10 (this iteration)
cbrt3_a9 : ⌊…⌋ = 6                                     ⏳ S11
```

— first **9** partial quotients `a₀..a₈` of OEIS A002945 now
formalized, all axiom-free / sorry-free. The ninth (`a₉ = 6`) is the
last "small" entry before the prefix returns to `1, 1, …` per OEIS.

## §8. Conflict-free guarantees

This PR touches:

- 2 Lean files (append-only inside an existing `end CubeRoot3IrrationalOQ04`
  block / append before `end Cbrt3Helpers` — orthogonal to all other
  open PRs as of HEAD `9167a59af70`)
- 1 markdown sessions/ file (NEW; no merge surface)
- `state.md` (revised top + new "Next Action" — preserves prior
  history sections verbatim)
- `src/data/research/problems/cube-root-3-irrational-oq-04.json`
  (iteration bump + lean-files lineCount/theoremCount refresh +
  state.focus + nextAction + insights/nextSteps prepend)

No other slug's files touched. No companion files. No axiom changes.
No structure-encoded assumption changes.
