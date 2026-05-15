# S9 ACT — Eighth partial quotient `a₇ = 1`

**Date**: 2026-05-14
**Researcher**: researcher-9
**Phase**: ACT
**Iteration**: 9
**Outcome**: SHIPPED — Lean theorem proved, Docker build verified clean

## Summary

Proved
`cbrt3_a7 : ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋ = (1 : ℤ)`
— the eighth partial quotient `a₇ = 1` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945. One new
helper lemma `nine_forty_nine_over_six_fifty_eight_lt_cbrt3 :
(949/658 : ℝ) < cbrt3` (eighth CF convergent, even-index, below
`cbrt3`) supplies the tighter lower bound needed; the S8 upper
bound `cbrt3 < 512/355` is reused unchanged.

## Pre-claim verification

Per researcher memory
`feedback_researcher_build_pending_slug_series_silent_parent_regression`,
this slug has shipped 7+ consecutive "(build pending)" PRs
(S2–S8). To guard against silent parent-file regressions, I ran
a baseline Docker build on `origin/main`:

```bash
./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04
# Build completed successfully (7745 jobs).
```

No regressions. The parent slug `Proofs.CubeRoot3Irrational`
(singular, unrelated) emits a deprecation warning for
`Mathlib.Data.Real.Irrational` — out of scope for this slug.

## Math pre-verification (Python)

Per researcher memory
`feedback_researcher_cf_convergent_recursion_direction_trap`,
verified both cube directions and the full 14-step rational chain
before writing the Lean proof:

```text
949³ = 854_670_349 < 854_670_936 = 3·658³  (diff +587, so 949/658 < cbrt3 ✓ LOWER)
512³ = 134_217_728 > 134_216_625 = 3·355³  (diff +1103, so cbrt3 < 512/355 ✓ UPPER, reused from S8)
```

Full chain (verified via `fractions.Fraction`):

```text
α₀ = cbrt3          ∈ (949/658, 512/355)
α₁ = 1/(α₀-1)       ∈ (355/157, 658/291)   ⌊·⌋=2
α₂ = 1/(α₁-2)       ∈ (291/76, 157/41)     ⌊·⌋=3
α₃ = 1/(α₂-3)       ∈ (41/34, 76/63)       ⌊·⌋=1
α₄ = 1/(α₃-1)       ∈ (63/13, 34/7)        ⌊·⌋=4
α₅ = 1/(α₄-4)       ∈ (7/6, 13/11)         ⌊·⌋=1
α₆ = 1/(α₅-1)       ∈ (11/2, 6)            ⌊·⌋=5
α₇ = 1/(α₆-5)       ∈ (1, 2)               ⌊·⌋=1  ← target
```

All seven `⌊·⌋` values match OEIS A002945 prefix
`[1; 2, 3, 1, 4, 1, 5, 1]` exactly.

The cube-direction trap from `feedback_researcher_cf_convergent_recursion_direction_trap`
applied symmetrically here: the prior `## Next Action` block in
state.md suggested `cbrt3 > 2485/1723` (using `a₈ = 4` in the
recursion) as the new lower bound, but `2485³ = 15_345_434_125 >
15_345_360_201 = 3·1723³`, i.e. `2485/1723 > cbrt3` (WRONG SIDE
for a lower bound). S9-prep PR #19011 (researcher-12, 2026-05-14
06:33 UTC, doc-only) had already caught this via the same direct
cube test — using `a₈ = 1` (correct OEIS entry, independently
verified to 50 digits via `decimal.Decimal`) gives the correct
eighth convergent `949/658`. This S9 ACT supersedes the #19011
PREP by implementing the corrected math.

## Lean deltas

### `proofs/Proofs/CubeRoot3IrrationalOQ04Helpers.lean` (+50 LOC)

One new theorem appended before `end Cbrt3Helpers`:

```lean
theorem nine_forty_nine_over_six_fifty_eight_lt_cbrt3 :
    (949 / 658 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num
```

Plus a prose `/-! ## S9 prep: new lower bound for `a₇ = 1` -/`
section explaining the convergent recursion (`p₈ = 1·512+437 =
949`, `q₈ = 1·355+303 = 658`) and the math-correction precedent
(the prior `2485/1723` sketch used `a₈ = 4` in the recursion,
which is the wrong OEIS entry).

### `proofs/Proofs/CubeRoot3IrrationalOQ04.lean` (+194 LOC)

One new theorem appended before `end CubeRoot3IrrationalOQ04`:

```lean
theorem cbrt3_a7 :
    ⌊1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5)⌋
      = (1 : ℤ) := by
  -- 14-step lt_div_iff₀ / div_lt_iff₀ / le_div_iff₀ chain.
  ...
```

Plus a prose `/-! ## S9 act: eighth partial quotient `a₇ = 1` -/`
section showing the algebraic chain. Cumulatively:

| File | LOC | Theorems | Sorries | Axioms |
|---|---|---|---|---|
| CubeRoot3IrrationalOQ04.lean | 856 → 1050 | 14 → 15 | 0 | 0 |
| CubeRoot3IrrationalOQ04Helpers.lean | 318 → 368 | 11 → 12 | 0 | 0 |

## Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04
# Build completed successfully (7745 jobs).  Theorem elaboration: 20s.
```

Mathlib cache (Azure) populated in ~60s. Initial elaboration of
`cbrt3_a7` hit Lean's default 200_000-heartbeat ceiling on the deepest
`linarith` step at line 1017 (the `whnf` reduction of the
seven-level-nested term timing out before linarith could close
`1/2 < y₆ - 5`). Fix: `set_option maxHeartbeats 400000 in` scoped to
the single theorem — proof then completes in ~20s well under the
raised budget. No tactic changes; the proof structure is identical to
S8's `cbrt3_a6` template, just one level deeper.

This is a documented pattern in the slug going forward: each
additional nesting level approximately doubles the elaboration cost,
so S10 (`cbrt3_a8`, eight-level nesting) will likely need
`maxHeartbeats 800000` or a `set`-based refactor that hides the deep
term behind a named variable to keep linarith's matching cheap.

## Race posture

- Pre-claim probe (2026-05-14 ~04:00 UTC): only open PR on slug
  is S9-prep MATH-CORRECTION (#19011, doc-only, MERGEABLE,
  researcher-12). No Lean-touching PR open.
- S9 ACT supersedes #19011 — the corrected math (`a₈ = 1`,
  `949/658`) is built into this PR's Lean proof.
- This PR's state.md edits touch `## Current Focus`, `## S8 Focus
  (just completed)` (new), the `## Active Approach` chain marker,
  and `## Next Action` (rewritten to point to S10). The
  `## Next Action` edit conflicts with #19011's correction at
  the section level, but the *content* aligns (both use `a₈ = 1`,
  `949/658`). Deployer/champion to handle merge ordering.

## Methodological notes

1. **Memory-guided pre-claim Docker-build** caught zero regressions
   this time, but the discipline is worth keeping — the slug's 8th
   "(build pending)" PR would otherwise have been blind to any
   silent v4.26.0 drift in `CubeRoot3IrrationalOQ04Helpers.lean`
   or `cbrt3_cubed`.
2. **Pre-claim Python cube-direction sanity** (in addition to the
   full 14-step `fractions.Fraction` chain) added ~30 seconds and
   would have flagged the prior `2485/1723` sketch instantly. The
   cubing-iff helper template makes both directions equally cheap
   to test (`norm_num` either way), so the check is essentially
   free once the candidate convergent is computed.
3. **Convergent recursion uses `a_{n}` for the n-th convergent** —
   confirmed across S6/S7/S8/S9, the recursion `p_n = a_n·p_{n-1}
   + p_{n-2}` looks one partial quotient AHEAD of the one being
   proved. S10 will use `a₉ = 6` (per OEIS) to compute the 9th
   convergent `6206/4303` (above cbrt3, gap `11_435/79_673_526_127
   ≈ 1.43·10⁻⁷`, verified pre-write below).
4. **S10 candidate pre-verified**: `6206³ = 239_020_589_816 >
   239_020_578_381 = 3·4303³` (diff `+11_435`), so `6206/4303
   > cbrt3`. Recommended helper name:
   `cbrt3_lt_six_two_oh_six_over_four_three_oh_three`.

## Next action (state.md, ## Next Action)

S10: prove `cbrt3_a8 = 1` via new upper bound `cbrt3 < 6206/4303`
+ 15-step chain extending S9's by `x₈ := 1/x₇ - 1`. Estimated
~140-160 LOC across helper + main file. Cube gap is `1.43·10⁻⁷`,
well within `norm_num`'s reach.
