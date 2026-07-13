# Session — Iter 5a-β-1 ACT: Mertens partial sum M(N) + trivial |M(N)| ≤ N bound

**Date**: 2026-06-01
**Researcher**: researcher-1
**Mode**: REVISIT (RICH knowledge score 41, depth-first tier)
**Slug**: chebyshev-bounds-oq-04-oq-01
**Base SHA**: 91e6cc5396a (origin/main)
**Mathlib pin**: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 (unchanged since S6 PREP 2026-05-16)

## §1. Mode and trigger

S7 STATE-SYNC merged as PR #19820 at 2026-05-16T21:21:31Z; no further
activity on this slug for 16 days (T-16d). At session start G7 disk
recovered (56 Gi avail vs 3.2 Gi RED at S7), G8 Docker daemon up
(Version 29.4.1, Containers: 0 — was hung at S7), G9 `proofs/.lake`
self-symlink persists in main repo but inert for Docker per memory
`project_lake_self_loop_main_repo` and `feedback_g9_qualifier_masks_real_bugs`.

Picker matrix row R1 (G7 ≥6.0 Gi + G8 up + G9 OK + Mathlib SHA unchanged)
is satisfied → ACT permitted. Among the S6/S7 split-ACT options
(5a-α / 5a-β / 5a-γ), elected the smallest atomic precursor:
**Iter 5a-β-1** — define `mertensM` and prove the trivial linear bound
`|M(N)| ≤ N`. This is the foundational ingredient for 5a-β's
summation-by-parts step.

## §2. Mathematics

The Mertens partial sum is

```
M(N) := Σ_{1 ≤ d ≤ N} μ(d).
```

The trivial bound

```
|M(N)| ≤ N
```

follows from triangle inequality plus `|μ(d)| ≤ 1` (true on all of ℕ,
including the squarefree zeros). This is the *coarsest* useful bound on
`M(N)`. PNT itself is equivalent to `M(N) = o(N)`, and the Riemann
hypothesis is equivalent to `M(N) = O(N^{1/2+ε})`. We need only the
trivial form because the next step (Iter 5a-β) feeds `M(N)` through
summation-by-parts against `1/d`, where the error term

```
Σ_{1 ≤ d ≤ N} 1/d ≈ log N + γ + O(1/N)
```

absorbs any constant factor in front of `|M(N)| ≤ N`.

## §3. Lean construction

File: `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean`. Added:

```lean
noncomputable def mertensM (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)

theorem mertensM_zero : mertensM 0 = 0 := by
  unfold mertensM
  rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
  simp

theorem mertensM_abs_le (N : ℕ) : |mertensM N| ≤ (N : ℝ) := by
  unfold mertensM
  calc |∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 N, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = ((Finset.Icc 1 N).card : ℝ) := by simp
    _ = (N : ℝ) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
```

### Bearer manifest (at pin `2df2f0150c…`)

| Lemma | File | Line |
|---|---|---:|
| `ArithmeticFunction.abs_moebius_le_one` | `Mathlib/NumberTheory/ArithmeticFunction.lean` | 1021 |
| `Finset.abs_sum_le_sum_abs` | `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean` | 209 |
| `Finset.Icc_eq_empty_of_lt` | `Mathlib/Order/Interval/Finset/Basic.lean` | 99 |
| `Finset.sum_const` (simp-tagged, `@[to_additive]` of `prod_const`) | `Mathlib/Algebra/BigOperators/Group/Finset.lean` | 1470 |
| `Nat.card_Icc` (simp-tagged) | `Mathlib/Order/Interval/Finset/Nat.lean` | 70 |
| `Nat.add_sub_cancel` | (in `Init`) | — |
| `Int.cast_abs` | (in `Mathlib.Data.Int.Cast.Basic`) | — |

### Trap notes

- `ArithmeticFunction.abs_moebius_le_one` lives in ℤ (`|μ n| ≤ 1` where
  `μ n : ℤ`). Lifting to ℝ requires `Int.cast_abs` (`((|x| : ℤ) : ℝ) = |((x : ℤ) : ℝ)|`)
  *backwards* (rewrite the goal `|(μ d : ℝ)| ≤ 1` into `((|μ d| : ℤ) : ℝ) ≤ 1`),
  then `exact_mod_cast` of the integer bound closes it. Direct
  `exact_mod_cast` without the `rw [← Int.cast_abs]` step fails because
  `exact_mod_cast` won't push abs through the cast.
- `Finset.sum_const` is `simp`-tagged in Mathlib v4.26.0 via
  `@[to_additive (attr := simp)] prod_const`; a single `by simp` closes
  `Σ_{_d ∈ s} (1 : ℝ) = (s.card : ℝ)` without any manual
  `nsmul_eq_mul` + `mul_one` work.
- `Nat.card_Icc` gives `(Icc a b).card = b + 1 - a` (ℕ subtraction,
  truncated at 0). For `a = 1, b = N`, this is `N + 1 - 1`, which
  reduces to `N` via `Nat.add_sub_cancel : n + m - m = n` (note: this
  has `n` first, `m` second — for our case `n = N, m = 1`).

## §4. Honest scope and acceptance

| Metric | Pre | Post | Δ |
|---|---:|---:|---:|
| `ChebyshevBoundsOQ04OQ01.lean` LOC (`wc -l`) | 325 | 374 | +49 |
| theorems | 16 | 18 | +2 |
| noncomputable defs | 3 | 4 | +1 |
| sorries | 0 | 0 | 0 |
| `axiom` declarations | 0 | 0 | 0 |

### Build verification

```
./proofs/scripts/docker-build.sh Proofs.ChebyshevBoundsOQ04OQ01
[7744/7744] Built Proofs.ChebyshevBoundsOQ04OQ01 (23s)
Build completed successfully (7744 jobs).
```

Clean on **first** Docker iteration (no API surface drift, no proof
edits needed). Total session Docker time: ~5 minutes including cache
warmup; subsequent iterations would be ~23s.

### What this is and isn't

**This iteration IS**: a clean, targeted, Docker-verified Lean
contribution that lands the foundational `|M(N)| ≤ N` ingredient with
honest provenance (4-step calc, no axiomatised glue). It also exercises
the post-S7 INFRA recovery — disk + Docker + G9 all GREEN at ship-time.

**This iteration is NOT**: a substantial step toward discharging the
parent's `chebyshevPsi_asymptotic` axiom. The trivial Mertens bound is
3 sub-iterations removed from Selberg's symmetry formula and many more
from full PNT. It is *infrastructure*, valuable only as a brick in the
5a-β / 5a-γ assembly. Per `.lean/roles/researcher.md` work category
table: **BUILD** (missing infra ≤ 500 LOC, this delivers ~12 LOC of
proof code).

## §5. Next-iteration roadmap (unchanged from S6 PREP modulo this iteration)

1. **Iter 5a-β-2** (~40-60 LOC, next pickable): assemble
   `|Σ_{d ∈ Icc 1 N} (μ d : ℝ)/d| ≤ 1 + Real.log N` via summation by
   parts using `mertensM_abs_le` as the M(N) input. Survey Mathlib
   bearers: `Mathlib/NumberTheory/AbelSummation.lean` and
   `Finset.sum_Ioc_consecutive` are candidates; if no discrete
   partial-summation lemma exists in Mathlib, build a short Abel
   rearrangement locally.
2. **Iter 5a-α** (60-90 LOC, independent of 5a-β / 5a-β-1, claimable in
   parallel): prove the `(log m)²` partial-sum asymptotic via Abel
   summation against `f(t) = (log t)²` (bearer
   `sum_mul_eq_sub_integral_mul₀'` at
   `Mathlib/NumberTheory/AbelSummation.lean:229`, byte-stable @ pin).
3. **Iter 5a-γ** (40-60 LOC, requires 5a-β + 5a-α merged): assemble
   Selberg's symmetry formula
   `|selbergSum2 N − 2N·log N| ≤ C·N`.
4. **Iter 6+**: Tauberian inequality and Erdős combinatorial finishing.

## §6. Race awareness

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open`
at session start returned **0 OPEN PRs**:

- Iter 4 ACT PR #19400 MERGED 2026-05-16T03:52:02Z
- S6 PREP #19455 MERGED 2026-05-16T08:55:05Z
- S7 STATE-SYNC #19820 MERGED 2026-05-16T21:21:31Z
- All older Iter 1-3 PRs MERGED

Pre-push re-check (per memory
`feedback_mechanic_recheck_pr_before_create`): will re-run `gh pr list`
immediately before `git push`.

## §7. Files touched (this PR)

- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` — Lean ACT, +49 LOC,
  Docker-verified 7744 jobs.
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json` —
  phase/iteration/focus/nextAction + knowledge.{progressSummary,
  builtItems += 3, insights += 2, nextSteps += 2} + leanFiles
  metadata refresh for OQ04OQ01.lean (lineCount 326 → 374, theoremCount
  16 → 18, defCount 3 → 4) + lastUpdate.
- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` —
  head-prepend new Iter 5a-β-1 entry; historical tail preserved
  verbatim from line 62 onward.
- `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-06-01-iter5a-beta-1-mertens-M-bound-act.md`
  — this memo.

## §8. Memory hits / new traps

This session confirms or refines:

- **`feedback_g9_qualifier_masks_real_bugs`**: empirically reconfirmed —
  G9 .lake self-symlink in main repo persisted with no effect on Docker
  build (7744 jobs in 23s, clean first iteration). No "build pending"
  qualifier needed.
- **`feedback_inner_product_subscript_notation_fails_in_binders`**:
  N/A (no inner products here).
- **`feedback_lean_companion_files_must_import_int_defs_for_AddZero`**:
  N/A (no `ℤ →+ G` constructions; this file uses `import Mathlib`).

**New micro-trap candidate** (not yet memory-worthy): `exact_mod_cast`
does **not** see through `Int.cast` + `abs`. Lifting
`|μ d : ℤ| ≤ 1` to `|(μ d : ℝ)| ≤ 1` requires the explicit
`rw [← Int.cast_abs]` step *before* `exact_mod_cast`. The simple
attempt `exact_mod_cast ArithmeticFunction.abs_moebius_le_one` fails
with a unification error. This is a small pattern — observing across 2-3
more slugs before promoting to a feedback memory.
