# S6 ACT — exact representability criterion for consecutive triples

**Date**: 2026-06-11
**Researcher**: researcher-2
**Mode**: ACT (Lean)
**Branch**: `research/frobenius-oq-03-s6-consecutive-characterization`
**Build**: `./proofs/scripts/docker-build.sh Proofs.FrobeniusNumberOQ03`
→ **3059/3059 jobs clean**.

## TL;DR

Shipped `representable3_consecutive_iff`, the exact two-sided
representability criterion for three-consecutive generators:

```lean
representable3_consecutive_iff (n m : ℕ) :
    Representable3 n (n + 1) (n + 2) m ↔ ∃ s : ℕ, n * s ≤ m ∧ m ≤ (n + 2) * s
```

This is the structural key to Roberts' tight `d = 1` closed form. The prior
16 iterations only had one-directional Sylvester bounds
(`large_representable3_*`); the **iff** is new.

## The idea

`n·x + (n+1)·y + (n+2)·z = n·(x+y+z) + (y + 2z)`. With `s := x+y+z`, the
remainder `y + 2z` ranges over exactly `[0, 2s]` as `y, z` vary subject to
`y + z ≤ s` (for `t ≤ s` take `y=t, z=0`; for `s < t ≤ 2s` take
`y = 2s-t, z = t-s`). So `m` is representable iff `m ∈ [n·s, (n+2)·s]` for
some `s`. The Frobenius question becomes interval-covering on `ℕ`.

## Proof notes

- **Forward**: from `(x,y,z)`, witness `s = x+y+z`; the two bounds follow
  from `ring` identities (`n·s + (y+2z) = m`, `(n+2)·s = m + (2x+y)`) fed
  to `omega`.
- **Backward**: case on `t := m - n·s` vs `s`. Explicit witnesses
  `(s-t, t, 0)` and `(0, 2s-t, t-s)`, but realised via
  `obtain ⟨u, hu⟩ : ∃ u, s = u + (m - n*s)` etc. to keep the Nat
  subtractions out of the multiplications. Each closed by a `ring` helper
  + `omega`.
- **The one fix during ACT**: the `key` step was written
  `have key : ... := by rw [hu]; ring`. Because `hu : s = u + (m - n*s)`,
  the bare `rw [hu]` rewrote the `s` *inside* `m - n*s` too, producing a
  self-referential mess that `ring` could not close (Nat subtraction).
  Fix: `conv_lhs => rw [hu]` to rewrite only the standalone `n * s`, then
  `rw [Nat.mul_add]`. **Lesson: when the rewrite target also occurs inside
  a subtraction/other atom you want to preserve, scope the `rw` with
  `conv`.**

## Net delta

+50 LOC (390 → 440), +1 theorem (26 → 27), 0 sorries / 0 axioms, no new
imports. Section `S6` appended before `end FrobeniusOQ03`.

## Tracker drift corrected

The research JSON/state had drifted: `leanFiles` recorded 281 LOC / 17 thm,
but `origin/main` was already at 390 / 26 — the merged S6 pair-symmetric
Sylvester results (`set_non_representable3_finite_of_coprime_ac/bc`,
`frobeniusNumber3_le_min_sylvester_bound`, lines ~281–389) had never been
synced into this tracker. Corrected `leanFiles[0]` to the post-S6 reality
(440 / 27) and refreshed `currentState` + `state.md` head.

## Next (S6b) — the closed form, now reduced

`g(n, n+1, n+2) = ⌊(n-2)/2⌋·n + (n-1)` for `n ≥ 3`. Hand-checked:
F(3)=2, F(4)=7, F(5)=9, F(6)=17 — all match.

- **Upper bound** (every `m > F` representable): set `s := m / n`. Then
  `n·s ≤ m < n·(s+1)`, so `m ≤ n·s + (n-1)`. From `m > F = ⌊(n-2)/2⌋·n +
  (n-1)` get `s ≥ ⌊(n-2)/2⌋ + 1`, hence `2s ≥ n-1` (omega on the literal-2
  division), so `m ≤ n·s + (n-1) ≤ n·s + 2s = (n+2)·s`; apply
  `representable3_consecutive_iff`. (No parity case-split — the planned
  Route A's `n mod 2` split is unnecessary.)
- **Lower bound** (`F` non-representable): refute `∃ s, n·s ≤ F ≤ (n+2)·s`.
  For `s ≤ ⌊(n-2)/2⌋`: `(n+2)·s < F`. For `s ≥ ⌊(n-2)/2⌋+1`: `n·s > F`.
- **Combine**: `frobeniusNumber3_le_of_subset_Iio` (upper) +
  `set_non_representable3_finite_of_coprime_ab` BddAbove + sSup-attained
  (lower) ⟹ `frobeniusNumber3 n (n+1) (n+2) = F`.

The only uncertainty is exact Mathlib lemma names for `n * (m/n) ≤ m` and
`m < n*(m/n + 1)` (candidates: `Nat.mul_div_le`, `Nat.div_mul_le_self`,
`Nat.lt_div_add_one_mul_self`, or `Nat.div_add_mod` + `Nat.mod_lt`).
Estimated ~50–70 LOC.
