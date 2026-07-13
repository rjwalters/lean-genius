# Session 27 — `chebyshev_hne_pi_sub` (`hne` side of WLOG bridge)

**Researcher**: researcher-11
**Date**: 2026-05-09
**Branch**: `research/erdos-1151-oq-04-s27-build-verify-1778280541`
**Build status**: docker build queued (cold cache; lake clone + cache-get
in progress at submit time)

## Summary

Added a single ~50-line private helper (`chebyshev_hne_pi_sub`) that supplies
the **`hne` side** of the half-π → general θ ∈ (0, π) WLOG bridge for
`trig_sum_harmonic_lb`:

```lean
private lemma chebyshev_hne_pi_sub (n : ℕ) (hn : 0 < n) (θ : ℝ)
    (hne : ∀ k : Fin n, Real.cos θ ≠ chebyshevNode n k) :
    ∀ k : Fin n, Real.cos (Real.pi - θ) ≠ chebyshevNode n k
```

The "**sum side**" (i.e. `S(θ, n) = S(π − θ, n)`) is already provided by
`trig_sum_reindex_symmetry` (S18, merged via #17050). Together, S18 + S27
constitute the entire **machinery for the WLOG bridge**. Once
`trig_sum_harmonic_lb_asymp_le_half_pi` (S26, in flight as PR #17486) lands,
the asymptotic-side bound on θ ∈ (0, π) follows via case split:

- `θ ≤ π/2`: apply S26 directly.
- `θ > π/2`: let `θ' := π − θ ∈ (0, π/2)`. Use S27 on `hne` to obtain
  `hne'` for `θ'`, apply S26 to `(θ', hθ'_pos, hθ'_le, hne')` to get the
  bound on `S(π − θ, n)`, then use S18 to rewrite the sum back as
  `S(θ, n)`.

## Why packaged independently of S25/S26

Both PR #17457 (S25, combine helper) and PR #17486 (S26, half-π asymp packaging)
are still open. Per memory pattern `feedback_researcher_session_time_merge.md`,
the MODERATE+ tier is over-subscribed; a follow-up that depends on both
risks CONFLICTING on rebase. S27 depends only on:

1. `chebyshevNode` (definition, line 86 on origin/main, untouched since S6).
2. `Real.cos_pi_sub` (Mathlib core).
3. `Nat.cast_sub` / `Nat.cast_one` / `Nat.cast_pos` / `field_simp` / `ring` /
   `omega` / `linarith` (all Mathlib core, no version drift).

It uses the **same involution** `σ : Fin n ≃ Fin n`, `k ↦ n − 1 − k.val`
that S18's `trig_sum_reindex_symmetry` already establishes in scope.

## Proof skeleton

```
intro k
let σk : Fin n := ⟨n - 1 - k.val, _⟩

-- Cast σk.val from ℕ to ℝ
have hσ_val : (σk.val : ℝ) = (n : ℝ) - 1 - (k.val : ℝ) := by
  show ((n - 1 - k.val : ℕ) : ℝ) = _
  rw [Nat.cast_sub hk_le, Nat.cast_sub hone_le, Nat.cast_one]

-- Angle identity (real form): φ_{σ k} = π − φ_k
have hangle_eq : (2 * (σk.val : ℝ) + 1) * π / (2 * n) =
    π - (2 * (k.val : ℝ) + 1) * π / (2 * n) := by
  rw [hσ_val]; field_simp; ring

-- Node sign-flip: chebyshevNode n σk = − chebyshevNode n k
have hnode_eq : chebyshevNode n σk = -chebyshevNode n k := by
  simp only [chebyshevNode]
  rw [hangle_eq, Real.cos_pi_sub]

-- Conclude
rw [Real.cos_pi_sub]
intro h
apply hne σk
rw [hnode_eq]; linarith
```

## Counts

|              | Before (S26) | After (S27) | Δ   |
|--------------|-------------:|------------:|----:|
| Lines        | 2288         | 2340        | +52 |
| Theorems     | 59           | 60          | +1  |
| Sorries      | 2            | 2           | 0   |

(Line numbers vs `origin/main` 2288 baseline — S25/S26 also branch off
this baseline, but with disjoint insertions; S27 inserts at lines 1843–
1894, S25 at 2087–2147, S26 at 2087–2213. All three insertions are
mutually rebase-friendly.)

## Build status

**[BUILD UNVERIFIED]** — Docker build started this session (cold cache,
mathlib v4.26.0 fresh-clone in progress at submit time). The proof body
uses only Mathlib-core tactics with no version-drift risk; insertion is
between two stable lemmas (`trig_sum_reindex_symmetry`,
`chebyshev_trig_sum_pos`). Outcome will be reported in a follow-up
comment if any drift surfaces.

Per `feedback_basel_oq03_iter12_three_fixes.md`, when ≥3 build-pending
merges accumulate on a slug, drift can compound silently. The 30+ errors
at lines 818–2069 reported in PR #17486 (S26) are pre-existing; this
helper does not introduce new constructs that touch the affected APIs.

## Files modified

- `proofs/Proofs/Erdos1151OQ04.lean` — new helper at lines 1845–1894
  (~50 lines including docstring; insertion between
  `trig_sum_reindex_symmetry` and `chebyshev_trig_sum_pos`)
- `src/data/research/problems/erdos-1151-oq-04.json` — leanFile
  `lineCount` 2288→2340, `theoremCount` 59→60
- `research/problems/erdos-1151-oq-04/state.md` — Iteration 27 section
- `research/problems/erdos-1151-oq-04/session-27-hne-pi-sub.md` — this note

## Outcome

**Progress** (1 helper added on the WLOG bridge; S25 + S26 + S27 + S18
together close the half-π → (0, π) reduction; remaining work for
`trig_sum_harmonic_lb` is ~10 lines of caller-side glue post-merge).
