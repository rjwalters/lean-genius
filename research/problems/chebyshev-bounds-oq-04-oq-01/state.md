# State — chebyshev-bounds-oq-04-oq-01

## Current phase

**Phase**: ACT (Iter 4 Möbius–log literal form Λ₂(n) = Σ_{d|n} μ(d)·log²(n/d) verified)
**Iteration**: 5 (Iter 5 in planning — Selberg's symmetry formula S₂(N) = 2N·log N + O(N))
**Since**: 2026-05-16T02:55:00Z

## Lean snapshot (post-Iter 4)

| File | LOC | Thm | Defs | Sorries | Axioms | Status |
|---|---:|---:|---:|---:|---:|---|
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | 325 | 16 | 3 noncomputable | 0 | 0 | build-verified 7744 jobs at Iter 4 |
| `proofs/Proofs/ChebyshevBoundsOQ04.lean` | (parent) | — | — | 0 | 1 | parent's `chebyshevPsi_asymptotic` axiom remains the open target |

OQ-04-OQ-01 is the **elementary Selberg–Erdős 1949 PNT** approach to
discharging that parent axiom (no complex analysis).

## Iteration log

### Iter 4 — 2026-05-16 (this session, PR pending)

**Result**: Closes the literal Möbius–log form deferred from Iter 3:

```
Λ₂(n) = Σ_{d ∣ n} μ(d) · (Real.log (n/d : ℕ))²    (n > 0).
```

One new theorem (file grows 312 → 325 LOC, 15 → 16 theorems, 0 sorries,
0 axioms maintained):

- `selbergLambda2_eq_moebius_log_sq`: applies
  `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` (Mathlib v4.26.0
  `Mathlib/NumberTheory/ArithmeticFunction/Moebius.lean:240`) to Iter 3's
  `sum_divisors_selbergLambda2_eq_log_sq`, then re-indexes
  `divisorsAntidiagonal → divisors` via `Nat.sum_divisorsAntidiagonal`
  (`Mathlib/NumberTheory/Divisors.lean:543`). Proof body ~8 LOC.

**Build trap (worth recording for future Möbius-inversion lifts)**: the
lift `∀ m > 0, ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2`
must annotate `m : ℕ` explicitly. Without it, Lean infers `m : ℝ` from
`Real.log m` (which accepts `ℝ` directly), then fails on `m.divisors`
("Real.divisors" not found) and rejects
`sum_divisors_selbergLambda2_eq_log_sq hm` (expects `0 < ?m : ℕ`). Fix
is a single-token addition (`∀ m : ℕ, 0 < m → ...`). General pattern:
any iff-form Möbius-inversion lift in this file should type-annotate
the bound `ℕ` variable when the RHS coerces through `Real.log`.

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.ChebyshevBoundsOQ04OQ01` reports clean
`[7744/7744] Built Proofs.ChebyshevBoundsOQ04OQ01 (51s)` after 2 Docker
iterations on base SHA `8a3cda556b6` against Mathlib v4.26.0 pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Iter 3 — 2026-05-14 (PR #19092 merged 2026-05-15T22:59:33Z)

**Result**: Closes the central algebraic step of the elementary PNT
strategy — Selberg's **dual identity**

```
Σ_{d ∣ n} Λ₂(d) = (Real.log n)²    (n > 0).
```

Three new theorems (file grows 230 → 312 LOC, 12 → 15 theorems, 0
sorries, 0 axioms maintained):

- `vonMangoldtConv_eq_mul`: bridge connecting this file's explicit
  divisor-sum definition `vonMangoldtConv n = Σ_{d ∈ n.divisors} Λ(d) · Λ(n/d)`
  to Mathlib's `ArithmeticFunction.mul` form
  `((vonMangoldt : ArithmeticFunction ℝ) * vonMangoldt) n =
   Σ_{x ∈ n.divisorsAntidiagonal} Λ(x.1) · Λ(x.2)`. Proof: 1 LOC after
  `Nat.map_div_right_divisors` + `Finset.sum_map` + `rfl`.
- `sum_divisors_vonMangoldtConv`: the convolution-in-sum identity
  `Σ_{d ∣ n} (Λ ∗ Λ)(d) = Σ_{d ∣ n} Λ(d) · log(n/d)` via
  `(Λ ∗ Λ) ∗ ζ = Λ ∗ (Λ ∗ ζ) = Λ ∗ log`
  (`ArithmeticFunction.vonMangoldt_mul_zeta` + `coe_mul_zeta_apply` +
  `mul_assoc`).
- `sum_divisors_selbergLambda2_eq_log_sq` (main deliverable): combines
  the above with `ArithmeticFunction.vonMangoldt_sum` (Σ Λ(d) = log n)
  and `Real.log_mul` applied to each divisor pair (d, n/d) — both
  positive because `d ∣ n` and `n > 0`.

The "original" Möbius-inversion form `Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d)`
is one step away (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`)
and is deferred to Iter 4 (~15 LOC).

**Incidental parent-file fixes** (this PR bundles them to keep the
slug build-clean):

- `proofs/Proofs/ChebyshevBoundsOQ04.lean:298` — Mathlib v4.26.0 `ring`
  regression: `4^m = 2^(2*m)` no longer closes by `ring` (tactic treats
  `4` and `2` as distinct atoms; `ring_nf` suggestion does not help).
  Fix: `by ring` → `by rw [pow_mul]; rfl` (1 LOC).
- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean:191` — Mathlib v4.26.0
  rename `Nat.divisors_prime` → `Nat.Prime.divisors` (dot-method form).
  Fix: 1 LOC inline at `vonMangoldtConv_prime` (an Iter 2 lemma).

Both regressions surfaced because the slug had last been Docker-built
at Iter 2 merge (2026-05-12T00:48Z), and Mathlib's tracked revision
evolved in the intervening 2 days. Pattern: see MEMORY
`feedback_researcher_build_pending_slug_series_silent_parent_regression.md`.

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.ChebyshevBoundsOQ04OQ01` reports clean
`[7744/7744] Built Proofs.ChebyshevBoundsOQ04OQ01 (10s)` after 2 Docker
iterations (iter 1 surfaced the 3 errors above, iter 2 clean).

### Iter 2 — 2026-05-12 (PR #17690 merged)

**Result**: Closes the Iter 1 documented next-iteration deliverables
#1 and #2:

- `vonMangoldtConv_prime`: `(Λ ∗ Λ)(p) = 0` for prime `p`. Proof via
  `Nat.Prime.divisors` (formerly `Nat.divisors_prime`, see Iter 3 notes)
  + `Finset.sum_pair` + `vonMangoldt_apply_one`.
- `selbergLambda2_prime`: `Λ₂(p) = (log p)²` for prime `p`. Proof via
  `vonMangoldt_apply_prime`.

LOC delta: 206 → 230 (+24). Theorem count: 10 → 12. Sorries unchanged
(0). Axioms unchanged (0). PR #17690 also refreshed the gallery
`meta.json` description + `originalContributions` to mention Iter 2.

**Race note (post-merge cleanup deferred)**: PR #17689 ("Iter 2 —
prime values", different branch, OPEN+CONFLICTING since
2026-05-12T22:13Z) was a parallel attempt superseded by #17690 but
never closed. Decision to comment-close it deferred to maintainer.

### Iter 1 — 2026-05-09 (researcher-12, PR #17658 merged)

**Result**: OBSERVE-phase scaffold of the Selberg–Erdős strategy.

**Built** (`proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean`, 209 LOC):

- 3 noncomputable defs:
  - `vonMangoldtConv : ℕ → ℝ` — `Λ ∗ Λ` as a literal divisor sum
    (chosen over Mathlib's `ArithmeticFunction.mul` for cleaner
    algebraic rewrites downstream — VALIDATED by Iter 3's bridge).
  - `selbergLambda2 : ℕ → ℝ` — `Λ(n) · log n + (Λ ∗ Λ)(n)`.
  - `selbergSum2 : ℕ → ℝ` — `Σ_{n ≤ N} Λ₂(n)`.
- 10 routine theorems: zero-value, one-value, non-negativity,
  successor-recursion, monotonicity (one per def).
- 0 sorries, 0 axioms.

Gallery entry `chebyshev-bounds-oq-04-oq-01` created (status
`formalized`, badge `wip`). File roadmap + Future Work sections
document the downstream Selberg symmetry formula + Erdős finishing
argument; the parent's `chebyshevPsi_asymptotic` axiom remains the
open target.

## Blockers

None. Iter 5 (Selberg's symmetry formula
`Σ_{n ≤ N} Λ₂(n) = 2N · log N + O(N)`) is the next analytic step.
Requires either: (a) a Mathlib-internal summation-by-parts framework
specialised to `Λ`-weighted sums (Mathlib v4.26.0 has only
`Finset.sum_Ioc_consecutive` and `summation_by_parts` lemmas in
`Mathlib/Analysis/MeanInequalitiesPow.lean` — neither directly
applicable), or (b) a hand-rolled `Abel`-style derivation using
Iter 4's identity as the launching point. Recommended path is (b) for
Iter 5a (the leading-term `2N log N`) and a separate Iter 5b for the
`O(N)` error via the Möbius hyperbola bound.

## Next Action

**Iter 5a — Selberg's symmetry formula, leading term**: prove

```
Σ_{n ≤ N} Λ₂(n) = 2 N · log N + O(N).
```

Starting from Iter 4's `selbergLambda2_eq_moebius_log_sq`, sum over
`n ≤ N` and swap the order to get

```
Σ_{n ≤ N} Λ₂(n) = Σ_{d ≤ N} μ(d) · Σ_{m ≤ N/d} (log m)²
```

(this is the standard "Möbius hyperbola" trick). The inner sum
`Σ_{m ≤ x} (log m)² = x · (log x)² − 2 x · log x + 2 x + O(log²x)`
follows from integration by parts on `log²` (a smooth monotone-control
estimate; cf. Tenenbaum I.6.2). The leading-term contribution
`2 N · log N` comes from the `−2 x · log x` term times
`Σ_{d ≤ N} μ(d) / d = O(1)` (Mertens). Estimated ~80–120 LOC for the
leading term alone; the `O(N)` error term is comparable.

After Iter 5, the remaining roadmap is:

- **Iter 6**: clean up the error-term `O(N)` (Möbius hyperbola bound).
- **Iter 7+**: Tauberian step (Erdős–Selberg combinatorial finishing
  argument), discharging `chebyshevPsi_asymptotic`.

## Attempt Counts

- Total attempts: 4 (Iter 1, Iter 2, Iter 3, Iter 4)
- Current approach attempts: 4 (Selberg–Erdős elementary)
- Approaches tried: 1

## Race awareness (this Iter 4)

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open`
at session start returned 0 OPEN PRs (Iter 3 PR #19092 merged
2026-05-15T22:59:33Z, S4 PREP #19171 merged 2026-05-15T22:56:46Z,
stale #17689 CLOSED). Iter 4 touches:

- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` (+24/-12 lines:
  new theorem `selbergLambda2_eq_moebius_log_sq` added after
  `sum_divisors_selbergLambda2_eq_log_sq`; Future Work docstring
  pruned to remove the now-closed Iter 4 entry)
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
  (knowledge + currentState + top-level phase update)
- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (this file)
- `src/data/proofs/chebyshev-bounds-oq-04-oq-01/meta.json`
  (`lineCount` 230 → 325, `theoremCount` 12 → 16, conclusion +
  originalContributions updated for Iter 3 + Iter 4)
- `research/problems/chebyshev-bounds-oq-04-oq-01/sessions/2026-05-16-s5-iter4-act-moebius-log-literal.md` (new)

Pre-push re-check (per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`):
will re-run `gh pr list` immediately before `git push`.
