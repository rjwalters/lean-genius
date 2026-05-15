# State — chebyshev-bounds-oq-04-oq-01

## Current phase

**Phase**: ACT (Iter 3 dual identity Σ_{d|n} Λ₂(d) = (log n)² verified)
**Iteration**: 4 (Iter 4 in planning — Möbius-inverted "original" form)
**Since**: 2026-05-14T15:50:00Z

## Lean snapshot (post-Iter 3)

| File | LOC | Thm | Defs | Sorries | Axioms | Status |
|---|---:|---:|---:|---:|---:|---|
| `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` | 312 | 15 | 3 noncomputable | 0 | 0 | build-verified 7744 jobs at Iter 3 |
| `proofs/Proofs/ChebyshevBoundsOQ04.lean` | (parent) | — | — | 0 | 1 | parent's `chebyshevPsi_asymptotic` axiom remains the open target |

OQ-04-OQ-01 is the **elementary Selberg–Erdős 1949 PNT** approach to
discharging that parent axiom (no complex analysis).

## Iteration log

### Iter 3 — 2026-05-14 (this session, PR pending)

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

None. Iter 4 (Möbius inversion of the dual identity to the "original"
form `Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d)`) has clear Mathlib API
(`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`), no exotic
typeclass machinery needed.

## Next Action

**Iter 4 — Möbius-inverted "original" form**: prove

```
Λ₂(n) = Σ_{d ∣ n} μ(d) · (log(n/d))²        (for n ≥ 1)
```

by applying `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` to the
Iter 3 dual identity `sum_divisors_selbergLambda2_eq_log_sq`, then
re-indexing `divisorsAntidiagonal` → `divisors` via
`Nat.map_div_right_divisors`. Estimated ~15 LOC.

After Iter 4, the remaining roadmap is:

- **Iter 5–6**: Selberg's symmetry formula
  `Σ_{n ≤ N} Λ₂(n) = 2N log N + O(N)` via summation by parts +
  Möbius hyperbola bound for the error term.
- **Iter 7+**: Erdős finishing argument bridging
  `S₂(N) → ψ(N) ∼ N`, discharging `chebyshevPsi_asymptotic`.

## Attempt Counts

- Total attempts: 3 (Iter 1, Iter 2, Iter 3)
- Current approach attempts: 3 (Selberg–Erdős elementary)
- Approaches tried: 1

## Race awareness (this Iter 3)

`gh pr list -R rjwalters/lean-genius --search "chebyshev-bounds-oq-04-oq-01 in:title" --state open`
at session start returned 1 OPEN PR (#17689, CONFLICTING since
2026-05-12T22:13Z, superseded by merged #17690). Iter 3 touches:

- `proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean` (new lemmas in
  Iter-3-marked section after `selbergLambda2_prime`; existing Iter 1/2
  content unchanged except `Nat.divisors_prime` → `Nat.Prime.divisors`
  at line 191)
- `proofs/Proofs/ChebyshevBoundsOQ04.lean` (1-LOC parent regression
  fix at line 298)
- `src/data/research/problems/chebyshev-bounds-oq-04-oq-01.json`
  (knowledge + currentState + top-level phase update)
- `research/problems/chebyshev-bounds-oq-04-oq-01/state.md` (this file)

No file overlap with stale #17689 — the parent fix and rename are
incidental to Iter 3, and #17689's "Iter 2 prime values" content was
already merged via #17690 (verified during pre-claim race check).
