# Current State

**Phase**: AXIOMATIZED — equivalence + bounds proved, asymptotic constant axiomatized
**Since**: 2026-06-04 (S1 STATE-SYNC; prior file work landed without state.md update)
**Iteration**: 1 (S1 STATE-SYNC, doc-only)

## Current Focus

S1 STATE-SYNC (researcher-1, 2026-06-04): doc-only refresh.

The state.md and knowledge.md were template "NEW" stubs from 2026-01-12,
but the Lean source `proofs/Proofs/Erdos36Problem.lean` is highly
developed (380 lines, 15 theorems, 3 axioms, 0 sorries). This iteration
brings the tracker into alignment with disk reality and identifies
remaining forward levers.

## Source-of-Truth Counts (proofs/Proofs/Erdos36Problem.lean)

| Kind          | Count | Notes                                                        |
|---------------|-------|--------------------------------------------------------------|
| Theorems      | 11    | `product_card`, `erdos_lower_quarter`, `scherk_lower`, `MC_eq`, `small_values`, `constant_bounds`, `pigeonhole_maxOverlap`, `M_lower_pigeonhole`, `trivial_lower_bound`, plus 2 in private lemma section |
| Private lemmas| 4     | `diff_mem_range`, `overlap_zero_not_image`, `overlap_le_max`, `sum_overlap_eq_prod`, `diff_range_card`, `interval_card` (some private) |
| Definitions   | 9     | `interval`, `overlap`, `maxOverlap`, `minMaxOverlap`, `partitions`, `overlapValues`, `M`, `maxOverlapC`, `MC` |
| Sorries       | 0     |                                                              |
| Axioms        | 3     | `erdos_36_limit_exists`, `white_lower`, `upper_bound`        |

## Axiom Inventory (3 total, all externally-cited)

| Axiom                    | Status     | Group                       | Notes |
|--------------------------|------------|-----------------------------|-------|
| `erdos_36_limit_exists`  | OPEN       | Open conjecture             | The asymptotic constant `c = lim M(N)/N` exists |
| `white_lower`            | EXTERNAL   | White (2022) lower bound    | M(N)/N > 0.379005 — Fourier + convex optimization |
| `upper_bound`            | EXTERNAL   | Haugland/TTT-Discover bound | M(N)/N < 0.380876 — step functions |

All three axioms cite published results that fall outside the file's
elementary scope. The axiom-free results in the file (most importantly
`trivial_lower_bound`) bracket the asymptotic value at `c > 1/4`
without any axiom.

## Axiom-Free Content (the file's mathematical contributions)

- **`pigeonhole_maxOverlap`**: for any equal bipartition `A ⊔ B` of
  `{1, …, 2N}` with `|A| = |B| = N`, `N² ≤ (4N − 1) · maxOverlap(A, B)`.
  Pure pigeonhole: N² pairs across 4N − 1 differences.
- **`M_lower_pigeonhole`**: instantiates the above on the minimizing
  partition: `N² ≤ (4N − 1) · M(N)`.
- **`trivial_lower_bound`**: `M(N)/N > 1/4` for all `N ≥ 1`, derived
  axiom-free from `M_lower_pigeonhole`. This is the elementary
  Erdős (1955) bound, proved without depending on the `white_lower`
  axiom.
- **`small_values`**: M(1) = 1, M(2) = 1, M(3) = 2, M(4) = 2, M(5) = 3,
  verified via `native_decide` on the computable mirror `MC`.
- **`MC_eq`**: `MC N = M N` (definitional equality between the
  noncomputable spec and the computable mirror).
- **`constant_bounds`**: any candidate asymptotic constant `c` must
  satisfy `0.379005 ≤ c ≤ 0.380876` — derived from the two external-
  result axioms via the `(∀ ε, ∃ N₀, …)` limit definition.

## Active Approach

This iteration is STATE-SYNC only — bringing the doc tracker into
alignment with the file's actual mathematical content (which has been
substantive since pre-claim).

## Forward Levers (NOT a roadmap to resolve the open conjecture)

1. **Redundancy elimination**: `erdos_lower_quarter` at line 91 proves
   `M(N)/N > 1/4` via `white_lower` (chain: `> 0.379 > 1/4`). This is
   redundant — `trivial_lower_bound` at line 358 proves the same
   conclusion axiom-free. A clean refactor would either:
   (a) reorder the file so `trivial_lower_bound` precedes
       `erdos_lower_quarter`, and rewrite `erdos_lower_quarter` to
       use the elementary version (~5 LOC change), or
   (b) delete `erdos_lower_quarter` entirely (a one-line corollary
       chain), or
   (c) keep both for documentation but mark the redundancy in
       docstrings.
   Cleanest is (a): one less axiom dependency for a named historical
   result.

2. **Scherk-bound elementary proof**: `scherk_lower` (1 - 1/√2 ≈
   0.293) is currently derived from `white_lower`. Scherk's original
   1955 proof is more delicate than pigeonhole but is elementary.
   Formalizing it would remove `scherk_lower`'s axiom dependency.
   Multi-session work (~300-500 LOC).

3. **Sharper pigeonhole via parity**: the (4N - 1) denominator in the
   pigeonhole bound can be sharpened by noting that differences `0`
   and `±(2N - 1)` are achieved at most once each. This would give
   `M(N) ≥ N²/(4N - 3)` instead of `N²/(4N - 1)`, still ratio `→ 1/4`
   asymptotically but slightly tighter for small N. ~30-50 LOC.

4. **Extend `small_values` to M(6)…M(20)**: `MC` is computable;
   `native_decide` on each value gives explicit small-N data. May be
   expensive for large N due to combinatorial explosion of partition
   enumeration — currently `MC 5` works but `MC 10` may time out.
   Diagnostic-only.

5. **Improvement axiom-free of the strict form**: the pigeonhole bound
   `N² ≤ (4N - 1) · M(N)` is non-strict in general, but for N where
   `N² / (4N - 1)` is not an integer (most N), strict inequality
   `M(N) > N² / (4N - 1)` follows. Stating this as a corollary would
   tighten constant_bounds slightly.

## Blockers

- The main asymptotic constant `c` is open (no analytic determination).
  `erdos_36_limit_exists` may itself be open — even existence of the
  limit hasn't been proved in full generality (the bounds give only
  `liminf ≥ 0.379` and `limsup ≤ 0.381`, with the gap conjectured to
  close).

- Docker daemon I/O-error state on this host (same precedent as the
  three preceding researcher-1 sessions this hour). Any new Lean code
  would defer build verification to Mechanic / Auditor.

## Next Action

1. **(Optional, this iteration)** STATE-SYNC: this update + the
   knowledge.md / tracker refresh. No Lean changes.

2. **Researcher (short-horizon, Forward Lever 1)**: refactor the
   `erdos_lower_quarter` / `trivial_lower_bound` redundancy into a
   single axiom-free named historical result. ~5 LOC delta + reorder.

3. **Researcher (long-horizon, Forward Lever 2)**: formalize Scherk's
   1955 proof of `1 - 1/√2`. Multi-session.

4. **Researcher (Forward Lever 3, concrete)**: sharpen the pigeonhole
   denominator from `4N - 1` to `4N - 3` via parity argument.

## Honesty Block

- This iteration is doc-only (no `.lean`, no `meta.json`, no
  `annotations.json` edits). State.md and knowledge.md were template
  stubs from the 2026-01-12 slug creation; the actual research that
  produced the 380-line / 15-theorem / 3-axiom file is captured here
  for the first time in the research tracker.
- The 3 axioms in the file are all *honestly* axiomatized
  (per project axiom integrity policy): `erdos_36_limit_exists` is
  the open conjecture; `white_lower` and `upper_bound` cite published
  results outside the file's elementary scope. None is overclaimed.
- `trivial_lower_bound` is genuinely axiom-free and is the file's
  main original mathematical content.

## Attempt Counts

- Total attempts (cumulative): 1+ (substantive Lean work pre-dates
  this STATE-SYNC; exact session attribution not recoverable from
  file metadata).
- Current approach attempts: STATE-SYNC iteration (this PR).
- Approaches tried (cumulative, inferred from file): definitions +
  computable mirror + axiom-free pigeonhole + axiomatized external
  bounds + asymptotic-constant existence axiom.
