# S28 (tracker S12) — `(246, 50)` decided; the Engelsma axiom is eliminated

**Date**: 2026-09-29
**Agent**: researcher-1
**Mode**: REVISIT (RICH, score 64)
**Outcome**: completed-target — `engelsma_lower_bound` is no longer an axiom.

## §1 The feasibility question answered: the wall was a phantom

Every plan since S4 flagged the `(246, 50)` computation as an untested
wall-clock/memory risk, with a probe-first protocol. The probe took one
scratch file:

| `(w, k)`    | value | interpreter time |
|-------------|-------|------------------|
| `(32, 10)`  | false | 0.09 ms |
| `(76, 20)`  | false | 2.6 ms  |
| `(124, 30)` | false | 0.8 ms  |
| `(176, 40)` | false | 4.0 ms  |
| `(246, 50)` | false | **108 ms** |
| `(247, 50)` | true  | 39 ms   |

All values match Engelsma's H-table (H(20)=76, H(30)=124, H(40)=176,
H(50)=246) at every point, `false` at the exact width and `true` one wider.

Why so fast: `chosen` stays `[0]` throughout, so the node guard
`candidates.length < k - chosen.length` compares the pool against the
constant `k - 1`, while each prime level multiplies the pool by
`(p - 1)/p`. By Mertens the pool crosses below `k - 1` within the first
~6 primes on almost every residue combination, so the effective search
tree is tiny — the naive ∏(p−1) branch-count estimate is off by many
orders of magnitude.

## §2 What landed

1. `BoundedPrimeGapsOQ03OQ02.lean` S28 section:
   `engelsmaSearchPruned_246_50_eq_false` (`native_decide`),
   `engelsmaSearchPruned_247_50_eq_true` (sharpness cross-check: the
   `true` side re-derives, via the S27 soundness direction, what the
   parent's explicit `engelsma50Tuple` witnesses — H(50) = 246 exactly),
   and `engelsma_lower_bound_verified` (the bridge consumer applied).
2. `BoundedPrimeGapsOQ03.lean`: `import Proofs.BoundedPrimeGapsOQ03OQ02`;
   Part IV's `axiom engelsma_lower_bound` → `theorem` with the SAME name
   and byte-identical statement, proved by
   `BoundedPrimeGapsOQ03OQ02.engelsma_lower_bound_verified`. Every
   downstream consumer (7 use sites, Parts V–VI) is untouched.
3. Gallery `bounded-prime-gaps-oq-03/meta.json`: `leanFile.axiomCount`
   1 → 0, `lineCount`s refreshed, `meta.axiomCount` stays 1 — now counting
   `Lean.ofReduceBool` per the gallery native_decide convention (the
   headline result is native_decide-backed, so the entry remains
   `axiomatized`/`axiom`); `assumptions` rewritten accordingly.

`#print axioms engelsma_lower_bound`: foundational + per-declaration
`…native_decide.ax_*` instances only. The trust base narrows from "an
external 2013 computation nobody can re-run" to the Lean compiler.

## §3 Verification

- Host: plain `lean` (v4.31.0, shared Mathlib oleans), both files exit 0.
- Docker `docker-build.sh Proofs.BoundedPrimeGapsOQ03` — green (see PR).
- Pre-existing `push_neg` deprecation warning at OQ03.lean:97 (untouched
  code) — not introduced by this change.

## §4 State after S28

The OQ-03-OQ-02 mission — replace the Engelsma axiom by a verified
search — is **COMPLETE** (S26 soundness repair → S27 bridge → S28
compute). Optional follow-ons only: kernel-`decide` for small sanity
tests; parametric H(k) verification for other table entries. Remaining
assumptions of the bounded-prime-gaps cluster (`maynard_tao_sieve`, the
analytic sieve input) live in parent entries and are out of scope here.
