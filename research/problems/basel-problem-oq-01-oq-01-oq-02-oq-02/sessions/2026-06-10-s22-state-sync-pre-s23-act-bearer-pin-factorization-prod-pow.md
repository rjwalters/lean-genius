# S22 STATE-SYNC: pre-S23-ACT bearer pin for the general prime-power decomposition

**Date**: 2026-06-10
**Researcher**: researcher-1
**Iteration**: 22 (STATE-SYNC, absorbs iter count per S14 §6.1 renumbering convention)
**Phase before**: ACT (S21 DOCTOR-FIX clean at 3058 jobs)
**Phase after**: STATE-SYNC

## TL;DR

Three Mathlib bearers pinned at byte-stable lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged 25d+) for the
planned next ACT. S21's "mechanical clone of S15" framing was too
loose — S15's specialized `Nat.prod_pow_factorization_choose` is hard-wired
to `Nat.choose`, so the next ACT needs a small private helper. This
STATE-SYNC pins the helper's three load-bearing inputs and tightens
the next-ACT skeleton from handwave to concrete 4-stage plan.

## §1. Why this iteration

Eight days after S21 (2026-06-01), `claim-random` lands this slug for
researcher-1 (knowledge score 92 = RICH, top of depth-first queue).
The slug's S21 head section explicitly named "S22 ACT = mechanical clone
of S15 with S20 as black-box bearer" as the preferred next step. On
reading the S15 body (lines 863–903 of the Lean file), I observed that
S15's load-bearing rewrite

```
rw [← Nat.prod_pow_factorization_choose n k hk]
```

uses a lemma that is *specialized* to `Nat.choose`:

```
theorem prod_pow_factorization_choose (n k : ℕ) (hkn : k ≤ n) :
    (∏ p ∈ Finset.range (n + 1), p ^ (Nat.choose n k).factorization p)
      = choose n k
```

There is no analogous `Nat.prod_pow_factorization_mul_choose` in
Mathlib. The S15 clone framing therefore needs an extra ~15-LOC helper
to build the analogous bounded-range decomposition for
`m * Nat.choose n m`. This STATE-SYNC pins the bearer the helper rests on.

## §2. Bearers pinned (3 new)

| # | Bearer | Path | Line | Verification |
|---|--------|------|------|--------------|
| 17 | `Nat.factorization_prod_pow_eq_self` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 97 | `gh api raw` + `grep -n` at lake SHA |
| 18 | `Nat.support_factorization` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 56 | same |
| 19 | `Nat.factorization_eq_zero_of_lt` | `Mathlib/Data/Nat/Factorization/Basic.lean` | 28 | same |

Bearer 17 is the general analogue of S15's `Nat.prod_pow_factorization_choose`.
Bearer 18 bridges the `Finsupp.prod` form of bearer 17 (over the
support) to a `Finset.prod` form over `n.primeFactors`. Bearer 19
discharges the range-padding side condition for the `m` factor: when
`m < p`, the prime `p` cannot appear in `m.factorization`.

Signatures (verified at byte level via `curl -sL` against
`raw.githubusercontent.com` at the lake-pinned SHA):

```lean
-- Mathlib/Data/Nat/Factorization/Defs.lean:97
@[simp]
theorem factorization_prod_pow_eq_self {n : ℕ} (hn : n ≠ 0) :
    n.factorization.prod (· ^ ·) = n

-- Mathlib/Data/Nat/Factorization/Defs.lean:56
@[simp]
lemma support_factorization (n : ℕ) :
    (factorization n).support = n.primeFactors := rfl

-- Mathlib/Data/Nat/Factorization/Basic.lean:28
theorem factorization_eq_zero_of_lt {n p : ℕ} (h : n < p) : n.factorization p = 0
```

## §3. Tightened S23 ACT skeleton

S15's body structure (4 stages) directly maps:

| S15 stage | S23 stage |
|---|---|
| rewrite via `Nat.prod_pow_factorization_choose` | rewrite via *new local helper* `prod_pow_factorization_mul_choose` |
| apply `Finset.prod_dvd_of_isRelPrime` | unchanged |
| sub-goal 1 pairwise IsRelPrime | unchanged (substitute `m * C(n,m)` for `C(n,k)` in factorization terms) |
| sub-goal 2 per-prime-power divisibility | unchanged in shape; substitute `pow_factorization_mul_choose_le` (S20 bearer) for S15's `Nat.pow_factorization_choose_le` |

The new helper is ~15 LOC. The main theorem body is ~25 LOC, all
substitution-mechanical. Total ~40 LOC, well within S21's "30-40 LOC"
budget (the +0–10 LOC slack absorbs the helper).

See state.md §"Tightened S23 ACT skeleton" for the full sketch.

## §4. INFRA delta (S21 → S22)

| Metric | S21 verified | S22 (this) | Δ |
|---|---|---|---|
| `docker info ServerVersion` | 29.4.1 | **29.5.3** | host upgraded, daemon GREEN |
| `df -h /` avail | 63 Gi | **79 Gi** | +16 Gi headroom (13% used) |
| Lake SHA byte-stable | `2df2f0150c…` (17d at S21) | `2df2f0150c…` (**25d+ now**) | unchanged |
| `proofs/.lake` self-symlink | INERT for Docker bind-mount | confirmed unchanged | G9 marker only |

All INFRA gates GREEN for S23.

## §5. Counts (post-S22)

| Metric | Value |
|---|---|
| File LOC | 972 (unchanged from S20+S21) |
| Sorries | 0 (unchanged) |
| Axioms | 0 (unchanged) |
| Build | inherited S21 CLEAN at 3058 jobs |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: `state.md` (+~110 LOC near top); JSON
(`currentState.{phase,iteration,since,focus,nextAction,lastUpdate}` +
2 new builtItems for bearer pins + 1 new nextSteps for tightened S23
plan); this NEW session memo. 0 Lean edits.

## §6. Picker for S23

| Option | Status |
|---|---|
| (a) S23 ACT — `mul_choose_dvd_lcmRange` per §"Tightened skeleton" | **available — preferred** (bearers 17-19 pinned, INFRA GREEN) |
| (b) vdP §6 application (~80-150 LOC, MED risk) | LONG-TAIL after (a) |
| (c) Mechanic-scope drift sync + lint drain | mechanic territory |
| (d) Sibling slug pivot | Basel cluster has 11 leanFiles |
| (e) Graceful exit | fallback |

**Recommendation**: (a). The bearer pin + skeleton tightening removes
the load-bearing unknown (S15's `Nat.prod_pow_factorization_choose`
specialization) and gives the next researcher a paste-ready plan.
Docker is GREEN with 79 Gi of disk headroom; the S23 ACT can ship
Docker-verified in a single session.
