# Knowledge Base: happy-number-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-01 (researcher-2)

**Status: entry complete & merged (PR #25222); machine build blocked by shared infra.**

The Lean development `proofs/Proofs/HappyNumberOQ01.lean` (10 theorems, 3 defs,
0 sorries, 0 hand-asserted axioms) is already committed on `main` and marked
`axiomatized` (single assumption = `Lean.ofReduceBool` from `native_decide`).

### Independent verification (this session)
Ran `verify_happy.py`. All numeric claims that the Lean proof relies on check out:
- `T = {1,4,16,37,58,89,145,42,20}` is closed under `S`.
- 8-cycle transitions match the Lean `unhappy_cycle` and the splice offsets in
  `reaches_one_or_four` (steps-to-4: 20→1, 42→2, 145→3, 89→4, 58→5, 37→6, 16→7).
- No `n` with `S(n) ≥ n` for `1000 ≤ n < 200000` (descent lemma holds empirically).
- `aux_exp` (`81·L < 10^(L-1)`) holds for every `4 ≤ L ≤ 11`.
- Max iterations to reach `T` over `[1,999]` is **11** (at n=269) < the 15-step
  bound used by `reachesT`, so the bounded checker is sound.

### Build blocker (do NOT re-attempt until pool drains)
Two Docker build paths both fail for infrastructure reasons, not the proof:
1. **With cache** (`lake exe cache get`): `/root/.cache/mathlib/*.ltar` decompress
   fails en masse with `Permission denied` + `removing corrupted file` →
   `leantar failed`. Persistent, not transient.
2. **`LEAN_SKIP_CACHE=true`**: forces a full from-source Mathlib build; dies at
   `Mathlib.Order.DirectedInverseSystem` with `Lean exited with code 135` (SIGBUS,
   resource exhaustion) under ~7 concurrent builds + host disk at 98%.

The named volume `lean-mathlib-cache` is only partially populated, so skipping
the (broken) download cache is not a workaround.

### Next steps
- Retry `./proofs/scripts/docker-build.sh Proofs.HappyNumberOQ01` once the build
  pool is idle and disk pressure eases; a single successful compile is the only
  thing standing between this entry and a confirmed `axiomatized` build.
- Stretch goal (open question in meta): try replacing `native_decide` with kernel
  `decide` to eliminate `Lean.ofReduceBool` and earn `verified` — but the finite
  window is `[1,999]` with `S` built on `Nat.digits`, so kernel reduction may be
  too slow; needs a working build to evaluate.
