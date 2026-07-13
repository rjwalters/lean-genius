# Current State

**Phase**: AXIOMATIZED
**Since**: 2026-05-16T09:10:00Z
**Iteration**: 9

> **Phase note (skill-compliance footnote):** `AXIOMATIZED` here means the
> slug-level deliverable is in maintenance / deferred-extension mode (Lean
> file is build-verified at 0 axioms / 0 sorries; status `"axiomatized"`
> per the open-conjecture convention in `CLAUDE.md` Axiom Integrity Policy,
> not via `axiom` declarations). Maps to skill-canonical `OBSERVE` for the
> next research wake-up.

## Current Focus

Maintenance / deferred extension. The Lean file
`proofs/Proofs/Erdos374Problem.lean` is at 265 LOC with 13 named theorems
+ 3 private lemmas + 5 definitions, 0 axioms, 0 sorries. Status
`"axiomatized"` per open-conjecture convention. The structural pillars
(D₂ backward direction `{n² : n ≥ 2} ⊆ D₂`, prime exclusion
`Prime p → ¬inDk k p` for `k ≥ 2`, and edge case `1 ∈ D₂`) are
proven. The open growth-rate question for `|D_k ∩ {1,…,n}|` with
`3 ≤ k ≤ 6` remains formally unstated; extension would axiomatize
the conjecture and add provable consequences.

## Active Approach

None in flight. Last active approach (S8, PR #8355, 2026-03-30): proved
`squares_have_square_factorial_product` via the `[n²−1, n²]` witness with
the factorization `(n²−1)! · n²·(n²−1)! = (n·(n²−1)!)²`. Build-verified
under Mathlib `v4.26.0`.

## Blockers

None.

## Next Action

Three orthogonal extension paths, increasing risk order:

- **(a) LOW** — Add `527 ∈ D_6` as a `theorem`-with-sorry witness
  (Erdős–Graham 1976 / Luca–Saradha–Shorey 2014). Decide-reduction
  infeasible (search space too large); requires hand-constructed
  6-element factorial witness. Estimated ~30 LOC + 1 sorry.

- **(b) MEDIUM** — Forward D₂ direction `inDk 2 m → ∃ n, m = n*n` to
  complete the `D_2 = {n² : n ≥ 2}` equivalence. Requires showing the
  only valid 2-element sequence ending at `m` with square factorial
  product is `[n²−1, n²]`. Estimated ~80 LOC.

- **(c) HIGH** — Axiomatize the open growth-rate conjecture
  `axiom growth_rate_D_k : ∀ k ∈ {3,4,5,6}, ∃ f : ℕ → ℕ, |{m ≤ n : inDk k m}| = f n + o(f n)`
  plus 2-3 conditional consequences. Would change `axiomCount` 0 → 1
  and require `meta.json` update.

ACT-readiness: **GREEN** for (a) and (b); **AMBER** for (c) (asymptotic
sequence infrastructure not yet in scope).

This S9 STATE-SYNC PR does **not** execute any of these; it only
documents the true current state.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 0
- Approaches tried: 4
  - (a) constructive `[n²−1, n²]` witness for `D_2` backward
  - (b) Legendre `v_p(p!) = 1` + `not_prime_dvd_factorialProduct` induction for prime exclusion
  - (c) `[0,1]` witness for `1 ∈ D_2` edge case
  - (d) `Nat.find` for `bigF` noncomputable definability

## Session Log Pointer

See `sessions/2026-05-16-s09-state-sync-axiomatized-265loc-deferred-growth-rate.md`
for the full audit trail (file-level inventory tables, iteration ledger
referencing PR #5368, #7259, #7264, #7521, #7272, #8308, #8347, #8355,
and out-of-scope deferred extensions).
