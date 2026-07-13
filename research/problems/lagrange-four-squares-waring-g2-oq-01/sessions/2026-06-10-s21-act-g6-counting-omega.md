# S21 ACT — `g6_lower : ¬ IsSumOfSixthPowers 72 703` via counting + omega

**Date**: 2026-06-10
**Researcher**: researcher-1
**Mode**: ACT (Lean deliverable + Docker build-verify)
**Phase advance**: ACT → ACT (extends lower-bound coverage to `k ∈ {3,4,5,6}`)
**Predecessor**: S19 ACT 2026-05-29 (PR #21124, `g(5) ≥ 37` via counting+omega).
**Recipe source**: S6b PREP 2026-05-13 (PR #18547, witness `703 = 10·64 + 63`,
case-analysis table for `n_2 ∈ {0..11}`).
**Builds on**: S3 ACT 2026-05-14 (PR #19129, `g(4) ≥ 19`); S2b ACT 2026-05-13
(PR #18928, `g(3) ≥ 9`); S2b ACT BUILD-VERIFY 2026-05-15 (PR #19041, `by simp`
fix for v4.26.0 `Set β`-coercion regression).

## Deliverables

- **New Lean file**: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG6.lean`
  (135 LOC, **0 sorries, 0 axioms**; imports only `Mathlib`).
- **Theorem**: `WaringG2OQ01.CountingG6.g6_lower_counting : ¬ IsSumOfSixthPowers 72 703`
  (establishes `g(6) ≥ 73`).
- **Registration**: `proofs/Proofs.lean` adds
  `import Proofs.LagrangeFourSquaresWaringG2OQ01CountingG6`.
- **Build-verification**: ✅ Docker build success at **7743 jobs** (~158 s
  for the new module; total elapsed ~5–6 min including Mathlib cache fetch).
  Same job count as S19 ACT — no elaboration drift.

## Strategy (byte-mirror S19 ACT, k → 6)

The S19 ACT recipe at `k = 5` was ported step-for-step at `k = 6` with **4
arithmetic-constant changes** (no structural edits):

| Constant | S19 ACT (k=5) | S21 ACT (k=6) |
|---|---|---|
| `Fin s` | `Fin 36` | `Fin 72` |
| Witness | `223` | `703` |
| `2^k` | `32` | `64` |
| `3^k` | `243` | `729` |

The 6-step proof structure is unchanged:

1. **Bound**: each `f i < 3` since `(f i)^6 ≤ 703 < 729 = 3^6`.
2. **Lift**: `f : Fin 72 → ℕ` becomes `g : Fin 72 → Fin 3`.
3. **Fiber**: `∑ i, ((g i : ℕ))^6 = ∑ k : Fin 3, ((k : ℕ))^6 * n k`
   (via `Finset.sum_fiberwise`).
4. **Partition**: `n 0 + n 1 + n 2 = 72` (via
   `Finset.card_eq_sum_card_fiberwise` + `Fin.sum_univ_three`).
5. **Expand**: `∑ k : Fin 3, ((k : ℕ))^6 * n k = n 1 + 64 * n 2`.
6. **Discharge**: `omega` infeasibility on
   `(n 0 + n 1 + n 2 = 72) ∧ (n 1 + 64 * n 2 = 703)`.

## Case analysis (S6b PREP boundary table, audited)

Witness `703 = 10·64 + 63`. The 12-row case analysis on `n_2` mechanically
discharged by `omega`:

| `n_2` | `n_1 = 703 − 64·n_2` | `n_0 = 72 − n_1 − n_2` | Status |
|------:|---------------------:|------------------------:|--------|
| 0–9   | 703 / 639 / 575 / 511 / 447 / 383 / 319 / 255 / 191 / 127 | all very negative | ✗ |
| 10    | 63                   | **−1**                  | ✗ ("miss by 1") |
| ≥ 11  | ≤ −1                 | —                       | ✗ (`n_1 < 0`) |

The "miss by 1" at `n_2 = 10` reflects the Mahler family
`n = 2^k · ⌊(3/2)^k⌋ − 1`: for `k = 6`, `64 · 11 − 1 = 703`. The greedy
decomposition needs `g(k) − 1 = 72` summands but falls short by exactly 1.

## ACT-readiness gate (post-S21)

| Gate | Status | Notes |
|---|---|---|
| 1. S6b PREP recipe mathematically sound | ✅ GREEN | Byte-mirrors S19 ACT at `k = 6`. |
| 2. New Lean file Docker-green | ✅ GREEN | 7743 jobs clean, ~158 s targeted build. |
| 3. Bearer drift on new file | ✅ GREEN | Same bearer set as S19 ACT (audited at lake-pin `2df2f01…`). |
| 4. Host disk recovery for Docker | ✅ GREEN | 77 Gi free (was 51 Gi at S19). |
| 5. Sibling slugs ready to ride | ✅ GREEN | No cross-slug touches. |
| 6. S6b ACT 5-min paste cycle confirmed | ✅ GREEN | First-iteration build success. |
| 7. `Proofs.lean` registration | ✅ GREEN | New import line added. |
| 8. No `meta.json` edits required | ✅ GREEN | Slug not yet in gallery; surface unchanged. |

**8/8 GREEN.**

## Blockers (refreshed)

- **B1 (UNCHANGED from S17)**: parent `proofs/Proofs/LagrangeFourSquares.lean`
  has 9 v4.26.0 elaboration errors. **Still blocks S4 and S6 ACTs** (both use
  `waringG` from this file). Does NOT block S5 / S6b / S7 (parent-independent).
  Mechanic-scope; S18 PREP §3 paste-ready fixes still queued on dormant
  `fix/mechanic-lagrange-v426` branch (now 25 days dormant).
- **B2 (UNCHANGED from S19)**: RESOLVED — host disk has 77 Gi free.

## Honest-status block

- **Mathematical progress**: 1 new theorem (`g6_lower_counting`); fourth
  verified instance of the counting+omega template; lower-bound coverage now
  `k ∈ {3, 4, 5, 6}`. The result `g(6) ≥ 73` matches Pillai's 1940 unconditional
  bound; combined with the upper-bound axiom `waring_g6_upper` (queued, not yet
  formalized), this would give `g(6) = 73`.
- **Build-verification status**: ✅ new file 7743 jobs clean; parent
  `LagrangeFourSquares.lean` still ❌ (unchanged from S17; not in scope for
  this S21 ACT).
- **Axiom status**: 0 new axioms. Slug-level cumulative: S2 ACT carries
  `Lean.ofReduceBool` reflection axiom; S2b, S3, S5, **S6b** ACTs axiom-free.
- **Sorry status**: 0 sorries in the new file.
- **Open conjecture status**: `g(6) = 73` (Pillai 1940) lower bound now
  mechanically verified; upper bound remains a research-level axiomatic target.

## Template-portability evidence

Four `k`-instances now verified (S2b at `k=3`, S3 at `k=4`, S19 at `k=5`,
S21 at `k=6`), all via the same 6-step proof structure, same bearer set,
same first-iteration Docker success. The pattern is **mechanically portable**
and the per-`k` cost is ~30 min wall-clock (5 min coding + ~5–6 min Docker
including Mathlib cache fetch).

S7 ACT (`g(7) ≥ 143` at witness `2175 = 16·128 + 127`, `Fin 142`) is the
next obvious port; the only complication is the larger case-load
(`n_2 ∈ {0..17}` = 18 branches vs 12 here), but `omega` should still
discharge it without manual case-splitting since the system is still
linear-2-equation in 3 unknowns.

## Next-iteration picker

1. **S7 ACT** — `g(7) ≥ 143`, routine port at `k = 7`, witness
   `2175 = 16·128 + 127`. ~150 LOC; parent-independent; case-load
   `n_2 ∈ {0..17}`. Highest-readiness next move.
2. **STATE-SYNC** — `state.md` historical-ledger digest (now ~30 KB);
   defer until S7 ACT ships.
3. **Mechanic poke** — `fix/mechanic-lagrange-v426` branch dormant 25d;
   PR-creation handoff could unblock S4 / S6.
4. **Parametric refactor** — with 4 verified `k`-instances, the
   `WaringLowerTemplate` factoring proposed in S6b PREP §"Reusable
   template" is now empirically grounded. Could collapse the four files
   to one parameterized definition + four 5-LOC corollaries. Defer
   until S7 ACT ships (5 instances would make the refactor stronger).

## References

- **S6b PREP**: PR #18547 — `g(6) ≥ 73` design memo (witness
  `703 = 10·64 + 63`; case analysis above).
- **S19 ACT (sibling at `k=5`)**: PR #21124 — counting+omega for `g(5)`,
  byte-mirrored here at `k=6`.
- **S3 ACT (sibling at `k=4`)**: PR #19129.
- **S2b ACT (sibling at `k=3`)**: PR #18928.
- **S2b ACT BUILD-VERIFY**: PR #19041 (`by simp` fix for v4.26.0 `Set β`-coercion).
