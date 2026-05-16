# Current State

**Phase**: ACT-READY
**Since**: 2026-05-16T07:25:00.000Z
**Iteration**: 3

## Current Focus

`k = 2` infinite-family elimination: prove `bound_k_two (n : ℕ) (h : 4 ≤ n) : LPFBound n 2` joining the existing `not_exception_k_zero` and `not_exception_k_one` structural results. This is the next sharp-boundary advance after the file reached 0-axiom / 0-sorry status in PR #7229 (S1 closure, 2026-03-13).

## Active Approach

Case-split on parity of `n` via `Nat.mod_two_eq_zero_or_one`:
- Even `n`: `n.choose 2 = (n/2) * (n - 1)`, witness `n - 1` for `(n/2) ∣ n.choose 2`.
- Odd `n`: `n.choose 2 = n * (n/2)`, witness `n` for `(n/2) ∣ n.choose 2`.
Then apply `Nat.minFac_le_of_dvd` with `2 ≤ n / 2` (from `n ≥ 4`).

Paste-ready Lean code documented in `sessions/2026-05-16-s2-prep-bound-k-two.md` §3.
9 Mathlib bearers pin-audited on SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

## Blockers

None for math. **G7 host disk 100% capacity** is infrastructure-only and does not block ACT — three fallback paths documented in PREP §5:
1. Wait for host disk recovery
2. Trust cache-replay for small structural elaboration (~200ms expected)
3. Ship `(build pending — disk pressure)` per `_docker_build_disk_full_ship_build_pending_per_s5_act_precedent` memory pattern

## Next Action

**S3 ACT**: apply PREP §3 paste to `proofs/Proofs/Erdos1094Problem.lean` between lines 142 and 144 (after `not_exception_k_one`). Run `./proofs/scripts/docker-build.sh Proofs.Erdos1094Problem`. Ship PR `research(erdos-1094): S3 ACT — bound_k_two infinite family for k=2`.

If build succeeds: also update `src/data/proofs/erdos-1094/meta.json` lineCount 248 → ~286 and theoremCount 38 → 40.

If next researcher pivots, two parallelisable follow-ups documented in PREP §9:
- **OQ-01**: `bound_k_three` (parity-mod-3 analysis, 50-80 LOC)
- **OQ-02**: `bound_k_even_n` for all `k` (Kummer / `Nat.Prime.multiplicity_choose`, 30-50 LOC, eliminates entire even-n axis)

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 0
- Approaches tried: 1 (S1: axiom elimination via PR #7229)

## Iteration History

| Iter | Date | Phase | Outcome | PR |
|---|---|---|---|---|
| 1 | 2026-03-13 | ACT | Eliminated `main_implies_384` axiom (proved naive #384 false via C(7,3) counterexample); added corrected `ErdosProblem384` def; file reached 0-axiom/0-sorry | #7229 |
| 2 | 2026-03-13 | (closure) | meta.json marked status=axiomatized | #7229 |
| 3 | 2026-05-16 | PREP | This session: §-paste-ready `bound_k_two` + bearer pin table + ACT-readiness gate; doc-only | (this PR) |

## Open PRs touching `erdos-1094`

None (`gh pr list --search "erdos-1094 in:title"` returned 0 open as of 2026-05-16T07:30Z).

## Lean Inventory (verified this session)

```
proofs/Proofs/Erdos1094Problem.lean
  lines:     248
  theorems:  38
  axioms:     0
  sorries:    0
  defs:       8
```

Header docstring: lines 1-19. Namespace open: line 23.
Parts: 1 (defs, 24-36), 2 (conjecture, 38-43), 3 (14 exceptions, 45-83), 4 (8 non-exceptions, 85-111), 5 (basic properties, 113-150), 6 (Selfridge, 152-158), 7 (stronger bounds, 160-175), 8 (Prob 384, 177-211), 9 (binomial props, 213-219), 10 (summary, 221-248).

Insertion point for S3 ACT: between lines 142 (`exact hbound (bound_k_one n (by omega))`) and 144 (`-- Verified small cases of the n=2k bound`).

## Source-of-truth audit

Mathlib pin verified `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `proofs/lake-manifest.json` (v4.26.0 inputRev). All 9 bearer lemmas confirmed present via `gh api repos/leanprover-community/mathlib4/contents/...?ref=<pin>` this session. No bearer drift detected since file last touched 2026-03-13.
