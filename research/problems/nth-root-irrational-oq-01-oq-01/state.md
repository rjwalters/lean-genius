# Research State: nth-root-irrational-oq-01-oq-01

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-16T00:00:00-07:00
**Iteration**: 7

## Current Focus
Slug COMPLETE and VERIFIED. The exact-degree item that this file previously
listed as the open "Next Action" was already closed: `NthRootIrrationalOQ01OQ01Degree.lean`
(`finrank_adjoin_trace_eq`: `2·[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)`, 0 sorries / 0 axioms) is
registered in `proofs/Proofs.lean` and was Docker-verified green on 2026-06-15
(the final S2/researcher-5 session that fixed the `synthInstance.maxHeartbeats`
timeout and built all five files). state.md was frozen at the earlier S6
certification session (#24640) and never advanced past ACT — this update syncs it
to match `knowledge.md` (header: COMPLETED/VERIFIED), the problem JSON
(`status: completed`, `phase: COMPLETED`), and `meta.json` (`verified`/`original`,
0 axioms, 0 sorries).

## Completed Result
Five-file Niven/cyclotomic family, all merged, registered, and Docker-green:
- `NthRootIrrationalOQ01OQ01.lean` — primitive n-th root of unity irrational (n≥3);
  rational roots of unity are ±1.
- `NthRootIrrationalOQ01OQ01Real.lean` — `2cos(2π/n)` irrational for φ(n)≥3.
- `NthRootIrrationalOQ01OQ01Cos.lean` / `…CosRational.lean` — full Niven
  classification: `cos(2π/n)` rational ⇔ n ∈ {1,2,3,4,6}, values {1,−1,−1/2,0,1/2}.
- `NthRootIrrationalOQ01OQ01Degree.lean` — exact degree `2·[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)`,
  turning the rationality criterion into a degree theorem.

## Blockers
None. No genuinely-open sub-item remains.

## Next Action
None — slug complete. Only conceivable extension is additional concrete small-`n`
instantiations beyond the existing `fifthRoot` example, which would be cosmetic
(no new theory). No follow-up OQ warranted.
