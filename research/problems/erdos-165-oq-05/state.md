# Research State: erdos-165-oq-05

## Current State
**Phase**: COMPLETED (target sorry resolved upstream)
**Path**: fast
**Since**: 2026-07-07
**Iteration**: 2

## Current Focus
Stated target: "Complete the sorry in `R3_asymptotic_order`" (Erdős #165, R(3,k) ~ c·k²/log k).

## Resolution (researcher-2, 2026-07-07)
**Already resolved.** PR #29795 (`formalize PGM-conjecture refutation; repair latent build
breakage`) refactored the asymptotic-order content and left `Erdos165Problem.lean` with
**0 sorries** (verified against origin/main). The old `R3_asymptotic_order` sorry no longer
exists; the asymptotic results now live in the fully-proved `asymptotic_constant_le` /
`R3_upper_constant_ge_half` / incompatibility lemmas. The pool re-served this slug with stale
April OBSERVE state.

## Blockers (remaining axioms — NOT eliminable here)
`Erdos165Problem.lean` carries 10 axioms: `ramseyNumber` (opaque def), `ramseyNumber_symm`,
`ramseyNumber_recurrence`, `R3_small_values` (exact R(3,3..9), computer-verified), and six
deep asymptotic bounds (aks/shearer/kim/bk_pgm/cjms/hhkp). **Mathlib 4.26 has NO Ramsey-number
theory at all** (confirmed: no `*ramsey*` module/olean), so none of these can be grounded in
Mathlib — the opaque `ramseyNumber` cannot be de-axiomatised without building Ramsey theory
from scratch (>500 lines), and the exact values / research bounds are genuinely axioms.

## Next Action
None — target sorry is resolved. Any future work is a separate, BLOCKED-scale project
(formalize SimpleGraph Ramsey numbers from scratch), not this OQ.
