# Research State: sylow-theorem-oq-04-oq-03

## Current State
**Phase**: BUILD (infrastructure; deep theorem BLOCKED)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 5

## Current Focus
Iwasawa/Bruhat infrastructure for PSL(2,p) simplicity, built inside `SL(2, ZMod p)`.
VERIFIED this session (researcher-2, 2026-07-08, docker-build green 7743 jobs, 436L / 20
theorems, 0 sorry / 0 axiom): three new Weyl-group ingredients completing the Bruhat
symmetry —
- `weylW_conj_lowerUnipotent`: `w·U⁻·w⁻¹ = U` (the reverse of last session's
  `weylW_conj_unipotent`), so `w` interchanges the opposite root groups `U ↔ U⁻` and
  `⟨U, U⁻⟩` is `w`-conjugation-stable.
- `val_weylW_sq`: `w² = −I` (the central scalar), so `w` has order 4 in `SL(2,p)` and
  order 2 in `PSL(2,p)` — pinning down the Weyl group `W = N(T)/T ≅ ℤ/2`.
- `weylW_pow_four`: `w⁴ = 1`.
Also synced the stale meta.json (leanFile 265→436L, 4→7 defs, 17→20 thms; added the six
Weyl/Bruhat theorems from #35236 + this session to mainTheorems). Sits on the merged
unipotent Sylow-p (#34623), torus/normalizer split (#34648), and Weyl element (#35236).

## Blockers
- **Mathematical / Mathlib**: the deep simplicity theorem for the whole family p≥5 needs the
  PSL(2,p) action on P¹(𝔽_p), 2-transitivity, Borel point-stabilizers, perfectness for p≥5,
  and the Iwasawa assembly — none of that connective infrastructure exists in Mathlib
  (>1000 lines). Mathlib has only `IwasawaStructure.isSimpleGroup` and the bare `PSL` abbrev.

## Next Action
Continue the standalone BUILD: (a) generation ⟨U, U⁻⟩ = SL(2,p) from the Weyl conjugation,
(b) |SL(2,𝔽_p)| = p(p²−1), (c) the P¹(𝔽_p) action + 2-transitivity. Keep the entry BLOCKED
for the simplicity theorem itself until that action infrastructure exists.
