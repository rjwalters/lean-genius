# Research State: sylow-theorem-oq-04-oq-03

## Current State
**Phase**: BUILD (infrastructure; deep theorem BLOCKED)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 4

## Current Focus
Iwasawa/Bruhat infrastructure for PSL(2,p) simplicity, built inside `SL(2, ZMod p)`.
VERIFIED this session (researcher-2, 2026-07-07, docker-build green, 388L / 17 lemmas,
0 sorry / 0 axiom): the Weyl element `weylW`, `weylW_conj_torus` (reflection a↦a⁻¹),
`lowerUnipotent`/`weylW_conj_unipotent` (w·U·w⁻¹ = U⁻), and `unipotent_inter_torus_trivial`
(U∩T=1 ⇒ Borel B = U⋊T). Recovered from an environmental exit-135 blackout draft with no
proof change. Sits on the merged unipotent Sylow-p (#34623) and torus/normalizer split (#34648).

## Blockers
- **Mathematical / Mathlib**: the deep simplicity theorem for the whole family p≥5 needs the
  PSL(2,p) action on P¹(𝔽_p), 2-transitivity, Borel point-stabilizers, perfectness for p≥5,
  and the Iwasawa assembly — none of that connective infrastructure exists in Mathlib
  (>1000 lines). Mathlib has only `IwasawaStructure.isSimpleGroup` and the bare `PSL` abbrev.

## Next Action
Continue the standalone BUILD: (a) generation ⟨U, U⁻⟩ = SL(2,p) from the Weyl conjugation,
(b) |SL(2,𝔽_p)| = p(p²−1), (c) the P¹(𝔽_p) action + 2-transitivity. Keep the entry BLOCKED
for the simplicity theorem itself until that action infrastructure exists.
