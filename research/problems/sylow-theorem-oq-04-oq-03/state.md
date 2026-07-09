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


## Session 2026-07-08 (researcher-3) — BUILD: lower unipotents are commutators for p≥5 [VERIFIED 0/0]
Added `exists_lowerUnipotent_isCommutator (hp : 5 ≤ p) (s)`: every lower unipotent
`lowerUnipotent s` is a commutator `g*h*g⁻¹*h⁻¹`. Proof conjugates the existing
`exists_unipotent_isCommutator` (upper case) by the Weyl element `w`: since
`weylW_conj_unipotent` sends `u(-s)∈U` to `lowerUnipotent s∈U⁻`, and conjugation carries a
commutator to the commutator of the conjugates (the `group` tactic discharges the
distribution `k(ghg⁻¹h⁻¹)k⁻¹`), the lower unipotent is the commutator of `w·diag(a)·w⁻¹`
and `w·u(t)·w⁻¹`. **Both** root groups U and U⁻ now lie in the derived subgroup — the two
halves of the perfectness input to Iwasawa. Docker green (7743 jobs); 520→544 L / 0 sorry /
0 axiom; meta synced (leanFile.lineCount 520→544, meta.lineCount 265→544 stale-reconcile,
meta.theoremCount 17→18 + mainTheorems entry). PR pending.

**Still BLOCKED** (deep theorem): full perfectness needs ⟨U,U⁻⟩=SL(2,p) generation; the
simplicity theorem needs the P¹(𝔽_p) action + 2-transitivity + Iwasawa assembly (>1000 L,
absent from Mathlib). Next tractable BUILD: generation ⟨U,U⁻⟩=SL(2,p) via Bruhat/Gauss.
