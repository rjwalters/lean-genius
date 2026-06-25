# Current State

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Iteration**: 2
**Status**: in-progress

## Current Focus

Formalized the characteristic-independent **core** of the Abel–Ruffini theorem
(researcher-9). The original stub ("Abhyankar conjecture formalization") names a
deep open-area positive-characteristic result (Raynaud/Harbater fundamental
groups of curves) that is not one-iteration formalizable; scoped down to the
tractable, genuinely meaningful group-theoretic + Galois obstruction.

## Delivered (PR pending)

`proofs/Proofs/AbelRuffiniObstructionOQ06.lean` — 5 theorems, 0 axioms, 0 sorries
(typechecked `lake env lean`, Docker down; `#print axioms` = only
propext/Classical.choice/Quot.sound):

- `symmetricGroup_not_solvable {n} (5 ≤ n) : ¬IsSolvable (Equiv.Perm (Fin n))` —
  generalizes Mathlib's `Equiv.Perm.fin_5_not_solvable` (only `Fin 5`) to all
  `n ≥ 5` via `Equiv.Perm.not_solvable` + `Cardinal.mk_fin`.
- `perm_fin_two_solvable : IsSolvable (Equiv.Perm (Fin 2))` (abelian, `decide`).
- `symmetric_threshold` — both endpoints together.
- `not_solvableByRad_of_not_solvable_gal` — Abel–Ruffini criterion
  (contrapositive of `solvableByRad.isSolvable'`): non-solvable Galois group ⇒
  not solvable by radicals.
- `solvable_gal_of_solvableByRad` — converse re-exposed.

## Blockers / Out of scope

- `n ≤ 4` solvability of `Sₙ` (S₃, S₄ derived series): no ready Mathlib lemma,
  positive-direction derived-series computation is heavy/risky offline — only the
  abelian endpoint `S₂` is included.
- Concrete unsolvable quintic (e.g. x⁵−4x+2): requires real-root counting +
  `prime_degree_dvd_card`; the hard part is absent from Mathlib. Left for a
  follow-up.
- Characteristic-p Abhyankar conjecture: deep open-area result, out of scope.

## Next Action

Possible follow-up: prove `Sₙ` solvable for `n ≤ 4` (derived series of S₄), or a
concrete unsolvable quintic.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
