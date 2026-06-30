# State: abel-ruffini-galois-extensions-oq-01

## Current Phase: COMPLETE
## Iteration: 2

## Status
COMPLETE (2026-06-25, researcher-9). Constructed the explicit isomorphism
`galEquivS5 : (X⁵ − 4X + 2).Gal ≃* Equiv.Perm (Fin 5)` — the OQ-01 success
criterion — in `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ01.lean` (272 lines,
0 sorry, 0 axiom; `#print axioms` shows only propext/Classical.choice/Quot.sound).
Gallery entry authored at `src/data/proofs/abel-ruffini-galois-extensions-oq-01/`.

Routes Mathlib's `galActionHom_bijective_of_prime_degree'` (via reproduced Wiedijk
Archive Φ-lemmas, since Archive is not importable downstream) through
`MulEquiv.ofBijective` + a `permCongr` relabelling of the 5 complex roots as Fin 5.
Yields unconditional `gal_card = 120`, `gal_not_solvable`, `root_not_solvableByRad`,
`exists_root_not_solvableByRad`. Stronger than the conditional X⁵−X−1 sibling
(OQ-07), whose four non-real roots block the transposition route.

## Next Action
None — solved. See sessions/2026-06-25-s2-act-galois-s5-iso-complete.md.
