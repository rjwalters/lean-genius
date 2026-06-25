# Knowledge: abel-ruffini-oq-06

## Summary

The Abel–Ruffini theorem: the general polynomial equation of degree `n ≥ 5` is
not solvable by radicals. The proof factors into (a) a group-theoretic fact —
`Sₙ` is solvable iff `n ≤ 4` — and (b) Galois' criterion — solvable by radicals
iff the Galois group is solvable.

## What is formalized (researcher-9, 2026-06-25)

`proofs/Proofs/AbelRuffiniObstructionOQ06.lean`, namespace
`AbelRuffiniObstructionOQ06`, 0 axioms / 0 sorries:

| Theorem | Statement |
|---|---|
| `symmetricGroup_not_solvable` | `5 ≤ n → ¬IsSolvable (Equiv.Perm (Fin n))` |
| `perm_fin_two_solvable` | `IsSolvable (Equiv.Perm (Fin 2))` |
| `symmetric_threshold` | `S₂` solvable ∧ `Sₙ` unsolvable for all `n ≥ 5` |
| `not_solvableByRad_of_not_solvable_gal` | irreducible `q`, `q(α)=0`, `¬IsSolvable q.Gal` ⇒ `¬IsSolvableByRad F α` |
| `solvable_gal_of_solvableByRad` | converse (= `solvableByRad.isSolvable'`) |

## Key Mathlib facts used

- `Equiv.Perm.not_solvable (X) (5 ≤ #X) : ¬IsSolvable (Equiv.Perm X)` — the
  cardinal-indexed non-solvability; the `Fin n` version follows by `Cardinal.mk_fin`.
- `Equiv.Perm.fin_5_not_solvable` — the `n = 5` base case (uses that `A₅` is its
  own commutator subgroup).
- `isSolvable_of_comm` — abelian ⇒ solvable.
- `solvableByRad.isSolvable'` (Mathlib/FieldTheory/AbelRuffini.lean) — the Galois
  direction; our criterion is its contrapositive.

## Gaps / what Mathlib does NOT provide

- No lemma giving `IsSolvable (Equiv.Perm (Fin n))` for `n ∈ {3,4}` (positive
  direction of the threshold). Would need an explicit derived-series argument
  `S₄ ⊳ A₄ ⊳ V₄ ⊳ 1`. Only the abelian endpoint `S₂` is done here.
- No packaged concrete unsolvable quintic. `prime_degree_dvd_card` gives the
  divisibility, but counting exactly two non-real roots of e.g. `x⁵−4x+2` (to
  force complex conjugation as a transposition, hence `Gal ≅ S₅`) is not in
  Mathlib — that real-analysis step is the missing piece.

## Scope note

This is the **characteristic-independent** core. The problem title's
"characteristic-dependent / Abhyankar conjecture" angle refers to the deep
positive-characteristic theory of fundamental groups of curves
(Raynaud 1994 / Harbater 1994) — out of scope and unformalized.

## Approaches Tried

- Tried to anchor on a concrete quintic — blocked by missing real-root-count
  machinery in Mathlib.
- Settled on the uniform `n ≥ 5` non-solvability + abstract radical criterion,
  which are certain to compile and capture the genuine mathematical obstruction.
