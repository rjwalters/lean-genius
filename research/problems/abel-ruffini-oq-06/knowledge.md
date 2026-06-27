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

## Session 2026-06-27 (researcher-8) — solvable side of the threshold

**Mode**: FRESH · **Outcome**: progress (verified, 0-axiom)

New file `proofs/Proofs/AbelRuffiniOQ06.lean`, namespace `AbelRuffiniOQ06`,
0 axioms / 0 sorries (single-file checked with `lake env lean`; `#print axioms`
shows only `propext`/`Classical.choice`/`Quot.sound`):

| Theorem | Statement |
|---|---|
| `permSolvable_of_alternatingSolvable` | `[IsSolvable (alternatingGroup (Fin n))] → IsSolvable (Equiv.Perm (Fin n))` |
| `alternatingFinThree_isSolvable` | `IsSolvable (alternatingGroup (Fin 3))` (order 3, cyclic) |
| `alternatingFinTwo_isSolvable` | `IsSolvable (alternatingGroup (Fin 2))` (trivial) |
| `permFinTwo_isSolvable` | `IsSolvable (Equiv.Perm (Fin 2))` |
| `permFinThree_isSolvable` | `IsSolvable (Equiv.Perm (Fin 3))` |

This **directly answers open question 2** of the sibling entry
`abel-ruffini-obstruction-oq-06` ("formalize solvability of S₃ and S₄"),
closing `n = 3` and reducing `n = 4` to a single fact.

### Key Mathlib facts used
- `solvable_of_ker_le_range` — solvability transfers across `1 → A → G → B` when
  `ker(g) ≤ range(f)` and `A`, `B` solvable. Used with `f = (Aₙ).subtype`,
  `g = Equiv.Perm.sign`, `B = ℤˣ` (abelian).
- `alternatingGroup_eq_sign_ker` : `alternatingGroup α = sign.ker`. The kernel
  hypothesis collapses to `Aₙ ≤ Aₙ` after `Subgroup.range_subtype`.
- `nat_card_alternatingGroup` : `Nat.card (Aₙ) = (Nat.card α)!/2` (note the RHS
  uses `Nat.card`, so chase with `Nat.card_eq_fintype_card, Fintype.card_fin`).
- `isCyclic_of_prime_card` (wants `Nat.card`, not `Fintype.card`!),
  `IsCyclic.commutative`, `isSolvable_of_comm`.

### Remaining gap — S₄ / A₄
`S₄ solvable ⟺ A₄ solvable` via the reduction. `A₄` (order 12) is solvable by
`A₄ ⊳ V₄ ⊳ 1` (Klein-four normal subgroup, quotient `ℤ/3`). Mathlib has no
`A₄`-solvable lemma and only a TODO toward `V₄ ⊴ A₄` in
`SpecificGroups/KleinFour.lean`. Isolated as a `sorry` in companion
`proofs/Proofs/AbelRuffiniOQ06Aristotle.lean` and submitted to Aristotle.

### Environment notes
- Docker build infeasible this session (daemon hung, `docker ps` → rc 124; disk
  ~84%). Verified via `LAKE_UNSAFE=1 lake env lean Proofs/AbelRuffiniOQ06.lean`
  (single-file elaboration against prebuilt Mathlib oleans — bounded memory,
  NOT `lake build`).
