# S18c-orbit-precursor — Sign-Flip Stabilizer Cardinality

**Iteration**: S18c-orbit-precursor (Part 31)
**Author**: researcher-11
**Date**: 2026-05-12
**File**: `proofs/Proofs/FourSquareDistributionOQ01.lean`
**Net change**: lineCount 2652 → 2723 (+71); theoremCount 144 → 145
(+1); sorry count 0 → 0; axiom count 1 → 1.

## Goal

Prove the sign-flip stabilizer cardinality formula needed by the
deferred S18c-orbit cardinality argument
(`orbitCard_dvd_eight_of_pos_target_decl`).

For any `v : Fin 4 → ℤ`:

  `|{ s : SignFlip // applyFlip s v = v }| =
     2 ^ |{ i : Fin 4 | v i = 0 }|`.

## Lemma statement

```
lemma signFlipStabilizer_card (v : Fin 4 → ℤ) :
    Fintype.card { s : SignFlip // applyFlip s v = v } =
      2 ^ (Finset.univ.filter (fun i : Fin 4 => v i = 0)).card
```

## Proof sketch

The stabilizer of `v` is `{ s : SignFlip | ∀ i, s i = true → v i = 0 }`
(by `applyFlip_eq_iff`, Part 29). The key observation: a sign-flip
`s` is in the stabilizer iff `s i = false` at every nonzero coord;
at zero coords, `s i` is unconstrained.

Therefore `Stab v ≃ ({ i : Fin 4 // v i = 0 } → Bool)`: restrict `s`
to its values on zero coords (forward) and extend by `false` on
nonzero coords (inverse). The proof builds the explicit equivalence
and counts cardinality via `Fintype.card_fun`, `Fintype.card_bool`,
`Fintype.card_subtype`.

## Use in S18c-orbit argument

Combined with the orbit-stabilizer theorem
`MulAction.orbit_card_dvd_of_finite` and `Fintype.card SignFlip = 16`
(Part 29), this yields the sign-flip orbit cardinality:

  `|Orbit_(ℤ/2)⁴ v| = 16 / 2^k = 2^(4-k) = 2^(# nonzero coords)`.

For solutions to `sumSq v = n` with `n > 0`, at least one coord is
nonzero, so the sign-flip orbit has cardinality ≥ 2. The full
8-divisibility target requires combining this with the
permutation-side orbit count (forthcoming) and a case analysis on
the zero/coincidence pattern of `(|v 0|, |v 1|, |v 2|, |v 3|)`.

## Spec reference

`s18-eight-divisibility-spec.md §3.8`, "(ℤ/2)⁴ ⋊ S₄ orbit decomposition".

## Build status

**Build pending verification.** Local Docker build attempted with
`./proofs/scripts/docker-build.sh Proofs.FourSquareDistributionOQ01`;
once the second-attempt iteration of the `Equiv` proof landed, this
note will be updated with the final outcome.

Mathlib API references (verified at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Symbol | File | Purpose |
|--------|------|---------|
| `Fintype.card_fun` | `Mathlib.Data.Fintype.Pi` | `Fintype.card (α → β) = card β ^ card α` |
| `Fintype.card_bool` | `Mathlib.Data.Fintype.Basic` | `Fintype.card Bool = 2` |
| `Fintype.card_subtype` | `Mathlib.Data.Fintype.Card` | `Fintype.card {x // p x} = (filter p).card` |
| `Bool.eq_false_or_eq_true` | `Init.SimpLemmas` | `∀ (b : Bool), b = false ∨ b = true` |

## Next step

S18c-orbit: invoke `MulAction.orbit_card_dvd_of_finite` (Mathlib
v4.26.0) and case-analyse on the zero/coincidence pattern of `v` to
conclude `8 ∣ |Orbit_{(ℤ/2)⁴ ⋊ S₄} v|` for every `v ∈ solSet n` when
`n > 0`. Requires a permutation-side stabilizer count (`Stab_S₄ v` as
a function of the multiplicity pattern of `(|v 0|, |v 1|, |v 2|,
|v 3|)`) which is the natural next precursor; the present
`signFlipStabilizer_card` is the (ℤ/2)⁴-side half.
