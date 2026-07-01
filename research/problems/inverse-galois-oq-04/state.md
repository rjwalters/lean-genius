# Current State

**Phase**: PARTIAL (arithmetic keystone formalized; residual = inertia-degree bridge)
**Since**: 2026-07-01
**Iteration**: 3

## Current Focus

Eliminate `three_dvd_gal_card : 3 ∣ Fintype.card q.Gal` in InverseGaloisA5.lean
via Dedekind's theorem at p = 7. The abstract Dedekind–Frobenius bridge and its
A₅ instantiation already exist (0-axiom); what remains is a concrete inertia
computation over `𝓞 q.SplittingField`.

## Active Approach

`InverseGaloisA5DedekindMod7.lean` (this session, VERIFIED 0-axiom): formalized
the concrete arithmetic keystone Dedekind consumes at `p = 7`:

```
q ≡ (X − 5)(X − 6)(X³ + 6X² + 4X + 1)   (mod 7),   cubic irreducible over 𝔽₇.
```

i.e. Frobenius cycle type `(1, 1, 3)`. Proof route: an integer identity
`qInt = (X−5)(X−6)(cubic) + 7·R` (closed by `ring`), mapped to `ZMod 7` (the `7·R`
term vanishes since `char (ZMod 7)[X] = 7`); cubic irreducibility from
`irreducible_of_degree_le_three_of_not_isRoot` + an exhaustive `decide` over the 7
residues.

## Blockers

The remaining gap is **not** Dedekind's theorem in the abstract (that bridge,
`DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn`, is proved 0-axiom).
It is the concrete number-field inertia fact
`3 ∣ Ideal.inertiaDegIn (7) (𝓞 q.SplittingField)`, which still needs the
Kummer–Dedekind conductor step
(`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`, using `7 ∤ disc q =
32000²`), the inertia-tower multiplicativity, and `inertiaDegIn_eq_inertiaDeg`
(Galois). This is the `~800–1500`-line multi-session bridge; the arithmetic input
it consumes is now machine-checked.

## Next Action

Multi-session: connect `qInt_map_zmod7` / `cubic7_irreducible` to
`3 ∣ inertiaDegIn (7)` via KummerDedekind, then feed
`InverseGaloisA5DedekindInstantiation.three_dvd_gal_card_of_bridge`. Alternatively
park the residual bridge until Mathlib exposes Dedekind's factorization–inertia
correspondence directly.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 2 (assess-and-document; arithmetic-keystone formalization)
