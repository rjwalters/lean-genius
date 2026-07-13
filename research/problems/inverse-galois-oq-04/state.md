# Current State

**Phase**: ACT
**Since**: 2026-07-02T11:48:15-07:00
**Iteration**: 5

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

## Session 4 addition (researcher-8, VERIFIED 0-axiom)

`DedekindInertiaTower.lean`: packaged the abstract inertia-tower + Galois-uniformity
step as `inertiaDeg_dvd_inertiaDegIn` (over a tower `R ⊆ S ⊆ T`, `T/R` Galois:
`inertiaDeg p P ∣ inertiaDegIn p T`) plus its reduction form
`dvd_inertiaDegIn_of_dvd_inertiaDeg`. Combines `Ideal.inertiaDeg_algebra_tower`
(multiplicativity, no Galois on the non-normal middle ring) and
`Ideal.inertiaDegIn_eq_inertiaDeg` (Galois uniformity). This covers **steps 2 & 3**
of the residual route below.

## Session 5 addition (researcher-5, BUILD-PENDING — host-disk docker block)

`DedekindInertiaFactor.lean`: packaged **Step 1** (Kummer–Dedekind factor brick) as the
companion to Session 4's tower brick. `exists_dvd_inertiaDeg` turns a degree-`d` monic
irreducible factor of `minpoly θ mod p` (given `¬ p ∣ exponent θ`) into a maximal prime `P`
over `(p)` with `d ∣ inertiaDeg (p) P` — exactly the input of
`DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg`. Written but NOT yet machine-verified:
the docker build failed on infrastructure (host disk at 100 %, curl/containerd I/O error), not
on any Lean error. Needs a clean `#print axioms` before it can be called VERIFIED.

With all three steps now abstract bricks, the sole residual obligation is `¬ 7 ∣ exponent α`
(conductor of `ℤ[α]` coprime to `7`, true since `q mod 7` is squarefree ⟺ `7 ∤ disc q`). A full
Mathlib v4.26 inventory confirms the **Dedekind criterion** that would discharge this is ABSENT
(no discriminant–index relation, no `p ∤ disc ⟹ ¬p∣exponent`, no p-maximality). Filling it is
> 1000 lines of foundational theory → BLOCKED on a genuine Mathlib gap.

## Blockers

The remaining gap is **not** Dedekind's theorem in the abstract (that bridge,
`DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn`, is proved 0-axiom), and
is **no longer** the inertia-tower multiplicativity / Galois-uniformity steps (packaged
this session, 0-axiom). What remains is the single Kummer–Dedekind conductor step:
exhibit one prime `P` of `𝓞 ℚ(α)` over `(7)` with `3 ∣ inertiaDeg (7) P` — the prime
matching the irreducible cubic factor of `q mod 7` — via
`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply` (conductor coprime to 7 since
`7 ∤ disc q = 32000²`). Feeding that prime into
`DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg` then yields
`3 ∣ Ideal.inertiaDegIn (7) (𝓞 q.SplittingField)`.

## Next Action

Multi-session: prove Step 1 (KummerDedekind conductor step) to produce the intermediate
prime `P` with `3 ∣ inertiaDeg (7) P`, feed it through
`DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg`, then into
`InverseGaloisA5DedekindInstantiation.three_dvd_gal_card_of_bridge`. Alternatively park
the residual step until Mathlib exposes the factorization–inertia correspondence directly.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 2
- Approaches tried: 3 (assess-and-document; arithmetic-keystone formalization; inertia-tower brick)
