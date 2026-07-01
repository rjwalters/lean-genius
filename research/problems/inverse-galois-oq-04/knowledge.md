# Knowledge: Dedekind Theorem to Eliminate A5 Axiom (inverse-galois-oq-04)

## Goal

Eliminate the single remaining axiom in `proofs/Proofs/InverseGaloisA5.lean`:

```lean
axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal
```

where `q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5` (translate of X⁵ + 20X + 16,
Galois group A₅). This is the "Axiom B" of the file, intended to be discharged
by **Dedekind's theorem** applied at p = 7.

## Session 1 (researcher-3, 2026-06-28): ASSESSED → BLOCKED on infrastructure

### State of the proof

The file is mature: exactly **1 axiom** (`three_dvd_gal_card`), 0 sorries.
Everything else needed for |Gal(q)| = 60 is already proved:
- `five_dvd_gal_card` : 5 ∣ |Gal| (irreducibility, Eisenstein at 5)
- `gal_card_dvd_60_proved` : |Gal| ∣ 60 (Vandermonde/discriminant ⇒ Gal ⊆ A₅;
  this is the *former* Axiom A, now a theorem — Part XIV)
- `gal_card_ne_15`, `gal_card_ne_30` : exclude orders 15, 30 (Sylow + A₅ simplicity)
- `vandermondeProduct_sq_eq_proved` : Δ² = disc (former axiom, now proved — Part XV)

`q_gal_card` (|Gal| = 60) is then: 15 ∣ |Gal| (= 3·5 dvd) ∧ |Gal| ∣ 60 ∧ ≠15 ∧ ≠30
⇒ |Gal| = 60. The ONLY input still axiomatized is `3 ∣ |Gal|`.

### Why 3 ∣ |Gal| has no axiom-free shortcut for this polynomial

With the proved facts, Gal is a transitive subgroup of A₅ on 5 points, so
|Gal| ∈ {5, 10, 60} (C₅, D₅, A₅; F₂₀ ⊄ A₅). Distinguishing D₅ (order 10) from
A₅ (order 60) is *exactly* the question of whether Gal contains an order-3
element. There is no computational route: Gal lives over the splitting field of
q (a degree-60 number field), not a decidable finite structure, so `native_decide`
cannot reach it. Detecting the 3-cycle requires one of:
  (a) Dedekind's theorem at p=7 (q mod 7 = (X-5)(X-6)(irred cubic) ⇒ (1,1,3)
      cycle type ⇒ order-3 element), or
  (b) Dummit's resolvent-sextic correspondence (R₆ has no rational root ⇒ not D₅).
Both are absent from Mathlib.

### Mathlib gap (surveyed Mathlib 4.26.0)

Dedekind's theorem — "factorization type of f mod p (p ∤ disc) = cycle type of
Frobenius in Gal acting on roots" — is **entirely absent**. There is no
Frobenius-element-as-Galois-permutation primitive. Building blocks that exist:
- `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`
  (ideal factorization ↔ min-poly factors mod p)
- `Ideal.inertiaDeg` / `ramificationIdx`, `Ideal.card_inertia_eq_ramificationIdxIn`,
  `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`
  (RamificationInertia/Galois.lean)
- `Polynomial.Gal.galActionHom` (+ `_injective`) — faithful action on rootSet
- `Equiv.Perm.cycleType`, `lcm_cycleType` (= orderOf)

Missing bridge: define the Frobenius automorphism at an unramified prime
P | (7), show it induces the residue-field Frobenius, and prove its cycle type
on the roots = the inertia-degree multiset = the mod-7 factorization degrees.
**Estimate: 800–1500 lines of foundational number theory.** This exceeds the
BUILD threshold (<500 lines) and a single session.

### What this session did

- Confirmed exactly 1 axiom remains; verified the downstream proof chain.
- Fixed a stale docstring on `q_gal_card` (claimed "2 axioms"; vandermonde was
  already eliminated) — comment-only.
- Replaced the vague "What's Missing in Mathlib" roadmap with a concrete,
  citeable Mathlib bridge plan (KummerDedekind + RamificationInertia/Galois +
  galActionHom + cycleType) and the 800–1500-line estimate — comment-only.
- All Lean edits are comments; no proof terms touched, compilation unaffected.

### Classification: BLOCKED (needs >1000 lines foundational Mathlib work)

Recommend parking until Mathlib gains Dedekind's theorem / Frobenius-as-Galois-
automorphism, or until a dedicated multi-session effort builds the bridge here.
The gallery entry `inverse-galois-a5` is already correctly `axiomatized` /
badge `axiom` / axiomCount 1 with an accurate `assumptions` note — no gallery
change needed.

## Session 2 (researcher-7, 2026-06-30): RE-CONFIRMED BLOCKED

Re-surveyed Mathlib 4.26.0 (bundled in this worktree): still **no**
Frobenius-element-as-Galois-permutation primitive and **no** Dedekind
factorization↔cycle-type theorem (`grep` for `frobenius` in Galois/number-theory
files and for `cycleType.*Frobenius` both empty). The ~800–1500-line foundational
gap identified in Session 1 is unchanged, so there is no axiom-free single-session
route to discharge `three_dvd_gal_card`.

Note for a future attempt: the *arithmetic* input Dedekind would consume IS
verifiable in isolation — q mod 7 = X⁵+2X⁴+3X³+4X²+4X+2 over 𝔽₇ splits as
(X-5)(X-6)·(irreducible cubic); the cubic's irreducibility reduces to "no root in
ZMod 7" (degree 3), which is `decide`-able. But this fact cannot be connected to
|Gal| without the missing Frobenius/Dedekind bridge, so on its own it does not
advance OQ-04. Recommend deprioritize until that bridge lands in Mathlib.

## Session 3 (researcher-8, 2026-07-01): FORMALIZED the arithmetic keystone (VERIFIED 0-axiom)

Acted on Session 2's note: the mod-7 factorization datum Dedekind consumes is now
machine-checked in `proofs/Proofs/InverseGaloisA5DedekindMod7.lean` (0 axioms — only
`propext` / `Classical.choice` / `Quot.sound`; no `sorry`, no `native_decide`).

Contents:
- `qInt` : the ℤ model of `q` (same coefficients), with `qInt_map_rat` proving it
  casts to `InverseGaloisA5.q` over ℚ.
- `qInt_eq_factor_add_seven` : the ℤ[X] identity
  `qInt = (X−5)(X−6)(X³+6X²+4X+1) + 7·(6X³−21X²−12X−5)` (closed by `ring`).
- `qInt_map_zmod7` : **`q ≡ (X−5)(X−6)·cubic7 (mod 7)`** — obtained by mapping the
  ℤ identity to `ZMod 7`; the `7·R` term dies because `(7 : (ZMod 7)[X]) = 0`
  (`CharP.cast_eq_zero` via `Polynomial.instCharP`).
- `cubic7_irreducible` : `X³ + 6X² + 4X + 1` is irreducible over `𝔽₇`, via
  `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` + `cubic7_no_root`
  (an exhaustive `decide` over the 7 residues; `cubic7_natDegree` via `compute_degree!`).

So Frobenius cycle type `(1, 1, 3)` at `p = 7` is now a verified fact rather than a
hand computation.

### Key Lean recipes (reusable)
- **Factorization mod p, robustly**: prove the identity over `ℤ[X]` as
  `poly = factors + p · R` (fully closed by `ring`, no characteristic reasoning), then
  `Polynomial.map` to `ZMod p`; the `p · R` term vanishes via
  `(p : (ZMod p)[X]) = 0` = `CharP.cast_eq_zero _ p` (needs `Nat.cast_ofNat` to align
  the `OfNat` numeral) + `Polynomial.instCharP`. Avoids all `ring`-in-char-p pitfalls.
- **Cubic irreducibility over a finite field**: `irreducible_of_degree_le_three_of_not_isRoot`
  (`Mathlib/Algebra/Polynomial/SpecificDegree.lean`) with `natDegree ∈ Finset.Icc 1 3`
  and `∀ x, ¬ IsRoot`; discharge no-roots by `simp only [def, eval_add, eval_mul,
  eval_pow, eval_X, eval_ofNat, eval_one]` then `revert x; decide` (kernel `decide`,
  not `native_decide`, so axiom-clean).
- `C n` ↔ numeral: `Polynomial.C_ofNat` / `map_ofNat` in the simp set.

### Residual gap (unchanged in size, but the arithmetic input is now closed)
Still needs, over `𝓞 q.SplittingField`:
`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply` (KummerDedekind; conductor
coprime to 7 since `7 ∤ disc q = 32000²`) → inertia degree 3 at the cubic's prime →
inertia-tower multiplicativity → `inertiaDegIn_eq_inertiaDeg` (Galois) →
`3 ∣ inertiaDegIn (7) (𝓞 q.SplittingField)` → feed
`InverseGaloisA5DedekindInstantiation.three_dvd_gal_card_of_bridge`. This file does
**not** remove `three_dvd_gal_card`; it verifies and pins the arithmetic datum the
remaining ~hundreds-of-lines KummerDedekind bridge will consume. Gallery entry
`inverse-galois-a5` remains correctly `axiomatized` (axiomCount 1) — no gallery change.

## Session 4 (researcher-8, 2026-07-01): PACKAGED the inertia-tower + Galois-uniformity brick (VERIFIED 0-axiom)

New file `proofs/Proofs/DedekindInertiaTower.lean` isolates **steps 2 and 3** of the
Session-3 residual gap as a single abstract, reusable, 0-axiom lemma (only
`propext` / `Classical.choice` / `Quot.sound`; no `sorry`, no `native_decide`).

- `DedekindInertiaTower.inertiaDeg_dvd_inertiaDegIn` : in a tower of commutative rings
  `R ⊆ S ⊆ T` with `T / R` Galois (Galois group `G`, `[IsGaloisGroup G R T]`), for
  maximal ideals `p ◁ R`, `P ◁ S` over `p`, `Q ◁ T` over `P`,
  `Ideal.inertiaDeg p P ∣ Ideal.inertiaDegIn p T`.
- `DedekindInertiaTower.dvd_inertiaDegIn_of_dvd_inertiaDeg` : reduction form — to get
  `d ∣ inertiaDegIn p T` it suffices to exhibit *one* intermediate prime `P` with
  `d ∣ inertiaDeg p P`. This is exactly the shape the A₅ argument consumes.

Proof packages two existing Mathlib facts:
- `Ideal.inertiaDeg_algebra_tower p P Q : inertiaDeg p Q = inertiaDeg p P * inertiaDeg P Q`
  — multiplicativity in the tower, needing **no** Galois hypothesis on the non-normal
  middle field `S = ℚ(α)`;
- `Ideal.inertiaDegIn_eq_inertiaDeg p Q G : inertiaDegIn p T = inertiaDeg p Q`
  — Galois uniformity: all primes of the top field `T` over `p` share one inertia degree.
Then `inertiaDeg p P ∣ inertiaDeg p P * inertiaDeg P Q = inertiaDeg p Q = inertiaDegIn p T`.
The transitivity instance `Q.LiesOver p` is supplied by `Ideal.LiesOver.trans Q P p`.

### Effect on the residual gap
Applied with `R = ℤ`, `S = 𝓞 ℚ(α)`, `T = 𝓞 q.SplittingField`, `G = q.Gal`, `p = (7)`,
`d = 3`, this collapses the three-step route to a **single** remaining obligation:

> **(Step 1, KummerDedekind only)** exhibit one prime `P` of `𝓞 ℚ(α)` over `(7)` with
> `3 ∣ Ideal.inertiaDeg (7) P` — i.e. the prime matching the irreducible cubic factor
> `cubic7` of `q mod 7` (Session 3), whose inertia degree is its degree, `3`.

Steps 2 (inertia-tower multiplicativity) and 3 (Galois uniformity) are now machine-checked
and packaged; only the KummerDedekind conductor step
(`inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`, using `7 ∤ disc q = 32000²`)
still stands between the verified arithmetic datum and `3 ∣ inertiaDegIn (7)`. This file
does **not** remove `three_dvd_gal_card`; gallery entry `inverse-galois-a5` stays
correctly `axiomatized` (axiomCount 1) — no gallery change.

### Key Lean recipe (reusable)
- **Tower inertia divisibility, abstractly**: for `d ∣ inertiaDegIn` reductions, use
  `Ideal.inertiaDeg_algebra_tower` (multiplicativity, no Galois needed on the middle
  ring) composed with `Ideal.inertiaDegIn_eq_inertiaDeg _ _ G` (Galois uniformity on the
  top ring), stated over an `[IsGaloisGroup G R T]` tower with `[IsScalarTower R S T]`
  and `LiesOver` instances chained by `Ideal.LiesOver.trans`. Keeps the middle field
  non-normal — the whole point for `ℚ(α) ⊂ splitting field`.
