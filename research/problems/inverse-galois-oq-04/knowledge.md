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
