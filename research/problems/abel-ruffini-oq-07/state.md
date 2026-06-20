# Research State: abel-ruffini-oq-07

## Current State
**Phase**: FORMALIZE (instantiation blocked on a Mathlib gap)
**Path**: full
**Since**: 2026-06-19
**Iteration**: 4

## Current Focus
Promoted the now-proved generic order-6⟹swap infrastructure
(`orderOf_eq_six_pow_three_isSwap`, `gal_eq_top_of_five_dvd_and_order6`) from an
unregistered `*Aristotle.lean` scratch file to a registered gallery module
`AbelRuffiniOQ07Order6` (in `Proofs.lean`) so CI verifies it. Re-classified the blocker:
the abstract Dedekind–Frobenius bridge `orderOf_arithFrobAt_eq_inertiaDegIn` is **proved
and registered** (`DedekindFrobeniusBridge.lean`); the real remaining gap is the
**instantiation** — specifically `inertiaDegIn(2, 𝓞_{f.SplittingField}) = 6` from the
mod-2 factor type, which needs the **factorization↔inertia-degree correspondence**,
confirmed **ABSENT** from pinned Mathlib v4.26 (grep: 0 hits). Build not re-confirmed
(Docker unresponsive this session).

## Active Approach
Instantiate the proved abstract bridge at p=2 in `𝓞_{f.SplittingField}`; transport
`arithFrobAt ℤ f.Gal Q` through `galActionHom` into `Perm (Fin 5)`; feed
`gal_eq_top_of_five_dvd_and_order6`. Blocked on the missing factorization↔inertia lemma.

## Blockers
- Instantiation of the (now-proved) abstract bridge: `inertiaDegIn(2, 𝓞_K) = 6` from the
  mod-2 factor type needs the factorization↔inertia-degree correspondence, absent from
  Mathlib v4.26. Shared crux with `inverse-galois-a5-oq-01` (p=7, inertiaDegIn=3).

## Next Action
Build (or locate) the factorization↔inertiaDegIn lemma, then instantiate the abstract
bridge at p=2 and transport through `galActionHom` to obtain an order-6 element of
`f.Gal`, closing the entry unconditionally.

## History
- **S1 (OBSERVE/ORIENT, 2026-06-18):** scouted; corrected the false "3 real roots" claim
  (f has 1 real root ⟹ conjugation is even). Identified the Dedekind–Frobenius bridge as
  the blocker.
- **S2–S3 (FORMALIZE, 2026-06-18/19):** built the verified reduction `AbelRuffiniOQ07.lean`
  (0 sorry/0 axiom): irreducibility (Selmer), `5 ∣ |Gal|` unconditional, mod-2/mod-3
  factor-type lemmas, group-theoretic assembly with the transposition as a hypothesis.
- **r12 (2026-06-19):** isolated the blocker as the abstract lemma
  `orderOf_arithFrobAt_eq_inertiaDegIn`; submitted to Aristotle.
- **S4 (2026-06-19, researcher-1):** abstract bridge landed + registered; promoted the
  generic order-6 step to a registered module; re-classified blocker as the
  factorization↔inertiaDegIn Mathlib gap (this file).
