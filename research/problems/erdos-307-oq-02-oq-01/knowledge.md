# erdos-307-oq-02-oq-01 — Prove prime_sets_disjoint via p-adic valuation

**Status:** COMPLETED (0 sorries, 0 axioms — verified via `lake env lean`, Docker down)

## Problem

Discharge the `prime_sets_disjoint` sorry documented in `Erdos307OQ02.lean`:
if `P, Q` are finite sets of primes with `(Σ_{p∈P} 1/p)(Σ_{q∈Q} 1/q) = 1`,
then `P ∩ Q = ∅`. Parent flagged it as "requires Mathlib's p-adic valuation theory".

## Session 2026-06-27 (Session 1) — COMPLETED

**Mode:** FRESH
**Outcome:** completed (theorem fully proved, axiom-free)

### What I Did
- Recognized the p-adic content `v_{p₀}(Σ 1/p) = -1` can be captured elementarily
  without `padicValRat`, as a single reduction mod `p₀` in the field `𝔽_{p₀}`.
- Wrote `proofs/Proofs/Erdos307OQ02OQ01.lean` (171 lines, 5 defs, 4 lemmas/theorems):
  - `reciprocalSum_mul_denom`: `(Σ 1/p)·(∏ p) = Σ_p ∏_{q≠p} q` over ℚ (via `Finset.mul_prod_erase`, `inv_mul_cancel_left₀`).
  - `primeNumer_mul_eq`: clears denominators in the product-1 hypothesis to the
    INTEGER identity `NP·NQ = DP·DQ` (cast down via `exact_mod_cast`).
  - `prime_not_dvd_primeNumer`: the p-adic core — `p₀ ∤ NP` for prime `p₀ ∈ P`,
    by reducing `NP` in `ZMod p₀`: non-`p₀` summands carry the factor `p₀` and
    vanish (`Finset.prod_eq_zero` + `ZMod.natCast_self`); survivor `∏_{q≠p₀} q`
    is a product of units (`Finset.prod_ne_zero_iff` + `ZMod.natCast_eq_zero_iff`
    + `Nat.prime_dvd_prime_iff_eq`).
  - `prime_sets_disjoint`: a shared prime `p₀` divides `DP·DQ` but neither `NP`
    nor `NQ`, contradicting `NP·NQ = DP·DQ`.
- Registered in `proofs/Proofs.lean`; added gallery entry `src/data/proofs/erdos-307-oq-02-oq-01/`.

### Key Findings
- The valuation fact `v_{p₀}(Σ_{p∈P} 1/p) = -1` ⟺ "`p₀ ∤ NP`", a one-line modular reduction.
- Clearing denominators turns the ℚ-hypothesis into a clean ℕ-identity, sidestepping
  rational arithmetic entirely for the divisibility contradiction.
- The argument needs no size/structure assumptions beyond primality — works for all finite prime sets.

### Files Modified
- `proofs/Proofs/Erdos307OQ02OQ01.lean` (new)
- `proofs/Proofs.lean` (import)
- `src/data/proofs/erdos-307-oq-02-oq-01/meta.json` (new)

### Verification
- Docker build blocked (containerd `meta.db` I/O error). Verified via main-repo
  Mathlib `.olean` cache: `lake env lean` EXIT 0, no warnings.
- `#print axioms prime_sets_disjoint` → `[propext, Classical.choice, Quot.sound]`
  (no `sorryAx`, no `Lean.ofReduceBool`).

### Next Steps
- Remaining parent sorry `prime_set_size_lower_bound` (|P ∪ Q| ≥ 60) needs a
  verified Mertens-type bound on `Σ_{p≤281} 1/p ≈ 2.009` — independent of this work.
