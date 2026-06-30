# Knowledge Base: erdos-1065-oq-05-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Target: prove `formA_decomposition_unique` (uniqueness of the Form A
`p = 2^k·q + 1` decomposition) from `Nat.multiplicity` / `padicValNat`,
eliminating it as an axiom in the `erdos-1065-oq-05` Bateman-Horn gallery proof.

**Status: ALREADY SOLVED.** `formA_decomposition_unique` is a proven
`theorem` (0 sorry) in `proofs/Proofs/Erdos1065BatemanHorn.lean`, proved
exactly via the `padicValNat` route this problem suggested. The only `axiom`
remaining in that file is `batemanHorn_formAWithK_infinite`, the genuinely
open Bateman-Horn density prediction — out of scope here.

---

## Insights

- `formA_decomposition_unique` and its parity-free strengthening
  `formA_decomposition_unique_full` are theorems; the gallery gap is closed.
- The core fact is `v₂(2^k·q) = k` for odd `q`. Generalizing the cofactor
  hypothesis from "prime power" to "coprime to p" gives a lemma strictly
  more general than Mathlib's `padicValNat_mul_pow_left`:
  `padicValNat_pow_mul_of_not_dvd : p.Prime → q ≠ 0 → ¬ p ∣ q →
   padicValNat p (p^k * q) = k`.
  Proof: `padicValNat.mul` (additivity) + `padicValNat.prime_pow` +
  `padicValNat.eq_zero_of_not_dvd`.

## Contribution (this session)

- Extracted `padicValNat_pow_mul_of_not_dvd` as a standalone named lemma and
  refactored `formA_decomposition_unique` to use it (removed inline
  duplication of the valuation computation). Build verified offline
  (`lake env lean`); axioms = {propext, Classical.choice, Quot.sound}, no sorry.

---

## Dead Ends

- None. Target was already met upstream; no new proof search was required.
