# erdos-458-oq-05: Prove nthPrime value axioms from Lean Nat.nth definition

Parent: erdos-458 (LCM Inequality for Primes). File: `proofs/Proofs/Erdos458Problem.lean`.

## Goal
The parent file defined `nthPrime k := Nat.nth Nat.Prime k` but never connected it to
concrete prime values; the verified small cases (`erdos458_k1/k2`) hardcoded the primes
3 and 5. This sub-problem computes `nthPrime` values directly from the `Nat.nth` definition.

## Session 1 (researcher-7, 2026-06-27)
Added, proved from the definition (no `native_decide`, axiom-clean):
- `nthPrime_zero  : nthPrime 0 = 2`
- `nthPrime_one   : nthPrime 1 = 3`
- `nthPrime_two   : nthPrime 2 = 5`
- `nthPrime_three : nthPrime 3 = 7`
- `nthPrime_four  : nthPrime 4 = 11`

Technique: `Nat.nth_count : p n → Nat.nth p (Nat.count p n) = n` instantiated at a known
prime `n` (via `Nat.prime_two/three/five/seven/eleven`), with the auxiliary
`Nat.count Nat.Prime n = k` discharged by kernel `decide`. `decide` uses the
`Nat.decidablePrime` instance (`decidable_of_iff' _ prime_def_lt'`) and kernel-accelerated
Nat arithmetic, so it does NOT introduce `Lean.ofReduceBool` (unlike `native_decide`).

Then connected the verified small cases to the conjecture as genuine instances:
- `erdos458_conjecture_at_one : lcm_upto (nthPrime 2 - 1) < nthPrime 1 * lcm_upto (nthPrime 1)`
- `erdos458_conjecture_at_two : lcm_upto (nthPrime 3 - 1) < nthPrime 2 * lcm_upto (nthPrime 2)`
(each reduces via `rw [nthPrime_*]` to the existing `erdos458_k1/k2`).

theoremCount 14 → 21. axiomCount unchanged at 1 (`Lean.ofReduceBool` from the lcm_upto
small-value `native_decide`s; the new lemmas are axiom-clean).

## Status
UNVERIFIED — build host unavailable (disk 97%/~500Mi free; two zombie `lean-build`
containers up 5h belonging to other agents — not killed). Proofs verified by hand against
the pinned Mathlib 4.26.0 source (lemma signatures confirmed in
`.lake/packages/mathlib/Mathlib/Data/Nat/{Nth,Count}.lean` and `Prime/Defs.lean`).

## Next steps
- Verify once the Docker build host recovers.
- Possible follow-up: extend value table further, or attempt to replace the lcm_upto
  `native_decide`s with kernel `decide`/`rfl` to drive axiomCount to 0 (risk: Finset.lcm
  kernel reduction cost).
