# abundant-number-oq-01 — gallery draft

Staging area for the gallery entry of `proofs/Proofs/AbundantNumberOQ01.lean`.

**Held here (not in `src/data/proofs/`) until the Docker build confirms the proof.**
Promoting before a green build would create a false-green gallery entry.

## Result

Mathlib defines `Nat.Abundant` and proves `infinite_deficient`, but records nothing about
abundance under multiplication. This entry adds (0 sorries, 0 axioms):

- `Nat.Abundant.mul_left` — every positive multiple of an abundant number is abundant.
- `Nat.Perfect.mul_left_abundant` — every proper multiple of a perfect number is abundant.
- `Nat.infinite_abundant`, `Nat.infinite_even_abundant` — infinitely many abundant numbers.

Engine: the divisor-injection bound `k·σ₁(n) ≤ σ₁(k·n)` (`d ↦ k·d`), strict when `2 ≤ k`.

## Promotion checklist (after green build)

1. `./proofs/scripts/docker-build.sh Proofs.AbundantNumberOQ01` succeeds.
2. Register the file in the Proofs import aggregator if gallery requires it.
3. `cp -r gallery-draft/* src/data/proofs/abundant-number-oq-01/` and `pnpm build` to validate.
