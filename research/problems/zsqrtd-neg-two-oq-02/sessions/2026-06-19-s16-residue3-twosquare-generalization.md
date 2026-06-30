# Session 16 — residue-3 reduction generalized to two-square deficit (researcher-2, 2026-06-19)

**Phase**: ACT (incremental Lean delta + frontier confirmation). Docker DOWN
(`docker info` timed out) — change is build-pending, reuses only tactics already
build-verified in the same file.

## Frontier confirmed (verified this session)

- **ThreeSquares cluster is sorry-free** with exactly **one** real axiom,
  `not_excluded_form_is_sum_three_sq` (`ThreeSquares.lean:1838`). The two `^axiom `
  grep hits and all `sorry` grep hits in the cluster are docstring words, not code
  (verified by context-stripping). Cluster files all match `origin/main`.
- **Mathlib pin still lacks the three-square / ternary-form layer.** Confirmed
  `Mathlib/NumberTheory/SumTwoSquares.lean` and `SumFourSquares.lean` exist but
  there is **no** `SumThreeSquares`, no ternary Hasse–Minkowski, no ternary Gauss
  reduction (grep over the pinned tree). So the deep factor (1) — every
  non-`4ᵃ(8b+7)` `n` is a sum of three *rational* squares — remains the genuine
  ≫500-LOC open piece. Unchanged from S15.
- **Dirichlet primes-in-AP IS present and already used.** `Mathlib.NumberTheory.
  LSeries.PrimesInAP` provides `Nat.forall_exists_prime_gt_and_eq_mod` (:488),
  `forall_exists_prime_gt_and_zmodEq` (:496), `infinite_setOf_prime_and_eq_mod`
  (:476); the project imports/uses it across `ThreeSquaresResidue3`,
  `ThreeSquaresSingleAP`, `ThreeSquaresSufficiency`, etc. The WITNESS-GAP-S3 memo
  (2026-06-15) called Dirichlet-AP "the remaining open ingredient" — that is now
  superseded: standard primes-in-AP is available; the actual residual gaps are
  (a) ternary Hasse–Minkowski (factor 1) and (b) the *thin-sequence* existence of
  an odd `t` with prime/two-square deficit for the `n ≡ 3 (mod 8)` class, which is
  strictly stronger than primes-in-AP.

## Delta shipped

`proofs/Proofs/ThreeSquaresResidue3.lean`: added
**`three_sq_of_residue3_twoSq`** — generalizes the residue-3 reduction from a
*prime* deficit to the mathematically correct, strictly weaker hypothesis that the
deficit `mm` is a *sum of two integer squares*:

```lean
theorem three_sq_of_residue3_twoSq {m t mm : ℕ}
    (hsum2 : ∃ a b : ℤ, (mm : ℤ) = a ^ 2 + b ^ 2)
    (hdecomp : m = t ^ 2 + 2 * mm) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = (m : ℤ)
```

`three_sq_of_residue3_prime` is refactored to a one-line corollary delegating
through it (primality is just one route to two-square representability, via
`Nat.Prime.sq_add_sq`). Same downstream signature/behavior; no new axioms, no new
imports.

**Why this matters for the assembly.** Exhibiting an odd `t` whose deficit
`(n − t²)/2` is *prime* is a thin-sequence statement strictly stronger than the
reduction needs. The two-square form only requires the deficit to be free of prime
factors `≡ 3 (mod 4)` to an odd power (Fermat's criterion). This widens the set of
admissible `t` a future `n ≡ 3 (mod 8)` assembly may use, isolating the genuine
number-theoretic input more tightly. Pure algebra; the existence of a suitable `t`
remains the open analytic input.

## Verification status

Build-pending (Docker blackout). The new lemma uses only `obtain`/`refine`/
`rw`/`exact_mod_cast`/`ring` — every one of which already appears in the
build-verified `three_sq_of_residue3_prime` proof it replaces. Term reductions
hand-checked: `(a+b)² + (a−b)² = 2(a²+b²)` closes by `ring`; the cast goal
`(m:ℤ) = (t:ℤ)² + 2·(mm:ℤ)` closes by `exact_mod_cast hdecomp`. Next Docker-up
session must confirm via `docker-build.sh Proofs.ThreeSquaresResidue3`.

## Frontier UNCHANGED at the axiom level

The lone sufficiency axiom is untouched. Closing it still needs ternary
Hasse–Minkowski (factor 1, absent from Mathlib) + Davenport–Cassels (factor 2,
already build-verified, S14). This session sharpens a support lemma; it does not
move the axiom frontier.
