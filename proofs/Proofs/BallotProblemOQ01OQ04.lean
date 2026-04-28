/-
# Chung-Feller Theorem via the Cycle Lemma

## Research Problem: ballot-problem-oq-01-oq-04

The Chung-Feller theorem states that the number of lattice paths from (0,0)
to (2n,0) with steps +1 and -1, having exactly k upsteps above the x-axis,
equals C(2n,n)/(n+1) = Cₙ (the nth Catalan number), independent of k.

## Proof Architecture

The full proof is composed of three files:

- `BallotProblemOQ01OQ04Core.lean` — definitions and the cycle-lemma bridge
  (`IsBalancedPath`, `prepend_one_good_rotation`, `balanced_path_total`,
  `balancedPathsOfType`, etc.)
- `BallotProblemOQ01OQ04OQ01.lean` — the explicit bijection
  `chungFellerMap` from balanced paths to (Dyck paths) × (Fin (n+1)),
  proving `chung_feller_bijection_exists` and `chung_feller_uniform'`
  with 0 sorries and 0 axiom uses.
- This file — the gallery face, re-exporting the uniform-distribution
  theorem under its conventional name `chung_feller_uniform` and the
  per-type Catalan-number count.

## Proof Strategy

1. A lattice path from (0,0) to (2n,0) has n upsteps (+1) and n downsteps (-1).
2. Prepend +1 to get a sequence of length 2n+1 with sum 1.
3. By the cycle lemma (proved in BallotProblemOQ01.lean), exactly 1 of the
   2n+1 cyclic rotations has all partial sums positive.
4. Mapping each balanced path l to (Dyck-tail of its good rotation,
   upstepsAboveAxis l) is a bijection between balanced paths of length 2n
   and (Dyck paths) × (Fin (n+1)). This forces uniform distribution across
   types.

## Status

- 0 axioms, 0 sorries.
- The previously stated `axiom chung_feller_uniform` is now proved by
  re-export of `ChungFellerBijection.chung_feller_uniform'`, which itself
  was proved with no axiom uses.

## References

- Chung, K.L. and Feller, W. (1949). On fluctuations in coin-tossing.
- Dvoretzky, A. and Motzkin, Th. (1947). A problem of arrangements.
-/

import Proofs.BallotProblemOQ01OQ04OQ01

namespace ChungFeller

open ChungFellerBijection

/-- **Chung-Feller Theorem (uniform distribution)**.

    For each pair `j, k ∈ {0, 1, …, n}`, the number of balanced paths from
    `(0,0)` to `(2n,0)` with exactly `j` upsteps above the x-axis equals
    the number with exactly `k` upsteps above the x-axis — i.e. the
    distribution is uniform across the `n+1` types.

    Combined with `balanced_path_total` (`C(2n,n) = Cₙ × (n+1)`), this
    implies each type has exactly `Cₙ` paths.

    This was previously stated as an axiom in this file; the proof is
    supplied by `ChungFellerBijection.chung_feller_uniform'`, which uses
    the explicit bijection between balanced paths and Dyck paths × types
    constructed via the cycle-lemma rotation. -/
theorem chung_feller_uniform (n : ℕ) (j k : ℕ) (hj : j ≤ n) (hk : k ≤ n) :
    Set.ncard (balancedPathsOfType n j) = Set.ncard (balancedPathsOfType n k) :=
  ChungFellerBijection.chung_feller_uniform' n j k hj hk

end ChungFeller
