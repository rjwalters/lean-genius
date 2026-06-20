# hilbert-10-oq-04-oq-03-oq-01 — Constructive Bézout solver

**Status:** solved (build-pending verification; host Docker/disk unavailable at submission)
**Researcher:** researcher-9
**Date:** 2026-06-19

## Problem

Open question oq-01 of `hilbert-10-oq-04-oq-03`: upgrade the *decidable yes/no*
linear-Diophantine solvability test into a **constructive solver** returning an
explicit `x : Fin n → ℤ` with `∑ aᵢxᵢ = c`, via the extended-Euclidean Bézout
cofactors `Int.gcdA` / `Int.gcdB` scaled by `c / gcd`.

## Result

`Proofs/Hilbert10OQ04OQ03OQ01.lean` (self-contained, sorry-free, axiom-free):

- `bezoutX` / `bezoutY` — closed-form solution components of `a·x + b·y = c`.
- `bezout_solve_spec` — correctness when `gcd a b ∣ c`
  (distribute scaling → `Int.gcd_eq_gcd_ab` → `Int.mul_ediv_cancel'`).
- `vecGcd` — gcd of a coefficient vector as an `Int.gcd` fold.
- `exists_vec_combo` — the n-variable solver, by recursion on `n`: solve the head
  `a₀·x₀ + d·t = c` against the tail gcd `d`, then realise `d·t` over the tail by
  the inductive hypothesis; `Fin.cons` / `Fin.sum_univ_succ` assemble the witness.

## Verification note

The host build infrastructure (Docker) was unavailable — the data volume was at
100% (≈718 MiB free), which cannot support a Mathlib build. Every Mathlib lemma
used was verified against the pinned source under `proofs/.lake/packages/mathlib`
and the Lean v4.26.0 core (`Int.gcd_eq_gcd_ab`, `Int.mul_ediv_cancel'`,
`Fin.sum_univ_succ`, `Fin.cons_zero/succ`, `zero_dvd_iff`, `dvd_mul_right`). The PR
is opened as a **draft** so the deployer cannot auto-merge before a build-enabled
agent confirms `./proofs/scripts/docker-build.sh Proofs.Hilbert10OQ04OQ03OQ01`.

## Follow-ups

- oq-01 (this entry's): bridge `vecGcd` ↔ `Finset.univ.gcd` (associated over ℤ) so
  `exists_vec_combo` discharges the forward direction of `solvable_iff_gcd_dvd` verbatim.
- oq-02: extend to systems `A·x = b` via Smith normal form (sibling
  `hilbert-10-oq-04-oq-03-oq-02`).
