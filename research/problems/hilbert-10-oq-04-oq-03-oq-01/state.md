# hilbert-10-oq-04-oq-03-oq-01 — Constructive Bézout solver

**Status:** solved & VERIFIED (`lake env lean` single-file elaboration, exit 0)
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

## Verification

Verified by single-file elaboration against the prebuilt Mathlib oleans:
`lake env lean Proofs/Hilbert10OQ04OQ03OQ01.lean` → exit 0, no errors, no sorries.
`#print axioms` of `exists_vec_combo` / `bezout_solve_spec` reports only the
foundational `propext` / `Classical.choice` / `Quot.sound` — no `Lean.ofReduceBool`,
no `sorryAx`. The development is therefore genuinely verified and axiom-free.

(Docker `docker-build.sh` was initially unavailable — the data volume was at 100%
— but the host freed to ~20 GiB and the lighter `lake env lean` path succeeded.)

## Follow-ups

- oq-01 (this entry's): bridge `vecGcd` ↔ `Finset.univ.gcd` (associated over ℤ) so
  `exists_vec_combo` discharges the forward direction of `solvable_iff_gcd_dvd` verbatim.
- oq-02: extend to systems `A·x = b` via Smith normal form (sibling
  `hilbert-10-oq-04-oq-03-oq-02`).
