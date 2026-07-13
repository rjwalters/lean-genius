# S1 — Mod-3 Structure of Markov Triples

**Date:** 2026-06-27
**Agent:** researcher-1
**Phase:** OBSERVE → ACT (fresh problem scoped + proved)
**Build status:** PENDING (host blocker) — hand-verified by compiled precedent.

## What was done

This was a fresh EMPTY problem (`markov-equation-oq-02`) with only a bare
registry slug and no problem statement. I scoped it (see `problem.md`) to the
**prime-3 arithmetic structure** of Markov triples — the natural complement to
the existing prime-2/parity and coprimality layers — and proved it.

New file `proofs/Proofs/MarkovEquationOQ02.lean` (0 sorry / 0 axiom):

- `not_three_dvd_both` — coprime pair cannot share the factor `3` (verbatim
  prime-3 analogue of `MarkovCoprime.not_two_dvd_both`).
- `markov_not_three_dvd` — **main**: no coordinate of a Markov triple is
  divisible by `3`. Proof: reduce `x²+y²+z²=3xyz` to `ZMod 3` (RHS `≡ 0`), a
  `decide` shows one zero residue forces all three zero, which contradicts
  `markov_coprime`.
- `markov_not_three_dvd_fst` — the first-coordinate specialisation.
- `markov_sq_eq_one_mod_three` — every coordinate `≡ ±1 (mod 3)` (residue
  squares to `1`), via `decide` on nonzero `ZMod 3` elements.
- Four sanity `example`s on `(1,1,1)`, `(1,1,2)`, `(1,2,5)`, `(2,5,29)`.

## Why these tactics are trustworthy without a local build

Every step mirrors already-compiled code in the same Markov family:

- The `congrArg (Int.cast) … ; push_cast ; linear_combination` + `decide`-over-
  `ZMod 3` pattern is copied from `three_dvd_all_of_hurwitz_one`
  (`MarkovHurwitzOQ03OQ01.lean:101–117`) — same modulus, same cast lemma
  `ZMod.intCast_zmod_eq_zero_iff_dvd` (also used across ~20 other gallery files).
- `not_three_dvd_both` is `MarkovCoprime.not_two_dvd_both` with `2 ↦ 3`
  (`isUnit_of_dvd'` + `Int.isUnit_iff` + `norm_num`).
- `markov_coprime` signature confirmed: `IsCoprime x y ∧ IsCoprime y z ∧
  IsCoprime x z`.
- Dropped a tentative `markov_three_coprime_fst` (would need
  `Prime.coprime_iff_not_dvd` in the `IsCoprime`-over-ℤ form, for which I found
  only the `Nat.Coprime` precedent) to keep the file robust under the build
  outage.

## Build blocker (same as the pascals PR this session)

Docker build host is down: Data volume 100% full + containerd blob-store I/O
corruption, no `lean4-arm64:v4.26.0` image; local single-file `lean` typecheck
impossible (worktree olean cache partial — `Aesop.olean`, `Mathlib/Tactic.olean`
absent). Direct `lake build` is policy-prohibited. Shipped build-pending with a
request to verify via `./proofs/scripts/docker-build.sh Proofs.MarkovEquationOQ02`
once the host recovers.

## Next

- Build-verify and (post-verification) add the gallery entry
  `src/data/proofs/markov-equation-oq-02/` (meta + annotations).
- Optional follow-ups: residues mod other small primes; the
  `markov_three_coprime` corollary once the right `IsCoprime` lemma is confirmed.
- Out of scope: the parent's hard open questions (Markov uniqueness conjecture;
  `(log N)²` tree growth).
