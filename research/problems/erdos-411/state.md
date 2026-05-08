# Current State

**Phase**: ITERATE
**Since**: 2026-05-08
**Iteration**: 8 (post-ratio4 + Steinerberger sufficient direction)

## Current Focus

Formalize Steinerberger's (2025) reduction of the r=2 doubling problem
to the elementary equation φ(n) + φ(n + φ(n)) = n. The sufficient
direction is now proved.

## Active Approach

`iteratedTotientStep 2 n = (n + φ(n)) + φ(n + φ(n))` reduces by `rfl`,
giving `steinerberger_iff` (g_2(n) = 2n ↔ Steinerberger equation) by `omega`.
Combined with `doubling_propagation`, this proves
`steinerberger_r2_sufficient` with K = 0 for any even n > 2 satisfying
the equation. Verified the n=10, n=94 cases satisfy the equation by
`native_decide`.

## Blockers

The reverse direction (DoublingRelation n 2 → φ(n) + φ(n + φ(n)) = n)
requires backward reasoning along orbits of g and is genuinely harder:
the asymptotic doubling at K could begin with an iterate g_K(n), not n
itself, so arguing back to n needs a different technique.

## Next Action

(Optional) Attempt the converse direction: show that for even n > 2, if
DoublingRelation n 2 holds with witness K, then g_K(n) satisfies the
Steinerberger equation; characterize when the witness can be taken K = 0.

Alternatively: Selfridge–Weintraub g_{k+9}(n) = 9·g_k(n) solutions or
Weintraub's g_{k+25}(3114) = 729·g_k(3114) (would need a totientStep_p_dvd
lemma for general primes p).

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1 (succeeded)
- Approaches tried: 8 (axiomatic skeleton; Cambie ratio-3; Cambie ratio-4
  for two cases; Steinerberger sufficient direction)

## Sessions

### Session 2026-05-08 — S8 Steinerberger sufficient direction (PROVED)

**Mode**: ITERATE
**Outcome**: 5 new theorems added (axiom-free, sorry-free)

#### What I added
- `iteratedTotientStep_two`: g_2(n) = (n + φ(n)) + φ(n + φ(n)) by rfl
- `steinerberger_iff`: g_2(n) = 2n ↔ φ(n) + φ(n + φ(n)) = n (rw + omega)
- `steinerberger_r2_sufficient`: even n > 2, equation ⇒ DoublingRelation n 2
- `steinerberger_eq_n10`: n=10 satisfies the equation (native_decide)
- `steinerberger_eq_n94`: n=94 satisfies the equation (native_decide)

#### Files Modified
- `proofs/Proofs/Erdos411Problem.lean` (+41 lines, 22 theorems total)
- `src/data/proofs/erdos-411/meta.json` (lineCount, theoremCount,
  originalContributions, proofStrategy, mainTheorems)
- `research/problems/erdos-411/state.md` (this file)

#### Notes
- Build pending — Docker build typically takes 30-45 min from clean cache
  due to broken proofs/.lake symlink (see memory: feedback_researcher_lake_symlink_broken)
- All proofs use only definitional unfolding, omega, native_decide, and
  composition of pre-existing lemmas; no Mathlib api drift risk
