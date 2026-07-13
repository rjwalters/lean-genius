# Session 2026-07-10 (researcher-6) — prime-landing .eq/.gt family packaging

**Mode**: REVISIT (RICH tier; fresh branch off origin/main) | **Outcome**: progress
(UNVERIFIED — Docker infra down all session: containerd content-store blob
`input/output error`, `docker images` errors; operator-level, disk healthy ~115 GiB)

## What I Did
Completed the r8 "Next Steps" item: package the prime-landing trichotomy criteria
into infinitely-often family membership, the `.eq`/`.gt` analogues of the VERIFIED
`prime_landing_family_reversal`.

- `prime_landing_family_equality` — for `Odd a`, `a ≥ 3`, `seedS a = 1`,
  `seedE a` prime, and the balance equality
  `φ(seedB a) + 2^{seedT a} = 2·(a − φ a)`, the *entire* family `a·2^(k+1)` lies in
  `EqualitySet` (`φ(n) = φ(D(n))` for every `k`).
- `prime_landing_family_forward` — same hypotheses with the strict forward inequality
  `2·(a − φ a) < φ(seedB a) + 2^{seedT a}` place the whole family in `ForwardSet`
  (`φ(D(n)) < φ(n)` for every `k`).

Together with `prime_landing_family_reversal` this packages all three regimes of the
prime-landing trichotomy into infinitely-often membership. The abstract packagings
subsume the previously isolated concrete families (`mem_EqualitySet_sophieGermain`,
`mem_EqualitySet_five`, `mem_ForwardSet_thirteen`).

## Proof recipe
Line-for-line mirror of `prime_landing_family_reversal` (2-liner each), swapping
`lt → eq/gt`:
`rw [classifySeed_eq_iff ha ha3 k]` (VERIFIED general bridge, membership ⇔ classifier
value) then `exact (classifySeed_eq_iff_of_seedS_one_seedE_prime ha3 hs1 hep).2 hcrit`
(the r8 criterion, classifier value ⇔ linear inequality). Same for `.gt`.

## New declarations (0 sorry / 0 new axiom; UNVERIFIED, infra down)
- `prime_landing_family_equality`
- `prime_landing_family_forward`

## Files Modified
- `proofs/Proofs/EulerTotientOQ04OQ03.lean` (+~30 lines, 2 theorems)

## Next Steps
- Elementary/structural side is now fully packaged (all three regimes as
  infinitely-often families + trichotomy criteria). The only remaining open direction
  is the density-1 analytic forward statement (smooth-number density / Luca–Pomerance)
  — a genuine Mathlib gap, not session-sized.
