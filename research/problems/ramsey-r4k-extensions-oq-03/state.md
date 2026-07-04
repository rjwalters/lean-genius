# Research State: ramsey-r4k-extensions-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 15 (PART XV)

## Current Focus
Globalized the PART-XIV single-step monotonicity into the window-wide statement its own
docstring only asserted. Two new axiom-free theorems in
`Proofs/RamseyR4kExtensionsOQ03Deletion.lean`:
- `deletionBound_mono_window`: chaining the single step by `Nat.le_induction`,
  `deletionBound n k ≤ deletionBound N k` whenever `2·C(m,k−1) < 2^C(k,2)` for every
  `m ∈ [n, N)`. So the deletion optimum is attained no earlier than the *top* of the
  `(k−1)`-window — the general, `decide`-free statement that the alteration bound keeps
  climbing past the union cap (top of the strictly narrower `k`-window).
- `deletion_noloss_across_window`: Ramsey form — for any `N` reachable across the
  `(k−1)`-window there is a 2-colouring of `K_N` with a monochromatic-`Kₖ`-free set of at
  least `deletionBound n k` vertices. This is the general mechanism instantiated by the
  concrete `+1/+2/+3/+4` witnesses at `k = 6,7,8,9`.

PART XIV proved only the single step `n → n+1`; PART XV turns that into the whole run,
completing the "runs out to the top of the `(k−1)`-window" claim. Pure `Nat` induction on
top of the existing Pascal-rule step; closed by `le_trans`/`omega`. No `decide`, no
probability. docker-build clean (7744 jobs), Tier-A axiom-free.

## Active Approach
Elementary `Nat`-division monotonicity. docker-build clean (7744 jobs), Tier-A axiom-free
(`propext / Classical.choice / Quot.sound`).

## Attempt Count
- Total attempts: 15
- Current approach attempts: 1
- Approaches tried: LLL parameters, dependency-degree bound, LLL vs union bound
  identity, honest union-bound comparison (VII), deletion method (VIII), k=7
  machine-checked witness + compile repair (IX), general M=1 gain theorem (X),
  avoidance_pos numeric premises (XI), k=8 witness via descFactorial (XII),
  general M-window unification theorem (XIII), deletion-window monotonicity via
  Pascal's rule (XIV), window-wide monotonicity + Ramsey form via Nat.le_induction (XV)

## Blockers
- **MATH**: `SymmetricLLLForRamsey` full formalization (>1000 lines, measure theory) —
  the sole remaining non-Mathlib ingredient. Left as explicit hypothesis. See sibling
  `lovasz-local-lemma-oq-01`.

## Next Action
The axiom-free line is now saturated *and* globalized: the deletion mechanism is stated at
full generality (`ramsey_deletion_window`, every M), its window's monotonic growth is proved
both per-step (PART XIV) and window-wide (`deletionBound_mono_window`, PART XV), with a Ramsey
existence form (`deletion_noloss_across_window`) and concrete k=6,7,8,9 witnesses. The only
remaining genuinely-mathematical increments both need machinery beyond elementary `Nat`:
either (a) the BLOCKED `SymmetricLLLForRamsey` measure-theoretic construction (>1000 lines),
or (b) a Stirling-based *asymptotic* proof that the additive window width grows like a
constant fraction of the union value — i.e. `Nat.choose` ratio asymptotics beyond Pascal's
rule (real analysis, not `omega`). Further concrete k≥10 witnesses would be enumeration
theater. Recommend releasing the claim; the natural next worker should target the sibling
`lovasz-local-lemma-oq-01` measure-theory core, or attempt (b) with `Nat.choose` asymptotics.
