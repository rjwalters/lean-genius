# Knowledge: erdos-748-incomplete-01

## Research Notes

### Sharper trivial lower bound (2026-06-25, researcher-9)

Added `sharp_lower_bound : ∀ n, f n ≥ 2 ^ ((n+1)/2)` — i.e. `f(n) ≥ 2^⌈n/2⌉`,
0 axioms. The previously-stated `trivial_lower_bound` only extracted the weaker
exponent `⌊n/2⌋` despite the proof already establishing `2^|U| ≤ f n` for the
upper half `U = {⌊n/2⌋+1,…,n}`, whose cardinality is `n − ⌊n/2⌋ = ⌈n/2⌉`. The
sharp version simply keeps `|U|` instead of weakening it to `⌊n/2⌋`. For odd `n`
this is a full factor of 2 (√2 per element) larger and is the best the upper-half
construction yields. `erdos_748_summary` now cites the sharp bound (`∀ n`, no
`n ≥ 2` hypothesis needed). Typechecked clean via `lake env lean` (Docker down).

### Current state (2026-06-25, researcher-2)

`proofs/Proofs/Erdos748Problem.lean` is in good shape: **0 sorries, 2 axioms**.
The formalization of the Cameron–Erdős conjecture is essentially complete at the
*achievable* level. The two remaining axioms are genuinely deep literature results:

- `green_upper_bound` — Green (2004), `f(n) ≪ 2^{n/2}`. Fourier-analytic /
  structure-theorem proof; formalizing it is a >1000-line undertaking (BLOCKED).
- `precise_asymptotic` — Green/Sapozhenko (2003/2004), `f(n) ~ c_n·2^{n/2}`
  with parity-dependent constants. Same blocker.

The trivial lower bound `f(n) ≥ 2^{⌊n/2⌋}` is **fully proved** (formerly an axiom)
via the powerset of the upper half `{⌊n/2⌋+1,…,n}` embedding into the sum-free
subsets.

This session added two new 0-axiom structural theorems:
- `sumFreeSubsets_subset_succ : sumFreeSubsets n ⊆ sumFreeSubsets (n+1)` —
  sum-freeness is intrinsic to a set, so enlarging the ambient range `{1,…,n}`
  cannot break it.
- `f_monotone : Monotone f` — the counting function never decreases. Proved by
  `monotone_nat_of_le_succ` from the subset-step + `Finset.card_le_card`.

### Follow-up status

The natural follow-up "largest sum-free subset of {1,…,n} has size ⌈n/2⌉" is
owned by **open PR #30202** (do not duplicate).

## Known Facts

- Lean file: `proofs/Proofs/Erdos748Problem.lean` (0 sorries, 2 deep axioms)
- Companion: `proofs/Proofs/Erdos748Aristotle.lean`
- `f n := (Finset.Icc 1 n).powerset.filter IsSumFree |>.card`
- Both remaining axioms are deep (Green 2004 / Sapozhenko 2003), not routine.

## Approaches Tried

- Axiom hunt: only `trivial_lower_bound` was routine; already eliminated upstream.
- Structural additions (monotonicity of `f`) — done this session, 0 new axioms.
