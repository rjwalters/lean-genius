# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-1, 2026-05-12): Initial OBSERVE survey scaffold for the
exact-count generalization of the parent file's `card_sq_eq_one_ge_three`
qualitative lower bound.

Question (full text from the parent's open-questions list):

> Can the CRT construction be generalized to give a formula for the
> number of square roots of unity in `(ℤ/nℤ)ˣ` for any `n`?

Answer (S1 survey): yes, and the formula is

$$
\#\sqrt{1}_n \;=\; 2^{\omega_{\text{odd}}(n) + \varepsilon_2(n)}
$$

where `ω_odd(n)` is the number of distinct odd prime factors and
`ε₂(n) ∈ {0, 1, 2}` depends on the 2-adic valuation of `n`. Concrete
table for `n = 1..120` verified in `knowledge.md`.

## Active Approach

**Mathlib bridge + CRT specialization.**

The parent file proves the **existence** of a third square root for
every non-cyclic `(ℤ/nℤ)ˣ` (and shows non-cyclicity is automatic
when `n ≠ 1, 2, 4, p^k, 2p^k` for odd primes `p`). OQ-03 upgrades
this to the **exact count**.

All Mathlib infrastructure required is already in place at the pinned
revision:

- `ZMod.chineseRemainder` (already used by the parent).
- `ZMod.unitsCyclic` family — `(ZMod p^k)ˣ` cyclic for odd `p`.
- `(ZMod 2^k)ˣ ≅ ℤ/2 × ℤ/2^{k-2}` decomposition for `k ≥ 3`
  (the parent's `exists_third_sqrt_pow2` exhibits the non-trivial
  element constructively).

The OQ-03 deliverable is to **count**, not to **reprove**.

## Blockers

None mathematical.

Practical:

- The `proofs/.lake` symlink in the researcher worktree points to
  itself; any Docker build will be a fresh ~45-minute clone. Strict
  text-only iterations (this S1) are unaffected.
- The parent file uses `Nat.ordProj_mul_ordCompl_eq_self` rather than
  `Nat.factorization` for the 2-adic split; S2 should match this
  convention to avoid duplicate machinery.

## Next Action

**S2 (any researcher)**: Create
`proofs/Proofs/GaussWilsonNonCyclicOQ03.lean` with:

1. `noncomputable def numSqrtsOne (n : ℕ) : ℕ` — closed-form count.
2. `decide`/`rfl` examples verifying the formula at small `n`
   (1..16, 24, 30, 60, 105, 120).
3. Statement (with `sorry`) of the main theorem
   `card_sqrts_one_eq_numSqrtsOne n hn : ... = numSqrtsOne n`.
4. Helper lemmas relating `Finset.filter (· ^ 2 = 1)` over `ZMod n`
   to the same filter over `(ZMod n)ˣ` (via `unitOfSqEqOne` from
   the parent).

Skeleton in `knowledge.md`. ~80 lines, 1 sorry, 0 axioms expected.

**S3..S5** (subsequent sessions):

- S3: prime-power cases via `ZMod.unitsCyclic` (~100 lines).
- S4: CRT multiplicativity (~50 lines).
- S5: induction-on-`factorization.support` assembly (~40 lines).

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1 (Mathlib bridge + CRT)
- Approaches tried: 1

## Open files

- `problem.md` — theoretical context, decomposition into S2–S5,
  Mathlib infrastructure map.
- `knowledge.md` — S1 session notes: numerical table N=1..120,
  closed-formula derivation, parent-file API summary, three
  equivalent counts (ring / units / characters), S2 skeleton.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` (~280 lines) — full problem statement, decomposition.
- `state.md` (this file) — phase NEW → OBSERVE.
- `knowledge.md` (~200 lines) — numerical table, derivation, Mathlib
  status, S2 skeleton.
- `src/data/research/problems/gauss-wilson-non-cyclic-oq-03.json`
  (new file; orphan in main-repo working tree was untracked) —
  phase NEW → OBSERVE; 5 insights, 3 mathlibGaps, 4 nextSteps,
  references including Disquisitiones Arithmeticae §96.
