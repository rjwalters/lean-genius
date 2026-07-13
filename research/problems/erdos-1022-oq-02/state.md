# Research State: erdos-1022-oq-02

## Current State
**Phase**: ACT (saturated — verified 0-axiom/0-sorry file; adding closed-form corollaries)
**Path**: full
**Since**: 2026-07-09 (researcher-6)
**Iteration**: 1

## Problem
Erdős #1022 OQ-02: growth rate of the Property-B sparseness threshold `c_t`.
`Proofs/Erdos1022OQ02.lean` isolates the **first-moment** answer over bounded
ground sets: the admissible coefficient `c(t) = ⌊2^{t-1}/|V|⌋` grows exponentially
in the minimum set size `t`. File is `verified`, 0 axioms / 0 sorries, with a rich
two-index (`t + k`) exponential API for `c`.

## Iteration 1 (researcher-6, 2026-07-09) — single-index closed-form lower bound [UNVERIFIED — docker infra down]

**Outcome**: one addition, `admissibleCoeff_ge_two_pow_sub` (0 new axioms, 0 new
sorries). All the file's exponential lower bounds were in two-index `t + k` form
(`admissibleCoeff_two_pow_mul_le`, `admissibleCoeff_ge_two_pow_of_card`
`2^k ≤ c(|V|+1+k)`); none stated the growth in the single variable `t`. The new
lemma collapses the unconditional iterate by `k = t − |V| − 1`:

    for t > |V|:   2^{t − |V| − 1}  ≤  c(t) = ⌊2^{t-1}/|V|⌋.

This turns the docstring remark in `admissibleCoeff_ge_two_pow_of_le`
("`c(t) ≥ 2^{t−t₀}` for `t ≥ t₀`") into a checked theorem with the concrete,
unconditional threshold `t₀ = |V| + 1`. One-line proof: specialise
`admissibleCoeff_ge_two_pow_of_card` and rewrite the index via `omega`.

Also synced the gallery `lineCount` (505 → 568; was already stale pre-edit).

**Build note — UNVERIFIED (environmental)**: `docker-build.sh` died at Docker image
build with `containerd .../meta.db: input/output error` (session-wide docker outage;
host disk healthy). The proof is a one-line specialisation + `omega` index rewrite;
hand-checked. CI in a clean environment is ground truth.

## Next Action
File is saturated. Future claimants: verify the added lemma builds once docker is
restored; otherwise release without churning the complete verified core.

## Blockers
Docker infra down (containerd meta.db I/O error).
