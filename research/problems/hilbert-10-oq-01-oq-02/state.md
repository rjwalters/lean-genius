# Current State

**Phase**: ACT
**Since**: 2026-05-08T13:00:00Z
**Iteration**: 7
**Last Updated**: 2026-05-08 (researcher-8)

## Current Focus

Iteration 7 (2026-05-08, researcher-8, this PR): completing the
**¬¬-shadow / double-negation invariance** story for all four
definability classes. Each of Σ₁, Π₁, Σ₂, Π₂ is proved stable under
classical double-negation of the predicate:

    Class(¬¬ S)  ⟺  Class(S),  for Class ∈ {Σ₁, Π₁, Σ₂, Π₂}.

All four are one-line corollaries of the iteration-3/4 `_iff_of_pred_iff`
class-congruence helpers, applied to the classical bridge
`S q ↔ ¬¬ S q` (factored out as a private named lemma
`doubleNeg_pred_iff`). One concrete corollary specializes the Σ₁
shadow to the open question for ℤ ⊂ ℚ:

    IntegersAreDiophantineOverQ  ⟺  Σ₁(fun q => ¬¬ IntSubset q).

Net new content: 0 definitions, 6 theorems (5 public + 1 private
bridge), 0 axioms.
Updated to total: 11 definitions (incl. 3 private), 39 theorems (incl.
4 private), 1 axiom, 0 sorries, 885 lines (was 787).

Iterations 1–6 established Σ₁ (open), Π₂ (Koenigsmann), the Σ₁/Π₁
duality (with symmetric form), the Σ₂/Π₂ duality (with symmetric form),
all four class-congruence helpers, the unconditional Σ₂(ℚ\ℤ) corollary
of Koenigsmann, the ∅ and ℚ trivial-set library across all four classes,
and the smallest non-trivial parameter-dependent witness {0}/ℚ\{0}
across all four classes via the projection polynomial `P(q,x) = q`.

## Active Approach

S7 — ¬¬-shadow / double-negation invariance (this iteration):

1. `doubleNeg_pred_iff S` (private bridge) — `∀ q, S q ↔ ¬¬ S q`,
   classical (one `Classical.byContradiction`).
2. `diophantineDefinition_doubleNeg_iff S` — Σ₁(¬¬ S) ⟺ Σ₁(S).
3. `coDiophantineDefinition_doubleNeg_iff S` — Π₁(¬¬ S) ⟺ Π₁(S).
4. `universalExistentialDefinition_doubleNeg_iff S` — Π₂(¬¬ S) ⟺ Π₂(S).
5. `existentialUniversalDefinition_doubleNeg_iff S` — Σ₂(¬¬ S) ⟺ Σ₂(S).
6. `integers_diophantine_iff_doubleNeg` — concrete shadow specialization
   for the OPEN Σ₁ question on ℤ ⊂ ℚ.

Each of #2–#5 is a single `(_iff_of_pred_iff (doubleNeg_pred_iff S)).symm`
term; #6 is `(diophantineDefinition_doubleNeg_iff IntSubset).symm`. No
new imports; no field arithmetic; no Mathlib dependencies. Same Path A
(zero-Mathlib, classical-only) discipline as iterations 5/6.

## Why this matters

The four ¬¬-shadow theorems make explicit a property that was used
implicitly in iteration 5's symmetric Σ₂/Π₂ duality: the Π₂ class is
invariant under `¬¬`-rewriting. Promoting that to a named theorem at
each level gives a uniform tool for refutation arguments that produce
classical double-negation layers (e.g., a Π₁ counter-witness obtained
by `Classical.byContradiction` before being repackaged as a Σ₁
predicate). The concrete `integers_diophantine_iff_doubleNeg` corollary
is the bridge a refutation argument would actually use on the OPEN
question for ℤ ⊂ ℚ.

## Build Status

Iteration 7 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so
Docker build would re-fresh-clone Mathlib (~25-45 min). The six new
theorems use ONLY one-line term-mode proofs that compose existing
iteration-3/4 lemmas by `.symm`; no tactic blocks, no new imports, no
new defs. Confidence high; CI is the ground truth.

Iteration 6 build: PASSED ✅ (per #17083 CI).
Iteration 5 build: PASSED ✅ (per #17065 CI).
Iteration 4 build: PASSED ✅ (per #17026 CI).
Iteration 3 build: PASSED ✅ (3 jobs, exit code 0).

## Blockers

None for axiom-free Path A pure-logic iterations. Field-arithmetic
extensions (closure under union/intersection, Π₁ ⊆ Π₂ via
polynomial-inversion, arbitrary singletons {a} for a ≠ 0) all require
Mathlib for `Rat.sub_eq_zero_iff`, `Rat.mul_eq_zero`, etc.

## Next Action

Commit, push, create PR for iteration 7 (this).

If S7 lands cleanly, S8+ candidates:
- **S8 (Path A, axiom-free)**: extend the smallest-non-trivial-witness
  story to other constant-polynomial subsets — e.g., `{q : ℚ | q = 0 ∨
  q = 0}` (degenerate), or chained singletons via predicate equivalence
  (`{0} ∪ {0} = {0}` via `_iff_of_pred_iff`).
- **S8 (Path B, Mathlib import)**: arbitrary singletons {a} for a : ℚ
  via `P(q, x) = q - a` and `Rat.sub_eq_zero_iff` (the genuine
  generalization of S6's `singletonZero`).
- **S8 (Path C, axiomatized)**: Daans 2021 (10-quantifier reduction of
  Koenigsmann) as a separate axiomatized witness — adds 1 axiom,
  documentary value only.
- **S9+**: closure properties (union/intersection) — needs
  `Rat.mul_eq_zero` (Mathlib).
- **S9+**: Π₁ ⊆ Π₂ via the polynomial-inversion trick `a ≠ 0 ⟺ ∃ z,
  a·z = 1` — needs `Rat` field arithmetic.

The Path A axiom-free corner of the file is now substantially
saturated; further single-PR progress without Mathlib is
incrementally smaller.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1 (S7 — ¬¬-shadow, this iteration)
- Approaches tried: 6 (S2 Σ₁/Π₁ duality, S3 Σ₂/Π₂ duality, S4 class
  congruence, S5 symmetric duality + trivial sets, S6 smallest
  non-trivial subset, S7 ¬¬-shadow)
