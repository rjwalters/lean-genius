# Current State

**Phase**: FORMALIZED (verified infrastructure; open problem itself remains open)
**Since**: 2026-06-25
**Iteration**: 5

## Current Focus

Formalized the exact arithmetic of mediant insertion on Farey gaps:
`proofs/Proofs/Erdos1005ProblemOQ02.lean` (389 lines, 24 theorems, 1 def,
0 sorries, 0 axioms; #print axioms reports only propext / Classical.choice /
Quot.sound).

## Active Approach

Two verified threads:
1. **Gap-splitting calculus** — a unimodular gap `1/(bd)` splits under its
   mediant into `1/(b(b+d))` and `1/(d(b+d))`; these sum back to `1/(bd)`,
   stand in ratio `d:b`, and each is strictly smaller than the whole. Each
   half is again unimodular (recursive Stern–Brocot insertion).
2. **Minimal-denominator theorem (headline)** — every fraction `p/q` strictly
   between two unimodular neighbours `a/b < c/d` has `q ≥ b+d`, with equality
   forcing `p/q = (a+c)/(b+d)`. The mediant is the unique smallest-denominator
   fraction in the gap; `b+d` is a hard lower bound on any refinement.

## Blockers

The actual open question — improving the lower bound `f(n) ≥ (1/12 − o(1))n`
on the longest run of *similarly ordered* Farey fractions — is **not**
addressed. That constant `c ∈ [1/12, 1/4]` remains open. This session
formalizes the verified mediant calculus that such constructions rest on, not
a resolution of the bound.

## Iteration 3 addition (verified)

Added **§5 (strict denominator growth + depth-two refinement)**, 0-sorry /
0-axiom: `interior_denom_gt_max` (every in-gap fraction has denominator
> max(b,d) — refinement strictly raises the smallest denominator);
`denom_ge_left_subgap`/`denom_ge_right_subgap` (each sub-gap is again
unimodular, giving depth-two bounds q ≥ 2b+d, q ≥ b+2d); and the headline
`denom_ge_of_between_ne_mediant` — the mediant is the *unique* denominator-(b+d)
point, and the next admissible denominator jumps by ≥ min(b,d). This is the
strict-growth step the counting argument rests on; the 1/12 run constant itself
remains open.

## Iteration 4 addition (design/knowledge — build host down)

Recorded `sessions/2026-06-27-s4-counting-roadmap-and-literature.md`: pins the
literature to **van Doorn 2025, arXiv:2509.00121** (lower `(1/12−o(1))n`,
explicit upper `n/4 + 5`, sharpening the parent knowledge.md's `n/4 + O(1)`),
maps each verified lemma (minimal-denominator `q ≥ b+d`, strict growth, depth-
two `q ≥ 2b+d` / `b+2d`) onto a counting-argument roadmap, and fixes the precise
next Lean target: a **depth-`k` Fibonacci denominator bound** (0-axiom
induction over nested mediant insertions ⇒ `O(log_φ n)` refinement depth under
the order-`n` cap). No Lean change this cycle: Docker build host data volume is
100% full (containerd meta.db I/O error; `docker-build.sh` false-exits 0), so
an unverified inductive proof would risk the file's clean 0-axiom status.

## Iteration 5 addition (verified, 0-axiom — build host still down, used `lake env lean`)

Added **§6 (iterated one-sided insertion — exact linear denominator growth)**,
0-sorry / 0-axiom (verified by `lake env lean` against the main-repo Mathlib
`.olean` cache; Docker still unusable). Five theorems:
`unimodular_iterate_left`/`_right` (k-fold one-sided insertion stays unimodular,
`a/b < (k·a+c)/(k·b+d)`, by scale-invariance of `bc=ad+1` — no induction);
`denom_ge_iterate_left`/`_right` (depth-`k` interior denominator bound
`q ≥ (k+1)·b+d`); `iterate_left_denom_linear` (the exact `(k+1)·b+d`).

**Key correction.** The Iteration-4 "depth-`k` Fibonacci ⇒ `O(log n)` refinement
depth" target was **mathematically wrong as a universal claim**: the one-sided
chain `0/1, 1/2, 1/3, …, 1/n` has only LINEAR denominator growth and fits
`Θ(n)` refinement levels under the order-`n` cap. Exponential `φ^k` growth (hence
`O(log n)` depth) is special to *balanced/alternating* chains — the opposite
extreme from this linear worst case. §6 formalizes the linear extreme and the
file/meta now record the correction. A sharp run-length count toward `1/12` must
distinguish the two extremes.

## Next Action

Formalize the complementary **balanced/alternating** extreme: track the
alternating mediant chain's denominators against `Nat.fib`, proving the `φ^k`
growth and the `O(log_φ n)` depth bound for balanced descent. Then bridge depth
to run length (monotone Stern–Brocot paths under the order-`n` cap ↔ runs of
similarly ordered fractions).

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1
