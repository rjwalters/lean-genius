# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-3): OBSERVE survey for `lagrange-four-squares-waring-g2-oq-01` — the open-question child of the verified gallery entry `lagrange-four-squares-waring-g2` (`Proofs/LagrangeFourSquaresWaringG2.lean`, $g(2) = 4$). The OQ asks for the analogous determination of $g(k)$ for $k \ge 3$ — i.e. Waring's problem in full generality.

This iteration produces:
- `problem.md` — formal problem statement, classical $g(k)$ values, Mathlib infrastructure map, decomposition into tractable S2/S3/S4 steps.
- `knowledge.md` — historical $g(k)$ table with citations, mod-arithmetic recipe for lower bounds, references to Hardy & Wright + Vaughan + OEIS A002804.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` — new entry.

No Lean changes in S1.

## Active Approach

**Two-tier strategy: lower bounds verified, upper bounds axiomatized.**

The classical $g(k)$ values are:

| $k$ | $g(k)$ | Lower-bound witness | Upper-bound technique |
|---:|------:|---|---|
| 2 | 4 | $7$ needs $4$ squares | Lagrange (Mathlib's `Nat.sum_four_squares`) |
| 3 | 9 | $23$ needs $9$ cubes | Wieferich–Kempner 1909/1912 (research-level) |
| 4 | 19 | $79$ needs $19$ fourth-powers | Balasubramanian–Deshouillers–Dress 1986 (research-level) |
| 5 | 37 | $223$ needs $37$ fifth-powers | Chen Jingrun 1964 (research-level) |
| 6 | 73 | $703$ needs $73$ sixth-powers | Pillai 1940 (research-level) |
| $\ge 7$ | $2^k + \lfloor (3/2)^k \rfloor - 2$ | — | Mahler 1957 + Kubina–Wunderlich 1990 (verified up to $k \sim 5 \times 10^8$) |
| existence | Hilbert–Waring | — | Hilbert 1909 (integral) / Hardy–Littlewood 1922 (circle method) |

**Lower bounds** are mod-arithmetic exercises in Lean (the parent file demonstrates the technique for $k = 2$: every $a^2 \in \{0, 1, 4\} \pmod{8}$).
**Upper bounds** are research-level proofs in additive combinatorics / analytic number theory; Mathlib has zero infrastructure for the circle method or for Wieferich–Kempner's polynomial-identity decomposition.

The OQ-01 plan therefore is:
1. Verify the lower bounds for $k = 3, 4$ (and possibly $5, 6$) via Lean-native mod arguments and bounded `decide` searches.
2. Introduce axioms for the upper bounds, citing the original papers.
3. Combine to produce explicit `waringG k = N` theorems that are *axiomatized*, with the axiom-dependence clearly documented in `meta.json`.

## Blockers

None mathematical for S1 (this is an OBSERVE iteration).

Practical infrastructure constraints (deferred to S2+):
- The `Proofs/.lake` symlink in the researcher worktree points to itself (per `feedback_researcher_lake_symlink_broken.md`); any future Docker build will be a fresh ~25-minute clone.
- `decide` on $3^{18}$ tuples for $g(4) \ge 19$ is infeasible; mod-16 argument is mandatory.

## Next Action

**S2 (any researcher)**: Prove `g3_lower : ¬ IsSumOfCubes 8 23` in a new file `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean`.

Concrete plan:

```lean
import Mathlib.Tactic
import Proofs.LagrangeFourSquaresWaringG2  -- for the IsSumOf-style definitions

namespace WaringG2OQ01

/-- `IsSumOfCubes s n`: `n` is a sum of `s` non-negative cubes. -/
def IsSumOfCubes (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n

/-- Bound each summand: if `a^3 ≤ n` then `a ≤ Nat.sqrt (Nat.sqrt n) + 1` (loose).
For `n = 23`, `a ≤ 2` since `3^3 = 27 > 23`. -/
lemma cube_bound_23 (a : ℕ) (h : a ^ 3 ≤ 23) : a ≤ 2 := by
  by_contra hlt; push_neg at hlt
  have : 27 ≤ a ^ 3 := by nlinarith
  linarith

/-- **g(3) lower bound**: 23 is not a sum of 8 cubes. -/
theorem twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23 := by
  rintro ⟨f, hf⟩
  -- Each f i ≤ 2; brute-force the 3^8 = 6561 cases.
  -- The actual proof uses `interval_cases` on each Fin index after bounding f i ≤ 2.
  sorry  -- ≈ 30 lines with `interval_cases` + `decide`
```

**Expected size**: ~80 Lean lines + ~50 lines of supporting infrastructure (`IsSumOfCubes` definition, cube-bound lemma, finite-search closure). Single-session S2 deliverable.

Alternative (more elegant): define a finite-search decidability instance via `Fintype (Fin 3 → Fin 8)` and reduce the lower bound to a `decide`. This requires re-coupling the search space tightly:

```lean
def representations23 : Finset (Fin 8 → Fin 3) :=
  Finset.univ.filter (fun f => ∑ i, ((f i : ℕ)) ^ 3 = 23)

theorem representations23_empty : representations23 = ∅ := by decide
```

This is the cleaner version; `decide` on $3^8 = 6561$ tuples is well within Lean's tactic budget.

## Prior Next-Action Sketch

(None — this is the inaugural S1 iteration.)

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE survey)
- Current approach attempts: 1 (OBSERVE → ACT decomposition)
- Approaches tried: 1

## Open files

- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, S2/S3/S4 decomposition.
- `knowledge.md` — $g(k)$ historical table with citations, mod-arithmetic recipes, bibliographic references.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` (~3.2K words) with formal Lean signature targets and tractability analysis.
- `state.md` (this file) advancing phase NEW → OBSERVE.
- `knowledge.md` (~2.5K words) with $g(k)$ historical table, mod-arithmetic recipes, and bibliography (Hardy & Wright, Vaughan, OEIS A002804, Wieferich, Kempner, BDD, Chen, Pillai, Mahler, Kubina–Wunderlich).
- `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` — new entry with progressSummary, builtItems=[], 6 insights, 3 mathlibGaps, 4 nextSteps.

The S1 next-action is fully specified: a self-contained `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` introducing `IsSumOfCubes` and proving `twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23` via bounded `decide` over $3^8 = 6561$ tuples (~80 Lean lines).
