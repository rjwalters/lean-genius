# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-10): OBSERVE survey for `erdos-455-oq-04` — the seeker-extracted child of the verified gallery entry `erdos-455` ("Monotone Prime Gap Sequences"). Parent's `conclusion.openQuestions[3]`:

> Can the problem be generalized to other arithmetic conditions on gaps (e.g., gaps forming an arithmetic progression)?

This iteration produces:

- `problem.md` — formal Lean target signatures (`APGapPrimeSeq d` structure, `apGap_zero_iff_prime_AP`, `apGap_subsumes_monotone`, conjectural growth bound), S2-S7 decomposition, Mathlib gap analysis.
- `knowledge.md` — gap-condition hierarchy table; cubic-growth heuristic; manual enumeration showing AP-gap-with-$d>0$ sequences are sparse beyond length 4; comparison with parent and sibling sub-OQs.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/erdos-455-oq-04.json` — gallery JSON.

No Lean changes in S1.

## Active Approach

**The generalization splits cleanly into two subcases**:

1. **Constant-gap ($d = 0$)**: primes in arithmetic progression = **Green–Tao theorem** territory. Mathlib has no Green–Tao; axiomatise.
2. **AP-gap ($d > 0$, strictly increasing gap differences)**: a *new* mathematical question. Growth bound conjectural at $\Omega(n^3)$ (the author's heuristic; not in published literature).

### Key technical insight

For an AP-gap prime sequence with $d > 0$:
- $g_n = g_0 + n \cdot d$ — linear gap growth.
- $q_n = q_0 + n g_0 + \binom{n}{2} d$ — quadratic $a priori$.
- Tightening to $n^3$ requires combining with primality density constraints (Vinogradov / Heath-Brown level estimates) — not in Mathlib.

### Concrete-example search (S6 task)

Manual enumeration in S1 (see `knowledge.md` for detail) failed to find a length-5 AP-gap prime sequence with $d = 2$ by hand. A computer search through the first 10^5 primes is recommended; expected to reveal:
- Many length-3 sequences (Green-Tao guarantees length-$k$ APs for $d = 0$).
- Few length-4+ sequences with $d > 0$.
- Possibly no length-10+ sequences for any fixed $d$.

## Blockers

None mathematical for S1. Practical:

- **Green–Tao 2008 absent from Mathlib**: S5 must axiomatise. The 30+-page proof is far from Mathlib-reachable in a single iteration.
- **Cubic growth bound is conjectural**: no published reference. S4's axiom is the author's reasoned conjecture.
- **`status: "axiomatized"` is mandatory** — Green-Tao alone forces this.

## Next Action

**S2 (any researcher)**: Define `HasAPGaps`, `APGapPrimeSeq d` in `proofs/Proofs/Erdos455OQ04.lean`. Prove the trivial equivalence `apGap_zero_iff_prime_AP` and the monotone-gap subsumption `apGap_subsumes_monotone`.

Concrete plan:

```lean
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Proofs.Erdos455Problem  -- parent (HasNonDecreasingGaps, MonotoneGapPrimeSeq)

namespace Erdos455OQ04

/-- A sequence has AP-gaps with common difference d (integer-valued for d < 0 case). -/
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop :=
  ∀ n, (q (n + 2) : ℤ) - 2 * (q (n + 1) : ℤ) + (q n : ℤ) = d

structure APGapPrimeSeq (d : ℤ) where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  allPrime : ∀ n, (seq n).Prime
  apGaps : HasAPGaps seq d

theorem apGap_zero_iff_prime_AP : ... := by ...
theorem apGap_subsumes_monotone : d ≥ 0 → HasAPGaps q d → HasNonDecreasingGaps q := by ...

end Erdos455OQ04
```

Expected ~50 Lean lines, 0 sorries.

**S3** (after S2): Axiomatize Green-Tao for prefix-AP statements.
**S4** (after S3): Axiomatize cubic growth bound for $d > 0$ AP-gap sequences.
**S5** (after S4): Combine; gallery integration with `status: "axiomatized"`, `axiomCount: 2-3`.
**S6** (optional): Computer-search examples; `native_decide` certificates for small witnesses.

## Honesty

This S1 OBSERVE is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry/axiom deltas
- 3 markdown files
- 1 gallery JSON

The **constant-gap subcase = Green-Tao** — deep, well-known, axiomatised. The **AP-gap subcase with $d > 0$** is a *new* question to the author's knowledge; the cubic growth bound is conjectural.

The future Lean entry will be `status: "axiomatized"` because Green-Tao is non-negotiable. Even if the cubic-growth axiom proves wrong, the structural framework (S2-S3) remains correct.
