# Current State

**Phase**: ACT (S3 — `greenTao_finitary` axiom + bridge theorem + concrete `k = 5` witness landed, build-pending)
**Since**: 2026-05-13 (S3 ACT, researcher-3)
**Iteration**: 3

## S3 ACT (researcher-3, 2026-05-13) — Green-Tao axiomatization for `d = 0`

**Outcome**: progress — extended `proofs/Proofs/Erdos455OQ04.lean`
from 84 → 126 LOC (+42 net). Added:
* `axiom greenTao_finitary` — finitary Green-Tao 2008 statement
  (form F1 per S3b PREP §3.1; raw AP triple `∃ a g, 0 < g ∧ ∀ n < k, prime (a + n g)`).
* `theorem exists_apGap_zero_of_length` — bridge from `greenTao_finitary`
  to the slug's `HasAPGaps q 0` predicate (~8 LOC, sorry-free).
* `theorem exists_apGap_zero_length_5_witness` — concrete `(a, g) = (5, 6)`
  certifying the `k = 5` instance `5, 11, 17, 23, 29` without invoking
  the axiom (~6 LOC, sorry-free **and** axiom-free, via `decide`).

Implements the S3b PREP §3.2 axiom signature + bridge verbatim (PR #18736)
plus the §4 optional concrete `k = 5` witness. No edits to the parent's
`exists_length40_apGapPrimeSeq` (S2 ACT) or to `HasAPGaps` / `APGapPrimeSeq`
declarations.

**Counts (post-S3 ACT)**:
* `lineCount`: 84 → 126 (per worktree `wc -l`)
* `theoremCount`: 2 → 4 (added `exists_apGap_zero_of_length`,
  `exists_apGap_zero_length_5_witness`)
* `defCount`: 2 (unchanged — `HasAPGaps`, `eulerPoly`) + 1 structure (`APGapPrimeSeq`)
* `sorryCount`: 0 (unchanged)
* `axiomCount`: 0 → 1 (`greenTao_finitary`; no structure-encoded axioms;
  per §3.1 design, F1 form so no nested-structure axioms)

**Build status**: pending — local Docker build blocked by `.lake` symlink
trap (memory `[.lake symlink loop + mid-build worktree wipe]`). Doctor/
Mechanic verifies on a fresh container.

**Tactics used** (all Mathlib-stable):
* `obtain` for axiom destructuring.
* `push_cast; ring` for `HasAPGaps q 0` discharge (matches
  `eulerPoly_hasAPGaps` from S2 ACT).
* `decide` / `interval_cases` for the `k = 5` concrete witness
  (`5, 11, 17, 23, 29` primality follows from kernel reduction).

**Next**: S4 PREP — Bunyakovsky-style axiom for `d > 0`. The S3b PREP §6.1
recommendation is to **drop the cubic-growth claim** (heuristically false:
prime density for irreducible quadratic `f(n)` is ~`1/log n`, giving
logarithmic-not-cubic growth) and replace with a Bunyakovsky-conjectural
unbounded-length axiom. Out of scope for S3 ACT.

## (Historic) S2 ACT (researcher-5, 2026-05-13) — Euler-polynomial witness scaffold

**Outcome**: progress — new file `proofs/Proofs/Erdos455OQ04.lean`
(~80 LOC, 2 defs + 1 structure + 2 theorems, **0 sorries, 0 axioms**)
landed as the verbatim transfer of S2 PREP §1 (PR #18540) minus the
deferred `apGap_odd_length_le_three` parity-bound. Concretely closes
the parent's `openQuestions[3]` at length 40 via Euler's
`n² + n + 41` polynomial, which has constant second-difference `d = 2`
and is prime for all `n < 40`.

Insertion in `proofs/Proofs.lean`: one new `import Proofs.Erdos455OQ04`
line, alphabetic between `Erdos454ProblemAristotle` and
`Erdos455Problem`.

**Counts**:
* `lineCount`: 0 → ~80
* `theoremCount`: 0 → 2
* `defCount`: 0 → 2 (HasAPGaps, eulerPoly) + 1 structure (APGapPrimeSeq)
* `sorryCount`: 0
* `axiomCount`: 0 (zero `axiom` declarations, zero structure-encoded axioms)

**Build status**: pending — worktree `.lake` symlink trap precludes
local Docker build. Doctor/Mechanic verifies on a fresh container.

**Next**: S2b ACT — `apGap_zero_iff_prime_AP` (~10 LOC) +
`apGap_subsumes_monotone` (~15 LOC) + `apGap_odd_length_le_three`
(~30 LOC, requires `Int.even_sub`). All three sorry-free per
state.md's pre-existing analysis.

## (Historic) Iteration 1 (researcher-10, 2026-05-12) — S1 OBSERVE

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
