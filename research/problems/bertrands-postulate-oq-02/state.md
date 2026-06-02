# Research State: bertrands-postulate-oq-02

## Current State

**Phase**: ACT (post-iter-2 metadata cleanup; ready for S3 ACT Sub-Milestone B+)
**Since**: 2026-06-02T19:30:00Z
**Last Updated**: 2026-06-02 (Session 3, researcher-1)
**Iteration**: 3

## Iteration 3 (2026-06-02T19:30Z, researcher-1): S3 OBSERVE / metadata cleanup (doc-only)

S3 OBSERVE absorbs the iter-2 deliverables (created without `state.md` /
`sessions/` infrastructure) into the canonical session log, fixes
metadata drift, and re-specifies the next ACT target.

### What was missing before this iteration

`research/problems/bertrands-postulate-oq-02/` had `problem.md`,
`feasibility.md`, `knowledge.md`, and `meta.json` — but no `state.md`,
no `sessions/` directory, and `meta.json` was stale at iteration 1
(SURVEY) despite knowledge.md documenting an iter-2 DEEP DIVE on
2026-05-30. The iter-2 work shipped under commit
`c847186b08c` (PR #21322, mistitled "research(qt-multichoose): S3 ACT")
which bundled `LegendreGapEquivalence.lean` (212 LOC, 21 thms/defs,
0 axioms, 0 sorries) with the qt-multichoose deliverables.

### Metadata reconciliation in this iteration

| File | Before iter 3 | After iter 3 |
|------|----------------|---------------|
| `research/problems/bertrands-postulate-oq-02/meta.json` `currentState.iteration` | 1 | 3 |
| `research/problems/bertrands-postulate-oq-02/meta.json` `currentState.phase` | SURVEY | ACT |
| `research/problems/bertrands-postulate-oq-02/state.md` | absent | present (this file) |
| `research/problems/bertrands-postulate-oq-02/sessions/` | absent | created with this S3 file |
| `src/data/research/problems/bertrands-postulate-oq-02.json` top-level `phase` | NEW | ACT |
| `src/data/research/problems/bertrands-postulate-oq-02.json` `currentState.iteration` | 2 | 3 |
| `src/data/research/problems/bertrands-postulate-oq-02.json` `currentState.lastUpdate` | missing | 2026-06-02T19:30:00Z |

No Lean changes in this iteration; gallery counts and axiom posture
unchanged.

### Iter-2 deliverable summary (absorbed into this state.md)

**Date**: 2026-05-30 (researcher-1, Session 2; committed in PR #21322).

**Output**: `proofs/Proofs/LegendreGapEquivalence.lean` — 212 LOC,
21 theorems/lemmas/defs, 0 axioms, 0 sorries. Build verified.

**Content**: Four pointwise equivalences of Legendre's Conjecture
(original / gap / distance / half-open), reducing the statement to the
identity `(n+1)² = n² + 2n + 1` plus `omega`. Three global form
equivalences (`legendre_iff_gap_form`, `legendre_iff_distance_form`,
`legendre_iff_halfOpen_form`) lift the pointwise versions to universal
quantifiers. Five sample transferrals (`legendre_gap_1`,
`legendre_gap_5`, `legendre_gap_20`, `legendre_distance_10`,
`legendre_halfOpen_15`) confirm `LegendrePartial`'s base cases hold in
each equivalent form.

**Mathematical posture**: equivalences only. No new progress on the
open conjecture. The value is *organizational* — providing the gallery
with Lean records of the "Legendre = prime in `(n², n² + 2n]`" and
"Legendre = prime-distance ≤ 2n" reformulations that the literature
states informally.

**Axiom delta**: 0 new (still inherits 1 axiom `legendre_conjecture`
from `LegendrePartial.lean`).

**Why no gallery entry**: `LegendreGapEquivalence.lean` does NOT have a
corresponding `src/data/proofs/` directory. This is the standard
gallery-vs-research split — research deliverables live in
`proofs/Proofs/` but only graduate to the gallery (`src/data/proofs/`)
when they're judged "publishable." Pure equivalences are typically not
graduated unless paired with a non-trivial consequence. Reasonable;
keeps the gallery focused on landmark facts.

## Blockers

### B1 — No blockers (clean state)

No INFRA blockers (Docker corruption is a different file's concern;
this slug builds cleanly via standard `lake build` on a healthy host).

No content blockers — Sub-Milestone B+ (the next ACT target) is
specified and tractable; its building block
(`nth_prime_succ_le_of_prime_gt`) is already in `Proofs.PrimeGapBounds`.

## Next Action

**S4 ACT — Sub-Milestone B+ — `LegendreConjecture` ↔ prime-gap bound.**

State and prove:

```lean
theorem legendre_iff_primeGap :
    LegendreConjecture ↔
      ∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
        ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1
```

(Statement modulo formal-Lean tweaks for `Nat.nth Nat.Prime` API and the
0-case base.)

**Building blocks (already in repo)**:
- `Nat.nth Nat.Prime` — Mathlib (`Mathlib.Data.Nat.Prime.Nth`,
  already imported in `LegendreGapEquivalence.lean`).
- `Nat.sqrt` — Mathlib core.
- `nth_prime_succ_le_of_prime_gt` — `proofs/Proofs/PrimeGapBounds.lean:123`
  (already in the repo; used by Sub-Milestone B+ per knowledge.md).

**Outline of the proof** (per knowledge.md §"Sub-Milestone B"):
- **Forward** (`legendre → gap bound`): for each `k`, let
  `n := Nat.sqrt (Nat.nth Nat.Prime k)`. The prime `Nat.nth Nat.Prime k`
  lies in `[n², (n+1)²)` by the `Nat.sqrt` characterization. Apply
  Legendre at `n` (existence of prime in `(n², (n+1)²)`) — call this
  prime `q`. Then `q > Nat.nth Nat.Prime k` (since
  `q > n² ≥ Nat.nth Nat.Prime k`); by minimality of the next prime
  enumeration, `Nat.nth Nat.Prime (k+1) ≤ q < (n+1)² = n² + 2n + 1`.
  Hence `Nat.nth Nat.Prime (k+1) - Nat.nth Nat.Prime k ≤ 2n + 1 = 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1`.
- **Reverse** (`gap bound → legendre`): for each `n ≥ 1`, find the
  largest `k` with `Nat.nth Nat.Prime k ≤ n²` (exists by
  `Nat.nth_prime_le_iff` / `Nat.exists_prime_le`). Apply the gap bound:
  `Nat.nth Nat.Prime (k+1) ≤ n² + 2*Nat.sqrt(n²) + 1 = n² + 2n + 1 = (n+1)²`.
  If `Nat.nth Nat.Prime (k+1) > n²` (which holds by choice of `k`),
  then this is the desired prime in `(n², (n+1)²]`. The strict-upper
  edge `< (n+1)²` is salvaged by the half-open form
  (`LegendreHalfOpenAt`) — or fold via `legendreAt_iff_halfOpen`.

**Estimated size**: +100 to +180 LOC in a new file
`proofs/Proofs/LegendrePrimeGapEquivalence.lean` (separate file to keep
the equivalence-stack modular). 0 new axioms expected. 0 sorries
expected.

**Risks**:
- `Nat.sqrt` properties: `Nat.sqrt (n^2) = n`, `Nat.sqrt_lt_iff`,
  `Nat.lt_succ_sqrt'` etc. — needs careful Mathlib lookup.
- `Nat.nth Nat.Prime k`'s "next prime" characterization vs. the
  existing `nth_prime_succ_le_of_prime_gt`. Verify the lemma's exact
  signature before committing.
- Base case `k = 0` (which prime is "Nat.nth Nat.Prime 0"? Probably
  `2`; check Mathlib). May need separate handling.

### Then S5 ACT — Sub-Milestone A — "Cramér implies Legendre"

Per knowledge.md §"Sub-Milestone A": state Cramér's conjecture
(`∃ C, ∀ k, p_(k+1) - p_k ≤ C * (log p_k)^2`) as a hypothesis,
combine with the iter-2 gap-form equivalence to derive
`LegendreConjecture` for sufficiently large `n`. Bridge to
`legendre-partial`'s computational base cases for the small-n tail.

Size: +100-150 LOC. Could be done before or after S4; independent.

## Attempt Counts

- Total iterations: 3 (S1 SURVEY 2026-05-30; S2 ACT 2026-05-30; S3
  OBSERVE 2026-06-02)
- Current approach iterations: 1 (S3 is a metadata-cleanup OBSERVE,
  separate "approach" from S2 ACT)
- Approaches tried: 2 (SURVEY/scoping; ACT via equivalence reformulation)

## References

- `proofs/Proofs/LegendreGapEquivalence.lean` — iter-2 deliverable
  (212 LOC, 0 axioms).
- `proofs/Proofs/LegendrePartial.lean` — base computational verifications;
  declares the `legendre_conjecture` axiom.
- `proofs/Proofs/PrimeGapBounds.lean:123` — `nth_prime_succ_le_of_prime_gt`
  (key lemma for S4 Sub-Milestone B+).
- `research/problems/bertrands-postulate-oq-02/knowledge.md` —
  full survey + Sub-Milestone roadmap.
- `research/problems/bertrands-postulate-oq-02/problem.md` — formal
  statement of Legendre's Conjecture.
- Granville, A. "Harald Cramér and the distribution of prime numbers,"
  *Scand. Actuar. J.* (1995). Discusses the equivalence
  Legendre ↔ gap bound `g(p_k) ≤ 2√p_k + 1`.
- Tao, T. "Structure and randomness in the prime numbers" (2007).
  Notes that Legendre's Conjecture is strictly stronger than what RH
  implies for prime gaps.
