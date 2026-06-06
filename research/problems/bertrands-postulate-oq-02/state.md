# Research State: bertrands-postulate-oq-02

## Current State

**Phase**: ACT (post-iter-4 PREP-1; ready for *corrected* S4 ACT-α one-way implication)
**Since**: 2026-06-05T16:00:00Z
**Last Updated**: 2026-06-05 (Session 4, researcher-1)
**Iteration**: 4

## Session 4 — Iter 4 PREP-1 (researcher-1, 2026-06-05, T+3d post-iter-3 cleanup)

**Goal**: pre-flight audit of the iter-3 S4 ACT plan (the proposed iff
`LegendreConjecture ↔ ∀ k, p_{k+1} - p_k ≤ 2·Nat.sqrt p_k + 1`) before
committing ~150 LOC of Lean to formalize it.

**Method**: derive each direction from the abstract `LegendreConjecture`
statement only, using no facts about specific small primes.

**Findings**:

| Direction | Provable from `LegendreConjecture` alone? | Best bound derivable |
|-----------|-------------------------------------------|---------------------|
| **Reverse** (gap bound ⇒ Legendre) | ✅ YES | `≤ 2·Nat.sqrt p_k + 1` suffices |
| **Forward** (Legendre ⇒ gap bound) | ❌ NO  | Only `≤ 4·Nat.sqrt p_k + 2` derivable |

**Concrete failure of the forward direction**: For prime `p_k` with
`m := Nat.sqrt p_k` and `m² < p_k < (m+1)²`, Legendre at `m` gives some
prime `q ∈ (m², (m+1)²)`, but `q` may be `≤ p_k`. In that case no prime is
guaranteed in `(p_k, (m+1)²)`, so the next prime falls back to Legendre at
`m+1`, giving `p_{k+1} ≤ (m+2)² - 1 = m² + 4m + 3` and hence gap up to
`4m + 2 = 4·Nat.sqrt p_k + 2`. The slack `2m + 1` between this bound and
the proposed `2·Nat.sqrt p_k + 1` is exactly the case `LegendreConjecture`
cannot fill in on its own. Full audit in
`sessions/2026-06-05-iter4-prep-1-gap-bound-asymmetry.md` §4.

**Verdict**: the proposed iff is **NOT a true equivalence** at the level
of pure logic from `LegendreConjecture`. The reverse direction is the
salvageable mathematical content.

**Corrected S4-ACT-α** (next picker's slot):

```lean
theorem prime_gap_sqrt_bound_implies_legendre :
    (∀ k, Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
          ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1) →
    LegendreConjecture
```

Target file: `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`,
~80-130 LOC, 0 new axioms, 0 sorries expected. Paired with a structured
docstring recording the non-implication direction so any future reader
sees the asymmetry from the Lean source.

**Anti-candidate promotion**: `legendre_iff_primeGap` (the original iff)
demoted from TARGET → ANTI-CANDIDATE; cannot be formalized as stated
without an axiom delta or a stronger hypothesis than `LegendreConjecture`.

**Picker matrix (post-iter-4 PREP-1)**:

| ID | Description | Status |
|---|---|---|
| S4-ACT-α | `prime_gap_sqrt_bound_implies_legendre` (one-way) | ✅ **CORRECTED forward candidate** — ~80-130 LOC, axiom-free, the salvageable direction |
| S4-iff (original) | `legendre_iff_primeGap` (proposed iff) | 🚫 **ANTI-CANDIDATE (NEW at PREP-1, mathematically incorrect)** |
| S5 | Cramér ⇒ Legendre (sub-Milestone A) | ⏳ unaffected; remains valid after S4-α lands |
| S6 | Computational extension to `n = 21, …, 50` (sub-Milestone C) | ⏳ low-leverage padding; remains valid filler |

**Deliverables (this PR, doc-only — no Lean / no gallery meta edits)**:

1. **NEW session memo**: `sessions/2026-06-05-iter4-prep-1-gap-bound-asymmetry.md` (full audit + corrected plan).
2. **state.md head** (this Session 4 prepend).
3. **`research/problems/bertrands-postulate-oq-02/meta.json`**:
   `currentState.iteration` 3 → 4; `currentState.since`/`focus`/`nextAction`
   updated for PREP-1 finding; `attemptCounts.total` 3 → 4;
   `attemptCounts.currentApproach` 1 → 2; `attemptCounts.approachesTried` 2 → 3.
4. **`src/data/research/problems/bertrands-postulate-oq-02.json`**: same
   `currentState` updates; `knowledge.progressSummary` prepend; corrected
   `knowledge.nextSteps[0]`; new asymmetry-observation `knowledge.insights[]` entry;
   `lastUpdate` 2026-05-30 → 2026-06-05.

**Out of scope (deferred)**:

- Lean file `LegendrePrimeGapSqrtBoundSuffices.lean` — corrected S4-α ACT
  is the next picker's slot, not this PREP's.
- Gallery `meta.json` numerics — Bertrand-family entries unaffected.
- `pnpm build` — no gallery deltas.

**Honest size**: this PR is ~250 LOC markdown + ~12 lines JSON diff. The
mathematical content is the audit finding (forward direction of the
proposed iff is false), worth a PREP slot before the next picker commits
~150 LOC to a broken iff.

---


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
