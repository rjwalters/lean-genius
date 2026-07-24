# Research State: bertrands-postulate-oq-02

## Current State

**Phase**: COMPLETED — all queued structural targets discharged
**Since**: 2026-07-24T00:00:00Z
**Last Updated**: 2026-07-24 (Session 8, researcher-1)
**Iteration**: 8

## Session 8 — Dead-axiom removal + Cramér ⇒ Legendre composition (researcher-1, 2026-07-24)

**Mode**: REVISIT — stale-BLOCKED reactivation. The 2026-06-13 verification
blackout (Docker hung + Aristotle 404) is long over; both queued items were
discharged and Docker-verified this session (3094 jobs, first try).

1. **Dead axiom removed (slug axioms 1 → 0).** `axiom legendre_conjecture`
   (`LegendrePartial.lean:148`) deleted — 0 code uses fleet-wide, as the S6/S7
   audits found. The contradicting `LegendreGapEquivalence.lean` docstring
   claim was stale (the global equivalences quantify over the `Prop`, not the
   axiom); all four stale docstring spots corrected. Gallery
   `src/data/proofs/legendre-partial/meta.json` updated
   (`meta.axiomCount` 2 → 1, ofReduceBool only; `leanFile.axiomCount` 1 → 0).
2. **S5-ACT-A + B + C all DONE** in NEW `proofs/Proofs/CramerImpliesLegendre.lean`
   (229 LOC, 0 axioms, 0 sorries): `CramerConjecture` as a `Prop`; analytic
   estimate `C·(log x)² ≤ √x − 1` eventually (via Mathlib
   `isLittleO_log_rpow_rpow_atTop`); Cramér ⇒ sqrt gap bound above a
   threshold; and the compositions `cramer_implies_legendre_eventually`,
   `cramer_exceptions_finite`, `cramer_reduces_legendre_to_finite`
   (Cramér reduces Legendre to finitely many explicit cases — the honest
   strongest form, since Cramér's constants are existential). Enabled by
   extracting iter-6's large-`n` branch as `legendreAt_of_sqrt_gap_above` in
   `LegendrePrimeGapSqrtBoundSuffices.lean` (refactor, no statement changes).

**Why COMPLETED**: the iter-3..7 roadmap (Sub-Milestones A, B, B+, dead-axiom
removal) is fully discharged; the only listed remainder (S6, computational
n = 21..50) is explicitly low-leverage enumeration. Reopen bar: materially new
mechanism (e.g. an unconditional BHP-strength gap bound — far beyond current
Mathlib analytic NT). Follow-up questions generated: 0 (candidates fail the
tractability bar; siblings oq-03/oq-04 cover Bertrand-strengthening). Memo:
`sessions/2026-07-24-iter8-dead-axiom-removal-cramer-composition.md`.

---

> **Status set `blocked` (2026-06-13).** After the S7 leanFiles correction, the
> only remaining work is build-dependent and unbuildable today (verification
> blackout: Docker hung + Aristotle 404): (1) remove the dead `legendre_conjecture`
> axiom (`LegendrePartial.lean:148`, axiom 1→0 — needs a build to confirm the
> sibling docstring's usage claim is stale), (2) the S5-ACT-A hard analytic half
> (conditional per the Cramér-bound obstacle). Depth-first `claim-random` kept
> re-handing this RICH slug out post-sync; `blocked` stops the no-op re-claim
> churn until Docker recovers. Core formalization is 0-sorry.

## Session 7 — S7 STATE-SYNC — leanFiles drift correction (researcher-1, 2026-06-13)

**Mode**: STATE-SYNC (tracker-only; no Lean touched).

**Drift fixed.** The research JSON `leanFiles` listed the **wrong files
entirely** — `BertrandsPostulate.lean` + the `BertrandsPostulateOQ03*`
family (nearly identical to the `bertrands-postulate-oq-03` sibling's list),
and **none** of this slug's actual deliverables. Every commit tagged
`research(bertrands-postulate-oq-02)` (S4-ACT-α #22593, iter6 S5-ACT-B′ #22905,
S6 audit #22999) touches the **`Legendre*.lean`** files. Corrected `leanFiles`
to the true set, at canonical origin/main counts:

| File | LOC (wc+1) | thm | def | sorry | axiom |
|------|-----------:|----:|----:|------:|------:|
| `LegendrePrimeGapSqrtBoundSuffices.lean` | 268 | 8 | 1 | 0 | 0 |
| `LegendreGapEquivalence.lean` | 213 | 15 | 6 | 0 | 0 |
| `LegendrePartial.lean` | 166 | 21 | 3 | 0 | 1 |

Slug totals: **0 sorries, 1 axiom** (the `legendre_conjecture` axiom in
`LegendrePartial.lean:148`, flagged dead by S6 #22999).

**Catch-up since Session-6 head:** iter6 S5-ACT-B′ (#22905,
`prime_gap_sqrt_bound_above_implies_legendre`, eventually-suffices form) and
the S6 dead-axiom audit (#22999) both merged after this state.md's head.

**Dead-axiom note (deferred).** `legendre_conjecture : LegendreConjecture`
(LegendrePartial.lean:148) assumes the OPEN conjecture and has **0 code uses**
fleet-wide — grep finds only docstring mentions in the sibling Legendre files
and a *separate* same-named axiom in `BertrandsPostulateOQ03.lean:194`.
Removal (axiom 1→0) is the right next ACT, BUT `LegendreGapEquivalence.lean`'s
docstring (lines 38, 197) *claims* it uses `Legendre.legendre_conjecture`,
contradicting the 0-use grep. Resolve + build-verify when Docker recovers
(verification blackout 2026-06-13: Docker hung, Aristotle 404) rather than
blind-shipping an axiom deletion that could silently break the build.

Files touched (2): this state.md block + JSON `leanFiles` / `currentState`.

---

## Session 6 — Iter 6 S5-PREP-2 — Cramér⇒Legendre bridging gap audit (researcher-9, 2026-06-10, T+4d post-iter-5)

**Goal**: pre-flight audit of the iter-5 picker's claim that "the route
Cramér ⇒ Legendre cleanly factors through `prime_gap_sqrt_bound_implies_legendre`"
before committing the +200-250 LOC `CramerImpliesLegendre.lean` ACT.

**Method**: derive the type signature of each composition step from the
existing iter-5 theorem hypothesis (`PrimeGapSqrtBound: ∀ k`) and Cramér's
conjecture (`∃ C k₀, ∀ k ≥ k₀, …`), check whether they compose.

**Finding**: the iter-5 theorem's `∀ k` hypothesis **does not directly accept
Cramér's `∀ k ≥ k₀` output**. The asymptotic Cramér bound does not extend
to small `k` (e.g. `1·(log 2)² ≈ 0.48 < 1 = p₁ - p₀`, so even C = 1 fails
at `k = 0`). A refined iter-5 variant taking the gap bound only for `p_k ≥ M`
is needed for the composition to typecheck.

**Numerical analysis** (computed via Python; see §3 of the session memo):

| C (Cramér constant)  | smallest p with `C·log²p ≤ 2√p+1` | k₀ ≈ π(p) − 1 |
|----------------------|----------------------------------:|--------------:|
| 1.0     (original)   |                              121  |          29   |
| 1.1229  (Granville)  |                              358  |          70   |

For `n ≥ 21`, iter-5 picks `k(n) := Nat.findGreatest (λ k, p_k ≤ n²) n²`,
which satisfies `k(n) ≥ 84`. Both numerical thresholds (29 and 70) are
≤ 84, so **legendre-partial's existing `n = 1..20` coverage suffices** to
discharge the finite tail — for `C = 1`, even `n ≤ 15` covers it. No
mathematical gap.

**Recommendation (S5-ACT-B′, next picker's slot)**: add the refined variant
inside `LegendrePrimeGapSqrtBoundSuffices.lean`:

```lean
theorem prime_gap_sqrt_bound_above_implies_legendre
    (M : ℕ)
    (h_gap_above : ∀ k, M ≤ Nat.nth Nat.Prime k →
                   Nat.nth Nat.Prime (k+1) - Nat.nth Nat.Prime k
                     ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1)
    (h_legendre_below : ∀ n, 1 ≤ n → n^2 < 2*M → LegendreAt n) :
    LegendreConjecture
```

Proof: case `n² < 2·M` direct from `h_legendre_below`; case `n² ≥ 2·M`
applies Mathlib's `Nat.bertrand` at `n²/2` to obtain a prime `q` with
`n²/2 < q ≤ n²`, hence the iter-5-style `k` satisfies `p_k ≥ q > n²/2 ≥ M`,
unlocking `h_gap_above`. iter-5's `prime_gap_sqrt_bound_implies_legendre`
is recovered as the corollary at `M = 0` (gap-above-0 ≡ gap-for-all-k;
`n² < 0` vacuous). Estimated +85 LOC, 0 new axioms.

**Picker matrix (post-iter-6)**:

| ID         | Description                                       | Status                       |
|------------|---------------------------------------------------|------------------------------|
| S4-ACT-α   | `prime_gap_sqrt_bound_implies_legendre` (one-way) | ✅ DONE (iter 5)             |
| S5-PREP-2  | Cramér-bridge audit + refined-iter-5 spec         | ✅ DONE (**iter 6**)         |
| S5-ACT-B′  | Implement refined-iter-5 variant                  | ⏳ **Newly recommended**     |
| S5-ACT-A   | Real-analytic estimate C·log²p ≤ 2√p+1            | ⏳ Newly specified            |
| S5-ACT-B   | Cramér statement + ⇒ gap-above-threshold          | ⏳ Newly specified            |
| S5-ACT-C   | Compose Cramér ⇒ Legendre                         | ⏳ Awaits B′, A, B            |
| S6         | Computational extension to n ≥ 21                 | ⏳ Low leverage               |

**Next picker's slot (recommended)**: S5-ACT-B′ — refined-iter-5 inside
`LegendrePrimeGapSqrtBoundSuffices.lean`. Smallest unit that unblocks the
Cramér ⇒ Legendre composition; type signature fixed in §5 of the session
memo; ~85 LOC; 0 new axioms expected.

**Deliverables (this PR)**:

1. NEW session memo `sessions/2026-06-10-iter6-s5-prep-cramer-bridge-gap.md`.
2. `state.md`: this Session 6 prepend.
3. `meta.json` + `src/data/research/problems/bertrands-postulate-oq-02.json`:
   `currentState.phase` ACT → PREP; `currentState.iteration` 5 → 6;
   `currentState.since`/`focus`/`nextAction` updated; `attemptCounts.total`
   5 → 6; `attemptCounts.currentApproach` 3 → 4;
   `knowledge.insights` += four new entries (quantifier mismatch; numerical
   thresholds; refined-iter-5 spec; legendre-partial sufficiency).
4. `knowledge.md`: append Iteration 6 Log.

**Honest size**: ~330 LOC markdown + ~25 LOC JSON diff. No Lean. Same shape
as iter-4 PREP-1 — a pre-flight audit that spares the next ACT picker the
structural-redesign cleanup they'd otherwise hit at Lean compile time.

---



## Session 5 — Iter 5 S4-ACT-α DONE (researcher-1, 2026-06-06, T+1d post-iter-4 PREP-1)

**Goal**: implement the corrected S4-ACT-α identified by iter 4 PREP-1: the
salvageable one-way implication

  `(∀ k, p_{k+1} - p_k ≤ 2 · √p_k + 1) ⟹ LegendreConjecture`.

**Method**: new file `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`
(227 LOC), axiom-free. Strategy:

- Case `n = 1`: prime `2` directly witnesses `LegendreAt 1`.
- Case `n ≥ 2`: take `k = Nat.findGreatest (fun k => p_k ≤ n²) n²`,
  the index of the largest prime ≤ n². Use:
  - `not_prime_sq_of_ge_two` to get `p_k < n²` strictly (n² composite for n ≥ 2);
  - `nth_prime_ge` + `Nat.findGreatest_is_greatest` to get `p_{k+1} > n²`;
  - the gap-bound hypothesis + `Nat.sqrt_lt'` to get `p_{k+1} < (n+1)²`.

**Deliverable**: `LegendrePrimeGapSqrtBoundSuffices.lean` — 227 LOC,
0 axioms, 0 sorries, **Docker build verified**:

```
✔ [3074/3074] Built Proofs.LegendrePrimeGapSqrtBoundSuffices (6.8s)
Build completed successfully (3074 jobs).
```

**Public surface**:

| Name | Type | Notes |
|------|------|-------|
| `PrimeGapSqrtBound` | `Prop` | Definition: `∀ k, p_{k+1} - p_k ≤ 2·√p_k + 1` |
| `not_prime_sq_of_ge_two` | aux lemma | `2 ≤ n → ¬ Nat.Prime (n^2)` |
| `nth_prime_ge` | aux lemma | `k + 2 ≤ Nat.nth Nat.Prime k` |
| **`prime_gap_sqrt_bound_implies_legendre`** | main thm | `PrimeGapSqrtBound → LegendreConjecture` |
| `prime_gap_sqrt_bound_implies_gap_form` | corollary | gap form (via iter-2) |
| `prime_gap_sqrt_bound_implies_distance_form` | corollary | distance form (via iter-2) |
| `prime_gap_sqrt_bound_implies_halfOpen_form` | corollary | half-open form (via iter-2) |

**Asymmetry preserved in docstring**: the file's module docstring records
that the converse direction (`Legendre ⟹ gap bound`) is **not** provable
from `LegendreConjecture` alone (see iter 4 PREP-1 audit memo). The
asymmetry is visible to any future reader directly from the Lean source.

**Honest size**: ~230 LOC Lean + ~250 LOC markdown + ~15 lines JSON diff.
The mathematical heavy lifting was done by iter 4 PREP-1 (identifying the
direction that survives). This iteration is the implementation.

**Picker matrix (post-iter-5)**:

| ID | Description | Status |
|---|---|---|
| S4-ACT-α | `prime_gap_sqrt_bound_implies_legendre` (one-way) | ✅ **DONE (iter 5)** |
| S4-iff (original) | `legendre_iff_primeGap` (proposed iff) | 🚫 ANTI-CANDIDATE (PREP-1 verdict, permanent) |
| S5 | Cramér ⇒ Legendre (sub-Milestone A) | ⏳ **Newly tractable** via composition with iter-5's theorem |
| S6 | Computational extension to `n = 21, …, 50` (sub-Milestone C) | ⏳ low-leverage padding |

**Next picker's slot (recommended)**: S5 ACT — Cramér ⇒ Legendre. The route
factors cleanly through iter-5's theorem:

```
Cramér's conjecture
  ⟹ (for sufficiently large k) p_{k+1} - p_k ≤ C·(log p_k)² ≤ 2·√p_k + 1
  ⟹ LegendreConjecture (via prime_gap_sqrt_bound_implies_legendre)
```

with legendre-partial covering the finite small-k tail. Estimated +200-250
LOC, 0 new axioms expected (only Cramér as hypothesis).

**Deliverables (this PR)**:

1. NEW Lean file `proofs/Proofs/LegendrePrimeGapSqrtBoundSuffices.lean`.
2. NEW session memo `sessions/2026-06-06-iter5-s4-act-alpha-sqrt-bound-suffices.md`.
3. `proofs/Proofs.lean`: import line added for the new file.
4. `state.md`: this Session 5 prepend.
5. `meta.json` + `src/data/research/problems/bertrands-postulate-oq-02.json`:
   `currentState.iteration` 4 → 5; `phase`/`since`/`focus`/`nextAction` updated;
   `attemptCounts.total` 4 → 5; `attemptCounts.currentApproach` 2 → 3;
   `knowledge.builtItems` += new file entries; `knowledge.insights` +=
   iter-5 result; `lastUpdate` 2026-06-05 → 2026-06-06.
6. `knowledge.md`: append Iteration 5 Log.

---



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

## iter6 S5-ACT-B′ — eventually-suffices theorem (researcher-2, 2026-06-12)

Landed `prime_gap_sqrt_bound_above_implies_legendre (M)` in
`LegendrePrimeGapSqrtBoundSuffices.lean`: the sqrt prime-gap bound need only
hold for primes `p_k ≥ M`, with `n² < 2M` cases handled by a separate
`h_legendre_below` hypothesis. New ingredient vs iter-5: `Nat.bertrand` +
`Nat.nth_count`/`Nat.le_findGreatest`/`Nat.nth_monotone` to show the largest
prime `≤ n²` is `≥ M` when `n² ≥ 2M`. The old global theorem
`prime_gap_sqrt_bound_implies_legendre` is now its `M = 0` corollary;
downstream equivalence corollaries unchanged. **Docker: 3074 jobs, first try;
0 sorries, 0 new axioms.** Memo:
`sessions/2026-06-12-iter6-s5-act-b-prime-above-suffices.md`.
