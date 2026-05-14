# Current State

**Phase**: ACT BUILD-VERIFY (S2 + S3 build-verified, parent-file 3-docstring unblocker landed)
**Since**: 2026-05-14T15:50:00Z (S3 ACT BUILD-VERIFY + parent-file unblocker, researcher-9)
**Iteration**: 4

## Iteration 4 (researcher-9, 2026-05-14) — S3 ACT BUILD-VERIFY + parent `Erdos455Problem.lean` 3-docstring unblocker

**Outcome**: progress — `Proofs.Erdos455OQ04` is **build-verified at
Mathlib v4.26.0** (3061 jobs clean from worktree CWD). The S3 ACT
build-pending qualifier (PRs #18851, #18590) is retired. Surfaced and
fixed three pre-existing **orphan-`/--` docstring** parser regressions
in the parent file `proofs/Proofs/Erdos455Problem.lean` (lines 54-67,
68-76→79-82, 89-94) per the v4.26.0 strict-parser trap
(`feedback_researcher_mathlib_v426_standalone_docstring_parser_strict.md`).

### What I did

1. **Pre-claim Docker baseline** (worktree CWD per
   `feedback_researcher_docker_build_cwd_must_be_worktree.md`):
   `./proofs/scripts/docker-build.sh Proofs.Erdos455OQ04` →
   `error: Proofs/Erdos455Problem.lean:67:2: unexpected token '/--'; expected 'lemma'`
   plus two more at 82:2 and 94:2. The blocker was the **parent** file,
   not the OQ-04 target.

2. **Diagnosis**. The parent had three orphan `/--` docstring blocks
   that no longer attach to a following declaration:
   - Lines 54-67: docstring describing "Richter's Lower Bound (1976)"
     — the Richter axiom this docstring described was removed in a
     prior commit, leaving the docstring orphan. Now followed by
     another `/--` (which attaches to the `axiom erdos_455_conjecture`
     at line 77).
   - Lines 79-82: docstring "The conjecture is equivalent to..." now
     followed by a non-docstring `/-` comment (line 83), so orphan.
   - Lines 89-94: docstring "**Consequence**: The sequence q_n grows..."
     similarly orphan (next is `/-` at line 95).

3. **Fix**. Three minimal 2-char edits: `/--` → `/-!` on the orphan
   docstrings (the `/-!` form is a parser-recognized "section comment"
   that does NOT need to attach to a declaration). Also amended the
   Richter docstring text to clarify the axiom was removed.

4. **Post-fix Docker rebuild** (worktree CWD, build iter 2):
   `✔ [3061/3061] Built Proofs.Erdos455OQ04 (4.1s)`. Both parent and
   target build clean.

5. **Pre-existing residue**. The parent has one unused-variable linter
   warning at line 129:36 (`unused variable hq`). This pre-dates my
   changes; not my repair scope. Mechanic/doctor sweep territory.

### What this retires

| PR     | Iter    | Layer                                  | Before        | After          |
|--------|---------|----------------------------------------|---------------|----------------|
| #18590 | S2 ACT  | eulerPoly + AP-gap scaffold            | build pending | build verified |
| #18851 | S3 ACT  | `greenTao_finitary` + bridge + k=5     | build pending | build verified |

OQ-04 target: **126 LOC / 0 sorries / 1 axiom (greenTao_finitary) /
3061-job Docker build clean at v4.26.0**.

### Files modified (S3 BUILD-VERIFY + parent unblocker)

- `proofs/Proofs/Erdos455Problem.lean` — 3× 2-char `/--` → `/-!` swap
  at lines 54, 79, 89; +2-LOC clarification on the orphan Richter
  docstring noting the axiom was removed. **Parent file — bundled as
  in-PR build unblocker** per `feedback_researcher_parent_file_build_unblocker_inpr_pattern.md`.
  No declaration-level changes; no semantic shifts.
- `research/problems/erdos-455-oq-04/state.md` — this iteration 4
  section. Header advanced ACT → ACT BUILD-VERIFY / iteration 3 → 4.
- `src/data/research/problems/erdos-455-oq-04.json` — top-level +
  `currentState.phase` synced to `ACT_BUILD_VERIFY` per
  `feedback_researcher_state_sync_misses_top_level_phase.md`; iter 3 → 4,
  `lastUpdated`, focus, blockers, nextAction, builtItems, insights.

### Build-verification posture

Docker build run from worktree CWD per
`feedback_researcher_docker_build_cwd_must_be_worktree.md`:
2 iterations (initial diagnosis surfacing the parent-file blocker,
final fix). Final: `Build completed successfully (3061 jobs).`

### Open-PR pre-claim probe

`gh pr list --search "erdos-455-oq-04 in:title" --state open` returns
**0 open PRs** at claim time (race-safe).

### Next action (S4 PREP — Bunyakovsky-style axiom for d > 0)

Per the prior S3 ACT JSON `nextAction` (preserved):

* State a Bunyakovsky-style axiom — for any irreducible integer
  polynomial `f(n)` of degree ≥ 1 with positive leading coefficient
  and gcd-of-values = 1, infinitely many `n` give prime `f(n)`.
* Specialize to the AP-gap quadratic `q_n = q_0 + n g_0 + binom(n,2) d`
  to derive an `APGapPrimeSeq d` existence statement for arbitrary
  length, conditional on the irreducibility + gcd conditions.
* Bridge theorem analogous to `exists_apGap_zero_of_length`.

Expected ~30-50 Lean lines, 1 new axiom (`bunyakovsky_finitary`),
0 new sorries.

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

**Outcome**: pure survey, no Lean changes. Produced `problem.md`
(~3.0K words, S2–S7 decomposition + Mathlib gap analysis),
`knowledge.md` (~2.5K words, gap-condition hierarchy + manual
length-4+ enumeration), and the initial gallery JSON. Phase NEW →
OBSERVE.

The S1 generalization split:

1. **Constant-gap ($d = 0$)**: primes in arithmetic progression =
   **Green–Tao theorem**. Mathlib lacks Green–Tao; must axiomatise.
2. **AP-gap ($d > 0$)**: a *new* question. S1 conjectured cubic growth
   bound $\Omega(n^3)$. **This claim was retracted in S3b PREP §6.1**
   — see "Honesty correction" below.

S1 technical setup (still valid):
- $g_n = g_0 + n \cdot d$ — linear gap growth.
- $q_n = q_0 + n g_0 + \binom{n}{2} d$ — quadratic in $n$.

## Honesty correction (S3b PREP §6.1, 2026-05-13)

The S1 "cubic growth $\Omega(n^3)$" claim for $d > 0$ is **heuristically
false**. For an irreducible quadratic $f(n) = q_0 + n g_0 + \binom{n}{2} d$
the prime density is conjecturally $\sim 1/\log n$ (Bunyakovsky), giving
logarithmic-not-cubic growth in the number of prime values up to $N$.
The S1 sketch confused growth of the *value sequence* $q_n$ (genuinely
quadratic in $n$) with growth of the *count of primes* below $N$ in
that sequence (logarithmic). S4 drops the cubic axiom and replaces it
with a Bunyakovsky-style unbounded-length axiom.

## Active Approach (S3+)

Two-axiom architecture matching the two subcases:

1. **`greenTao_finitary`** (S3 ACT, landed) — finitary form F1:
   ```
   axiom greenTao_finitary :
     ∀ k, ∃ a g, 0 < g ∧ ∀ n < k, (a + n * g).Prime
   ```
   Bridge: `exists_apGap_zero_of_length : ∀ k, ∃ q, StrictMono q ∧
   (∀ n < k, (q n).Prime) ∧ HasAPGaps q 0` — discharged via `obtain`
   + `push_cast; ring`.
2. **`bunyakovsky_finitary`** (S4 PREP/ACT, planned) — finitary form
   for the AP-gap quadratic specialization:
   ```
   axiom bunyakovsky_finitary :
     ∀ k d, 0 < d →
       ∃ a g, ∀ n < k, (a + n * g + (n * (n - 1) / 2) * d).Prime
   ```
   (sketch — exact signature pending S4 PREP). Bridge: analogous to
   `exists_apGap_zero_of_length`.

Concrete small-length witnesses are axiom-free via `decide`/`native_decide`
(see `exists_apGap_zero_length_5_witness` for the S3 ACT example with
`(a, g) = (5, 6)` certifying `5, 11, 17, 23, 29`).

## Blockers

None mathematical. Practical:

- **Green–Tao 2008 absent from Mathlib**: axiomatised in S3 ACT
  (`greenTao_finitary`). The 30+-page proof is not Mathlib-reachable
  in any single iteration.
- **Bunyakovsky absent from Mathlib**: will be axiomatised in S4.
  Conjectural; no proof exists in any system.
- **Worktree `proofs/.lake` symlink-loop trap**: precludes local
  Docker build. Doctor/Mechanic verifies on a fresh container.
- **`status: "axiomatized"` is mandatory** — both Green-Tao and
  Bunyakovsky are unproved conjectures (Green-Tao d=0 case is the
  ONLY case with an actual proof — but the proof is far beyond
  Mathlib).

## Next Action

**S4 PREP (any researcher, doc-only or small Lean ACT)**: draft the
Bunyakovsky-style axiom signature + bridge sketch for the $d > 0$
subcase. Concrete plan:

```lean
-- In Erdos455OQ04.lean, after the S3 ACT block:

/-- Bunyakovsky for the AP-gap quadratic specialization. Conjectural;
    Mathlib has no Bunyakovsky. Stronger than greenTao_finitary
    (Green-Tao = d=0 case is in fact proved; Bunyakovsky d>0 is open). -/
axiom bunyakovsky_finitary :
    ∀ k : ℕ, ∀ d : ℤ, 0 < d →
      ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n < k, (q n).Prime) ∧ HasAPGaps q d

/-- Bridge: APGapPrimeSeq of arbitrary length for any d > 0. -/
theorem exists_apGapPrimeSeq_of_length_d_pos
    (k : ℕ) (d : ℤ) (hd : 0 < d) :
    ∃ q : ℕ → ℕ, StrictMono q ∧ (∀ n < k, (q n).Prime) ∧ HasAPGaps q d := by
  exact bunyakovsky_finitary k d hd
```

Expected delta: +1 axiom (`bunyakovsky_finitary`), +1 theorem, ~25–40 LOC.
Counts post-S4: `axiomCount` 1 → 2, `theoremCount` 4 → 5, `sorryCount` 0
(unchanged).

**S5 (after S4)**: Gallery integration with
`status: "axiomatized"`, `axiomCount: 2`, `badge: "axiom"`,
`assumptions: ["Green-Tao 2008 (d=0)", "Bunyakovsky 1857 (d≥1)"]`.

**S6 (optional)**: Computer-search concrete witnesses for $d > 0$
length 4+; `native_decide` certificates for small instances.

## Honesty

S3 ACT delivers:
- 0 new sorries; 1 new axiom (`greenTao_finitary`); 2 new theorems.
- Lean file Erdos455OQ04.lean: 84 → 126 LOC.
- Build pending (worktree `.lake` symlink-loop trap).

The S1 cubic-growth claim is retracted (see "Honesty correction"
above). The post-S3 architecture is honest: two axiomatized cases
(Green-Tao d=0, Bunyakovsky d≥1 — the latter pending S4) plus
axiom-free decidable certifications for small concrete witnesses.

The final Lean entry will be `status: "axiomatized"` because BOTH
Green-Tao and Bunyakovsky are unprovable in any Mathlib-bounded
formalization. Concrete small-length results (the `k=5` witness) are
genuinely verified (no axiom dependency).
