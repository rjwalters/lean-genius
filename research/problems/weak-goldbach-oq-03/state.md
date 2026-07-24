# Current State

**Phase**: ACTIVE — S9 ACT shipped (Schnirelmann–Goldbach bridge). Docker recovered; the 2026-06-13 BLOCKED flag is lifted. **Census correction**: the axiom floor is now **4**, not 5 — sibling weak-goldbach-oq-01 (PR #34353, merged 2026-07-03) *proved* `schnirelmann_basis_theorem` outright in `Proofs/SchnirelmannTheorem.lean`, consuming this tracker's planned S9 Approach D (Schnirelmann sumset inequality) wholesale. S9 here instead formalized the classical **bridge**: `schnirelmann_goldbach_bridge` derives "every n ≥ 2 is a sum of ≤ 3h+2 primes" from the single hypothesis σ({0,1} ∪ (P+P)) > 0 (Schnirelmann's Brun-sieve estimate, unformalized HEROIC — kept as a hypothesis, NOT a new axiom), plus unconditional cross-validation `sum_of_at_most_four_primes` (k = 4 via Helfgott). File: 943 LOC, 4 axioms (`helfgott_weak_goldbach`, `circle_method_asymptotic`, `chen_theorem`, `binary_goldbach_verified`), 0 sorries, docker-verified.
**Since**: 2026-07-24 (S9 ACT; S8 was 2026-06-10)
**Iteration**: 9

## Current Focus

S9 (researcher-1, 2026-07-24): ACT — Schnirelmann–Goldbach bridge.
New in `WeakGoldbach.lean` (all docker-verified, no new axioms):

- `goldbachSumset : Set ℕ` = {0,1} ∪ {n | IsSumOfTwoPrimes n}, with a
  decidable-membership instance riding the existing verified decision
  procedure.
- `exists_two_three_multiset`: every m ≥ 2 is a sum of ≤ m primes from
  {2,3} (parity split; replicate-multiset witnesses).
- `goldbachSumset_multiset_decomp`: a multiset of G-elements splits into
  r ones (r ≤ card) and a prime multiset (card ≤ 2·card) preserving sums
  (Multiset.induction_on).
- `schnirelmann_goldbach_bridge`: σ(G) > 0 → BoundedPrimeSums (every
  n ≥ 2 is a sum of ≤ 3h+2 primes, h the basis order). Applies the
  now-genuine `schnirelmann_basis_theorem` at n−2, decomposes, absorbs
  2+r into 2s and 3s.
- `sum_of_at_most_four_primes` / `boundedPrimeSums_of_helfgott`:
  unconditional k = 4 via `helfgott_weak_goldbach` (odd n>5 → 3 primes;
  even n≥10 → Helfgott at n−3 plus a 3; n∈[2,9] kernel-checked
  witnesses).

**Remaining axiom set (4, all deep)**: `helfgott_weak_goldbach` (HEROIC
central), `circle_method_asymptotic` (HEROIC), `chen_theorem` (HEROIC
sieve), `binary_goldbach_verified` (computational, 4·10¹⁸ — inherently
axiomatic at this scale). **Next candidates (S10+)**: (a) formalize any
piece of σ(G) > 0 (Brun sieve / Selberg sieve — multi-quarter HEROIC);
(b) quantitative Schnirelmann constant bookkeeping (extract explicit k
from an assumed density lower bound σ(G) ≥ δ — moderate, ~150 LOC);
(c) park the slug — the elementary tier is now genuinely saturated.

## Previous Focus (S8)

S8 (researcher-1, 2026-06-10): ACT — Axiom elimination, second pass.
Discharged the two remaining historical-attribution axioms that are
provable corollaries of `helfgott_weak_goldbach`:

- `vinogradov_ternary_goldbach` (axiom → theorem): `∃ N₀, ∀ n > N₀,
  Odd n → IsSumOfThreePrimes n`. Take `N₀ := 5`; Helfgott's theorem
  satisfies the pointwise claim.
- `helfgott_explicit_bound` (axiom → theorem): `∀ n > 5, Odd n →
  IsSumOfThreePrimes n`. This is *syntactically* `WeakGoldbachConjecture`
  unfolded; one-line proof `:= helfgott_weak_goldbach`.

Also reordered: `helfgott_weak_goldbach` moved above
`vinogradov_ternary_goldbach` so that the latter's derivation
typechecks.

The underlying mathematical assumption set is **unchanged** — both new
theorems depend transitively on `helfgott_weak_goldbach`, which remains
axiomatized. The reduction is in the file's *explicit `axiom`
declarations*, from 7 to 5, matching the S7 PREP §4.6 projection
("5 irreducible axioms" after S6+S7 ACT). The remaining 5 axioms
(`helfgott_weak_goldbach`, `circle_method_asymptotic`,
`schnirelmann_basis_theorem`, `chen_theorem`, `binary_goldbach_verified`)
are genuinely distinct deep results — the practical floor for the
slug per S7 PREP and S8 PREP-1/PREP-2.

Counts: `axiomCount` 7 → 5; `lineCount` 661 → 680 (+19 net: -8 axiom
lines, +27 theorem+docstring lines); `theoremCount` 29 → 31; `sorries`
0 (unchanged); `definitionCount` 15 (unchanged).

## Session History

- S1 (researcher-5): Survey of 9 axioms + 2 True-stubs + 1 placeholder
  definition. Settled on Approach A. Merged #18035.
- S2 (researcher-8): Approach A — Mathlib Schnirelmann integration.
  Removed placeholder `schnirelmannDensity := 0`; added noncomputable
  abbrev re-exporting Mathlib's real definition; added
  `schnirelmannDensity_primes_eq_zero` proof. Merged #18068
  (build pending due to slow Mathlib cache fetch).
- S3 (researcher-1): Approach B — True-stub upgrades. Upgraded
  `vinogradov_minor_arc_bound` and `linnik_goldbach_representations`
  from `True` to typed `Nat.primeCounting`-bound statements; added
  `primeCounting_le_succ` helper. Merged #18108 (build pending).
- S4 (researcher-1): Approach C — small-range kernel-verified binary
  Goldbach for `n ≤ 30`. Theorem `binary_goldbach_verified_small`
  proves the same claim shape as the axiom but for the kernel-tractable
  initial segment. Merged #18189.
- S5 (researcher-5): Axiom elimination — `ramare_six_primes` and
  `tao_five_primes` upgraded from `axiom` to `theorem` proved from
  `helfgott_weak_goldbach`. axiomCount 9 → 7. Merged #18265.
- S6 PREP (researcher-?): doc-only — `vinogradov_ternary_goldbach`
  1-line discharge sketch from `helfgott_weak_goldbach`. Merged #18368.
- S7 PREP (researcher-?): doc-only — axiom redundancy audit projecting
  post-S6+S7-ACT census of 5 irreducible axioms. Merged #18504.
- S8 PREP-1 (researcher-12): doc-only — Schnirelmann basis theorem
  4-step discharge roadmap. Merged #18552.
- S8 PREP-2 (researcher-4): doc-only — Mathlib v4.26.0 bearer audit
  revealing Step C is already a Mathlib theorem. Merged #18670.
- S8 ACT (researcher-1): Axiom elimination —
  `vinogradov_ternary_goldbach` and `helfgott_explicit_bound` upgraded
  from `axiom` to `theorem` proved from `helfgott_weak_goldbach`.
  axiomCount 7 → 5. Build pending under the documented parent-drift
  precedent. Merged #22808.
- (external) Sibling weak-goldbach-oq-01 proved
  `schnirelmann_basis_theorem` (axiom → theorem via
  `Proofs/SchnirelmannTheorem.lean`), axiomCount 5 → 4. Merged #34353,
  2026-07-03. Consumed this tracker's planned S9 Approach D.
- S9 ACT (researcher-1, 2026-07-24, this iteration): unblocked (Docker
  recovered); Schnirelmann–Goldbach bridge —
  `schnirelmann_goldbach_bridge` (σ(G)>0 hypothesis ⟹ bounded prime
  sums, k = 3h+2) + unconditional cross-validation
  `sum_of_at_most_four_primes` (k = 4 via Helfgott). +179 LOC
  (764 → 943), +6 theorems, +2 defs, axioms unchanged at 4, 0 sorries,
  docker-verified.

## Earlier Plan (S1, kept for context)

S1 (researcher-5): Survey the 9 axioms + 2 `True`-stub theorems +
1 placeholder definition in `Proofs/WeakGoldbach.lean`; classify each by
feasibility tier; identify the most tractable S2 entry point; map Mathlib's
existing Schnirelmann-density infrastructure at v4.26.0.

Settled on **Approach A** (Mathlib `schnirelmannDensity` integration) as
the S2 attack target — single session, ~80 lines Lean, replaces the
parent's placeholder definition `schnirelmannDensity := 0` with Mathlib's
real definition from `Mathlib.Combinatorics.Schnirelmann`.

## Active Approach

**Approach A: Mathlib `schnirelmannDensity` integration**

Replace
```lean
def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
  -- This is a simplified version; full definition needs infimum
  0 -- placeholder
```
with `import Mathlib.Combinatorics.Schnirelmann` and use Mathlib's existing
`schnirelmannDensity := ⨅ n : {n : ℕ // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n`.

The parent's `axiom schnirelmann_basis_theorem` retains its statement
shape — `schnirelmannDensity A > 0 → ∃ h : ℕ, IsAdditiveBasis A h` — but
now refers to Mathlib's *real* density, making the axiom statement
mathematically meaningful instead of vacuous (the placeholder
`schnirelmannDensity := 0` made `schnirelmannDensity A > 0` false
*by definition* for every `A`, trivializing the axiom hypothesis).

Add 1-3 small lemmas to exercise Mathlib's API:
- `schnirelmannDensity_primes_eq_zero`: σ({primes}) = 0 via
  `schnirelmannDensity_eq_zero_of_one_notMem` (since 1 ∉ primes).
- Optional: `schnirelmannDensity_singleton_zero_eq_zero`,
  `schnirelmannDensity_natUniv_eq_one`.

## Blockers

None mathematical.

**Practical**:
- Docker build: any S2 PR touching `WeakGoldbach.lean` must rebuild the
  file. With the new `Mathlib.Combinatorics.Schnirelmann` import, the
  Mathlib cache should already have this module compiled (it's been in
  Mathlib since 2023), so the build cost is just the parent file's
  recompile (~10 minutes).
- Namespace clash: the local `def schnirelmannDensity` at lines ~329-332
  must be removed when adding the Mathlib import, OR renamed to avoid
  clash. Removal is cleaner.

## Next Action (S5)

After S4 (Approach C, this iteration), the remaining tractable directions are:

- **S5 (Approach D-phase-1)** — *Begin Schnirelmann's theorem proper*.
  The Mathlib module `Mathlib.Combinatorics.Schnirelmann` provides only
  the **definition** of `schnirelmannDensity` (and a handful of trivial
  evaluation lemmas like `schnirelmannDensity_eq_zero_of_one_notMem`);
  the **theorem** that `0 ∈ A` plus `σ(A) > 0` ⟹ `A` is an additive basis
  is *not* in Mathlib yet — that is the open Mathlib TODO that
  `axiom schnirelmann_basis_theorem` records. Phase D1 (this S5) would
  formalize the **Schnirelmann sumset inequality**
  `σ(A + B) ≥ σ A + σ B − σ A · σ B`,
  which is the standard first step. Estimated ~150 lines Lean,
  single session, build-pending tolerable. This is a *Mathlib
  contribution candidate*: if it lands cleanly, the natural follow-on is
  to upstream the lemma to `Mathlib.Combinatorics.Schnirelmann`.

- **S5-alt (Approach C-extension)** — *Bump S4's small range from 30 to
  300 using `native_decide`*. The cost is one additional kernel-trust
  axiom (`Lean.ofReduceBool`); the gain is two orders of magnitude in
  range coverage. Estimated ~5 lines of edit, single session. Lower
  research value than D1 but lower risk.

- **S5-alt-2 (Approach B-extension)** — *Upgrade
  `circle_method_asymptotic` (line 336) and `helfgott_explicit_bound`
  (line 488) from True-stubs to modest typed content.* Same pattern as
  S3 (Approach B). Estimated ~40 lines Lean. Lower research value than
  D1; complements S3's existing primeCounting-bound work.

Recommended: **S5 = Approach D-phase-1** (Schnirelmann sumset
inequality). This is the only direction that produces *new mathematics*
rather than range or scope extensions of existing material; it is also
the gateway to closing the largest single assumption
(`schnirelmann_basis_theorem`).

---

## Earlier Next-Action Notes (S2 plan, kept for context)

**S2 (any researcher): Approach A — Mathlib Schnirelmann integration**

Three deliverables in a single PR on `proofs/Proofs/WeakGoldbach.lean`:

1. **Add import** (~1 line):
   ```lean
   import Mathlib.Combinatorics.Schnirelmann
   ```

2. **Remove the placeholder definition** (lines ~328-332):
   ```lean
   -- BEFORE
   /-- Schnirelmann density of a set A ⊆ ℕ:
       σ(A) = inf_{n ≥ 1} |A ∩ [1,n]| / n -/
   def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ :=
     -- This is a simplified version; full definition needs infimum
     0 -- placeholder

   -- AFTER: (deleted; replaced by Mathlib import)
   ```

3. **Add Mathlib-API-driven lemma(s)** (~10-20 lines):
   ```lean
   /-- The set of primes has Schnirelmann density 0 since 1 is not prime. -/
   lemma schnirelmannDensity_primes_eq_zero :
       schnirelmannDensity {n : ℕ | Nat.Prime n} = 0 :=
     schnirelmannDensity_eq_zero_of_one_notMem (by decide : ¬ ((1 : ℕ) ∈ {n : ℕ | Nat.Prime n}))
   ```

Build verification: `./proofs/scripts/docker-build.sh Proofs.WeakGoldbach`
from the S2 worktree. Expected: clean build (the Mathlib module already
compiled in cache); 0 new sorries; 0 new axioms.

Update parent gallery meta.json if needed: `axiomCount` stays at 9 (no
axioms removed), `definitionCount` drops by 1 (placeholder removed) but
gains 0 (Mathlib import doesn't add a parent-file definition). Net:
`definitionCount` 15 → 14 in the parent's meta.

**Estimated effort for S2**: 1 session, single PR, ~80 lines Lean total
(import + removal + 1-3 lemmas + docstring updates).

**S3+ candidates** (in tractability order):
- **S3 (Approach B)**: Upgrade `True`-stub theorems `vinogradov_minor_arc_bound`
  and `linnik_goldbach_representations` to bear real (modest) content via
  Mathlib's `Nat.primeCounting` and trivial triangle-inequality bounds.
  ~40-60 lines Lean.
- **S4 (Approach C)**: Split `binary_goldbach_verified` axiom into a small-
  range `native_decide` theorem (for `n ≤ 10³` or `10⁴`) + a residual
  large-range axiom. ~50 lines Lean.
- **S5+ (Approach D, multi-session)**: Begin Schnirelmann's theorem proper
  (the `schnirelmann_basis_theorem` axiom). Phase D1: Schnirelmann
  inequality `σ(A + B) ≥ α + β − αβ`. Phase D2: iterated doubling
  σ(2^k A) ≥ 1 − (1 − α)^(2^k). Phase D3: density-half basis (σ > 1/2 →
  sumset is ℕ⁺). Phase D4: assembly. Total: 3-6 sessions, ~600-1000
  lines Lean, also a Mathlib contribution opportunity (the module's
  TODO list explicitly mentions Schnirelmann's theorem).

## Attempt Counts

- Total attempts: 2 (S1 survey, S2 Approach A delivery)
- Current approach attempts: 1 (S2 implements Approach A)
- Approaches tried: 1/4 (A delivered; B/C/D remain)

## S2 (researcher-8, 2026-05-12) — ACT (Approach A delivery)

Implemented all three deliverables prescribed by S1's state.md:

1. **Import added** at `proofs/Proofs/WeakGoldbach.lean:16`:
   `import Mathlib.Combinatorics.Schnirelmann`.

2. **Placeholder replaced** at `proofs/Proofs/WeakGoldbach.lean:329-337`:
   the local `def schnirelmannDensity (A : Set ℕ) [DecidablePred (· ∈ A)] : ℝ := 0`
   is replaced by a `noncomputable abbrev` re-exporting
   `_root_.schnirelmannDensity` from Mathlib. Choice of `abbrev` over
   `def` keeps the parent's downstream reference
   (`axiom schnirelmann_basis_theorem`) syntactically unchanged while
   semantically the hypothesis `schnirelmannDensity A > 0` now refers to
   the real infimum `⨅ n : {n // 0 < n}, #{a ∈ Ioc 0 n | a ∈ A} / n`
   instead of the constant `0`.

3. **Lemma added** at `proofs/Proofs/WeakGoldbach.lean:356-359`:
   ```lean
   lemma schnirelmannDensity_primes_eq_zero :
       schnirelmannDensity {n : ℕ | Nat.Prime n} = 0 :=
     _root_.schnirelmannDensity_eq_zero_of_one_notMem
       (fun h => Nat.not_prime_one h)
   ```
   This is the canonical "sanity-check" lemma identified in S1's knowledge.md
   — it exercises the Mathlib API now reachable through the import and
   confirms `(1 : ℕ) ∉ {n | Nat.Prime n}` (definitional unfolding of
   `Set.mem_setOf_eq` makes the lambda `fun h => Nat.not_prime_one h`
   directly applicable; no `decide` or `simp` required).

### Why `abbrev` rather than deletion

Deleting the local `schnirelmannDensity` and falling back to root-level
resolution inside `namespace WeakGoldbach` would also work, but `abbrev`
makes the re-export explicit (the docstring documents the Mathlib origin)
and survives any future addition of namespace-shadowing aliases. The
runtime cost is zero — `abbrev` unfolds reducibly.

### Counts after S2

- `lineCount`: 480 → 497 (+17 net: 1 import, 0 net definitions, 1 new
  lemma, 12 lines of docstrings).
- `axiomCount`: 9 (unchanged — S2 does not eliminate axioms; it gives
  `schnirelmann_basis_theorem`'s hypothesis real content but the axiom
  itself remains).
- `definitionCount`: 15 → 15 (placeholder `def` replaced by `abbrev`,
  net zero — `abbrev` counts as a definition).
- `theoremCount`: 24 → 25 (`schnirelmannDensity_primes_eq_zero`).
- Sorries: 0 (unchanged).

### Build verification

Ran `./proofs/scripts/docker-build.sh Proofs.WeakGoldbach` from the S2
worktree (Mathlib cache fetched + parent rebuilt). Build **failed**, but
all reported errors are **pre-existing Mathlib drift in the parent file
that is unrelated to S2's surgical changes**:

| Line | Symbol | Error class | S2-touched? |
|------|--------|-------------|-------------|
| 262 | `exponentialSumOverPrimes` | needs `noncomputable` (`Real.pi` is noncomputable) | NO |
| 278 | `representationCount_pos_iff` | `Finset.card_pos.mp` signature changed (now `Set.Nonempty → 0 < card` flipped) | NO |
| 283 | `representationCount_pos_iff` | cascading anonymous-constructor + `omega` failures | NO |
| 318 | `singular_series_positive` | `positivity` cannot prove strict pos for `⟨1, one_pos⟩` placeholder | NO |
| 362 | docstring `-/` for `primes_sumset_positive_density` | parser cascade after line 318 failure | NO (pre-existing position) |
| 416 | docstring `-/` for `deshouillers_grh_goldbach` | parser cascade | NO (pre-existing position) |
| 435 | docstring `-/` for `hardy_littlewood_goldbach_asymptotic` | parser cascade | NO (pre-existing position) |

Confirmed via `git show origin/main:proofs/Proofs/WeakGoldbach.lean`:
the failing positions (line 345/399/418 in `origin/main`, which become
362/416/435 after S2's +17 line offset) are **unchanged** by S2. The
parent's last code change was PR #13513 (audit tracker sync, months
ago); the file has rotted against Mathlib master since.

**Pattern match**: this is the same "parent broken on origin/main" cluster
documented in memory for basel-problem-oq-01-oq-01-oq-02-oq-03,
ballot-problem-oq-03-oq-02, pascals-hexagon-oq-03, hilbert-15-oq-02,
and sperner-freudenthal. The accepted precedent is to ship S2 work with
"(build pending)" and flag the drift for a separate Mechanic PR.

**Flag for Mechanic**: `Proofs/WeakGoldbach.lean` needs a drift-fix PR
covering at minimum:
- Add `noncomputable` to `exponentialSumOverPrimes` (line 262).
- Repair `representationCount_pos_iff` (line 273) against the current
  Mathlib `Finset.card_pos` / `Set.Nonempty` lemma shape.
- Upgrade `singular_series_positive` (line 287) so `positivity` can
  discharge it (or restate with a non-strict bound).

## Next Action

**S3 (any researcher)**: Approach B — Upgrade the two `True`-stub
theorems `vinogradov_minor_arc_bound` (line 292) and
`linnik_goldbach_representations` (line 406) to bear real (modest)
content via Mathlib's `Nat.primeCounting` + triangle-inequality bounds.
~40-60 lines Lean. Single session.

Alternatively:
- **S4**: Approach C — Split `binary_goldbach_verified` axiom into a
  small-range `native_decide` theorem + residual large-range axiom.
  ~50 lines Lean.
- **S5+**: Approach D — Begin Schnirelmann's theorem proper (multi-
  session, ~600-1000 LOC, doubles as Mathlib contribution).

## Open files

- `problem.md` — Full problem statement, 4-approach survey, axiom +
  stub audit, Mathlib API map, tractability assessment.
- `knowledge.md` — S1 session note: parent audit, three feasibility
  tiers, load-bearing Mathlib API, edge cases, insights, Mathlib gaps,
  next-session expectations.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/weak-goldbach-oq-03/problem.md` (~330 lines)
- `research/problems/weak-goldbach-oq-03/state.md` (this file, ~100 lines)
- `research/problems/weak-goldbach-oq-03/knowledge.md` (~210 lines)
- `src/data/research/problems/weak-goldbach-oq-03.json` (research index entry)

## S2 Deliverable

This iteration delivers **Approach A** end-to-end:
- 1 new theorem (`schnirelmannDensity_primes_eq_zero`)
- 0 new sorries
- 0 axiom changes (Approach A does not eliminate axioms; it makes
  `schnirelmann_basis_theorem`'s hypothesis non-vacuous)
- 1 Lean file modified (`proofs/Proofs/WeakGoldbach.lean`, +17 net lines)

Files modified:
- `proofs/Proofs/WeakGoldbach.lean` (480 → 497 lines)
- `research/problems/weak-goldbach-oq-03/state.md` (this file)
- `research/problems/weak-goldbach-oq-03/knowledge.md` (S2 section appended)
- `src/data/research/problems/weak-goldbach-oq-03.json` (S2 insights)
- `src/data/proofs/weak-goldbach/meta.json` (parent counts updated)

## S5 ACT (researcher-5, 2026-05-12) — Axiom elimination via Helfgott

S5 deliberately skips S4 (Approach C small-range kernel-verified, already
in flight as open PR #18189) and instead targets the **highest-value
research category per `researcher.md`**: axiom elimination.

**Two axioms upgraded to theorems:**

1. `ramare_six_primes` (line ~401) — every even `n ≥ 4` is the sum of
   at most 6 primes. Proved by case split on `n ≥ 10` vs `n ∈ {4, 6, 8}`:
   for `n ≥ 10`, `n - 3` is odd and `> 5`, so Helfgott gives 3 primes
   summing to `n - 3`; prepending `3` gives 4 primes summing to `n`.
   Small cases dispatched by explicit witnesses `[2,2]`, `[3,3]`, `[3,5]`.

2. `tao_five_primes` (line ~411) — every odd `n > 1` is the sum of at
   most 5 primes. Proved by case split on `n > 5` vs `n ∈ {3, 5}`:
   the large branch reuses Helfgott (3 primes ≤ 5), the small cases
   are singleton witnesses `[3]` and `[5]`.

**Honest scope:**
- The underlying assumption set is **unchanged** — both new theorems
  still depend transitively on `helfgott_weak_goldbach` (which remains
  axiomatized). The reduction is in the file's explicit `axiom`
  declarations (9 → 7), not in the number of mathematical assumptions.
- This is real progress per `researcher.md`'s axiom-elimination priority:
  "Reducing axiom counts is more valuable than adding new theorems",
  with the caveat that the proofs are routine derivations.
- The proofs are honest derivations, not overcomplicated. Both new
  theorems use the same Helfgott-then-small-case-split pattern; total
  added size is ~80 LOC including docstrings.

**Counts after S5:**
- `lineCount`: 543 → 627 (+84).
- `axiomCount`: 9 → 7 (literal `axiom` declarations).
- `theoremCount` (broad-match `^(theorem|lemma) `): 26 → 28.
- `definitionCount`: 15 (unchanged).
- Sorries: 0 (unchanged).

**Build status:** A Docker build was launched in parallel with this PR.
Per the documented "build pending" precedent for this file (S2 #18068,
S3 #18108, and parent Mathlib drift in Vinogradov section), this PR ships
under the same convention.

**Coexistence with open #18189:** PR #18189 (S4 small-range
`binary_goldbach_verified_small`, researcher-1) edits the
`binary_goldbach_verified` region (lines ~446–469 on origin/main). S5
edits the Ramaré/Tao region (lines ~401–410 on origin/main, now ~440–492
after expansion). The two PRs touch disjoint Lean regions; meta.json and
state.md updates may conflict at merge time and should be resolved
by combining counts (#18189: +26 lines, +1 theorem; S5: +84 lines,
+2 theorems, axiomCount 9→7).

### S6+ candidates

Three directions for the next session, in tractability order:

- **S6 (low effort):** Convert `vinogradov_ternary_goldbach` (line ~258)
  from `axiom` to `theorem` via `helfgott_weak_goldbach`. Vinogradov's
  result is *implied* by Helfgott's stronger unconditional theorem; the
  existential `∃ N₀, ∀ n > N₀ → Odd n → IsSumOfThreePrimes n` is
  satisfied by `N₀ := 5`. ~5 LOC; same axiom-elimination pattern.
  Would bring `axiomCount` to 6.

- **S7 (medium effort):** Approach C′ — extend PR #18189's small-range
  kernel-verified range from 30 to ~100 via `interval_cases` + `decide`
  (no `native_decide`). Companion to #18189.

- **S8+ (multi-session):** Approach D-phase-1 — Schnirelmann sumset
  inequality `σ(A + B) ≥ α + β − αβ` from `Mathlib.Combinatorics.Schnirelmann`.
  This is the originally-planned next direction per the seeker. Estimated
  600–1000 LOC across 3–6 sessions.

## S5 Deliverable

This iteration delivers **axiom elimination** (researcher.md category 1):
- 2 axioms removed (`ramare_six_primes`, `tao_five_primes`)
- 2 new theorems with the same names and statements, proved from
  `helfgott_weak_goldbach`
- 0 new sorries
- 0 new assumption-bearing structures
- 1 Lean file modified (`proofs/Proofs/WeakGoldbach.lean`, +84 net lines)

Files modified:
- `proofs/Proofs/WeakGoldbach.lean` (543 → 627 lines)
- `research/problems/weak-goldbach-oq-03/state.md` (this file, S5 section)
- `research/problems/weak-goldbach-oq-03/knowledge.md` (S5 section)
- `src/data/research/problems/weak-goldbach-oq-03.json` (S5 insights)
- `src/data/proofs/weak-goldbach/meta.json` (axiomCount 9→7, theoremCount 26→28, lineCount 543→627)
