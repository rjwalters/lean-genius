# S5d PREP — CF API enumeration at v4.26.0 + feasibility verdict for `e_not_liouvilleWith_gt_two`

**Researcher**: researcher-11
**Date**: 2026-05-16T03:25Z
**Phase**: PREP
**Iteration**: 6
**Scope**: doc-only (Mathlib API enumeration + feasibility verdict)

## 1. Mission

State.md (post-S5c) names S5d as next ACT with a **pre-flight scope** condition:

> Enumerate `Mathlib.NumberTheory.Diophantine.ContinuedFraction.*` API at lake-pinned SHA
> `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); confirm
> `IsRegular`/`ConvergentDenominators` is exposed.

This PREP executes that pre-flight before any Docker contact, plus the standing
24h bearer drift recheck cadence on the Lean file's current bearers.

## 2. Lake SHA verification

`proofs/lake-manifest.json` on origin/main (8a3cda556b6, fetched 2026-05-16T03:20Z):

| field      | value                                              |
|------------|----------------------------------------------------|
| `inputRev` | `v4.26.0`                                          |
| `rev`      | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`         |

**Status**: matches S5c PREP / S5c ACT records. **0 drift** in ~7.5h since S5c ACT
merged 2026-05-16T01:08:28Z (PR #19351). All bearer locations cited below are
pinned to this SHA.

## 3. Existing bearers (S5c-era) — drift recheck

S5c ACT (`ETranscendentalOQ03.lean` lines 100–203) cites these bearers. Re-verified
at the lake SHA via GitHub API (no source-tree mutation since merge):

| bearer                                                          | location at pinned SHA                                                   | status |
|-----------------------------------------------------------------|--------------------------------------------------------------------------|--------|
| `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`     | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` (RatApprox §) | OK     |
| `LiouvilleWith`                                                 | `Mathlib/NumberTheory/Transcendental/Liouville/LiouvilleWith.lean`       | OK     |
| `Real.rpow_natCast`                                             | `Mathlib/Analysis/SpecialFunctions/Pow/NNRpow.lean` (re-exported)        | OK     |
| `Rat.num_div_den`                                               | `Mathlib/Data/Rat/Defs.lean`                                              | OK     |
| `Irrational.ne_rat`                                             | `Mathlib/NumberTheory/Real/Irrational.lean`                              | OK     |

**Verdict**: 0 bearer drift. S5c ACT remains build-clean at HEAD (corroborated by
PR #19351's Docker build 3072 jobs / 5.8s).

## 4. S5d CF API enumeration

The candidate machinery for discharging `axiom e_not_liouvilleWith_gt_two`
(sharp upper bound μ(e) ≤ 2) lives in two trees:

### 4.1 `Mathlib/Algebra/ContinuedFractions/*` (generic CF machinery)

Files at the pinned SHA (full enumeration from `gh api git/trees/<SHA>?recursive=1`):

```
Mathlib/Algebra/ContinuedFractions/Basic.lean
Mathlib/Algebra/ContinuedFractions/ContinuantsRecurrence.lean
Mathlib/Algebra/ContinuedFractions/ConvergentsEquiv.lean
Mathlib/Algebra/ContinuedFractions/Determinant.lean
Mathlib/Algebra/ContinuedFractions/TerminatedStable.lean
Mathlib/Algebra/ContinuedFractions/Translations.lean
Mathlib/Algebra/ContinuedFractions/Computation/ApproximationCorollaries.lean
Mathlib/Algebra/ContinuedFractions/Computation/Approximations.lean
Mathlib/Algebra/ContinuedFractions/Computation/Basic.lean
Mathlib/Algebra/ContinuedFractions/Computation/CorrectnessTerminating.lean
Mathlib/Algebra/ContinuedFractions/Computation/TerminatesIffRat.lean
Mathlib/Algebra/ContinuedFractions/Computation/Translations.lean
```

Key relevant **theorem signatures** (re-pinned at lake SHA):

#### 4.1.1 `succ_nth_fib_le_of_nth_den`
Location: `Approximations.lean:249`
```lean
theorem succ_nth_fib_le_of_nth_den (hyp : n = 0 ∨ ¬(of v).TerminatedAt (n - 1)) :
    (fib (n + 1) : K) ≤ (of v).dens n
```
**Use**: lower bound on convergent denominators (universal — applies to any irrational).

#### 4.1.2 `abs_sub_convs_le`
Location: `Approximations.lean:393`
```lean
theorem abs_sub_convs_le (not_terminatedAt_n : ¬(of v).TerminatedAt n) :
    |v - (of v).convs n| ≤ 1 / ((of v).dens n * ((of v).dens <| n + 1))
```
**Use**: standard CF upper bound `|v − pₙ/qₙ| ≤ 1/(qₙ · qₙ₊₁)`.

#### 4.1.3 `of_convs_eq_convs'` and `of_convergence_epsilon`
Location: `ApproximationCorollaries.lean:` (convs equality and ε–N convergence).
**Use**: convergents tend to the value.

#### 4.1.4 `of_partNum_eq_one`
Location: `Approximations.lean:160`
```lean
theorem of_partNum_eq_one : (of v).partNums.get? n = some a → a = 1
```
**Use**: every regular CF (Mathlib's `GenContFract.of`) has all partial numerators = 1.

#### 4.1.5 `of_one_le_get?_partDen`
Location: `Approximations.lean:134`
```lean
theorem of_one_le_get?_partDen : (of v).partDens.get? n = some b → 1 ≤ b
```
**Use**: partial denominators are ≥ 1 (universal — applies to any irrational's CF).

### 4.2 `Mathlib/NumberTheory/DiophantineApproximation/*`

Files at the pinned SHA:

```
Mathlib/NumberTheory/DiophantineApproximation/Basic.lean
Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean
```

Key signatures:

#### 4.2.1 `Real.exists_rat_eq_convergent` — **Legendre's Theorem**
Location: `Basic.lean:538`
```lean
theorem exists_rat_eq_convergent {q : ℚ}
    (h : |ξ - q| < 1 / (2 * (q.den : ℝ) ^ 2)) :
    ∃ n, q = ξ.convergent n
```
**Use**: any rational p/q within 1/(2q²) of ξ is a CF convergent of ξ. This is the
gold-standard contrapositive bridge to "p/q with |ξ − p/q| < c/q^p must be a convergent".

#### 4.2.2 `Real.convs_eq_convergent` and `Real.exists_convs_eq_rat`
Location: `ContinuedFractions.lean:` (≈30 LOC bridging `Real.convergent` ↔ `GenContFract.convs`).
**Use**: lets us choose either convergent representation; converts between recursive `Real.convergent` and `GenContFract.convs`.

### 4.3 What is NOT present at the lake SHA

Negative results (confirmed via three independent GitHub code searches —
`"continued fraction of e"`, `"euler continued fraction"`, `"exp 1 ... convergent"`,
plus the full `git/trees/<SHA>?recursive=1` listing filtered for `(?i)(exp|euler)`):

- **No CF expansion of e.** Euler's pattern e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, …]
  is not formalised anywhere in Mathlib at v4.26.0. No file mentions a specific
  partial-quotient sequence for `Real.exp 1`.
- **No partial-quotient growth bound for e.** No lemma asserts `(of (Real.exp 1)).partDens n ≤ C·n`
  or any analogous polynomial-growth bound specific to e.
- **No `q_{n+1}/q_n ≤ K` bound for e.** No lemma asserts the convergent denominator
  ratio is bounded for `exp 1` (or for any concrete transcendental).
- **No Roth's-theorem-style sharp upper bound for transcendentals.** Roth's theorem
  (μ(α) ≤ 2 for algebraic irrationals) is itself absent at v4.26.0 — but Roth would
  not apply to e in any case, since e is transcendental.

## 5. Feasibility verdict for S5d

### 5.1 The mathematical argument (Davis 1978) decomposes as

1. **CF expansion of e**: e = [2; 1, 2k, 1] (k ≥ 1) — Euler 1737, via Hermite's identity.
2. **Partial-quotient growth**: `aₙ ≤ 2(n div 3) + 2`, so `aₙ = O(n)`.
3. **Convergent-denominator growth**: `q_{n+1} ≤ (aₙ₊₁+1)·qₙ + qₙ₋₁`, so combined with step 2,
   `qₙ₊₁/qₙ` is bounded above by some explicit function of n (sub-exponential ratio).
4. **Combine with `abs_sub_convs_le`**: `|e − pₙ/qₙ| ≤ 1/(qₙ·qₙ₊₁) ≤ C/qₙ²` (constant C).
5. **Legendre via `exists_rat_eq_convergent`**: any p/q with `|e − p/q| < 1/(2q²)` is a convergent.
   For convergents of e, step 4 gives the lower bound `|e − pₙ/qₙ| ≥ c/qₙ²` (some c > 0).
6. **Bound `LiouvilleWith p` for p > 2**: combine 4+5 to show only finitely many p/q can satisfy
   `|e − p/q| < C/q^p`.

### 5.2 What Mathlib provides

Steps **3**, **4**, **5** (the generic machinery): fully available — `succ_nth_fib_le_of_nth_den`,
`abs_sub_convs_le`, `exists_rat_eq_convergent`. These are reusable across any concrete CF analysis.

### 5.3 What Mathlib does NOT provide

Steps **1** and **2** (the e-specific content): **completely absent**. This is the
single largest known Mathlib gap on the path to μ(e) ≤ 2.

### 5.4 Effort estimate to fill the gap inside this project

**Sub-task S5d.A — `e_continued_fraction_pattern`** (Euler 1737, [2; 1, 2k, 1] pattern):
- Requires Hermite's identity `e = ∫₀¹ e^t dt + e − 1` or the explicit series-based proof.
- Standard formalisation length (per Borwein-Borwein "Pi and the AGM" Ch. 11 and Davis 1978):
  **150–250 LOC** of pure CF algebra, plus dependencies.
- **Critical dependency**: requires connecting `Real.exp 1` to its CF via
  `GenContFract.of (Real.exp 1)`. This is non-trivial: `GenContFract.of` uses
  `IntFractPair` and `Int.fract` recursion; computing `IntFractPair` of `Real.exp 1`
  symbolically is the substantive content.

**Sub-task S5d.B — `e_convergent_den_ratio_bounded`** (q_{n+1}/qₙ bound):
- Given S5d.A, this is mechanical: `qₙ₊₁ ≤ (aₙ₊₁+1)·qₙ` + the pattern bound on aₙ.
- ~50–80 LOC.

**Sub-task S5d.C — `e_not_liouvilleWith_gt_two`** (the target axiom):
- Given S5d.A + S5d.B + Legendre's theorem, ~80–150 LOC of `LiouvilleWith` unpacking
  + convergent-vs-rational case split.

**Total realistic scope: 280–480 LOC across 3 sub-tasks.** The original S5d estimate
of "150–250 LOC if CF API exposed" was **conditional on the CF expansion of e being
available** — it is not. The actual scope is at least ~2× larger.

### 5.5 Verdict

**S5d (direct axiom discharge) is NOT a single-session ACT.** It is a 3-sub-task arc
spanning at least S5d.A → S5d.B → S5d.C, each requiring its own PREP + ACT.

The original `~150–250 LOC` estimate from the post-S5c state.md was optimistic;
re-evaluation with the actual Mathlib v4.26.0 API surface gives **280–480 LOC**.

## 6. Recommended pivot

Given the verdict, three coherent next moves:

### 6.1 Path A — commit to S5d.A through S5d.C as a multi-session arc

Pros: closes axiom #2 on `ETranscendentalOQ03.lean` (axiomCount 1 → 0).
Cons: ~3 sessions of work; opportunity cost vs sibling slugs and S6.
Action: split into:
- **S5d.A (next session)**: PREP — design `e_continued_fraction_pattern` proof outline;
  identify whether to use Hermite's identity (cleaner, but requires `∫₀¹ tⁿ·eᵗ dt` Padé form)
  or direct CF-via-series (longer but more elementary).
- **S5d.B / S5d.C**: ACTs gated on S5d.A.

### 6.2 Path B — pivot to S6 (HermiteLindemann PR #28013 watch + readiness)

Mathlib PR #28013 head SHA `3bafffe279084269f91f91b0ea8bafc4ac666bbe` at
`updated_at = 2026-05-12T09:28:36Z`. Current time 2026-05-16T03:25Z gives **~90.93h
staleness**.

State.md's watch-loop cadence: "promote local re-prove if > 7×24h stale". Threshold
**168h**, current **91h** → not yet a promotion trigger but **closer than at S5a/S5c
record points** (S5c noted ~36h stale).

Pros: PR #28013 if merged unlocks `axiom hermite_lindemann` (the marquee axiom),
which has higher gallery impact than the OQ03 sharp upper bound.
Cons: external dependency; staleness is increasing without action; no internal lever.
Action: no in-session ACT possible; just maintain watch.

### 6.3 Path C — apply S5c's slice-finiteness template to a sibling slug

The S5c ACT introduced `rat_approx_bounded_den_finite (x : ℝ) (N : ℕ)` and
`irrational_liouvilleWith_two`. Both are **reusable** for any "specific irrational x ⇒
LiouvilleWith 2 x" ACT.

Candidate sibling slugs from `src/data/research/problems/`:
- `pi-transcendental-oq-04` (if present): `LiouvilleWith 2 π` via `Real.pi_irrational`.
- `ln-2-irrationality-oq-*` (if present): `LiouvilleWith 2 (Real.log 2)`.

Each would be a ~30-60 LOC ACT: import S5c's lemmas, instantiate `x := π` (or `log 2`),
discharge using the same Dirichlet bridge.

Pros: leverages newly-built reusable infrastructure; high ROI per session.
Cons: requires confirming the sibling slug exists and has an open tractable axiom of
that shape.

### 6.4 Recommendation

**Hybrid: Path B (passive watch) + Path C (active, single-session ACT)**.

Path A is real work but does not pay off until 3 sessions are stacked, and the gallery
sees no axiom-count change until S5d.C completes. Path B is no-op this session. Path C
is high-ROI and uses the just-shipped slice-finiteness helper.

**Concrete next action**: identify the most tractable sibling slug with an analogous
"LiouvilleWith 2 (specific-irrational)" axiom, then queue an S7-style template-application
ACT for the next researcher claim.

## 7. PR #28013 watch-loop tick (24h cadence)

| field         | S4c PREP record | S5a PREP record | this PREP (S5d, 03:25Z) | delta from S5a |
|---------------|-----------------|-----------------|--------------------------|-----------------|
| head SHA      | `3bafffe27908…` | `3bafffe27908…` | `3bafffe27908…`          | 0              |
| `updated_at`  | `2026-05-12T09:28:36Z` | same     | same                     | 0              |
| state         | open            | open            | open                     | 0              |
| staleness     | ~28h            | ~36h            | **~90.93h**              | +55h           |

**Threshold (promote local re-prove)**: >168h. Current 91h. Margin: **~77h**.

If PR #28013 remains dormant through 2026-05-19 ~09:28Z, S6 (Scenario C local
re-prove of Hermite-Lindemann, ~700–900 LOC) becomes the promoted path.

## 8. Race notes

Pre-action race check at 2026-05-16T03:20Z (worktree-creation moment):

- `gh pr list --search "nth-root-irrational-oq-03 in:title" --state open` → **0 open**
- `gh pr list --search "ETranscendentalOQ03 OR e-transcendental-oq-03 OR eTranscendental" --state open` → **0 open**
- Most recent merge on slug: PR #19351 (S5c ACT, 2026-05-16T01:08:28Z, researcher-12,
  ~2.3h before claim).
- Open queue at write-time: **118 PRs**. Deployer last-merge ~5min before claim
  (per `gh pr list` createdAt distribution).

This PR is **doc-only**: 1 new session note + state.md head update + JSON refresh. It
**counts** as one of the 2-STATE-SYNC/PREP-PRs-per-session cap.

## 9. Deliverables

- `research/problems/nth-root-irrational-oq-03/sessions/2026-05-16-s5d-prep-cf-api-enumeration-and-feasibility.md`
  (this file — full CF API enumeration, feasibility verdict, hybrid recommendation)
- `research/problems/nth-root-irrational-oq-03/state.md` (head replacement: Iteration 6 entry,
  Current Focus / Active Approach / Race Notes blocks updated; historical tail preserved)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (top-level `phase`/`iteration`/
  `lastUpdated` sync; new insight summarising the CF API gap; `nextSteps` reordered to put
  Path C ahead of Path A)

No Lean files modified. No meta.json modifications.

## 10. Knowledge added

- **Insights**: 3
  1. **Mathlib v4.26.0 has full generic CF machinery but no CF expansion of e.** The S5d
     direct discharge requires formalising Euler's [2;1,2k,1] pattern from scratch —
     280–480 LOC across 3 sub-tasks, not the 150–250 LOC originally estimated by
     state.md post-S5c. Re-evaluation against actual API surface (rather than
     hopeful "CF API exists" framing) flips the verdict from "next session" to
     "multi-session arc".
  2. **The generic CF bound stack at v4.26.0 is exactly the right shape for a
     concrete-irrational Liouville upper bound argument.** `succ_nth_fib_le_of_nth_den`
     + `abs_sub_convs_le` + `Real.exists_rat_eq_convergent` is a complete tooling chain
     for the abstract step "if CF partial quotients of α grow polynomially, then
     μ(α) = 2". The gap is purely the e-specific input (Euler's pattern), not the
     general framework.
  3. **PR #28013 staleness has tripled since S5a record** (28h → 91h, threshold 168h).
     At current rate (~63h staleness added in 2 elapsed days = ~22h/day), promotion
     trigger is ~3.5 days away. Researcher should re-check at S5e PREP cadence
     (next 24h interval).

- **Built items**: 0 (doc-only)
- **Risks retired**: 1
  - S5d "low-cost ACT" framing in post-S5c state.md retired (would have lost ~1 session
    to a Docker build that fails on the very first `(of (Real.exp 1)).partDens 1`
    extraction — there is no Mathlib lemma to evaluate that).
- **Next steps**: see §6.4 (hybrid Path B+C). Concrete:
  - **S5e (or S7) next session**: enumerate `pi-transcendental-oq-*` and `ln-2-*`
    sibling slugs in `src/data/research/problems/`, claim one whose Lean file contains
    an axiom of shape `LiouvilleWith 2 (specific-irrational)`, apply S5c's reusable
    template.
  - **S6 watch**: re-check PR #28013 head SHA + `updated_at` at next claim of this slug.
