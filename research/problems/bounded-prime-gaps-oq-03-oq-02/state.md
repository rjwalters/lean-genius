# Current State

**Phase**: ACT
**Since**: 2026-05-12T07:08:00Z
**Iteration**: 5
**Researcher**: researcher-11 (S5); researcher-10 (S4); researcher-8 (S3); researcher-12 (S2); researcher-10 (S1)

## Current Focus

S5 (this PR) — Intermediate-scale Engelsma analogue via `native_decide`
at `(k, w) = (8, 22)`, a **cautious scaling checkpoint** between
S4's $\binom{16}{6} = 8008$ search and the originally planned S6
case $\binom{30}{10} \approx 3 \times 10^7$:

```
theorem engelsma_analogue_8_22 :
    ∀ H ∈ (Finset.range 22).powersetCard 8,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 18 ≤ H.max' ⟨0, h0⟩ := by
  native_decide
```

Search space `Nat.choose 22 8 = 319,770` ≈ `3.2 × 10⁵` — roughly
**40× the S4 case** but still four orders of magnitude below
the deferred S6 case. The implication is vacuously satisfied at
every enumerated subset since Engelsma's table records `H(8) = 26`
> 21, so no admissible 8-tuple fits in `Finset.range 22`. The
threshold `18 ≤ H.max'` mirrors S4's convention of a conservative
under-estimate of the (unattained) diameter bound.

**Why deviate from state.md's stated S5 next-action (`(10, 30)`)?**
The (10, 30) case has documented runtime risk: 30–120 s estimated
under `native_decide`, possibly exceeding default CI timeouts. The
local worktree shares the broken `proofs/.lake` symlink, so we
cannot pre-verify build. Per `knowledge.md` §6.4 — the feasibility
checkpoint principle — we want **empirical scaling evidence** at
an intermediate scale (40× S4) before committing to the 3,750× S4
case. If S5 builds in a few seconds, the (10, 30) extrapolation
becomes principled (~33× slow-down → tens of seconds). If S5 itself
runs slowly, that informs whether we proceed to (10, 30) or move
directly to the §6.4 Path-C-prime fallback. The originally planned
`(10, 30)` case is **renumbered to S6** below.

**Axiom bookkeeping**: `native_decide` reuses the `Lean.ofReduceBool`
axiom introduced in S4; `leanFile.axiomCount` stays at `1` (each
additional `native_decide` requires the axiom once per file, not
once per use).

**theoremCount**: 6 → 7 (the new `engelsma_analogue_8_22`).
**lineCount**: 192 → 245.

## Next Action

**S6 — Mid-size Engelsma analogue at `(k, w) = (10, 30)`** per
knowledge.md §3.3 (originally planned as S5; deferred after S5
introduced the (8, 22) intermediate scaling step). Concrete
target:

```lean
theorem engelsma_analogue_10_30 :
    ∀ H ∈ (Finset.range 30).powersetCard 10,
      ∀ (h0 : 0 ∈ H), IsAdmissible H → 22 ≤ H.max' ⟨0, h0⟩ := by
  native_decide
```

`Nat.choose 30 10 ≈ 3 × 10^7`. Estimated `native_decide` runtime
30–120 seconds. May exceed default CI timeouts; if S5's runtime
extrapolates poorly, fall back to the §6.4 Path-C-prime plan
(land what we have, narrow the axiom statement).

### Previous focus (S3)

S3 — Kernel-`decide` regression checks for the S2 `Decidable`
instance: four theorems demonstrating correct reduction on small tuples.

* `admissible_twin_via_S2`         — `IsAdmissible {0, 2}` via S2 instance.
* `admissible_triple_via_S2`       — `IsAdmissible {0, 2, 6}` via S2 instance.
* `admissible_quadruple_via_S2`    — `IsAdmissible {0, 2, 6, 8}` via S2 instance.
* `not_admissible_zero_one_via_S2` — `¬ IsAdmissible {0, 1}` via S2 instance
  (negative case; `(·%2)` image card = 2 ≥ 2).

All four use kernel `decide` (not `native_decide`), keeping `axiomCount = 0`.
These are the simplest Path-A (verified-backtracking) sanity checks per
`knowledge.md` §3.3 — exercising the new instance on tuples already proven
admissible in `BoundedPrimeGaps.lean` (via hand-written calculation) plus one
negative case to confirm the decider rejects non-admissible inputs.

`native_decide`-based Engelsma-analogue checks (`(k, w) = (6, 16)` and
beyond) are explicitly deferred to S4, where the introduction of the
`Lean.ofReduceBool` axiom needs to be accounted for in meta.json.

### Previous focus (S2)

S2 — `Decidable (IsAdmissible H)` infrastructure
landed in a new file
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (+109 lines,
1 abbrev, 1 theorem, 1 instance, 0 axioms, 0 sorries):

* `abbrev IsAdmissibleBdd (H : Finset ℕ) : Prop` — restricts
  `IsAdmissible`'s prime quantifier to
  `p ∈ Finset.range (H.card + 1)`. Phrased as a `Finset`-bounded
  `∀`-quantifier so that decidability via
  `Finset.decidableDforallFinset` + `Nat.decidablePrime` +
  `Nat.decLt` is automatic. Declared as `abbrev` (not `def`) so
  the body stays transparent during instance search.
* `theorem isAdmissible_iff_bdd (H) : IsAdmissible H ↔ IsAdmissibleBdd H`
  — forward direction is restriction; backward case-splits on
  `p ≤ H.card`, dispatching `p > H.card` via the chain
  `(H.image (· % p)).card ≤ H.card < p` from
  `Finset.card_image_le`. Closes with `omega`.
* `instance instDecidableIsAdmissible (H) : Decidable (IsAdmissible H)`
  — `decidable_of_iff (IsAdmissibleBdd H) (isAdmissible_iff_bdd H).symm`.

Discharges knowledge.md §3.1 (the strict prerequisite for both
Path A small-case `native_decide` sanity checks per §3.3 and the
eventual Path B verified-backtracking work per §4).

Also registers the new file in `proofs/Proofs.lean` and adds
its `leanFiles` entry to
`src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json`,
plus bumps `currentState` from S1 OBSERVE → S2 ACT.

Honesty: build verification is pending — the current worktree
shares the broken `proofs/.lake` symlink (per memory
`feedback_researcher_lake_symlink_broken.md`), so
`docker-build.sh Proofs.BoundedPrimeGapsOQ03OQ02` is not run
pre-commit. The proof script consists of `omega` plus standard
Mathlib API (`Finset.mem_range`, `Nat.lt_succ_of_le`,
`Nat.lt_of_not_le`, `Finset.card_image_le`); all are
long-stable, so build risk is low.

## Active Approach

S2 lands the Decidable instance (Path A's foundation). The
next iterations explore Path A's small-case sanity checks
(§3.3) before any Path B commitment.

## Blockers

None at S2. Path B's runtime feasibility on the full
`(50, 246)` problem remains a *risk* per knowledge.md §6.4
but cannot be assessed until at least S4.

## Subsequent Iterations (deferred)

- S6 — Mid-size Engelsma analogue at `(k, w) = (10, 30)`
  via `native_decide` (originally state.md's S5; deferred to S6
  after the (8, 22) intermediate). Risk: 30–120 s runtime.
- S7 — `engelsma_lower_bound_of_finitary` bridge lemma
  (Option B prerequisite) per knowledge.md §2.4. Can be tackled
  in parallel with S6 since the bridge proof is pure-Lean
  combinatorics independent of `native_decide` runtime.
- S8+ — Path B verified-backtracking prototype, building on
  the S4/S5/S6 `native_decide` infrastructure as a unit-test
  harness.
- Path C (Selberg sieve fallback) remains an alternative if
  Path B's runtime extrapolation fails at S6.

## Attempt Counts

- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Session Log

- **S1 (2026-05-11, researcher-10)**: OBSERVE. Located the axiom, reduced to the finitary
  decidable form, surveyed three approach paths (A/B/C in `knowledge.md`), identified
  Path B as target, identified S2 as a foundational `Decidable (IsAdmissible H)` instance.
  Doc-only iteration. No Lean changes. PR #17774 merged.
- **S2 (2026-05-11, researcher-12)**: ACT. New file
  `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (109 lines): `IsAdmissibleBdd`,
  `isAdmissible_iff_bdd`, `instDecidableIsAdmissible`. 0 axioms, 0 sorries.
  Build pending. PR #17790 merged.
- **S3 (2026-05-12, researcher-8)**: ACT. Extended S2 file (109 → 149 lines, +40):
  4 kernel-`decide` regression theorems exercising the S2 instance on
  `{0, 2}`, `{0, 2, 6}`, `{0, 2, 6, 8}` (positive) and `{0, 1}` (negative).
  Kernel decide preserves `axiomCount = 0`; `native_decide`-based larger
  Engelsma analogues deferred to S4. PR #17812 merged.
- **S4 (2026-05-12, researcher-10)**: ACT. Extended S3 file (149 → 192 lines, +43):
  `engelsma_analogue_6_16` via `native_decide` over the 8008 subsets of
  `(Finset.range 16).powersetCard 6`. First `native_decide` in this file;
  introduces the `Lean.ofReduceBool` axiom (`leanFile.axiomCount` 0 → 1).
  Vacuous antecedent (no admissible 6-tuple fits in range 16; Engelsma
  records narrowest diameter 16). PR #17847 merged.
- **S5 (2026-05-12, researcher-11)**: ACT. Extended S4 file (192 → 245 lines, +53):
  `engelsma_analogue_8_22` via `native_decide` over the 319,770 subsets of
  `(Finset.range 22).powersetCard 8`. Intermediate scaling checkpoint
  (~40× S4 search), reuses the `Lean.ofReduceBool` axiom from S4
  (`axiomCount` stays at 1). Vacuous antecedent (Engelsma records H(8)=26
  > 21, so no admissible 8-tuple fits in range 22). The originally planned
  (10, 30) case is deferred to S6, pending evidence on S5's `native_decide`
  runtime to extrapolate the (10, 30) feasibility. Build pending; the
  Docker symlink trap prevents local verification.
