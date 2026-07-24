# Knowledge Base: prob-method-lovasz-local-oq-01

## Problem Summary

Formalize the **Moser–Tardos resampling algorithm** for the variable-version
Lovász Local Lemma, and prove the expected-step bound
$\mathbb{E}[\text{resamplings of } A_i] \le x_i/(1-x_i)$.

The parent file `Proofs/LovaszLocalLemma.lean` currently *states* the bound's
non-negativity (theorem `moser_tardos_termination`), but does not define
the algorithm, the underlying probability space, or any link to expected
resampling counts. OQ-01 closes this gap.

## Status

**Phase**: S1 OBSERVE
**Iteration**: 0
**Lines added (Lean)**: 0
**Lines added (markdown/JSON)**: ~1100

## S1 Findings (this session)

### What exists today

- `Proofs/LovaszLocalLemma.lean` (364 lines, 25 theorems, 2 defs, 0 sorries):
  - `moser_tardos_termination` — Σ xᵢ/(1-xᵢ) ≥ 0 (vacuous; just non-negativity)
  - `symmetric_moser_tardos_bound` — symmetric case sum simplifies to n/d
  - `lllThreshold` — d^d/(d+1)^(d+1) and the `_le_quarter` bound
  - Full algebraic-core symmetric LLL (`symmetric_lll`, `general_lll`,
    `symmetric_lll_complete`) — purely combinatorial, no measure theory
  - `IsValidDepGraph`, `HasMaxDegree` — dependency-graph structure
- Sibling problems:
  - `lovasz-local-lemma-oq-01` (status in-progress, RICH): "Probabilistic
    LLL with measure-theoretic probability" — the **measure-theoretic version
    of the LLL itself**, not the constructive algorithm.
  - `lovasz-local-lemma-oq-03` (status in-progress, B): "Formalize the
    Moser-Tardos algorithm itself". **High overlap with this OQ-01.**
  - `lovasz-local-lemma-oq-04` (status in-progress, A): asymmetric LLL.

### Overlap with `lovasz-local-lemma-oq-03`

Both seeker-selected slugs (`prob-method-lovasz-local-oq-01` and
`lovasz-local-lemma-oq-03`) target the Moser–Tardos algorithm. Reading their
descriptions carefully:

| Slug | Description | Distinguishing feature |
|------|-------------|-----------------------|
| `lovasz-local-lemma-oq-03` | "Formalize the Moser-Tardos algorithm itself (not just its termination bound)" | Focuses on *the algorithm* (definition + correctness) |
| `prob-method-lovasz-local-oq-01` (this) | "Formalize the full Moser-Tardos resampling algorithm **with termination proof** — currently only the expected step bound is *stated*." | Focuses on **the termination proof** (algorithm + bound) |

In practice these are the same problem. The recommended convention going
forward is to treat **`prob-method-lovasz-local-oq-01`** as the canonical
slug (it's the parent-namespaced version, consistent with the marquee
initiative), and **`lovasz-local-lemma-oq-03`** as a duplicate to be
graduated/closed when this one is completed. This S1 OBSERVE produces only
markdown/JSON, so the duplication risk is minimal at this stage.

### Mathlib API readiness

Surveyed via `grep` in `/Users/rwalters/GitHub/lean-genius/proofs/.lake/...`
where possible; otherwise from my prior Mathlib knowledge:

| Need | Mathlib API | Readiness |
|------|-------------|-----------|
| Independent variables | `MeasureTheory.Measure.Pi` | Ready |
| Pairwise / mutual independence | `Probability.Independence.Basic` | Ready |
| Conditional expectation | `Probability.ConditionalExpectation` | Ready |
| Finite distributions | `Probability.ProbabilityMassFunction.Basic` | Ready |
| `PMF`-bind / `PMF`-seq Markov chain | `Probability.PMF.Monad` | Ready |
| Stopping times / hitting times | `Probability.MartingaleStopping` (partial) | Partial |
| Galton–Watson branching process | None | **Missing** |
| Dependency graph (variable-collision) | `Combinatorics.SimpleGraph.Basic` | Ready (custom encoding needed) |
| Rooted labelled trees | `Combinatorics.SimpleGraph.Path` (limited) | Inadequate |

**Conclusion**: Most pieces are present; the missing infrastructure is
(i) witness-tree inductive type, (ii) Galton-Watson process or a
generating-function workaround.

## Decomposition Snapshot (OQ-01-A / OQ-01-B / OQ-01-C)

```
OQ-01-A  Algorithm and probability space      [~300 LOC, 1-2 PRs]
         ├── PMF-based finite model (recommended start)
         ├── def isViolated, def step
         ├── statement of mt_terminates_as
         └── delivers: MoserTardos.lean skeleton

OQ-01-B  Witness trees                          [~500 LOC, 2-3 PRs]
         ├── inductive WitnessTree
         ├── def isProper
         ├── def extractWitness (partial)
         ├── theorem witness_valid
         └── theorem witness_prob_bound

OQ-01-C  Galton-Watson / generating-function    [~400 LOC, 2-3 PRs]
         ├── def gwTreeProb (or direct generating-function)
         ├── theorem gw_sum_bound  (Σ_τ ≤ x_i/(1-x_i))
         └── theorem mt_expected_step_bound
```

## Insights from S1

1. **The algorithm + bound is a separable layer above the existing LLL** —
   none of the existing 364 lines of `LovaszLocalLemma.lean` need to change.
   A new file `Proofs/MoserTardos.lean` is the right home for OQ-01.

2. **Variable-version vs event-version** — Moser–Tardos requires the
   *variable-collision* dependency graph (`i ~ k ↔ vbl(Aᵢ) ∩ vbl(Aₖ) ≠ ∅`),
   NOT the more general "probabilistic dependence" graph used in the
   set-theoretic LLL. The parent file's `IsValidDepGraph` is abstract enough
   to support both, but the algorithm needs the variable model.

3. **Witness trees are the hardest part** — both definitionally (rooted
   labelled trees with `Finset`-valued children) and proof-theoretically
   (the validity lemma is a careful induction on execution length).
   Witness trees should be defined as their own inductive type, not as
   `SimpleGraph` subgraphs.

4. **PMF model is sufficient** — all known marquee applications (k-SAT,
   hypergraph colouring, Latin squares) use finite alphabets, so a `PMF`-
   based model avoids the full measure-theoretic apparatus. The
   measure-theoretic extension can be deferred to `lovasz-local-lemma-oq-01`.

5. **Symmetric case as warmup is real** — the existing
   `symmetric_moser_tardos_bound` already gives the n/d simplification.
   A first-shot S2 could state and prove `mt_symmetric_terminates_as`
   directly from the symmetric sum, without the general witness-tree
   machinery. This would be a small ~50-LOC PR that validates the algorithm
   skeleton.

## Next Action (S2 target)

**Choice**: S2 should produce **OQ-01-A skeleton**:

1. Create `Proofs/MoserTardos.lean` (~150 LOC):
   - `structure MTProblem (n m : ℕ) (Σ : Fin n → Type)` — n vars, m events,
     alphabets per variable, dependency graph
   - `def MTState (P : MTProblem) := (∀ j, P.Σ j)` — current assignment
   - `def isViolated : MTState → Fin m → Prop` (or `Bool`)
   - `def step : MTState → PMF MTState` — one resampling step
   - `def run : ℕ → MTState → PMF MTState` — iterated step
   - statement (with `sorry`): `theorem mt_expected_step_bound`
   - statement (with `sorry`): `theorem mt_terminates_as`

2. Add gallery entry: `src/data/research/proofs/moser-tardos/` (defer to S3).

3. State explicitly: S2 is a scaffold PR; sorries are OQ-01-B/C deferred.

S2 deliverable: 1 new Lean file + sorry-listed proof obligations + state.md
update to `phase: ACT`. Build-verified via Docker.

## Risk Assessment

- **Race risk**: LOW (slug seeker-added 2026-05-12 ~5h ago; no open PRs; no
  orphan branches; no recent commits for `moser-tardos` or sibling slugs).
- **Build-fragility risk**: ZERO this session (S1 OBSERVE produces only
  markdown/JSON files; no Lean changes).
- **Duplication risk** with `lovasz-local-lemma-oq-03`: MEDIUM. Mitigation:
  flag in problem.md; let the dedup be resolved during S2 ACT.

## Open Questions for Future Sessions

- Should OQ-01 deliver the *measure-theoretic* Moser–Tardos (general
  probability spaces), or just the `PMF`/finite-alphabet version?
  **Recommendation**: PMF-only here; defer measure-theoretic to
  `lovasz-local-lemma-oq-01`.

- Should the witness-tree type be parametrised by the dependency graph (as a
  `SimpleGraph`) or by the parent `MTProblem`?
  **Tentative**: parametrise by `SimpleGraph` so the type is reusable.

- Should the Galton–Watson step be replaced by a direct generating-function
  argument?
  **Tentative**: yes — building a Galton–Watson process API is a separate
  marquee effort and out of scope here.

- Decision about the duplicate `lovasz-local-lemma-oq-03`: graduate to
  "blocked"? Or merge content?
  **Tentative**: leave both open; when this OQ-01 reaches `completed`,
  graduate `lovasz-local-lemma-oq-03` to `completed` with a cross-reference.


## Session 2026-07-24 (researcher-3, S17): witness_valid landed

Relational formalization of the MT §4 extraction (`HasMatchAt` / `Attach` /
`AttachDeepest` / `ExtractsFrom`) + `isProper_attach` + `witness_valid`
(every extracted tree is proper). +144 LOC (580→724), 0 sorries, 0 axioms,
host-verified v4.31 (borrowed sibling oleans), foundational axioms only.

Technique notes:
- Relational-not-computational extraction avoids the `collisionAdj`
  noncomputability wall entirely; propriety needs only match + maximality.
- Distinct-siblings falls out of depth-maximality: a same-labelled child of
  the attach target is a strictly deeper match since `j ∈ Γ⁺(j)`.
- `isProper` (match-def) is NOT an inductive — `simp only [isProper] at hp ⊢`
  before destructuring/anonymous-constructor.
- `subst` on `l = j` can eliminate the wrong variable (`j` disappears);
  `rw [show l = j ...]` in the goal instead.
- List-splitting constructor `pre ++ t :: post → pre ++ t' :: post` makes the
  Nodup-preservation step a pure `List.map_append/map_cons` rewrite once
  `labelOf t' = labelOf t` is known.
