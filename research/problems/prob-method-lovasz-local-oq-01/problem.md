# Problem: Formalize the full Moser-Tardos resampling algorithm with termination proof

**Slug**: `prob-method-lovasz-local-oq-01`
**Parent**: `prob-method-lovasz-local`
**Created**: 2026-05-12
**Status**: NEW (S1 OBSERVE)
**Source**: seeker-selected (2026-05-12T09:56:28Z)
**Tier**: B (significance 7, tractability 5)
**Initiative**: Probabilistic Method Library (Phase 1)

## Open Question

> "Formalize the full Moser-Tardos resampling algorithm with termination proof —
> currently only the expected step bound is *stated*."

The parent file `proofs/Proofs/LovaszLocalLemma.lean` already contains:

```lean
theorem moser_tardos_termination {n : ℕ} {x : Fin n → ℚ}
    (hx_range : ∀ i, 0 ≤ x i ∧ x i < 1) :
    0 ≤ (Finset.univ : Finset (Fin n)).sum (fun i => x i / (1 - x i)) := by
  apply Finset.sum_nonneg ...
```

This is *only* the non-negativity of the bound `Σ xᵢ/(1-xᵢ)`. The actual
Moser–Tardos theorem says this quantity is an **upper bound on the expected
number of resamplings** when the algorithm is run on bad events satisfying the
general LLL inequality. **The algorithm itself is not defined**, nor is the
underlying probability space, nor any link to expected resamplings.

OQ-01 is to close this gap: define the algorithm, state and prove termination,
and bound the expected step count by `Σ xᵢ/(1-xᵢ)`.

## Formal Statement

### The Moser–Tardos Algorithm (variable version)

Fix:
- A finite collection of independent random variables `V₁, …, Vₙ : Ω → S`
  on a probability space `(Ω, μ)` (typically each `Vⱼ` is uniform on a finite
  alphabet `Sⱼ`).
- A finite collection of "bad events" `A₁, …, Aₘ : (∀ j, Sⱼ) → Prop`, each
  `Aᵢ` depending on a fixed subset `vbl(Aᵢ) ⊆ {1, …, n}` of variable indices.

Define the **dependency graph** `Γ` on `{1, …, m}` by `i ~ k ↔ vbl(Aᵢ) ∩
vbl(Aₖ) ≠ ∅` (note: this is the variable-collision graph, NOT a generic
"probabilistic dependence" graph).

```text
MOSER–TARDOS(A, V):
  draw V₁, …, Vₙ independently
  while ∃ i, Aᵢ(V) holds:
    pick any such i (arbitrary deterministic rule)
    resample {Vⱼ : j ∈ vbl(Aᵢ)} independently
  return V
```

### Termination Theorem (Moser–Tardos 2010)

If there exist `x : Fin m → [0,1)` such that for every `i`:
$$
\Pr[A_i] \le x_i \prod_{k \sim i} (1 - x_k),
$$
then almost surely the algorithm terminates, and:
$$
\mathbb{E}[\#\text{resamplings of } A_i] \le \frac{x_i}{1 - x_i}.
$$
Summing over `i` gives `𝔼[total resamplings] ≤ Σᵢ xᵢ/(1−xᵢ)`, the
already-stated bound.

### Why This Matters

Moser–Tardos turns the LLL from a pure-existence statement into a
**polynomial-time randomised algorithm** that constructively avoids all bad
events. The algorithm is the canonical bridge between the probabilistic method
and explicit algorithm design (k-SAT solvers, hypergraph colouring,
Latin-square completion, etc.).

A full Lean formalisation of Moser–Tardos would be the first machine-checked
construction of an LLL avoidance, and provides the missing constructive
counterpart to the symmetric/general LLL already in the gallery.

## Three-Part Decomposition (Roadmap)

Per the marquee-initiative pattern, we decompose into independently shippable
sub-tasks:

### OQ-01-A: Algorithm and Probability Space

Define the algorithmic substrate. Two design choices:

1. **`PMF`-based finite model** — represent the state as a `PMF (Fin n → Sⱼ)`,
   the algorithm as a `Nat → PMF` Markov chain, and termination as
   `tendsto (fun t => PMF.support (μₜ).filter badConfig) 0`. Avoids the
   need for general measure spaces.
2. **`MeasureTheory` general model** — define the algorithm on a fixed
   probability space using `Mathlib.MeasureTheory.Measure.pi` for variable
   independence and `MeasureTheory.MeasurableSpace.comap` for vbl-restricted
   measurability.

Choice (1) is sufficient for the symmetric LLL with finite alphabets and is
the recommended starting point.

**Deliverable**: `MoserTardos.lean` skeleton with `def algorithm` + `def
isViolated` + `def step` + statement of `mt_terminates_as`.

### OQ-01-B: Witness Trees

The proof of Moser–Tardos uses a combinatorial object called a **witness tree**
(or "log-tree"). A witness tree `τ` rooted at event `i` records, in a specific
way, the cascade of resamplings that triggered the step where `i` was selected.

Key definitions:
- `inductive WitnessTree (Γ : Sym2-graph) (m : ℕ)` — a rooted, labelled tree
  where children of a node labelled `i` are distinct and labelled with
  elements of `Γ(i) ∪ {i}`.
- `def isProper : WitnessTree → Prop` — children labels pairwise distinct in
  `Γ(i) ∪ {i}`.
- `def Pr_τ : WitnessTree → ℝ≥0` — product over nodes of `Pr[A_{label(v)}]`.

Key lemmas (to be proved or stated):
- **Validity**: Any witness tree extracted from an execution log of the
  algorithm is proper.
- **Tree-probability bound**: For a fixed proper witness tree `τ`, the
  probability that `τ` appears in the execution log is at most `∏_v
  Pr[A_{label(v)}]`.

### OQ-01-C: Galton–Watson Coupling and the Bound

Bound `Σ_{τ rooted at i, proper} ∏_v Pr[A_{label(v)}] ≤ x_i / (1 - x_i)` by
coupling with a Galton–Watson branching process where each node labelled `j`
independently has, for each `k ∈ Γ(j) ∪ {j}`, a child of label `k` with
probability `x_k`.

Key calculation:
$$
\sum_{\tau \text{ proper, root}=i} \prod_v \Pr[A_{label(v)}]
\le \frac{1}{\prod_{k \sim i \cup \{i\}} (1-x_k)} \cdot
\sum_{\tau \text{ proper, root}=i} \Pr_{GW}[\tau]
$$
and the right-hand sum is at most `x_i/(1-x_i)` by a Galton-Watson
generating-function calculation.

**This is where the LLL inequality is used**: the bound
`Pr[A_j] ≤ x_j ∏_{k ~ j}(1 - x_k)` is exactly what makes the per-event
contribution telescope to `x_j` when reweighted by the missing
`(1 - x_k)` factors.

## Dependencies

| Direction | Problem | Relationship |
|-----------|---------|--------------|
| Depends on | `prob-method-lovasz-local` (parent) | Provides general/symmetric LLL inequality |
| Depends on | `prob-method-expectation` | Probability framework |
| Blocks | `lovasz-local-lemma-oq-03` | "Formalize the Moser-Tardos algorithm itself" — substantive overlap; this OQ-01 is the constructive companion. |
| Sibling | `lovasz-local-lemma-oq-04` | Asymmetric / variable LLL — Moser-Tardos applies as-is |

## Mathlib API Survey

### Available (Mathlib 4)

- `Mathlib.Probability.IdentDistrib` — identically distributed RVs
- `Mathlib.Probability.Independence.Basic` — independence of σ-algebras/RVs
- `Mathlib.MeasureTheory.Measure.IsProbabilityMeasure` — base type
- `Mathlib.MeasureTheory.Measure.Pi` — product measure (for V₁ ⊗ … ⊗ Vₙ)
- `Mathlib.MeasureTheory.Function.LpSpace` — expectation
- `Mathlib.Probability.ConditionalProbability` — `Pr[A ∣ B]`
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — `PMF α`
- `Mathlib.Probability.ProbabilityMassFunction.Monad` — `PMF`-bind, `PMF`-seq
- `Mathlib.Combinatorics.SimpleGraph.Basic` — dependency graph
- `Mathlib.Combinatorics.SimpleGraph.Subgraph` — `Γ(i) ∪ {i}` is a closed neighbourhood

### Missing (must be built)

- **Witness trees** — a new inductive type. The closest Mathlib analogue is
  `Mathlib.Combinatorics.SimpleGraph.Path`, but witness trees are *labelled,
  rooted, and the children of each node are a Finset rather than a list*.
- **Galton–Watson branching processes** — Mathlib has `PMF` but no branching
  process API. We may avoid this by giving a direct generating-function proof.
- **Execution-log semantics for a Markov chain on a state space**: `PMF`-bind
  iteration exists, but the witness-tree extraction is a custom recursion.

## Three Candidate Approaches

### Approach 1: Symmetric-LLL Specialization First

Specialise to the **symmetric case** (all `xᵢ = 1/(d+1)`, all `Pr[Aᵢ] ≤
1/(e(d+1))`). Avoid the general witness-tree machinery; use a simpler "fixed
depth" counting argument that bounds expected length by `n/d`.

**Pros**: Reuses `symmetric_moser_tardos_bound` already in `LovaszLocalLemma.lean`.
**Cons**: Doesn't deliver the full Moser–Tardos result; this OQ-01 then becomes
"already done" trivially.
**Verdict**: Insufficient. Reject as the *only* deliverable; can be S2 warmup.

### Approach 2: Direct Witness-Tree Proof (Moser–Tardos 2010 §4)

Implement the full witness-tree construction:
1. Define `WitnessTree Γ` as an inductive type.
2. Define algorithm execution as a sequence in `PMF`; extract witness-tree
   from log.
3. Prove validity + probability bound + Galton-Watson sum-bound.

**Pros**: Faithful to the published proof; gives the strongest result.
**Cons**: Witness-tree extraction is the technically hardest piece; Galton-
Watson coupling needs new infrastructure.
**Verdict**: Right long-term target. Decompose into A/B/C above.

### Approach 3: Entropy-Compression (Moser 2009, k-SAT)

The original Moser k-SAT proof predates the witness-tree refinement and uses an
entropy-compression argument: bounding the length of a compression of the
random-bit sequence used by the algorithm.

**Pros**: More elementary than witness trees; bounds the worst-case length
deterministically (with high probability).
**Cons**: Only gives the symmetric Moser–Tardos result; doesn't generalise to
asymmetric `xᵢ`. Information-theoretic infrastructure (entropy of random-bit
sequences) is partial in Mathlib.
**Verdict**: Possible alternative for OQ-01-symmetric only.

**Recommended path**: Approach 2 with the OQ-01-A/B/C decomposition. Start
with OQ-01-A (algorithm definition in `PMF` model).

## Key Difficulties

1. **Algorithm as fixpoint vs PMF stream** — defining a "run-until-no-bad-
   event-holds" loop in Lean requires either a `Decidable` decision procedure
   or a non-constructive iteration on `PMF`. The `PMF`-bind iteration is the
   right starting point.
2. **Independence of resampling** — every `step` resamples only `vbl(Aᵢ)`, so
   the resampled coordinates must be independent of the un-resampled ones.
   This is a `MeasureTheory.Measure.Pi.restrict` argument.
3. **Witness-tree extraction is partial** — the function `executionLog →
   WitnessTree` is *only defined when the algorithm has produced enough
   resamplings*; needs `Option` or `Part` wrapping.
4. **The Galton–Watson sum** — `Σ_τ Pr_GW[τ] ≤ 1` (the GW process is honest)
   is the easy part; bounding `Σ_τ ∏_v Pr[A_{label(v)}] ≤ x_i/(1-x_i)` via
   re-weighting requires a generating-function-style sum.
5. **Connecting to expected step count** — `Σ_τ Pr_τ = 𝔼[#resamplings of i]`
   uses the witness-tree-per-resampling bijection, which is again partial /
   `Option`-valued.

## Tractability Assessment

**Difficulty**: Hard
**Tractability**: 5/10
**Significance**: 7/10

**Justification**:
- Mathematically standard but Lean-novel (no existing formalisation found in
  Mathlib4 or any visible Lean formalisation gallery as of 2026-05-12).
- The witness-tree object is genuinely new code (~150 LOC inductive + ~300
  LOC lemmas).
- Galton-Watson coupling is the hardest piece, but a direct generating-
  function proof can bypass it.
- The symmetric specialisation (Approach 1/Approach 3 hybrid) is more
  tractable and would already be a real contribution.

**Estimated Effort**:
- OQ-01-A (algorithm + state space): 1-2 PRs (~300 LOC)
- OQ-01-B (witness trees + tree-prob bound): 2-3 PRs (~500 LOC)
- OQ-01-C (Galton-Watson / generating-function sum): 2-3 PRs (~400 LOC)
- **Total**: 5-8 PRs, comparable to a marquee sub-theorem.

## References

### Papers
- **Moser & Tardos (2010)** — *A constructive proof of the general Lovász
  Local Lemma*. J. ACM 57(2). The canonical reference for OQ-01.
- **Moser (2009)** — *A constructive proof of the Lovász Local Lemma* (STOC).
  The original entropy-compression argument for symmetric LLL.
- **Spencer (2011)** — *Asymptopia* §4, an expository account of the witness
  tree machinery.
- **Alon & Spencer** — *The Probabilistic Method* (3rd ed.) §5.7, witness
  tree proof of Moser–Tardos.

### Mathlib targets

- `Mathlib.MeasureTheory.Measure.Pi`
- `Mathlib.Probability.Independence.Basic`
- `Mathlib.Probability.ProbabilityMassFunction.Monad`
- `Mathlib.Combinatorics.SimpleGraph.Basic`

### Internal cross-references

- `Proofs/LovaszLocalLemma.lean` — parent, contains the stated bound.
- `prob-method-expectation` — basic probability framework.
- `lovasz-local-lemma-oq-03` — sibling "Formalize the Moser–Tardos algorithm".
  Substantial overlap; coordinate before duplicating.
- `lovasz-local-lemma-oq-04` — variable / asymmetric LLL. Moser–Tardos applies
  unchanged.

## Metadata

```yaml
tags:
  - probabilistic-method
  - combinatorics
  - graph-theory
  - lovasz-local-lemma
  - moser-tardos
  - constructive-algorithm
  - marquee-phase-1
related_proofs:
  - prob-method-lovasz-local
  - prob-method-expectation
  - prob-method-alteration
difficulty: hard
source: seeker-selected
parent_oq: prob-method-lovasz-local
created: 2026-05-12
```
