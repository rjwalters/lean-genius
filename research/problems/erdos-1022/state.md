# Current State

**Phase**: AXIOMATIZED — matching case proved; sparsity conjecture and LLL bridge axiomatized
**Since**: ~2026-03 (multiple sessions; first scaffold 2026-03-28 per problem JSON `started`;
last research PR `erdos-1022 — degree-bounded ⇒ sparse via double counting` #13269 merged
2026-04-27)
**Iteration**: 5+ shipped (exact count unrecorded; see `builtItems` in
`src/data/research/problems/erdos-1022.json` for granular log)

## Status Summary

Three Lean files now ship in a stable axiomatized rest state:

| File | Lines | Theorems | Defs | Axioms | Sorries | Role |
|------|------:|---------:|-----:|-------:|--------:|------|
| `Erdos1022Problem.lean` | 600 | 26 | 6 | 1 | 0 | Main file — Property B, sparsity, matching ⇒ Property B, first-moment, degree-bounded ⇒ sparse |
| `Erdos1022OQ01.lean` | 165 | 8 | 3 | 0 | 0 | Property $B_k$ ($k$-colorability) hierarchy and monotonicity |
| `Erdos1022OQ03.lean` | 420 | 21 | 8 | 1 | 0 | LLL infrastructure: monoProb, lllThreshold, propertyB consequences |
| **Total** | **1185** | **55** | **17** | **2** | **0** | |

`meta.json` for this slug is **not yet wired** to a gallery proof entry (no `src/data/proofs/erdos-1022/`);
both `erdos-1022-oq-01/` (the $B_k$ Lean file) and `erdos-1022-oq-03/` are independent gallery entries
with their own `meta.json`. This STATE-SYNC commit does not touch any gallery `meta.json`.

### Headline result (matching case, post all completed iterations)

`matching_has_propertyB` (Erdos1022Problem.lean §5):

```
∀ α [DecidableEq α] [Fintype α] (F : Finset (Finset α))
    (hsize : AllSizeAtLeast F 2)
    (hdeg : IsDegreeBounded F 1),
  HasPropertyB F.
```

This is **Lovász (1968) for the matching case ($c(2) = 1$) of Erdős 1022, formally proved
in Lean 4** from first principles. The companion `matching_implies_sparse` confirms
matchings are themselves 1-sparse, so `degree_one_size_two_propertyB_and_sparse` exhibits
the conjecture's matching instance: every 1-bounded-degree family of $\geq 2$-sets has both
Property B and 1-sparsity.

The general sparsity conjecture ($t \geq 3$, $c(t) \to \infty$) remains axiomatized as
`erdos_1022_conjecture`.

### Axiom inventory (2 across all three files)

**Foundational / open-conjecture axioms:**

- `erdos_1022_conjecture` (Erdos1022Problem.lean §3, line 77) — the central Erdős #1022
  statement: $\exists\, c\colon \mathbb{N}\to\mathbb{N}$ with $c(t) \to \infty$ such that
  every $c(t)$-sparse family of $\geq t$-sets has Property B. **Open** since 1973
  (Erdős–Lovász). No proof strategy in sight.

**Deep results (research-track, multi-paper proofs):**

- `lll_propertyB` (Erdos1022OQ03.lean §6, line 244) — the Lovász Local Lemma applied to
  Property B: under `monoProb t ≤ lllThreshold d`, any $t$-uniform family with intersection
  degree $\leq d$ has Property B. **Discharge path:** finite probability + LLL infrastructure
  in Mathlib — currently absent. Companion `lll_via_frequency` and the numeric LLL bound
  theorems (`lll_condition_t3_d1`, `lll_condition_t5_d3`, `lll_condition_t8_d10`) already
  show the threshold algebra works without the axiom; the axiom is the bridge from
  "threshold condition holds" to "PropertyB holds".

**No structure-encoded axioms** (`grep -E "Axioms\b" Proofs/Erdos1022*.lean` returns nothing
of substance): both axioms are free-standing `axiom` declarations. Status `axiomatized` is
honest.

## Current Focus

None active. Clean axiomatized rest state.

## Active Approach

— (none)

## Forward Levers

Three orthogonal next steps for future iterations:

1. **Discharge `lll_propertyB` via a constructive deletion proof for the matching case
   $d = 1$.** The `matching_has_propertyB` theorem already covers this regime
   non-probabilistically; an alternative path is to instantiate `lll_propertyB` at $d = 1$,
   $t = 2$ and check `monoProb 2 = 1/2 ≤ lllThreshold 1 = 1/4` — but this **fails**
   ($1/2 > 1/4$). The LLL bridge becomes useful only at $t \geq 3$; the natural next case
   is $t = 3, d = 1$ where `monoProb 3 = 1/4 ≤ lllThreshold 1 = 1/4` already holds
   (`lll_condition_t3_d1`), so a 3-uniform family with intersection degree $\leq 1$ has
   Property B. A clean combinatorial proof of this specific case (no probability needed)
   would let us drop `lll_propertyB` for $d = 1, t = 3$ at least.

2. **Mine literature for non-trivial sparse families with Property B.** Beck (1978) and
   later Radhakrishnan–Srinivasan (2000) give edge-count thresholds; translating them to
   *sparsity* thresholds for fixed $t$ would either confirm $c(t) \to \infty$ for finite
   ranges or surface an obstacle. Concrete near-term goal: formalize a $c(3) \geq 1$ result
   — every 1-sparse family of 3-sets has Property B — as a strict generalization of the
   matching theorem. Compare with `erdos_first_moment_bound` (already proved) to bracket the
   answer.

3. **Connect to OQ-01 ($k$-colorability hierarchy).** `Erdos1022OQ01.lean` proves
   $\mathrm{Property}\,B_k \to \mathrm{Property}\,B_{k+1}$ and the threshold
   $|\mathcal{F}| < k^{t-1}/(k-1)$ implication. A natural lemma to add: under the same
   sparsity hypothesis, $c(t,k)$-sparse families have Property $B_k$ — i.e., generalize the
   conjecture statement. This would extend the OQ-01 hierarchy from the threshold regime
   into the sparsity regime, mirroring the Erdős 1022 generalization.

## Honesty

- **Title in `src/data/research/problems/erdos-1022.json` is still `[Problem Title]`**
  placeholder from the original seeker-init scaffold; this STATE-SYNC commit replaces it
  with `Erdős #1022 — Property B and Sparse Set Families` and fills in
  `problemStatement.formal` / `problemStatement.plain` / `problemStatement.whyMatters` /
  `knownResults` so the problem JSON matches the Lean reality (1185 LOC, 55 theorems,
  axiomatized, $c(2) = 1$ Lovász matching case proved).
- The Lean files have shipped on `main` since at least 2026-04-27 (PR #13269); the JSON
  metadata is the lagging document.
- **No `.lean` source is edited** in this PR; the axiom counts in the table above are read
  from current `origin/main` heads. `Erdos1022Problem.lean` (lineCount 600, axiom 1) /
  `Erdos1022OQ01.lean` (165, 0) / `Erdos1022OQ03.lean` (420, 1) — totals: 1185 LOC,
  2 axioms, 0 sorries.
- **No gallery `meta.json` touched.** The slug `erdos-1022` has no gallery proof directory;
  `erdos-1022-oq-01/` and `erdos-1022-oq-03/` are separately wired.
- **No race detected.** `gh pr list --search "erdos-1022 in:title" --state open` returns
  empty as of the timestamp of this branch.
