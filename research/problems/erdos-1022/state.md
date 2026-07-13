# Current State

**Phase**: AXIOMATIZED — matching case proved; sparsity conjecture and LLL bridge axiomatized
**Since**: ~2026-03 (multiple sessions; first scaffold 2026-03-28 per problem JSON `started`;
last research PR `erdos-1022 — degree-bounded ⇒ sparse via double counting` #13269 merged
2026-04-27)
**Iteration**: 6 shipped (S1 STATE-SYNC #18886 2026-05-13, S2 STATE-SYNC 2026-05-17)

## Status Summary

Three Lean files now ship in a stable axiomatized rest state. Numbers below
use the **canonical mechanic regex** convention (raw inclusive
`^(protected|private|noncomputable )*(theorem|lemma) ` for theorems and
`^(noncomputable )?(def|abbrev|structure|class|inductive|instance) ` for
definitions; raw `wc -l` for lines), matching `src/data/proofs/erdos-1022/meta.json`.

| File | Lines | Theorems | Defs | Axioms | Sorries | Role |
|------|------:|---------:|-----:|-------:|--------:|------|
| `Erdos1022Problem.lean` | 599 | 28 | 7 | 1 | 0 | Main file — Property B, sparsity, matching ⇒ Property B, first-moment, degree-bounded ⇒ sparse |
| `Erdos1022OQ01.lean` | 164 | 8 | 3 | 0 | 0 | Property $B_k$ ($k$-colorability) hierarchy and monotonicity |
| `Erdos1022OQ03.lean` | 419 | 21 | 8 | 1 | 0 | LLL infrastructure: monoProb, lllThreshold, propertyB consequences |
| **Total** | **1182** | **57** | **18** | **2** | **0** | |

(S1 #18886 reported 600/26/6, 165/8/3, 420/21/8 = 1185/55/17 using a narrow
`^theorem ` regex that excluded the two `private lemma` declarations at lines
397 and 416 of `Erdos1022Problem.lean` and the one `private def` at line 388,
plus an off-by-one line count on all three files. S2 propagates the canonical
counts.)

`meta.json` is already wired for two gallery entries:

- `src/data/proofs/erdos-1022/meta.json` — gallery entry for the main file,
  `meta.lineCount=599`, `meta.theoremCount=28`, `meta.definitionCount=7`,
  `meta.axiomCount=1` (canonical, matches actual file).
- `src/data/proofs/erdos-1022-oq-01/meta.json` — gallery entry for OQ-01,
  `meta.lineCount=164`, `meta.theoremCount=8`, `meta.definitionCount=3`,
  `meta.axiomCount=0` (canonical, matches actual file).
- **No `src/data/proofs/erdos-1022-oq-03/` exists yet** — OQ-03 (LLL bridge)
  is research-only; pending a gallery wiring decision.

This S2 STATE-SYNC commit does not touch any gallery `meta.json`.

### Iteration Ledger

| Iter | Date | Kind | PR | Notes |
|------|------|------|-----|-------|
| 1–4 | 2026-03 to 2026-04-27 | scaffold + proofs | #7595, #7630, #7781, #7833, #8322, #13269 | Built Erdos1022Problem.lean, OQ01.lean, OQ03.lean from stub; proved matching case + first-moment + degree-bounded ⇒ sparse |
| 5 | 2026-05-13 | S1 STATE-SYNC (doc-only) | #18886 | First-commit `state.md` + `problem.md`; JSON title/statement repair from `[Problem Title]` placeholder. Reported counts used narrow `^theorem ` and miscounted `wc -l` by +1 on each file. |
| 6 | 2026-05-17 | S2 STATE-SYNC (doc-only) | this PR | 5-field JSON `leanFiles[*]` repair to canonical mechanic counts (Problem: 600→599 LOC, 26→28 thms, 6→7 defs; OQ01: 165→164 LOC; OQ03: 420→419 LOC); state.md status table and total row aligned; gallery-meta cross-reference correction (erdos-1022/ does exist; erdos-1022-oq-03/ does not). |

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

- **S1 (#18886, 2026-05-13) preamble**: the title in
  `src/data/research/problems/erdos-1022.json` was `[Problem Title]` placeholder from
  seeker-init; S1 replaced it with `Erdős #1022 — Property B and Sparse Set Families` and
  filled in `problemStatement.formal` / `problemStatement.plain` /
  `problemStatement.whyMatters` / `knownResults` so the problem JSON matched the Lean
  reality. S1's reported counts (1185 LOC, 55 theorems, 17 defs) used narrow
  `^theorem ` regex (excluded 2 `private lemma` decls in Erdos1022Problem.lean lines 397,
  416) and narrow `^def ` regex (excluded 1 `private def` line 388) plus an off-by-one
  `wc -l` count. **S2 (this PR) repairs those 5 numeric fields.**
- **S2 canonical numbers**: `Erdos1022Problem.lean` (599 LOC, 28 theorems, 7 defs,
  1 axiom) / `Erdos1022OQ01.lean` (164, 8, 3, 0) / `Erdos1022OQ03.lean` (419, 21, 8, 1)
  — totals: **1182 LOC, 57 theorems, 18 defs, 2 axioms, 0 sorries**. Numbers match
  `src/data/proofs/erdos-1022/meta.json` and `…erdos-1022-oq-01/meta.json` canonical
  fields (set by mechanic batches under the inclusive regex convention).
- The Lean files have shipped on `main` since at least 2026-04-27 (PR #13269);
  byte-stable since (last `proofs/Proofs/Erdos1022*.lean` touch was the bulk re-import
  in #19454 sperner ACT on 2026-05-16, which re-added without modifying content).
- **No `.lean` source is edited** in this PR.
- **No gallery `meta.json` touched.** Gallery wiring is correct as of S2:
  `erdos-1022/` and `erdos-1022-oq-01/` are wired with canonical counts;
  `erdos-1022-oq-03/` is NOT wired (research-only).
- **No race detected.** `gh pr list --search "erdos-1022 in:title" --state open` returns
  empty as of the timestamp of this branch.
- **INFRA S2 snapshot (non-blocking for doc-only)**: G7 host disk 4.5 GiB available
  (RED, below 5 GiB soft floor; same Path-A window as concurrent erdos-301 S3
  cycle); G8 docker server at 5s probe timeout (RED, hung); G9 `.lake` host-rooted
  (GREEN).
