# Problem: Szemerédi's Theorem for 4-Term Progressions via Hypergraph Regularity

**Slug**: roth-theorem-oq-03
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall \delta > 0,\ \exists N_0,\ \forall N \ge N_0,\ \forall A \subseteq \mathbb{Z}/N\mathbb{Z}\ \text{with}\ |A| \ge \delta N :\ \exists\, a, d \in \mathbb{Z}/N\mathbb{Z},\ d \ne 0,\ \{a,\ a+d,\ a+2d,\ a+3d\} \subseteq A.
$$

Equivalently, writing $r_4(N)$ for the maximum size of a subset of $\{1, \dots, N\}$ containing no 4-term arithmetic progression, the goal is $r_4(N) = o(N)$.

### Plain Language

Roth's theorem (the parent gallery proof, `roth-theorem`) says every sufficiently dense set of integers contains three equally-spaced numbers $a, a+d, a+2d$. This problem asks for the next case: every sufficiently dense set contains *four* equally-spaced numbers $a, a+d, a+2d, a+3d$. This is the $k=4$ instance of Szemerédi's theorem.

The jump from 3 to 4 terms is not cosmetic. The Fourier-analytic argument that powers Roth's theorem fundamentally breaks for 4-APs: the count of 4-APs is *not* controlled by ordinary (linear) Fourier coefficients, because a set can be "quadratically structured" (e.g. concentrated on values of a quadratic phase $e^{2\pi i \alpha n^2}$) while looking pseudorandom to every linear character. The modern route that repairs this is the (hyper)graph regularity method: one models 4-AP counting by a 3-uniform hypergraph, applies a hypergraph regularity + counting lemma, and derives a removal lemma that forces a 4-AP to appear once the density is bounded below.

### Why This Matters

The $k=4$ case is the first genuinely "higher-order" case of Szemerédi's theorem and the historical dividing line between linear Fourier analysis and higher-order Fourier analysis (Gowers norms, quadratic Fourier analysis, the inverse theorem for the $U^3$ norm). Formalizing it:

- extends the gallery from linear additive combinatorics (`roth-theorem`) into the regime where the regularity method is unavoidable;
- exercises and stress-tests Mathlib's Szemerédi-regularity infrastructure (`Combinatorics.SimpleGraph.Regularity`, triangle removal, corners) at the level needed for a genuine density result;
- provides the combinatorial backbone shared with the polynomial Szemerédi and multidimensional Szemerédi theorems, and with property-testing removal lemmas in theoretical computer science.

## Known Results

### What's Already Proven

- **Roth's theorem (k=3), parent gallery proof** `roth-theorem` — `roth_density_bound` in `Proofs/RothTheorem.lean`, fully verified (0 sorries, 0 axioms), wrapping Mathlib's `roth_3ap_theorem_nat`. Provides the Fourier machinery (`parseval_on_zmod`, `fourier_large_coefficient`, `density_increment_lemma`) and the corners/regularity chain used for $k=3$.
- **Szemerédi's theorem (general $k$), classical** — Szemerédi 1975 (Acta Arith. 27) proves $r_k(N) = o(N)$ for every $k$ by an intricate combinatorial argument; not yet in Mathlib for $k \ge 4$.
- **Hypergraph removal lemma, classical** — Gowers 2007 and Nagle–Rödl–Schacht–Skokan 2005–2006 establish the hypergraph regularity + counting + removal lemmas that give a clean proof of Szemerédi's theorem; the $k=4$ case needs 3-uniform hypergraph regularity.
- **Graph regularity in Mathlib** — `Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma` (Szemerédi regularity), the triangle counting/removal lemmas, and `Mathlib.Combinatorics.Additive.Corner` are available and already power the $k=3$ corners route.

### What's Still Open

- Mathlib has **no** hypergraph regularity lemma, no hypergraph counting lemma, and no hypergraph removal lemma; only the *graph* (2-uniform) regularity method is formalized.
- No formalization of a genuine 4-AP density theorem exists in Mathlib (the qualitative $r_4(N)=o(N)$ statement).
- Higher-order Fourier analysis (Gowers $U^3$ norm, its inverse theorem) is entirely unformalized, so the Fourier route to $k=4$ is currently out of reach.

### Our Goal

Formalize the qualitative statement $r_4(N) = o(N)$ — i.e. the $\delta,N_0$ existence statement above — following the (hyper)graph-regularity/removal-lemma route, and connect it to the parent Roth formalization by reusing its AP-counting and $\mathbb{Z}/N\mathbb{Z}$ scaffolding. Concretely, the deliverable is either:

1. a full Lean proof of `four_ap_density_bound` reducing 4-APs to a hypergraph removal lemma proved from a formalized 3-uniform hypergraph regularity lemma; or
2. a *conditional* formalization that states and cleanly isolates the hypergraph removal lemma as an explicit `axiom`/hypothesis (documented per the Axiom Integrity Policy, `status: "axiomatized"`) and derives `four_ap_density_bound` from it — establishing the reduction while the regularity infrastructure is built out.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `roth-theorem` | Parent: the $k=3$ case; supplies AP-counting on $\mathbb{Z}/N\mathbb{Z}$, the corners/regularity chain, and the density-increment template | Fourier analysis on $\mathbb{Z}/N\mathbb{Z}$, Parseval, density increment, corners theorem |
| `szemeredi-theorem` | The general-$k$ statement this problem is a special case of | Regularity method, ergodic/combinatorial Szemerédi |
| `erdos-1097` | Studies common differences of 3-APs; same objects (progressions in dense sets), complementary structural questions | Additive combinatorics, extremal counting |
| `cauchy-schwarz-oq-02-oq-01` | Provides the Parseval/energy identity; Gowers norms are higher-degree analogues of the same Cauchy–Schwarz energy machinery | Cauchy–Schwarz, Parseval, $L^2$ energy |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Hypergraph regularity + removal lemma (the modern combinatorial route).** Encode 4-AP counting as a tripartite 3-uniform hypergraph whose "triangles" (in the hypergraph sense) correspond to 4-APs, apply a 3-uniform hypergraph regularity lemma and its counting lemma to obtain a hypergraph removal lemma, and conclude that a positive density of 4-APs (hence at least one nontrivial one) must exist.
   - Why it might work: This is the standard, fully rigorous proof (Gowers; Nagle–Rödl–Schacht–Skokan) and it mirrors the *graph* regularity → triangle removal → corners → Roth chain that Mathlib already realizes for $k=3$, so there is a template to imitate.
   - Risk: Mathlib has no hypergraph regularity at all. Formalizing 3-uniform regularity + counting from scratch is a very large undertaking (the index-increment / energy-boosting argument, the counting lemma with its many error terms). Realistically the full route is a multi-month effort; the near-term deliverable is the reduction with the hypergraph removal lemma isolated as a stated assumption.

2. **Approach B — Higher-order (quadratic) Fourier analysis via the $U^3$ inverse theorem.** Show that if $A$ has no 4-AP then its 4-AP count is anomalously small, deduce (via Gowers–Cauchy–Schwarz) that the $U^3[\mathbb{Z}/N\mathbb{Z}]$ norm of $1_A - \delta$ is large, invoke the inverse theorem for $U^3$ (correlation with a quadratic phase / nilsequence), and run a density increment onto a Bohr-set-like structure — the direct generalization of the parent Roth argument.
   - Why it might work: It is the closest analogue to the already-formalized `fourier_large_coefficient` + `density_increment_lemma` pipeline, so the *shape* of the argument is familiar and reuses `parseval_on_zmod`-style identities.
   - Risk: The $U^3$ inverse theorem (Green–Tao–Ziegler / Gowers) is deep and completely unformalized; quadratic phases and Bohr-set localization add substantial infrastructure. This is at least as hard as Approach A and arguably harder to formalize cleanly.

### Key Difficulties

- **Fourier analysis is insufficient for $k=4$.** Linear characters do not control 4-AP counts; the parent proof's `fourier_large_coefficient` has no direct 4-AP analogue, so a genuinely new tool (hypergraph regularity or $U^3$/Gowers norms) is mandatory.
- **No hypergraph regularity in Mathlib.** The 3-uniform regularity lemma, its counting lemma, and the removal lemma must be built (or assumed); even the correct *definitions* (regular triads, the two-level partition structure) are delicate to state formally.
- **Encoding 4-APs as hypergraph configurations.** Setting up the tripartite 3-uniform hypergraph so that hyper-triangles biject with (a linear image of) 4-APs, and transferring AP-freeness ↔ triangle-freeness, requires careful arithmetic bookkeeping (cf. the $k=3$ `apFree_imp_threeAPFree_val` transfer).
- **Quantitative vs. qualitative.** Only $o(N)$ is targeted; still, the regularity method yields tower-type bounds, and one must be careful that the formalized statement is the clean existence form, not an unusable explicit bound.

### What Would a Proof Need?

- **Key lemma 1 (encoding):** a bijective/injective correspondence between nontrivial 4-APs in $A \subseteq \mathbb{Z}/N\mathbb{Z}$ and hyper-triangles of an explicitly constructed 3-uniform hypergraph on a constant number of vertex classes.
- **Key lemma 2 (hypergraph counting/removal):** a 3-uniform hypergraph removal lemma — few hyper-triangles implies few hyperedges can be deleted to destroy all of them — from a 3-uniform regularity + counting lemma (or this stated as an isolated assumption).
- **Key lemma 3 (transfer):** AP-free ($A$ has no nontrivial 4-AP) $\Rightarrow$ the encoded hypergraph is essentially hyper-triangle-free, so by removal its density is $o(1)$, contradicting $|A| \ge \delta N$ for large $N$.
- **Technical requirements:** reuse of the parent's `ZMod N` AP-counting scaffolding; a formal 3-uniform hypergraph type with regularity/counting statements; careful $o(N)$/$N_0$ existential bookkeeping matching Mathlib's `roth_3ap_theorem_nat` style.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The mathematics is classical and rigorous (Szemerédi 1975; Gowers 2007; NRSS 2005–06), but every viable route needs infrastructure Mathlib lacks entirely — hypergraph regularity or the $U^3$ inverse theorem — so a *fully verified* proof is a large multi-month formalization.
- A tractable intermediate milestone exists: formalize the reduction to a hypergraph removal lemma (Key lemmas 1 and 3) and isolate the removal lemma itself as a documented assumption, yielding an `axiomatized` entry analogous to the parent's OQ-02 companion. This is a realistic near-term deliverable.
- Available leverage: the parent `roth-theorem` gives a working $k=3$ regularity→removal→corners template; Mathlib's `Combinatorics.SimpleGraph.Regularity` and `Combinatorics.Additive.Corner` supply the 2-uniform analogues to imitate.

**Estimated Effort**:
- Exploration: 3–5 days (fix encoding, decide Approach A vs. conditional reduction, survey Mathlib regularity API).
- If tractable (conditional reduction with removal lemma as stated assumption): 2–4 weeks.
- If hard (full hypergraph regularity from scratch, or $U^3$ route): unknown, plausibly multiple months.

## References

### Papers
- E. Szemerédi, "On sets of integers containing no $k$ elements in arithmetic progression", Acta Arith. 27 (1975), 199–245 — original proof that $r_k(N) = o(N)$ for all $k$.
- W. T. Gowers, "Hypergraph regularity and the multidimensional Szemerédi theorem", Ann. of Math. 166 (2007), 897–946 — regularity/removal proof of Szemerédi's theorem.
- B. Nagle, V. Rödl, M. Schacht, J. Skokan, "The counting lemma for regular $k$-uniform hypergraphs", Random Structures Algorithms 28 (2006), 113–179 — hypergraph counting lemma underpinning the removal route.
- W. T. Gowers, "A new proof of Szemerédi's theorem", GAFA 11 (2001), 465–588 — introduces Gowers uniformity norms; the higher-order Fourier route to $k=4$.
- B. Green, T. Tao, "An arithmetic regularity lemma, an associated counting lemma, and applications", An Irregular Mind, Bolyai Soc. Math. Stud. 21 (2010), 261–334 — modern regularity/counting framework for AP counting.

### Online Resources
- Terence Tao, "Szemerédi's theorem" and the hypergraph regularity notes on `terrytao.wordpress.com` — expository accounts of the $k=4$ / hypergraph-removal argument.
- Wikipedia, "Szemerédi's theorem" (`https://en.wikipedia.org/wiki/Szemer%C3%A9di%27s_theorem`) — statement, history, and bounds for $r_k(N)$.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma` — Szemerédi regularity lemma (2-uniform), the analogue to generalize to 3-uniform.
- `Mathlib.Combinatorics.SimpleGraph.Triangle.Removal` / `.Counting` — triangle counting and removal, the $k=3$ template.
- `Mathlib.Combinatorics.Additive.Corner.Roth` — corners theorem and `roth_3ap_theorem_nat`, reused for the $k=3$ base case.
- `Mathlib.Analysis.Fourier` and `Mathlib.GroupTheory.*` for `ZMod N` character/Parseval scaffolding shared with the parent proof.

## Metadata

```yaml
tags:
  - combinatorics
  - additive-combinatorics
  - arithmetic-progressions
  - szemeredi
  - hypergraph-regularity
  - removal-lemma
related_proofs:
  - roth-theorem
  - szemeredi-theorem
  - erdos-1097
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
