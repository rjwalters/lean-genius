# Problem: Grünbaum Lower Bound — Constructing Point Sets with ≫ n^{3/2} Four-Point Lines

**Slug**: erdos101-problem-oq-03
**Created**: 2026-07-09T15:22:59-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $P \subset \mathbb{R}^2$ be a finite planar point set with $|P| = n$ and no five points of $P$ collinear. Define the four-point-line count exactly as in the parent gallery proof `erdos101-problem`:

$$
f_4(P) \;=\; \#\bigl\{ \ell \subset \mathbb{R}^2 \text{ a line} : |\ell \cap P| = 4 \bigr\}
\;=\; \#\bigl\{\, S \in \tbinom{P}{4} : S \text{ collinear} \,\bigr\}.
$$

The goal is to establish the **lower bound**: there exists an absolute constant $c > 0$ and, for infinitely many $n$, a set $P_n$ with $|P_n| = n$, no five collinear, and

$$
f_4(P_n) \;\ge\; c\, n^{3/2}.
$$

Equivalently, $\displaystyle \max_{\substack{|P| = n \\ \text{no 5 collinear}}} f_4(P) \;=\; \Omega\!\left(n^{3/2}\right)$, witnessed by an explicit (Grünbaum-style) construction.

### Plain Language

The parent proof establishes *upper* bounds on how many lines can pass through exactly four points of a planar set (with no five collinear). This problem asks for the complementary *lower* bound: to actually build point configurations that contain **many** four-point lines — on the order of $n^{3/2}$ of them. Grünbaum's construction does this by placing points on a small family of lines/conics in a projective grid so that a huge number of collinear 4-tuples appear, while carefully avoiding any five-in-a-line. We want to formalize a concrete construction and prove it achieves at least $c\,n^{3/2}$ four-point lines.

### Why This Matters

The number $n^{3/2}$ is the historical heart of Erdős Problem #101 ($100 prize). Erdős conjectured the true maximum was $\Theta(n^{3/2})$, precisely because Grünbaum's projective construction *matched* that order from below. Although Solymosi–Stojaković (2013) later refuted the upper half of that conjecture — building sets with $n^{2 - O(1/\sqrt{\log n})}$ four-point lines — Grünbaum's $\Omega(n^{3/2})$ bound remains a clean, fully explicit, and historically pivotal lower bound. Formalizing it:

- Provides the *first proven, machine-checked lower bound* to sit against the parent proof's $n(n-1)/12$ upper bound, sandwiching the extremal function.
- Exercises constructive incidence geometry in Lean (explicit coordinates, counting collinear 4-tuples), a capability the gallery currently lacks.
- Is a stepping stone toward the far harder Solymosi–Stojaković construction.

## Known Results

### What's Already Proven

- `erdos101-problem` (`Proofs/Erdos101Problem.lean`) — machine-checked **upper** bounds: `trivial_upper_bound` ($f_4(P) \le n(n-1)/2$), `improved_upper_bound` ($f_4(P) \le n(n-1)/12$, pair-packing), and `fourCollinearThrough_bound` (at most $(n-1)/3$ four-point lines through a single point). Supplies the exact definition of `collinear`, `NoFiveCollinear`, and `fourPointLineCount` reused here.
- Grünbaum, "New views on some old questions of combinatorial geometry" (1976) — the projective-plane construction giving $\Omega(n^{3/2})$ four-point lines (the classical lower bound).
- Burr–Grünbaum–Sloane (1974, the "orchard problem") and Füredi–Palásti (1984) — companion constructions in the *no-four-point-line* regime achieving $\sim n^2/6$ collinear **triples**; structural cousins showing how collinearity constraints trade off against rich-line counts.

### What's Still Open

- Erdős #101 upper bound: is $f_4(P) = o(n^2)$? (the $100 question, still open).
- No formal (Lean) construction currently certifies **any** nontrivial lower bound on $f_4$.
- The tighter Solymosi–Stojaković $n^{2 - o(1)}$ lower bound is unformalized (a separate, harder target).

### Our Goal

Formalize an **explicit** finite point set $P_n \subset \mathbb{R}^2$ (or $\mathbb{Q}^2$) with no five collinear and prove $f_4(P_n) \ge c\,n^{3/2}$ for an explicit constant $c$, using the parent proof's `collinear`/`fourPointLineCount` definitions verbatim. A convenient, fully rational-coordinate variant of Grünbaum's idea suffices; we do not need the optimal constant, only the $n^{3/2}$ order along an infinite sequence of $n$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos101-problem | Parent proof; supplies `collinear`, `NoFiveCollinear`, `fourPointLineCount` definitions and the matching upper bounds this lower bound is measured against | Signed-area determinant collinearity, Finset pair-packing, `Finset.card_biUnion` |
| erdos-101 | Canonical Erdős #101 entry with full historical context on Grünbaum's construction and the $n^{3/2}$ conjecture | Problem exposition, incidence-geometry survey |
| erdos-104 | Curve-analogue ($100 prize): unit circles containing ≥3 points; same $\Omega(n^{3/2}) \le \text{ans} \le O(n^2)$ gap and same construction philosophy | Incidence geometry, lattice/grid constructions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Explicit rational grid / lattice construction.**
   Place points on a bounded integer grid $\{0,\dots,m-1\}^2$ (so $n = m^2$) and count lines of a fixed small slope set that hit exactly four grid points, choosing the slopes so that no line of the arrangement carries five points. A carefully pruned sub-grid or a union of arithmetic progressions on a bounded number of parallel lines yields $\Theta(m^3) = \Theta(n^{3/2})$ four-point lines.
   - Why it might work: coordinates are explicit integers/rationals, so collinearity reduces to an integer determinant identity closable by `ring`/`omega`; counting collinear 4-tuples becomes a counting-lattice-points-on-lines problem amenable to `Finset` cardinality lemmas.
   - Risk: enforcing *no five collinear* on a dense grid is delicate — many grid lines carry $\ge 5$ points; the pruning to guarantee "exactly 4, never 5" is the crux and may force a messy case analysis.

2. **Approach B — Grünbaum's projective triangle-grid construction, dualized to affine coordinates.**
   Take Grünbaum's configuration of three families of concurrent lines (a projective triangular pencil) and realize the incidences as explicit affine points, giving $\Theta(n^{3/2})$ four-point lines by design, with the no-five-collinear property built into the pencil structure.
   - Why it might work: the $n^{3/2}$ order and the no-five property are *guaranteed by the geometry* rather than argued after the fact, reducing the proof to verifying a clean incidence count.
   - Risk: translating projective concurrency into Lean's affine determinant predicate requires handling points at infinity or a projective transformation, which is heavier machinery than the parent proof uses; the affine realization's coordinates may be irrational.

### Key Difficulties

- **Enforcing `NoFiveCollinear` on the construction.** The parent proof only *uses* the hypothesis; here we must *verify* it for an explicit set, which means proving a universal statement over all 5-subsets — the hardest part.
- **Counting the four-point lines from below.** We need a lower bound on `fourPointLineCount`, i.e., exhibit an *injection* from a size-$\ge c n^{3/2}$ index set into the family of collinear 4-subsets, and prove each image really has exactly four collinear points (not three, not five).
- **Choosing $n$ along a subsequence.** The clean count holds for $n$ of a special form (e.g. $n = m^2$); the spec must state the bound along that subsequence, not for every $n$.

### What Would a Proof Need?

- Key lemma 1: a `collinear`-membership lemma certifying that a designated $4$-element subset of the construction is collinear (via the explicit determinant identity), for each line in the family.
- Key lemma 2: a `NoFiveCollinear` verification for the whole construction — the universal "no 5-subset is collinear" statement, likely proved by a slope/line-classification argument.
- Key lemma 3: an injective indexing (`Finset.card_le_card_of_injOn` in reverse — a lower-bound injection) from the family of lines-with-4-points into `fourCollinearFamily`, yielding `fourPointLineCount P ≥ c * n^{3/2}` (stated with `Nat`/`Real` cardinalities as in the parent).
- Technical requirements: explicit coordinate arithmetic (`ring`, `omega`, `nlinarith`), lattice-point counting on lines, and reuse of the parent file's `collinear` / `fourPointLineCount` definitions.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- Constructive lower bounds in incidence geometry are substantially harder to formalize than the parent's counting upper bounds: one must both *build* an explicit object and *certify two* nontrivial global properties (many four-point lines AND no five collinear).
- Similar-flavored constructions have been formalized in principle (explicit finite geometric configurations, lattice-point counts), but the simultaneous "exactly four, never five" control is a genuine obstacle with no off-the-shelf Mathlib lemma.
- Mathlib provides strong support for the counting side — `Finset.card_biUnion`, `Finset.card_le_card_of_injOn`, `Finset.powersetCard`, and determinant/`ring` automation — so the *counting* half is tractable; the *no-five-collinear verification* half is where the effort concentrates.
- The parent proof already supplies the exact definitions and the symmetric `collinear` API, so no foundational scaffolding is needed.

**Estimated Effort**:
- Exploration: several days (pin down a concrete construction with a clean, provable no-five-collinear certificate)
- If tractable: 2–4 weeks (formalize the explicit set, the incidence count, and the no-five verification)
- If hard: unknown (if the affine realization forces irrational coordinates or heavy projective machinery)

## References

### Papers
- Grünbaum, B., "New views on some old questions of combinatorial geometry," *Atti dei Convegni Lincei* 17 (1976), 451–468 — source of the projective construction giving $\Omega(n^{3/2})$ four-point lines.
- Solymosi, J. & Stojaković, M., "Many Collinear k-tuples with no k+1 Collinear Points," *Discrete Comput. Geom.* 50 (2013), 811–820 — later improvement to $n^{2 - O(1/\sqrt{\log n})}$; the harder companion target.
- Burr, S.A., Grünbaum, B. & Sloane, N.J.A., "The orchard problem," *Geometriae Dedicata* 2 (1974), 397–424 — construction of $n$-point sets with $\sim n^2/6$ collinear triples and no four-point lines.
- Füredi, Z. & Palásti, I., "Arrangements of lines with a large number of triangles," *Proc. Amer. Math. Soc.* 92 (1984), 561–566 — related many-triple construction.

### Online Resources
- https://erdosproblems.com/101 — canonical statement of Erdős #101 and curator notes on the lower-bound history.
- https://terrytao.wordpress.com/2013/09/ — Tao's blog exposition "Many collinear k-tuples" of the Solymosi–Stojaković construction and Grünbaum's lower bound.

### Mathlib
- `Mathlib.Data.Finset.Card` — `Finset.card_le_card_of_injOn`, `Finset.card_biUnion` for the injective counting lower bound.
- `Mathlib.Data.Finset.Powerset` — `Finset.powersetCard` for four-subset enumeration, matching the parent's `fourPointLineCount`.
- `Mathlib.Tactic` — `ring`, `omega`, `nlinarith` for the explicit-coordinate collinearity/determinant identities.

## Metadata

```yaml
tags:
  - combinatorial-geometry
  - incidence-geometry
  - four-point-lines
  - collinearity
  - erdos-problems
  - lower-bound-construction
related_proofs:
  - erdos101-problem
  - erdos-101
  - erdos-104
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:22:59-07:00
```
