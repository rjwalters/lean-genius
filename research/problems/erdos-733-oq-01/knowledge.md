# Erdős #733 OQ-01 — The limiting constant λ = lim log f(n)/√n

## Problem

For an $n$-point configuration in $\mathbb{R}^2$, a *line-compatible sequence* is the
sorted multiset of point-counts over its **rich lines** (lines containing $\ge 2$
points). Let $f(n)$ be the number of distinct line-compatible sequences.
Szemerédi–Trotter (1983) proved $f(n) = \exp(\Theta(\sqrt n))$. Erdős's follow-up,
recorded as this OQ, asks:

> Does $\lambda = \lim_{n\to\infty}\dfrac{\log f(n)}{\sqrt n}$ exist, and what is its value?

This is **OPEN**. The gallery file `proofs/Proofs/Erdos733Problem.lean` encodes only
`lower_bound : ∃ c>0, f(n) ≥ exp(c√n)` and `upper_bound : ∃ C>0, f(n) ≤ exp(C√n)`
as axioms — no explicit constants.

## Session 2026-06-14 (Session 1) — ORIENT

**Mode**: FRESH · **Outcome**: progress (explicit lower bound on the constant)

### Result: an explicit, rigorously-verified lower bound on λ

**Claim.** $\displaystyle \liminf_{n\to\infty}\frac{\log f(n)}{\sqrt n}\ \ge\ \pi\sqrt{2/3}\approx 2.5651.$

**Construction.** Take any multiset of integers $\ge 3$ with sum $s\le n$ ("parts").
Realize each part $a$ as its own *generic* line carrying exactly $a$ points, and place
the remaining $n-s$ points in general position. Generically the only lines with $\ge 3$
points are the chosen ones; every other rich line carries exactly $2$ points. The
realized sequence is therefore
$$[\text{parts}\ge 3]\ \cup\ \big[\,2\text{ repeated } \tbinom n2-\textstyle\sum_i\binom{a_i}{2}\text{ times}\,\big],$$
which is **determined by and determines** the multiset of parts $\ge 3$. Distinct
multisets give distinct line-compatible sequences, so
$$f(n)\ \ge\ Q(n):=\#\{\text{partitions of any }s\le n\text{ into parts}\ge 3\}.$$
Excluding parts $1,2$ only multiplies the partition generating function by the
polynomial $(1-x)(1-x^2)$, leaving the Hardy–Ramanujan exponential rate unchanged:
$\log Q(n)\sim \pi\sqrt{2n/3}$. Hence $\lambda \ge \pi\sqrt{2/3}$ (as a liminf).

### Verification (durable, exact arithmetic)

`verify_lower_constant.py` (committed):
- For $n=4,\dots,12$: realizes **every** parts-$\ge 3$ construction with exact $\mathbb{Q}$
  coordinates, recomputes the rich-line multiset from scratch, and confirms (i) each
  construction realizes its predicted sequence and (ii) the realized sequences are
  pairwise distinct. The distinct count equals $Q(n)$ exactly (3,4,6,8,11,15,20,26,35),
  with **0 mismatches, 0 collisions** — so the construction is valid and injective.
- Hardy–Ramanujan check: $\log Q(n)/\sqrt n$ rises toward $\pi\sqrt{2/3}=2.5651$
  (1.55 at $n{=}50$ → 2.35 at $n{=}4000$; convergence is slow, governed by the
  $O(\log n/\sqrt n)$ correction in $\log p(n)=\pi\sqrt{2n/3}-\tfrac34\log n+O(1)$).

### Key Findings
- The constant problem is genuinely open; only the $\Theta$ (not the constant) is known.
- $\pi\sqrt{2/3}\approx 2.5651$ is a clean, elementary, rigorous **lower** bound on
  $\lambda$ — sharper than the gallery's "$\exists c>0$". It need not be tight: the
  $\sqrt n\times\sqrt n$ grid (Erdős's original construction) may yield a larger constant
  by also using rich lines of intermediate multiplicity; pinning the grid constant is
  harder and was not attempted.
- **Upper side is the hard direction**: a naïve count of $(m_2,m_3,\dots)$ tuples
  satisfying the pairs constraint $\sum_k \binom k2 m_k\le\binom n2$ vastly overshoots
  $\exp(\Theta(\sqrt n))$, so the Szemerédi–Trotter upper constant requires the full
  realizability structure, not a counting bound. No explicit $C$ extracted.
- **Formalization note (integrity)**: in `Erdos733Problem.lean` the definition
  `countLineCompatible n` (L103–105) is a placeholder equal to $2^n-1$
  (`(range n).powerset.filter (·.card>0)).card`), *not* $f(n)$. The `lower_bound`/
  `upper_bound` axioms are thus stated about a stand-in count. Correcting this needs a
  genuine (noncomputable) definition of line-compatibility over $\mathbb{R}^2$; flagged,
  not fixed (out of scope for this OQ, and unbuildable under the current Docker blackout).

### Files Modified
- `research/problems/erdos-733-oq-01/verify_lower_constant.py` (new)
- `research/problems/erdos-733-oq-01/knowledge.md` (new)
- `src/data/research/problems/erdos-733-oq-01.json` (new)

### Next Steps
- Compute the $\sqrt n\times\sqrt n$ grid's sequence-count constant for a possibly
  larger lower bound (Erdős's "easy" construction may beat $\pi\sqrt{2/3}$).
- Extract an explicit upper constant $C$ from the quantitative Szemerédi–Trotter
  rich-lines bound (the genuinely hard half).
- If pursuing Lean: replace the placeholder `countLineCompatible` with a real
  definition, then state `lower_bound` with the explicit $c=\pi\sqrt{2/3}-\varepsilon$.

---

## Session 2026-06-15 (exact small-n f(n), researcher-4) — DATA

**Mode**: build-free (dual blackout: Docker DOWN, Aristotle MCP 404).
**Outcome**: progress — the **first exact values of f(n) itself** (prior sessions
computed only bounds: S1's $Q(n)$ lower bound, S2/S3's asymptotic constant bounds,
both still open PRs #24269/#24295). Orthogonal to those.

### Result: $f(3)=2,\ f(4)=3,\ f(5)=5,\ f(6)=9$ (all exact / stabilized)

Computed by exhaustive enumeration of all $n$-subsets of a $g\times g$ integer grid
(exact arithmetic), collecting distinct rich-line sequences, with $g$ grown until the
count **stabilizes** (every grid config is realizable ⇒ count is a rigorous lower
bound on $f(n)$, and equals $f(n)$ once saturated). `verify_small_n_fn.py` (committed).

| $n$ | $f(n)$ | stabilized? | $Q(n)$ (S1 lower bд) | placeholder $2^n-1$ |
|----|--------|-------------|----------------------|---------------------|
| 3  | 2      | ✓ ($3,4,5$ grids agree) | 2 | 7 |
| 4  | 3      | ✓ ($4,5,6$)             | 3 | 15 |
| 5  | **5**  | ✓ ($5,6,7$)             | **4** | 31 |
| 6  | **9**  | ✓ ($6{\times}6$ and $7{\times}7$ both $=9$) | **6** | 63 |

The realized sequences: $f(5)=\{[5],[4,2^4],[3,3,2^4],[3,2^7],[2^{10}]\}$;
$f(6)$ adds the multi-/concurrent-line profiles $[6],[5,2^5],[4,3,2^6],[4,2^9],
[3,3,3,2^6],[3,3,2^9],[3,3,3,3,2^3]$ (and the all-generic $[2^{15}]$) — note
$f(6)=9>Q(6)=6$, the surplus again coming from intersecting/multiple rich lines.

### Key finding: $f(5)=5 > Q(5)=4$ — the S1 lower bound is **not tight at finite $n$**

The extra sequence is $[3,3,2,2,2,2]$: **two 3-point lines sharing a common point**
(two lines of 3 through 5 points must intersect, since $3+3-1=5$). S1's construction
puts each part on its *own generic (disjoint)* line, which needs $3+3=6$ points for
two 3-lines and therefore cannot realize $[3,3,\dots]$ at $n=5$. So **intersecting
rich lines (point-sharing) genuinely add line-compatible sequences** that the
disjoint-line construction misses. This gives EXACT small-$n$ corroboration of S2's
asymptotic observation that the point-sharing grid beats disjoint lines
("$\log(G/Q)/\sqrt n \uparrow$"), and confirms $\lambda$'s true lower bound exceeds
what the $Q(n)$ family alone certifies (consistent with $\lambda \ge \pi\sqrt{2/3}$
being a floor, not the value).

### Integrity note (reconfirmed)
The gallery's `countLineCompatible n = 2^n-1` placeholder is wildly off as an estimate
of $f(n)$ (e.g. $2^4-1=15$ vs $f(4)=3$); it remains a stand-in pending a real ℝ²
line-compatibility definition (Docker-gated, out of scope here).

### Next Steps (carried)
- Extend to $f(7),f(8)$ (needs $\ge 8\times 8$ grids with symmetry reduction or the
  order-type DB; pure-Python $\binom{g^2}{n}$ is the bottleneck) to fit
  $\log f(n)/\sqrt n$ against the $[\,2.5651,\,C\,]$ bracket. So far
  $f=2,3,5,9$ for $n=3,4,5,6$.
- (unchanged) tighten the S3 upper constant; replace the Lean placeholder.

---

## Session 2026-06-15 (arrangement lower bound, researcher-8) — ACT

**Mode**: build-free (dual blackout: Docker DOWN, Aristotle MCP unavailable).
**Outcome**: progress — a structural reformulation of $f(n)$, a clean computable
lower bound $G(n)$ that **equals the exact $f(n)$ for $n\le 6$** and extends
rigorous (exact-arithmetic-verified) lower bounds to $n=7,\dots,12$, beating both
prior lower bounds (S1's $Q$, the pencil refinement $P$). The asymptotic constant
is **not** improved (honestly: $G\sim Q$ asymptotically).

### Structural reformulation: $f(n)=\#\{\text{realizable multisets of }\ge 3\text{-line sizes}\}$

The point-count of every rich line is recorded, and the number of 2-point lines is
**forced**:
$$\#(2\text{-lines}) = \binom n2 - \sum_{\ge 3\text{ lines }L}\binom{|L|}{2}.$$
So the entire line-compatible sequence is a function of the multiset of $\ge 3$-line
sizes. Hence
$$f(n)=\#\{\,M\text{ a multiset of integers }\ge 3 : \mu(M)\le n\,\},$$
where $\mu(M)$ is the minimum number of points whose $\ge 3$-rich lines have exactly
the sizes in $M$ (all other rich lines carrying 2 points; surplus points sit in
general position as 2-lines). This recasts the OQ as: count multisets by their
minimum incidence-realization budget.

### Computable lower bound $G(n)\le f(n)$ (three explicit constructions)

$\mu(M)$ itself is a hard incidence optimisation (maximise point-sharing among the
lines). Using three always-realizable constructions and taking the cheapest
OVER-estimates $\mu$, hence UNDER-counts — a rigorous lower bound. For
$M=\{a_1,\dots,a_k\}$ ($a_i\ge 3$):

| construction | budget | condition |
|---|---|---|
| disjoint (one generic line per part) | $\sum a_i$ | — |
| **pencil** (all $k$ lines concurrent at one point) | $\sum a_i-(k-1)$ | $k\ge 1$ |
| **complete arrangement** ($k$ generic lines, all $\binom k2$ pairwise intersections used) | $\sum a_i-\binom k2$ | $a_i\ge k-1\ \forall i$ |

$\mu^*(M)=\min(\text{applicable budgets})$, $G(n)=\#\{M:\mu^*(M)\le n\}$.

### Verification (durable, exact arithmetic)

`verify_arrangement_lower.py` (committed): for **every** multiset counted in $G(n)$,
$n=3,\dots,12$, it realizes the $\mu^*$-optimal construction in exact $\mathbb Q$
coordinates, recomputes the rich-line multiset from scratch, and confirms (i) the
$\ge 3$-lines are exactly $M$ (no accidental extra collinearity) and (ii) all
realized sequences are pairwise distinct. **0 mismatches, 0 collisions** for all
$n\le 12$ ⇒ every $G(n)$ below is a verified lower bound on $f(n)$.

| $n$ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 |
|----|---|---|---|---|---|---|---|----|----|----|
| $G(n)$ | 2 | 3 | 5 | 9 | **14** | **21** | **31** | **45** | **63** | **87** |
| exact $f(n)$ | 2 | 3 | 5 | 9 | ? | ? | ? | ? | ? | ? |
| $P(n)$ pencil | 2 | 3 | 5 | 7 | 11 | 15 | 22 | 30 | 42 | 56 |
| $Q(n)$ disjoint (S1) | 2 | 3 | 4 | 6 | 8 | 11 | 15 | 20 | 26 | 35 |

### Key findings

- **$G(n)=f(n)$ exactly for $n=3,4,5,6$** ($2,3,5,9$, against researcher-4's
  exhaustive grid enumeration): the three elementary constructions already realize
  *every* line-compatible sequence at small $n$. (For $n\ge 7$, $G$ is only a lower
  bound — multisets needing partial/general $b$-matching arrangements, e.g. five
  3-lines, are not in these three families, so $f(n)\ge G(n)$ with possible gap.)
- **The surplus of $f$ over the disjoint bound $Q$ is explained by point-sharing:**
  - $n=5$: $f(5)=5>Q(5)=4$ is the **pencil** $[3,3]$ — two 3-lines sharing a point
    (budget 5, not the disjoint 6). $P$ and $G$ both capture it; $G$ is tight here.
  - $n=6$: the surplus includes the **complete quadrilateral** $[3,3,3,3]$ — four
    generic lines, their 6 intersection points (budget 6) — which BOTH the disjoint
    and pencil families miss. Captured only by the complete-arrangement budget.
- **$P(n)$ = single-pencil bound** $=\#\{$partitions into parts $\ge 2$ of sum
  $\le n-1\}$: a clean closed form strictly between $Q$ and $G$, tight at $n=5$.
- **Asymptotics — no constant improvement (honesty):** $G\ge Q$ so $\lambda\ge
  \pi\sqrt{2/3}$ is preserved, but the complete-arrangement contribution alone has a
  strictly *smaller* exponential rate (forcing $a_i\ge k-1$ is rigid: numerically
  $\log G_{\mathrm{ca}}(n)/\sqrt n\approx 1.75$ at $n=6400$, still well below
  $2.5651$ and rising slowly), so the disjoint family dominates as $n\to\infty$ and
  $G(n)\sim Q(n)$. The constant $\lambda$ stays **OPEN**; closing the gap needs the
  full realizability structure (which multisets are *not* realizable — the
  Szemerédi–Trotter / forbidden-configuration content), exactly as on the upper side.

### Files Modified
- `research/problems/erdos-733-oq-01/verify_arrangement_lower.py` (new)
- `research/problems/erdos-733-oq-01/knowledge.md` (this entry)
- `src/data/research/problems/erdos-733-oq-01.json` (insights/builtItems)

### Next Steps
- The honest path to the constant: characterise *non-realizable* multisets (the
  exact incidence obstruction), since $f(n)=\#\{M:\mu(M)\le n\}$ and $G$ already
  pins the count for small $n$. Computing $\mu(M)$ exactly (min points for given
  line sizes with pairwise $\le 1$ intersection = a geometric $b$-matching /
  realizable $(p_k,\ell_m)$-configuration problem) would replace $G$ by $f$ and
  is the crux.
- Cross-check $G(7),G(8)$ against an independent exhaustive computation (e.g. the
  order-type database) to test whether $G(n)=f(n)$ persists past $n=6$.
- (unchanged) tighten the S3 upper constant; replace the Lean `countLineCompatible`
  placeholder ($=2^n-1$, Docker-gated).
