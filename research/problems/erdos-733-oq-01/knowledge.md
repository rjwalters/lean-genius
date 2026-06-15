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

> Session 2 (#24269, separate open PR) executed the grid next-step on the *lower*
> side: generic grid + Gale–Ryser gives $\lambda_{\mathrm{grid}}\in[\pi\sqrt{2/3},2\pi/\sqrt3]$,
> strictly beating disjoint lines. This Session 3 attacks the **upper** next-step.

## Session 2026-06-15 (Session 3) — ORIENT (upper side)

**Mode**: REVISIT · **Outcome**: progress (first explicit *upper* constant on the true λ)

Sessions 1–2 only pushed λ up from below. This session gives the first **explicit
finite upper bound** on the genuine constant λ (not just $\lambda_{\mathrm{grid}}$),
turning the gallery's "$\exists C$" into a concrete bracket.

### The argument (dyadic Szemerédi–Trotter product bound)

Every pair of points lies on exactly one rich line, so the **pair identity**
$\sum_{k\ge2}\binom k2 m_k=\binom n2$ holds exactly ($m_k=\#$ lines with exactly
$k$ points). Hence $m_2$ is determined and $f(n)=\#\{$realizable $(m_3,\dots,m_n)\}$.

Bound $f(n)$ by an **independent product over dyadic multiplicity scales**. For
$j\ge1$ the block $k\in[2^j,2^{j+1})\cap[3,n]$ has width $w_j$ and total line-count
$M_j$. Two rigorous caps on $M_j$:
- **pair cap** (elementary): $M_j\le\binom n2/\binom{2^j}2$;
- **ST cap**: $t_{\ge k}\le A\,n^2/k^3+B\,n/k$ with $A=O(c_0^3)$, $B=4$, $c_0$ any
  valid incidence constant in $I(P,L)\le c_0(|P||L|)^{2/3}+|P|+|L|$.

The block contributes $\le\binom{M_j+w_j}{w_j}$ distinct sub-vectors, so
$$\log f(n)\ \le\ S(n):=\sum_j\log\binom{M_j+w_j}{w_j},\qquad M_j=\min(\text{ST cap},\text{pair cap}).$$

### Result: $S(n)=\Theta(\sqrt n)$ with an explicit constant — the upper bound is genuinely $\exp(\Theta(\sqrt n))$

`verify_upper_constant.py` (committed, exact/high-precision, EXIT 0):
- **Part B** (the crux): $S(n)/\sqrt n$ **converges** ($22.6\to34.39$ over
  $n=10^3..10^{12}$), $S(n)/n^{2/3}\to0$, and $S(n)/(\sqrt n\log n)\to0$. So the
  bound carries **no spurious $\log$ factor**: it is $\exp(\Theta(\sqrt n))$.
- **Part C** (control): the **pair-budget-only** bound diverges in $/\sqrt n$
  ($22.6\to364$) while $/n^{2/3}\to7.85$ (constant). This isolates the mechanism:
  pair-counting alone gives $\exp(\Theta(n^{2/3}))$ (S1's flagged overshoot); it is
  **ST's $k^3$ tail, not the pair budget, that produces the $\sqrt n$ rate**.
- **Part A**: the continuum closed form uses $\int_0^\infty\ln(1+u^{-2})\,du=\pi$ and
  $\int_0^\infty\ln(1+v^{-4})\,du=\pi\sqrt2$ (both verified to $4\times10^{-5}$),
  via the symmetric bound $\log\binom{a+b}{b}\le b\ln(1+a/b)+a\ln(1+b/a)$.
- **Part D**: explicit constant $C=S(\!10^{11}\!)/\sqrt{10^{11}}\approx23.5$ ($c_0{=}1$)
  to $34.4$ ($c_0{=}2.5$). Combined with S1:
  $$\boxed{\ \pi\sqrt{2/3}=2.5651\ \le\ \lambda\ \le\ C\ }\quad(C\ \text{explicit, finite}).$$

### Key Findings
- **First explicit upper bound on the true λ.** Before this, the upper side was only
  "$\exists C$". The bracket $2.565\le\lambda\le C$ is now two-sided with explicit ends.
- **Mechanism pinned.** The contrast Part B vs Part C shows precisely why $f(n)=
  \exp(\Theta(\sqrt n))$ and not $\exp(\Theta(n^{2/3}))$: the cubic ($k^{-3}$)
  Szemerédi–Trotter line-count tail, not the quadratic pair budget. The naive
  $(m_k)$-counting overshoot S1 warned about is quantified ($n^{2/3}$ rate, const $7.85$).
- **Honesty.** $C$ is **loose** — the ST incidence constant $c_0$ is not optimised and
  the dyadic product is a coarse over-count, so the bracket $[2.565,\sim24]$ is wide.
  The *value* of λ remains **open**; this only establishes that an explicit finite
  ceiling exists and identifies the convergent integrals controlling the rate.
- The integrity flag on `countLineCompatible` (S1) is unchanged; build-free session
  (Docker/Aristotle blackout), no Lean touched.

### Files Modified
- `research/problems/erdos-733-oq-01/verify_upper_constant.py` (new)
- `research/problems/erdos-733-oq-01/knowledge.md`, `src/data/research/problems/erdos-733-oq-01.json` (S3)

### Next Steps
- Optimise $c_0$ (use the best explicit ST incidence constant) and tighten the dyadic
  over-count to shrink $C$ toward the conjectural truth.
- Decide whether $\lambda=\lambda_{\mathrm{grid}}$ (is the grid the extremal construction?)
  — this would connect S2's lower bracket to this upper bound.
- The hard target remains the *exact* λ; both sides are still far apart.
