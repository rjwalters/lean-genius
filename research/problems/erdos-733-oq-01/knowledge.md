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
