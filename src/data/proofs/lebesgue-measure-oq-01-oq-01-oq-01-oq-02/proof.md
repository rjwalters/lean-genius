# The Oscillation of Thomae's Function is Exactly 1/q

## The Question

Thomae's function (the "popcorn function")
$$
T(x) = \begin{cases} 1/q & x = p/q \text{ in lowest terms},\\ 0 & x \text{ irrational},\end{cases}
$$
is continuous at the irrationals and discontinuous at every rational. *How big*
is each discontinuity? The right gauge is the **oscillation**
$$
\omega_T(x) \;=\; \inf_{N \ni x \text{ nbhd}} \operatorname{diam} T(N),
$$
the eventual spread of values near $x$. The parent entry showed the discontinuity
set of $T$ is null (the measure side of **Lebesgue's criterion**); this entry
computes the oscillation *exactly* and shows its level sets are finite — the
finer, oscillation-theoretic form of the criterion.

We work with Mathlib's `oscillation f x = ⨅ S ∈ (𝓝 x).map f, EMetric.diam S`
(`Mathlib.Analysis.Oscillation`), valued in $[0,\infty]$.

## The Result

$$
\boxed{\;\omega_T(p/q) = \tfrac{1}{q} \quad\text{(}q\text{ the reduced denominator)},\qquad \omega_T(x) = 0 \text{ for } x \text{ irrational}.\;}
$$

## The Argument

### A key local bound (`exists_nbhd_thomae_le`)

Everything rests on one lemma: **if $T(a) \le v$ with $v > 0$, then $T \le v$ on a
whole ball around $a$.** The points where $T > v$ are exactly the rationals with
$1/\text{den} > v$, i.e. denominator $< 1/v$. For each denominator $d$ there are
finitely many such fractions near $a$ (`finite_rat_bounded`: the numerator is
pinned between $\lfloor(a-1)d\rfloor$ and $\lceil(a+1)d\rceil$), and **none of them
equals $a$** (they have value $> v \ge T(a)$). A finite set of points, all
distinct from $a$, lies a positive distance $\delta$ away (`pos_min_dist`); on
$\operatorname{ball}(a,\delta)$ the function stays $\le v$.

### Oscillation at a rational $r = p/q$ (`oscillation_thomae_rat`)

- **Upper bound $\le 1/q$.** Take $v = 1/q = T(r)$ in the key lemma: on a small
  ball $T \in [0, 1/q]$, so the image has diameter $\le 1/q$, and the oscillation
  — an infimum over neighborhoods — is $\le 1/q$ (`biInf_le` against the image of
  the ball, which lies in the mapped neighborhood filter via
  `Filter.image_mem_map`).
- **Lower bound $\ge 1/q$.** Any set $S$ in $(\mathcal N_r)_* T$ has $T^{-1}S$ a
  neighborhood of $r$, hence contains an open $U \ni r$. It holds $T(r) = 1/q \in S$,
  and — since the **irrationals are dense** (`dense_irrational`) — some irrational
  $y \in U$ gives $T(y) = 0 \in S$. So $\operatorname{diam} S \ge \operatorname{edist}(1/q, 0) = 1/q$
  (`EMetric.edist_le_diam_of_mem`). The infimum is therefore $\ge 1/q$.

### Oscillation at an irrational (`oscillation_thomae_irrational`)

The same key lemma with $v = \varepsilon$ (any $\varepsilon > 0$, legitimate since
$T(x) = 0 \le \varepsilon$) bounds the oscillation by $\operatorname{ofReal}\varepsilon$.
Letting $\varepsilon \to 0$ (`ENNReal.le_of_forall_pos_le_add`) gives
$\omega_T(x) = 0$, and `Oscillation.eq_zero_iff_continuousAt` returns continuity at
$x$ — the parent's continuity-at-irrationals, now read off the oscillation.

### Finite level sets (`oscillation_levelSet_finite`)

For $\varepsilon > 0$, a point of $[a,b]$ with $\omega_T \ge \varepsilon$ cannot be
irrational (oscillation $0$ there), so it is a rational $p/q$ with
$1/q = \omega_T(p/q) \ge \varepsilon$, i.e. $q \le 1/\varepsilon$. Bounded-denominator
rationals in a bounded interval are finite (`finite_rat_Icc`), so the level set is
finite. Consequently the discontinuity set is
$\bigcup_n \{x : \omega_T(x) \ge 1/n\}$, a **countable union of finite sets** — null,
which is precisely why $T$ is Riemann integrable.

## Why It Matters

The value $1/q$ ties the analytic oscillation to the **arithmetic of the reduced
denominator**: the discontinuity at $p/q$ is large exactly when $q$ is small, and
the finite level sets are the mechanism inside Lebesgue's criterion. Mathlib has no
Riemann/Darboux integral, so the fully general criterion remains open; here its
oscillation engine is realized concretely for the canonical example.

## Formalization Notes

- 316 lines, 13 theorems/lemmas, 1 definition, **0 axioms, 0 sorries** (only
  `propext`, `Classical.choice`, `Quot.sound`).
- The Thomae infrastructure (definition, value at rationals/irrationals,
  finiteness of bounded-denominator rationals) is reproved in-file so the entry
  builds independently of its siblings.
- One lemma, `exists_nbhd_thomae_le`, serves three masters: the rational upper
  bound, the irrational vanishing, and (through the latter) continuity at the
  irrationals.
