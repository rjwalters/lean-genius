# Thomae's Function and Lebesgue's Criterion for Riemann Integrability

## The Question

Thomae's function (the "popcorn function")
$$
T(x) = \begin{cases} 1/q & x = p/q \text{ in lowest terms},\\ 0 & x \text{ irrational},\end{cases}
$$
is the textbook example of a function that is **Riemann integrable despite being
discontinuous on a dense set** (every rational). *Why* is it Riemann integrable?
**Lebesgue's criterion**: a bounded function on $[a,b]$ is Riemann integrable if
and only if its set of discontinuities has Lebesgue measure zero.

The grandparent entry computed the Lebesgue integral of $T$ via $T =_{\text{a.e.}} 0$;
a later entry proved Riemann integrability but **deliberately routed around the
criterion** (Mathlib has no first-class `RiemannIntegrable` predicate). This entry
supplies the part that was skipped: the **measure-theoretic heart of Lebesgue's
criterion** — that the discontinuity set of $T$ is null.

## The Argument

### 1. $T$ is continuous at every irrational

Fix an irrational $x$ and $\varepsilon > 0$. Choose $N$ with $1/(N+1) < \varepsilon$.

- **Finitely many "bad" rationals nearby.** Only finitely many rationals with
  denominator $\le N$ lie in $[x-1, x+1]$ (`finite_rat_bounded`): for each
  denominator $d \le N$ the numerator is pinned between $\lfloor (x-1)d\rfloor$
  and $\lceil (x+1)d\rceil$.
- **They stay away from $x$.** Since $x$ is irrational, its distance to this
  finite set is some $\delta > 0$ (`pos_min_dist`).
- **Conclusion.** For $|y - x| < \min(\delta, 1)$: if $y$ is irrational then
  $T(y) = 0 < \varepsilon$; if $y = p/q$ then $q > N$ (else $y$ would be one of
  the bad rationals within $\delta$), so $T(y) = 1/q < 1/(N+1) < \varepsilon$.

Hence $|T(y) - T(x)| = |T(y)| < \varepsilon$, i.e. $T$ is continuous at $x$.

### 2. The discontinuity set is contained in the rationals

By the contrapositive: if $T$ is discontinuous at $x$, then $x$ is not irrational,
so $x \in \operatorname{range}(\mathbb{Q} \hookrightarrow \mathbb{R})$
(`thomae_discontinuitySet_subset`).

### 3. The rationals are Lebesgue-null

$\operatorname{range}(\mathbb{Q} \hookrightarrow \mathbb{R})$ is **countable**, and
Lebesgue measure has no atoms, so it is null (`rat_range_null`,
`Set.Countable.measure_zero`).

### 4. Lebesgue's criterion

Therefore the discontinuity set is null (`thomae_discontinuitySet_null`), which is
**exactly the hypothesis of Lebesgue's criterion**. Equivalently, $T$ is
**continuous almost everywhere** (`thomae_ae_continuousAt`). By Lebesgue's theorem
this is what makes $T$ Riemann integrable.

### 5. The value

$T$ vanishes a.e. (its nonzero set $\subseteq$ the null rationals), so it is
integrable with
$$\int_{\mathbb{R}} T = 0, \qquad \int_0^1 T = 0,$$
packaged with the criterion in `thomae_riemann_via_lebesgue_criterion`.

## A Note on "Riemann Integrable"

Mathlib's `intervalIntegral` *is* the Bochner/Lebesgue integral; there is no
separate `RiemannIntegrable` predicate, and no general Lebesgue-criterion lemma.
So "Riemann integrable" is not a Lean statement we can name directly. What we
*can* — and do — formalize is the criterion's content for $T$: the discontinuity
set is null and $T$ is continuous a.e. Classically these *are* the reason $T$ is
Riemann integrable, and the Lebesgue value $0$ matches the Riemann value.

## Self-Containment

The continuity-at-irrationals argument is reproved here rather than imported,
because the gallery file that carried it has **bit-rotted** against the current
Mathlib: `div_lt_iff` became `div_lt_iff₀`, `Set.Finite.ofFinset` now demands an
`iff` (so we use `Set.Finite.subset`), the denominator bound uses
`one_div_le_one_div_of_le`, and the `Finset.induction_on` `insert` case takes the
`@insert` binder form. The proof here compiles 0-sorry, 0-axiom against the
pinned toolchain.

## Historical Significance

Henri Lebesgue's 1902 criterion explained, once and for all, *which* bounded
functions are Riemann integrable — the discontinuities must be negligible in
measure. Thomae's function (1875) is the sharp example: discontinuous on a dense
set yet Riemann integrable, because that dense set (the rationals) has measure
zero. It marks the boundary where the Riemann integral runs out and the Lebesgue
integral takes over.
