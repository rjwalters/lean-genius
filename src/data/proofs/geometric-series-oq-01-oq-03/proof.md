# Geometric Series at the Boundary: Abel Summability

## The Question

The parent entry studied the geometric series $\sum_{n=0}^{\infty} r^n$ at the
critical boundary $|r| = 1$. There ordinary convergence fails, but the **Cesàro
mean** of Grandi's series $1 - 1 + 1 - 1 + \cdots$ still converges to $\tfrac12$.

Cesàro is one way to extract a value from a divergent series. Is it the only one,
and does a *different* method give the same answer? This entry develops the third
regularization lens at the boundary: **Abel summability**.

## Abel Summability

A real sequence $(a_n)$ is **Abel summable to $L$** when the power series
$$A(x) = \sum_{n=0}^{\infty} a_n x^n$$
converges for every $x \in [0,1)$ and its value tends to $L$ as $x \to 1^-$:
$$\lim_{x \to 1^-} A(x) = L.$$
The Abel sum is unique, because the left-neighborhood filter $\mathcal{N}^{<}(1)$
is nontrivial — a function cannot tend to two different limits along it.

## Three Outcomes at the Boundary

### 1. Grandi's series is Abel summable to $\tfrac12$

For $|x| < 1$ the Abel function of $a_n = (-1)^n$ is a geometric series with
ratio $-x$:
$$\sum_{n=0}^{\infty} (-1)^n x^n = \sum_{n=0}^{\infty} (-x)^n = \frac{1}{1+x}.$$
As $x \to 1^-$ this tends to $\tfrac{1}{1+1} = \tfrac12$. So
$$1 - 1 + 1 - 1 + \cdots \ \xrightarrow{\text{Abel}}\ \tfrac12,$$
**recovering Euler's value and agreeing with the parent's Cesàro mean** — two
genuinely different methods, the same answer.

### 2. $r = 1$ is *not* Abel summable

For $a_n = 1$ the Abel function is the ordinary geometric series
$$\sum_{n=0}^{\infty} x^n = \frac{1}{1-x},$$
which **diverges to $+\infty$** as $x \to 1^-$ (here $1 - x \to 0^+$, so its
reciprocal blows up). Hence $r = 1$ has no Abel sum. Abel summability still
**separates** the genuinely divergent $r = 1$ from the regularizable $r = -1$,
sharpening the parent's blanket statement "$|r| \ge 1 \Rightarrow$ not summable."

### 3. Abel summability is regular

For $|r| < 1$ the Abel function of $a_n = r^n$ is
$$\sum_{n=0}^{\infty} r^n x^n = \sum_{n=0}^{\infty} (rx)^n = \frac{1}{1-rx}
\ \xrightarrow[x \to 1^-]{}\ \frac{1}{1-r},$$
which is exactly the **ordinary** sum $\sum_n r^n$. So whenever a series already
converges, its Abel sum equals its true sum: Abel summation *extends* ordinary
convergence and never contradicts it. This property is called **regularity**.

## Key Proof Techniques

- **Closed form on the disc**: each Abel function is a geometric series in an
  auxiliary variable, evaluated by Mathlib's `hasSum_geometric_of_abs_lt_one`
  after rewriting $(-1)^n x^n = (-x)^n$ and $r^n x^n = (rx)^n$.
- **Radial limits by continuity**: the limits $\tfrac{1}{1+x} \to \tfrac12$ and
  $\tfrac{1}{1-rx} \to \tfrac{1}{1-r}$ come from `Tendsto.inv₀` (inversion is
  continuous away from $0$) restricted to $\mathcal{N}^{<}(1)$ via
  `mono_left nhdsWithin_le_nhds`.
- **Divergence at $r = 1$**: the map $x \mapsto 1 - x$ sends
  $\mathcal{N}^{<}(1)$ to $\mathcal{N}^{>}(0)$, and `tendsto_inv_nhdsGT_zero`
  sends that to $+\infty$; `not_tendsto_nhds_of_tendsto_atTop` over the NeBot
  filter rules out any finite Abel sum.
- **Eventual closed form**: each Abel function equals its closed form only on
  $|x| < 1$, so the limit is transported by `Tendsto.congr'` along the
  eventual equality near $1^-$.

## Historical Significance

Niels Henrik Abel proved in 1826 that a convergent series $\sum a_n = L$ always
satisfies $\sum a_n x^n \to L$ as $x \to 1^-$ — *Abel's continuity theorem*. The
converse is taken as a *definition* of summability for divergent series. Abel's
method, like Cesàro's, is **regular** and assigns $\tfrac12$ to Grandi's series;
Frobenius later showed Abel summation strictly dominates Cesàro. These regular
methods are the rigorous core behind Euler's bold $1 - 1 + 1 - \cdots = \tfrac12$,
and the same machinery underlies modern regularization in analysis and physics.
