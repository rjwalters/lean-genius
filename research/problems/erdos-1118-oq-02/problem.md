# erdos-1118-oq-02

## Problem Statement

What are the higher-dimensional analogues of Erdős Problem #1118 for holomorphic
maps $f : \mathbb{C}^n \to \mathbb{C}^n$? Specifically, what is the right theory of
finite-measure superlevel sets
$$E(c) = \{\, z \in \mathbb{C}^n : \lVert f(z)\rVert > c \,\}, \qquad \lambda_{2n}(E(c)) < \infty,$$
where $\lambda_{2n}$ is Lebesgue measure on $\mathbb{C}^n \cong \mathbb{R}^{2n}$?

## Source

- **Parent proof**: erdos-1118 (Erdős Problem #1118: Entire Functions with Finite Measure Superlevel Sets)
- **Category**: generalization
- **Tractability**: challenging

## Tags

erdos, complex-analysis, several-complex-variables, entire-functions, measure-theory, growth-rate, solved

## Related Gallery Proofs

- erdos-1118

## Proposed Formulation (OBSERVE → ORIENT)

The parent one-variable theory has two parts (Camera 1977, Gol'dberg 1979):

- **Q1 (growth characterization).** A non-constant entire $f:\mathbb{C}\to\mathbb{C}$ has
  some $c$ with $\lvert E(c)\rvert<\infty$ iff $\int_0^\infty \frac{r}{\log\log M(r)}\,dr<\infty$,
  where $M(r)=\max_{|z|=r}\lvert f(z)\rvert$.
- **Q2 (threshold classification).** The threshold set
  $T(f)=\{c>0 : \lvert E(c)\rvert<\infty\}$ is always an upper set, but it need **not**
  extend down to $0$: Gol'dberg realized $T(f)\in\{\varnothing,\ (0,\infty),\ [m,\infty),\ (m,\infty)\}$.

The several-complex-variables analogue requires the following modelling choices. The
ones below are reasoned from the parent material; items flagged **(open)** are genuine
formulation gaps, not yet settled by the parent proof.

### 1. Objects: holomorphic maps and a non-degeneracy hypothesis

Take $f:\mathbb{C}^n\to\mathbb{C}^n$ holomorphic (each component $f_j$ entire in the SCV
sense). The one-variable hypothesis "non-constant" is **too weak** here: a holomorphic
map can be non-constant yet have positive-dimensional fibers (e.g.
$f(z_1,z_2)=(z_1,0)$), making every superlevel set a cylinder of infinite $2n$-measure
trivially. The right replacement is a **non-degeneracy / dominance** hypothesis — e.g.
$f$ generically finite (Jacobian $\det Df \not\equiv 0$), so $f$ is open and proper onto
its image off a thin set. **(open: the precise minimal hypothesis.)**

### 2. Superlevel set and norm-independence

$E(c)=\{z\in\mathbb{C}^n:\lVert f(z)\rVert>c\}$. Because all norms on the
finite-dimensional space $\mathbb{C}^n$ are equivalent, **finiteness of $\lambda_{2n}(E(c))$
is independent of the chosen norm** (a different norm only rescales the threshold $c$ by a
bounded factor). So the *qualitative* theory (which $f$ admit some finite-measure $E(c)$,
and the order-type of $T(f)$) is norm-free; only the *quantitative* growth constant can
depend on the norm. This is a clean, true reduction.

### 3. The growth invariant

$M(r)=\max_{\lVert z\rVert=r}\lVert f(z)\rVert$. Since each $\lvert f_j\rvert$ is
plurisubharmonic and $\max$/sums preserve plurisubharmonicity, $\log\lVert f\rVert$ is
plurisubharmonic; hence $M(r)$ is non-decreasing in $r$ and obeys a Hadamard
three-spheres convexity bound. This gives the reusable monotone growth profile the
one-variable proof relies on.

### 4. The growth-integral analogue (Q1 analogue)

In one variable the kernel $r\,dr$ is exactly the planar area element in polar
coordinates. In $2n$ real dimensions the radial volume element is
$r^{2n-1}\,dr$ (up to the surface area of $S^{2n-1}$). The **natural candidate** is
therefore
$$\int_0^\infty \frac{r^{2n-1}}{\log\log M(r)}\,dr < \infty,$$
replacing $r\,dr$ by $r^{2n-1}\,dr$. **(open)** Whether $\log\log M(r)$ is still the
correct denominator in SCV — i.e. whether the level sets thin out at the same
double-logarithmic rate — is **not** established by the parent material and is the central
analytic open question. The dimensional volume scaling is solid; the denominator is the
conjectural part.

### 5. Threshold classification (Q2 analogue)

$T(f)=\{c>0:\lambda_{2n}(E(c))<\infty\}$. The **order/measure facts transfer verbatim and
are dimension-free**: $c_1<c_2\Rightarrow E(c_2)\subseteq E(c_1)$, finite measure is
upward-monotone in $c$, and $T(f)$ is an upper set. These need only set inclusion and
monotonicity of measure — no analysis, no dimension. **(open)** Whether the
Gol'dberg pathologies (gaps in $T(f)$; the four order-types) persist for $n\ge 2$, or
whether higher dimension forces extra rigidity, is unresolved.

### Summary of the formulation split

| Component | Status in SCV |
|-----------|---------------|
| Superlevel nesting, finite-measure upward monotonicity, $T(f)$ upper-set | **Dimension-free; directly reusable** |
| Norm-independence of the finiteness question | **True (norm equivalence)** |
| $M(r)$ monotone via plurisubharmonicity of $\log\lVert f\rVert$ | **True; reusable growth profile** |
| Correct non-degeneracy hypothesis on $f$ | open |
| Growth-integral kernel $r^{2n-1}/\log\log M(r)$ | volume factor solid; denominator conjectural |
| Persistence of Gol'dberg threshold pathologies | open |

## Research Notes

The goal for this OQ is explicitly to settle a *truthful formulation* before any
formalization. The table above is the deliverable: it isolates what is genuinely new
(the analytic Q1 kernel and the Q2 pathology question) from what is mechanical
(the dimension-free order/measure scaffold). The parent file's
`superlevel_nested`, `finite_measure_monotone`, and `threshold_is_upper_set` are the
exact lemmas that lift to $\mathbb{C}^n$ unchanged and should anchor any future Lean
development.
