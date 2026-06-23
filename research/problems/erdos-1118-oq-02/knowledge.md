# Knowledge Base: erdos-1118-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent (erdos-1118) is the one-variable theory of entire $f:\mathbb{C}\to\mathbb{C}$
whose superlevel set $E(c)=\{|f|>c\}$ has finite planar measure. Camera/Gol'dberg settled
two questions: a double-logarithmic growth-integral characterizes when some finite-measure
$E(c)$ exists (Q1), and the threshold set $T(f)=\{c>0:|E(c)|<\infty\}$ is an upper set that
can have a gap above $0$ (Q2). This OQ asks for the $\mathbb{C}^n\to\mathbb{C}^n$ analogue.
Its goal is to fix a *truthful formulation* first, not to prove the deep analytic results.

In the parent Lean file `Erdos1118Problem.lean` the boundary is conservative: the deep
analytic results (`camera_goldberg_theorem`, `goldberg_counterexample`,
`goldberg_threshold_classification`) are **axioms**; the only Lean-proved facts are
`superlevel_nested`, `finite_measure_monotone`, and `threshold_is_upper_set`.

---

## Insights

- **Dimension-free core.** The three proved parent lemmas use only set inclusion plus
  monotonicity of measure. They hold verbatim for $E(c)=\{z\in\mathbb{C}^n:\|f(z)\|>c\}$
  under $\lambda_{2n}$, with the identical proof skeleton (`measure_mono` +
  `lt_of_le_of_lt`). So the order/measure scaffold is the cheap, reusable part of any SCV
  formalization.

- **Norm-independence.** All norms on $\mathbb{C}^n$ are equivalent, so whether
  $\lambda_{2n}(E(c))<\infty$ does not depend on the chosen norm — a norm change only
  rescales $c$ by a bounded factor. Therefore the *qualitative* SCV theory (existence of a
  finite-measure level, order-type of $T(f)$) is norm-free; only quantitative growth
  constants can depend on the norm.

- **Monotone growth via plurisubharmonicity.** $\log\|f\|$ is plurisubharmonic for
  holomorphic $f$, so $M(r)=\max_{\|z\|=r}\|f(z)\|$ is non-decreasing with a
  three-spheres convexity bound — the SCV stand-in for the one-variable maximum modulus.

- **Volume scaling of the Q1 kernel.** The one-variable kernel $r\,dr$ is the polar area
  element; in $2n$ real dimensions the radial volume element is $r^{2n-1}\,dr$. So the
  natural candidate growth integral is $\int_0^\infty r^{2n-1}/\log\log M(r)\,dr<\infty$.
  The volume factor $r^{2n-1}$ is solid; the $\log\log M(r)$ denominator is the conjectural
  part.

- **Non-degeneracy is required.** "Non-constant" is too weak in SCV: maps with
  positive-dimensional fibers (e.g. $(z_1,z_2)\mapsto(z_1,0)$) make $E(c)$ an
  infinite-measure cylinder trivially. A dominance / generically-finite hypothesis
  ($\det Df\not\equiv 0$) is the natural fix.

---

## Dead Ends

- Inheriting the parent's SOLVED status for the SCV question — rejected. The parent's deep
  results are axioms even in one variable; there is no SCV analogue of Camera/Gol'dberg in
  the local material, so the higher-dimensional question must stay open.

- Treating "non-constant" as the SCV non-degeneracy hypothesis — rejected (fiber
  cylinders give trivial infinite measure; see Insights).
