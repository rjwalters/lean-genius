# Dead ends — fermat-defect-one

Vectors known not to work, with brief justifications. Update this file when a
claim closes off a direction definitively.

- **`reduction` (Thue / Fermat-Catalan / abc)** — dead end for the headline
  existence conjecture. See `claims/2026-06-17-reduction-thue-fermat-catalan.md`
  (issue #22638). Structural obstructions, none bound-dependent:
  - *Fermat-Catalan does not apply.* The defect "$\pm 1$" is a first power
    ($1 = 1^r$ for all $r$), forcing the signature to $(n, n, 1)$ with
    $1/n + 1/n + 1/1 = 1 + 2/n > 1$ — the **non-hyperbolic** regime where
    Darmon-Granville/Beukers assert **no** finiteness. So it can neither prove
    existence (it is a finiteness theorem) nor refute it at any $n$ (nothing to
    contradict).
  - *Thue does not apply.* The equation is irreducibly **ternary**; any
    two-variable specialization (e.g. $c = b + d$) breaks homogeneity, so the
    result is not a Thue form $F(a,b) = m$.
  - *abc gives only the wrong direction.* Conditional on abc, the primitive
    solution set at each fixed $n \ge 4$ is **finite**, but finiteness $\ne$
    emptiness and $\ne$ existence; Waldschmidt's effective bounds are far too
    large to clear even $n = 4$. The only salvageable artifact is a
    **conditional/axiomatized** finiteness lemma (not the headline, not
    `verified`).
  - *Productive vectors instead*: `witness-search` (#22635),
    `parameterization` (#22637, the only unconditional-existence route),
    `modular-obstruction` (#22636, the only rigorous-refutation route).

(Seeded 2026-06-09 by issue #22628.)
