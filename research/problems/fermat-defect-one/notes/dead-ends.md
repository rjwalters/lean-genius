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
  - *Productive vectors instead*: `witness-search` (#22635, per-$n$ verified
    witnesses), `modular-obstruction` (#22636, the only rigorous-refutation
    route). NB: `parameterization` was named here as "the only
    unconditional-existence route" — that is now **also closed for $n \ge 3$**;
    see the next entry.

- **`parameterization` (polynomial families $a(t)^n + b(t)^n - c(t)^n \equiv
  \pm 1$)** — dead end for the headline existence conjecture at $n \ge 3$. See
  `claims/2026-06-17-parameterization-polynomial-families.md` (issue #22637).
  - *Exhaustive search.* ~59 M low-degree integer triples checked exactly
    ($n \in \{2,3,4,5\}$, degree $1$–$3$): **32 nonconstant families at $n = 2$**
    (Pythagorean, out of scope), **none at $n = 3, 4, 5$**.
  - *Unconditional obstruction.* The $t^{nd}$ leading coefficient of an
    equal-degree family is $\ell_a^n + \ell_b^n - \ell_c^n$; its vanishing is a
    nonzero integer solution of $x^n + y^n = z^n$, which **Fermat's Last
    Theorem** forbids for $n \ge 3$. The polynomial-FLT / **Mason–Stothers**
    theorem upgrades this to a complete impossibility at *any* degree and *any*
    coefficient size — there is no "larger degree / larger box" rescue. The
    inhomogeneous unit $\pm 1$ does not help.
  - *Consequence.* No single polynomial family can prove defect-one existence
    for $n \ge 3$. Combined with the `reduction` dead-end, the
    $\forall n \ge 3$ existence statement has **no known uniform-construction
    route**; `witness-search` settles one exponent at a time, and a genuinely
    new idea is needed for the universal statement.

(Seeded 2026-06-09 by issue #22628.)
