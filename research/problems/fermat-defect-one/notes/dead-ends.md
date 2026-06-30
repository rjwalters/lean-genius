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
    witnesses). NB: `parameterization` was named here as "the only
    unconditional-existence route" — that is now **also closed for $n \ge 3$**;
    see below. And `modular-obstruction` was named "the only rigorous-refutation
    route" — that is now **also closed for all $n$** (no prime, and no composite
    modulus, can obstruct); see below.

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

- **`modular-obstruction` (single prime $p$, Level-3 refutation)** — dead end
  for refuting Level 3 at *any* $(n, \epsilon)$, at *any* prime. See
  `claims/2026-06-17-modular-obstruction-n456-level3.md` (issue #22636).
  - *Exhaustive search.* All $(n, \epsilon, p)$ with $n \in \{4,5,6\}$,
    $\epsilon \in \{-1,+1\}$, $p \in \{3,5,7,11,13\}$ — every one of the 30
    cells admits a primitive residue solution mod $p$. No obstruction.
  - *Unconditional obstruction to the method.* Universal "unit" residue
    witnesses exist in *every* $\mathbb{Z}/p$ for all $n \ge 1$:
    $(a,b,c) = (0,0,1)$ for the negative sign ($0^n + 0^n + 1 = 1^n$) and
    $(1,0,0)$ for the positive sign ($1^n + 0^n = 0^n + 1$). The unit offset
    "$\pm 1$" is absorbed by $1 = 1^n$, so the congruence is trivially solvable
    mod any modulus; composite/CRT moduli inherit the same witnesses.
  - *Consequence.* Single-modulus congruence obstructions cannot exist for
    defect-one. Any genuine arithmetic obstruction (if Level 3 fails somewhere)
    must be global/archimedean (size-based), not local at a prime. Formalized
    in `proofs/Proofs/FermatDefectOne.lean`
    (`fermat_defect_no_obstruction_{neg,pos}` + 30 `decide`-checked instances,
    built clean: 0 sorry / 0 axiom / no new `native_decide`).

## Bounded-search results (not dead ends — lower bounds on M(n))

`witness-search` is *not* a dead end; it is the productive per-exponent vector.
Exhausted ranges are recorded here so they are not re-run:

- **n = 4, c ≤ 1000 — no witness (primitive or not).** Exhaustive integer
  search, two independent methods agreeing (hashed solve-for-$b$ over 498 501
  $(a,c)$ pairs + triple-loop cross-check). Gives $M(4) \ge 1001$ if finite.
  See `claims/2026-06-17-witness-search-n4-bound1000.md` (issue #22635) and
  `claims/scripts/witness_search_n4_bound1000.py`. No small modulus prunes the
  space (consistent with the `modular-obstruction` dead-end above); the absence
  is a global size fact, not a congruence. A future $n=4$ search should start at
  $c > 1000$ with a sieved enumeration.

(Seeded 2026-06-09 by issue #22628.)
