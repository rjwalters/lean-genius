# Symmetric fractional exterior extension: exact finite witnesses

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: the linear symmetric cross-block relaxation is feasible at `q=12`
and at binary `q=16`. No uniform extension theorem or ambient graph is
claimed. The exterior Gram diagonal fails in both witnesses.

## Precisely what is realized

Take the actual C-shore construction in
`NONBIP_MIXED_SIZE_TWO_TRIPLE_COMPANION_AUDIT.md`. On `C=Z/(2q)` use

```text
H: differences ±1;
D: odd differences except ±1, together with q;
L: all nonzero differences outside D and {±2}.
```

Let `F=E(L)` and let `B` be its unsigned vertex-edge incidence matrix.
Write `n=q-2`. The exact rational matrices `T` recorded here satisfy

```text
T = Tᵀ,              diag(T)=0,           0 <= T_ef <= 1,
T 1 = n 1,           HB+BT=J,
H²+BBᵀ=(q-1)I+J-D.                                    (1)
```

Thus local column matching feasibility is not the only surviving
relaxation: symmetry can also be imposed if entries are allowed to be
fractional. The binary example means that a proposed contradiction using
only (1) and this carrier cannot exclude every binary parameter. It says
nothing about feasibility at every binary parameter or at large parameters.

## Exact witness representation and independent verification

`size_two_symmetric_fractional_witnesses.json` records the nonzero
dihedral orbits of unordered pairs of selector edges, together with their
rational values. Translation and reflection act on C and hence on F.
There are 54 nonzero orbits at q=12 and 104 at q=16; unspecified entries
are zero. Symmetric reversal of an edge pair is included in expansion.

`check_size_two_symmetric_fractional.py` uses only Python's standard
library and `Fraction`. It reconstructs all selector edges independently,
expands each orbit under all translations/reflections, checks overlap
consistency, and verifies every matrix entry of (1). In particular it does
not trust a solver status or check only representative equations.

```sh
python3 research/problems/erdos-85-wip-01/check_size_two_symmetric_fractional.py
```

The two cases check respectively 2,880 and 7,168 entries of the cross
block, in addition to symmetry, diagonal, bounds, row sums, and the full
C-shore Gram equation.

Discovery used a bounded linear program. The unreduced q=12 attempt hit
its 45-second limit without a conclusion. A dihedral reduction then gave
100 equations/132 variables at q=12 and 196/359 at q=16. The q=12 floating
solution reconstructed directly to rationals. Direct rational rounding
failed at q=16; instead its selected support was solved by exact rational
Gaussian elimination. Only the resulting exact, independently checked
witness is evidence. The checked artifact needs neither SciPy nor SymPy.

## The exact missing quadratic condition

For a symmetric matrix with entries in `[0,1]` and row sums `n`,

```text
n-(T²)_ee = sum_f T_ef(1-T_ef) >= 0.                    (2)
```

Since each selector has two endpoints, `(BᵀB)_ee=2`. The required
exterior Gram equation would be

```text
BᵀB+T²=(q-1)I+J-D_F,
```

where `D_F` has zero diagonal. Its diagonal is therefore `2+(T²)_ee=q`,
or `(T²)_ee=n`. By (2), this is equivalent to every entry in row e being
zero or one. Requiring this in every row forces integrality of T.

The verifier computes (2) exactly and confirms a strictly positive deficit
in every row of both witnesses. They therefore explicitly violate the
exterior Gram diagonal; they are not approximate ambient graphs.

## Disposition

Do not pursue a universal exclusion from symmetry and the linear cross
block alone: its `[0,1]` relaxation has an exact binary witness. The
remaining candidate must retain integrality (equivalently the exterior
Gram diagonal within this relaxation), additional defect-intertwiner
constraints, or the off-diagonal exterior Gram/C4 conditions. Existence of
a symmetric zero-one extension is still open for this family; this audit
does not answer it or close A-REG-NONBIP.
