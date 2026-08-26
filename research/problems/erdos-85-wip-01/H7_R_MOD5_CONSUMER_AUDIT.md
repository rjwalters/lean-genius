# H7 `R mod 5` consumer audit

## Scope

The block-spectral decomposition gives

```text
R = 3 T_low + 1 (mod 5),
R = tr(A D^2),   D = K + J - A^2.
```

This note tests whether the fixed empty mask can make that congruence a
standalone exclusion mechanism.

## Logical dependence

The congruence is a Newton-integrality consequence of the exact factors

```text
charpoly(C) = x^6 (x^2 - 7x + 7) r(x),
charpoly(A) = (x^2 - 7)^6 (x^3 - 7x^2 - 7x + 42) r(x).
```

Those factors use only the fixed support matrix identities, symmetry of `C`,
and the canonical row degrees.  Consequently every integral `C` satisfying
those identities already satisfies the congruence, whether or not it is
C4-free.  Computing `R mod 5` again from the same identities cannot disagree
with it.  A contradiction needs an **independent** C4-sensitive restriction
on `R` or `T_low`; the empty mask by itself is not such a restriction.

## Bounded hard-mask probe

To check whether the pinned representative accidentally fixes either
residue, I built the exact Boolean relaxation for `F6/t2` (mask `1048903`):

- 861 symmetric low-edge variables;
- every low vertex has its canonical residual degree `7 - supportCard`;
- for every high label and low vertex, exactly one low neighbor carries that
  label (`BC = J`);
- all 21 pinned empty-sector edge units;
- no C4 clauses.

The relaxation has 19,635 variables and 39,571 sequential-counter clauses.
CaDiCaL immediately produced distinct models.  The first eight gave:

| model | `T_low` | `R` | `(T_low mod 5, R mod 5)` |
|---:|---:|---:|---:|
| 0 | 15 | -604 | `(0,1)` |
| 1 | 14 | -612 | `(4,3)` |
| 2 | 14 | -802 | `(4,3)` |
| 3 | 10 | -1564 | `(0,1)` |
| 4 | 9 | -1742 | `(4,3)` |
| 5 | 13 | -980 | `(3,0)` |
| 6 | 13 | -990 | `(3,0)` |
| 7 | 9 | -1752 | `(4,3)` |

Every model satisfies `R - 3 T_low - 1 = 0 (mod 5)`, as predicted, while
both quantities and their residues vary despite the fixed hard mask.  These
models are deliberately not C4-free (off-diagonal entries of algebraic `D`
range down to `-5`), so they do not refute a future C4-sensitive lemma.  They
do decisively show that support, degree, and mask data do not evaluate `R`
modulo five.

## Verdict

**CUT direct per-mask evaluation of the congruence.**  It is an invariant,
not an independent obstruction, and the hard mask realizes several allowed
residue pairs before C4 constraints enter.

The block decomposition remains valuable.  Its next consumer must constrain
`R` or `T_low` using genuinely new C4-sensitive combinatorics (for example a
classification of deficiency-overlap patterns), not recompute either term
from `BB^T`, `BC`, degrees, or the pinned empty mask alone.
