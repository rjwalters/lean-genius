# General Quartic — Research Knowledge

## Session 1 (2026-03-26, researcher-7)

**Mode**: AXIOM HUNT
**Prior**: 9 axioms, 6 theorems, 344 lines
**After**: 6 axioms, 9 theorems, 360 lines

### Axioms Eliminated (3)

1. **`depressed_quartic_forward`** — Pure polynomial ring identity. The substitution y = x + a/4
   transforms x⁴ + ax³ + bx² + cx + d into y⁴ + py² + qy + r. Proved via `linear_combination h`:
   the expanded depression is identically equal to the original quartic.

2. **`depressed_quartic_backward`** — Converse of above, same ring identity in reverse direction.
   Also proved via `linear_combination h`.

3. **`resolvent_cubic_has_root`** — By the Fundamental Theorem of Algebra (ℂ is algebraically closed),
   any polynomial of degree ≥ 1 has a root. The resolvent cubic has leading coefficient 8 ≠ 0,
   hence degree 3 ≥ 1. Proved via `IsAlgClosed.exists_root` + coefficient analysis showing
   coeff 3 = 8 via `Polynomial.coeff_*` simp lemmas.

### Remaining Axioms (6) — Analysis

| Axiom | Difficulty | Notes |
|-------|-----------|-------|
| `ferrari_factorization_forward` | Hard | Requires showing quartic = product of two factors given resolvent condition. Non-trivial algebra with auxiliary hypotheses. |
| `ferrari_factorization_backward` | Hard | Same factorization, reverse direction. Note: the file's resolvent cubic may use non-standard parameterization. |
| `quartic_has_four_roots` | Medium | FTA gives ≤ 4 roots for degree 4. Exact factorization into 4 linear factors needs `Polynomial.roots` multiset API. |
| `biquadratic_forward` | Medium | Involves `Complex.cpow` (square root). Need (cpow z (1/2))² = z. |
| `biquadratic_backward` | Medium | Quadratic formula verification through `Complex.cpow`. |
| `ferrari_roots_verify` | Hard | Substitution of explicit radical formulas back into quartic. Heavy `Complex.cpow` manipulation. |

### Insight: Resolvent Cubic Parameterization

The file's resolvent cubic `8m³ + 20pm² + (16p²-8r)m + (4p³-4pr-q²) = 0` is the SHIFTED
version of the standard resolvent. Substituting `t = m + p/2` into the standard form
`8t³ + 8pt² + 2p²t - 8rt - q² = 0` gives exactly the file's form.

This means:
- The file uses `m` where standard references use `m - p/2`
- The factorization conditions (α² = 2m + p, β = q/(2α)) should be verified against this shifted form
- There may be an inconsistency between the resolvent definition and the factorization axioms
  (standard factorization with shifted resolvent needs α² = 2m, not α² = 2m + p)

### Next Steps

- Investigate whether Ferrari factorization axioms are mathematically consistent with the resolvent cubic definition
- If consistent: prove `ferrari_factorization_backward` via product = quartic identity
- If inconsistent: fix the resolvent cubic definition (change to standard form)
- Consider proving `biquadratic_backward` via `Complex.cpow` properties
