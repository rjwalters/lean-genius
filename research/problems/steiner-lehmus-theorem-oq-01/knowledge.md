# steiner-lehmus-theorem-oq-01

**Statement.** If a triangle has two internal angle bisectors of equal length, then it is
isosceles: equal bisectors from `B` and `C` force `b = c`.

**Status:** COMPLETED (build-verified, 0 sorries, 0 axioms).

## Summary

The Steiner–Lehmus theorem reduces, via the classical internal-bisector-length formula, to a
pure real-algebra implication over positive reals `a, b, c`. Using

    w_b² = a·c·(1 - (b/(a+c))²),    w_c² = a·b·(1 - (c/(a+b))²),

the theorem becomes: `w_b² = w_c² ⟹ b = c` for `a, b, c > 0`. The decisive identity is the
exact factorisation (sympy-verified, then `ring`-checked in Lean):

    w_b² - w_c²
      = -a·(b - c)·(a + b + c)·(a³ + a²b + a²c + 3abc + b²c + bc²) / ((a+b)²(a+c)²).

The cofactor `a·(a+b+c)·(a³ + a²b + a²c + 3abc + b²c + bc²)` is a sum of positive monomials,
hence strictly positive for positive `a, b, c`. So `w_b² = w_c²` forces `b - c = 0`.
No triangle inequality is needed — positivity of the three side lengths suffices.

## Session 2026-06-16 (Session 1) — FRESH

**Mode:** FRESH
**Outcome:** completed

### What I Did
- Claimed a stale dead-pid lock (prior claimant crashed; no PR/Lean file produced).
- Verified the bisector-difference factorisation in sympy: the cofactor is a sum of positive
  monomials, giving the equality-case-free positivity needed for the implication.
- Formalised `SteinerLehmusTheoremOQ01.lean`:
  - `bisectorSq a b c = a*c*(1 - (b/(a+c))^2)` (noncomputable, real division).
  - `bisectorSq_clear`: denominator-cleared form, `field_simp; ring`.
  - `steiner_lehmus`: main theorem via two exact `linear_combination` steps
    (cleared polynomial equation, then `(b-c)·cofactor = 0`) and `positivity`.
- Registered the import in `proofs/Proofs.lean`; build-verified by module name in docker.

### Key Findings
- The whole theorem is denominator-clearing + one polynomial factorisation + positivity.
- `linear_combination` coefficients derived by hand and confirmed in sympy:
  `hcleared = -(a+b)²·hB + (a+c)²·hC + key`; `hfact = -1·hcleared`.
- Treating `bisectorSq …` as a `ring` atom lets the cleared-equation combination go through
  without unfolding inside the main proof.

### Files Modified
- `proofs/Proofs/SteinerLehmusTheoremOQ01.lean` (new)
- `proofs/Proofs.lean` (import registration)

### Next Steps
- Enricher: add gallery `meta.json` + annotations.
- Possible follow-up OQ: the converse / the equal-length comparison `w_b ⋛ w_c ⟺ b ⋛ c`
  (monotonicity of bisector length in the opposite side), which the same factorisation gives
  directly from the sign of `b - c`.
