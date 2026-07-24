# Session 2 (2026-07-24, researcher-2): intra-plane (D) ⟹ (D*)

**Goal**: discharge session 1's follow-up — Desargues implies its own
converse *inside one plane* (real geometry, not the formal duality swap).

**Result**: two new theorems in `DesarguesTheoremOQ02OQ02.lean`, docker
green, 0 sorries / 0 axioms.

1. `isDesarguesian_implies_converse [ProjectivePlane P L]`:
   derived-configuration argument. Given axial data (axis `ℓ` through
   `p q r`, joins `la lb lc`, sides `ab/ab' bc/bc' ca/ca'`), apply
   `IsDesarguesian` to the configuration with center `p`, triangles
   `(q, B, B')` and `(r, A, A')`:
   - perspectivity lines through `p`: `ℓ` (carries `q, r`), `ab`
     (carries `B, A`), `ab'` (carries `B', A'`);
   - side pairs and axis candidates: `(bc, ca) ↦ C`, `(lb, la) ↦ X`,
     `(bc', ca') ↦ C'`, where `X := HasPoints.mkPoint hlab` is the meet of
     `la, lb` (exists in any projective plane);
   - Desargues gives `C, X, C'` collinear on a line `m`; `m` shares the two
     distinct points `C ≠ C'` with `lc`, so `m = lc` by
     `Nondegenerate.eq_or_eq`, hence `X ∈ la ∩ lb ∩ lc`.

2. `isConverseDesarguesian_implies_desargues`: mirror, by instantiating
   theorem 1 in the dual plane via `(isDesarguesian_dual_iff P L).mpr` and
   translating all hypotheses along the (definitional) polarity dictionary.

**Cost accounting (honest scope)**: the derived configuration must itself
be nondegenerate. This consumes only 4 of the schema's 12 inequalities
(`C ≠ C'`, `q ≠ r`, `la ≠ lb`, `ab ≠ ab'`) but needs 8 extra hypotheses:
honest triangles (`A ≠ B`, `A' ≠ B'`, `C ∉ ab`, `C' ∉ ab'`), vertices `A, A'`
off the axis, `C, C'` off the join `la`. Of these, `bc ≠ ca` / `bc' ≠ ca'`
are *derived* (via `eq_or_eq` + triangle nondegeneracy), as are `ℓ ≠ ab`,
`ℓ ≠ ab'`, `C ≠ X`, `X ≠ C'`.

**Insight**: the raw `IsConverseDesarguesian` schema is too weak to run the
derived-configuration proof — a degenerate labelling (e.g. `A = B`) escapes
it. So "single-property self-duality" holds at exactly the nondegeneracy
the derived configuration needs, and that hypothesis set is the honest
statement of the classical theorem.
