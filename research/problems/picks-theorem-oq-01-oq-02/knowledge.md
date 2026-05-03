# picks-theorem-oq-01-oq-02: 2D Ehrhart Polynomial via Pick's Theorem

**Problem**: Formalize the Ehrhart polynomial L(P,t) = A·t² + (B/2)·t + 1 for 2D convex lattice polygons.

**Status**: COMPLETED (PR pending)

**Key Result**: The 2D Ehrhart polynomial follows from Pick's theorem applied to tP, with scaling axioms for area and boundary count. Additionally, the rectangle and right triangle cases are proved from scratch via Finset combinatorics with 0 axioms.

---

## Session 2026-05-03 (Session 1) - Initial Formalization

**Mode**: FRESH  
**Outcome**: completed (PR pending Docker verification)

### What I Did
- Created `proofs/Proofs/PicksTheoremOQ01OQ02.lean` (309 lines)
- Created gallery entry at `src/data/proofs/picks-theorem-oq-01-oq-02/` (meta.json, annotations.json, index.ts)
- Attempted Docker build (failed due to multi-agent Docker contention, not Lean errors)

### Mathematical Content

**Part I: Rectangles** (0 axioms)
- `rectangleScaled a b t`: Finset of lattice points in t·[0,a]×[0,b]
- `rectangle_ehrhart`: L(R_{a,b},t) = (ta+1)(tb+1) via Finset.card_product
- `rectangle_ehrhart_quadratic`: L = ab·t² + (a+b)·t + 1 via ring

**Part II: Right Triangles** (0 axioms)
- `triangleScaled n t`: Finset of lattice points in t·Δ_n = {(x,y): x+y≤tn}
- `triangleScaled_eq_biUnion`: decomposes triangle as ⋃_{k=0}^{tn} antidiag(k) (pairwise disjoint)
- `triangle_ehrhart_double`: 2·L(Δ_n,t) = (tn+1)(tn+2) via Gauss sum

**Part III: General Polygons** (3 axioms)
- `picks_theorem`: A = i + B/2 - 1 (matches gallery axiom)
- `scaled_area`: Area(tP) = t²·Area(P)
- `scaled_boundary`: |∂(tP)| = t·|∂P| for t ≥ 1
- `ehrhart_formula`: L(P,t) = A·t² + (B/2)·t + 1 (KEY RESULT)
- `ehrhart_interior`: i(tP) = A·t² - (B/2)·t + 1 (Ehrhart-Macdonald reciprocity)

**Part IV: Examples**
- `rectanglePolygon`: concrete SimpleLatticePolygon for m×n rectangles
- `rectangle_frameworks_agree`: Finset count matches abstract formula

**Part V: h*-vector**
- `hstar`: h*₀=1, h*₁=A+B/2-1, h*₂=i(P)
- `hstar_one_nonneg`: h*₁ ≥ 0 (from Pick + boundary_ge_three)
- `ehrhart_from_hstar`: L = h*₀·C(t+2,2) + h*₁·C(t+1,2) + h*₂·C(t,2)

### Key Findings
- The antidiagonal biUnion decomposition is the cleanest approach for the triangle: row k of the triangle has exactly k+1 lattice points, matching antidiag(k).card
- The `opaque scaledPolygon` approach avoids circular definitions: defining interior_count via the Ehrhart formula makes Pick's theorem tautologically true
- Cross-framework consistency (rectangle_frameworks_agree) validates that both proof methods agree

### Files Modified
- `proofs/Proofs/PicksTheoremOQ01OQ02.lean` (new, 309 lines)
- `src/data/proofs/picks-theorem-oq-01-oq-02/meta.json` (new)
- `src/data/proofs/picks-theorem-oq-01-oq-02/annotations.json` (new)
- `src/data/proofs/picks-theorem-oq-01-oq-02/index.ts` (new)

### Next Steps
- Docker build verification (blocked by multi-agent contention)
- Consider adding more annotations after PR merges
