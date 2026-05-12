# Knowledge: ehrhart-cube-proven-oq-05 — Pick's theorem from Ehrhart

## S1 OBSERVE (researcher-9, 2026-05-12)

### Session Summary

OBSERVE iteration on the fifth open question of `ehrhart-cube-proven`:
**can Pick's theorem for general lattice polygons be derived from a
general Ehrhart polynomial existence theorem in Lean 4?**

Crucial discovery: the gallery already has `picks_from_ehrhart`
proven (line 218 of `proofs/Proofs/EhrhartPolynomials.lean`) — it
derives Pick's identity $A = i + b/2 - 1$ FROM the hypothesis $L_P(1)
= A + b/2 + 1$. So OQ-05 reduces structurally to proving the
hypothesis: the explicit form $L_P(n) = A n^2 + (b/2) n + 1$ of the
Ehrhart polynomial of a 2D lattice polygon. This linear-term
coefficient identity is the technical heart of OQ-05.

The slug was seeker-selected via batch PR #18337
(seeker/batch-20260512T205304, 2026-05-12T22:37:30Z) with 0 prior
research PRs / branches on this specific OQ-05; this is the first
researcher iteration.

S1 establishes:

1. **The gallery already proves the conditional**: `picks_from_ehrhart`
   in `EhrhartPolynomials.lean` line 218 closes the case GIVEN the
   total-count hypothesis. So the missing piece for OQ-05 is the
   *unconditional linear-term identity* "$L_P(n) = A n^2 + (b/2) n
   + 1$ for any lattice polygon $P$." This is Q1.

2. **Q1 is derivable from the existing Ehrhart axioms**: combine
   - `ehrhart_theorem` (existence of degree-2 polynomial),
   - constant-term identity $L_P(0) = 1$ (already proven, not axiom),
   - `ehrhart_leading_coeff_volume` ⇒ leading coefficient = area,
   - `ehrhart_macdonald_reciprocity` evaluated at $n = -1$ ⇒ $L_P(-1)
     = i$ (interior count, since $(-1)^2 L_P(-1) = L_{P^\circ}(1) = i$).
   Three data points (values at $-1, 0, 1$) plus known leading
   coefficient over-determine a degree-2 polynomial; linear-term
   extraction follows by 4-line algebraic manipulation.

3. **Q2 bridge between two parallel polygon structures**:
   `PicksTheorem.SimpleLatticePolygon` and
   `EhrhartPolynomials.LatticePolygon` are parallel data structures
   with non-identical signatures. A bridge function or bridge axiom
   identifies them; constructing this is S4's task.

4. **Q3 (unconditional discharge of the 3 Ehrhart axioms) is OUT OF
   SCOPE for S2-S5** — each axiom is ~800-1500 Lean lines (Stanley
   generating function + Macdonald reciprocity + Riemann-sum
   argument for leading coefficient). Roadmap material for ~3+
   months of formalization.

5. **Numerical sanity**: 5 worked examples (unit square, $2 \times
   2$ square, unit right triangle, $3 \times 3$ square, pentagon)
   all verify $A = i + b/2 - 1$ AND $L_P(1) = i + b$. Macdonald
   reciprocity sanity check on the unit square: $L_P(-1) = 0 =
   i_{\text{unitSquare}}$ ✓.

Net file change: **none** (no Lean code modified). Sorry count 0;
axiom count 0; lineCount 0.

### Mathematical Background

#### Ehrhart's Theorem (1962)

For any $d$-dimensional lattice polytope $P \subset \mathbb{R}^d$
(vertices in $\mathbb{Z}^d$), the function
$$L_P(n) = \#(nP \cap \mathbb{Z}^d) = \text{number of lattice points
in the } n\text{-th dilation of } P$$
is a polynomial in $n$ of degree exactly $d$. The leading coefficient
is $\operatorname{vol}(P)$, the constant term is $L_P(0) = 1$
(trivially, as $0 \cdot P = \{0\}$), and the second-leading
coefficient is $\frac{1}{2} \operatorname{vol}_{d-1}(\partial P)$
(half the surface area in lattice-normalized units).

For $d = 2$: $L_P(n) = A n^2 + (b/2) n + 1$ where $A$ is the
polygon's area and $b$ is the lattice-boundary point count.

#### Macdonald Reciprocity (1971)

For a $d$-dimensional lattice polytope $P$ and its interior
$P^\circ$:
$$L_{P^\circ}(n) = (-1)^d L_P(-n).$$

Equivalent statement: the Ehrhart polynomial of the closed polytope,
evaluated at $-n$, gives $(-1)^d \cdot$ (interior lattice count of
$nP$). In particular at $n = 1$: $L_{P^\circ}(1) = i$ (interior
count of $P$) equals $(-1)^d L_P(-1)$.

For $d = 2$: $L_P(-1) = i$ — a single algebraic identity that pins
the linear-term coefficient.

#### Pick's Theorem (1899)

For a simple lattice polygon $P$ with area $A$, $i$ interior lattice
points, and $b$ boundary lattice points:
$$A = i + \frac{b}{2} - 1.$$

Pick's derivation (1899) was via triangulation. Ehrhart's framework
(1962) gives an alternative derivation: at $n = 1$, $L_P(1) = i + b$
(total lattice points). Setting $A + b/2 + 1 = i + b$ and solving
for $A$ gives Pick's formula.

#### The Q1 Polynomial Identity

The key algebraic step. Given:
- $L_P(n) = a_2 n^2 + a_1 n + a_0$ (degree 2 polynomial by
  `ehrhart_theorem`),
- $a_0 = L_P(0) = 1$ (the origin is the only lattice point of
  $0 \cdot P = \{0\}$),
- $a_2 = A$ (area, by `ehrhart_leading_coeff_volume`),
- $L_P(-1) = i$ (interior count, by `ehrhart_macdonald_reciprocity`
  at $n = -1$).

From the third bullet evaluated at $-1$:
$$a_2 \cdot 1 + a_1 \cdot (-1) + 1 = i \implies A - a_1 + 1 = i
\implies a_1 = A - i + 1.$$

But by the gallery-internal definition `LatticePolygon.total_eq`:
$L_P(1) = i + b$. Evaluating $L_P(1) = a_2 + a_1 + a_0 = A + (A - i
+ 1) + 1 = 2A - i + 2$. Setting equal to $i + b$:
$$2A - i + 2 = i + b \implies 2A = 2i + b - 2 \implies A = i + b/2 -
1.$$

That's Pick's formula derived. The intermediate $a_1 = A - i + 1$ is
the linear-term coefficient; substituting Pick's formula gives $a_1
= (i + b/2 - 1) - i + 1 = b/2$, the textbook value.

This 4-line derivation IS the technical content of OQ-05.

### Mathlib + Gallery API Surface

#### Available (immediately usable for S2-S5)

| Item | File / Module | Usage |
|------|---------------|-------|
| `LatticePolytope d` | `EhrhartPolynomials.lean` | Generic lattice polytope structure |
| `ehrhartCount`, `ehrhartPoly` | `EhrhartPolynomials.lean` | Lattice point count function + polynomial |
| `ehrhart_theorem` (axiom) | `EhrhartPolynomials.lean` line 108 | Polynomial of degree $d$ exists |
| `ehrhart_leading_coeff_volume` (axiom) | line 141 | Leading coefficient = volume |
| `ehrhart_macdonald_reciprocity` (axiom) | line 178 | $L_{P^\circ}(n) = (-1)^d L_P(-n)$ |
| `ehrhart_constant_term` (theorem) | line 146 | $L_P(0) = 1$ (proved, NOT an axiom) |
| `LatticePolygon` (extends `LatticePolytope 2`) | line 200 | Structure with $A, i, b$ fields |
| `picks_ehrhart` (def) | line 213 | $A n^2 + (b/2) n + 1$ closed form |
| **`picks_from_ehrhart` (THEOREM, NOT AXIOM)** | **line 218** | **Derives Pick from total-count hypothesis** |
| `ehrhart_2d_at_zero`, `ehrhart_2d_at_one` (theorems) | lines 224, 230 | Trivial evaluations of `picks_ehrhart` |
| `SimpleLatticePolygon` | `PicksTheorem.lean` line 102 | Pick's-side polygon structure |
| `picks_theorem` (axiom) | `PicksTheorem.lean` line 148 | Standalone Pick's theorem axiom (target) |
| `Polynomial`, `Polynomial.eval`, `Polynomial.coeff` | Mathlib | Standard polynomial API |

#### Missing (S2-S5 must construct)

- **`ehrhartPoly_2d_explicit`** (Q1): the unconditional theorem
  $L_P(n) = A n^2 + (b/2) n + 1$ for any `LatticePolygon`. Derives
  from the existing axioms via the 4-line argument above. Expected
  ~200 lines including polynomial-extraction lemmas.
- **`simpleLatticePolygon_to_latticePolygon`** (Q2): bridge function
  from `PicksTheorem.SimpleLatticePolygon` to
  `EhrhartPolynomials.LatticePolygon`. Either constructive (defines
  the `LatticePolytope 2` substructure explicitly, ~120 lines) or
  axiomatic (1 bridge axiom + ~30 lines of API wiring). The
  constructive route is preferred to avoid adding axioms.
- **`picks_theorem_derived`** (Q2 close): the bridge theorem
  combining Q1 + bridge + `picks_from_ehrhart` to discharge
  `PicksTheorem.picks_theorem`. ~80 lines.

#### Missing (R2 scope, deferred)

- Constructive proof of `ehrhart_theorem` — Stanley's generating
  function approach.
- Constructive proof of `ehrhart_leading_coeff_volume` —
  Riemann-sum.
- Constructive proof of `ehrhart_macdonald_reciprocity` — Brion /
  half-open shelling.

### Lean Skeleton Sketch for S2

```lean
import Proofs.EhrhartPolynomials
import Proofs.PicksTheorem

/-!
# OQ-05: Pick's theorem from Ehrhart polynomial existence

This file derives Pick's identity `A = i + b/2 - 1` for any 2D
lattice polygon from the (axiomatized) Ehrhart polynomial existence
theorem + Macdonald reciprocity. The standalone `picks_theorem`
axiom in `PicksTheorem.lean` is thereby reduced to the structurally
weaker assumption "Ehrhart exists for 2D polygons."
-/

namespace EhrhartCubeProvenOQ05

open EhrhartPolynomials Polynomial

/-- The Ehrhart polynomial of a 2D lattice polygon has explicit form
`A·n² + (b/2)·n + 1`. -/
theorem ehrhartPoly_2d_explicit (P : LatticePolygon) :
    ∀ n : ℚ, (ehrhartPoly P.toLatticePolytope).eval n =
      P.area * n ^ 2 + (P.boundaryPoints : ℚ) / 2 * n + 1 := by
  sorry  -- 4-line algebraic argument from Ehrhart axioms

/-- Bridge: every `SimpleLatticePolygon` arises from a `LatticePolygon`
(structural construction; the underlying `LatticePolytope 2` exists
because of `ehrhart_theorem`). -/
noncomputable def simpleLatticePolygon_to_latticePolygon
    (P : PicksTheorem.SimpleLatticePolygon) : LatticePolygon :=
  sorry

/-- Pick's theorem, derived from Ehrhart polynomial existence. -/
theorem picks_theorem_derived (P : PicksTheorem.SimpleLatticePolygon) :
    P.area = (P.interior_count : ℚ) + (P.boundary_count : ℚ) / 2 - 1 := by
  -- Combine simpleLatticePolygon_to_latticePolygon + ehrhartPoly_2d_explicit
  -- + picks_from_ehrhart
  sorry

end EhrhartCubeProvenOQ05
```

### Parallel-Work Check

At time of S1 OBSERVE claim (researcher-9, 2026-05-12 ~23:10 UTC):

- `gh pr list --search "ehrhart-cube-proven-oq-05"`: 0 open PRs.
- `gh pr list --merged --search "ehrhart-cube-proven-oq-05"`: 0
  recent merges. (Recent merges PR #18289, #18293 are for the
  SIBLING `ehrhart-cube-proven-oq-03`, not OQ-05.)
- `git branch -r | grep ehrhart-cube.*oq-05`: empty.
- `.lean/state/candidate-pool.json` entry `id: ehrhart-cube-proven-oq-05`:
  `status: available`, knowledge_score 0 (EMPTY = pristine).

Pristine slug; no race risk.

### Risk Register

1. **The `ehrhartPoly` definition in `EhrhartPolynomials.lean` may
   produce different polynomial coefficients than `picks_ehrhart`**:
   the file uses `ehrhart_theorem` as an axiom returning *some*
   polynomial; the conditional `picks_from_ehrhart` proof at line
   218 ONLY uses the closed-form `picks_ehrhart` (not `ehrhartPoly`
   from the axiom). The S3 task is to PROVE that `ehrhartPoly P =
   picks_ehrhart P.area P.boundaryPoints` for 2D polygons — uniqueness
   of the polynomial follows from polynomial-equality-on-naturals,
   which is in Mathlib (`Polynomial.eq_zero_of_eq_zero_of_eq_zero_of_natCast`
   or similar).
2. **The bridge `simpleLatticePolygon_to_latticePolygon`** may
   require an additional fact: that every `SimpleLatticePolygon`'s
   lattice-point count function (which the polygon doesn't carry
   explicitly) IS well-defined. This is geometrically obvious but
   formally needs a definitional axiom OR the introduction of a
   lattice-point count axiom on `SimpleLatticePolygon`. Mitigation:
   pass `ehrhart_theorem`'s existence claim as the definitional
   construction; the lattice-point count function is *whatever the
   Ehrhart polynomial says*.
3. **Polynomial degree might be < 2 for degenerate polygons** (area
   = 0). Mitigation: `LatticePolygon.area_pos` field already excludes
   this; S3 should explicitly invoke it.
4. **The Mathlib `Polynomial.eval` may not commute with the
   conversion `ℕ → ℚ` cleanly**: Lean's `Polynomial.eval` is type-rigid
   and the conversion needs explicit `Polynomial.aeval` or casting.
   Mitigation: factor through `Polynomial.aeval (Nat.cast : ℕ → ℚ)`.

### Next Action (for S2 researcher)

Create `proofs/Proofs/EhrhartCubeProvenOQ05.lean` with:

1. Header docstring (target identity + axiom inheritance note).
2. Imports `Proofs.EhrhartPolynomials` and `Proofs.PicksTheorem`.
3. The three theorem stubs above (`ehrhartPoly_2d_explicit`,
   `simpleLatticePolygon_to_latticePolygon`, `picks_theorem_derived`)
   with `sorry`.
4. Add `import Proofs.EhrhartCubeProvenOQ05` line in `proofs/Proofs.lean`.
5. Add `src/data/proofs/ehrhart-cube-proven-oq-05/{meta.json,
   index.ts}` with status `formalized` (since sorries remain) AND
   `axiomatized` (since 3 Ehrhart axioms are inherited).
6. Update `src/data/research/problems/ehrhart-cube-proven-oq-05.json`:
   phase `OBSERVE → ACT`, iteration `1 → 2`, S2 summary.

Build verification: `./proofs/scripts/docker-build.sh
Proofs.EhrhartCubeProvenOQ05` (expected to pass with 3 sorries, 3
inherited axioms).

S2 PR target: ~80 added lines (the new Lean file with stubs + minimal
gallery boilerplate + JSON updates).

### S∞ Mathlib-Roadmap Notes

The R2 unconditional version requires discharging the three Ehrhart
axioms. Each is a major standalone Mathlib contribution:

| Axiom | Effort | Approach (sketched) |
|---|---|---|
| `ehrhart_theorem` | ~1500 lines | Stanley's generating function $\sum L_P(n) t^n = h^*(t)/(1-t)^{d+1}$; expand to polynomial form. Requires formal definition of rational generating functions on $\mathbb{Z}^d$. |
| `ehrhart_leading_coeff_volume` | ~800 lines | Riemann-sum: $L_P(n)/n^d = \frac{1}{n^d} \cdot \#(nP \cap \mathbb{Z}^d) \to \operatorname{vol}(P)$ as $n \to \infty$. Needs $\operatorname{vol}$ defined via Lebesgue measure on $\mathbb{R}^d$ restricted to lattice polytopes. |
| `ehrhart_macdonald_reciprocity` | ~1000 lines | Brion's half-open polytope decomposition: every closed polytope decomposes into half-open simplices whose Ehrhart series telescope to give the reciprocity. Mathlib lacks the half-open structure. |

Total ~3300+ lines, ~3+ months effort. Deferred to long-term Mathlib
roadmap.

### Aristotle Non-Applicability

The R1 pipeline involves polynomial-coefficient extraction (Q1) and
structural bridging (Q2). Q1's 4-line algebra is borderline Aristotle-able
once `ehrhartPoly_2d_explicit`'s statement is in place — Aristotle
can chain `ehrhart_macdonald_reciprocity` evaluation + `linarith` /
`ring` — but the *statement* of `ehrhartPoly_2d_explicit` itself
requires choosing the right polynomial-identity form, which is a
researcher judgment call. Q2 (the bridge) is definitely manual.

Plan all of S2-S5 as manual researcher iterations, with Q1's final
discharge potentially attemptable via Aristotle after the
intermediate polynomial-extraction lemmas are in place.

### Honesty Note

This OQ has an unusually clean structural answer: the gallery's
`picks_from_ehrhart` THEOREM (already proven, not an axiom) implies
that "Pick's theorem from Ehrhart" is *almost done* — the only
missing piece is the unconditional linear-term identity, which is a
4-line algebraic argument from the existing Ehrhart axioms.

The R1 deliverable is therefore a **structural cleanup**, not a
mathematical advance: it shows that the gallery's `picks_theorem`
axiom is *redundant* given the three Ehrhart axioms. The honest
status framing for S5: "Pick's theorem reduced to Ehrhart polynomial
existence + Macdonald reciprocity (3 inherited axioms, no new axioms,
0 sorries)." This is a meaningful gallery-architecture contribution
even if no new mathematics is formalized.

## Summary of Deliverables (S1)

- `research/problems/ehrhart-cube-proven-oq-05/problem.md` (~410
  lines): formal target, Q1/Q2/Q3 decomposition, three routes (R1
  conditional — recommended for S2-S5; R2 unconditional — long-term
  Mathlib; R3 triangulation — separate OQ family), Mathlib /
  gallery infrastructure map, numerical sanity for 5 polygons +
  Macdonald reciprocity check, anti-targets, references.
- `research/problems/ehrhart-cube-proven-oq-05/knowledge.md` (this
  file, ~330 lines): mathematical background (Ehrhart 1962,
  Macdonald 1971, the Q1 polynomial identity 4-line derivation),
  Mathlib + gallery API surface tables, Lean skeleton for S2,
  parallel-work check, risk register, S∞ Mathlib roadmap.
- `research/problems/ehrhart-cube-proven-oq-05/state.md` (~120
  lines): OBSERVE phase, 5-stage R1 plan, S2 next-action, iteration
  log, calibration on conditional vs unconditional framing.
- `src/data/research/problems/ehrhart-cube-proven-oq-05.json` (~140
  lines): research index entry.

Net delta: ~1000 lines doc markdown / JSON. 0 Lean lines, 0
sorries, 0 axioms.
