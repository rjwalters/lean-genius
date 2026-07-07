/-
# Puiseux's Theorem — OQ-03: a combinatorial Newton polygon

This file is the first Lean deliverable for the open question

  *"Can the Newton–Puiseux algorithm be made efficient enough for computational
  algebraic geometry at scale?"*

extracted from the gallery entry `puiseux-theorem` (Wiedijk #41 family).  Two
earlier doc-only OBSERVE sessions surveyed the literature
(Chudnovsky–Chudnovsky 1986, Duval 1989, Walsh 2000, Poteaux–Rybowicz 2008–15,
Poteaux–Weimann 2017–21) and the Mathlib v4.26.0 state, and identified the
**combinatorial Newton polygon** as the cleanest tractable entry point
(their "S2-A").  This file delivers it.

## What the Newton polygon is

For a polynomial `P(Y) = Σ aᵢ Yⁱ` with coefficients `aᵢ` in a valued field
`K((x))`, the Newton polygon is the lower convex hull of the *support points*

    (i, v(aᵢ))   for the indices i with aᵢ ≠ 0,

where `v(aᵢ) ∈ ℚ` is the valuation (the order of `aᵢ` as a Laurent/Puiseux
series).  The crucial fact — the Newton polygon theorem — is that the negatives
of the edge slopes are exactly the valuations of the roots of `P` in any
algebraically closed valued extension, which is why the slopes feed the
parent's `leadingExponentFromSlope`.

## What this file proves (all machine-checked, 0 sorries, 0 axioms)

We avoid committing to any particular hull-construction *algorithm* and instead
use the standard **supporting-line** characterization of a lower-hull vertex:
a support point `p` is a lower vertex when some line lies weakly below every
support point and passes through `p`.  This is a `Prop`, so the API is honest
about the combinatorial content without needing a verified convex-hull routine.

* `IsLowerVertex` — the supporting-line predicate.
* `isLowerVertex_of_minimal` — the minimum-valuation point is always a lower
  vertex (horizontal supporting line).  This is the seed of the polygon.
* `exists_lowerVertex` — every nonempty support set has a lower vertex
  (via `List.argmin`).
* `IsLowerVertex.mem` — lower vertices are genuine support points.
* The worked example `Y² − x`: both `(0,1)` and `(2,0)` are lower vertices, the
  single edge has slope `-1/2`, and the resulting leading exponent `1/2`
  matches the parent's `leadingExponentFromSlope 1 2`.

## What remains (honest scope)

* **Newton polygon theorem** (slopes = root valuations): needs a valuation API
  on `K((x))[Y]` not yet in Mathlib v4.26.0 — the harder half of S2-A.
* **Termination measure** for one Newton–Puiseux reduction step (S2-B).
* **Quasi-linear complexity bound** (Poteaux–Weimann `Õ(d·δ)`): the moonshot
  S2-C, blocked on the absence of an arithmetic-complexity model in Mathlib.

See `research/problems/puiseux-theorem-oq-03/` for the session notes.

## References

* I. Newton, *Method of Fluxions* (1676) — the fractional-exponent procedure.
* V. Puiseux, *Recherches sur les fonctions algébriques* (1850).
* R. Walker, *Algebraic Curves* (1950), Ch. IV.
* A. Poteaux, M. Weimann, *Computing Puiseux series: a fast divide and conquer
  algorithm*, Ann. Henri Lebesgue 4 (2021), 1061–1102.
-/
import Proofs.PuiseuxTheorem
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.RingTheory.HahnSeries.Valuation

namespace PuiseuxTheoremOQ03

/-- A **support point** `(i, v)` of a polynomial `P(Y) = Σ aᵢ Yⁱ` over a valued
field: the exponent `i` of `Y` paired with the valuation `v = v(aᵢ) ∈ ℚ` of the
coefficient.  Indices with `aᵢ = 0` (valuation `+∞`) are simply omitted from the
support list. -/
abbrev SupportPoint := ℕ × ℚ

/-- The slope of the segment joining two support points. -/
def edgeSlope (p q : SupportPoint) : ℚ := (q.2 - p.2) / ((q.1 : ℚ) - (p.1 : ℚ))

/-- `p` is a **lower vertex** of the Newton polygon of `pts` when some
(non-vertical) line `y = m·i + b` lies weakly below every support point of `pts`
and passes through `p`.  This is the supporting-line characterization of a
vertex of the lower convex hull; phrasing it as a predicate keeps the API
independent of any particular hull-construction algorithm. -/
def IsLowerVertex (pts : List SupportPoint) (p : SupportPoint) : Prop :=
  p ∈ pts ∧ ∃ m b : ℚ, p.2 = m * (p.1 : ℚ) + b ∧ ∀ q ∈ pts, m * (q.1 : ℚ) + b ≤ q.2

/-- A lower vertex is a genuine support point. -/
theorem IsLowerVertex.mem {pts : List SupportPoint} {p : SupportPoint}
    (h : IsLowerVertex pts p) : p ∈ pts := h.1

/-- **The minimum-valuation point is always a lower vertex.**  A horizontal
supporting line `y = v(p)` lies weakly below every support point and passes
through `p`.  This is the seed of the Newton polygon: the lowest point is always
a vertex. -/
theorem isLowerVertex_of_minimal {pts : List SupportPoint} {p : SupportPoint}
    (hp : p ∈ pts) (hmin : ∀ q ∈ pts, p.2 ≤ q.2) : IsLowerVertex pts p := by
  refine ⟨hp, 0, p.2, by ring, fun q hq => ?_⟩
  simpa using hmin q hq

/-- **Every nonempty support set has a lower vertex.**  Take the point of
minimum valuation via `List.argmin`. -/
theorem exists_lowerVertex {pts : List SupportPoint} (h : pts ≠ []) :
    ∃ p, IsLowerVertex pts p := by
  rcases hm : pts.argmin (·.2) with _ | m
  · exact absurd (List.argmin_eq_none.mp hm) h
  · exact ⟨m, isLowerVertex_of_minimal (List.argmin_mem hm)
      (fun q hq => List.le_of_mem_argmin hq hm)⟩

/-! ### Worked example: `Y² − x`

Over `K((x))`, the polynomial `Y² − x` has coefficients `a₀ = −x` (valuation
`1`), `a₁ = 0` (omitted), and `a₂ = 1` (valuation `0`).  Its support is therefore
`{(0, 1), (2, 0)}`, the Newton polygon is the single edge from `(0,1)` to
`(2,0)` of slope `-1/2`, and the root is `x^{1/2}`. -/

/-- Support points of `Y² − x`: `(0, 1)` from the constant term `−x` and
`(2, 0)` from the leading term `1`. -/
def YsqMinusX : List SupportPoint := [(0, 1), (2, 0)]

/-- The constant-term support point `(0,1)` is a lower vertex of `Y² − x`,
witnessed by the edge line `y = -½ i + 1`. -/
theorem ysqMinusX_vertex_const : IsLowerVertex YsqMinusX (0, 1) := by
  refine ⟨by simp [YsqMinusX], -1/2, 1, by norm_num, fun q hq => ?_⟩
  fin_cases hq <;> norm_num

/-- The leading-term support point `(2,0)` is a lower vertex of `Y² − x`,
witnessed by the same edge line `y = -½ i + 1`. -/
theorem ysqMinusX_vertex_lead : IsLowerVertex YsqMinusX (2, 0) := by
  refine ⟨by simp [YsqMinusX], -1/2, 1, by norm_num, fun q hq => ?_⟩
  fin_cases hq <;> norm_num

/-- The single Newton-polygon edge of `Y² − x` has slope `-1/2`. -/
theorem ysqMinusX_edge_slope : edgeSlope (0, 1) (2, 0) = -1/2 := by
  norm_num [edgeSlope]

/-- **The Newton polygon recovers the leading exponent of the root.**  The
negative of the edge slope `-1/2` equals the parent's
`leadingExponentFromSlope 1 2 = 1/2`, the leading exponent of the root
`x^{1/2}` of `Y² − x`. -/
theorem ysqMinusX_leading_exponent :
    -edgeSlope (0, 1) (2, 0)
      = PuiseuxTheorem.leadingExponentFromSlope 1 2 (by norm_num) := by
  norm_num [edgeSlope, PuiseuxTheorem.leadingExponentFromSlope]

/-! ### Edges and convexity of the lower hull

The vertex API above identifies the *corners* of the Newton polygon.  Its edges
carry the arithmetic: the negative of an edge slope is the valuation of a root.
We now give the edge predicate and prove the polygon is **convex** — adjacent
edge slopes are non-decreasing — which is the combinatorial reason a
polynomial's root valuations form a sorted list. -/

/-- The slope of a supporting line through two support points of **distinct**
index is forced to equal their `edgeSlope`.  (A non-vertical line is determined
by any two of its points.) -/
theorem slope_eq_edgeSlope {p q : SupportPoint} {m b : ℚ}
    (hp : p.2 = m * (p.1 : ℚ) + b) (hq : q.2 = m * (q.1 : ℚ) + b)
    (hne : p.1 ≠ q.1) : m = edgeSlope p q := by
  have hd : (q.1 : ℚ) - (p.1 : ℚ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hne (Nat.cast_injective h).symm
  have hnum : q.2 - p.2 = m * ((q.1 : ℚ) - (p.1 : ℚ)) := by rw [hp, hq]; ring
  rw [edgeSlope, hnum, mul_div_assoc, div_self hd, mul_one]

/-- `(p, q)` is a **lower edge** of the Newton polygon of `pts`: `p` lies
strictly left of `q`, and a single supporting line passes through both `p` and
`q` while lying weakly below every support point.  By `slope_eq_edgeSlope` that
line necessarily has slope `edgeSlope p q`. -/
def IsLowerEdge (pts : List SupportPoint) (p q : SupportPoint) : Prop :=
  p ∈ pts ∧ q ∈ pts ∧ p.1 < q.1 ∧
    ∃ m b : ℚ, p.2 = m * (p.1 : ℚ) + b ∧ q.2 = m * (q.1 : ℚ) + b ∧
      ∀ r ∈ pts, m * (r.1 : ℚ) + b ≤ r.2

/-- The left endpoint of a lower edge is a lower vertex. -/
theorem IsLowerEdge.isLowerVertex_left {pts : List SupportPoint}
    {p q : SupportPoint} (h : IsLowerEdge pts p q) : IsLowerVertex pts p := by
  obtain ⟨hp, _, _, m, b, hp1, _, hsup⟩ := h
  exact ⟨hp, m, b, hp1, hsup⟩

/-- The right endpoint of a lower edge is a lower vertex. -/
theorem IsLowerEdge.isLowerVertex_right {pts : List SupportPoint}
    {p q : SupportPoint} (h : IsLowerEdge pts p q) : IsLowerVertex pts q := by
  obtain ⟨_, hq, _, m, b, _, hq1, hsup⟩ := h
  exact ⟨hq, m, b, hq1, hsup⟩

/-- **Convexity of the Newton polygon.**  Two lower edges sharing the middle
vertex `q` have non-decreasing slope: the left edge `p → q` is no steeper than
the right edge `q → r`.

The proof is the textbook one-line convexity argument.  The left edge's
supporting line `ℓ₁` lies weakly below `r`, while the right edge's line `ℓ₂`
passes through `r`; both lines meet at `q`.  Subtracting the two relations at the
points `q` and `r` gives `(slope ℓ₁ − slope ℓ₂)·(r.1 − q.1) ≤ 0`, and
`r.1 > q.1` forces `slope ℓ₁ ≤ slope ℓ₂`. -/
theorem edgeSlope_mono {pts : List SupportPoint} {p q r : SupportPoint}
    (hpq : IsLowerEdge pts p q) (hqr : IsLowerEdge pts q r) :
    edgeSlope p q ≤ edgeSlope q r := by
  obtain ⟨_, _, hpq_lt, m₁, b₁, hp1, hq1, hsup1⟩ := hpq
  obtain ⟨_, hr_mem, hqr_lt, m₂, b₂, hq2, hr2, _⟩ := hqr
  have e1 : m₁ = edgeSlope p q := slope_eq_edgeSlope hp1 hq1 (ne_of_lt hpq_lt)
  have e2 : m₂ = edgeSlope q r := slope_eq_edgeSlope hq2 hr2 (ne_of_lt hqr_lt)
  rw [← e1, ← e2]
  -- ℓ₁ supports r; ℓ₂ passes through r
  have hbelow : m₁ * (r.1 : ℚ) + b₁ ≤ m₂ * (r.1 : ℚ) + b₂ := by
    have h := hsup1 r hr_mem; rwa [hr2] at h
  -- both lines meet at q
  have hq_eq : m₁ * (q.1 : ℚ) + b₁ = m₂ * (q.1 : ℚ) + b₂ := by rw [← hq1, ← hq2]
  have hgt : (q.1 : ℚ) < (r.1 : ℚ) := by exact_mod_cast hqr_lt
  nlinarith [hbelow, hq_eq, hgt]

/-- The **root valuations are sorted**: since valuations are the negatives of
edge slopes, convexity (`edgeSlope_mono`) says the valuation read off the left
edge is at least the one read off the right edge. -/
theorem rootValuation_antitone {pts : List SupportPoint} {p q r : SupportPoint}
    (hpq : IsLowerEdge pts p q) (hqr : IsLowerEdge pts q r) :
    -edgeSlope q r ≤ -edgeSlope p q :=
  neg_le_neg (edgeSlope_mono hpq hqr)

/-- The single segment of `Y² − x` is a genuine lower edge. -/
theorem ysqMinusX_isLowerEdge : IsLowerEdge YsqMinusX (0, 1) (2, 0) := by
  refine ⟨by simp [YsqMinusX], by simp [YsqMinusX], by norm_num,
    -1/2, 1, by norm_num, by norm_num, fun r hr => ?_⟩
  fin_cases hr <;> norm_num

/-! ### Supporting-slope bounds and convexity from below

`edgeSlope_mono` above states convexity between two *edges sharing a vertex*.
The lemmas here give the complementary, finer statement directly from a single
supporting line: the supporting slope `m` through a vertex `p` bounds the slope
to **every** other support point — `m` is a lower bound to the right and an upper
bound to the left.  This yields the sharper convexity certificate
`interior_slopes`: **no** support point — vertex or not — ever dips below a lower
edge.  These are stated on the raw supporting-line data, so they apply to any
vertex/edge regardless of whether the intermediate points happen to be vertices
of further edges. -/

/-- **Supporting-slope lower bound (rightward).**  If a line of slope `m` passes
through `p` and lies weakly below every support point, then every support point
`q` strictly to the right of `p` has `m ≤ edgeSlope p q`.  So the supporting
slope is the *smallest* slope leaving `p` — the dominant edge of the lower hull. -/
theorem edgeSlope_ge_of_supportingLine {pts : List SupportPoint} {p q : SupportPoint}
    {m b : ℚ} (hpe : p.2 = m * (p.1 : ℚ) + b) (hq : q ∈ pts)
    (hsupp : ∀ r ∈ pts, m * (r.1 : ℚ) + b ≤ r.2)
    (hlt : (p.1 : ℚ) < q.1) : m ≤ edgeSlope p q := by
  have hpos : (0 : ℚ) < (q.1 : ℚ) - p.1 := by linarith
  have hq2 : m * (q.1 : ℚ) + b ≤ q.2 := hsupp q hq
  rw [edgeSlope, le_div_iff₀ hpos]
  have hexp : m * ((q.1 : ℚ) - p.1) = m * (q.1 : ℚ) - m * (p.1 : ℚ) := by ring
  rw [hexp]; linarith [hpe, hq2]

/-- **Supporting-slope upper bound (leftward).**  Symmetrically, every support
point `q` strictly to the left of `p` has `edgeSlope q p ≤ m`. -/
theorem edgeSlope_le_of_supportingLine {pts : List SupportPoint} {p q : SupportPoint}
    {m b : ℚ} (hpe : p.2 = m * (p.1 : ℚ) + b) (hq : q ∈ pts)
    (hsupp : ∀ r ∈ pts, m * (r.1 : ℚ) + b ≤ r.2)
    (hlt : (q.1 : ℚ) < p.1) : edgeSlope q p ≤ m := by
  have hpos : (0 : ℚ) < (p.1 : ℚ) - q.1 := by linarith
  have hq2 : m * (q.1 : ℚ) + b ≤ q.2 := hsupp q hq
  rw [edgeSlope, div_le_iff₀ hpos]
  have hexp : m * ((p.1 : ℚ) - q.1) = m * (p.1 : ℚ) - m * (q.1 : ℚ) := by ring
  rw [hexp]; linarith [hpe, hq2]

/-- **A lower edge is convex from below.**  For *any* support point `r` strictly
between the endpoints `p` and `q` of a lower edge, the right sub-slope is at most
the left sub-slope: `edgeSlope r q ≤ edgeSlope p r`.  Equivalently, `r` lies on
or above the edge line — the polygon never dips below an edge.  Unlike
`edgeSlope_mono`, `r` need not be a vertex of any edge; this is the full
lower-hull convexity certificate. -/
theorem IsLowerEdge.interior_slopes {pts : List SupportPoint} {p q r : SupportPoint}
    (h : IsLowerEdge pts p q) (hr : r ∈ pts)
    (hpr : (p.1 : ℚ) < r.1) (hrq : (r.1 : ℚ) < q.1) :
    edgeSlope r q ≤ edgeSlope p r := by
  obtain ⟨_, _, _, m, b, hpe, hqe, hsupp⟩ := h
  have h1 : m ≤ edgeSlope p r := edgeSlope_ge_of_supportingLine hpe hr hsupp hpr
  have h2 : edgeSlope r q ≤ m := edgeSlope_le_of_supportingLine hqe hr hsupp hrq
  linarith

/-! ### Well-definedness of edge slopes (uniqueness)

Every result above is about *existence* (`exists_lowerVertex`,
`exists_isLowerEdge_of_leftmost`, `exists_lowerHull`) or *ordering*
(`edgeSlope_mono`, `edgeSlopes_pairwise_le`).  None pins down that the polygon's
data is *unique*.  The two theorems here close that gap directly from the
supporting-slope bounds: through a fixed vertex the slope of a lower edge is
forced, even though the opposite endpoint may not be — several support points can
be collinear on one edge, so the *endpoint* is ambiguous while the *slope* (and
hence the root valuation read off it) is not.  This is the well-definedness
counterpart to the existence theorems and the reason the edge-slope list
`edgeSlopes` of a hull is a genuine invariant of the support set. -/

/-- **Uniqueness of the leaving edge-slope.**  If both `(p, q)` and `(p, q')` are
lower edges sharing the left endpoint `p`, they have equal slope.  The right
endpoint itself can differ when support points are collinear on the edge, but the
slope is determined: each edge's supporting line, being weakly below all points,
gives the *least* slope leaving `p`, so the two slopes bound each other. -/
theorem IsLowerEdge.leaving_slope_unique {pts : List SupportPoint}
    {p q q' : SupportPoint} (h : IsLowerEdge pts p q) (h' : IsLowerEdge pts p q') :
    edgeSlope p q = edgeSlope p q' := by
  obtain ⟨_, hq, hpq, m, b, hpe, hqe, hsup⟩ := h
  obtain ⟨_, hq', hpq', m', b', hpe', hqe', hsup'⟩ := h'
  have e1 : m = edgeSlope p q := slope_eq_edgeSlope hpe hqe (ne_of_lt hpq)
  have e2 : m' = edgeSlope p q' := slope_eq_edgeSlope hpe' hqe' (ne_of_lt hpq')
  have hlt : (p.1 : ℚ) < q'.1 := by exact_mod_cast hpq'
  have hlt' : (p.1 : ℚ) < q.1 := by exact_mod_cast hpq
  have h1 : m ≤ edgeSlope p q' := edgeSlope_ge_of_supportingLine hpe hq' hsup hlt
  have h2 : m' ≤ edgeSlope p q := edgeSlope_ge_of_supportingLine hpe' hq hsup' hlt'
  rw [← e2] at h1
  rw [← e1] at h2
  rw [← e1, ← e2]
  linarith

/-- **Uniqueness of the arriving edge-slope.**  Symmetrically, if `(p, q)` and
`(p', q)` are lower edges sharing the right endpoint `q`, they have equal slope;
each line gives the *greatest* slope arriving at `q`. -/
theorem IsLowerEdge.arriving_slope_unique {pts : List SupportPoint}
    {p p' q : SupportPoint} (h : IsLowerEdge pts p q) (h' : IsLowerEdge pts p' q) :
    edgeSlope p q = edgeSlope p' q := by
  obtain ⟨hp, _, hpq, m, b, hpe, hqe, hsup⟩ := h
  obtain ⟨hp', _, hpq', m', b', hpe', hqe', hsup'⟩ := h'
  have e1 : m = edgeSlope p q := slope_eq_edgeSlope hpe hqe (ne_of_lt hpq)
  have e2 : m' = edgeSlope p' q := slope_eq_edgeSlope hpe' hqe' (ne_of_lt hpq')
  have hlt : (p'.1 : ℚ) < q.1 := by exact_mod_cast hpq'
  have hlt' : (p.1 : ℚ) < q.1 := by exact_mod_cast hpq
  have h1 : edgeSlope p' q ≤ m := edgeSlope_le_of_supportingLine hqe hp' hsup hlt
  have h2 : edgeSlope p q ≤ m' := edgeSlope_le_of_supportingLine hqe' hp hsup' hlt'
  rw [← e2] at h1
  rw [← e1] at h2
  rw [← e1, ← e2]
  linarith

/-- The **root valuation** (`= −edgeSlope`) read off any lower edge leaving a
fixed vertex `p` is therefore unique — the Newton–Puiseux algorithm reads a
well-defined valuation at each vertex regardless of how collinear support points
are resolved. -/
theorem IsLowerEdge.leaving_rootValuation_unique {pts : List SupportPoint}
    {p q q' : SupportPoint} (h : IsLowerEdge pts p q) (h' : IsLowerEdge pts p q') :
    -edgeSlope p q = -edgeSlope p q' :=
  congrArg Neg.neg (h.leaving_slope_unique h')

/-! ### Endpoints of the Newton polygon

`exists_lowerVertex` produces *a* vertex — the point of minimum *valuation*.  The
two theorems here pin down the polygon's horizontal extent: the minimum-*index*
and maximum-*index* support points are always lower vertices.  Concretely, the
polygon's lower hull stretches across the whole `Y`-degree range `[iₘᵢₙ, iₘₐₓ]`,
which is the combinatorial reason the edge widths sum to the degree and hence
every root (counted with ramification) is accounted for.

Unlike `isLowerVertex_of_minimal`, the supporting line here is *not* horizontal:
through the leftmost point we take the least of the edge slopes leaving it (via
`List.argmin`), and through the rightmost point the greatest of the edge slopes
arriving at it (via `List.argmax`). -/

/-- **The minimum-index support point is a lower vertex** (the left endpoint of
the Newton polygon).  If every other support point lies strictly to the right of
`p`, the supporting line of least edge-slope leaving `p` lies weakly below all of
them. -/
theorem isLowerVertex_of_leftmost {pts : List SupportPoint} {p : SupportPoint}
    (hp : p ∈ pts) (hleft : ∀ q ∈ pts, q ≠ p → p.1 < q.1) :
    IsLowerVertex pts p := by
  classical
  rcases hR : (pts.filter (fun q => decide (q ≠ p))).argmin (edgeSlope p) with _ | q₀
  · -- the filtered list is empty: every support point equals `p`
    have hempty : pts.filter (fun q => decide (q ≠ p)) = [] := List.argmin_eq_none.mp hR
    refine ⟨hp, 0, p.2, by ring, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · have hmem : q ∈ pts.filter (fun q => decide (q ≠ p)) :=
        List.mem_filter.mpr ⟨hq, by simpa using hqp⟩
      rw [hempty] at hmem; simp at hmem
  · refine ⟨hp, edgeSlope p q₀, p.2 - edgeSlope p q₀ * (p.1 : ℚ), by ring, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; linarith
    · have hmem : q ∈ pts.filter (fun q => decide (q ≠ p)) :=
        List.mem_filter.mpr ⟨hq, by simpa using hqp⟩
      have hle : edgeSlope p q₀ ≤ edgeSlope p q := List.le_of_mem_argmin hmem hR
      have hlt : (p.1 : ℚ) < (q.1 : ℚ) := by exact_mod_cast hleft q hq hqp
      have hpos : (0 : ℚ) < (q.1 : ℚ) - (p.1 : ℚ) := by linarith
      have key : edgeSlope p q₀ * ((q.1 : ℚ) - (p.1 : ℚ)) ≤ q.2 - p.2 :=
        (le_div_iff₀ hpos).mp hle
      have hdist : edgeSlope p q₀ * ((q.1 : ℚ) - (p.1 : ℚ))
          = edgeSlope p q₀ * (q.1 : ℚ) - edgeSlope p q₀ * (p.1 : ℚ) := by ring
      linarith [key, hdist]

/-- **The maximum-index support point is a lower vertex** (the right endpoint of
the Newton polygon).  Symmetric to `isLowerVertex_of_leftmost`: the supporting
line of greatest edge-slope arriving at `p` lies weakly below every support
point. -/
theorem isLowerVertex_of_rightmost {pts : List SupportPoint} {p : SupportPoint}
    (hp : p ∈ pts) (hright : ∀ q ∈ pts, q ≠ p → q.1 < p.1) :
    IsLowerVertex pts p := by
  classical
  rcases hR : (pts.filter (fun q => decide (q ≠ p))).argmax (edgeSlope · p) with _ | q₀
  · have hempty : pts.filter (fun q => decide (q ≠ p)) = [] := List.argmax_eq_none.mp hR
    refine ⟨hp, 0, p.2, by ring, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; simp
    · have hmem : q ∈ pts.filter (fun q => decide (q ≠ p)) :=
        List.mem_filter.mpr ⟨hq, by simpa using hqp⟩
      rw [hempty] at hmem; simp at hmem
  · refine ⟨hp, edgeSlope q₀ p, p.2 - edgeSlope q₀ p * (p.1 : ℚ), by ring, fun q hq => ?_⟩
    by_cases hqp : q = p
    · subst hqp; linarith
    · have hmem : q ∈ pts.filter (fun q => decide (q ≠ p)) :=
        List.mem_filter.mpr ⟨hq, by simpa using hqp⟩
      have hge : edgeSlope q p ≤ edgeSlope q₀ p := List.le_of_mem_argmax hmem hR
      have hlt : (q.1 : ℚ) < (p.1 : ℚ) := by exact_mod_cast hright q hq hqp
      have hpos : (0 : ℚ) < (p.1 : ℚ) - (q.1 : ℚ) := by linarith
      have key : p.2 - q.2 ≤ edgeSlope q₀ p * ((p.1 : ℚ) - (q.1 : ℚ)) :=
        (div_le_iff₀ hpos).mp hge
      have hdist : edgeSlope q₀ p * ((p.1 : ℚ) - (q.1 : ℚ))
          = edgeSlope q₀ p * (p.1 : ℚ) - edgeSlope q₀ p * (q.1 : ℚ) := by ring
      linarith [key, hdist]

/-- Both endpoints of the worked example `Y² − x` are recovered as lower vertices
by the endpoint theorems: `(0,1)` is leftmost and `(2,0)` is rightmost. -/
theorem ysqMinusX_endpoints :
    IsLowerVertex YsqMinusX (0, 1) ∧ IsLowerVertex YsqMinusX (2, 0) := by
  refine ⟨isLowerVertex_of_leftmost (by simp [YsqMinusX]) ?_,
    isLowerVertex_of_rightmost (by simp [YsqMinusX]) ?_⟩
  · intro q hq hne; fin_cases hq <;> simp_all
  · intro q hq hne; fin_cases hq <;> simp_all

/-! ### Existence of the first edge

The vertex theorems above identify *corners* of the Newton polygon but never
produce an actual edge.  `exists_isLowerEdge_of_leftmost` closes that gap: from
the left endpoint it constructs a genuine `IsLowerEdge`, namely the segment to
the support point of least edge-slope leaving `p`.  This is the first concrete
step of a hull-construction (and hence of the Newton–Puiseux recursion, whose
termination measure `S2-B` reduces the degree one dominant edge at a time):
unlike `isLowerVertex_of_leftmost`, it returns the right endpoint, not just the
fact that `p` is a vertex. -/

/-- **The leftmost support point spawns a lower edge.**  If every other support
point lies strictly to the right of `p`, then joining `p` to the point of least
edge-slope leaving it (`List.argmin (edgeSlope p)`) yields a genuine lower edge:
the dominant (least-slope) edge out of the left endpoint of the Newton polygon. -/
theorem exists_isLowerEdge_of_leftmost {pts : List SupportPoint} {p : SupportPoint}
    (hp : p ∈ pts) (hother : ∃ q ∈ pts, q ≠ p)
    (hleft : ∀ q ∈ pts, q ≠ p → p.1 < q.1) :
    ∃ q, IsLowerEdge pts p q := by
  classical
  rcases hR : (pts.filter (fun q => decide (q ≠ p))).argmin (edgeSlope p) with _ | q₀
  · -- the filter is empty, contradicting the existence of some other point
    obtain ⟨q, hq, hqp⟩ := hother
    have hmem : q ∈ pts.filter (fun q => decide (q ≠ p)) :=
      List.mem_filter.mpr ⟨hq, by simpa using hqp⟩
    rw [List.argmin_eq_none.mp hR] at hmem
    simp at hmem
  · obtain ⟨hq₀pts, hq₀dec⟩ := List.mem_filter.mp (List.argmin_mem hR)
    have hq₀ne : q₀ ≠ p := by simpa using hq₀dec
    have hlt : (p.1 : ℚ) < (q₀.1 : ℚ) := by exact_mod_cast hleft q₀ hq₀pts hq₀ne
    have hlt' : p.1 < q₀.1 := by exact_mod_cast hlt
    have hne : (q₀.1 : ℚ) - (p.1 : ℚ) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlt).symm
    refine ⟨q₀, hp, hq₀pts, hlt', edgeSlope p q₀,
      p.2 - edgeSlope p q₀ * (p.1 : ℚ), by ring, ?_, fun r hr => ?_⟩
    · -- the line of slope `edgeSlope p q₀` through `p` passes through `q₀`
      have hthis : edgeSlope p q₀ * ((q₀.1 : ℚ) - (p.1 : ℚ)) = q₀.2 - p.2 := by
        rw [edgeSlope, div_mul_cancel₀ _ hne]
      linear_combination -hthis
    · -- that line lies weakly below every support point
      by_cases hrp : r = p
      · subst hrp; linarith
      · have hmem : r ∈ pts.filter (fun q => decide (q ≠ p)) :=
          List.mem_filter.mpr ⟨hr, by simpa using hrp⟩
        have hle : edgeSlope p q₀ ≤ edgeSlope p r := List.le_of_mem_argmin hmem hR
        have hltr : (p.1 : ℚ) < (r.1 : ℚ) := by exact_mod_cast hleft r hr hrp
        have hpos : (0 : ℚ) < (r.1 : ℚ) - (p.1 : ℚ) := by linarith
        have key : edgeSlope p q₀ * ((r.1 : ℚ) - (p.1 : ℚ)) ≤ r.2 - p.2 :=
          (le_div_iff₀ hpos).mp hle
        have hexp : edgeSlope p q₀ * ((r.1 : ℚ) - (p.1 : ℚ))
            = edgeSlope p q₀ * (r.1 : ℚ) - edgeSlope p q₀ * (p.1 : ℚ) := by ring
        linarith [key, hexp]

/-- The worked example `Y² − x` again, now via `exists_isLowerEdge_of_leftmost`:
the leftmost support point `(0,1)` spawns a lower edge without supplying its right
endpoint by hand. -/
theorem ysqMinusX_exists_edge : ∃ q, IsLowerEdge YsqMinusX (0, 1) q :=
  exists_isLowerEdge_of_leftmost (by simp [YsqMinusX])
    ⟨(2, 0), by simp [YsqMinusX], by decide⟩
    (by intro q hq hne; fin_cases hq <;> simp_all)

/-! ### Global convexity: the whole edge-slope sequence is sorted

`edgeSlope_mono` proves convexity for *two* adjacent edges sharing a vertex.  The
Newton polygon is a *chain* of such edges `v₀ → v₁ → … → vₙ`, and its defining
structural property is that **all** the edge slopes are non-decreasing along the
chain — equivalently, the negated slopes (the root valuations) are sorted.  This
section lifts the pairwise statement to the entire chain.

We model a polygon as a list of vertices `vs` whose consecutive pairs are lower
edges (`List.IsChain (IsLowerEdge pts) vs`), read off its edge slopes with
`edgeSlopes`, and prove that list is `Pairwise (· ≤ ·)` — i.e. sorted: every
slope is `≤` every later one.  The proof is a clean structural induction whose
only arithmetic input is `edgeSlope_mono`. -/

/-- The list of edge slopes along a chain of support points: the slope of each
consecutive pair.  `edgeSlopes [v₀, v₁, …, vₙ] = [edgeSlope v₀ v₁, …,
edgeSlope vₙ₋₁ vₙ]`. -/
def edgeSlopes : List SupportPoint → List ℚ
  | p :: q :: rest => edgeSlope p q :: edgeSlopes (q :: rest)
  | _ => []

/-- **Global convexity (chain form).**  Along any chain of lower edges the edge
slopes are non-decreasing between consecutive entries.  Structural induction:
the head step `edgeSlope p q ≤ edgeSlope q r` is `edgeSlope_mono`, the tail is the
induction hypothesis. -/
theorem chain_edgeSlopes {pts : List SupportPoint} :
    ∀ {vs : List SupportPoint}, List.IsChain (IsLowerEdge pts) vs →
      List.IsChain (· ≤ ·) (edgeSlopes vs)
  | [], _ => by simp only [edgeSlopes]; exact List.isChain_nil
  | [_], _ => by simp only [edgeSlopes]; exact List.isChain_nil
  | p :: q :: rest, hc => by
      cases rest with
      | nil => simp only [edgeSlopes]; exact List.isChain_singleton _
      | cons r rest' =>
        obtain ⟨hpq, hc'⟩ := List.isChain_cons_cons.mp hc
        obtain ⟨hqr, _⟩ := List.isChain_cons_cons.mp hc'
        have ih := chain_edgeSlopes hc'
        simp only [edgeSlopes] at ih ⊢
        exact List.isChain_cons_cons.mpr ⟨edgeSlope_mono hpq hqr, ih⟩

/-- **Global convexity (sorted form).**  The edge slopes of a Newton polygon are
`Pairwise (· ≤ ·)`: every slope is `≤` every later slope, not merely the next
one.  This is the full statement that the lower hull is convex.  (`IsChain`
upgrades to `Pairwise` because `≤` on `ℚ` is transitive.) -/
theorem edgeSlopes_pairwise_le {pts vs : List SupportPoint}
    (hc : List.IsChain (IsLowerEdge pts) vs) : (edgeSlopes vs).Pairwise (· ≤ ·) :=
  List.isChain_iff_pairwise.mp (chain_edgeSlopes hc)

/-- **The root valuations of the whole polygon are sorted.**  Since each root
valuation is the negative of an edge slope, global convexity says the valuations
read off left-to-right are non-increasing — the sorted list of root valuations
that the Newton–Puiseux recursion consumes one dominant edge at a time. -/
theorem rootValuations_pairwise_ge {pts vs : List SupportPoint}
    (hc : List.IsChain (IsLowerEdge pts) vs) :
    ((edgeSlopes vs).map (fun s => -s)).Pairwise (· ≥ ·) := by
  rw [List.pairwise_map]
  exact (edgeSlopes_pairwise_le hc).imp fun h => neg_le_neg h

/-! ### Worked three-vertex example

A genuine convex chain `(0,2) → (1,0) → (3,1)` with two edges of slopes `-2` and
`1/2`.  Both segments are real lower edges (each supporting line lies weakly
below all three points), so the chain theorems apply and produce the sorted slope
list `[-2, 1/2]`. -/

/-- Support points of a polynomial whose Newton polygon has two edges. -/
def threeVertex : List SupportPoint := [(0, 2), (1, 0), (3, 1)]

/-- The three vertices form a genuine chain of lower edges. -/
theorem threeVertex_chain : List.IsChain (IsLowerEdge threeVertex) threeVertex := by
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩⟩
  · refine ⟨by simp [threeVertex], by simp [threeVertex], by norm_num,
      -2, 2, by norm_num, by norm_num, fun r hr => ?_⟩
    fin_cases hr <;> norm_num
  · refine ⟨by simp [threeVertex], by simp [threeVertex], by norm_num,
      1/2, -1/2, by norm_num, by norm_num, fun r hr => ?_⟩
    fin_cases hr <;> norm_num

/-- The edge slopes of the example are `[-2, 1/2]`. -/
theorem threeVertex_edgeSlopes : edgeSlopes threeVertex = [-2, 1/2] := by
  norm_num [edgeSlopes, threeVertex, edgeSlope]

/-- The example's edge slopes are sorted — global convexity in action. -/
theorem threeVertex_sorted : (edgeSlopes threeVertex).Pairwise (· ≤ ·) :=
  edgeSlopes_pairwise_le threeVertex_chain

/-! ### Degree counting: edge widths sum to the index span

The edge slopes carry the *valuations* of the roots; the **widths** carry their
*multiplicities*.  The horizontal projection (width) of the edge from `p` to `q`
is `q.1 − p.1`, and the Newton polygon theorem assigns to that edge exactly
`q.1 − p.1` roots (counted with multiplicity), all of valuation `−edgeSlope p q`.
So the combinatorial backbone of "every root is accounted for" is the telescoping
identity proved here: along any vertex chain the edge widths sum to the index
span `(last index) − (first index)`.  For a degree-`d` polynomial whose hull runs
from index `0` (constant term) to index `d` (leading term), the widths sum to
`d` — all `d` roots, with multiplicity, are distributed across the edges.

This is the multiplicity counterpart of the slope-sorting results above
(`edgeSlopes_pairwise_le`); together they say the Newton polygon reads off the
roots' valuations *in sorted order* and *with the correct total multiplicity*. -/

/-- The list of edge widths along a chain of support points: the horizontal
projection `q.1 − p.1` of each consecutive pair.  `edgeWidths [v₀, …, vₙ]
= [v₁.1 − v₀.1, …, vₙ.1 − vₙ₋₁.1]`. -/
def edgeWidths : List SupportPoint → List ℚ
  | p :: q :: rest => ((q.1 : ℚ) - (p.1 : ℚ)) :: edgeWidths (q :: rest)
  | _ => []

/-- **Telescoping degree identity.**  The edge widths along any vertex chain sum
to the span of indices from the first vertex to the last — the total horizontal
extent of the Newton polygon.  Proof is the usual telescoping induction; the head
width `v₁.1 − v₀.1` plus the tail span `(last).1 − v₁.1` collapses to
`(last).1 − v₀.1`. -/
theorem sum_edgeWidths : ∀ (v : SupportPoint) (vs : List SupportPoint),
    (edgeWidths (v :: vs)).sum = (((v :: vs).getLast (by simp)).1 : ℚ) - (v.1 : ℚ)
  | _, [] => by simp [edgeWidths]
  | v, w :: ws => by
      have ih := sum_edgeWidths w ws
      have hgl : (v :: w :: ws).getLast (by simp) = (w :: ws).getLast (by simp) :=
        List.getLast_cons (by simp)
      simp only [edgeWidths, List.sum_cons]
      rw [ih, hgl]
      ring

/-- **All edge widths along a Newton polygon are positive.**  Each lower edge has
`p.1 < q.1` by definition, so every width in the chain is strictly positive.
Combined with `sum_edgeWidths` this shows the index span is positive whenever the
polygon has at least one edge: the hull genuinely moves left-to-right. -/
theorem edgeWidths_pos {pts : List SupportPoint} :
    ∀ {vs : List SupportPoint}, List.IsChain (IsLowerEdge pts) vs →
      ∀ w ∈ edgeWidths vs, 0 < w
  | [], _ => by simp [edgeWidths]
  | [_], _ => by simp [edgeWidths]
  | p :: q :: rest, hc => by
      intro w hw
      obtain ⟨hpq, hc'⟩ := List.isChain_cons_cons.mp hc
      simp only [edgeWidths, List.mem_cons] at hw
      rcases hw with rfl | hw
      · obtain ⟨_, _, hlt, _⟩ := hpq
        have : (p.1 : ℚ) < (q.1 : ℚ) := by exact_mod_cast hlt
        linarith
      · exact edgeWidths_pos hc' w hw

/-- **The degree-counting corollary.**  For a Newton polygon whose vertex chain
runs from the left endpoint at index `0` to the right endpoint at index `d` (the
`Y`-degree), the edge widths sum to `d`: all `d` roots are distributed, with
multiplicity, across the edges of the polygon. -/
theorem sum_edgeWidths_eq_degree {v : SupportPoint} {vs : List SupportPoint}
    {d : ℕ} (hv : v.1 = 0) (hlast : ((v :: vs).getLast (by simp)).1 = d) :
    (edgeWidths (v :: vs)).sum = d := by
  rw [sum_edgeWidths, hlast, hv]; simp

/-- The widths of the worked three-vertex example are `[1, 2]`. -/
theorem threeVertex_edgeWidths : edgeWidths threeVertex = [1, 2] := by
  norm_num [edgeWidths, threeVertex]

/-- The example's edge widths sum to `3`, the index span from `(0,2)` to `(3,1)` —
the polygon accounts for all `3` units of `Y`-degree. -/
theorem threeVertex_sum_widths : (edgeWidths threeVertex).sum = 3 := by
  norm_num [edgeWidths, threeVertex]

/-- The example's widths are all positive (it is a genuine left-to-right chain). -/
theorem threeVertex_widths_pos : ∀ w ∈ edgeWidths threeVertex, 0 < w :=
  edgeWidths_pos threeVertex_chain

/-! ### Slope × width = vertical drop (the "product of roots" bookkeeping)

The two halves built above run in parallel but never meet: `edgeSlopes` carries
the root **valuations** (sorted, `edgeSlopes_pairwise_le`) and `edgeWidths` carries
the root **multiplicities** (telescoping to the degree, `sum_edgeWidths_eq_degree`).
This section couples them.  For each edge, `edgeSlope p q · (width p q)` collapses
to the **vertical drop** `q.2 − p.2`, and summing along a chain telescopes to the
total drop `(last).2 − (first).2`.

In Newton–Puiseux terms this is the *multiplicative* counterpart of the
degree-counting identity.  Each edge contributes `width` roots of valuation
`−slope`, so `slope · width` is the total valuation those roots carry, and the
sum over all edges is `Σ (valuationᵢ · multiplicityᵢ)` — the valuation of the
product of all roots, i.e. `v(constant term) − v(leading term)` read straight off
the endpoints of the polygon.  Where `sum_edgeWidths_eq_degree` says *how many*
roots there are, this says *what their valuations sum to with multiplicity*. -/

/-- **Per-edge slope × width identity.**  The edge slope times the horizontal
width recovers the vertical drop, because the width is exactly the denominator of
the slope.  Requires distinct indices so the width is nonzero. -/
theorem edgeSlope_mul_width {p q : SupportPoint} (hne : p.1 ≠ q.1) :
    edgeSlope p q * ((q.1 : ℚ) - (p.1 : ℚ)) = q.2 - p.2 := by
  have hd : (q.1 : ℚ) - (p.1 : ℚ) ≠ 0 :=
    sub_ne_zero.mpr fun h => hne (Nat.cast_injective h).symm
  rw [edgeSlope, div_mul_cancel₀ _ hd]

/-- The list of vertical drops along a chain of support points: the rise
`q.2 − p.2` of each consecutive pair.  `edgeDrops [v₀, …, vₙ]
= [v₁.2 − v₀.2, …, vₙ.2 − vₙ₋₁.2]`. -/
def edgeDrops : List SupportPoint → List ℚ
  | p :: q :: rest => (q.2 - p.2) :: edgeDrops (q :: rest)
  | _ => []

/-- **Telescoping drop identity.**  The vertical drops along any vertex chain sum
to the total drop from the first vertex to the last.  Same telescoping induction as
`sum_edgeWidths`, with the `y`-coordinate in place of the `x`-coordinate. -/
theorem sum_edgeDrops : ∀ (v : SupportPoint) (vs : List SupportPoint),
    (edgeDrops (v :: vs)).sum = ((v :: vs).getLast (by simp)).2 - v.2
  | _, [] => by simp [edgeDrops]
  | v, w :: ws => by
      have ih := sum_edgeDrops w ws
      have hgl : (v :: w :: ws).getLast (by simp) = (w :: ws).getLast (by simp) :=
        List.getLast_cons (by simp)
      simp only [edgeDrops, List.sum_cons]
      rw [ih, hgl]
      ring

/-- **The slope list and width list zip to the drop list.**  Along a chain of
lower edges (so every edge has distinct indices), the elementwise product of the
edge slopes and edge widths is exactly the list of vertical drops.  This is the
list-level statement that couples the valuation data to the multiplicity data. -/
theorem zipWith_edgeSlopes_edgeWidths {pts : List SupportPoint} :
    ∀ {vs : List SupportPoint}, List.IsChain (IsLowerEdge pts) vs →
      List.zipWith (· * ·) (edgeSlopes vs) (edgeWidths vs) = edgeDrops vs
  | [], _ => by simp [edgeSlopes, edgeWidths, edgeDrops]
  | [_], _ => by simp [edgeSlopes, edgeWidths, edgeDrops]
  | p :: q :: rest, hc => by
      obtain ⟨hpq, hc'⟩ := List.isChain_cons_cons.mp hc
      have hne : p.1 ≠ q.1 := by
        obtain ⟨_, _, hlt, _⟩ := hpq; exact ne_of_lt hlt
      have ih := zipWith_edgeSlopes_edgeWidths hc'
      simp only [edgeSlopes, edgeWidths, edgeDrops, List.zipWith_cons_cons]
      rw [edgeSlope_mul_width hne, ih]

/-- **The capstone bookkeeping identity.**  Along a Newton-polygon vertex chain the
slope-weighted-by-width sum telescopes to the total vertical drop.  Combining the
list-level coupling with the drop telescope:
`Σ (edgeSlopeᵢ · widthᵢ) = (last).2 − (first).2`.  Since each edge slope is the
negated valuation and each width the multiplicity of its roots, the left side is
`−Σ(valuationᵢ · multiplicityᵢ)`; the right side is the drop in `y`-coordinate
across the polygon. -/
theorem sum_slope_mul_width {pts : List SupportPoint} {v : SupportPoint}
    {vs : List SupportPoint} (hc : List.IsChain (IsLowerEdge pts) (v :: vs)) :
    (List.zipWith (· * ·) (edgeSlopes (v :: vs)) (edgeWidths (v :: vs))).sum
      = ((v :: vs).getLast (by simp)).2 - v.2 := by
  rw [zipWith_edgeSlopes_edgeWidths hc, sum_edgeDrops]

/-- **Sum of root valuations counted with multiplicity.**  Negating the capstone:
since each root valuation is `−edgeSlope` and the width is its multiplicity,
`Σ (valuationᵢ · multiplicityᵢ) = (first).2 − (last).2 = v(constant) − v(leading)`.
This is the valuation of the product of all the roots, read straight off the two
endpoints of the polygon. -/
theorem neg_sum_slope_mul_width {pts : List SupportPoint} {v : SupportPoint}
    {vs : List SupportPoint} (hc : List.IsChain (IsLowerEdge pts) (v :: vs)) :
    -(List.zipWith (· * ·) (edgeSlopes (v :: vs)) (edgeWidths (v :: vs))).sum
      = v.2 - ((v :: vs).getLast (by simp)).2 := by
  rw [sum_slope_mul_width hc]; ring

/-- The example's slope-weighted-by-width products are `[-2, 1]`, summing to `-1`:
the total vertical drop from `(0,2)` to `(3,1)`. -/
theorem threeVertex_sum_slope_mul_width :
    (List.zipWith (· * ·) (edgeSlopes threeVertex) (edgeWidths threeVertex)).sum = -1 := by
  rw [threeVertex_edgeSlopes, threeVertex_edgeWidths]
  norm_num [List.zipWith_cons_cons]

/-! ### Hull construction: splicing a dominant edge onto the right sub-hull

The results so far identify vertices and edges and prove the polygon convex *given*
a chain of lower edges, but they never *build* the chain.  `exists_isLowerEdge_of_leftmost`
produces the dominant (least-slope) first edge `p → q` from the left endpoint; the
Newton–Puiseux recursion then continues on the support to the right of `q`.

The mathematical subtlety the recursion hides is this: a lower edge of the *right
restriction* `pts.filter (q.1 ≤ ·.1)` need not be a lower edge of the *full* `pts`,
because its supporting line — pinned only by the right points — could dip below a
point left of `q`.  The **transfer lemma** `isLowerEdge_of_right` shows this never
happens *provided the edge's slope is at least the dominant slope*: convexity forces
the right edge's line to sit above the dominant line on the left half, where the
dominant line already lies below every point.  This is the exact reason the
divide-and-conquer hull recursion is correct, and it is the principal combinatorial
input that was missing from this file.

`chain_transfer` then propagates the bound along an entire right sub-hull (each edge
slope dominates the previous one by `edgeSlope_mono`, so all of them clear the
dominant slope), and `isLowerEdge_chain_extend` packages the whole step: prepend the
dominant edge to a right sub-hull chain and obtain a genuine lower-edge chain of the
full support — one peel of the Newton–Puiseux recursion, verified. -/

/-- **Global-support transfer across a dominant split.**  Let `(m₀, b₀)` be the line
of a *dominant* edge: it passes through the cut point `q` and lies weakly below every
support point of `pts`.  If `a → c` is a lower edge of the right restriction
`pts.filter (q.1 ≤ ·.1)` whose slope is at least the dominant slope `m₀`, then
`a → c` is a lower edge of the *full* `pts`.

The only nontrivial check is that the `a → c` line stays below the points left of the
cut.  There its slope `m ≥ m₀` makes it sit below the dominant line (the two lines
cross at the cut, where `a → c` is already below `q`), and the dominant line is below
everything — so `a → c` clears the left points too. -/
theorem isLowerEdge_of_right {pts : List SupportPoint} {q a c : SupportPoint}
    {m₀ b₀ : ℚ} (hq_mem : q ∈ pts) (hq_line : q.2 = m₀ * (q.1 : ℚ) + b₀)
    (hsupp0 : ∀ r ∈ pts, m₀ * (r.1 : ℚ) + b₀ ≤ r.2)
    (hac : IsLowerEdge (pts.filter (fun r => decide (q.1 ≤ r.1))) a c)
    (hslope : m₀ ≤ edgeSlope a c) :
    IsLowerEdge pts a c := by
  obtain ⟨ha_filt, hc_filt, hac_lt, m, b, ha_line, hc_line, hsupp_filt⟩ := hac
  have ha_pts : a ∈ pts := (List.mem_filter.mp ha_filt).1
  have hc_pts : c ∈ pts := (List.mem_filter.mp hc_filt).1
  have hm : m = edgeSlope a c := slope_eq_edgeSlope ha_line hc_line (ne_of_lt hac_lt)
  have hmge : m₀ ≤ m := by rw [hm]; exact hslope
  -- the cut point `q` lies in the right restriction, so the `a → c` line is below it
  have hq_filt : q ∈ pts.filter (fun r => decide (q.1 ≤ r.1)) :=
    List.mem_filter.mpr ⟨hq_mem, by simp⟩
  have hqcmp : m * (q.1 : ℚ) + b ≤ m₀ * (q.1 : ℚ) + b₀ := by
    rw [← hq_line]; exact hsupp_filt q hq_filt
  refine ⟨ha_pts, hc_pts, hac_lt, m, b, ha_line, hc_line, fun r hr => ?_⟩
  by_cases hr_cut : q.1 ≤ r.1
  · exact hsupp_filt r (List.mem_filter.mpr ⟨hr, by simpa using hr_cut⟩)
  · push_neg at hr_cut
    have hr_lt : (r.1 : ℚ) < (q.1 : ℚ) := by exact_mod_cast hr_cut
    have hsupp0r : m₀ * (r.1 : ℚ) + b₀ ≤ r.2 := hsupp0 r hr
    nlinarith [mul_nonneg (sub_nonneg.mpr hmge) (sub_nonneg.mpr (le_of_lt hr_lt)),
      hqcmp, hsupp0r]

/-- **Propagating the dominant bound along a right sub-hull.**  Given a dominant line
`(m₀, b₀)` through the cut `q` lying below all of `pts`, any chain of lower edges of
the right restriction whose first edge clears the dominant slope is, edge for edge, a
chain of lower edges of the full `pts`.  Each successive edge slope dominates the
previous one (`edgeSlope_mono`), so the bound carries to the whole chain and
`isLowerEdge_of_right` upgrades every edge. -/
theorem chain_transfer {pts : List SupportPoint} {q : SupportPoint} {m₀ b₀ : ℚ}
    (hq_mem : q ∈ pts) (hq_line : q.2 = m₀ * (q.1 : ℚ) + b₀)
    (hsupp0 : ∀ r ∈ pts, m₀ * (r.1 : ℚ) + b₀ ≤ r.2) :
    ∀ (a : SupportPoint) (rest : List SupportPoint),
      List.IsChain (IsLowerEdge (pts.filter (fun r => decide (q.1 ≤ r.1)))) (a :: rest) →
      (∀ c, rest.head? = some c → m₀ ≤ edgeSlope a c) →
      List.IsChain (IsLowerEdge pts) (a :: rest)
  | _, [], _, _ => List.isChain_singleton _
  | a, c :: rest', hchain, hbound => by
      obtain ⟨hac, hchain'⟩ := List.isChain_cons_cons.mp hchain
      have hac_slope : m₀ ≤ edgeSlope a c := hbound c rfl
      have hi : IsLowerEdge pts a c :=
        isLowerEdge_of_right hq_mem hq_line hsupp0 hac hac_slope
      refine List.isChain_cons_cons.mpr ⟨hi, ?_⟩
      refine chain_transfer hq_mem hq_line hsupp0 c rest' hchain' ?_
      intro d hd
      cases rest' with
      | nil => simp at hd
      | cons e rest'' =>
        simp only [List.head?_cons, Option.some.injEq] at hd
        subst hd
        obtain ⟨hce, _⟩ := List.isChain_cons_cons.mp hchain'
        exact le_trans hac_slope (edgeSlope_mono hac hce)

/-- **One peel of the Newton–Puiseux recursion, verified.**  Prepend the dominant
edge `p → q` (least-slope edge leaving the left endpoint, whose line `(m₀, b₀)`
supports all of `pts`) to a chain of lower edges of the right restriction
`pts.filter (q.1 ≤ ·.1)`, and obtain a genuine chain of lower edges of the full
`pts`.  This is the inductive step of hull construction: the leftmost dominant edge
followed by the recursively-built right sub-hull is the complete Newton polygon. -/
theorem isLowerEdge_chain_extend {pts : List SupportPoint} {p q : SupportPoint}
    {m₀ b₀ : ℚ} {rest : List SupportPoint}
    (hp_mem : p ∈ pts) (hq_mem : q ∈ pts) (hpq_lt : p.1 < q.1)
    (hp_line : p.2 = m₀ * (p.1 : ℚ) + b₀) (hq_line : q.2 = m₀ * (q.1 : ℚ) + b₀)
    (hsupp0 : ∀ r ∈ pts, m₀ * (r.1 : ℚ) + b₀ ≤ r.2)
    (hchain : List.IsChain (IsLowerEdge (pts.filter (fun r => decide (q.1 ≤ r.1))))
      (q :: rest)) :
    List.IsChain (IsLowerEdge pts) (p :: q :: rest) := by
  refine List.isChain_cons_cons.mpr
    ⟨⟨hp_mem, hq_mem, hpq_lt, m₀, b₀, hp_line, hq_line, hsupp0⟩, ?_⟩
  refine chain_transfer hq_mem hq_line hsupp0 q rest hchain ?_
  intro c hc
  cases rest with
  | nil => simp at hc
  | cons d rest'' =>
    simp only [List.head?_cons, Option.some.injEq] at hc
    subst hc
    obtain ⟨hqd, _⟩ := List.isChain_cons_cons.mp hchain
    have hd_pts : d ∈ pts := (List.mem_filter.mp hqd.2.1).1
    have hqd_lt : (q.1 : ℚ) < (d.1 : ℚ) := by exact_mod_cast hqd.2.2.1
    exact edgeSlope_ge_of_supportingLine hq_line hd_pts hsupp0 hqd_lt

/-! ### Worked example: building the two-edge polygon by splicing

We rebuild `threeVertex_chain` — the chain `(0,2) → (1,0) → (3,1)` — *constructively*
via `isLowerEdge_chain_extend`, supplying only the dominant edge `(0,2) → (1,0)` and
the right sub-hull `(1,0) → (3,1)` over the restriction `{(1,0), (3,1)}`.  The transfer
machinery promotes the right edge — whose hand-built supporting line ignores `(0,2)` —
to a genuine lower edge of the full support. -/

/-- The right restriction of `threeVertex` at the cut index `1` is `[(1,0), (3,1)]`. -/
theorem threeVertex_filter :
    threeVertex.filter (fun r => decide ((1 : ℕ) ≤ r.1)) = [((1, 0) : SupportPoint), (3, 1)] := by
  decide

/-- The right sub-hull is a single lower edge of the restriction. -/
theorem threeVertex_rightHull :
    List.IsChain (IsLowerEdge (threeVertex.filter (fun r => decide ((1 : ℕ) ≤ r.1))))
      [((1, 0) : SupportPoint), (3, 1)] := by
  rw [threeVertex_filter]
  refine List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩
  refine ⟨by simp, by simp, by norm_num, 1 / 2, -1 / 2, by norm_num, by norm_num, fun r hr => ?_⟩
  fin_cases hr <;> norm_num

/-- `threeVertex_chain` rebuilt by splicing the dominant edge onto the right sub-hull,
exercising `isLowerEdge_chain_extend`.  The right edge `(1,0) → (3,1)` becomes a lower
edge of the *full* `threeVertex` only because its slope `1/2` clears the dominant slope
`-2` — exactly the transfer hypothesis. -/
theorem threeVertex_chain_via_extend :
    List.IsChain (IsLowerEdge threeVertex) threeVertex :=
  isLowerEdge_chain_extend (p := (0, 2)) (q := (1, 0)) (m₀ := -2) (b₀ := 2)
    (by simp [threeVertex]) (by simp [threeVertex]) (by norm_num)
    (by norm_num) (by norm_num)
    (fun r hr => by fin_cases hr <;> norm_num)
    threeVertex_rightHull

/-! ### The complete lower hull: a verified Newton–Puiseux peel-down

Everything above builds *one* peel of the recursion (`isLowerEdge_chain_extend`) and
proves a given chain convex.  The capstone is to run the recursion to completion: from
the left endpoint, repeatedly splice the dominant edge onto the right sub-hull until the
support is exhausted, and obtain a *single* chain of lower edges that starts at the
leftmost vertex and ends at the rightmost.  This is the existence half of the Newton
polygon construction — the object the Newton–Puiseux algorithm walks edge by edge.

The recursion measure is `pts.length`: each peel removes the leftmost point from the
right-restriction `pts.filter (q.1 ≤ ·.1)` (the dominant cut sits strictly to its right),
so the restriction is strictly shorter and the fuelled strong induction below terminates.
The only mathematical inputs are the existence of a dominant edge from the left endpoint
(`exists_isLowerEdge_of_leftmost`) and the transfer step that promotes the recursively
built right sub-hull to a chain of the full support (`isLowerEdge_chain_extend`). -/

/-- **Fuelled strong-induction core of the hull construction.**  With `pts.length ≤ n`
as the well-founded measure, a strictly-leftmost point `p` of a distinct-index support
spawns a chain of lower edges `p :: vs` of `pts` ending at a vertex `w` of maximal index.
Each recursion peels the dominant edge `p → q₀` and recurses on the right restriction,
which is strictly shorter (so its length is `≤ n`). -/
theorem exists_lowerHull_aux : ∀ (n : ℕ) (pts : List SupportPoint) (p : SupportPoint),
    pts.length ≤ n → p ∈ pts →
    (∀ a ∈ pts, ∀ b ∈ pts, a.1 = b.1 → a = b) →
    (∀ q ∈ pts, q ≠ p → p.1 < q.1) →
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge pts) (p :: vs) ∧
      (p :: vs).getLast? = some w ∧ w ∈ pts ∧ ∀ r ∈ pts, r.1 ≤ w.1 := by
  intro n
  induction n with
  | zero =>
    intro pts p hlen hp _ _
    rw [List.eq_nil_iff_length_eq_zero.mpr (Nat.le_zero.mp hlen)] at hp
    simp at hp
  | succ n ih =>
    intro pts p hlen hp hdist hleft
    by_cases hmax : ∀ r ∈ pts, r.1 ≤ p.1
    · -- `p` is already the rightmost vertex: the hull is the single point `[p]`.
      exact ⟨[], p, List.isChain_singleton _, rfl, hp, hmax⟩
    · -- some support point lies strictly to the right of `p`; peel the dominant edge.
      push_neg at hmax
      obtain ⟨r₀, hr₀, hr₀lt⟩ := hmax
      have hother : ∃ q ∈ pts, q ≠ p :=
        ⟨r₀, hr₀, fun h => by rw [h] at hr₀lt; exact lt_irrefl _ hr₀lt⟩
      obtain ⟨q₀, hedge⟩ := exists_isLowerEdge_of_leftmost hp hother hleft
      obtain ⟨hp_mem, hq₀_mem, hpq_lt, m₀, b₀, hp_line, hq₀_line, hsupp0⟩ := hedge
      -- the right restriction at the dominant cut `q₀`
      have hq₀' : q₀ ∈ pts.filter (fun r => decide (q₀.1 ≤ r.1)) :=
        List.mem_filter.mpr ⟨hq₀_mem, by simp⟩
      -- the restriction is strictly shorter (it drops `p`), so its length is `≤ n`
      have hlen' : (pts.filter (fun r => decide (q₀.1 ≤ r.1))).length ≤ n := by
        have hle := List.length_filter_le (fun r => decide (q₀.1 ≤ r.1)) pts
        rcases lt_or_eq_of_le hle with h | h
        · omega
        · exfalso
          rw [List.length_filter_eq_length_iff] at h
          have hpp := h p hp
          simp only [decide_eq_true_eq] at hpp
          omega
      -- distinctness passes to the sublist
      have hdist' : ∀ a ∈ pts.filter (fun r => decide (q₀.1 ≤ r.1)),
          ∀ b ∈ pts.filter (fun r => decide (q₀.1 ≤ r.1)), a.1 = b.1 → a = b :=
        fun a ha b hb hab =>
          hdist a (List.mem_filter.mp ha).1 b (List.mem_filter.mp hb).1 hab
      -- `q₀` is strictly leftmost in the restriction
      have hleft' : ∀ q ∈ pts.filter (fun r => decide (q₀.1 ≤ r.1)), q ≠ q₀ → q₀.1 < q.1 := by
        intro q hq hqne
        obtain ⟨hq_pts, hq_dec⟩ := List.mem_filter.mp hq
        have hge : q₀.1 ≤ q.1 := by simpa using hq_dec
        rcases lt_or_eq_of_le hge with h | h
        · exact h
        · exact absurd (hdist q hq_pts q₀ hq₀_mem h.symm) hqne
      -- recurse on the strictly shorter restriction
      obtain ⟨vs', w, hchain', hlast', hw_pts', hwmax'⟩ :=
        ih (pts.filter (fun r => decide (q₀.1 ≤ r.1))) q₀ hlen' hq₀' hdist' hleft'
      refine ⟨q₀ :: vs', w, ?_, ?_, (List.mem_filter.mp hw_pts').1, ?_⟩
      · -- splice the dominant edge onto the recursively built right sub-hull
        exact isLowerEdge_chain_extend hp_mem hq₀_mem hpq_lt hp_line hq₀_line hsupp0 hchain'
      · -- the last vertex is unchanged by prepending `p`
        rw [show (p :: q₀ :: vs').getLast? = (q₀ :: vs').getLast? from rfl]; exact hlast'
      · -- `w` has maximal index over all of `pts`, not just the restriction
        intro r hr
        by_cases hcut : q₀.1 ≤ r.1
        · exact hwmax' r (List.mem_filter.mpr ⟨hr, by simpa using hcut⟩)
        · push_neg at hcut
          have hq₀w : q₀.1 ≤ w.1 := hwmax' q₀ hq₀'
          omega

/-- **Existence of the complete lower hull (Newton polygon chain).**  For any
distinct-index support with a strictly-leftmost point `p`, there is a chain of lower
edges `p :: vs` of `pts` whose final vertex `w` has the maximal index over the whole
support.  Equivalently: the dominant edges from the left endpoint splice into one
connected lower hull reaching the right endpoint.  This is the existence statement the
Newton–Puiseux recursion realizes; combined with `edgeSlopes_pairwise_le` (global
convexity) the resulting chain has sorted edge slopes — sorted root valuations. -/
theorem exists_lowerHull {pts : List SupportPoint} (p : SupportPoint)
    (hp : p ∈ pts)
    (hdist : ∀ a ∈ pts, ∀ b ∈ pts, a.1 = b.1 → a = b)
    (hleft : ∀ q ∈ pts, q ≠ p → p.1 < q.1) :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge pts) (p :: vs) ∧
      (p :: vs).getLast? = some w ∧ w ∈ pts ∧ ∀ r ∈ pts, r.1 ≤ w.1 :=
  exists_lowerHull_aux pts.length pts p le_rfl hp hdist hleft

/-- The worked example `Y² − x`: the complete lower hull from the leftmost vertex
`(0,1)` is the single edge to `(2,0)`, and `(2,0)` has maximal index — the constructive
end-to-end Newton polygon of the support `{(0,1), (2,0)}`. -/
theorem ysqMinusX_lowerHull :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge YsqMinusX) ((0, 1) :: vs) ∧
      ((0, 1) :: vs).getLast? = some w ∧ w ∈ YsqMinusX ∧ ∀ r ∈ YsqMinusX, r.1 ≤ w.1 :=
  exists_lowerHull (0, 1) (by simp [YsqMinusX])
    (by intro a ha b hb hab; fin_cases ha <;> fin_cases hb <;> simp_all)
    (by intro q hq hne; fin_cases hq <;> simp_all)

/-! ### Capstone: the complete Newton polygon, sorted and counted

The prior sessions built three pieces that never quite met on the *same* object:

* `exists_lowerHull` — the connected hull chain from the leftmost to the rightmost
  vertex actually exists (the divide-and-conquer recursion runs to completion);
* `edgeSlopes_pairwise_le` — the **valuation** half: any lower-edge chain has sorted
  edge slopes (negated = root valuations, non-increasing);
* `sum_edgeWidths` / `edgeWidths_pos` — the **multiplicity** half: the edge widths
  are positive and telescope to the index span (the `Y`-degree when anchored at `0`).

The first two were stated about an *abstract* chain hypothesis; the existence theorem
produced a *concrete* chain but said nothing about its slopes or widths.  The two
corollaries below close that gap by discharging the chain hypothesis with the very
chain the recursion builds, so the bundled combinatorial Newton polygon is now a
single existence statement. -/

/-- **The hull the recursion builds has sorted edge slopes.**  This is the literal
"single corollary" the construction was aiming for: compose `exists_lowerHull`
(existence of the connected lower hull) with `edgeSlopes_pairwise_le` (global
convexity) to obtain a hull chain from the leftmost to the rightmost vertex whose
edge slopes are sorted — i.e. whose negated slopes are the root valuations in sorted
(non-increasing) order, read off end to end. -/
theorem exists_lowerHull_sorted {pts : List SupportPoint} (p : SupportPoint)
    (hp : p ∈ pts)
    (hdist : ∀ a ∈ pts, ∀ b ∈ pts, a.1 = b.1 → a = b)
    (hleft : ∀ q ∈ pts, q ≠ p → p.1 < q.1) :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge pts) (p :: vs) ∧
      (p :: vs).getLast? = some w ∧ w ∈ pts ∧ (∀ r ∈ pts, r.1 ≤ w.1) ∧
      (edgeSlopes (p :: vs)).Pairwise (· ≤ ·) := by
  obtain ⟨vs, w, hchain, hlast, hw, hwmax⟩ := exists_lowerHull p hp hdist hleft
  exact ⟨vs, w, hchain, hlast, hw, hwmax, edgeSlopes_pairwise_le hchain⟩

/-- **The combinatorial Newton polygon, assembled end to end.**  For a distinct-index
support with strictly-leftmost point `p`, the lower-hull chain produced by
`exists_lowerHull` simultaneously satisfies every combinatorial property the
Newton–Puiseux recursion needs:

* it is a genuine chain of lower edges from `p` to a rightmost vertex `w`
  (`w` has maximal index over all of `pts`);
* its **edge slopes are sorted** (`Pairwise (· ≤ ·)`) — negated, the root valuations
  in sorted (non-increasing) order;
* its **edge widths are all positive** — every edge genuinely moves left-to-right;
* its **widths sum to the index span** `w.1 − p.1` — all roots accounted for with
  multiplicity (the `Y`-degree count when `p.1 = 0`).

This single statement bundles the valuation half (`edgeSlopes_pairwise_le`), the
multiplicity half (`sum_edgeWidths`, `edgeWidths_pos`), and the existence of the hull
(`exists_lowerHull`) into the complete combinatorial content of the Newton polygon
theorem.  Only the analytic bridge (slopes/widths ↔ actual roots of `P ∈ K((x))[Y]`)
remains, blocked on a `K((x))[Y]` valuation API absent from Mathlib 4.26.0. -/
theorem exists_lowerHull_newtonPolygon {pts : List SupportPoint} (p : SupportPoint)
    (hp : p ∈ pts)
    (hdist : ∀ a ∈ pts, ∀ b ∈ pts, a.1 = b.1 → a = b)
    (hleft : ∀ q ∈ pts, q ≠ p → p.1 < q.1) :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge pts) (p :: vs) ∧
      (p :: vs).getLast? = some w ∧ w ∈ pts ∧ (∀ r ∈ pts, r.1 ≤ w.1) ∧
      (edgeSlopes (p :: vs)).Pairwise (· ≤ ·) ∧
      (∀ z ∈ edgeWidths (p :: vs), 0 < z) ∧
      (edgeWidths (p :: vs)).sum = (w.1 : ℚ) - (p.1 : ℚ) := by
  obtain ⟨vs, w, hchain, hlast, hw, hwmax⟩ := exists_lowerHull p hp hdist hleft
  have hgl : (p :: vs).getLast (by simp) = w := by
    obtain ⟨_, hwgl⟩ := List.mem_getLast?_eq_getLast hlast
    exact hwgl.symm
  refine ⟨vs, w, hchain, hlast, hw, hwmax,
    edgeSlopes_pairwise_le hchain, edgeWidths_pos hchain, ?_⟩
  rw [sum_edgeWidths, hgl]

/-- The worked example `Y² − x`: the complete Newton polygon from the leftmost vertex
`(0,1)` exists with sorted slopes, positive widths, and widths summing to the index
span — the single combinatorial Newton polygon of the support `{(0,1), (2,0)}`. -/
theorem ysqMinusX_newtonPolygon :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge YsqMinusX) ((0, 1) :: vs) ∧
      ((0, 1) :: vs).getLast? = some w ∧ w ∈ YsqMinusX ∧ (∀ r ∈ YsqMinusX, r.1 ≤ w.1) ∧
      (edgeSlopes ((0, 1) :: vs)).Pairwise (· ≤ ·) ∧
      (∀ z ∈ edgeWidths ((0, 1) :: vs), 0 < z) ∧
      (edgeWidths ((0, 1) :: vs)).sum = (w.1 : ℚ) - (0 : ℚ) :=
  exists_lowerHull_newtonPolygon (0, 1) (by simp [YsqMinusX])
    (by intro a ha b hb hab; fin_cases ha <;> fin_cases hb <;> simp_all)
    (by intro q hq hne; fin_cases hq <;> simp_all)

/-! ### The third invariant on the concrete hull: valuation of the root product

The capstone `exists_lowerHull_newtonPolygon` bundles the *valuation* half (sorted edge
slopes) and the *multiplicity* half (positive widths summing to the index span) on the
recursion-built hull.  It omits the third Newton-polygon bookkeeping identity — the
slope-weighted-by-width drop `Σ (valuationᵢ · multiplicityᵢ) = v(constant) − v(leading)`
(`neg_sum_slope_mul_width`) — which until now lived only on an *abstract* chain
hypothesis, never on the chain the algorithm actually walks.  The corollary below lands
it on the concrete hull, so all three combinatorial invariants of the Newton polygon now
hold of the same object. -/

/-- **Valuation of the root product, on the concrete recursion-built hull.**  For a
distinct-index support with strictly-leftmost vertex `p`, the hull chain produced by
`exists_lowerHull` satisfies the third Newton-polygon invariant: the sum of root
valuations counted with multiplicity equals the vertical drop between the leftmost and
rightmost vertices, `−Σ (valuationᵢ · multiplicityᵢ) = p.2 − w.2 = v(constant) −
v(leading)`.  Combined with `exists_lowerHull_newtonPolygon` (sorted slopes + total
multiplicity) this puts *all three* combinatorial Newton-polygon invariants on one chain. -/
theorem exists_lowerHull_valuationProduct {pts : List SupportPoint} (p : SupportPoint)
    (hp : p ∈ pts)
    (hdist : ∀ a ∈ pts, ∀ b ∈ pts, a.1 = b.1 → a = b)
    (hleft : ∀ q ∈ pts, q ≠ p → p.1 < q.1) :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge pts) (p :: vs) ∧
      (p :: vs).getLast? = some w ∧ w ∈ pts ∧ (∀ r ∈ pts, r.1 ≤ w.1) ∧
      -(List.zipWith (· * ·) (edgeSlopes (p :: vs)) (edgeWidths (p :: vs))).sum
        = p.2 - w.2 := by
  obtain ⟨vs, w, hchain, hlast, hw, hwmax⟩ := exists_lowerHull p hp hdist hleft
  have hgl : (p :: vs).getLast (by simp) = w := by
    obtain ⟨_, hwgl⟩ := List.mem_getLast?_eq_getLast hlast
    exact hwgl.symm
  refine ⟨vs, w, hchain, hlast, hw, hwmax, ?_⟩
  rw [neg_sum_slope_mul_width hchain, hgl]

/-- `Y² − x`: the valuation of the root product read straight off the hull endpoints.
`−Σ (valuationᵢ · multiplicityᵢ) = 1 − 0 = 1` — the constant coefficient `(0,1)` sits one
unit above the leading coefficient `(2,0)`, so the single root has valuation `½` with
multiplicity `2`, total `1`. -/
theorem ysqMinusX_valuationProduct :
    ∃ (vs : List SupportPoint) (w : SupportPoint),
      List.IsChain (IsLowerEdge YsqMinusX) ((0, 1) :: vs) ∧
      ((0, 1) :: vs).getLast? = some w ∧ w ∈ YsqMinusX ∧ (∀ r ∈ YsqMinusX, r.1 ≤ w.1) ∧
      -(List.zipWith (· * ·) (edgeSlopes ((0, 1) :: vs)) (edgeWidths ((0, 1) :: vs))).sum
        = (1 : ℚ) - w.2 :=
  exists_lowerHull_valuationProduct (0, 1) (by simp [YsqMinusX])
    (by intro a ha b hb hab; fin_cases ha <;> fin_cases hb <;> simp_all)
    (by intro q hq hne; fin_cases hq <;> simp_all)

/-! ## The analytic-bridge brick: a ℚ-valued Puiseux valuation realizing the slopes

The combinatorial sections above compute Newton-polygon **edge slopes** as rational
numbers (e.g. slope `½` for `Y² − x`).  The standing blocker recorded for this slug was
that the *analytic* side — actual roots of `P ∈ K⸨x⸩[Y]` living in a ramified extension,
with a **ℚ-valued** valuation matching those slopes — was thought unstatable in Mathlib
4.26.0, whose Laurent-series valuation `Valued.v` is only `ℤᵐ⁰`-valued on the *unramified*
base.

That blocker is partly mis-stated: Mathlib's `HahnSeries.addVal Γ R : AddValuation R⟦Γ⟧
(WithTop Γ)` is defined for **any** linearly ordered `Γ`, in particular `Γ = ℚ`.  Taking the
Puiseux field to be `HahnSeries ℚ K` (Hahn series with rational exponents) therefore gives a
genuinely **ℚ-valued** additive valuation `x^q ↦ q` directly from Mathlib.  We record the
primitive and the worked `Y² − x` instance: the element `t = x^{1/2}` is an honest member of
the Puiseux field, satisfies `t² = x`, and has valuation `½` — the ramified root valuation
the polygon edge slope predicts.

What is *not* yet built (the genuinely >1000-line part still open) is the ramified embedding
`K⸨x⸩ ↪ HahnSeries ℚ K` and the general correspondence `edgeSlope = −v(root)` for an arbitrary
polynomial; this brick supplies only the valued target field and the single ramified root. -/

variable {K : Type*} [Field K]

/-- The **Puiseux field** over `K`: Hahn series with rational exponents.  Its additive
valuation `HahnSeries.addVal ℚ K` is `ℚ`-valued (codomain `WithTop ℚ`), unlike the
`ℤᵐ⁰`-valued valuation on the unramified Laurent base `K⸨x⸩`. -/
abbrev PuiseuxSeries (K : Type*) [Field K] := HahnSeries ℚ K

/-- The ramified monomial `x^q` (`q ∈ ℚ`) as a Puiseux series. -/
noncomputable def puiseuxMonomial (q : ℚ) : HahnSeries ℚ K := HahnSeries.single q 1

/-- **The ℚ-valued valuation reads off the exponent:** `v(x^q) = q`. -/
theorem puiseuxVal_monomial (q : ℚ) :
    HahnSeries.addVal ℚ K (puiseuxMonomial (K := K) q) = (q : WithTop ℚ) := by
  rw [puiseuxMonomial, HahnSeries.addVal_apply, HahnSeries.orderTop_single one_ne_zero]

/-- The ramified root `x^{1/2}` squares to the base monomial `x = x^1`. -/
theorem sqrt_x_sq :
    (puiseuxMonomial (K := K) (1 / 2)) ^ 2 = puiseuxMonomial (K := K) 1 := by
  simp only [puiseuxMonomial, HahnSeries.single_pow]
  norm_num

/-- **Analytic-bridge brick for `Y² − x`.**  In the Puiseux field `HahnSeries ℚ K` the
element `t = x^{1/2}` is a genuine root of `Y² − x` (`t² = x`) and carries rational valuation
`v(t) = ½` — exactly the Newton-polygon edge slope `ysqMinusX_valuationProduct` computes
combinatorially.  This realizes, for this instance, the slope ↔ root-valuation correspondence
the combinatorial side could previously only assert abstractly. -/
theorem ysqMinusX_root_valuation :
    (puiseuxMonomial (K := K) (1 / 2)) ^ 2 = puiseuxMonomial (K := K) 1 ∧
      HahnSeries.addVal ℚ K (puiseuxMonomial (K := K) (1 / 2)) = ((1 / 2 : ℚ) : WithTop ℚ) :=
  ⟨sqrt_x_sq, puiseuxVal_monomial (1 / 2)⟩

/-- The Puiseux valuation genuinely takes the **non-integer** value `½`, so it cannot factor
through the `ℤ`-valued Laurent valuation on the unramified base — the ramification is real. -/
theorem puiseuxVal_not_integer :
    HahnSeries.addVal ℚ K (puiseuxMonomial (K := K) (1 / 2)) = ((1 / 2 : ℚ) : WithTop ℚ) ∧
      ¬ ∃ n : ℤ, ((1 / 2 : ℚ)) = (n : ℚ) := by
  refine ⟨puiseuxVal_monomial (1 / 2), ?_⟩
  rintro ⟨n, hn⟩
  have hcast : ((2 * n : ℤ) : ℚ) = ((1 : ℤ) : ℚ) := by push_cast; linarith [hn]
  have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast hcast
  omega

/-! ### The full ramified-root family and the ℚ value group

The `Y² − x` brick above realizes a *single* ramified root (`x^{1/2}`, ramification index 2).
The monomial calculus `HahnSeries.single` enjoys (`single_pow`, `single_mul_single`) lets us
state the whole picture at once: every ramification index occurs, and the value group is all
of `ℚ`. All results stay **0 sorry / 0 axiom**. -/

/-- A Puiseux monomial raised to a natural power scales its exponent: `(x^q)ⁿ = x^{n·q}`. -/
theorem puiseuxMonomial_pow (q : ℚ) (n : ℕ) :
    (puiseuxMonomial (K := K) q) ^ n = puiseuxMonomial (K := K) (n • q) := by
  simp only [puiseuxMonomial, HahnSeries.single_pow, one_pow]

/-- Puiseux monomials multiply by adding exponents: `x^p · x^q = x^{p+q}` — so `q ↦ x^q` is a
monoid hom `(ℚ, +) → (PuiseuxSeries K, ·)`, exhibiting `ℚ` inside the multiplicative monomials. -/
theorem puiseuxMonomial_mul (p q : ℚ) :
    puiseuxMonomial (K := K) p * puiseuxMonomial (K := K) q
      = puiseuxMonomial (K := K) (p + q) := by
  simp only [puiseuxMonomial, HahnSeries.single_mul_single, one_mul]

/-- **Every ramification index is realized.** For each `n ≥ 1` the monomial `x^{1/n}` is an
`n`-th root of the base `x = x^1`, generalizing the `n = 2` case `sqrt_x_sq`. -/
theorem nthRoot_x (n : ℕ) (hn : 0 < n) :
    (puiseuxMonomial (K := K) (1 / n)) ^ n = puiseuxMonomial (K := K) 1 := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [puiseuxMonomial_pow]
  congr 1
  rw [nsmul_eq_mul, mul_one_div, div_self hn']

/-- The `n`-th ramified root carries valuation `1/n`. -/
theorem nthRoot_valuation (n : ℕ) :
    HahnSeries.addVal ℚ K (puiseuxMonomial (K := K) (1 / n)) = ((1 / n : ℚ) : WithTop ℚ) :=
  puiseuxVal_monomial (1 / n)

/-- **The full ramified-root family.** For every `n ≥ 1` there is a Puiseux element `t` with
`tⁿ = x` and `v(t) = 1/n`.  The `n = 2` instance is `ysqMinusX_root_valuation`; the family
shows every ramification index `n` is attained in `HahnSeries ℚ K`. -/
theorem exists_nthRoot_of_x (n : ℕ) (hn : 0 < n) :
    ∃ t : PuiseuxSeries K,
      t ^ n = puiseuxMonomial (K := K) 1 ∧
      HahnSeries.addVal ℚ K t = ((1 / n : ℚ) : WithTop ℚ) :=
  ⟨puiseuxMonomial (1 / n), nthRoot_x n hn, nthRoot_valuation n⟩

/-- **The value group is all of `ℚ`.** For every rational `q` the monomial `x^q` has valuation
exactly `q`.  This is the precise sense in which the Puiseux field is *fully ramified* over the
Laurent base `K⸨x⸩`: its value group is `ℚ`, whereas `K⸨x⸩` has value group `ℤ`
(cf. `puiseuxVal_not_integer`, a single witness of a non-integer value). -/
theorem puiseuxVal_surjective (q : ℚ) :
    ∃ t : PuiseuxSeries K, HahnSeries.addVal ℚ K t = (q : WithTop ℚ) :=
  ⟨puiseuxMonomial q, puiseuxVal_monomial q⟩

/-! ### The unramified base inclusion `K⸨x⸩ ↪ PuiseuxSeries K`

The Laurent field `K⸨x⸩ = HahnSeries ℤ K` includes into the Puiseux field
`PuiseuxSeries K = HahnSeries ℚ K` through the order embedding `ℤ ↪ ℚ` of value groups.
This is the **unramified, degree-1 brick** of the open ramified embedding
`K⸨x⸩ ↪ HahnSeries ℚ K`: it realises the Laurent series concretely inside the Puiseux
field as exactly the elements of *integer* valuation, leaving the genuinely fractional
ramification (e.g. `x^{1/2}`) outside the image. -/

/-- The unramified base inclusion `K⸨x⸩ = HahnSeries ℤ K ↪ PuiseuxSeries K`, the ring
homomorphism induced by the order embedding `ℤ ↪ ℚ` on value groups.  It sends the Laurent
monomial `xᵐ` to the Puiseux monomial `x^m` with the same (now ℚ-valued) exponent. -/
noncomputable def laurentToPuiseux : HahnSeries ℤ K →+* PuiseuxSeries K :=
  HahnSeries.embDomainRingHom (Int.castAddHom ℚ) Int.cast_injective (fun _ _ => Int.cast_le)

/-- `laurentToPuiseux` sends the Laurent monomial `single m r = r·xᵐ` to the Puiseux
monomial `single (m:ℚ) r = r·x^m`. -/
@[simp] theorem laurentToPuiseux_single (m : ℤ) (r : K) :
    laurentToPuiseux (HahnSeries.single m r) = HahnSeries.single (m : ℚ) r := by
  rw [laurentToPuiseux, HahnSeries.embDomainRingHom_apply, HahnSeries.embDomain_single]
  rfl

/-- The base inclusion is injective: `K⸨x⸩` embeds faithfully in the Puiseux field. -/
theorem laurentToPuiseux_injective :
    Function.Injective (laurentToPuiseux : HahnSeries ℤ K → PuiseuxSeries K) := by
  rw [laurentToPuiseux]; exact HahnSeries.embDomain_injective

/-- **The inclusion preserves the valuation**, mapping the ℤ-valued Laurent valuation to its
image in `WithTop ℚ`: `v_ℚ(image z) = (v_ℤ z) cast into ℚ`.  Hence every element of the
image has *integer* valuation. -/
theorem laurentToPuiseux_addVal (z : HahnSeries ℤ K) :
    HahnSeries.addVal ℚ K (laurentToPuiseux z)
      = WithTop.map (Int.cast : ℤ → ℚ) (HahnSeries.addVal ℤ K z) := by
  rw [HahnSeries.addVal_apply, HahnSeries.addVal_apply, laurentToPuiseux,
    HahnSeries.embDomainRingHom_apply, HahnSeries.orderTop_embDomain]
  rfl

/-- The Laurent generator `x` maps to the Puiseux generator `x¹`. -/
@[simp] theorem laurentToPuiseux_x :
    laurentToPuiseux (HahnSeries.single (1 : ℤ) (1 : K)) = puiseuxMonomial (K := K) 1 := by
  rw [laurentToPuiseux_single, puiseuxMonomial]; norm_num

/-- **Ramification lives strictly outside the unramified image.**  The half-power `x^{1/2}`
(valuation `½`) is *not* in the range of `laurentToPuiseux`: every image has an **integer**
valuation, but `v(x^{1/2}) = ½ ∉ ℤ`.  This is the structural witness that the Puiseux field
genuinely extends `K⸨x⸩` with fractional ramification — the converse companion to
`puiseuxVal_surjective` (value group `= ℚ`) and `puiseuxVal_not_integer`. -/
theorem puiseuxMonomial_half_not_in_range :
    ¬ ∃ z : HahnSeries ℤ K, laurentToPuiseux z = puiseuxMonomial (K := K) (1 / 2) := by
  rintro ⟨z, hz⟩
  have hval := laurentToPuiseux_addVal z
  rw [hz, puiseuxVal_monomial] at hval
  obtain hz0 | hzne := eq_or_ne (HahnSeries.addVal ℤ K z) ⊤
  · rw [hz0] at hval; simp at hval
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hzne
    rw [← hm, WithTop.map_coe, WithTop.coe_eq_coe] at hval
    -- hval : (1 : ℚ)/2 = ↑m, impossible since no integer equals 1/2
    have hcast : (m : ℚ) * 2 = 1 := by rw [← hval]; norm_num
    have hint : (m * 2 : ℤ) = 1 := by exact_mod_cast hcast
    omega

#print axioms exists_nthRoot_of_x
#print axioms puiseuxVal_surjective
#print axioms laurentToPuiseux_addVal
#print axioms puiseuxMonomial_half_not_in_range

/-! ### The single-edge (binomial) bridge: `edgeSlope = −v(root)` as a family

`ysqMinusX_root_valuation` realizes the slope ↔ root-valuation correspondence for the
*single* polynomial `Y² − x`.  For a **binomial** `Yⁿ − x^a` — support `{(0,a), (n,0)}`, a
single Newton edge — the correspondence holds as an *unbounded parametric family*: the edge
from `(0,a)` to `(n,0)` has slope `−a/n`, and the Puiseux element `t = x^{a/n}` is a genuine
root (`tⁿ = x^a`) carrying valuation `a/n = −edgeSlope`.  This is the first realization of
`edgeSlope = −v(root)` for a whole family rather than one instance; the general multi-edge
bridge (arbitrary `P ∈ K⸨x⸩[Y]`) stays open, blocked on the ramified embedding. -/

/-- The single Newton edge of the binomial `Yⁿ − x^a` (support `{(0,a),(n,0)}`) has slope
`−a/n`.  General in both the ramification index `n` and the constant valuation `a`. -/
theorem binomial_edgeSlope (n : ℕ) (a : ℚ) :
    edgeSlope ((0 : ℕ), a) ((n : ℕ), (0 : ℚ)) = -a / n := by
  simp [edgeSlope]

/-- The Puiseux element `x^{a/n}` is a genuine root of `Yⁿ − x^a`: raising it to the `n`-th
power recovers the base monomial `x^a`.  Generalizes `sqrt_x_sq` (`n = 2, a = 1`) to the
whole binomial family. -/
theorem binomial_root (n : ℕ) (a : ℚ) (hn : 0 < n) :
    (puiseuxMonomial (K := K) (a / n)) ^ n = puiseuxMonomial (K := K) a := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [puiseuxMonomial_pow]
  congr 1
  rw [nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn']

/-- The binomial root `x^{a/n}` carries valuation `a/n`. -/
theorem binomial_root_valuation (n : ℕ) (a : ℚ) :
    HahnSeries.addVal ℚ K (puiseuxMonomial (K := K) (a / n)) = ((a / n : ℚ) : WithTop ℚ) :=
  puiseuxVal_monomial (a / n)

/-- **`edgeSlope = −v(root)` for the whole binomial family.**  For every ramification index
`n ≥ 1` and every constant valuation `a ∈ ℚ`, the binomial `Yⁿ − x^a` has a Puiseux root `t`
(`tⁿ = x^a`) whose valuation `v(t) = a/n` equals the *negated* Newton-polygon edge slope
`−edgeSlope ((0,a),(n,0))`.  This lifts the single `Y² − x` brick to an unbounded family and
is the first statement pinning the combinatorial edge slope to an actual Puiseux root
valuation for anything beyond one instance. -/
theorem binomial_edgeSlope_eq_neg_root_valuation (n : ℕ) (a : ℚ) (hn : 0 < n) :
    ∃ t : PuiseuxSeries K,
      t ^ n = puiseuxMonomial (K := K) a ∧
      HahnSeries.addVal ℚ K t = ((a / n : ℚ) : WithTop ℚ) ∧
      (a / n : ℚ) = -edgeSlope ((0 : ℕ), a) ((n : ℕ), (0 : ℚ)) := by
  refine ⟨puiseuxMonomial (a / n), binomial_root n a hn, binomial_root_valuation n a, ?_⟩
  rw [binomial_edgeSlope n a]; ring

/-- Worked instance `Y³ − x²`: the root `t = x^{2/3}` satisfies `t³ = x²`, has valuation
`2/3`, and `2/3 = −edgeSlope ((0,2),(3,0))`.  A non-`Y²−x` witness of the family bridge. -/
theorem ycubeMinusXsq_root_bridge :
    ∃ t : PuiseuxSeries K,
      t ^ 3 = puiseuxMonomial (K := K) 2 ∧
      HahnSeries.addVal ℚ K t = ((2 / 3 : ℚ) : WithTop ℚ) ∧
      (2 / 3 : ℚ) = -edgeSlope ((0 : ℕ), (2 : ℚ)) ((3 : ℕ), (0 : ℚ)) :=
  binomial_edgeSlope_eq_neg_root_valuation 3 2 (by norm_num)

/-! ### Synthesis: which binomial roots ramify — the two bridges meet

The unramified-inclusion layer (`laurentToPuiseux`, image = integer-valuation elements) and
the binomial-root layer (`x^{a/n}`, valuation `a/n`) intersect on a single question: *when is
a binomial root genuinely ramified — i.e. outside the Laurent base?*  `puiseuxMonomial_half_not_in_range`
answered this for the one point `x^{1/2}`; the two lemmas below answer it for every monomial —
hence for every binomial root — at once. -/

/-- **General ramification criterion.**  A Puiseux monomial `x^q` lies outside the unramified
image `K⸨x⸩ ↪ PuiseuxSeries K` whenever its exponent `q` is not an integer.  This is the exact
generalization of `puiseuxMonomial_half_not_in_range` (the `q = 1/2` instance) from one point
to the whole non-integer locus: the image consists precisely of the integer-valuation
elements, so a non-integer valuation certifies genuine ramification. -/
theorem puiseuxMonomial_not_in_range_of_not_isInt (q : ℚ)
    (hq : ∀ m : ℤ, q ≠ (m : ℚ)) :
    ¬ ∃ z : HahnSeries ℤ K, laurentToPuiseux z = puiseuxMonomial (K := K) q := by
  rintro ⟨z, hz⟩
  have hval := laurentToPuiseux_addVal z
  rw [hz, puiseuxVal_monomial] at hval
  obtain hz0 | hzne := eq_or_ne (HahnSeries.addVal ℤ K z) ⊤
  · rw [hz0] at hval; simp at hval
  · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hzne
    rw [← hm, WithTop.map_coe, WithTop.coe_eq_coe] at hval
    exact hq m hval

/-- **Ramified binomial roots.**  The root `t = x^{a/n}` of the binomial `Yⁿ − x^a` is
genuinely ramified — it is *not* in the Laurent base `K⸨x⸩` — exactly when the exponent `a/n`
is not an integer (equivalently, when the reduced ramification index `n / gcd(a,n) > 1`).  The
integer valuation of the unramified image cannot match the fractional `a/n`.  Specialization
`a = 1, n = 2` recovers `puiseuxMonomial_half_not_in_range`. -/
theorem binomial_root_not_in_range_of_not_isInt (n : ℕ) (a : ℚ)
    (hq : ∀ m : ℤ, a / n ≠ (m : ℚ)) :
    ¬ ∃ z : HahnSeries ℤ K, laurentToPuiseux z = puiseuxMonomial (K := K) (a / n) :=
  puiseuxMonomial_not_in_range_of_not_isInt (a / n) hq

/-- Worked instance: the root `x^{1/3}` of `Y³ − x` is genuinely ramified (`1/3 ∉ ℤ`), so it
lies outside `K⸨x⸩` — a non-`x^{1/2}` witness that the binomial family reaches into the
ramified part of the Puiseux field. -/
theorem cubeRoot_x_not_in_range :
    ¬ ∃ z : HahnSeries ℤ K, laurentToPuiseux z = puiseuxMonomial (K := K) (1 / 3) := by
  have h : ((1 : ℚ) / ((3 : ℕ) : ℚ)) = 1 / 3 := by norm_num
  rw [← h]
  refine binomial_root_not_in_range_of_not_isInt 3 1 (fun m hm => ?_)
  rw [h] at hm
  have hmul : (3 : ℚ) * (m : ℚ) = 1 := by rw [← hm]; ring
  have hint : (3 * m : ℤ) = 1 := by exact_mod_cast hmul
  omega

#print axioms binomial_edgeSlope_eq_neg_root_valuation
#print axioms puiseuxMonomial_not_in_range_of_not_isInt
#print axioms binomial_root_not_in_range_of_not_isInt

/-! ### The `Yⁿ − x` family as honest support lists: `IsLowerEdge` and the leading exponent

The binomial layer above (`binomial_edgeSlope`, `binomial_edgeSlope_eq_neg_root_valuation`)
treats the two support points `(0, a)` and `(n, 0)` in isolation: it computes the slope of the
segment and produces the analytic root, but never exhibits the segment as a **lower edge of an
actual support list** — the combinatorial object the Newton-polygon machinery of this file is
built on.  This section closes that gap for the `Yⁿ − x` family (`n ≥ 1`): the support list
`YnMinusX n = [(0,1), (n,0)]` is defined, its single segment is proven to be a genuine
`IsLowerEdge` (witnessed by the supporting line `y = −(1/n)·i + 1`), the negated slope is
identified with the parent file's `PuiseuxTheorem.leadingExponentFromSlope`, and the capstone
restates `edgeSlope = −v(root)` with the slope read off the *edge of the support list* rather
than a bare pair of points.  The `n = 2` case recovers the original worked example
(`ynMinusX_two`). -/

/-- Support points of `Yⁿ − x`: `(0, 1)` from the constant term `−x` (valuation `1`) and
`(n, 0)` from the leading term `Yⁿ` (valuation `0`).  The intermediate coefficients vanish. -/
def YnMinusX (n : ℕ) : List SupportPoint := [(0, 1), (n, 0)]

/-- For `n = 2` the family specializes to the original worked example `Y² − x`. -/
theorem ynMinusX_two : YnMinusX 2 = YsqMinusX := rfl

/-- The single Newton-polygon edge of `Yⁿ − x` has slope `−1/n` (for every `n`; the formula
holds even at `n = 0`, where both sides are `0` by the `ℚ` convention `−1/0 = 0`).  This is
the `a = 1` instance of `binomial_edgeSlope`, kept in the form matching `YnMinusX`. -/
theorem ynMinusX_edge_slope (n : ℕ) :
    edgeSlope (0, 1) (n, 0) = -1 / (n : ℚ) := by
  simp only [edgeSlope, Nat.cast_zero, sub_zero]
  norm_num

/-- **The Newton polygon recovers the leading exponent of the root.**  The negative of the
edge slope `−1/n` equals the parent's `leadingExponentFromSlope 1 n = 1/n`, the leading
exponent of the ramified root `x^{1/n}` of `Yⁿ − x`.  Generalizes
`ysqMinusX_leading_exponent` from `n = 2` to every `n ≥ 1`. -/
theorem ynMinusX_leading_exponent (n : ℕ) (hn : 0 < n) :
    -edgeSlope (0, 1) (n, 0) = PuiseuxTheorem.leadingExponentFromSlope 1 n hn := by
  rw [ynMinusX_edge_slope n, PuiseuxTheorem.leadingExponentFromSlope]
  push_cast
  ring

/-- The single segment of `Yⁿ − x` is a genuine lower edge for every `n ≥ 1`, witnessed by the
supporting line `y = −(1/n)·i + 1` through both `(0, 1)` and `(n, 0)`.  Generalizes
`ysqMinusX_isLowerEdge`. -/
theorem ynMinusX_isLowerEdge (n : ℕ) (hn : 0 < n) :
    IsLowerEdge (YnMinusX n) (0, 1) (n, 0) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc : (-1 / (n : ℚ)) * (n : ℚ) = -1 := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hn', mul_one]
  refine ⟨by simp [YnMinusX], by simp [YnMinusX], hn, -1 / (n : ℚ), 1, by norm_num, ?_, ?_⟩
  · show (0 : ℚ) = -1 / (n : ℚ) * (n : ℚ) + 1
    rw [hc]; norm_num
  · intro r hr
    fin_cases hr
    · norm_num
    · show -1 / (n : ℚ) * (n : ℚ) + 1 ≤ (0 : ℚ)
      rw [hc]; norm_num

/-- **The slope ↔ root-valuation bridge for `Yⁿ − x`, read off the support list.**  For every
`n ≥ 1` the Puiseux element `t = x^{1/n}` is a genuine root of `Yⁿ − x` (`tⁿ = x`) whose
ℚ-valued valuation equals the **negative of the Newton-polygon edge slope**:
`v(t) = 1/n = −edgeSlope (0,1) (n,0)` — and by `ynMinusX_isLowerEdge` that slope is the slope
of an honest lower edge of `YnMinusX n`, not just of an isolated pair of points.  The
analytic content is the `a = 1` slice of `binomial_edgeSlope_eq_neg_root_valuation`. -/
theorem ynMinusX_slope_eq_root_valuation (n : ℕ) (hn : 0 < n) :
    ∃ t : PuiseuxSeries K,
      t ^ n = puiseuxMonomial (K := K) 1 ∧
      HahnSeries.addVal ℚ K t = ((-edgeSlope (0, 1) (n, 0) : ℚ) : WithTop ℚ) := by
  refine ⟨puiseuxMonomial (1 / n), nthRoot_x n hn, ?_⟩
  rw [nthRoot_valuation, ynMinusX_edge_slope n]
  congr 1
  ring

#print axioms ynMinusX_slope_eq_root_valuation
#print axioms ynMinusX_isLowerEdge

/-! ### The `Yⁿ − xᵐ` family: the general single lower edge as a support list

The `Yⁿ − x` family above pins the *constant* term to `−x` (valuation `1`), so its single
Newton edge always lands on `(0, 1)` and the realized slopes are exactly the unit fractions
`−1/n`.  The genuinely general *single lower edge* allows **both** endpoints to move: a binomial
`Yⁿ − xᵐ` (`n ≥ 1`, `m ≥ 0`) has support `{(0, m), (n, 0)}` and a single edge of slope
`−m/n` — an arbitrary non-positive rational, no longer just a unit fraction.  Its ramified root
is `t = x^{m/n}`, with `tⁿ = xᵐ` and valuation `m/n = −(edge slope)`.

This is the most general two-term Newton polygon, and it is exactly the local model of *one*
lower edge of an arbitrary `P ∈ K⸨x⸩[Y]`: an edge from `(i₀, h)` to `(i₁, 0)` of horizontal
width `w = i₁ − i₀` and height `h` contributes roots of valuation `h/w`, which is the `n = w`,
`m = h` instance here.  The `Yⁿ − x` family is the `m = 1` slice; `Y² − x` is `n = 2, m = 1`.

Relative to the ℚ-exponent binomial layer (`binomial_*`): the analytic statements here are the
`a = m ∈ ℕ` slice, but with `xᵐ` presented as the honest `m`-th power `(x¹)ᵐ` of the base
generator (so the equation `tⁿ = xᵐ` is literally about the polynomial `Yⁿ − xᵐ`), and the
combinatorial statements (`YnMinusXm`, `ynMinusXm_isLowerEdge`, `ynMinusXm_leading_exponent`)
have no `binomial_*` counterpart at all. -/

/-- Support points of `Yⁿ − xᵐ`: `(0, m)` from the constant term `−xᵐ` (valuation `m`) and
`(n, 0)` from the leading term `Yⁿ` (valuation `0`).  The intermediate coefficients vanish. -/
def YnMinusXm (n m : ℕ) : List SupportPoint := [(0, (m : ℚ)), (n, 0)]

/-- For `m = 1` the binomial family specializes to the `Yⁿ − x` family. -/
theorem ynMinusXm_one (n : ℕ) : YnMinusXm n 1 = YnMinusX n := by
  simp [YnMinusXm, YnMinusX]

/-- For `n = 2, m = 1` it specializes to the original worked example `Y² − x`. -/
theorem ynMinusXm_two_one : YnMinusXm 2 1 = YsqMinusX := by
  simp [YnMinusXm, YsqMinusX]

/-- The single Newton-polygon edge of `Yⁿ − xᵐ` has slope `−m/n`.  Unlike the `Yⁿ − x` family
(whose slopes are the unit fractions `−1/n`), letting `m` vary realizes an **arbitrary**
non-positive rational slope. -/
theorem ynMinusXm_edge_slope (n m : ℕ) :
    edgeSlope (0, (m : ℚ)) (n, 0) = -(m : ℚ) / (n : ℚ) := by
  simp only [edgeSlope, Nat.cast_zero, sub_zero, zero_sub]

/-- For `m = 1` the slope `−m/n` recovers the `Yⁿ − x` edge slope `−1/n`. -/
theorem ynMinusXm_edge_slope_one (n : ℕ) :
    edgeSlope (0, ((1 : ℕ) : ℚ)) (n, 0) = -1 / (n : ℚ) := by
  rw [ynMinusXm_edge_slope]; norm_num

/-- **The Newton polygon recovers the leading exponent of the root.**  The negative of the
edge slope `−m/n` equals the parent's `leadingExponentFromSlope m n = m/n`, the leading
exponent of the ramified root `x^{m/n}` of `Yⁿ − xᵐ`.  Generalizes `ynMinusX_leading_exponent`
from `m = 1` to every `m`. -/
theorem ynMinusXm_leading_exponent (n m : ℕ) (hn : 0 < n) :
    -edgeSlope (0, (m : ℚ)) (n, 0) = PuiseuxTheorem.leadingExponentFromSlope m n hn := by
  rw [ynMinusXm_edge_slope, PuiseuxTheorem.leadingExponentFromSlope]
  ring

/-- The single segment of `Yⁿ − xᵐ` is a genuine lower edge for every `n ≥ 1`, witnessed by the
supporting line `y = −(m/n)·i + m` through both `(0, m)` and `(n, 0)`.  Generalizes
`ynMinusX_isLowerEdge`. -/
theorem ynMinusXm_isLowerEdge (n m : ℕ) (hn : 0 < n) :
    IsLowerEdge (YnMinusXm n m) (0, (m : ℚ)) (n, 0) := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hc : (-(m : ℚ) / (n : ℚ)) * (n : ℚ) = -(m : ℚ) := by
    rw [div_mul_eq_mul_div, mul_div_assoc, div_self hn', mul_one]
  refine ⟨by simp [YnMinusXm], by simp [YnMinusXm], hn, -(m : ℚ) / (n : ℚ), (m : ℚ),
    by norm_num, ?_, ?_⟩
  · show (0 : ℚ) = -(m : ℚ) / (n : ℚ) * (n : ℚ) + (m : ℚ)
    rw [hc]; ring
  · intro r hr
    fin_cases hr
    · norm_num
    · show -(m : ℚ) / (n : ℚ) * (n : ℚ) + (m : ℚ) ≤ (0 : ℚ)
      rw [hc]; linarith

/-- The Puiseux element `x^{m/n}` is an `n`-th root of `xᵐ`: `(x^{m/n})ⁿ = xᵐ`, with `xᵐ`
presented as the `m`-th power of the base generator `x¹`.  Generalizes `nthRoot_x` (the
`m = 1` case `(x^{1/n})ⁿ = x`); the collapsed-monomial form is `binomial_root n m`. -/
theorem nthRoot_xm (n m : ℕ) (hn : 0 < n) :
    (puiseuxMonomial (K := K) ((m : ℚ) / (n : ℚ))) ^ n
      = (puiseuxMonomial (K := K) 1) ^ m := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [puiseuxMonomial_pow, puiseuxMonomial_pow]
  congr 1
  rw [nsmul_eq_mul, mul_comm, div_mul_cancel₀ _ hn', nsmul_eq_mul, mul_one]

/-- The root `x^{m/n}` of `Yⁿ − xᵐ` carries valuation `m/n`. -/
theorem nthRoot_xm_valuation (n m : ℕ) :
    HahnSeries.addVal ℚ K (puiseuxMonomial (K := K) ((m : ℚ) / (n : ℚ)))
      = (((m : ℚ) / (n : ℚ)) : WithTop ℚ) :=
  puiseuxVal_monomial ((m : ℚ) / (n : ℚ))

/-- **The general slope ↔ root-valuation bridge for `Yⁿ − xᵐ`.**  For every `n ≥ 1` and every
`m` the Puiseux element `t = x^{m/n}` is a genuine root of `Yⁿ − xᵐ` (`tⁿ = xᵐ`, the
right-hand side an honest `m`-th power) whose ℚ-valued valuation equals the **negative of the
Newton-polygon edge slope**: `v(t) = m/n = −edgeSlope (0, m) (n, 0)` — the slope of the lower
edge exhibited by `ynMinusXm_isLowerEdge`.  This is the correspondence `edgeSlope = −v(root)`
for the most general *two-term* Newton polygon — an arbitrary single lower edge with both
endpoints free.  The `m = 1` instance recovers `ynMinusX_slope_eq_root_valuation`. -/
theorem ynMinusXm_slope_eq_root_valuation (n m : ℕ) (hn : 0 < n) :
    ∃ t : PuiseuxSeries K,
      t ^ n = (puiseuxMonomial (K := K) 1) ^ m ∧
      HahnSeries.addVal ℚ K t = ((-edgeSlope (0, (m : ℚ)) (n, 0) : ℚ) : WithTop ℚ) := by
  refine ⟨puiseuxMonomial ((m : ℚ) / (n : ℚ)), nthRoot_xm n m hn, ?_⟩
  rw [nthRoot_xm_valuation, ynMinusXm_edge_slope]
  congr 1
  ring

/-- **A non-unit-fraction valuation, realized.**  `Y³ − x²` has Newton slope `−2/3`, and its
ramified root `x^{2/3}` carries valuation `2/3` — a value the entire `Yⁿ − x` family can
never attain (its valuations are exactly the unit fractions `1/n`).  Concrete witness that the
two-parameter family `Yⁿ − xᵐ` genuinely enlarges the realized value set; the
collapsed-monomial form of this instance is `ycubeMinusXsq_root_bridge`. -/
theorem y3MinusX2_root_valuation :
    ∃ t : PuiseuxSeries K,
      t ^ 3 = (puiseuxMonomial (K := K) 1) ^ 2 ∧
      HahnSeries.addVal ℚ K t = ((2 / 3 : ℚ) : WithTop ℚ) := by
  obtain ⟨t, ht, hv⟩ := ynMinusXm_slope_eq_root_valuation (K := K) 3 2 (by norm_num)
  refine ⟨t, ht, ?_⟩
  rw [hv, ynMinusXm_edge_slope]
  norm_num

#print axioms ynMinusXm_slope_eq_root_valuation
#print axioms ynMinusXm_isLowerEdge
#print axioms nthRoot_xm
#print axioms y3MinusX2_root_valuation

end PuiseuxTheoremOQ03
