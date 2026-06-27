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

/-! ### The Newton polygon is a graph over the index axis

The vertex predicate identifies corners by a supporting line, so *a priori* two
distinct support points could both qualify as vertices.  The lemmas here show
this never happens at a shared index.  A lower vertex's valuation is the
**minimum** over all support points sharing its index
(`IsLowerVertex.le_of_sameIndex`): the supporting line, evaluated at the common
index, sits at the vertex and weakly below every competitor.  Consequently at
most one support point per index can be a vertex (`IsLowerVertex.eq_of_index`),
so the lower hull is the graph of a well-defined function `i ↦ v`.  This is the
combinatorial content of "*the* Newton polygon" being a single polygonal arc
rather than an arbitrary point set, and it is what lets the Newton–Puiseux
algorithm collapse each index-fiber to its lowest point before tracing edges. -/

/-- **A lower vertex is lowest in its index-fiber.**  If `p` is a lower vertex and
`q` is any support point with the same index `p.1 = q.1`, then `p.2 ≤ q.2`.  The
supporting line through `p` agrees with `p` at that index and lies weakly below
`q`, so `p` cannot be beaten there. -/
theorem IsLowerVertex.le_of_sameIndex {pts : List SupportPoint} {p q : SupportPoint}
    (hp : IsLowerVertex pts p) (hq : q ∈ pts) (hidx : p.1 = q.1) : p.2 ≤ q.2 := by
  obtain ⟨_, m, b, hpe, hsup⟩ := hp
  have h := hsup q hq
  rw [← hidx] at h
  linarith [hpe, h]

/-- **Index-uniqueness of vertices.**  Two lower vertices with the same index are
equal.  Together with `le_of_sameIndex` this says the lower hull is the graph of
a function of the index: each `Y`-degree contributes at most one polygon vertex,
namely the support point of least valuation there. -/
theorem IsLowerVertex.eq_of_index {pts : List SupportPoint} {p q : SupportPoint}
    (hp : IsLowerVertex pts p) (hq : IsLowerVertex pts q) (hidx : p.1 = q.1) :
    p = q := by
  have h1 : p.2 ≤ q.2 := hp.le_of_sameIndex hq.mem hidx
  have h2 : q.2 ≤ p.2 := hq.le_of_sameIndex hp.mem hidx.symm
  exact Prod.ext_iff.mpr ⟨hidx, le_antisymm h1 h2⟩

/-- A support point that is **not lowest at its index** is not a lower vertex.
Augmenting `Y² − x`'s support with a spurious high point `(0, 5)` directly above
the constant term: `(0, 5)` fails to be a vertex because the genuine vertex
`(0, 1)` sits below it at the same index `0`. -/
theorem ysqMinusX_high_not_vertex :
    ¬ IsLowerVertex [(0, 1), (2, 0), (0, 5)] (0, 5) := by
  intro h
  have hle : (5 : ℚ) ≤ 1 := h.le_of_sameIndex (q := (0, 1)) (by simp) rfl
  norm_num at hle

end PuiseuxTheoremOQ03
