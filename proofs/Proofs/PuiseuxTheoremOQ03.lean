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

/-! ### Newton's valuation relation: width × slope telescopes to the valuation drop

The two preceding sections isolate the two halves of the Newton polygon theorem:
`edgeSlopes` carries the *valuations* of the roots (sorted, by convexity), and
`edgeWidths` carries their *multiplicities* (summing to the `Y`-degree).  This
section multiplies them together.

On an edge from `p` to `q` the polygon contributes `q.1 − p.1` roots (the width),
each of valuation `−edgeSlope p q`.  The valuation those roots contribute to the
total is therefore `(q.1 − p.1) · edgeSlope p q`, which — because the slope is the
rise over the run — is exactly the *vertical drop* `q.2 − p.2`.  Summing across a
vertex chain telescopes to `(last vertex).2 − (first vertex).2`.

Negating gives the classical relation: the sum of the valuations of all roots
(with multiplicity) equals `v(a₀) − v(a_d)`, the valuation of the constant term
minus that of the leading term — i.e. the valuation of `±a₀/a_d`, the product of
the roots.  This is the synthesis the slope-sorting and width-counting results
were each only half of. -/

/-- On a non-degenerate edge the product width × slope is the vertical drop:
`(q.1 − p.1) · edgeSlope p q = q.2 − p.2`.  This is just `edgeSlope`'s definition
(rise over run) cancelled against the run, valid whenever the indices differ. -/
theorem width_mul_edgeSlope {p q : SupportPoint} (h : (p.1 : ℚ) ≠ (q.1 : ℚ)) :
    ((q.1 : ℚ) - (p.1 : ℚ)) * edgeSlope p q = q.2 - p.2 := by
  have hne : (q.1 : ℚ) - (p.1 : ℚ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  rw [edgeSlope, mul_div_cancel₀ _ hne]

/-- The list of per-edge valuation drops along a chain of support points: the
product width × slope `(q.1 − p.1) · edgeSlope p q` of each consecutive pair.
On a genuine vertex chain each entry equals the vertical drop `q.2 − p.2`
(`width_mul_edgeSlope`). -/
def edgeDrops : List SupportPoint → List ℚ
  | p :: q :: rest => ((q.1 : ℚ) - (p.1 : ℚ)) * edgeSlope p q :: edgeDrops (q :: rest)
  | _ => []

/-- **Telescoping valuation identity.**  Along any vertex chain the per-edge
valuation drops (width × slope) sum to the total vertical drop from the first
vertex to the last, `(last).2 − (first).2`.  The chain hypothesis is what makes
each edge non-degenerate (`p.1 < q.1`), so `width_mul_edgeSlope` turns every term
into a genuine drop `q.2 − p.2` and the sum telescopes. -/
theorem sum_edgeDrops {pts : List SupportPoint} :
    ∀ {v : SupportPoint} {vs : List SupportPoint},
      List.IsChain (IsLowerEdge pts) (v :: vs) →
      (edgeDrops (v :: vs)).sum = (((v :: vs).getLast (by simp)).2) - v.2
  | _, [], _ => by simp [edgeDrops]
  | v, w :: ws, hc => by
      obtain ⟨hvw, hc'⟩ := List.isChain_cons_cons.mp hc
      have ih := sum_edgeDrops hc'
      obtain ⟨_, _, hlt, _⟩ := hvw
      have hne : (v.1 : ℚ) ≠ (w.1 : ℚ) := by exact_mod_cast Nat.ne_of_lt hlt
      have hdrop : ((w.1 : ℚ) - (v.1 : ℚ)) * edgeSlope v w = w.2 - v.2 :=
        width_mul_edgeSlope hne
      have hgl : (v :: w :: ws).getLast (by simp) = (w :: ws).getLast (by simp) :=
        List.getLast_cons (by simp)
      simp only [edgeDrops, List.sum_cons]
      rw [ih, hdrop, hgl]
      ring

/-- **Newton's valuation relation.**  The sum of the valuations of all roots
(counted with multiplicity) equals `v(a₀) − v(a_d)`: the valuation of the constant
term minus that of the leading term.  Each edge contributes `width` roots of
valuation `−slope`, so the total root-valuation sum is `−∑ (width · slope)`, which
by `sum_edgeDrops` collapses to `(first).2 − (last).2`.  For a hull running from
index `0` (constant term) to index `d` (leading term) the right-hand side is
`v(a₀) − v(a_d)` — the valuation of the product of the roots. -/
theorem sum_rootValuations {pts : List SupportPoint} {v : SupportPoint}
    {vs : List SupportPoint} (hc : List.IsChain (IsLowerEdge pts) (v :: vs)) :
    -((edgeDrops (v :: vs)).sum) = v.2 - (((v :: vs).getLast (by simp)).2) := by
  rw [sum_edgeDrops hc]
  ring

/-- The per-edge valuation drops of the worked three-vertex example are
`[-2, 1]`: edge `(0,2)→(1,0)` drops by `−2` (width `1`, slope `−2`) and edge
`(1,0)→(3,1)` rises by `1` (width `2`, slope `1/2`). -/
theorem threeVertex_edgeDrops : edgeDrops threeVertex = [-2, 1] := by
  norm_num [edgeDrops, threeVertex, edgeSlope]

/-- The drops of the example telescope to `1 − 2 = −1`, the vertical drop from the
first vertex `(0,2)` to the last `(3,1)`. -/
theorem threeVertex_sum_drops : (edgeDrops threeVertex).sum = -1 := by
  norm_num [edgeDrops, threeVertex, edgeSlope]

/-- The example's root valuations sum to `2 − 1 = 1 = v(a₀) − v(a_d)`: one root of
valuation `2` (from the width-`1` edge) plus two roots of valuation `−1/2` (from
the width-`2` edge) give `2 + 2·(−1/2) = 1`, matching `v(a₀) − v(a_d) = 2 − 1`. -/
theorem threeVertex_sum_rootValuations :
    -((edgeDrops threeVertex).sum) = 1 := by
  norm_num [edgeDrops, threeVertex, edgeSlope]

end PuiseuxTheoremOQ03
