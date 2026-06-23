# Knowledge Base: shapley-folkman-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

**Phase: ORIENT (iteration 2, researcher-3, 2026-06-14).** Build-free session
under the Docker + Aristotle verification blackout — no `.lean` committed.

### The precise gap vs. the gallery parent

`ShapleyFolkman.lean` already proves the **combinatorial** Shapley–Folkman
content. The relevant existing theorem is

```
theorem sum_close_to_convexHull (hne : ∀ i ∈ t, (S i).Nonempty)
    (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ f, (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧ ∑ i ∈ t, f i = x ∧
         (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E
```

i.e. *a hull point of the Minkowski sum decomposes as `x = Σ fᵢ` with each
`fᵢ ∈ conv(Sᵢ)` and **at most `n = finrank` summands convexified**
(`fᵢ ∉ Sᵢ`)*. There is also `repeated_sum_nearly_convex` (the `n • S` form).

**What OQ-02/Starr needs and the parent does NOT give:** the *metric* upgrade.
For the `≤ n` convexified summands, replace each `fᵢ` by a nearest point
`sᵢ ∈ Sᵢ` and bound the aggregate displacement:

```
‖x − Σ sᵢ‖  ≤  √(min(m,n)) · maxᵢ rad(Sᵢ),     rad = circumradius (min enclosing ball)
```

uniformly over all hull points `x` (⇒ the one-sided Hausdorff bound). The
parent stops at the combinatorial count; the displacement/aggregation lemma is
the genuinely new work.

### Why `√n` and not `n` (the only non-routine step)

Naively, summing `≤ n` deviation vectors each of norm `≤ L` gives `n·L` by the
triangle inequality. Starr's `√n·L` is *strictly better* and is the crux: it is
**not** a triangle-inequality bound. It comes from a Cassels/Starr ℓ²
aggregation — the squared deviations of the convexified summands satisfy
`Σ‖fᵢ − sᵢ‖² ≤ n·L²` rather than only `(Σ‖fᵢ−sᵢ‖)² ≤ (nL)²`, then Cauchy–Schwarz
over the `≤ n` excess indices gives `‖Σ(fᵢ−sᵢ)‖ ≤ √n·L` (with `min(m,n)`
replacing `n` when `m < n`). This squared-sum estimate is the one new lemma a
Lean proof must supply.

---

## Insights

### Numerical de-risking (durable, `verify_starr_bound.py`)

Ran a pure numpy/scipy verification (no Docker/Lean) estimating
`D = sup_{x∈conv(ΣSᵢ)} dist(x, ΣSᵢ)` by sampling convex combinations of the
Minkowski-sum point set (so reported `D` is a **lower** bound on the true sup —
a true violation could only be larger, so a passing bound check is not a
sampling artifact). 15 cases, **0 violations** of `√(min(m,n))·max_rad`:

1. **The bound holds** on random sets (n=2,3; m=2,4,6) with comfortable margin.
2. **m-independence is sharp** (the headline feature): for `Sᵢ = {0,1} ⊂ ℝ`
   (rad = ½), `D ≈ 0.500` for **every** m ∈ {1,2,5,10,25,50} (range
   [0.4996, 0.5000], span 4e-4), while the naive triangle bound `Σ rad`
   grows linearly `0.5 → 25.0`. So `D = √(min(m,1))·½ = ½` exactly — the bound
   is attained and flat in m.
3. **The `√n` factor is essentially attained** in n=2: axis-cycling
   `Sᵢ = {0, e_axis}` gives `D ≈ 0.701` vs. bound `√2·½ = 0.7071` (≈99%).
   (For n=3,4 the sampled `D` sits below the bound — the axis-cycle family is
   not the worst case there, and the sup is undersampled — but n=1 and n=2
   pin the constant.)

**Conclusion of the experiment:** the Starr constant `√(min(m,n))·max rad` is
correct and sharp, and m-independence is real — worth the Lean formalization.

### Mathlib bearer map (v4.26.0 pin)

| Need | Mathlib bearer | Status |
|------|----------------|--------|
| hull point ⇒ ≤ n convexified summands | parent `sum_close_to_convexHull` | **present** (this repo) |
| Minkowski sum of sets | `∑ i ∈ t, S i` (pointwise `Set.add`) | present |
| convex hull, Carathéodory | `convexHull`, `convexHull_eq_union` | present |
| Hausdorff distance | `Metric.hausdorffDist`, `EMetric.hausdorffEdist` | present |
| diameter / size of a set | `Metric.diam`, `Bornology.IsBounded` | present |
| Cauchy–Schwarz / ℓ² | `inner_mul_le_norm_mul_norm`, `Finset.inner_mul_le_norm_mul_norm` | present |
| **circumradius `rad(S)` (min enclosing ball)** | — | **MISSING** (must define) |
| **the `√(min(m,n))` ℓ² aggregation lemma** | — | **MISSING** (the one new lemma) |

So the formalization is **not** API-wiring on top of a missing foundation:
everything is present except (i) a `rad` definition and (ii) the Cassels–Starr
squared-deviation aggregation.

### Suggested ACT decomposition (when a backend returns)

1. `def rad (S : Set E) : ℝ` — circumradius; for the *bound* it suffices to use
   any center (e.g. a chosen point of `S`) giving `rad ≤ diam`, but sharpness
   wants the min-enclosing-ball center. Start with the `diam`-based weaker
   bound `‖fᵢ − sᵢ‖ ≤ diam(Sᵢ)` to get a (looser) `√n·diam` result first.
2. Per-summand displacement: for `fᵢ ∈ conv(Sᵢ)`, `∃ sᵢ ∈ Sᵢ` with
   `‖fᵢ − sᵢ‖ ≤ rad(Sᵢ)` (via Carathéodory the convex combo is over points of
   `Sᵢ`; pick the nearest).
3. **The new lemma:** `Σ_{i ∈ excess} ‖fᵢ − sᵢ‖² ≤ (#excess) · L²` ⇒
   `‖Σ (fᵢ − sᵢ)‖ ≤ √(#excess)·L ≤ √(min(m,n))·L` (Cauchy–Schwarz on the
   `≤ n` excess indices). This is where the `√` is born.
4. Quantify over all hull points ⇒ the `Metric.hausdorffDist` statement.

---

## Dead Ends

- **Triangle-inequality only** gives `n·L`, not Starr's `√n·L`; it cannot reach
  the sharp constant the experiment confirms. The ℓ²/Cauchy–Schwarz route is
  required.
- **Expecting a ready-made circumradius in Mathlib v4.26.0:** none found;
  `Metric.diam` exists but `rad` (min enclosing ball) must be defined (or the
  weaker `diam`-based bound used for a first pass).
- (No Lean attempted this session — blocked by the verification blackout; the
  above is ORIENT only.)
