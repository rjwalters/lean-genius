# Knowledge Base: shapley-folkman

Insights accumulated during research on this problem.

---

## Problem Understanding

The Shapley-Folkman Lemma states: any point in the convex hull of a Minkowski sum
of N sets in ℝ^d can be decomposed so that at most d summands come from convex hulls
rather than the original sets.

Current status: `shapley_folkman`, `sum_close_to_convexHull`, `repeated_sum_nearly_convex`
all proved (0 sorries). Only `reduce_excess_by_one` remains.

---

## Session 2026-04-13 (Session 2) — Proof Architecture for reduce_excess_by_one

**Mode**: FRESH
**Outcome**: proof architecture progress — 1 sorry → 2 sorrys + 1 proved sub-step

### What I Did
- Replaced the single sorry in `reduce_excess_by_one` with a full proof structure
- Added `binary_repr_of_mem_convexHull_not_mem` private lemma (with sorry)
- Wrote Steps 1-5 of the perturbation proof with only Step 6 (the construction) remaining sorry
- Step 5 (sign normalization of linear dependence coefficients) is **actually proved**

### Proof Architecture

The proof proceeds as:

1. **Binary reps** (sorry → `binary_repr_of_mem_convexHull_not_mem`):
   For each excess j: `D.point j = s_j • a_j + (1-s_j) • b_j` with
   `a_j ∈ S j`, `b_j ∈ conv(S j)`, `s_j ∈ (0,1)`.
   Construction: take first Carathéodory vertex as `a_j`, renormalized sum of rest as `b_j`.

2. **Embedding** (sorry):
   Extract `emb : Fin(d+1) → ι` with all images in `excessIndices`.
   (Requires finset enumeration API — `orderEmbOfCardLE` needs LinearOrder on ι;
   need alternative like `Finset.exists_subset_card_le` + list enumeration.)

3. **Direction vectors**: `δ_l = bv(emb l) - av(emb l)` — explicit, no sorry.

4. **Linear dependence**: `linearDependent_coefficients` gives `c`, nonzero, `Σ c_l • δ_l = 0` — proved.

5. **Sign normalization** (PROVED):
   Negate c if `c l₀ > 0`. Either way get `c'` with `c' lneg < 0`, `Σ c'_l • δ_l = 0`.
   Key: `∑ -(c l) • δ l = -(∑ c l • δ l) = 0` via `Finset.sum_neg_distrib`.

6. **Perturbation construction** (sorry):
   `ε = min { (1-s_l)/(-c'_l) : c'_l < 0 } ∩ { s_l/c'_l : c'_l > 0 } > 0`
   `point'(emb l) = (s_l - ε·c'_l)·a_l + (1-s_l+ε·c'_l)·b_l`
   At minimizing lmin (with `c'_lmin < 0`): b-weight hits 0 → `point' = a_lmin ∈ S(emb lmin)`
   Sum preserved since `Σ c'_l·δ_l = 0`.

### Key Findings
- Sign normalization (step 5) is provable and IS proved in the file
- `binary_repr` construction: take `a = f 0 ∈ s`, `t = w 0 ∈ (0,1)` (since `n ≥ 2` and weights positive),
  `b = (1-t)^{-1} • Σ_{k≥1} w_k • f_k ∈ conv(s)`. Then `x = t•a + (1-t)•b`.
- Embedding extraction: need `∃ emb : Fin(d+1) → ι, ∀ l, emb l ∈ S` from `S.card ≥ d+1`.
  Mathlib approach: `Finset.exists_subset_card_le` gives a subset J of size d+1, then
  `J.orderIsoOfFin rfl` enumerates J (requires LinearOrder — workaround: use subtype).
- Step 6 D' construction: needs to define modified `point` function, prove convex hull membership,
  sum equality, and count excess decrease. This is the main work remaining.

### Files Modified
- `proofs/Proofs/ShapleyFolkman.lean` (lines 216-300):
  - Added `binary_repr_of_mem_convexHull_not_mem` (1 sorry)
  - Rewrote `reduce_excess_by_one` with 3 sorrys (was 1), steps 3-5 proved

### Next Steps

1. **Prove `binary_repr_of_mem_convexHull_not_mem`**:
   - Use `convexHull_not_mem_requires_two` to get n≥2 points
   - `a = f 0`, `t = w 0`, `b = (1-t)⁻¹ • Σ_{k≥1} w_k • f_k`
   - Need: `b ∈ convexHull s` (convex combo of s-points), `w 0 < 1` (since `w 1 > 0`),
     `x = t•a + (1-t)•b` (algebraic identity after Finset sum manipulation)

2. **Fix embedding extraction** (Step 2):
   - Use `Finset.card_le_iff_exists_subset` to get a subset J of size d+1
   - Then enumerate J via coercion to a Fintype subtype

3. **Prove Step 6 (perturbation construction)**:
   - This is the hard sorry. Needs: min of finite positive set, new Decomposition struct,
     convexHull membership via convex combination argument, sum preservation, excess count

---

## Session 2026-04-12 (Session 1) — Prior progress

**Outcome**: `sum_close_to_convexHull` and `repeated_sum_nearly_convex` proved. Only
`reduce_excess_by_one` remains as a sorry.

### Key Findings (Session 1)
- `reduce_excess_by_one` is the mathematical core
- `linearDependent_coefficients` proved (lines 194-205)
- `shapley_folkman` proved from `reduce_excess_by_one` by induction
- `convexHull_not_mem_requires_two` proved (lines 105-157)

---

## Insights

- `reduce_excess_by_one` proof works by DIRECT excess decrease (not M-induction).
  Key: choose c with a negative entry, then ε makes the b-weight hit 0, collapsing
  the excess index to a_lmin ∈ S j. No induction on vertex count needed.
- `sum_close_to_convexHull` depends on `Set.mem_finset_sum` (Mathlib) and `convexHull_min`.
- Binary representation: general n-point Carathéodory rep → binary rep via first-vertex extraction.

---

## Dead Ends

- "Toward a single point" perturbation: doesn't preserve convex hull membership for negative coefficients
- M-induction (induct on total vertex count): correct but more complex than needed
- Direct proof without binary reps: linearDependent_coefficients needs direction vectors,
  which requires reducing n-point reps to 2-point reps first
