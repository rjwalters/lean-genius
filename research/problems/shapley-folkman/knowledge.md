# Knowledge Base: shapley-folkman

Insights accumulated during research on this problem.

---

## Problem Understanding

The Shapley-Folkman Lemma states: any point in the convex hull of a Minkowski sum
of N sets in ℝ^d can be decomposed so that at most d summands come from convex hulls
rather than the original sets.

Current status: `shapley_folkman`, `sum_close_to_convexHull`, `repeated_sum_nearly_convex`
all proved (0 sorries). `reduce_excess_by_one` has 1 sorry remaining (Step 6 perturbation).

---

## Session 2026-04-21 (Session 6) — Case A Proved in new_mem_convexHull

**Mode**: REVISIT
**Outcome**: Progress — Case A proved; Case B still sorry

### What I Did

- Proved Case A of `new_mem_convexHull` in `ShapleyFolkman.lean`:
  The case where ε₀ (from neg-index bounds) is small enough to satisfy pos-index bounds too.
  Three sub-cases on c'_l via `lt_trichotomy`:
  - `c'_l < 0`: closes via `nlinarith + hε₀_le_neg` (ε₀ ≤ (1-sv_l)/|c'_l|)
  - `c'_l = 0`: point unchanged (c'_l * ε₀ = 0)
  - `c'_l > 0`: closes via `hCaseA + le_div_iff` (ε₀ ≤ (1-sv_l)/c'_l holds by case assumption)
  All convex hull memberships close with `convex_convexHull ℝ (S (emb l))`
- Case B: still sorry'd — requires joint ε = min(ε₀, min over pos_indices)
  and WF descent on Carathéodory vertex count per Starr 1969

### Key Finding: Case Split Sufficiency

The key insight for Case A: the existentially chosen ε₀ from neg-index bounds also satisfies pos-index bounds iff ε₀ ≤ (1-sv_l)/c'_l for all l in pos_indices. This is case assumption hCaseA. When hCaseA fails (Case B), we need a different ε that satisfies ALL bounds simultaneously.

### Sorrys Remaining in ShapleyFolkman.lean
1. `new_mem_convexHull` Case B — WF descent proof needed

### Files Modified
- `proofs/Proofs/ShapleyFolkman.lean`: ~50 lines replacing the old single sorry for Case A

### Next Steps
1. Case B: implement joint ε via `Finset.inf'` over pos and neg index bounds
2. Use WF descent on N = Σ n_j (Carathéodory vertex counts) — termination by vertex count
3. Alternative: submit Case B sorry to Aristotle as HARD

---

## Session 2026-04-13 (Session 4) — Architectural Analysis + Correct Approach Identified

**Mode**: REVISIT
**Outcome**: documented architectural gap, identified correct Starr 1969 approach

### What I Did
- Confirmed the binary approach gap: when ε-minimizer has c'_l > 0, the perturbed point
  equals bv(emb lmin) ∈ convexHull(S) \ S, NOT reducing excess.
- Showed the gap is real: with c'₁ = -1, sv₁ = 0.1, c'₂ = 2, sv₂ = 0.5, bounds are
  A₁ = 0.9 (c' < 0) vs A₂ = 0.25 (c' > 0); minimizer at A₂ < A₁, so lmin has c' > 0.
  Negating c' doesn't help (just swaps which direction hits first).
- Documented the correct approach (Starr 1969 / standard proof): use FULL Carathéodory
  representations (all n_j ≥ 2 vertices in S_j with strict positive weights), pick any
  two vertices z₀, z₁ per excess index, define δ_l = z₁_l - z₀_l (both in S), perturb
  by shifting weight between z₀ and z₁. ε = min over all l of:
    - w₁_l / c_l for c_l > 0 (β-weight reaches 0)
    - w₀_l / (-c_l) for c_l < 0 (α-weight reaches 0)
  At minimizer: one vertex drops to 0 weight. If only 2 vertices, point = remaining vertex ∈ S.
  Use well-founded descent on total vertex count N = Σ n_j.
- Documented full proof sketch in ShapleyFolkman.lean at lines 348-380.

### Sorrys Remaining
1. Step 6 (perturbation with well-founded descent) — ~100-120 lines to implement

### Key Findings
- Binary representation (a ∈ S, b ∈ conv(S)) is insufficient for single-step excess reduction
  unless all d+1 direction vectors happen to have c' < 0 at their minimizer
- Correct proof needs "decorated decomposition" carrying full Carathéodory data per excess index
- Well-founded descent on N = Σ nⱼ terminates: each step removes one vertex (decreases N by 1);
  when some j drops from 2→1 vertex, that index becomes non-excess, decreasing excess count
- The c'>0 / c'<0 case split is handled by choosing ε small enough that the first vertex to
  reach 0 weight determines which direction "wins"
- Implementation requires: `Finset.inf'` for the ε minimum, a WF recursion on N, and
  explicit convex combination construction with adjusted weights

### Files Modified
- `proofs/Proofs/ShapleyFolkman.lean` lines 349-380: expanded architectural comment

### Next Steps
1. Implement Step 6 with decorated decomposition + WF descent:
   - Define `DecoratedDecomp` carrying Carathéodory data (n_j vertices w/ positive weights)
   - Perturbation: shift α/β weights by ε·c, where ε = Finset.inf' of bounds
   - Well-founded descent on N = Σ n_j terminates in finitely many steps
   - When n_j = 1, that point is the single vertex ∈ S_j → non-excess
2. Alternative: submit Step 6 to Aristotle as HARD sorry with mathematical context

---

## Session 2026-04-13 (Session 3) — Embedding Extraction Fixed

**Mode**: REVISIT
**Outcome**: Step 2 proved — embedding extraction via Multiset.toList

### What I Did
- Replaced Step 2 sorry with list-based proof: convert `D.excessIndices.val` to a `List`
  via `Multiset.toList`, then index with `List.get`. Membership follows from
  `Multiset.mem_toList.mp (List.get_mem ...)`.
- Key lemmas: `Multiset.toList_length` (list length = multiset card), `List.get_mem`,
  `Multiset.mem_toList`, `Finset.mem_def`

### Sorrys Remaining
1. Step 6 (perturbation construction) — the only remaining sorry

### Files Modified
- `proofs/Proofs/ShapleyFolkman.lean` lines 317-328: replaced Step 2 sorry

### Next Steps
1. Prove Step 6: define ε = min { (1-sv_l)/(-c'_l) : c'_l < 0 }, construct D',
   verify convex hull membership (weights in [0,1] summing to 1), sum preservation,
   and excess count decrease (lmin index has b-weight hitting 0)

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

---

## Session 2026-04-14 (Session 5) — Proof Architecture Expansion

**Mode**: REVISIT
**Outcome**: progress — 1 sorry replaced by structured proof with 1 focused sorry remaining

### What I Did
- Replaced single sorry in `reduce_excess_by_one` Step 6 with ~300-line structured proof
- Proved `hemb_inj` (injectivity of embedding via `List.nodup_iff_injective_get`)
- Proved `hD'_subset` (D'.excessIndices ⊆ D.excessIndices, trivially true via hemb_mem)
- Proved `hnew_point_av` (new_point(emb l_min) = av(emb l_min) ∈ S via algebraic identity)
- Proved ε₀ perturbation construction (min over neg-coefficient ratio bounds)
- Proved sum preservation (∑ perturbations = ε₀ · ∑ c'_l · δ_l = 0)

### Key Findings
- hD'_subset is TRIVIALLY TRUE: emb maps into D.excessIndices (by hemb_mem), so all
  perturbed excess indices were already in D.excessIndices
- hemb_inj proved cleanly using List.nodup_iff_injective_get applied to D.excessIndices.val.toList
- The ε₀ from neg-coefficient bounds only is INSUFFICIENT for new_mem_convexHull:
  for positive-coefficient indices l (c'_l > 0), a-weight = sv_l - ε₀·c'_l may go negative
- Fix requires: joint ε = min(ε_neg_min, ε_pos_min) where ε_pos_min = min(sv(emb l)/c'(l) for c'_l > 0)
- With joint ε: new_mem_convexHull is provable (all weights ≥ 0 by construction)
- BUT joint ε may be achieved by a pos-index (Case B), not lneg (Case A), so excess decrease proof breaks
- Case B WF argument: when pos-index achieves joint minimum, bv(emb l_B) ∈ conv(S) with fewer Carathéodory vertices → need WF on total vertex count

### Files Modified
- `proofs/Proofs/ShapleyFolkman.lean`: 1 sorry → 1 sorry (different, more focused)
- `src/data/research/problems/shapley-folkman.json`: updated knowledge

### Next Steps
1. Fix `new_mem_convexHull`: compute joint ε = min over both neg and pos coefficient bounds
2. Handle Case B separately with WF induction on Carathéodory vertex count
3. Alternative: submit new_mem_convexHull sorry to Aristotle as HARD sorry

---

## Session 2026-04-21 (Session 6) — Case A of new_mem_convexHull Proved

**Mode**: REVISIT
**Outcome**: progress — Case A of `new_mem_convexHull` fully proved; Case B still sorry

### What I Did
- Replaced `new_mem_convexHull` sorry (lines 543-547) with ~50-line case-split proof
- Introduced `by_cases hCaseA : ∀ l ∈ pos_indices, ε₀ ≤ sv (emb l) / c' l`
- In Case A (when ε₀ satisfies pos-index bounds too): proved all three sub-cases:
  - c'_l < 0: a-coeff ≥ 0 via nlinarith; b-coeff ≥ 0 via `hε₀_le_neg` bound; then `convex_convexHull`
  - c'_l = 0: perturbed point equals `D.point (emb l)` which is already in conv(S)
  - c'_l > 0: a-coeff ≥ 0 via `hCaseA` hypothesis + `le_div_iff`; b-coeff ≥ 0 via nlinarith + `hsv_lt1`
- For non-emb indices: `new_point_not_emb` gives same as `D.point i ∈ conv(S i)` via `D.mem_convexHull`
- Case B: sorry with documented reason: "requires joint ε; full proof by WF induction on Carathéodory vertex count"

### Key Findings
- Case A proof works cleanly when ε₀ (from neg_indices only) also satisfies all pos_indices bounds
- `convex_convexHull ℝ (S (emb l))` directly proves convex combinations stay in convexHull
- The three-way c'_l trichotomy (`lt_trichotomy`) is the right decomposition
- For c'_l = 0: `hzero` simplifies to exact `D.point` membership — no perturbation
- Case B architectural insight: pos-index minimizer means new point goes to bv ∈ conv(S) not S;
  excess count doesn't decrease without WF on Carathéodory vertex count (Starr 1969 full proof)

### Files Modified
- `proofs/Proofs/ShapleyFolkman.lean`: replaced `new_mem_convexHull` sorry with 50-line case-split

### Next Steps
1. Prove Case B: define joint ε = min(ε₀, min over pos_indices sv(emb l)/c'(l)), then show
   WF descent: either Case A kicks in (excess decreases), or pos-index minimizer gives new_point
   ∈ conv(S) with strictly fewer Carathéodory vertices (Starr 1969)
2. Submit remaining Case B sorry to Aristotle as HARD sorry
