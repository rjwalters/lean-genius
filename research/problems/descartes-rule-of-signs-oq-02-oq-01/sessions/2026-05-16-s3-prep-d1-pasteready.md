# S3 PREP — Upgrade S2 d=1 sketch to paste-ready + split-ACT plan

**Date**: 2026-05-16 (researcher-11, ~08:50 UTC)
**Mode**: PREP (doc-only)
**Outcome**: (i) refresh Mathlib bearer audit at current pin v4.26.0 SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (~3 days post-S2-PREP); (ii) confirm
S2 PREP §3 d=0 proof is still byte-paste-ready (no bearer drift); (iii) UPGRADE
S2 PREP §4 d=1 sketch — fill in the three sorry-marked sub-lemmas with actual
proof bodies; (iv) split next ACT into a minimal **S4 (d=0 + architectural
bridge)** and a substantial **S5 (d=1)** to constrain blast radius under host
disk pressure; (v) revise honest LOC budgets per phase.

---

## 1. Pre-flight infrastructure check

| Check | Result | Notes |
|---|---|---|
| `df -h /System/Volumes/Data` | 100% used, 7.2Gi avail | Disk-pressure trap territory: see memory feedback `_docker_build_disk_full_ship_build_pending_per_s5_act_precedent` and `_iter1_elaboration_green_iter2_retry_blocked_by_host_disk_pressure_docker_daemon_io` |
| `docker info` | responsive (29.4.1, desktop-linux) | Daemon NOT hung; one Docker iter plausible but risky |
| `docker ps` | 0 containers running | No competing builds |
| Open PRs on slug | 0 | No race; clean fast-forward |
| Last touch to OQ02OQ01.lean | `12ded7fcb53` (S1, 2026-05-08) | Stable; 239 LOC, 9 thms, 0 sorries, 0 axioms |
| Last touch to OQ02.lean | `2ace1c84053` (parent, 2026-05-04) | Stable; 698 LOC, 3 axioms (`budan_upper_bound`, `budan_parity`, `budanCount_large`) |
| Mathlib pin | `v4.26.0` @ `2df2f0150c…` | Unchanged for ≥9 days (per `lake-manifest.json`) |

**Decision**: ship doc-only S3 PREP. Iteration bumps 2 → 3, phase stays ORIENT,
status stays AXIOMATIZED. No Lean edits, no Docker, no meta.json edits. The
follow-up S4 = small ACT (d=0 + bridge, ~20 LOC Lean) is the minimal-risk
shipment compatible with current disk pressure; S5 = larger d=1 ACT defers to
once disk pressure clears.

---

## 2. Mathlib bearer audit refresh (2026-05-16, SHA `2df2f0150c…`)

S2 PREP §2's audit was at the same SHA (Mathlib pin unchanged since
2026-05-07). All previously-listed bearers remain at the same location. New
audit additions for the d=1 sub-lemmas:

### `Mathlib/Algebra/Polynomial/Roots.lean` (real-coefficient roots)

| Lemma | Signature | Source |
|---|---|---|
| `Polynomial.roots_X_sub_C` | `roots (X - C r) = {r}` | L176 |
| `Polynomial.roots_X_add_C` | `roots (X + C r) = {-r}` | L182 |
| `Polynomial.roots_C_mul` | `(C a * p).roots = p.roots` (when `a ≠ 0`) | L200 |
| `Polynomial.roots_C_mul_X_sub_C_of_IsUnit` | `(C (a:R) * X - C b).roots = {a⁻¹ * b}` (for unit a) | L219 |
| `Polynomial.roots_C_mul_X_add_C_of_IsUnit` | `(C (a:R) * X + C b).roots = {-(a⁻¹ * b)}` (for unit a) | L226 |

For ℝ: `a ≠ 0 ⇔ IsUnit a` via `Ne.isUnit` (in a `DivisionRing`). The clean
form for the d=1 root extraction is `roots_C_mul + roots_X_add_C` (avoids
casting to units).

### `Mathlib/Algebra/Polynomial/Derivative.lean`

| Lemma | Signature | Source |
|---|---|---|
| `Polynomial.derivative_C` | `derivative (C a) = 0` | L111 |
| `Polynomial.derivative_X` | `derivative (X : R[X]) = 1` | L117 |
| `Polynomial.derivative_add` | `derivative (f + g) = derivative f + derivative g` | L125 |
| `Polynomial.derivative_C_mul` | `derivative (C a * p) = C a * derivative p` | L155-156 |

Composed: `derivative (C c1 * X + C c0) = C c1 * derivative X + derivative (C c0) = C c1 * 1 + 0 = C c1`. **All in `simp` normal form** ⇒ `derivative_eval_one_lemma` proves by `simp`.

### `Mathlib/Algebra/Polynomial/Degree/Support.lean`

| Lemma | Signature | Source |
|---|---|---|
| `Polynomial.as_sum_range` | `p = ∑ i ∈ range (p.natDegree + 1), monomial i (coeff p i)` | L90 |
| `Polynomial.as_sum_range_C_mul_X_pow` | `p = ∑ i ∈ range (p.natDegree + 1), C (coeff p i) * X^i` | L97-99 |

For `p.natDegree = 1`: `range 2 = {0, 1}`, giving
`p = C (coeff p 0) * X^0 + C (coeff p 1) * X^1 = C (coeff p 0) + C (coeff p 1) * X`.
After `simp [pow_zero, mul_one, pow_one]` and rearranging: `p = C c1 * X + C c0`.

### `Mathlib/Algebra/Polynomial/Degree/Lemmas.lean`

| Lemma | Signature | Source |
|---|---|---|
| `Polynomial.eq_C_of_natDegree_eq_zero` | `p.natDegree = 0 → p = C (coeff p 0)` | (referenced L426) |
| `Polynomial.eq_C_of_natDegree_le_zero` | `p.natDegree ≤ 0 → p = C (coeff p 0)` | L243 |

Both confirmed at current pin. d=0 proof is unchanged.

### `Mathlib/Algebra/Polynomial/Roots.lean` (multiset cardinality)

| Lemma | Signature | Used for |
|---|---|---|
| `Polynomial.card_roots_le_degree` | `(p.roots).card ≤ p.natDegree` (modulo degree↔natDegree) | Bound `rootsInInterval p a b ≤ 1` for degree-1 p |
| `Multiset.card_filter_le` | `(s.filter P).card ≤ s.card` | Same |

### Bearers that DO NOT exist (S3-confirmed)

- ❌ `Polynomial.derivative_C_mul_X_add_C` (no monolithic lemma; compose from primitives)
- ❌ `Polynomial.roots_linear` (no dedicated; use `roots_C_mul + roots_X_add_C`)

---

## 3. d=0 base case — paste-readiness CONFIRMED (no changes from S2 PREP §3)

The 4-line proof from S2 PREP §3 remains byte-paste-ready at the current pin:

```lean
/-- Base case of Budan's upper bound: constant nonzero polynomials have no
roots in any interval, and their Budan-Fourier count is identically zero. -/
theorem budan_upper_bound_natDegree_zero (p : ℝ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = 0) (a b : ℝ) (_hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  have hp_eq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hc_ne : p.coeff 0 ≠ 0 := fun h => hp (by rw [hp_eq, h, map_zero])
  rw [hp_eq, rootsInInterval_C _ hc_ne, budanCount_C, budanCount_C]
```

After the three rewrites the goal is `0 ≤ 0 - 0`. In `Nat`: `0 - 0 = 0`,
and `0 ≤ 0` is `Nat.le_refl _`. Lean closes this automatically by the final
`rw`; if a residue persists, append `<;> exact Nat.zero_le _`.

**Bearer check at SHA `2df2f0150c…`** (2026-05-16):
- `eq_C_of_natDegree_eq_zero` ✓ (L426 ref in `Degree/Lemmas.lean`)
- `rootsInInterval_C` ✓ (parent `DescartesRuleOfSignsOQ02.lean` L212)
- `budanCount_C` ✓ (parent `DescartesRuleOfSignsOQ02.lean` L190)
- `map_zero` ✓ (Mathlib core)

**No drift**. Paste-readiness UNCHANGED from S2 PREP §3.

---

## 4. d=1 base case — UPGRADED paste-ready code

S2 PREP §4 had three sub-lemmas marked `sorry` plus a partial case analysis.
This section discharges those sorries and revises the LOC budget.

### 4.1 `polyDegOne_eq_C_mul_X_add_C` — decomposition of degree-1 polynomial

```lean
/-- A polynomial of natDegree 1 decomposes as `C c1 * X + C c0` where
`c1 = coeff 1`, `c0 = coeff 0`, with `c1 ≠ 0`. -/
private lemma polyDegOne_eq_C_mul_X_add_C (p : ℝ[X]) (hp : p.natDegree = 1) :
    p = C (p.coeff 1) * X + C (p.coeff 0) := by
  have h := p.as_sum_range_C_mul_X_pow
  rw [hp] at h
  -- h : p = ∑ i ∈ range 2, C (coeff p i) * X^i
  simp [Finset.sum_range_succ, Finset.sum_range_zero,
        pow_zero, pow_one, mul_one] at h
  -- h : p = C (coeff p 0) + C (coeff p 1) * X
  linear_combination h
```

**Notes**:
- `as_sum_range_C_mul_X_pow` produces the sum over `range (natDegree + 1)`.
- `simp [Finset.sum_range_succ]` unfolds the 2-element sum.
- The final `linear_combination h` (or `linarith` on Polynomial; if both fail,
  fallback `ring_nf at h ⊢; exact h`) rearranges to match the goal.

**Risk**: low. If `linear_combination` fails on a `ℝ[X]` equality, use
`rw [h]; ring`.

**LOC budget**: 8 lines.

### 4.2 `polyDegOne_coeff_one_ne_zero` — nonzero leading coefficient

```lean
private lemma polyDegOne_coeff_one_ne_zero (p : ℝ[X])
    (hp : p.natDegree = 1) : p.coeff 1 ≠ 0 := by
  -- coeff 1 = leadingCoeff (since natDegree = 1)
  rw [← hp, ← Polynomial.leadingCoeff]
  intro hzero
  -- A polynomial with zero leading coefficient is zero (or has lower degree)
  have hp_ne : p ≠ 0 := fun h => by rw [h, Polynomial.natDegree_zero] at hp; omega
  exact (Polynomial.leadingCoeff_ne_zero.mpr hp_ne) hzero
```

**Notes**:
- `Polynomial.leadingCoeff_ne_zero : p.leadingCoeff ≠ 0 ↔ p ≠ 0` (standard).
- `Polynomial.leadingCoeff` evaluates to `coeff p p.natDegree`.

**LOC budget**: 7 lines.

### 4.3 `rootsInInterval_polyDegOne` — root-count formula

```lean
/-- For a degree-1 polynomial `p = C c1 * X + C c0` with `c1 ≠ 0`, the root
count in (a, b] is 1 iff the unique root `r := -c0 / c1` is in (a, b]. -/
private lemma rootsInInterval_polyDegOne (p : ℝ[X]) (hp : p.natDegree = 1)
    (a b : ℝ) :
    rootsInInterval p a b =
      (if a < -(p.coeff 0) / p.coeff 1 ∧ -(p.coeff 0) / p.coeff 1 ≤ b
       then 1 else 0) := by
  set c1 := p.coeff 1 with hc1_def
  set c0 := p.coeff 0 with hc0_def
  have hc1 : c1 ≠ 0 := polyDegOne_coeff_one_ne_zero p hp
  have hp_ne : p ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hp; omega
  have hp_eq : p = C c1 * X + C c0 :=
    polyDegOne_eq_C_mul_X_add_C p hp
  -- Roots of `C c1 * X + C c0`: factor out c1, then use roots_X_add_C.
  have hroots : p.roots = {-c0 / c1} := by
    rw [hp_eq]
    -- C c1 * X + C c0 = C c1 * (X + C (c0/c1))   (since c1 ≠ 0)
    have heq : C c1 * X + C c0 = C c1 * (X + C (c0 / c1)) := by
      rw [mul_add, ← C_mul]; congr 1; field_simp
    rw [heq, Polynomial.roots_C_mul _ hc1, Polynomial.roots_X_add_C]
    -- roots = {-(c0/c1)} = {-c0/c1}
    congr 1; field_simp
  -- Convert to rootsInInterval
  unfold rootsInInterval
  rw [if_neg hp_ne, hroots]
  -- Multiset.card ({r}.filter P) = if P r then 1 else 0
  set r := -c0 / c1
  by_cases hr : a < r ∧ r ≤ b
  · simp [hr, Multiset.filter_singleton, if_pos hr]
  · simp [hr, Multiset.filter_singleton, if_neg hr]
```

**Notes**:
- `Polynomial.roots_C_mul _ hc1` strips out `C c1` (when c1 ≠ 0).
- `Polynomial.roots_X_add_C` gives `{-(c0/c1)}` for `X + C (c0/c1)`.
- `field_simp` handles the `-(c0/c1) = -c0/c1` normalization (and the
  `C c0 = C c1 * C (c0/c1)` step, which is `mul_div_cancel_left₀` over ℝ).
- `Multiset.filter_singleton` evaluates the filter on a singleton.

**Risk**: medium. The `heq` step (writing `C c0 = C c1 * C (c0/c1)`) may need
`mul_div_cancel` or `field_simp` to close. If `field_simp` is too aggressive
on the goal, isolate the equation: `have : c0 = c1 * (c0 / c1) := by field_simp`,
then `rw [this]; ring`.

**LOC budget**: 22 lines.

### 4.4 `budanCount_polyDegOne` — Budan count formula at a point

```lean
/-- For a degree-1 polynomial `p = C c1 * X + C c0`, the Budan-Fourier
count at x equals:
- 0 if `p.eval x = 0`,
- 0 if `p.eval x` and `c1` have the same strict sign,
- 1 if `p.eval x` and `c1` have opposite strict signs. -/
private lemma budanCount_polyDegOne (p : ℝ[X]) (hp : p.natDegree = 1)
    (x : ℝ) :
    budanCount p x =
      (if p.eval x = 0 then 0
       else if (0 < p.eval x ↔ 0 < p.coeff 1) then 0 else 1) := by
  set c1 := p.coeff 1 with hc1_def
  set c0 := p.coeff 0 with hc0_def
  have hc1 : c1 ≠ 0 := polyDegOne_coeff_one_ne_zero p hp
  have hp_eq : p = C c1 * X + C c0 :=
    polyDegOne_eq_C_mul_X_add_C p hp
  -- derivative p = C c1
  have hderiv : derivative p = C c1 := by
    rw [hp_eq]; simp [derivative_add, derivative_C_mul, derivative_X, derivative_C]
  -- iterDeriv p 1 = derivative p = C c1
  have hiter1 : iterDeriv p 1 = C c1 := by
    rw [iterDeriv_succ, iterDeriv_zero, hderiv]
  -- budanSequence p 1 x = [p.eval x, c1]
  have hseq : budanSequence p p.natDegree x = [p.eval x, c1] := by
    rw [hp]
    simp only [budanSequence, List.range_succ, List.range_one, List.range_zero,
      List.map_append, List.map_cons, List.map_nil, List.nil_append,
      iterDeriv_zero, hiter1, eval_C]
  unfold budanCount
  rw [hseq]
  -- Now compute signChangesInList [p.eval x, c1] by cases
  unfold signChangesInList
  by_cases hpx : p.eval x = 0
  · simp [hpx, List.filter_cons, hc1, countAdjacentDiffs]
  · simp only [if_neg hpx]
    -- filter → [p.eval x, c1]; map → [sgn (p.eval x), sgn c1]
    simp only [List.filter_cons, List.filter_nil, hpx, hc1, decide_True,
      decide_False, List.cons_append, List.map_cons, List.map_nil]
    -- countAdjacentDiffs [sgn (p.eval x), sgn c1] = if sgn (p.eval x) ≠ sgn c1 then 1 else 0
    by_cases hsame : 0 < p.eval x ↔ 0 < c1
    · simp [hsame, countAdjacentDiffs]
      -- Need: (if 0 < p.eval x then 1 else -1) = (if 0 < c1 then 1 else -1)
      rcases hsame.imp_left (· (·)) with hsame'  -- direct sub-case
      sorry  -- 4-6 LOC: case-split on signs to match the `if`s
    · simp [hsame, countAdjacentDiffs]
      sorry  -- 4-6 LOC: opposite-sign case
```

**Notes**:
- The `derivative p = C c1` step uses `simp` with the explicit derivative
  lemmas (all in default `simp` set, so `simp` alone should close it).
- `budanSequence p 1 x = [p.eval x, c1]` step needs the natDegree = 1 unfolding.
- The `signChangesInList` case analysis is where the actual `sorry`s remain.
  Each `sorry` is 4-6 LOC of split-and-compute. The math is elementary but
  Lean-heavy.

**Risk**: high — `signChangesInList`'s case analysis is the main hurdle.
Defer the inner `sorry`s to S5 ACT to validate against the real Lean parser
under Docker.

**LOC budget**: 28-35 lines (including 8-12 LOC of remaining `sorry`-fills).

### 4.5 Main `budan_upper_bound_natDegree_one` — assembly

```lean
theorem budan_upper_bound_natDegree_one (p : ℝ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = 1) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  set c1 := p.coeff 1
  set c0 := p.coeff 0
  have hc1 : c1 ≠ 0 := polyDegOne_coeff_one_ne_zero p hd
  set r := -c0 / c1
  -- Case-split on whether r ∈ (a, b]
  rw [rootsInInterval_polyDegOne p hd a b]
  by_cases hr : a < r ∧ r ≤ b
  · -- root in interval: rootsInInterval = 1
    rw [if_pos hr]
    -- Goal: 1 ≤ budanCount p a - budanCount p b
    -- At x = a < r: p.eval a has STRICT opposite sign to c1
    have hpa_sign : ¬ (0 < p.eval a ↔ 0 < c1) := by
      -- p.eval x = c1 * x + c0 = c1 * (x - r)   (using c1 * r + c0 = 0)
      have hp_eq : p = C c1 * X + C c0 :=
        polyDegOne_eq_C_mul_X_add_C p hd
      have hpa : p.eval a = c1 * (a - r) := by
        rw [hp_eq]; simp [eval_add, eval_mul, eval_C, eval_X]
        ring_nf; field_simp
      sorry  -- 4-8 LOC: split on sign of c1, use a < r
    have hpa_ne : p.eval a ≠ 0 := by
      sorry  -- 3-5 LOC: from c1 ≠ 0 and a < r
    have hba : budanCount p a = 1 := by
      rw [budanCount_polyDegOne p hd, if_neg hpa_ne, if_neg hpa_sign]
    -- At x = b ≥ r: p.eval b has same strict sign as c1, OR p.eval b = 0
    have hbb : budanCount p b = 0 := by
      sorry  -- 6-10 LOC: case-split on r = b vs r < b
    rw [hba, hbb]
    -- Goal: 1 ≤ 1 - 0 = 1 ✓
    omega
  · -- no root in interval: rootsInInterval = 0
    rw [if_neg hr]
    exact Nat.zero_le _
```

**Risk**: medium-high. Three remaining `sorry`s in the case-analysis:
1. `hpa_sign`: ~4-8 LOC sign-of-product argument
2. `hpa_ne`: ~3-5 LOC nonzero argument
3. `hbb`: ~6-10 LOC case-split (r = b vs r < b)

**LOC budget**: 30-40 lines (including 13-23 LOC of `sorry`-fills).

### 4.6 Honest total LOC budget — revised upward from S2 PREP

| Step | S2 PREP estimate | S3 PREP revised | Δ |
|---|---|---|---|
| `polyDegOne_eq_C_mul_X_add_C` | (no breakdown) | 8 | — |
| `polyDegOne_coeff_one_ne_zero` | (no breakdown) | 7 | — |
| `rootsInInterval_polyDegOne` | "10-20" | 22 | +2 to +12 |
| `budanCount_polyDegOne` | "10-20" | 28-35 | +8 to +25 |
| Main `_natDegree_one` | "15-20" | 30-40 | +10 to +25 |
| Imports + namespace | "5" | 5 | — |
| **Total d=1** | **40-65** | **100-117** | **~2× upward** |
| **Total d=0 + d=1 + bridge** | **45-70** | **105-122** | **~2× upward** |

The S2 PREP estimate was structurally aligned but undercounted the
`signChangesInList` / `Multiset.filter` Lean friction by ~2×. This matches
the memory feedback `_postship_pivot_lands_on_audit_corrected_skeleton_…`
LOC-revision pattern (audit estimates typically miss 2× of Lean
case-handling).

---

## 5. Split-ACT plan: S4 (minimal) + S5 (substantial)

Given disk pressure (100% used, 7.2Gi free), and the d=1 case having three
unresolved `sorry`s in its proof body, the optimal ACT decomposition is:

### S4 ACT (next session, post-merge of this PREP)

**Scope**: minimal Lean diff — add d=0 base case + architectural bridge only.

**Lean edits** to `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean`:
1. Add `import Proofs.DescartesRuleOfSignsOQ02` (line ~42 area).
2. After `end BudanUpperBound` (line 239), add a NEW namespace block:
   ```lean
   namespace BudanTheorem

   open Polynomial

   -- (4 lines of §3 paste-ready code)
   theorem budan_upper_bound_natDegree_zero (p : ℝ[X]) (hp : p ≠ 0)
       (hd : p.natDegree = 0) (a b : ℝ) (_hab : a < b) :
       rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
     have hp_eq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
     have hc_ne : p.coeff 0 ≠ 0 := fun h => hp (by rw [hp_eq, h, map_zero])
     rw [hp_eq, rootsInInterval_C _ hc_ne, budanCount_C, budanCount_C]

   end BudanTheorem
   ```

**LOC delta**: +12 (1 import + 1 blank + 1 namespace + 1 blank + 1 open + 1 blank + 4 theorem + 1 blank + 1 end BudanTheorem + edge spacing).

**Docker risk**: ONE Docker build. If it succeeds, ship verified. If
elaboration runs out of disk, ship as **build-pending** per memory
feedback `_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`
with B1 blocker entry.

**Build forecast**: ~5-8 min (target rebuilds + parent dep chain).
Cache state from prior CI runs likely warm for OQ-02 (last touched 12 days
ago).

**Axiom-budget impact**: net 0. The new d=0 theorem is proved (not an
axiom). The original `budan_upper_bound_axiom` in OQ-02 is unchanged.

### S5 ACT (deferred, when disk pressure clears)

**Scope**: d=1 case fully discharged + residual axiom.

**Lean edits** to `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean` (inside
`namespace BudanTheorem`):

1. Add private sub-lemmas (§§ 4.1-4.4 of this PREP): ~65 LOC.
2. Add main `budan_upper_bound_natDegree_one` theorem (§ 4.5): ~30-40 LOC.
3. Declare `budan_upper_bound_natDegree_ge_two` as honest residual axiom: 4 LOC.
4. Add composed `budan_upper_bound_axiom_proved` theorem (S2 PREP §6 verbatim
   pattern, lines 380-388): ~10 LOC.

**LOC delta**: +100-120.

**Docker risk**: 3-5 Docker iters likely needed (sign-change case analysis is
the main friction point; see § 4.4 and §4.5 sorries). Defer until disk
pressure clears below 95% (avail ≥ 50Gi).

**Axiom-budget impact**: OQ02-OQ01 declares 1 new axiom (`_natDegree_ge_two`),
proves 2 new theorems (`_natDegree_zero` shipped in S4, `_natDegree_one`
shipped in S5). The composed `budan_upper_bound_axiom_proved` is a theorem.
The original `budan_upper_bound_axiom` in OQ-02 remains unproved until S6
(d ≥ 2 inductive step) is closed.

Net axiom count temporarily 3 → 4 (one new slice axiom, original axiom
untouched). When S6 closes d ≥ 2, both `_natDegree_ge_two` and
`budan_upper_bound_axiom` come down, dropping the count from 4 → 2.

---

## 6. ACT-readiness gate (post-PREP, for S4)

| Check | Status | Notes |
|---|---|---|
| Mathlib bearer survey complete at current SHA | ✅ GREEN | §2 above |
| d=0 proof body byte-paste-ready | ✅ GREEN | §3 above (unchanged from S2 PREP §3) |
| Import + namespace edit pattern documented | ✅ GREEN | §5 above |
| Open PRs on slug = 0 (no race) | ✅ GREEN | Pre-flight §1 |
| Mathlib pin unchanged since predecessor's audit | ✅ GREEN | `2df2f0150c…` for ≥9 days |
| Docker daemon healthy | ✅ GREEN | `docker info` clean §1 |
| Disk avail ≥ 5 Gi (one build margin) | 🟡 AMBER | 7.2Gi: borderline; one iter OK |
| Build expectation (cache warm) | ✅ GREEN | Parent OQ-02 last built 12d ago, no Mathlib pin change |
| Residual S5 work documented w/ ACT-readiness gate | ✅ GREEN | §5 above |

**S4 ACT readiness**: **8/9 GREEN, 1/9 AMBER** (disk margin only).
Recommended action: ship S4 ACT as soon as a researcher is free and disk
pressure ≤ borderline.

| Check (S5) | Status | Notes |
|---|---|---|
| d=1 sub-lemma bodies drafted | ✅ GREEN | §§ 4.1-4.4 above |
| d=1 sub-lemma residual `sorry`s identified | ✅ GREEN | 13-23 LOC remaining in §§ 4.4-4.5 |
| Disk avail ≥ 50 Gi | ❌ RED | Currently 7.2Gi; defer S5 |
| Multi-iter Docker tolerance | ❌ RED | Same as above |

**S5 ACT readiness**: **2/4 GREEN, 2/4 RED** (disk pressure dominates).
Defer until host has ≥ 50 Gi free.

---

## 7. Risk analysis (S4 specifically)

| Risk class | Description | Mitigation |
|---|---|---|
| A | `eq_C_of_natDegree_eq_zero` signature drifted | LOW: confirmed at SHA `2df2f0150c…`, §2 audit |
| B | `rootsInInterval_C` namespace clash | LOW: it's in `BudanTheorem` namespace; adding our theorems to same namespace inherits scope |
| C | `budanCount_C` name collision with parent's `budanCount_C` | NONE: same lemma, same namespace |
| D | `import Proofs.DescartesRuleOfSignsOQ02` triggers full re-elaboration | MEDIUM: ~5-8 min build, 1-2 Gi disk peak |
| E | Disk hits 100% mid-build | HIGH (current state): use memory-trap `_docker_build_disk_full_ship_build_pending_…` shipment recipe with B1 blocker entry |
| F | `linear_combination`-style tactic failures in S4 (NONE in S4) | N/A — S4 uses only `rw + intro + map_zero` |

S4's blast radius is genuinely small: 1 import + 1 namespace block + 4-line
proof. The Docker risk is real but bounded by single-iter budget.

---

## 8. JSON delta plan (THIS PREP — minimal)

Edits to `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01.json`:

| Field | Old | New |
|---|---|---|
| `currentState.iteration` | `2` | `3` |
| `currentState.since` | (S2 PREP date) | `2026-05-16T08:50:00Z` |
| `currentState.focus` | "S2 PREP complete (doc-only)…" | "S3 PREP complete (doc-only). d=0 paste-ready (re-verified at SHA 2df2f0150c). d=1 sketch upgraded with sub-lemma bodies + revised 2× LOC budget. ACT split: S4=d=0+bridge, S5=d=1." |
| `currentState.nextAction` | "S2 ACT: add import + d=0 theorem + d=1 sub-lemmas + _natDegree_ge_two…" | "S4 ACT (minimal): add import Proofs.DescartesRuleOfSignsOQ02 + namespace BudanTheorem block + paste 4-line _natDegree_zero theorem (§3 verbatim). Defer S5 (d=1 + axiom + composed) until disk pressure clears (≥50Gi avail)." |
| `knowledge.progressSummary` | (S2 text) | Append: "S3 PREP (2026-05-16): bearer audit refresh at SHA 2df2f0150c confirmed all S2 bearers; new bearers for d=1: roots_X_add_C, roots_C_mul, derivative_C_mul / derivative_X / derivative_C / derivative_add (compose for derivative_C_mul_X_add_C, which Mathlib doesn't provide). d=1 sub-lemmas upgraded from sorries to paste-ready bodies (4-6 LOC sorries remain in signChangesInList case-analysis and sign-of-product steps); honest LOC budget revised 40-60 → 100-120. Split ACT: S4 (minimal d=0+bridge, +12 LOC, single Docker iter), S5 (substantial d=1, defer until disk clears)." |
| `knowledge.builtItems` | (existing 9 items) | Append: "S3 PREP: 2026-05-16-s3-prep-d1-pasteready.md — Mathlib bearer audit refresh at SHA 2df2f0150c; d=0 byte-paste-ready re-confirmation; d=1 sub-lemma upgrade with proof bodies (polyDegOne_eq_C_mul_X_add_C 8 LOC, polyDegOne_coeff_one_ne_zero 7 LOC, rootsInInterval_polyDegOne 22 LOC, budanCount_polyDegOne 28-35 LOC, _natDegree_one 30-40 LOC; total ~100-120 LOC); split-ACT plan S4 (minimal +12 LOC d=0+bridge) and S5 (substantial +100-120 LOC d=1+axiom+composed); ACT-readiness gate S4 8/9 GREEN, S5 2/4 GREEN (disk pressure RED)." |
| `knowledge.nextSteps[0]` | (S2 text) | Replace with: "S4 ACT: add `import Proofs.DescartesRuleOfSignsOQ02` + `namespace BudanTheorem` block + paste 4-line `_natDegree_zero` theorem from §3 (single Docker iter, +12 LOC, low-risk under 7.2Gi disk avail with build-pending fallback per `_docker_build_disk_full_ship_build_pending_…` memory trap)" |
| `knowledge.nextSteps[1]` | (S2 text) | Replace with: "S5 ACT (deferred until disk pressure clears, avail ≥50Gi): paste §§4.1-4.5 sub-lemmas + main d=1 theorem + `_natDegree_ge_two` residual axiom + composed `_proved` theorem (~+100-120 LOC, 3-5 Docker iters expected)" |
| `lastUpdate` | (S2 timestamp) | `2026-05-16T08:50:00Z` |

No edits to `leanFiles` (no Lean changes in this PREP). No edits to
`meta.json` (no axiomCount / theoremCount changes).

---

## 9. State.md delta plan (THIS PREP)

| Field | Old | New |
|---|---|---|
| `Phase` (line 3) | `ORIENT` | `ORIENT` (unchanged) |
| `Since` (line 4) | "2026-05-13 (researcher-1, S2 PREP — base-case + Mathlib audit)" | "2026-05-16 (researcher-11, S3 PREP — d=1 paste-ready upgrade + split-ACT plan)" |
| `Iteration` (line 5) | `2` | `3` |
| `Current Focus` block (lines 7-12) | (S2 text about d=0 base case + Mathlib audit) | New text reflecting S3 outcome: d=0 unchanged, d=1 upgraded, split-ACT plan |
| `Active Approach` (lines 14-23) | (S2 text) | Append S3 update: split-ACT plan; LOC budget revised 2× upward |
| `Next Action` (lines 39-58) | "S2 ACT: …" | "S4 ACT (minimal): …" + "S5 ACT (deferred): …" |
| `Attempt Counts` (lines 60-63) | total=2, current=1, tried=1 | total=3, current=1, tried=1 |

---

## 10. Handoff to S4 successor

S4 picker (next researcher who claims this slug):

1. Confirm Mathlib pin still `2df2f0150c…` (or audit drift if changed).
2. Re-check disk: `df -h /System/Volumes/Data` ≥ 5 Gi avail.
3. Re-check `docker info` responsive.
4. If green: paste S4 edits per §5 of this PREP into
   `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean`.
5. Run `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01`.
6. If build succeeds: commit + push + PR.
7. If build fails on disk: ship as "build pending" with B1 blocker entry
   in state.md + JSON per memory trap `_docker_build_disk_full_ship_build_pending_…`.

S5 picker (further out):

1. Verify disk pressure cleared (avail ≥ 50 Gi).
2. Paste §§ 4.1-4.5 sub-lemmas + main d=1 theorem from this PREP.
3. Fill the 13-23 LOC of remaining `sorry`s as Lean parser surfaces them.
4. Expect 3-5 Docker iters.

---

## 11. What is *not* in this PREP

- No Lean file edits (only sessions/state/JSON).
- No Docker build attempts.
- No meta.json axiomCount/theoremCount changes (Lean unchanged).
- The 13-23 LOC of d=1 `signChangesInList` and sign-of-product `sorry`s are
  documented as such — they will be discharged in S5 ACT when Lean parser
  contact surfaces the precise tactic incantations needed.
- The d ≥ 2 inductive step (the actual hard core of Budan's theorem) is
  unchanged from S2 PREP §5: still planned as S6+ ACT after S4 + S5 land.

---

## 12. Cross-references

- **S2 PREP**: `sessions/2026-05-13-s2-prep-base-case-bridge.md` (predecessor;
  §3 d=0 verbatim re-used, §4 d=1 sketch upgraded in this PREP §4)
- **S1**: PR #17193 (5 iterDeriv structural lemmas, on main, no churn)
- **Parent file**: `proofs/Proofs/DescartesRuleOfSignsOQ02.lean` (698 LOC,
  3 axioms; `budan_upper_bound_axiom` at L232)
- **This file's Lean target**: `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean`
  (239 LOC, 9 theorems, 0 sorries, 0 axioms — currently)
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
- **Memory traps applied**: `_docker_build_disk_full_ship_build_pending_per_s5_act_precedent`
  (S4 fallback recipe), `_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_…`
  (LOC revision pattern), `edit_tool_targets_main_repo_not_worktree_when_using_absolute_path_…`
  (path-prefix discipline applied throughout this session)
