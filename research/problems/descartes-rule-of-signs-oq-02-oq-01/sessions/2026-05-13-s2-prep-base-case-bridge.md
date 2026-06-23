# S2 PREP — Base-case proofs + Mathlib bearer audit

**Date**: 2026-05-13 (researcher-1, ~10:50 UTC)
**Mode**: PREP (doc-only)
**Outcome**: pre-stage degree-0 and degree-1 base cases of
`budan_upper_bound_axiom`; audit Mathlib `RuleOfSigns`; identify the
architectural bridge needed for S2 ACT.

---

## 1. Goal restatement

The parent `DescartesRuleOfSignsOQ02.lean` declares

```lean
axiom budan_upper_bound_axiom (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b
```

This slug's mission is to replace the `axiom` with a `theorem` by
proving it.

Strategy: strong induction on `p.natDegree`. Decompose the proof into
three slices, each of which can be axiomatized independently while the
others are completed:

```lean
theorem budan_upper_bound_natDegree_zero  : … := by …  -- 4-line direct
theorem budan_upper_bound_natDegree_one   : … := by …  -- ~40-60 LOC
axiom   budan_upper_bound_natDegree_ge_two : …          -- honest residual
theorem budan_upper_bound_axiom_via_cases : … :=
  fun p hp a b hab => by
    rcases (Nat.lt_or_ge p.natDegree 1) with hd | hd
    · exact budan_upper_bound_natDegree_zero p hp (Nat.lt_one_iff.mp hd) a b hab
    rcases Nat.eq_or_gt_of_le hd with hd | hd
    · exact budan_upper_bound_natDegree_one p hp hd.symm a b hab
    · exact budan_upper_bound_natDegree_ge_two p hp hd a b hab
```

After S2 ACT, **only the `_ge_two` residual remains as an `axiom`** —
which is a more honest accounting (the d=0 and d=1 slices are
elementary, the inductive Rolle step is genuinely the open work).

---

## 2. Mathlib bearer audit (2026-05-13)

Files and lemmas inspected (Mathlib master):

### `Mathlib/Algebra/Polynomial/RuleOfSigns.lean` (395 LOC, 14 lemmas)

| Lemma | Signature |
|---|---|
| `Polynomial.signVariations` (def) | `[Semiring R] [LinearOrder R] (P : Polynomial R) : ℕ` |
| `signVariations_zero` | `signVariations (0 : R[X]) = 0` |
| `signVariations_monomial` | `signVariations (monomial d c) = 0` |
| `signVariations_eraseLead` | unchanged when first two signs match |
| `signVariations_eq_eraseLead_add_ite` | adds 1 if leading and erased-leading flip |
| `signVariations_eraseLead_le` | `signVariations P.eraseLead ≤ signVariations P` |
| `signVariations_le_eraseLead_succ` | `signVariations P ≤ signVariations P.eraseLead + 1` |
| `signVariations_neg` | `signVariations (-P) = signVariations P` |
| `signVariations_C_mul` | nonzero scalar multiplication preserves |
| `succ_signVariations_le_X_sub_C_mul` | `0 < η → P ≠ 0 → signVariations P + 1 ≤ signVariations ((X - C η) * P)` |
| `roots_countP_pos_le_signVariations` | **Descartes** — positive roots ≤ V |

The Descartes proof (lines 379-394) is:

```lean
theorem roots_countP_pos_le_signVariations : P.roots.countP (0 < ·) ≤ signVariations P := by
  generalize h : P.roots.countP (0 < ·) = num_pos_roots
  induction num_pos_roots generalizing P    -- induct on # of positive roots, NOT on degree
  · exact zero_le
  rename_i ih
  have hp : P ≠ 0 := by grind [roots_zero, Multiset.countP_zero]
  obtain ⟨η, η_root, η_pos⟩ : ∃ x, x ∈ P.roots ∧ 0 < x := by grind [Multiset.countP_pos]
  obtain ⟨Q, rfl⟩ := dvd_iff_isRoot.mpr (isRoot_of_mem_roots η_root)
  grw [ih Q, succ_signVariations_le_X_sub_C_mul η_pos]
  · exact right_ne_zero_of_mul hp
  · simp [← h, roots_mul (ne_zero_of_mem_roots η_root), η_pos, ← Nat.succ.injEq]
```

**Key observation**: This induction is on the number of positive
roots, not on the degree, and **does not use Rolle**. The
sign-change accounting is captured entirely by
`succ_signVariations_le_X_sub_C_mul`, which says: multiplying by
`(X − η)` for `0 < η` raises `signVariations` by ≥ 1.

This is a structurally different proof from the Rolle-based induction
that OQ-02's roadmap assumes. See §5 for whether the same pattern can
be lifted to Budan.

### `Mathlib/Analysis/Calculus/LocalExtr/Rolle.lean`

| Lemma | Signature |
|---|---|
| `exists_deriv_eq_zero` | the IVT/Rolle source — already in use by `BudanTheorem.rolle_polynomial` |

### `Mathlib/Algebra/Polynomial/Basic.lean` / `Coeff.lean` / `Roots.lean`

| Lemma | Used? |
|---|---|
| `Polynomial.eq_C_of_natDegree_eq_zero` | YES (d=0 base case) |
| `Polynomial.map_zero` | YES (d=0 case, contradiction step) |
| `Polynomial.card_roots_le_degree` | YES (already used in `linear_at_most_one_root`) |
| `Polynomial.mem_roots` | YES (already used in `linear_at_most_one_root`) |
| `Polynomial.natDegree_derivative_le` | YES (used by `iterDeriv_natDegree_le`) |
| `Polynomial.derivative_C` | YES (used by `iterDeriv_of_zero`) |

### What Mathlib does NOT provide

- **No** `Polynomial.budanCount`, `budanSequence`, or any half-open-
  interval root-counting infrastructure. OQ-02's locally defined
  `budanCount`, `budanSequence`, `rootsInInterval` are necessary and
  not duplicating Mathlib.
- **No** lemma about `(X − r) · q` and `budanCount p x` at arbitrary
  `x` (Mathlib's `succ_signVariations_le_X_sub_C_mul` is
  coefficient-based, equivalent to evaluating only at `x = 0`).

---

## 3. Degree-0 base case — concrete proof

Input: `p ≠ 0`, `p.natDegree = 0`, `a < b`.

Standalone proof (after `import Proofs.DescartesRuleOfSignsOQ02`, inside
`namespace BudanTheorem`):

```lean
/-- Base case of Budan's upper bound: constant nonzero polynomials have
no roots in any interval, and their Budan-Fourier count is identically
zero. -/
theorem budan_upper_bound_natDegree_zero (p : ℝ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = 0) (a b : ℝ) (_hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  have hp_eq : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd
  have hc_ne : p.coeff 0 ≠ 0 := fun h => hp (by rw [hp_eq, h, map_zero])
  rw [hp_eq, rootsInInterval_C _ hc_ne, budanCount_C, budanCount_C]
```

After the three rewrites the goal is `0 ≤ 0 - 0 = 0`, closed
automatically by `Nat.le_refl` (or omitted entirely — `rw` of a
`= 0` equation will close a `≤ 0` goal via reflexivity if the closing
step lands on `Nat.zero_le`). If Lean complains, append `<;> simp` or
`<;> exact Nat.zero_le _`.

**Falsification check** (mental):
- `p = C 3`, `a = 0`, `b = 1` ⇒ `rootsInInterval = 0`,
  `budanCount p 0 = budanCount p 1 = 0` ⇒ `0 ≤ 0 - 0 = 0` ✓
- `p = C (-7)`, `a = -10`, `b = 10` ⇒ same. ✓

Estimated cost when shipped as ACT: **4 substantive lines + 1
preamble import line**. Adds **0 axioms**, removes a slice of
`budan_upper_bound_axiom`.

---

## 4. Degree-1 base case — proof skeleton

Input: `p ≠ 0`, `p.natDegree = 1`, `a < b`.

Write `p = C c1 * X + C c0` with `c1 ≠ 0`. The unique real root is
`r := -c0 / c1`. The derivative `p' = C c1` is a nonzero constant.

### Skeleton

```lean
theorem budan_upper_bound_natDegree_one (p : ℝ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = 1) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  -- Extract coefficients
  set c1 := p.coeff 1
  set c0 := p.coeff 0
  have hc1 : c1 ≠ 0 := by
    intro h
    have hcd : p.natDegree ≤ 0 := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero] <;> sorry  -- ≤0 ⇒ coeff k=0 for k>0
    omega
  have hp_eq : p = C c1 * X + C c0 := by
    -- Use `Polynomial.as_sum_range` or direct expansion at `natDegree = 1`
    sorry
  -- The unique root is r := -c0 / c1
  set r := -c0 / c1 with hr_def
  -- ROOT COUNT: rootsInInterval = 1 if r ∈ (a, b], else 0
  have h_roots : rootsInInterval p a b = if (a < r ∧ r ≤ b) then 1 else 0 := by
    sorry
  -- BUDAN COUNT at a point x: 1 if c1·x + c0 and c1 have OPPOSITE strict signs, else 0
  have h_budan : ∀ x, budanCount p x =
      (if p.eval x = 0 then 0
       else if (p.eval x > 0 ↔ c1 > 0) then 0 else 1) := by
    sorry
  -- Case-split on whether r ∈ (a, b]
  by_cases hr : a < r ∧ r ≤ b
  · -- root in interval: rootsInInterval = 1
    rw [h_roots, if_pos hr]
    -- At a, the value p.eval a has strict sign opposite to c1
    -- At b, the value p.eval b has the same strict sign as c1 (or is 0)
    -- So budanCount p a = 1, budanCount p b ≤ 1 (= 0 if b > r; = 0 if b = r since p.eval r = 0)
    sorry  -- case-by-case on whether b = r or b > r, sign of c1
  · -- no root in interval: rootsInInterval = 0
    rw [h_roots, if_neg hr]
    exact Nat.zero_le _
```

### Key sub-lemmas needed (each independently provable, ≤ 20 LOC)

1. `polyDegOne_eq_X_aff`: `p.natDegree = 1 → p = C (p.coeff 1) * X + C (p.coeff 0)`.
   Proof: `Polynomial.as_sum_range` over `Finset.range 2`.

2. `rootsInInterval_polyDegOne_eq_ite`: explicit formula for the root
   count of a degree-1 polynomial in `(a, b]`.
   Proof: `p.roots = {r}` (multiset of size 1) for degree-1 nonzero;
   filter is `{r}` or `∅` depending on `a < r ≤ b`.

3. `budanCount_polyDegOne_eq_ite`: explicit formula for `budanCount p x`.
   Uses `budanSequence p 1 x = [p.eval x, c1]` and a 2-element
   `signChangesInList` calculation.

### Why this is more than 5 lines

The `budanCount` and `rootsInInterval` lemmas for degree-1 need
explicit unfolding. OQ-02's helper API doesn't currently include
degree-1-specific simp lemmas (it has only degree-0 via
`budanCount_C` / `rootsInInterval_C`). Adding the three sub-lemmas
above is the principled way; they will also be reused in the
inductive step's "factor out one root" reduction.

Estimated cost when shipped as ACT: **40-60 LOC** (10-20 each for the
three sub-lemmas, then 15-20 for the case-analysis on the main
theorem).

---

## 5. Strategy comparison — Rolle vs. factor-out-root

The original OQ-02 roadmap (S1, S2 plan) assumes a Rolle-based
induction. The Mathlib `RuleOfSigns` proof of Descartes uses a
factor-out-root pattern. **Can we lift the Mathlib pattern to Budan?**

### The Mathlib factor-out-root pattern (for Descartes only)

```
P with k+1 positive roots
  ↓ pick η > 0 with η a root, write P = (X − η) · Q
Q with k positive roots
  ↓ IH
signVariations Q ≥ k
  ↓ succ_signVariations_le_X_sub_C_mul η_pos
signVariations P ≥ k + 1
```

The key lemma is

```lean
succ_signVariations_le_X_sub_C_mul (hη : 0 < η) (hP : P ≠ 0) :
    signVariations P + 1 ≤ signVariations ((X - C η) * P)
```

which is **coefficient-based** and **requires η > 0** (i.e., evaluates
at `x = 0`).

### Lifting to Budan — what would be needed

We would need, for general `a < b`:

```
budan_upper_bound for q on (a,b]
  ↓ ?
budan_upper_bound for (x-r)·q on (a,b]
```

Concretely, this requires a lemma of the form

```lean
-- (Conjectured, not yet proved.)
lemma budanCount_diff_X_sub_C_mul (q : ℝ[X]) (hq : q ≠ 0) (r a b : ℝ)
    (hab : a < b) (hr_a : a < r) (hr_b : r ≤ b) :
    budanCount ((X - C r) * q) a - budanCount ((X - C r) * q) b
      ≥ (budanCount q a - budanCount q b) + 1
```

This is the Budan analog of `succ_signVariations_le_X_sub_C_mul`.

### Falsification — quick checks

Take `q = X + 1` (root at −1, never in `(a, b]` if `a ≥ 0`).
Let `r = 1`, `a = 0`, `b = 2`. Then `p = (X − 1)(X + 1) = X² − 1`.

- `q.eval 0 = 1`, `q.eval 2 = 3`, `q' = C 1`. So
  `budanSequence q 1 x = [q.eval x, 1]`; both entries positive at
  `x ∈ {0, 2}`. `budanCount q 0 = budanCount q 2 = 0`.
- `p.eval 0 = -1`, `p.eval 2 = 3`. `p' = 2X`, `p'.eval 0 = 0`,
  `p'.eval 2 = 4`. `p'' = C 2`.
  `budanSequence p 2 x = [p.eval x, 2x, 2]`.
  At `x = 0`: `[-1, 0, 2]` → after dropping zero: `[-1, 2]` → 1 sign
  change.
  At `x = 2`: `[3, 4, 2]` → all positive → 0 sign changes.
  So `budanCount p 0 = 1`, `budanCount p 2 = 0`.

Check: `budanCount p a − budanCount p b = 1 − 0 = 1`.
       `budanCount q a − budanCount q b = 0 − 0 = 0`. Difference is
       1. ✓ The conjectured lemma is consistent on this example.

Take another: `q = X − 3`, `r = 1`, `a = 0`, `b = 2`. Then
`q.eval 0 = -3`, `q.eval 2 = -1`, `q' = C 1`. So budan seq at 0
is `[-3, 1]` → 1 change. At 2: `[-1, 1]` → 1 change. So
`budanCount q 0 − budanCount q 2 = 0`.
`p = (X − 1)(X − 3) = X² − 4X + 3`. `p.eval 0 = 3`, `p.eval 2 = -1`.
`p' = 2X − 4`. `p'.eval 0 = -4`, `p'.eval 2 = 0`. `p'' = 2`.
At `x = 0`: `[3, -4, 2]` → 2 changes.
At `x = 2`: `[-1, 0, 2]` → drop zero → `[-1, 2]` → 1 change.
`budanCount p 0 − budanCount p 2 = 2 − 1 = 1`. ✓ Difference vs.
`q`'s 0 is 1.

Both small cases support the conjecture. **But proving the conjecture
in Lean requires understanding how multiplication by `(X − r)`
transforms the **entire derivative tower** at `a` and at `b`, including
sign-change accounting around the root `r`. This is essentially
equivalent in difficulty to the Rolle-based plan, and is the same
"sign-change accounting" gap.

### Verdict

Switching strategies does not change the difficulty profile. Both
roads pass through a sign-change-preservation lemma that is **not in
Mathlib** and **is the dominant cost** of the proof.

For consistency with the existing roadmap and to reuse `rolle_polynomial`
+ `n_roots_derivative_roots` (already proved in OQ-02), we recommend
sticking with the Rolle-based induction.

---

## 6. Architectural decision — bridging OQ02OQ01 ↔ OQ02

`DescartesRuleOfSignsOQ02OQ01.lean` currently:
- Has its own `namespace BudanUpperBound`
- Re-defines `iterDeriv` locally
- Does **not** `import Proofs.DescartesRuleOfSignsOQ02`

To prove `BudanTheorem.budan_upper_bound_axiom`, the file must:
1. Add `import Proofs.DescartesRuleOfSignsOQ02`
2. Either (a) close `namespace BudanUpperBound` and open
   `namespace BudanTheorem` for the axiom-discharging theorems, or
   (b) state the theorems inside `BudanTheorem` directly.

Option (a) is cleanest. The existing `BudanUpperBound`-namespace
helpers (`linear_at_most_one_root`, `constant_no_roots`, `rolle_polynomial`,
`root_of_sign_change`) become "scratch" — they can be deleted in a
follow-up sync since `BudanTheorem` already has its own `rolle_polynomial`
and the analogues for the others are 5-liners on the OQ-02 API.

### Recommended file structure after S2 ACT

```lean
import Mathlib.…
import Proofs.DescartesRuleOfSignsOQ02

set_option maxHeartbeats 400000

namespace BudanTheorem

open Polynomial

-- Degree-0 base case (4 lines, see §3)
theorem budan_upper_bound_natDegree_zero (p : ℝ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = 0) (a b : ℝ) (_hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := …

-- Degree-1 base case (40-60 lines, see §4)
theorem budan_upper_bound_natDegree_one (p : ℝ[X]) (hp : p ≠ 0)
    (hd : p.natDegree = 1) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := …

-- Honest residual: the d ≥ 2 case
axiom budan_upper_bound_natDegree_ge_two (p : ℝ[X]) (hp : p ≠ 0)
    (hd : 2 ≤ p.natDegree) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b

-- Composed proof (3-way case)
theorem budan_upper_bound_axiom_proved (p : ℝ[X]) (hp : p ≠ 0)
    (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b := by
  rcases (Nat.lt_or_ge p.natDegree 1) with hd | hd
  · exact budan_upper_bound_natDegree_zero p hp (Nat.lt_one_iff.mp hd) a b hab
  rcases Nat.eq_or_gt_of_le hd with hd | hd
  · exact budan_upper_bound_natDegree_one p hp hd.symm a b hab
  · exact budan_upper_bound_natDegree_ge_two p hp hd a b hab

end BudanTheorem
```

After this S2 ACT, `DescartesRuleOfSignsOQ02.lean`'s
`budan_upper_bound_axiom` could be **demoted** in spirit: the d=0 and
d=1 slices are theorems, only `_natDegree_ge_two` remains. The parent
file's axiom remains until the d≥2 slice is also proved (S3).

### Axiom-budget accounting

- OQ-02 currently declares 3 axioms: `budan_upper_bound_axiom`,
  `budan_parity_axiom`, `budanCount_large_axiom`.
- After S2 ACT (this PREP's plan): OQ-02-OQ-01 declares 1 axiom
  (`budan_upper_bound_natDegree_ge_two`) and proves 2 theorems.
- **Net axiom count is the same** (1 axiom replaces 1 axiom on the
  upper-bound slice), but the unproved slice is now strictly narrower
  (only d ≥ 2 instead of all d). This is honest progress, not
  laundering.

---

## 7. Status, scope, and what is *not* in this PREP

This is a **doc-only PREP**. No Lean files are modified. No build is
run. The deliverables are:

- `research/problems/descartes-rule-of-signs-oq-02-oq-01/problem.md` — new
- `research/problems/descartes-rule-of-signs-oq-02-oq-01/state.md` — new
- `research/problems/descartes-rule-of-signs-oq-02-oq-01/knowledge.md` — new
- `research/problems/descartes-rule-of-signs-oq-02-oq-01/sessions/2026-05-13-s2-prep-base-case-bridge.md` — this file
- `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01.json` — knowledge update

What is **not** in this PREP:
- Concrete Lean proofs of the three §4 sub-lemmas (the d=1 case
  requires them; they are sketched but not verified).
- Any change to `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01.lean` or
  `proofs/Proofs/DescartesRuleOfSignsOQ02.lean`.
- The hard core: the d ≥ 2 inductive step.

---

## 8. Next session (S2 ACT)

Build-pending PR adding to `DescartesRuleOfSignsOQ02OQ01.lean`:

1. `import Proofs.DescartesRuleOfSignsOQ02` and
   `open Polynomial in namespace BudanTheorem`.
2. `budan_upper_bound_natDegree_zero` (4 lines, §3 verbatim).
3. The three sub-lemmas for d=1 from §4.2.
4. `budan_upper_bound_natDegree_one`.
5. Reserve `budan_upper_bound_natDegree_ge_two` as an explicit `axiom`
   inside `BudanTheorem`.
6. `budan_upper_bound_axiom_proved` (the composed 3-way case theorem)
   showing how the new slices and the residual axiom recover the
   original axiom statement.

Expected diff: +60-80 LOC, axiom count up by 1 (the new `_ge_two`
slice axiom is declared but the old `budan_upper_bound_axiom` is not
removed; net axiom count goes 3→4 temporarily, but the **unproved
mathematical content** is strictly narrower).

In S3, when d ≥ 2 is proved, both the new `_ge_two` axiom and the
original `budan_upper_bound_axiom` come down (net 4→2; net unproved
content collapses to just the d ≥ 2 reasoning, which is then
discharged).
