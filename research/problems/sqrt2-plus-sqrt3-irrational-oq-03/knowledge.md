# Knowledge Base: sqrt2-plus-sqrt3-irrational-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

- Target: prove f(x) = x⁴ - 10x² + 1 is the minimal polynomial of α = √2+√3 over ℚ
- Step 1: verify f(α) = 0 by direct computation (α² = 5+2√6, α⁴ = 49+20√6)
- Step 2: prove f is irreducible over ℚ (rational root theorem + no quadratic factor)
- Step 3: conclude [ℚ(√2+√3):ℚ] = 4

---

## Insights

- α² = 5 + 2√6 (from (√2+√3)² = 2 + 2√6 + 3)
- α⁴ = (5 + 2√6)² = 25 + 20√6 + 24 = 49 + 20√6
- f(α) = α⁴ - 10α² + 1 = (49 + 20√6) - 10(5 + 2√6) + 1 = 49 + 20√6 - 50 - 20√6 + 1 = 0 ✓
- Rational root theorem: rational roots of x⁴-10x²+1 would be ±1; f(1)=-8≠0, f(-1)=-8≠0
- For quadratic factorization: (x²+ax+b)(x²-ax+c) = x⁴ + (b+c-a²)x² + a(c-b)x + bc
  Matching: b+c-a²=-10, a(c-b)=0, bc=1, and x³ coeff = 0 (already satisfied)
  From a(c-b)=0: either a=0 or b=c
  Case a=0: b+c=-10, bc=1 → b,c are roots of t²+10t+1=0, giving t = (-10±√96)/2 ∉ ℚ
  Case b=c: 2b-a²=-10, b²=1 → b=±1
    b=1: 2-a²=-10 → a²=12, a∉ℚ
    b=-1: -2-a²=-10 → a²=8, a∉ℚ
  → f is irreducible over ℚ ✓

---

## Dead Ends

- None yet (problem is tractable with direct computation)

---

## Session 2026-07-01 (researcher-2): mathlib-drift repair + native_decide elimination

The gallery Lean file `Sqrt2PlusSqrt3IrrationalOQ03.lean` had **silently bit-rotted**: it
no longer compiled against the current Mathlib (written 2026-04-22, many API changes since).
Broken items found & fixed:
- `natDegree_sub_eq_left_of_natDegree_lt` unification / manual natDegree computations →
  replaced throughout with the robust `monicity!` and `compute_degree!` tactics.
- `coeff_ofNat` renamed → `coeff_ofNat_zero` / `coeff_ofNat_succ`.
- `leadingCoeff_C_mul_X_add_C` renamed → `leadingCoeff_linear`.
- `natDegree_eq_one` reshaped to `∃ a ≠ 0, ∃ b, …` → destructure order `⟨p, hp, q, rfl⟩`.
- `isUnit_of_mul_eq_one` now `IsUnit.of_mul_eq_one` with `a` implicit (drop one `_`);
  `Int.units_eq_iff_abs_eq` gone → `Int.isUnit_iff` returns the `= 1 ∨ = -1` disjunction directly.
- `rcases … with rfl` on `a.coeff k = ±1` fails (not a local var) → use `with h` + `rw`.
- eval-mul rewrites needed forward `hab` not `← hab`; `interval_cases (a.natDegree)` replaced by
  an `omega`-derived 5-way disjunction so each case gets a named hypothesis.

**Non-square contradictions** (8, 12, 96 are not perfect squares): `nlinarith` alone CANNOT
prove `x^2 = 12 → False` (integrality). Robust pattern: bound `x` via
`nlinarith [h, sq_nonneg (x - k)]` to get strict `x < k` / `-k < x`, then
`interval_cases x <;> omega` (omega evaluates the literal square). NB: for the quadratic-factor
case the value is 8 **or** 12 depending on the sign product ha2·(a.coeff 0), so don't hardcode
the value — bound and interval_cases instead.

**native_decide → 0-axiom**: `¬ IsSquare (6 : ℕ)` was proved by `native_decide`
(pulls in `Lean.ofReduceBool`). Replaced with a kernel-checkable proof:
`rintro ⟨r, hr⟩; have : r ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨r, hr⟩; interval_cases r <;> omega`.
Plain `decide` does NOT work (`Nat.sqrt` uses well-founded recursion, kernel gets stuck).

Result: file compiles clean against current Mathlib; `#print axioms` on all credited theorems
lists only propext / Classical.choice / Quot.sound. Upgraded gallery meta
`formalized`/`mathlib`/axiomCount 1 → `verified`/`verified`/axiomCount 0. **COMPLETED.**
