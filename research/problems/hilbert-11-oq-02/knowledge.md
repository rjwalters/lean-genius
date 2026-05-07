# hilbert-11-oq-02
## When does the Hasse Principle Fail for Higher-Degree Forms? — Selmer Counterexample Framework

**Status: IN PROGRESS** — First iteration: proved the Selmer cubic has nontrivial real
solutions (via IVT), proved the easy direction of the Hasse principle (rational ⇒
local) over both ℝ and ℚₚ, and laid out the framework for the open question.

---

## Summary

`Hilbert11OQ02.lean` establishes a precise Lean framework for the open question
"when does the Hasse principle fail for higher-degree forms?".

**File stats**: ~210 lines, 7 theorems/defs, 2 axioms (Selmer 1951 + p-adic Hensel
infrastructure), 0 sorries.

---

## What Was Proved

### `selmerCubic_real_solution` (PROVED via IVT)
The Selmer cubic 3x³ + 4y³ + 5z³ = 0 has a nontrivial real solution.

**Proof sketch**: Set y = 1, z = 0. Need x ∈ ℝ with 3x³ + 4 = 0. The polynomial
g(x) = 3x³ + 4 satisfies g(-2) = -20 < 0 and g(0) = 4 > 0, so by `intermediate_value_Icc`
there exists x₀ ∈ [-2, 0] with g(x₀) = 0. Witness (x₀, 1, 0); nontrivial since 1 ≠ 0.

### `selmer_rat_implies_real` (PROVED)
Every rational solution of the Selmer cubic gives a real solution.
Trivial via `Rat.cast : ℚ → ℝ`. Uses `push_cast; ring` to convert.

### `selmer_rat_implies_padic` (PROVED)
Every rational solution gives a p-adic solution at every prime p.
Same idea: cast through `Rat.cast : ℚ → ℚ_[p]`.

### `selmer_locally_soluble_everywhere` (PROVED, modulo `selmer_padic_solubility` axiom)
Combines real solubility (proved) with p-adic solubility (axiomatized).

### `selmer_hasse_principle_fails` (PROVED, modulo two axioms)
Local solubility everywhere + no rational solution = Hasse principle fails.

---

## Axioms Introduced

### `selmer_no_rational_solution` (Selmer 1951, deep)
The cubic 3x³ + 4y³ + 5z³ = 0 has no nontrivial rational solutions.
**Why axiomatized**: Requires 3-descent on associated elliptic curve, computation of
Selmer groups via class field theory of ℚ(ζ₃, ∛15), local non-existence at primes
3 and 5. Far beyond present Mathlib infrastructure.

### `selmer_padic_solubility` (Hensel infrastructure pending)
For each prime p, the cubic has a nontrivial p-adic solution.
**Why axiomatized**: For p ∉ {2, 3, 5}, follows from Hensel applied to the reduction
mod p; for p ∈ {2, 3, 5}, requires direct construction at low precision. This could
be formalized in future work via ℚₚ Hensel infrastructure.

---

## Session Log

### Session 2026-05-07 (Session 1, researcher-9)
**Mode**: FRESH
**Outcome**: progress

**What Was Done**:
1. Created new gallery file `Hilbert11OQ02.lean` (~210 lines) addressing the open
   question "when does the Hasse principle fail for higher-degree forms?".
2. Proved `selmerCubic_real_solution` via Intermediate Value Theorem on g(x) = 3x³ + 4
   over [-2, 0]; witness (x₀, 1, 0) where g(x₀) = 0.
3. Proved easy directions `selmer_rat_implies_real` and `selmer_rat_implies_padic`
   via `Rat.cast` and `push_cast; ring`.
4. Defined `selmerHassePrinciple` predicate capturing local-global property.
5. Proved `selmer_hasse_principle_fails` from the two axioms.
6. Stated the Colliot-Thélène conjecture informally (`colliot_thelene_conjecture := True`)
   and documented known cases vs. open cases.

**Key Lean techniques**:
- `intermediate_value_Icc h_le hg_cont.continuousOn hmem` for IVT.
- `linear_combination hsum` for ring-based equality from a hypothesis.
- `push_cast; ring` for ℚ → ℝ / ℚ → ℚₚ embedding via casting.
- `hg_eval ▸ hx_zero` for rewriting via equational hypothesis.

---

## Key Mathematical Insights

1. **Real solubility is constructive**: Unlike the deep p-adic and rational
   non-existence arguments, real solubility for the Selmer cubic admits an
   elementary IVT-based proof. This is the "low-hanging fruit" of the
   counterexample story.

2. **The hard part is rational non-existence**: The Hasse principle's failure for
   the Selmer cubic depends entirely on `selmer_no_rational_solution` (Selmer 1951).
   This is a deep theorem requiring elliptic curve 3-descent — far beyond present
   Mathlib infrastructure.

3. **Brauer-Manin captures many failures**: The conjecture (Colliot-Thélène) is that
   for nice varieties, Brauer-Manin is the only obstruction. Known for several families
   (conic bundles, del Pezzo deg ≥ 5) but open for cubic surfaces and K3 surfaces.

4. **Tractability gradient**: Real solubility (PROVED) → p-adic solubility (axiomatizable
   via Hensel) → rational non-existence (deep, far) → general characterization (open
   research question).
