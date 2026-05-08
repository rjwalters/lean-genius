import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Order.IntermediateValue
import Mathlib.Topology.Order.Bornology
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-
# Hilbert's 11th Problem OQ-02: When Does the Hasse Principle Fail for Higher-Degree Forms?

## Open Question: hilbert-11-oq-02

Hasse-Minkowski (formalized in `Hilbert11_QuadraticForms.lean` and `Hilbert11OQ01.lean`)
shows the Hasse principle holds for quadratic forms over ℚ. Selmer (1951) showed it
fails for the cubic 3x³ + 4y³ + 5z³ = 0, which has solutions over ℝ and every ℚₚ but
not over ℚ. The OPEN question asks for an exact characterization of when the Hasse
principle fails for higher-degree forms.

The Brauer-Manin obstruction (Manin 1971) explains many failures. The Colliot-Thélène
conjecture states that for smooth proper geometrically rationally connected varieties,
the Brauer-Manin obstruction is the only obstruction; this is known for several
families (conic bundles, del Pezzo surfaces of degree ≥ 5) but is open in general.

## What This File Contributes

1. **PROVED**: The Selmer cubic has a nontrivial **real** solution (constructed via IVT,
   witnessing local solubility over ℝ — the part of Selmer's theorem that is elementary).
2. **PROVED**: The "easy direction" of the Hasse principle for the Selmer cubic over ℝ
   (any rational solution gives a real solution, via the embedding ℚ ↪ ℝ).
3. **PROVED**: The "easy direction" over ℚₚ (rational ⇒ p-adic, via ℚ ↪ ℚₚ).
4. **AXIOMATIZED**: Selmer's theorem (no rational solutions). The full proof requires
   3-descent on a genus-1 curve, beyond present formalization.
5. **DEFINED**: A precise predicate `selmerHassePrinciple` capturing the local-global
   property for the Selmer cubic, plus the open conjecture statement.

## Status: 1 axiom (Selmer 1951), 0 sorries

## References
- Selmer, E. (1951). "The Diophantine equation ax³ + by³ + cz³ = 0", Acta Math. 85.
- Manin, Yu. I. (1971). "Le groupe de Brauer-Grothendieck en géométrie diophantienne",
  Actes du Congrès International des Mathématiciens, Nice.
- Colliot-Thélène, J.-L. (2003). "Points rationnels sur les fibrations".
- Skorobogatov, A. N. (2001). "Torsors and Rational Points", Cambridge.
-/

set_option linter.unusedVariables false

namespace Hilbert11OQ02

open Set

/-! ## Section 1: The Selmer Cubic Polynomial -/

/-- The Selmer cubic polynomial: f(x, y, z) = 3x³ + 4y³ + 5z³ over a commutative ring R. -/
def selmerPoly {R : Type*} [CommRing R] (x y z : R) : R :=
  3 * x ^ 3 + 4 * y ^ 3 + 5 * z ^ 3

/-! ## Section 2: Real Solubility (PROVED via IVT) -/

/-- The Selmer cubic 3x³ + 4y³ + 5z³ = 0 has a nontrivial real solution.

    **Construction**: Set y = 1, z = 0. Then we need a real x with 3x³ + 4 = 0, i.e.,
    x³ = -4/3. The function g(x) = 3x³ + 4 satisfies g(-2) = -20 < 0 and g(0) = 4 > 0,
    so the Intermediate Value Theorem gives an x₀ ∈ [-2, 0] with g(x₀) = 0.
    The triple (x₀, 1, 0) is then a nontrivial real solution since the second
    coordinate is 1 ≠ 0.

    This gives the **real solubility** half of the Selmer counterexample concretely;
    combined with axiomatized p-adic solubility, this would witness the Hasse principle
    failure (modulo the deep theorem that there are no rational solutions). -/
theorem selmerCubic_real_solution :
    ∃ (x y z : ℝ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  -- Define g(x) = 3x³ + 4
  let g : ℝ → ℝ := fun x => 3 * x ^ 3 + 4
  have hg_cont : Continuous g := by
    show Continuous (fun x : ℝ => 3 * x ^ 3 + 4)
    fun_prop
  have hg_neg : g (-2) = -20 := by show 3 * (-2 : ℝ) ^ 3 + 4 = -20; norm_num
  have hg_pos : g 0 = 4 := by show 3 * (0 : ℝ) ^ 3 + 4 = 4; norm_num
  have h_le : (-2 : ℝ) ≤ 0 := by norm_num
  have hmem : (0 : ℝ) ∈ Icc (g (-2)) (g 0) := by
    rw [hg_neg, hg_pos]
    exact ⟨by norm_num, by norm_num⟩
  obtain ⟨x₀, _hx_mem, hx_zero⟩ :=
    intermediate_value_Icc h_le hg_cont.continuousOn hmem
  refine ⟨x₀, 1, 0, Or.inr (Or.inl one_ne_zero), ?_⟩
  -- hx_zero : g x₀ = 0, i.e. 3 * x₀^3 + 4 = 0
  -- Goal: selmerPoly x₀ 1 0 = 0
  have hg_eval : g x₀ = 3 * x₀ ^ 3 + 4 := rfl
  have hsum : 3 * x₀ ^ 3 + 4 = 0 := hg_eval ▸ hx_zero
  show 3 * x₀ ^ 3 + 4 * (1 : ℝ) ^ 3 + 5 * (0 : ℝ) ^ 3 = 0
  linear_combination hsum

/-! ## Section 3: Easy Direction of the Hasse Principle (PROVED) -/

/-- **Easy direction over ℝ**: every rational solution of the Selmer cubic gives a real solution.

    Trivial via the embedding ℚ ↪ ℝ. -/
theorem selmer_rat_implies_real
    (h : ∃ (x y z : ℚ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) :
    ∃ (x y z : ℝ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  refine ⟨(x : ℝ), (y : ℝ), (z : ℝ), ?_, ?_⟩
  · rcases hne with hx | hy | hz
    · exact Or.inl (by exact_mod_cast hx)
    · exact Or.inr (Or.inl (by exact_mod_cast hy))
    · exact Or.inr (Or.inr (by exact_mod_cast hz))
  · show (3 : ℝ) * (x : ℝ) ^ 3 + 4 * (y : ℝ) ^ 3 + 5 * (z : ℝ) ^ 3 = 0
    have hcast : (3 : ℝ) * (x : ℝ) ^ 3 + 4 * (y : ℝ) ^ 3 + 5 * (z : ℝ) ^ 3 =
                 (((3 * x ^ 3 + 4 * y ^ 3 + 5 * z ^ 3 : ℚ)) : ℝ) := by
      push_cast; ring
    rw [hcast]
    have hheq : (3 * x ^ 3 + 4 * y ^ 3 + 5 * z ^ 3 : ℚ) = 0 := heq
    rw [hheq]
    norm_num

/-- **Easy direction over ℚₚ**: every rational solution of the Selmer cubic gives a
    p-adic solution. Trivial via the embedding ℚ ↪ ℚₚ. -/
theorem selmer_rat_implies_padic (p : ℕ) [Fact (Nat.Prime p)]
    (h : ∃ (x y z : ℚ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) :
    ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  obtain ⟨x, y, z, hne, heq⟩ := h
  refine ⟨(x : ℚ_[p]), (y : ℚ_[p]), (z : ℚ_[p]), ?_, ?_⟩
  · rcases hne with hx | hy | hz
    · exact Or.inl (by exact_mod_cast hx)
    · exact Or.inr (Or.inl (by exact_mod_cast hy))
    · exact Or.inr (Or.inr (by exact_mod_cast hz))
  · show (3 : ℚ_[p]) * (x : ℚ_[p]) ^ 3 + 4 * (y : ℚ_[p]) ^ 3 + 5 * (z : ℚ_[p]) ^ 3 = 0
    have hcast : (3 : ℚ_[p]) * (x : ℚ_[p]) ^ 3 + 4 * (y : ℚ_[p]) ^ 3 + 5 * (z : ℚ_[p]) ^ 3 =
                 (((3 * x ^ 3 + 4 * y ^ 3 + 5 * z ^ 3 : ℚ)) : ℚ_[p]) := by
      push_cast; ring
    rw [hcast]
    have hheq : (3 * x ^ 3 + 4 * y ^ 3 + 5 * z ^ 3 : ℚ) = 0 := heq
    rw [hheq]
    norm_num

/-! ## Section 4: Selmer's Theorem (Axiomatized) -/

/-- **Selmer's Theorem (1951)**: The cubic 3x³ + 4y³ + 5z³ = 0 has no nontrivial
    rational solutions.

    **Why axiomatized**: Selmer's proof uses:
    - 3-descent on the associated elliptic curve E: y² = x³ - 432·15².
    - Computation of the 3-Selmer group via class field theory of ℚ(ζ₃, ∛15).
    - Local non-existence of certain 3-coverings at the primes 3 and 5.

    These tools are not yet available in Mathlib; the proof would require
    substantial development of the arithmetic of elliptic curves with complex
    multiplication and the theory of Selmer groups.

    Combined with `selmerCubic_real_solution` (proved above) and the standard
    fact that the cubic is solvable over ℚₚ for every prime p (provable via Hensel
    for p ∉ {2, 3, 5}, requiring direct verification at small primes), Selmer's
    theorem establishes the **first known counterexample to the Hasse principle**. -/
axiom selmer_no_rational_solution :
    ¬∃ (x y z : ℚ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0

/-! ## Section 5: The Hasse Principle Predicate -/

/-- The **Hasse principle holds for the Selmer cubic** if rational solubility is
    equivalent to local solubility over ℝ AND over every ℚₚ.

    For the Selmer cubic specifically, the Hasse principle FAILS:
    - Local solubility over ℝ: PROVED (via IVT).
    - Local solubility over ℚₚ: standard (Hensel + small-prime check, axiomatized below).
    - Rational solubility: false by Selmer 1951 (axiomatized above).

    This predicate generalizes naturally to other cubic forms; the open question
    asks for an exact characterization of which cubics satisfy it. -/
def selmerHassePrinciple : Prop :=
  (∃ (x y z : ℚ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ↔
    ((∃ (x y z : ℝ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0)

/-- **Axiom: p-adic solubility of the Selmer cubic** at every prime p.

    For p ∉ {2, 3, 5}, this follows from Hensel's lemma applied to the reduction mod p.
    For p ∈ {2, 3, 5}, direct construction at low precision suffices. The full
    formalization in Lean would require Hensel infrastructure for ℚₚ. -/
axiom selmer_padic_solubility (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0

/-- **Theorem**: The Selmer cubic has local solutions everywhere (real and p-adic).
    This combines the proved `selmerCubic_real_solution` with the axiomatized
    `selmer_padic_solubility`. -/
theorem selmer_locally_soluble_everywhere :
    (∃ (x y z : ℝ), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)],
        ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  ⟨selmerCubic_real_solution, fun p _ => selmer_padic_solubility p⟩

/-- **Theorem**: The Hasse principle FAILS for the Selmer cubic.

    Local solubility holds everywhere (`selmer_locally_soluble_everywhere`), yet there
    is no rational solution (`selmer_no_rational_solution`). This is the famous
    counterexample of Selmer (1951), demonstrating that the local-global principle of
    Hasse-Minkowski does NOT extend from quadratic to cubic forms. -/
theorem selmer_hasse_principle_fails : ¬ selmerHassePrinciple := by
  intro h
  -- h : rational ↔ (real ∧ ∀ p, p-adic)
  -- We have local everywhere (selmer_locally_soluble_everywhere)
  -- but no rational (selmer_no_rational_solution)
  exact selmer_no_rational_solution (h.mpr selmer_locally_soluble_everywhere)

/-! ## Section 6: The Open Question -/

/-- **Open Question (Hilbert 11 OQ-02)**: For which polynomial systems over ℚ does the
    Hasse principle hold?

    For quadratic forms: ALWAYS (Hasse-Minkowski 1923).
    For cubic forms: SOMETIMES — fails for the Selmer cubic.
    In general: governed (conjecturally) by the Brauer-Manin obstruction.

    **Colliot-Thélène's conjecture**: For smooth proper geometrically rationally
    connected varieties X over ℚ, the Brauer-Manin set X(𝔸_ℚ)^{Br(X)} is dense in
    the set of adelic points; equivalently, the Brauer-Manin obstruction is the only
    obstruction to the Hasse principle.

    Known cases of the conjecture:
    - Quadratic forms (no obstruction needed) — Hasse-Minkowski 1923.
    - Conic bundles over ℙ¹ — Colliot-Thélène, Sansuc, Salberger.
    - del Pezzo surfaces of degree ≥ 5.
    - Some Châtelet surfaces.

    Open cases:
    - General cubic surfaces (del Pezzo of degree 3).
    - K3 surfaces.
    - Higher-dimensional Fano varieties.

    **Status**: Predicate `True` (informal statement). Full formal statement requires
    algebraic geometry infrastructure (étale cohomology, Brauer groups of schemes,
    adelic points) not yet in Mathlib. -/
def colliot_thelene_conjecture : Prop := True

/-! ## Section 7: Status Summary -/

/-!
| Component | Status |
|-----------|--------|
| `selmerCubic_real_solution` | **PROVED** (via IVT) |
| `selmer_rat_implies_real` | **PROVED** (via embedding) |
| `selmer_rat_implies_padic` | **PROVED** (via embedding) |
| `selmer_no_rational_solution` | **AXIOMATIZED** (Selmer 1951, deep) |
| `selmer_padic_solubility` | **AXIOMATIZED** (Hensel — could be proved with infrastructure) |
| `selmer_locally_soluble_everywhere` | **PROVED** (from above) |
| `selmer_hasse_principle_fails` | **PROVED** (assuming the two axioms) |
| `colliot_thelene_conjecture` | **DEFINED** (informal, open in general) |

### Axiom count: 2
- `selmer_no_rational_solution` (Selmer 1951)
- `selmer_padic_solubility` (Hensel infrastructure pending)

### Sorry count: 0
-/

/-! ## Section 8: Roadmap for Eliminating `selmer_padic_solubility`

The axiom `selmer_padic_solubility` is *not* a deep theorem — it is a routine
application of Hensel's lemma to the reduction `f̄(x,y,z) = 3x³+4y³+5z³ ∈
F_p[x,y,z]` once a *smooth* mod-p (or, at p = 3, mod-27) zero is known.
The work below catalogues, prime-by-prime, where the smooth zero lives and
which Hensel statement is needed; this turns the universal axiom into a
finite collection of prime-specific lemmas, each closeable with the standard
Mathlib `PadicNumbers`/`PadicInt` Hensel API.

### Decomposition by residue class of p mod 3

**Case A — p ≡ 2 (mod 3), p ∉ {2, 5}** (e.g. p ∈ {11, 17, 23, 29, 41, …}).
Cubing is a bijection on (ℤ/p)*, so for *any* nonzero a ∈ (ℤ/p)* the
equation z³ = a has a unique solution. Take x = 0, y = 1: the equation
reduces to 5z³ + 4 ≡ 0, i.e. z³ ≡ -4·5⁻¹ ∈ (ℤ/p)*, with the unique cube
root in (ℤ/p)*. The derivative ∂_z f = 15z² is nonzero at the root
(since z ≠ 0 mod p and p ∉ {3, 5}), so single-variable Hensel along z
lifts to a unique 3-adic z̃ ∈ ℤ_p with selmerPoly 0 1 z̃ = 0 in ℚ_p.
**Witness data.** p = 11: take z₀ = 2 (since 2³ = 8 ≡ -4·5⁻¹ ≡ -4·9 ≡ 8
mod 11, and ∂_z f(0,1,2) = 60 ≡ 5 ≢ 0 mod 11). p = 17: z₀ = 5.
p = 23: z₀ = 18. p = 29: z₀ = 22.

**Case B — p ≡ 1 (mod 3), p ≥ 7** (e.g. p ∈ {7, 13, 19, 31, 37, 43, …}).
Only one third of (ℤ/p)* are cubes, so the (0, 1, z) projection often
fails (it fails at p = 7, 13, 19, 31 but works at p = 37). Smooth
mod-p zeros nevertheless exist by Hasse-Weil applied to the smooth genus-1
curve {3x³+4y³+5z³ = 0} ⊂ ℙ²_{F_p}: the count of F_p-points lies in the
interval [p+1-2√p, p+1+2√p], which is ≥ 5 for every p ≥ 5. After fixing
two affine coordinates one obtains a polynomial in the third with
nonsingular reduction, and standard univariate Hensel lifts.
**Witness data.** p = 7: smooth zero (1, 1, 0), Jacobian (9, 12, 0) ≡
(2, 5, 0) mod 7 (∂_x and ∂_y both invertible). p = 13: (1, 4, 2). p = 19:
(1, 0, 4). p = 31: (1, 3, 17). p = 37: (0, 1, 5).

### Special primes p ∈ {2, 3, 5}

**p = 2.** The polynomial reduces to x³ + z³ mod 2, with smooth zero
(1, 0, 1) (Jacobian (1, 0, 1) mod 2 has rank ≥ 1). Hensel along z lifts
to a unique 2-adic z̃ ∈ ℤ_2 with selmerPoly 1 0 z̃ = 0 in ℚ_2.

**p = 5.** The polynomial reduces to 3x³ + 4y³ mod 5 (the leading 5 in
the z-coefficient vanishes). Smooth zero (1, 2, 0) since 3 + 4·8 = 35
≡ 0 mod 5 and Jacobian (4, 3, 0) mod 5 is invertible in the (x,y)-plane.
Hensel lifts.

**p = 3.** *Singular reduction.* All of 9, 12, 15 are divisible by 3, so
every mod-3 zero of `selmerPoly` has Jacobian ≡ 0 mod 3 — naive single-
variable Hensel does not lift. We must climb to mod 27 = 3³ before the
strong-form Hensel hypothesis `|f(α)|_p < |f'(α)|_p²` is met. The
witness (0, 1, 4) mod 27 satisfies `selmerPoly 0 1 4 = 4 + 5·64 = 324 =
12·27 ≡ 0 (mod 27)` with `∂_z f(0,1,4) = 15·16 = 240`, valuation
v₃(240) = 1. Since v₃(f) ≥ 3 > 2 · v₃(∂_z f) = 2, strong-form Hensel
applies and lifts to a unique 3-adic z̃ with v₃(z̃ - 4) ≥ 3.

### Status of this roadmap

This section is **documentation only** — no Lean code, no axiom changes,
no proof obligations. The next session can split `selmer_padic_solubility`
into the per-prime lemmas above and discharge each via the recipe given.
The `colliot_thelene_conjecture` placeholder (currently `Prop := True`)
is *not* in scope here; that requires Brauer-Manin / scheme-theoretic
infrastructure not present in Mathlib. -/

#check @selmerCubic_real_solution
#check @selmer_rat_implies_real
#check @selmer_rat_implies_padic
#check @selmer_no_rational_solution
#check @selmer_padic_solubility
#check @selmer_locally_soluble_everywhere
#check @selmer_hasse_principle_fails

end Hilbert11OQ02
