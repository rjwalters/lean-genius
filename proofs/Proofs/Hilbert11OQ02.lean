import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Bornology
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.ZMod.Basic
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
lifts to a unique 3-adic zt ∈ ℤ_p with selmerPoly 0 1 zt = 0 in ℚ_p.
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
to a unique 2-adic zt ∈ ℤ_2 with selmerPoly 1 0 zt = 0 in ℚ_2.

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
applies and lifts to a unique 3-adic zt with v₃(zt - 4) ≥ 3.

### Status of this roadmap

This section is **documentation only** — no Lean code, no axiom changes,
no proof obligations. The next session can split `selmer_padic_solubility`
into the per-prime lemmas above and discharge each via the recipe given.
The `colliot_thelene_conjecture` placeholder (currently `Prop := True`)
is *not* in scope here; that requires Brauer-Manin / scheme-theoretic
infrastructure not present in Mathlib. -/

/-! ## Section 9: Computational Verification of Hensel-Elimination Witnesses

For each prime in the Section 8 roadmap we record the mod-`p` (or mod-27,
for `p = 3`) witness that satisfies `selmerPoly = 0`. The arithmetic check
is by `decide` in `ZMod p`, so each lemma is *machine-verified* — there
is no hand-computation gap between the roadmap text and the
formalization.

Lifting these witnesses to ℚ_p requires Mathlib's Hensel API
(`Mathlib.NumberTheory.Padics.Hensel.hensels_lemma` and friends) and is
left for a future session; the lemmas here are the *inputs* that Hensel
will consume. -/

/-! ### Case A: p ≡ 2 (mod 3), p ∉ {2, 5} — `(0, 1, z₀)` projection -/

/-- Witness for the Selmer cubic at `p = 11`: `(0, 1, 2)` mod 11. -/
theorem selmer_witness_p11 :
    selmerPoly (0 : ZMod 11) 1 2 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 17`: `(0, 1, 5)` mod 17. -/
theorem selmer_witness_p17 :
    selmerPoly (0 : ZMod 17) 1 5 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 23`: `(0, 1, 18)` mod 23. -/
theorem selmer_witness_p23 :
    selmerPoly (0 : ZMod 23) 1 18 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 29`: `(0, 1, 22)` mod 29. -/
theorem selmer_witness_p29 :
    selmerPoly (0 : ZMod 29) 1 22 = 0 := by decide

/-! ### Case B: p ≡ 1 (mod 3), p ≥ 7 — smooth zero from Hasse–Weil bound -/

/-- Witness for the Selmer cubic at `p = 7`: `(1, 1, 0)` mod 7. -/
theorem selmer_witness_p7 :
    selmerPoly (1 : ZMod 7) 1 0 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 13`: `(1, 4, 2)` mod 13. -/
theorem selmer_witness_p13 :
    selmerPoly (1 : ZMod 13) 4 2 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 19`: `(1, 0, 4)` mod 19. -/
theorem selmer_witness_p19 :
    selmerPoly (1 : ZMod 19) 0 4 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 31`: `(1, 3, 17)` mod 31. -/
theorem selmer_witness_p31 :
    selmerPoly (1 : ZMod 31) 3 17 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 37`: `(0, 1, 5)` mod 37. -/
theorem selmer_witness_p37 :
    selmerPoly (0 : ZMod 37) 1 5 = 0 := by decide

/-! ### Special primes p ∈ {2, 5} — direct construction -/

/-- Witness for the Selmer cubic at `p = 2`: `(1, 0, 1)` mod 2. -/
theorem selmer_witness_p2 :
    selmerPoly (1 : ZMod 2) 0 1 = 0 := by decide

/-- Witness for the Selmer cubic at `p = 5`: `(1, 2, 0)` mod 5. -/
theorem selmer_witness_p5 :
    selmerPoly (1 : ZMod 5) 2 0 = 0 := by decide

/-! ### Special prime p = 3 — singular reduction; mod-27 witness -/

/-- Witness for the Selmer cubic at `p = 3` in the mod-27 strong-form
    Hensel sense: `selmerPoly 0 1 4 ≡ 0 (mod 27)`. The mod-3 reduction
    of the Selmer cubic is singular (every coefficient is ≡ 0 mod 3),
    so the witness is recorded mod 27 = 3³ to feed the strong-form
    Hensel hypothesis. See Section 8 for the valuation analysis. -/
theorem selmer_witness_p3_mod27 :
    selmerPoly (0 : ZMod 27) 1 4 = 0 := by decide

/-! ## Section 10: Status Summary (post Section 9) -/

/-!
Section 9 adds 12 named, machine-verified witness lemmas covering every
prime appearing in the Section 8 roadmap. The witnesses are now
*integrated* into the Lean development — not just text in a comment —
and any future per-prime Hensel lift can cite them by name.

### Updated counts
- Theorems: 5 + 12 witness lemmas = 17.
- Substantive theorems (non-`decide` content): 5 (unchanged).
- Definitions: 2 (`selmerPoly`, `selmerHassePrinciple` + `colliot_thelene_conjecture`).
- Sorries: 0 (unchanged).
- Axioms: 2 (unchanged): `selmer_no_rational_solution` + `selmer_padic_solubility`.
- Status: still `axiomatized`. -/

/-! ## Section 11: Hensel-Lifted ℚ_[11] Solubility (Proved, axiom-free)

Section 9 records the mod-11 witness `(0, 1, 2)` for the Selmer cubic. Here
we *lift* the witness to `ℚ_[11]` via Mathlib's univariate Hensel lemma,
producing a fully proved (axiom-free) instance of the
`selmer_padic_solubility` shape for `p = 11`. The argument:

1. Let `Gint(z) = 5z³ + 4 ∈ ℤ[z]` (the univariate polynomial obtained from
   `selmerPoly` by fixing `x = 0, y = 1`).
2. Compute `aeval (2 : ℤ_[11]) Gint = ((44 : ℤ) : ℤ_[11])` and
   `aeval (2 : ℤ_[11]) Gint.derivative = ((60 : ℤ) : ℤ_[11])`.
3. The Hensel hypothesis `‖g(2)‖ < ‖g'(2)‖²` reduces to `1/11 < 1`:
   `(11 : ℤ) ∣ 44` (so `‖44‖_11 < 1`) and `IsCoprime (60 : ℤ) 11`
   (so `‖60‖_11 = 1`).
4. `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma` yields `zt ∈ ℤ_[11]`
   with `5 zt³ + 4 = 0`. Casting `zt ↦ ((zt : ℤ_[11]) : ℚ_[11])` and packaging
   with `(x, y) = (0, 1)` gives a nontrivial `ℚ_[11]`-zero of `selmerPoly`.

This section discharges *one* of the (countably many) prime-specific
obligations encoded in the universal axiom `selmer_padic_solubility` for
the Selmer cubic. The other primes appearing in Section 9
(`p ∈ {2, 5, 7, 13, 17, 19, 23, 29, 31, 37}`) are amenable to the same
recipe with the documented mod-`p` witnesses; the special prime `p = 3`
needs the strong-form Hensel lemma applied to the mod-27 witness. Future
iterations can chain the construction. -/

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

namespace Hensel11

open Polynomial

set_option linter.unusedSimpArgs false

/-- Univariate Selmer polynomial in `z` at `(x, y) = (0, 1)`: `g(z) = 5z³ + 4`,
    over `ℤ` so that `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma` can
    consume it via the canonical `[Algebra ℤ ℤ_[11]]` instance. -/
def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3

private lemma Gint_aeval (a : ℤ_[11]) :
    aeval a Gint = (4 : ℤ_[11]) + (5 : ℤ_[11]) * a ^ 3 := by
  unfold Gint
  simp [aeval_C, aeval_X_pow] <;> ring

private lemma Gint_derivative_aeval (a : ℤ_[11]) :
    aeval a Gint.derivative = (15 : ℤ_[11]) * a ^ 2 := by
  unfold Gint
  simp [derivative_add, derivative_C, derivative_C_mul, derivative_X_pow,
        aeval_C, aeval_X_pow] <;> ring

private lemma Gint_aeval_at_2 :
    aeval (2 : ℤ_[11]) Gint = ((44 : ℤ) : ℤ_[11]) := by
  rw [Gint_aeval]
  push_cast
  ring

private lemma Gint_derivative_aeval_at_2 :
    aeval (2 : ℤ_[11]) Gint.derivative = ((60 : ℤ) : ℤ_[11]) := by
  rw [Gint_derivative_aeval]
  push_cast
  ring

private lemma norm_44_lt_one : ‖((44 : ℤ) : ℤ_[11])‖ < 1 := by
  rw [PadicInt.norm_intCast_lt_one_iff]
  norm_num

private lemma norm_60_eq_one : ‖((60 : ℤ) : ℤ_[11])‖ = 1 := by
  rw [PadicInt.norm_intCast_eq_one_iff]
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by decide)

/-- The Hensel hypothesis `‖g(2)‖ < ‖g'(2)‖²` for `Gint = 5z³ + 4` at `a = 2`,
    over `ℤ_[11]`. Reduces to `1/11 < 1` after `‖44‖ < 1` and `‖60‖ = 1`. -/
lemma hensel_hypothesis :
    ‖aeval (2 : ℤ_[11]) Gint‖ < ‖aeval (2 : ℤ_[11]) Gint.derivative‖ ^ 2 := by
  rw [Gint_aeval_at_2, Gint_derivative_aeval_at_2, norm_60_eq_one, one_pow]
  exact norm_44_lt_one

end Hensel11

/-- **Hensel-lifted `ℚ_[11]` solubility (proved, axiom-free)**.

    The Selmer cubic `3x³ + 4y³ + 5z³ = 0` has a nontrivial solution in
    `ℚ_[11]`, obtained by fixing `(x, y) = (0, 1)` and Hensel-lifting the
    mod-11 witness `z ≡ 2 (mod 11)` (cf. `selmer_witness_p11`) to
    `zt ∈ ℤ_[11] ⊂ ℚ_[11]`.

    This proof uses *only* `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma`
    and the explicit divisibilities `(11 : ℤ) ∣ 44` and `IsCoprime (60 : ℤ) 11`.
    It does NOT depend on the universal axiom `selmer_padic_solubility` and
    so demonstrates that the latter is, in principle, derivable for each
    specific prime appearing in Section 9. -/
theorem selmer_padic_solubility_p11_hensel :
    ∃ (x y z : ℚ_[11]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  obtain ⟨zt, hz_root, _, _, _⟩ := hensels_lemma Hensel11.hensel_hypothesis
  -- hz_root : aeval zt Hensel11.Gint = 0 in ℤ_[11]
  have hz_int : (4 : ℤ_[11]) + 5 * zt ^ 3 = 0 := by
    have heval := Hensel11.Gint_aeval zt
    rw [heval] at hz_root
    exact hz_root
  refine ⟨0, 1, (zt : ℚ_[11]), Or.inr (Or.inl one_ne_zero), ?_⟩
  -- Goal: selmerPoly (0 : ℚ_[11]) 1 (zt : ℚ_[11]) = 0,
  -- i.e., 3·0³ + 4·1³ + 5·((zt : ℚ_[11]))³ = 0.
  have hcast : (4 : ℚ_[11]) + 5 * (zt : ℚ_[11]) ^ 3 = 0 := by
    have h := congrArg (fun w : ℤ_[11] => (w : ℚ_[11])) hz_int
    push_cast at h
    exact h
  show (3 : ℚ_[11]) * (0 : ℚ_[11]) ^ 3 + 4 * (1 : ℚ_[11]) ^ 3 +
        5 * (zt : ℚ_[11]) ^ 3 = 0
  linear_combination hcast

/-! ## Section 12: Status Summary (post Section 11) -/

/-!
Section 11 lifts the mod-11 witness `(0, 1, 2)` to `ℚ_[11]` via Mathlib's
univariate Hensel lemma, producing a fully proved (axiom-free) instance of
the `selmer_padic_solubility` shape for `p = 11`. The general universal
axiom `selmer_padic_solubility` is unchanged — its full elimination would
require analogous Hensel lifts at every prime — but the p = 11 instance is
now derivable without invoking it.

### Updated counts
- Theorems: 17 + 1 (`selmer_padic_solubility_p11_hensel`) = 18.
- Substantive theorems (non-`decide` content): 6.
- Definitions: 2 (`selmerPoly`, `selmerHassePrinciple` + `colliot_thelene_conjecture`)
  plus 1 helper definition `Hensel11.Gint`.
- Sorries: 0 (unchanged).
- Axioms: 2 (unchanged): `selmer_no_rational_solution` + `selmer_padic_solubility`.
- Status: still `axiomatized`.
- New milestone: an axiom-free p-adic solubility instance demonstrates the
  Section 8 roadmap is mechanically realizable. -/

/-! ## Section 13: Parametric Case-A Hensel Lift

Section 11 lifts the Selmer cubic's mod-11 witness `(0, 1, 2)` to `ℚ_[11]` via a
prime-specific Hensel argument. The same argument works *unchanged* for every
Case-A prime (`p ≡ 2 (mod 3)`, `p ∉ {2, 5}`) once the witness `z₀` and the
divisibility data are supplied: the polynomial `g(z) = 5z³ + 4 ∈ ℤ[z]` is the
same for every `p`, and the Hensel hypothesis `‖g(z₀)‖_p < ‖g'(z₀)‖_p^2` reduces
to `(p : ℤ) ∣ (4 + 5·z₀³)` and `IsCoprime (15·z₀² : ℤ) (p : ℤ)`. We package this
as a single parametric theorem and derive the per-prime ℚ_[p] solubility
instances at `p ∈ {17, 23, 29}` as one-line corollaries, mirroring the Section
11 result for `p = 11`. -/

namespace HenselCaseA

open Polynomial

/-- The univariate polynomial `g(z) = 5z³ + 4 ∈ ℤ[z]`, obtained from the Selmer
    cubic by fixing `(x, y) = (0, 1)`. The same polynomial works for every prime;
    only the witness `z₀` and the divisibility data change. -/
def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3

private lemma Gint_derivative_eq : Gint.derivative = C 15 * X ^ 2 := by
  unfold Gint
  rw [derivative_add, derivative_C, zero_add, derivative_C_mul,
      derivative_X_pow]
  push_cast
  ring

private lemma Gint_aeval {p : ℕ} [Fact (Nat.Prime p)] (a : ℤ_[p]) :
    aeval a Gint = (4 : ℤ_[p]) + (5 : ℤ_[p]) * a ^ 3 := by
  unfold Gint
  rw [map_add, map_mul, map_pow, aeval_C, aeval_C, aeval_X]
  push_cast
  ring

private lemma Gint_derivative_aeval {p : ℕ} [Fact (Nat.Prime p)] (a : ℤ_[p]) :
    aeval a Gint.derivative = (15 : ℤ_[p]) * a ^ 2 := by
  rw [Gint_derivative_eq, map_mul, map_pow, aeval_C, aeval_X]
  push_cast
  ring

end HenselCaseA

/-- **Parametric Case-A Hensel lift for the Selmer cubic.**

    For any prime `p` and integer witness `z₀` satisfying
    * `(p : ℤ) ∣ (4 + 5 * z₀^3)` — `(0, 1, z₀)` is a mod-`p` zero of the cubic, and
    * `IsCoprime (15 * z₀^2 : ℤ) (p : ℤ)` — the `z`-derivative of `5z³+4` is
      invertible mod `p`,

    Mathlib's univariate Hensel lemma lifts `z₀` to `zt ∈ ℤ_[p]` with
    `4 + 5·zt^3 = 0`, and then `(0, 1, (zt : ℚ_[p]))` is a nontrivial
    `ℚ_[p]`-zero of the Selmer cubic. This generalizes Section 11 (the
    `p = 11`, `z₀ = 2` case) to every Case-A prime. -/
theorem selmer_padic_solubility_caseA {p : ℕ} [Fact (Nat.Prime p)]
    (z₀ : ℤ)
    (h_root_div : (p : ℤ) ∣ (4 + 5 * z₀ ^ 3))
    (h_deriv_coprime : IsCoprime (15 * z₀ ^ 2 : ℤ) (p : ℤ)) :
    ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  have h_aeval :
      aeval ((z₀ : ℤ_[p])) HenselCaseA.Gint =
        (((4 + 5 * z₀ ^ 3 : ℤ)) : ℤ_[p]) := by
    rw [HenselCaseA.Gint_aeval]
    push_cast
    ring
  have h_deriv :
      aeval ((z₀ : ℤ_[p])) HenselCaseA.Gint.derivative =
        (((15 * z₀ ^ 2 : ℤ)) : ℤ_[p]) := by
    rw [HenselCaseA.Gint_derivative_aeval]
    push_cast
    ring
  have h_norm_root :
      ‖aeval ((z₀ : ℤ_[p])) HenselCaseA.Gint‖ < 1 := by
    rw [h_aeval, PadicInt.norm_intCast_lt_one_iff]
    exact_mod_cast h_root_div
  have h_norm_deriv :
      ‖aeval ((z₀ : ℤ_[p])) HenselCaseA.Gint.derivative‖ = 1 := by
    rw [h_deriv, PadicInt.norm_intCast_eq_one_iff]
    exact h_deriv_coprime
  have h_hensel :
      ‖aeval ((z₀ : ℤ_[p])) HenselCaseA.Gint‖ <
        ‖aeval ((z₀ : ℤ_[p])) HenselCaseA.Gint.derivative‖ ^ 2 := by
    rw [h_norm_deriv, one_pow]
    exact h_norm_root
  obtain ⟨zt, hz_root, _, _, _⟩ := hensels_lemma h_hensel
  have hz_int : (4 : ℤ_[p]) + 5 * zt ^ 3 = 0 := by
    have heval := HenselCaseA.Gint_aeval zt
    rw [heval] at hz_root
    exact hz_root
  refine ⟨0, 1, (zt : ℚ_[p]), Or.inr (Or.inl one_ne_zero), ?_⟩
  have hcast : (4 : ℚ_[p]) + 5 * (zt : ℚ_[p]) ^ 3 = 0 := by
    have h := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hz_int
    push_cast at h
    exact h
  show (3 : ℚ_[p]) * (0 : ℚ_[p]) ^ 3 + 4 * (1 : ℚ_[p]) ^ 3 +
        5 * (zt : ℚ_[p]) ^ 3 = 0
  linear_combination hcast

instance : Fact (Nat.Prime 17) := ⟨by decide⟩
instance : Fact (Nat.Prime 23) := ⟨by decide⟩
instance : Fact (Nat.Prime 29) := ⟨by decide⟩

/-- ℚ_[17] solubility of the Selmer cubic: `(0, 1, zt)` for `zt` lifting
    `5 mod 17`. Routine corollary of `selmer_padic_solubility_caseA`; the
    witness data `17 ∣ 4 + 5·5³ = 629 = 17·37` and `gcd(15·5², 17) = gcd(375, 17)
    = 1` are decidable. -/
theorem selmer_padic_solubility_p17_hensel :
    ∃ (x y z : ℚ_[17]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 5
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[23] solubility of the Selmer cubic: `(0, 1, zt)` for `zt` lifting
    `18 mod 23`. Witness data: `23 ∣ 4 + 5·18³ = 29164 = 23·1268` and
    `gcd(15·18², 23) = gcd(4860, 23) = 1`. -/
theorem selmer_padic_solubility_p23_hensel :
    ∃ (x y z : ℚ_[23]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 18
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[29] solubility of the Selmer cubic: `(0, 1, zt)` for `zt` lifting
    `22 mod 29`. Witness data: `29 ∣ 4 + 5·22³ = 53244 = 29·1836` and
    `gcd(15·22², 29) = gcd(7260, 29) = 1`. -/
theorem selmer_padic_solubility_p29_hensel :
    ∃ (x y z : ℚ_[29]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 22
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-! ## Section 14: Status Summary (post Section 13) -/

/-!
Section 13 generalizes the Section 11 Hensel argument to every Case-A prime,
then uses the parametric theorem to discharge the `p = 17, 23, 29` instances of
`selmer_padic_solubility` in three one-line corollaries. The universal axiom
`selmer_padic_solubility` remains — full elimination requires also handling
Case B primes (`p ≡ 1 mod 3`, `p ≥ 7`) and the special primes `p ∈ {2, 3, 5}`
— but each iteration that adds an axiom-free Hensel lift makes the universal
axiom less load-bearing in practice.

### Updated counts
- Theorems: 18 + 1 (`selmer_padic_solubility_caseA`) + 3 (per-prime corollaries)
  = 22.
- Substantive theorems (non-`decide` content): 7 (was 6).
- Definitions: 4 + 1 (`HenselCaseA.Gint`) = 5.
- Sorries: 0 (unchanged).
- Axioms: 2 (unchanged): `selmer_no_rational_solution` + `selmer_padic_solubility`.
- Status: still `axiomatized`.
- New milestone: parametric Case-A theorem turns per-prime Hensel lifts into
  single-line corollaries; the four Case-A primes from Section 9
  (`p ∈ {11, 17, 23, 29}`) all admit axiom-free `ℚ_[p]`-solubility proofs. -/

/-! ## Section 15: General Lift-z Hensel Theorem (Case-B subset)

Section 13's `selmer_padic_solubility_caseA` lifts the `(0, 1, z)` projection of
the Selmer cubic, covering primes whose Section 9 witness has the `(0, 1, z₀)`
shape (`p ∈ {11, 17, 23, 29}`). Several Case-B primes
(`p ≡ 1 (mod 3)`, `p ≥ 7`) admit different witness shapes, but for many of them
the *same kind* of lift — fixing `(x, y) = (x₀, y₀) ∈ ℤ²` and Hensel-lifting `z`
— still works, with a coefficient `c = 3·x₀³ + 4·y₀³` substituting for the bare
constant `4` of Section 13.

This section states the fully general lift-z theorem
`selmer_padic_solubility_lift_z` and discharges the Case-B primes
`p ∈ {13, 19, 31, 37}` as one-line corollaries. The remaining Case-B prime
`p = 7` has Section-9 witness `(1, 1, 0)` with `z₀ = 0`, so the
`IsCoprime (15·0² : ℤ) (7 : ℤ) = IsCoprime 0 7` hypothesis fails: lift-z is
unavailable at `p = 7` and a complementary lift-x parametric theorem is needed
in a later iteration. -/

namespace HenselLiftZ

open Polynomial

/-- The univariate polynomial `G(z) = c + 5z³ ∈ ℤ[z]`, parametric in the
    constant term `c`. Specialized to `c = 3·x₀³ + 4·y₀³` it becomes the
    Selmer cubic with the `(x, y) = (x₀, y₀)` projection.
    `Section 13.HenselCaseA.Gint` is exactly `G 4` (the `(0, 1, z)` slice). -/
def G (c : ℤ) : Polynomial ℤ := C c + C 5 * X ^ 3

private lemma G_derivative_eq (c : ℤ) : (G c).derivative = C 15 * X ^ 2 := by
  unfold G
  rw [derivative_add, derivative_C, zero_add, derivative_C_mul,
      derivative_X_pow]
  push_cast
  ring

private lemma G_aeval {p : ℕ} [Fact (Nat.Prime p)] (c : ℤ) (a : ℤ_[p]) :
    aeval a (G c) = (c : ℤ_[p]) + (5 : ℤ_[p]) * a ^ 3 := by
  unfold G
  rw [map_add, map_mul, map_pow, aeval_C, aeval_C, aeval_X]
  push_cast
  ring

private lemma G_derivative_aeval {p : ℕ} [Fact (Nat.Prime p)] (c : ℤ) (a : ℤ_[p]) :
    aeval a (G c).derivative = (15 : ℤ_[p]) * a ^ 2 := by
  rw [G_derivative_eq, map_mul, map_pow, aeval_C, aeval_X]
  push_cast
  ring

end HenselLiftZ

/-- **General lift-z Hensel theorem for the Selmer cubic.**

    For any prime `p`, integer triple `(x₀, y₀, z₀)` with `(x₀, y₀) ≠ (0, 0)`,
    and divisibility hypotheses
    * `(p : ℤ) ∣ (3·x₀³ + 4·y₀³ + 5·z₀³)` — `(x₀, y₀, z₀)` is a mod-`p` zero
      of the Selmer cubic,
    * `IsCoprime (15·z₀² : ℤ) (p : ℤ)` — the `z`-derivative
      `∂_z(3x³+4y³+5z³) = 15z²` is invertible mod `p` at `z₀`,

    Mathlib's univariate Hensel lemma applied to
    `HenselLiftZ.G (3·x₀³ + 4·y₀³)` lifts `z₀` to `zt ∈ ℤ_[p]` satisfying
    `(3·x₀³ + 4·y₀³) + 5·zt³ = 0`. The triple
    `((x₀ : ℚ_[p]), (y₀ : ℚ_[p]), (zt : ℚ_[p]))` is then a nontrivial
    `ℚ_[p]`-zero of the Selmer cubic.

    This generalizes Section 13's `selmer_padic_solubility_caseA` (which fixes
    `x₀ = 0, y₀ = 1`) to any integer projection that fixes the `z`-coordinate
    last. It dispatches Section 9's Case-B primes whose witness has nonzero
    `z₀`: `p ∈ {13, 19, 31, 37}`. The Case-B prime `p = 7` has `z₀ = 0` and
    is *not* covered (the coprimality hypothesis fails); a complementary
    lift-x theorem is left for a future iteration. -/
theorem selmer_padic_solubility_lift_z {p : ℕ} [Fact (Nat.Prime p)]
    (x₀ y₀ z₀ : ℤ)
    (h_xy_nontriv : x₀ ≠ 0 ∨ y₀ ≠ 0)
    (h_root_div : (p : ℤ) ∣ (3 * x₀ ^ 3 + 4 * y₀ ^ 3 + 5 * z₀ ^ 3))
    (h_deriv_coprime : IsCoprime (15 * z₀ ^ 2 : ℤ) (p : ℤ)) :
    ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  set c : ℤ := 3 * x₀ ^ 3 + 4 * y₀ ^ 3 with hc_def
  have h_c_plus : c + 5 * z₀ ^ 3 = 3 * x₀ ^ 3 + 4 * y₀ ^ 3 + 5 * z₀ ^ 3 := by
    rw [hc_def]
  have h_div_total : (p : ℤ) ∣ (c + 5 * z₀ ^ 3) := by
    rw [h_c_plus]; exact h_root_div
  have h_aeval :
      aeval ((z₀ : ℤ_[p])) (HenselLiftZ.G c) =
        (((c + 5 * z₀ ^ 3 : ℤ)) : ℤ_[p]) := by
    rw [HenselLiftZ.G_aeval]
    push_cast
    ring
  have h_deriv :
      aeval ((z₀ : ℤ_[p])) (HenselLiftZ.G c).derivative =
        (((15 * z₀ ^ 2 : ℤ)) : ℤ_[p]) := by
    rw [HenselLiftZ.G_derivative_aeval]
    push_cast
    ring
  have h_norm_root :
      ‖aeval ((z₀ : ℤ_[p])) (HenselLiftZ.G c)‖ < 1 := by
    rw [h_aeval, PadicInt.norm_intCast_lt_one_iff]
    exact_mod_cast h_div_total
  have h_norm_deriv :
      ‖aeval ((z₀ : ℤ_[p])) (HenselLiftZ.G c).derivative‖ = 1 := by
    rw [h_deriv, PadicInt.norm_intCast_eq_one_iff]
    exact h_deriv_coprime
  have h_hensel :
      ‖aeval ((z₀ : ℤ_[p])) (HenselLiftZ.G c)‖ <
        ‖aeval ((z₀ : ℤ_[p])) (HenselLiftZ.G c).derivative‖ ^ 2 := by
    rw [h_norm_deriv, one_pow]
    exact h_norm_root
  obtain ⟨zt, hz_root, _, _, _⟩ := hensels_lemma h_hensel
  have hz_int : (c : ℤ_[p]) + 5 * zt ^ 3 = 0 := by
    have heval := HenselLiftZ.G_aeval c zt
    rw [heval] at hz_root
    exact hz_root
  refine ⟨(x₀ : ℚ_[p]), (y₀ : ℚ_[p]), (zt : ℚ_[p]), ?_, ?_⟩
  · -- Nontriviality from `(x₀, y₀) ≠ (0, 0)` (using injectivity of ℤ → ℚ_[p]).
    rcases h_xy_nontriv with hx | hy
    · left
      exact_mod_cast hx
    · right; left
      exact_mod_cast hy
  · -- selmerPoly value: 3·x₀³ + 4·y₀³ + 5·zt³ = c + 5·zt³ = 0.
    have hcast_zint : (c : ℚ_[p]) + 5 * (zt : ℚ_[p]) ^ 3 = 0 := by
      have h := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hz_int
      push_cast at h
      exact h
    have h_c_cast :
        ((c : ℤ) : ℚ_[p]) =
          (3 : ℚ_[p]) * (x₀ : ℚ_[p]) ^ 3 + 4 * (y₀ : ℚ_[p]) ^ 3 := by
      rw [hc_def]
      push_cast
      ring
    show (3 : ℚ_[p]) * (x₀ : ℚ_[p]) ^ 3 + 4 * (y₀ : ℚ_[p]) ^ 3 +
          5 * (zt : ℚ_[p]) ^ 3 = 0
    linear_combination hcast_zint - h_c_cast

instance : Fact (Nat.Prime 13) := ⟨by decide⟩
instance : Fact (Nat.Prime 19) := ⟨by decide⟩
instance : Fact (Nat.Prime 31) := ⟨by decide⟩
instance : Fact (Nat.Prime 37) := ⟨by decide⟩

/-- ℚ_[13] solubility of the Selmer cubic via the `(1, 4, 2)` Case-B witness
    (cf. `selmer_witness_p13`). Routine corollary of
    `selmer_padic_solubility_lift_z`; the witness data
    `13 ∣ 3·1 + 4·4³ + 5·2³ = 299 = 13·23` and
    `gcd(15·2², 13) = gcd(60, 13) = 1` are decidable. -/
theorem selmer_padic_solubility_p13_hensel :
    ∃ (x y z : ℚ_[13]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_z 1 4 2
    (Or.inl one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[19] solubility of the Selmer cubic via the `(1, 0, 4)` Case-B witness
    (cf. `selmer_witness_p19`). Witness data:
    `19 ∣ 3·1 + 0 + 5·4³ = 323 = 19·17` and
    `gcd(15·4², 19) = gcd(240, 19) = 1`. -/
theorem selmer_padic_solubility_p19_hensel :
    ∃ (x y z : ℚ_[19]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_z 1 0 4
    (Or.inl one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[31] solubility of the Selmer cubic via the `(1, 3, 17)` Case-B witness
    (cf. `selmer_witness_p31`). Witness data:
    `31 ∣ 3·1 + 4·3³ + 5·17³ = 24676 = 31·796` and
    `gcd(15·17², 31) = gcd(4335, 31) = 1`. -/
theorem selmer_padic_solubility_p31_hensel :
    ∃ (x y z : ℚ_[31]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_z 1 3 17
    (Or.inl one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[37] solubility of the Selmer cubic via the `(0, 1, 5)` Case-B witness
    (cf. `selmer_witness_p37`). Although `p = 37` belongs nominally to Case B
    (`37 ≡ 1 mod 3`), its Section-9 witness has the same `(0, 1, z₀)` shape as
    the Case-A primes, so `selmer_padic_solubility_caseA 5` would also work.
    Stating it through `selmer_padic_solubility_lift_z` keeps the dispatch
    table uniform across `p ∈ {13, 19, 31, 37}`. Witness data:
    `37 ∣ 0 + 4 + 5·5³ = 629 = 37·17` and
    `gcd(15·5², 37) = gcd(375, 37) = 1`. -/
theorem selmer_padic_solubility_p37_hensel :
    ∃ (x y z : ℚ_[37]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_z 0 1 5
    (Or.inr one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-! ## Section 16: Iteration 8 — Lift-x Parametric Hensel for p = 7

Iteration 8 mirrors Section 15's `selmer_padic_solubility_lift_z` with the
roles of `x` and `z` swapped: instead of fixing `(x₀, y₀)` and Hensel-lifting
`z`, we fix `(y₀, z₀)` and Hensel-lift `x`. The univariate polynomial is
`H(x) = c + 3x³ ∈ ℤ[X]` parametric in the constant term `c = 4·y₀³ + 5·z₀³`,
with derivative `H'(x) = 9x² ∈ ℤ[X]`. The Hensel hypotheses become:

- `(p : ℤ) ∣ (3·x₀³ + 4·y₀³ + 5·z₀³)` — same as lift-z, the global root condition.
- `IsCoprime (9·x₀² : ℤ) (p : ℤ)` — derivative invertible mod p (≠ derivative of lift-z).
- `(y₀, z₀) ≠ (0, 0)` — non-triviality of the post-lift solution.

Single corollary at `p = 7` via `(x₀, y₀, z₀) = (1, 1, 0)`:
- `7 ∣ 3·1 + 4·1 + 0 = 7` (`decide`-verified).
- `gcd(9·1², 7) = gcd(9, 7) = 1` (`decide`-verified).
- `(1, 0) ≠ (0, 0)` via `Or.inl one_ne_zero`.

This completes the Section 9 Case-B prime sweep (`p ∈ {7, 13, 19, 31, 37}` —
the four lift-z primes plus `p = 7` via lift-x), leaving only the special
primes `p ∈ {2, 3, 5}` blocked on direct construction (p ∈ {2, 5}) and the
singular-reduction strong-form Hensel (p = 3). -/

namespace HenselLiftX

open Polynomial

/-- The univariate polynomial `H(x) = c + 3x³ ∈ ℤ[x]`, parametric in the
    constant term `c`. Specialized to `c = 4·y₀³ + 5·z₀³` it becomes the
    Selmer cubic with the `(y, z) = (y₀, z₀)` projection. -/
def H (c : ℤ) : Polynomial ℤ := C c + C 3 * X ^ 3

private lemma H_derivative_eq (c : ℤ) : (H c).derivative = C 9 * X ^ 2 := by
  unfold H
  rw [derivative_add, derivative_C, zero_add, derivative_C_mul,
      derivative_X_pow]
  push_cast
  ring

private lemma H_aeval {p : ℕ} [Fact (Nat.Prime p)] (c : ℤ) (a : ℤ_[p]) :
    aeval a (H c) = (c : ℤ_[p]) + (3 : ℤ_[p]) * a ^ 3 := by
  unfold H
  rw [map_add, map_mul, map_pow, aeval_C, aeval_C, aeval_X]
  push_cast
  ring

private lemma H_derivative_aeval {p : ℕ} [Fact (Nat.Prime p)] (c : ℤ) (a : ℤ_[p]) :
    aeval a (H c).derivative = (9 : ℤ_[p]) * a ^ 2 := by
  rw [H_derivative_eq, map_mul, map_pow, aeval_C, aeval_X]
  push_cast
  ring

end HenselLiftX

/-- **General lift-x Hensel theorem for the Selmer cubic.**

    Mirror of Section 15's `selmer_padic_solubility_lift_z` with the roles
    of `x` and `z` swapped. Given a triple `(x₀, y₀, z₀) : ℤ³` with
    `(y₀, z₀) ≠ (0, 0)`, `(p : ℤ) ∣ selmerPoly_int x₀ y₀ z₀`, and
    `IsCoprime (9·x₀² : ℤ) (p : ℤ)`, the polynomial
    `HenselLiftX.H c = C c + C 3 * X^3` (where `c = 4·y₀³ + 5·z₀³`) lifts
    `x₀` to `xt ∈ ℤ_[p]` satisfying `c + 3·xt³ = 0`. The Selmer cubic in
    `ℚ_[p]` then has the solution `(xt, y₀, z₀) ≠ (0, 0, 0)` (nontriviality
    from `(y₀, z₀) ≠ (0, 0)`).

    This complements `selmer_padic_solubility_lift_z` and dispatches the
    Section-9 Case-B prime `p = 7` whose witness `(1, 1, 0)` has `z₀ = 0`. -/
theorem selmer_padic_solubility_lift_x {p : ℕ} [Fact (Nat.Prime p)]
    (x₀ y₀ z₀ : ℤ)
    (h_yz_nontriv : y₀ ≠ 0 ∨ z₀ ≠ 0)
    (h_root_div : (p : ℤ) ∣ (3 * x₀ ^ 3 + 4 * y₀ ^ 3 + 5 * z₀ ^ 3))
    (h_deriv_coprime : IsCoprime (9 * x₀ ^ 2 : ℤ) (p : ℤ)) :
    ∃ (x y z : ℚ_[p]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  set c : ℤ := 4 * y₀ ^ 3 + 5 * z₀ ^ 3 with hc_def
  have h_c_plus : c + 3 * x₀ ^ 3 = 3 * x₀ ^ 3 + 4 * y₀ ^ 3 + 5 * z₀ ^ 3 := by
    rw [hc_def]; ring
  have h_div_total : (p : ℤ) ∣ (c + 3 * x₀ ^ 3) := by
    rw [h_c_plus]; exact h_root_div
  have h_aeval :
      aeval ((x₀ : ℤ_[p])) (HenselLiftX.H c) =
        (((c + 3 * x₀ ^ 3 : ℤ)) : ℤ_[p]) := by
    rw [HenselLiftX.H_aeval]
    push_cast
    ring
  have h_deriv :
      aeval ((x₀ : ℤ_[p])) (HenselLiftX.H c).derivative =
        (((9 * x₀ ^ 2 : ℤ)) : ℤ_[p]) := by
    rw [HenselLiftX.H_derivative_aeval]
    push_cast
    ring
  have h_norm_root :
      ‖aeval ((x₀ : ℤ_[p])) (HenselLiftX.H c)‖ < 1 := by
    rw [h_aeval, PadicInt.norm_intCast_lt_one_iff]
    exact_mod_cast h_div_total
  have h_norm_deriv :
      ‖aeval ((x₀ : ℤ_[p])) (HenselLiftX.H c).derivative‖ = 1 := by
    rw [h_deriv, PadicInt.norm_intCast_eq_one_iff]
    exact h_deriv_coprime
  have h_hensel :
      ‖aeval ((x₀ : ℤ_[p])) (HenselLiftX.H c)‖ <
        ‖aeval ((x₀ : ℤ_[p])) (HenselLiftX.H c).derivative‖ ^ 2 := by
    rw [h_norm_deriv, one_pow]
    exact h_norm_root
  obtain ⟨xt, hx_root, _, _, _⟩ := hensels_lemma h_hensel
  have hx_int : (c : ℤ_[p]) + 3 * xt ^ 3 = 0 := by
    have heval := HenselLiftX.H_aeval c xt
    rw [heval] at hx_root
    exact hx_root
  refine ⟨(xt : ℚ_[p]), (y₀ : ℚ_[p]), (z₀ : ℚ_[p]), ?_, ?_⟩
  · -- Nontriviality from `(y₀, z₀) ≠ (0, 0)` (using injectivity of ℤ → ℚ_[p]).
    rcases h_yz_nontriv with hy | hz
    · right; left
      exact_mod_cast hy
    · right; right
      exact_mod_cast hz
  · -- selmerPoly value: 3·xt³ + 4·y₀³ + 5·z₀³ = (c + 3·xt³) = 0.
    have hcast_xint : (c : ℚ_[p]) + 3 * (xt : ℚ_[p]) ^ 3 = 0 := by
      have h := congrArg (fun w : ℤ_[p] => (w : ℚ_[p])) hx_int
      push_cast at h
      exact h
    have h_c_cast :
        ((c : ℤ) : ℚ_[p]) =
          (4 : ℚ_[p]) * (y₀ : ℚ_[p]) ^ 3 + 5 * (z₀ : ℚ_[p]) ^ 3 := by
      rw [hc_def]
      push_cast
      ring
    show (3 : ℚ_[p]) * (xt : ℚ_[p]) ^ 3 + 4 * (y₀ : ℚ_[p]) ^ 3 +
          5 * (z₀ : ℚ_[p]) ^ 3 = 0
    linear_combination hcast_xint - h_c_cast

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- ℚ_[7] solubility of the Selmer cubic via the `(1, 1, 0)` Case-B witness
    (cf. `selmer_witness_p7`). Routine corollary of
    `selmer_padic_solubility_lift_x`; the witness data
    `7 ∣ 3·1 + 4·1 + 5·0 = 7 = 7·1` and
    `gcd(9·1², 7) = gcd(9, 7) = 1` are decidable.

    This is the **last** Case-B prime to be axiom-free; combined with
    `selmer_padic_solubility_lift_z` for `p ∈ {13, 19, 31, 37}` and the
    Section 11 standalone proof for `p = 11`, all five Case-B primes from
    Section 9 are now Hensel-lifted. -/
theorem selmer_padic_solubility_p7_hensel :
    ∃ (x y z : ℚ_[7]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_x 1 1 0
    (Or.inl one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-! ## Section 17: Iteration 9 — Special primes p ∈ {2, 5} via lift-x

Iteration 9 dispatches the two "non-singular" special primes left in the
Section 8 roadmap by reusing the parametric `selmer_padic_solubility_lift_x`
of Section 16. Both Section-9 witnesses for `p = 2` and `p = 5` keep `x₀ = 1`,
so the lift-x derivative `9·x₀² = 9` is automatically coprime to either prime
(`gcd(9, 2) = gcd(9, 5) = 1`); the only per-prime arithmetic is the global
divisibility check.

- `p = 2`, witness `(1, 0, 1)`: `2 ∣ 3·1 + 0 + 5·1 = 8 = 2·4`,
  `gcd(9·1², 2) = 1`, nontriviality from `z₀ = 1 ≠ 0` via `Or.inr one_ne_zero`.
- `p = 5`, witness `(1, 2, 0)`: `5 ∣ 3·1 + 4·8 + 0 = 35 = 5·7`,
  `gcd(9·1², 5) = 1`, nontriviality from `y₀ = 2 ≠ 0` via `Or.inl (by decide)`.

Combined with Sections 11–16, **eleven of the twelve** Section-8 primes
(`p ∈ {2, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`) now admit axiom-free
`ℚ_[p]`-solubility proofs. The only prime still missing is `p = 3`, which
has singular reduction (every coefficient of `selmerPoly`'s Jacobian is
divisible by 3) and requires the strong-form Hensel lemma on the mod-27
witness `selmer_witness_p3_mod27 = (0, 1, 4)`. -/

instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- ℚ_[2] solubility of the Selmer cubic via the `(1, 0, 1)` witness
    (cf. `selmer_witness_p2`). Routine corollary of
    `selmer_padic_solubility_lift_x`; the witness data
    `2 ∣ 3·1 + 4·0 + 5·1 = 8` and `gcd(9·1², 2) = gcd(9, 2) = 1`
    are decidable. Nontriviality uses `z₀ = 1 ≠ 0`. -/
theorem selmer_padic_solubility_p2_hensel :
    ∃ (x y z : ℚ_[2]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_x 1 0 1
    (Or.inr one_ne_zero)
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[5] solubility of the Selmer cubic via the `(1, 2, 0)` witness
    (cf. `selmer_witness_p5`). Routine corollary of
    `selmer_padic_solubility_lift_x`; the witness data
    `5 ∣ 3·1 + 4·8 + 5·0 = 35 = 5·7` and `gcd(9·1², 5) = gcd(9, 5) = 1`
    are decidable. Nontriviality uses `y₀ = 2 ≠ 0`. -/
theorem selmer_padic_solubility_p5_hensel :
    ∃ (x y z : ℚ_[5]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_lift_x 1 2 0
    (Or.inl (by decide))
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-! ## Section 18: Status Summary (post Section 17) -/

/-!
Section 17 dispatches the two non-singular special primes `p ∈ {2, 5}` as
one-line corollaries of `selmer_padic_solubility_lift_x`, leveraging the
shared `x₀ = 1` choice in both Section-9 witnesses. The universal axiom
`selmer_padic_solubility` remains load-bearing, but **eleven of the twelve**
primes in the Section 8 roadmap now admit axiom-free `ℚ_[p]`-solubility
proofs.

### Updated counts (post Section 17)
- Theorems: 29 (post-Section 16) + 2 (`selmer_padic_solubility_p2_hensel`,
  `selmer_padic_solubility_p5_hensel`) = 31.
- Substantive theorems (non-`decide` content): 9 (unchanged — both new
  theorems are one-line corollaries that consume `decide`-verified data).
- Definitions: 7 (unchanged — both corollaries reuse `HenselLiftX.H`).
- Sorries: 0 (unchanged).
- Axioms: 2 (unchanged): `selmer_no_rational_solution` + `selmer_padic_solubility`.
- Status: still `axiomatized`.
- New milestone: lift-x dispatches the two non-singular special primes
  `p ∈ {2, 5}`; eleven of the twelve Section-8 primes
  (`p ∈ {2, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`) now admit axiom-free
  `ℚ_[p]`-solubility proofs.
- Remaining: `p = 3` only (singular reduction; requires strong-form Hensel
  on `selmer_witness_p3_mod27`). -/

/-! ## Section 19: Iteration 10 — Special prime `p = 3` via strong-form Hensel

Iteration 10 dispatches the **last** Section-8 prime — the singular case
`p = 3` — by feeding the mod-27 witness `selmer_witness_p3_mod27 = (0, 1, 4)`
to Mathlib's `hensels_lemma`. Although the mod-3 reduction of `selmerPoly`
is singular (every coefficient `9, 12, 15` of the Jacobian is divisible by
`3`), `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma` is in fact the
*strong-form* statement `‖f(α)‖ < ‖f'(α)‖²`, and the strong-form
hypothesis is satisfied at the mod-27 lift `a = 4 ∈ ℤ_[3]`.

The univariate polynomial is the same as Section 11: `Gint(z) = 5z³ + 4`,
matching the projection `(x, y) = (0, 1)`.

- `Gint(4) = 5·64 + 4 = 324 = 3⁴ · 4`, so `‖Gint(4)‖_3 = (1/3)⁴ = 1/81`.
- `Gint'(4) = 15·16 = 240 = 3 · 80`, so `‖Gint'(4)‖_3 = 1/3` and
  `‖Gint'(4)‖_3² = 1/9`.
- `1/81 < 1/9` ✓ — the strong-form Hensel hypothesis holds.

This dispatches the **twelfth and final** Section-8 prime. All twelve
primes (`p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`) now admit
axiom-free `ℚ_[p]`-solubility proofs. The universal axiom
`selmer_padic_solubility` remains as the only "all primes" closure
assumption — but it is no longer load-bearing for *any* specific prime
in the Section-8 roadmap, only for the meta-claim that the per-prime
recipe extends uniformly over the (countably infinite) set of all
primes. -/

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

namespace Hensel3

open Polynomial

set_option linter.unusedSimpArgs false

/-- Univariate Selmer polynomial in `z` at `(x, y) = (0, 1)`: `g(z) = 5z³ + 4`,
    over `ℤ` (same polynomial as `Hensel11.Gint`). -/
def Gint : Polynomial ℤ := C 4 + C 5 * X ^ 3

private lemma Gint_aeval (a : ℤ_[3]) :
    aeval a Gint = (4 : ℤ_[3]) + (5 : ℤ_[3]) * a ^ 3 := by
  unfold Gint
  simp [aeval_C, aeval_X_pow] <;> ring

private lemma Gint_derivative_aeval (a : ℤ_[3]) :
    aeval a Gint.derivative = (15 : ℤ_[3]) * a ^ 2 := by
  unfold Gint
  simp [derivative_add, derivative_C, derivative_C_mul, derivative_X_pow,
        aeval_C, aeval_X_pow] <;> ring

private lemma Gint_aeval_at_4 :
    aeval (4 : ℤ_[3]) Gint = ((324 : ℤ) : ℤ_[3]) := by
  rw [Gint_aeval]
  push_cast
  ring

private lemma Gint_derivative_aeval_at_4 :
    aeval (4 : ℤ_[3]) Gint.derivative = ((240 : ℤ) : ℤ_[3]) := by
  rw [Gint_derivative_aeval]
  push_cast
  ring

/-- Multiplicative factorization `324 = 3⁴ · 4` in `ℤ_[3]`. -/
private lemma cast_324_factored :
    ((324 : ℤ) : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) ^ 4 * ((4 : ℤ) : ℤ_[3]) := by
  push_cast
  ring

/-- Multiplicative factorization `240 = 3 · 80` in `ℤ_[3]`. -/
private lemma cast_240_factored :
    ((240 : ℤ) : ℤ_[3]) = ((3 : ℕ) : ℤ_[3]) * ((80 : ℤ) : ℤ_[3]) := by
  push_cast
  ring

private lemma norm_4_eq_one : ‖((4 : ℤ) : ℤ_[3])‖ = 1 := by
  rw [PadicInt.norm_intCast_eq_one_iff]
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by decide)

private lemma norm_80_eq_one : ‖((80 : ℤ) : ℤ_[3])‖ = 1 := by
  rw [PadicInt.norm_intCast_eq_one_iff]
  exact Int.isCoprime_iff_gcd_eq_one.mpr (by decide)

/-- `‖324‖_3 = (1/3)⁴ = 1/81`. -/
private lemma norm_324_eq :
    ‖((324 : ℤ) : ℤ_[3])‖ = ((3 : ℕ) : ℝ)⁻¹ ^ 4 := by
  rw [cast_324_factored, PadicInt.norm_mul, PadicInt.norm_pow,
      PadicInt.norm_p, norm_4_eq_one, mul_one]

/-- `‖240‖_3 = 1/3`. -/
private lemma norm_240_eq :
    ‖((240 : ℤ) : ℤ_[3])‖ = ((3 : ℕ) : ℝ)⁻¹ := by
  rw [cast_240_factored, PadicInt.norm_mul, PadicInt.norm_p,
      norm_80_eq_one, mul_one]

/-- The strong-form Hensel hypothesis `‖g(4)‖ < ‖g'(4)‖²` for
    `Gint = 5z³ + 4` at `a = 4`, over `ℤ_[3]`. Reduces to
    `(1/3)⁴ < (1/3)²`, i.e., `1/81 < 1/9`. -/
lemma hensel_hypothesis :
    ‖aeval (4 : ℤ_[3]) Gint‖ < ‖aeval (4 : ℤ_[3]) Gint.derivative‖ ^ 2 := by
  rw [Gint_aeval_at_4, Gint_derivative_aeval_at_4, norm_324_eq, norm_240_eq]
  norm_num

end Hensel3

/-- **Hensel-lifted `ℚ_[3]` solubility (proved, axiom-free, strong-form Hensel).**

    The Selmer cubic `3x³ + 4y³ + 5z³ = 0` has a nontrivial solution in
    `ℚ_[3]`, obtained by fixing `(x, y) = (0, 1)` and Hensel-lifting the
    mod-27 witness `z ≡ 4 (mod 27)` (cf. `selmer_witness_p3_mod27`) via
    the strong-form Hensel statement `‖f(α)‖ < ‖f'(α)‖²`.

    The mod-3 reduction is singular: every coefficient of the Jacobian
    `(9, 12, 15)` is divisible by `3`, so naive single-variable Hensel
    along the mod-3 witness `(0, 1, 0)` does *not* lift. The strong-form
    hypothesis nevertheless holds at the mod-27 lift `a = 4`:
    - `f(4) = 5·64 + 4 = 324 = 3⁴ · 4`, so `‖f(4)‖_3 = 1/81`.
    - `f'(4) = 15·16 = 240 = 3 · 80`, so `‖f'(4)‖_3 = 1/3` and
      `‖f'(4)‖_3² = 1/9`.
    - `1/81 < 1/9` ✓.

    This proof uses *only* `Mathlib.NumberTheory.Padics.Hensel.hensels_lemma`,
    `PadicInt.norm_p`, `PadicInt.norm_intCast_eq_one_iff`, and the
    multiplicativity of the `ℤ_[p]` norm. It does NOT depend on the
    universal axiom `selmer_padic_solubility`. With Sections 11–18 it
    completes the per-prime axiom-elimination for **all twelve** primes
    in the Section-8 roadmap. -/
theorem selmer_padic_solubility_p3_hensel :
    ∃ (x y z : ℚ_[3]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 := by
  obtain ⟨zt, hz_root, _, _, _⟩ := hensels_lemma Hensel3.hensel_hypothesis
  -- hz_root : aeval zt Hensel3.Gint = 0 in ℤ_[3]
  have hz_int : (4 : ℤ_[3]) + 5 * zt ^ 3 = 0 := by
    have heval := Hensel3.Gint_aeval zt
    rw [heval] at hz_root
    exact hz_root
  refine ⟨0, 1, (zt : ℚ_[3]), Or.inr (Or.inl one_ne_zero), ?_⟩
  -- Goal: selmerPoly (0 : ℚ_[3]) 1 (zt : ℚ_[3]) = 0,
  -- i.e., 3·0³ + 4·1³ + 5·((zt : ℚ_[3]))³ = 0.
  have hcast : (4 : ℚ_[3]) + 5 * (zt : ℚ_[3]) ^ 3 = 0 := by
    have h := congrArg (fun w : ℤ_[3] => (w : ℚ_[3])) hz_int
    push_cast at h
    exact h
  show (3 : ℚ_[3]) * (0 : ℚ_[3]) ^ 3 + 4 * (1 : ℚ_[3]) ^ 3 +
        5 * (zt : ℚ_[3]) ^ 3 = 0
  linear_combination hcast

/-! ## Section 20: Status Summary (post Section 19) -/

/-!
Section 19 dispatches the singular special prime `p = 3` via strong-form
Hensel on the mod-27 witness `selmer_witness_p3_mod27 = (0, 1, 4)`. This
completes the axiom-free per-prime sweep: **all twelve** primes in the
Section-8 roadmap now admit axiom-free `ℚ_[p]`-solubility proofs.

### Updated counts (post Section 19)
- Theorems: 31 (post-Section 17) + 1 (`selmer_padic_solubility_p3_hensel`) = 32
  (substantive); the eight private aux lemmas in `Hensel3` add 8 to the raw
  counter.
- Definitions: 7 + 1 (`Hensel3.Gint`) = 8.
- Sorries: 0 (unchanged).
- Axioms: 2 (unchanged): `selmer_no_rational_solution` + universal
  `selmer_padic_solubility`.
- Status: still `axiomatized` — the universal axiom remains as the
  "all primes" closure, but it is no longer load-bearing for any specific
  Section-8 prime.
- New milestone: strong-form Hensel dispatches `p = 3`. **All twelve**
  primes (`p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`) now admit
  axiom-free `ℚ_[p]`-solubility proofs.
- Remaining (out of scope here): full Colliot-Thélène conjecture
  requires Brauer-Manin / scheme-theoretic infrastructure not present
  in Mathlib, plus 3-descent on the associated elliptic curve to pin
  down `selmer_no_rational_solution`. Both are far beyond present
  Mathlib. -/

/-! ## Section 21: Iteration 11 — Bundled discharge over the Section-8 prime set

The twelve axiom-free per-prime theorems (Sections 11–19) collectively
exhibit that the universal axiom `selmer_padic_solubility p` is
**provable** for every prime `p` in the Section-8 roadmap
`{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`. The following bundled
statement records this in a single named theorem, giving downstream
consumers a single citation point for the discharged sub-collection
without invoking the universal axiom.

This is *not* a discharge of the universal axiom — the axiom
quantifies over **all** primes, and the per-prime recipe (Hensel-lift
on a concrete witness with a verified strong-form hypothesis) does not
extend uniformly to every prime ≥ 41 (each such prime would need its
own witness search, Hensel hypothesis verification, and corollary
proof). It does, however, give a tight finite witness of the
discharged sub-collection: the 12 primes in
`selmer_locally_soluble_everywhere`'s prime sweep are *exactly* the
primes for which the Hasse-failure proof needs `ℚ_[p]`-solubility
(`p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`), so for the
Hasse-failure pipeline the universal axiom is no longer load-bearing
on any specific input. -/

/-- **Bundled axiom-free `ℚ_[p]`-solubility** for the twelve primes in
    the Section-8 roadmap. For each
    `p ∈ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}`, the Selmer cubic
    `3x³ + 4y³ + 5z³ = 0` has a nontrivial `ℚ_[p]`-solution, proved
    axiom-free via the Hensel-lifting machinery of Sections 11–19.

    Stated as a 12-fold conjunction (one conjunct per prime) so the
    universally-quantified version with type `ℚ_[p]` for an arbitrary
    `p : ℕ` (which would require `[Fact p.Prime]` to even form `ℚ_[p]`)
    can be derived as a corollary by `fin_cases` plus instance lookup
    over the 12 global `Fact (Nat.Prime N)` instances. The conjunction
    form is a single citation point for the cumulative result of
    Sections 11–19 and avoids any tactic dispatch on the prime-set
    membership at consumer sites. -/
theorem selmer_padic_solubility_section8_primes :
    (∃ x y z : ℚ_[2],  (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[3],  (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[5],  (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[7],  (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[11], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[13], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[17], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[19], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[23], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[29], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[31], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[37], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) :=
  ⟨selmer_padic_solubility_p2_hensel,
   selmer_padic_solubility_p3_hensel,
   selmer_padic_solubility_p5_hensel,
   selmer_padic_solubility_p7_hensel,
   selmer_padic_solubility_p11_hensel,
   selmer_padic_solubility_p13_hensel,
   selmer_padic_solubility_p17_hensel,
   selmer_padic_solubility_p19_hensel,
   selmer_padic_solubility_p23_hensel,
   selmer_padic_solubility_p29_hensel,
   selmer_padic_solubility_p31_hensel,
   selmer_padic_solubility_p37_hensel⟩

/-! ## Section 22: Additional Case-A Primes (p ∈ {41, 47})

The Section-13 parametric Case-A theorem `selmer_padic_solubility_caseA`
applies to *every* prime `p` with `p ≡ 2 (mod 3)` and `p ∉ {2, 5}` for
which the witness search succeeds. Sections 11–19 used this recipe at
the four Case-A primes appearing in the Section-9 mod-`p` witness table
(`p ∈ {11, 17, 23, 29}`); the remaining Case-A primes are not part of
the Hasse-failure pipeline (which only needs the twelve Section-8
primes), but extending the discharged sub-collection demonstrates that
the parametric theorem's reach is not limited to the Section-8 primes
and provides additional axiom-free citation points for any consumer
needing `ℚ_[p]`-solubility at a Case-A prime beyond the Section-8 list.

This section adds two further Case-A primes, `p ∈ {41, 47}`, as
one-line corollaries of `selmer_padic_solubility_caseA`. The witness
data for each prime is decidable: for the chosen `z₀`, both the root
divisibility `(p : ℤ) ∣ (4 + 5·z₀^3)` and the derivative coprimality
`IsCoprime (15·z₀^2 : ℤ) (p : ℤ)` reduce to native `decide` on small
integers. -/

instance : Fact (Nat.Prime 41) := ⟨by decide⟩
instance : Fact (Nat.Prime 47) := ⟨by decide⟩

/-- ℚ_[41] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `9 mod 41`. Witness data: `41 ∣ 4 + 5·9³ = 3649 = 41·89`
    and `gcd(15·9², 41) = gcd(1215, 41) = 1`. -/
theorem selmer_padic_solubility_p41_hensel :
    ∃ (x y z : ℚ_[41]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 9
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[47] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `14 mod 47`. Witness data: `47 ∣ 4 + 5·14³ = 13724 = 47·292`
    and `gcd(15·14², 47) = gcd(2940, 47) = 1`. -/
theorem selmer_padic_solubility_p47_hensel :
    ∃ (x y z : ℚ_[47]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 14
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- **Bundled Case-A solubility extension** beyond the Section-8 list.
    For `p ∈ {41, 47}`, the Selmer cubic has an axiom-free
    `ℚ_[p]`-solubility proof via the same parametric Case-A recipe as
    `p ∈ {11, 17, 23, 29}`. Together with `selmer_padic_solubility_section8_primes`,
    this gives an axiom-free 14-prime sub-collection. -/
theorem selmer_padic_solubility_extended_caseA_primes :
    (∃ x y z : ℚ_[41], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[47], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) :=
  ⟨selmer_padic_solubility_p41_hensel,
   selmer_padic_solubility_p47_hensel⟩

/-! ## Section 23: Further Case-A Primes (p ∈ {53, 59})

Continuing the Section-22 pattern, this section adds two more Case-A
primes — `p ∈ {53, 59}` — as one-line corollaries of
`selmer_padic_solubility_caseA`. Together with Section 22 these extend
the discharged sub-collection from 14 to 16 primes total.

Like the Section-22 primes, neither `p = 53` nor `p = 59` is part of the
Hasse-failure pipeline (which only consumes the twelve Section-8 primes
plus the four Section-9-table primes `{11, 17, 23, 29}`). The purpose of
the extension is the same as Section 22: demonstrate the parametric
theorem's reach beyond the Section-8 list, and provide additional
axiom-free citation points for any consumer needing `ℚ_[p]`-solubility
at a small Case-A prime.

**Eligibility**: a prime `p` is Case-A in the sense of Section 13 iff
`p ≡ 2 (mod 3)` and `p ∉ {2, 5}`. Among primes `p < 60` not yet in the
discharged sub-collection (i.e., `p ∉ {2, 3, 5, 7, 11, 13, 17, 19, 23,
29, 31, 37, 41, 47}`), the Case-A primes are `{53, 59}`. Both `53 ≡ 2`
and `59 ≡ 2 (mod 3)`. -/

instance : Fact (Nat.Prime 53) := ⟨by decide⟩
instance : Fact (Nat.Prime 59) := ⟨by decide⟩

/-- ℚ_[53] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `34 mod 53`. Witness data: `53 ∣ 4 + 5·34³ = 196524 = 53·3708`
    and `gcd(15·34², 53) = gcd(17340, 53) = 1`. -/
theorem selmer_padic_solubility_p53_hensel :
    ∃ (x y z : ℚ_[53]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 34
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[59] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `52 mod 59`. Witness data: `59 ∣ 4 + 5·52³ = 703044 = 59·11916`
    and `gcd(15·52², 59) = gcd(40560, 59) = 1`. -/
theorem selmer_padic_solubility_p59_hensel :
    ∃ (x y z : ℚ_[59]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 52
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- **Bundled Case-A solubility extension v2** — covers all four
    extended Case-A primes `p ∈ {41, 47, 53, 59}`. Each is an axiom-free
    application of the Section-13 parametric Case-A theorem; together
    with `selmer_padic_solubility_section8_primes` (the 12 Section-8
    primes), this gives an axiom-free 16-prime sub-collection of the
    universal axiom `selmer_padic_solubility`. -/
theorem selmer_padic_solubility_extended_caseA_primes_v2 :
    (∃ x y z : ℚ_[41], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[47], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[53], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[59], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) :=
  ⟨selmer_padic_solubility_p41_hensel,
   selmer_padic_solubility_p47_hensel,
   selmer_padic_solubility_p53_hensel,
   selmer_padic_solubility_p59_hensel⟩

/-! ## Section 24: Case-A Primes Beyond 60 (p ∈ {71, 83, 89, 101})

Continuing the Sections 22/23 pattern, this section adds four further
Case-A primes — `p ∈ {71, 83, 89, 101}` — as one-line corollaries of
`selmer_padic_solubility_caseA`. Together with Sections 22 and 23,
this extends the discharged sub-collection from 16 to 20 primes total
(12 Section-8 primes + Sections 22/23's 4 primes + Section 24's 4 primes).

Eligibility (per Section 13): a prime `p` is Case-A iff `p ≡ 2 (mod 3)`
and `p ∉ {2, 5}`. All four primes satisfy this:

| prime | `p mod 3` | comment                                   |
| ----- | --------- | ----------------------------------------- |
| 71    | 2         | smallest Case-A prime above 60            |
| 83    | 2         | (next Case-A prime; 73 ≡ 1 mod 3, skipped)|
| 89    | 2         | (next; 79 ≡ 1 mod 3, skipped)             |
| 101   | 2         | smallest 3-digit Case-A prime; 97 ≡ 1     |

These primes (like the Sections 22/23 primes) are not part of the
Hasse-failure pipeline (which consumes only the twelve Section-8 primes
plus the four Section-9 table primes `{11, 17, 23, 29}`). They serve
the same purpose as Sections 22/23: demonstrate the parametric theorem's
unbounded reach and provide additional axiom-free citation points for
any consumer needing `ℚ_[p]`-solubility at a small Case-A prime.

**Witness data** (verified by direct ℤ-arithmetic + `decide`):

| prime | `z₀` | `4 + 5·z₀³`         | `p ∣ (4+5z₀³)` | `15·z₀²` | `gcd(15z₀², p)` |
| ----- | ---- | ------------------- | -------------- | -------- | --------------- |
| 71    | 63   | 1250239 = 71·17609  | ✓              | 59535    | 1               |
| 83    | 23   | 60839   = 83·733    | ✓              | 7935     | 1               |
| 89    | 9    | 3649    = 89·41     | ✓              | 1215     | 1               |
| 101   | 81   | 2657209 = 101·26309 | ✓              | 98415    | 1               |

The witnesses are the smallest non-negative `z₀ < p` with `5·z₀³ ≡ -4 (mod p)`,
obtained by iterating over `(ZMod p)`. Each exists uniquely because the
cube map on `(ZMod p)ˣ` is bijective when `gcd(3, p - 1) = 1`, which holds
exactly when `p ≡ 2 (mod 3)`. A future Section 25 may codify this
existence-of-cube-root step parametrically, eliminating the per-prime
enumeration entirely (the universal Case-A theorem). -/

instance : Fact (Nat.Prime 71) := ⟨by decide⟩
instance : Fact (Nat.Prime 83) := ⟨by decide⟩
instance : Fact (Nat.Prime 89) := ⟨by decide⟩
instance : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- ℚ_[71] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `63 mod 71`. Witness data: `71 ∣ 4 + 5·63³ = 1250239 = 71·17609`
    and `gcd(15·63², 71) = gcd(59535, 71) = 1`. -/
theorem selmer_padic_solubility_p71_hensel :
    ∃ (x y z : ℚ_[71]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 63
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[83] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `23 mod 83`. Witness data: `83 ∣ 4 + 5·23³ = 60839 = 83·733`
    and `gcd(15·23², 83) = gcd(7935, 83) = 1`. -/
theorem selmer_padic_solubility_p83_hensel :
    ∃ (x y z : ℚ_[83]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 23
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[89] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `9 mod 89`. Witness data: `89 ∣ 4 + 5·9³ = 3649 = 89·41`
    and `gcd(15·9², 89) = gcd(1215, 89) = 1`. -/
theorem selmer_padic_solubility_p89_hensel :
    ∃ (x y z : ℚ_[89]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 9
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- ℚ_[101] solubility of the Selmer cubic: `(0, 1, zt)` for `zt`
    lifting `81 mod 101`. Witness data: `101 ∣ 4 + 5·81³ = 2657209 = 101·26309`
    and `gcd(15·81², 101) = gcd(98415, 101) = 1`. -/
theorem selmer_padic_solubility_p101_hensel :
    ∃ (x y z : ℚ_[101]), (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0 :=
  selmer_padic_solubility_caseA 81
    (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide))

/-- **Bundled Case-A solubility extension v3** — covers all eight
    extended Case-A primes `p ∈ {41, 47, 53, 59, 71, 83, 89, 101}`.
    Each is an axiom-free application of the Section-13 parametric
    Case-A theorem; together with `selmer_padic_solubility_section8_primes`
    (the 12 Section-8 primes), this gives an axiom-free 20-prime
    sub-collection of the universal axiom `selmer_padic_solubility`. -/
theorem selmer_padic_solubility_extended_caseA_primes_v3 :
    (∃ x y z : ℚ_[41], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[47], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[53], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[59], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[71], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[83], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[89], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) ∧
    (∃ x y z : ℚ_[101], (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧ selmerPoly x y z = 0) :=
  ⟨selmer_padic_solubility_p41_hensel,
   selmer_padic_solubility_p47_hensel,
   selmer_padic_solubility_p53_hensel,
   selmer_padic_solubility_p59_hensel,
   selmer_padic_solubility_p71_hensel,
   selmer_padic_solubility_p83_hensel,
   selmer_padic_solubility_p89_hensel,
   selmer_padic_solubility_p101_hensel⟩

#check @selmerCubic_real_solution
#check @selmer_rat_implies_real
#check @selmer_rat_implies_padic
#check @selmer_no_rational_solution
#check @selmer_padic_solubility
#check @selmer_locally_soluble_everywhere
#check @selmer_hasse_principle_fails
#check @selmer_padic_solubility_p11_hensel
#check @selmer_padic_solubility_caseA
#check @selmer_padic_solubility_p17_hensel
#check @selmer_padic_solubility_p23_hensel
#check @selmer_padic_solubility_p29_hensel
#check @selmer_padic_solubility_lift_z
#check @selmer_padic_solubility_p13_hensel
#check @selmer_padic_solubility_p19_hensel
#check @selmer_padic_solubility_p31_hensel
#check @selmer_padic_solubility_p37_hensel
#check @selmer_padic_solubility_lift_x
#check @selmer_padic_solubility_p7_hensel
#check @selmer_padic_solubility_p2_hensel
#check @selmer_padic_solubility_p5_hensel
#check @selmer_padic_solubility_p3_hensel
#check @selmer_padic_solubility_section8_primes
#check @selmer_padic_solubility_p41_hensel
#check @selmer_padic_solubility_p47_hensel
#check @selmer_padic_solubility_extended_caseA_primes
#check @selmer_padic_solubility_p53_hensel
#check @selmer_padic_solubility_p59_hensel
#check @selmer_padic_solubility_extended_caseA_primes_v2
#check @selmer_padic_solubility_p71_hensel
#check @selmer_padic_solubility_p83_hensel
#check @selmer_padic_solubility_p89_hensel
#check @selmer_padic_solubility_p101_hensel
#check @selmer_padic_solubility_extended_caseA_primes_v3

end Hilbert11OQ02
