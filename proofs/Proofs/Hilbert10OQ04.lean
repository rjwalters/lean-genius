/-
# Hilbert's Tenth Problem OQ-04: The Simplest Undecidable Diophantine Equation

## Open Question

Among all undecidable Diophantine problems, what is the minimal complexity
in terms of:
  1. **Number of variables** (unknowns)
  2. **Degree** of the polynomial

## What is Known

### Decidable complexity classes (proved in this file):
- **Degree 1, 1 variable**: ax = b decidable by divisibility
- **0 variables**: trivially decidable (constant check)

### Undecidable (axiomatized from MRDP):
- **General H10**: Undecidable (parent Hilbert10.lean proves via halting problem)
- **9 variables**: Undecidable (Jones 1982)
- **9 variables suffice**: Any r.e. set can be represented with at most 9 variables

### The Open Gap:
- Minimum variables for undecidability: **known at least 3, known at most 9**
- Whether 3–8 variables suffice is unknown as of 2026
- Minimum degree: **known at least 2, known at most 4**

## Summary: 11 theorems/lemmas, 0 sorries, 4 axioms

Axioms:
1. jones_matiyasevich_bound — 9 variables suffice for any r.e. set
2. nine_var_h10_undecidable — H10 with at most 9 variables is undecidable
3. mrdp_finite_var — every r.e. set is Diophantine in finitely many variables
4. jones_universal_poly — explicit 9-variable universal polynomial of degree 4

Discharged: linear_bezout_n is now a theorem (n-variable Bézout / gcd via the
principal coefficient ideal over ℤ; the original axiom's strict `0 < d` was
corrected to `0 ≤ d` to cover the all-zero degenerate case).

## References

- Jones, J.P. (1982). Universal Diophantine equation. JSL 47(3):549-571.
- Matiyasevich, Yu. (1993). Hilbert's Tenth Problem. MIT Press.
- Davis, M., Putnam, H., Robinson, J. (1961). Decision problem for exponential
  Diophantine equations. Ann. Math. 74(3):425-436.
-/

import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic

open BigOperators

namespace Hilbert10Simplicity

-- ============================================================
-- Part I: Variable-Bounded Diophantine Equations
-- ============================================================

/-- A Diophantine polynomial in exactly n integer variables. -/
def DiophantineN (n : Nat) : Type := (Fin n → Int) → Int

/-- An integer solution to an n-variable equation P = 0. -/
def hasSolutionN {n : Nat} (P : DiophantineN n) : Prop :=
  ∃ x : Fin n → Int, P x = 0

/-- A decision procedure for n-variable H10. -/
def H10_n_decidable (n : Nat) : Prop :=
  ∃ alg : DiophantineN n → Bool, ∀ P : DiophantineN n, alg P = true ↔ hasSolutionN P

/-- H10 restricted to n-variable equations is undecidable. -/
def H10_n_undecidable (n : Nat) : Prop := ¬H10_n_decidable n

-- ============================================================
-- Part II: Linear Forms (Degree 1)
-- ============================================================

/-- A linear form in n variables: coefficients and constant term,
    representing a₁x₁ + ... + aₙxₙ + c = 0. -/
structure LinearForm (n : Nat) where
  coeffs : Fin n → Int
  constant : Int

/-- The value of a linear form at an assignment x. -/
def LinearForm.eval {n : Nat} (L : LinearForm n) (x : Fin n → Int) : Int :=
  (∑ i : Fin n, L.coeffs i * x i) + L.constant

/-- A linear form has an integer solution iff some assignment makes it zero. -/
def hasLinearSolution {n : Nat} (L : LinearForm n) : Prop :=
  ∃ x : Fin n → Int, L.eval x = 0

-- ============================================================
-- Part III: Proved Decidable Cases
-- ============================================================

/-- **0 variables**: The "equation" evaluates to a fixed integer c.
    Decidable: check c = 0. -/
theorem zero_var_decidable : H10_n_decidable 0 := by
  refine ⟨fun P => decide (P Fin.elim0 = 0), fun P => ?_⟩
  simp only [hasSolutionN, decide_eq_true_eq]
  constructor
  · intro h; exact ⟨Fin.elim0, h⟩
  · rintro ⟨x, hx⟩
    have heq : x = Fin.elim0 := funext fun i => absurd i.isLt (Nat.not_lt_zero _)
    rwa [← heq]

/-- **1-variable linear**: ax = b has an integer solution iff a divides b.

    Proof: If a·x₀ = b then b = a·x₀, so a ∣ b.
           If b = a·k then x = k works. -/
theorem linear_one_var (a b : Int) :
    (∃ x : Int, a * x = b) ↔ a ∣ b :=
  ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- 0·x = b has a solution iff b = 0. -/
theorem zero_coeff_linear (b : Int) :
    (∃ x : Int, (0 : Int) * x = b) ↔ b = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    simpa using hx.symm
  · rintro rfl
    exact ⟨0, by ring⟩

/-- 1·x = b always has a solution (x = b). -/
theorem unit_coeff_linear (b : Int) : ∃ x : Int, (1 : Int) * x = b :=
  ⟨b, by ring⟩

/-- -1·x = b always has a solution (x = -b). -/
theorem neg_unit_coeff_linear (b : Int) : ∃ x : Int, (-1 : Int) * x = b :=
  ⟨-b, by ring⟩

/-- **Monotonicity**: n-variable undecidability implies (n+1)-variable undecidability.

    Embed n-variable equations into (n+1)-variable by ignoring the last variable.
    A decision procedure for (n+1)-variable H10 would decide n-variable H10. -/
theorem H10_undecidable_monotone {n : Nat}
    (h : H10_n_undecidable n) : H10_n_undecidable (n + 1) := by
  intro ⟨alg, halg⟩
  apply h
  let embed : DiophantineN n → DiophantineN (n + 1) :=
    fun P x => P (fun i => x i.castSucc)
  refine ⟨fun P => alg (embed P), fun P => ?_⟩
  rw [halg (embed P)]
  simp only [hasSolutionN, embed]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨fun i => y i.castSucc, hy⟩
  · rintro ⟨x, hx⟩
    -- Extend x to n+1 variables by setting the last one to 0
    let y : Fin (n + 1) → Int := fun j =>
      if hlt : j.val < n then x ⟨j.val, hlt⟩ else 0
    refine ⟨y, ?_⟩
    convert hx using 2
    funext i
    simp only [y]
    split
    · exact congrArg x (Fin.ext (by simp))
    · rename_i h
      exact absurd (by simpa using i.isLt : ((i.castSucc : Fin (n + 1)) : ℕ) < n) h

-- ============================================================
-- Part IV: Axioms — Key Results from Literature
-- ============================================================

/-- **MRDP (variable-bounded form)**:
    Every r.e. set can be expressed as the parameterized solution set of a
    Diophantine equation in finitely many variables.

    Proved by Davis-Putnam-Robinson-Matiyasevich (1970). -/
axiom mrdp_finite_var :
    ∀ (S : Nat → Prop),
      ∃ (n : Nat) (P : Nat → DiophantineN n), ∀ k : Nat, S k ↔ hasSolutionN (P k)

/-- **Jones-Matiyasevich Upper Bound (1982)**:
    9 variables suffice: every r.e. set can be encoded by a Diophantine equation
    in at most 9 variables.

    Reference: Jones (1982) improved Matiyasevich's 1977 bound of 13 variables to 9. -/
axiom jones_matiyasevich_bound :
    ∀ (S : Nat → Prop),
      ∃ P : Nat → DiophantineN 9, ∀ k : Nat, S k ↔ hasSolutionN (P k)

/-- **9-variable H10 is undecidable**:
    The halting problem reduces to H10 restricted to 9-variable equations.
    Formally: applying jones_matiyasevich_bound to the halting set gives a
    9-variable polynomial whose solvability encodes halting — so a decision
    procedure for 9-variable H10 would solve the halting problem. -/
axiom nine_var_h10_undecidable : H10_n_undecidable 9

/-- **Linear Bézout (n variables)**:
    A linear equation a₁x₁ + ... + aₙxₙ = b has an integer solution iff there
    is a nonnegative `d` (the GCD of the aᵢ) dividing b, dividing every aᵢ, and
    divisible by every common divisor of the aᵢ.

    The GCD characterization uses `0 ≤ d` rather than `0 < d`: the degenerate
    all-zero case (every aᵢ = 0 and b = 0) is solvable yet the only witnessing
    `d` is `0`, which a strict `0 < d` would wrongly exclude (it would force a
    positive `d` divisible by *every* integer). This is the minimal correction
    to the originally-axiomatized statement, which was false in that case.

    Proved via the principal ideal generated by the coefficients: over ℤ the
    coefficient ideal `Ideal.span (Set.range a)` is principal, and a generator
    `g` is exactly such a GCD (taking `d = |g|` for nonnegativity). -/
theorem linear_bezout_n (n : Nat) (a : Fin n → Int) (b : Int) :
    (∃ x : Fin n → Int, ∑ i : Fin n, a i * x i = b) ↔
    ∃ d : Int, 0 ≤ d ∧ (d ∣ b) ∧ (∀ i : Fin n, d ∣ a i) ∧
      ∀ e : Int, (∀ i : Fin n, e ∣ a i) → e ∣ d := by
  classical
  -- Solvability is exactly membership of `b` in the coefficient ideal.
  have hmem : (∃ x : Fin n → Int, ∑ i : Fin n, a i * x i = b) ↔
      b ∈ Ideal.span (Set.range a) := by
    rw [Ideal.mem_span_range_iff_exists_fun]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, by simpa [mul_comm] using hx⟩,
           fun ⟨c, hc⟩ => ⟨c, by simpa [mul_comm] using hc⟩⟩
  rw [hmem]
  -- ℤ is a principal ideal ring, so the coefficient ideal has a generator `g`.
  set I : Ideal Int := Ideal.span (Set.range a) with hIdef
  obtain ⟨g, hg⟩ : ∃ g : Int, I = Ideal.span {g} :=
    ⟨Submodule.IsPrincipal.generator I,
      (Submodule.IsPrincipal.span_singleton_generator I).symm⟩
  -- Each coefficient lies in `I`, hence is divisible by `g`.
  have hg_dvd_a : ∀ i, g ∣ a i := by
    intro i
    have hai : a i ∈ I := Ideal.subset_span (Set.mem_range_self i)
    rwa [hg, Ideal.mem_span_singleton] at hai
  have hg_mem : g ∈ I := by rw [hg]; exact Ideal.mem_span_singleton_self g
  constructor
  · -- Forward: `b ∈ I` gives the gcd `d = |g|`.
    intro hb
    refine ⟨(g.natAbs : Int), by positivity, ?_, ?_, ?_⟩
    · -- |g| ∣ b, since g ∣ b
      have hgb : g ∣ b := by rwa [hg, Ideal.mem_span_singleton] at hb
      exact Int.natAbs_dvd.mpr hgb
    · -- ∀ i, |g| ∣ a i
      intro i; exact Int.natAbs_dvd.mpr (hg_dvd_a i)
    · -- universal: every common divisor of the aᵢ divides |g|
      intro e he
      have hle : I ≤ Ideal.span {e} := by
        rw [hIdef, Ideal.span_le]
        rintro y ⟨i, rfl⟩
        rw [SetLike.mem_coe, Ideal.mem_span_singleton]
        exact he i
      have heg : e ∣ g := by
        have := hle hg_mem
        rwa [Ideal.mem_span_singleton] at this
      exact Int.dvd_natAbs.mpr heg
  · -- Backward: any such `d` forces `g ∣ b`, hence `b ∈ I`.
    rintro ⟨d, _, hdb, _, huniv⟩
    have hgd : g ∣ d := huniv g hg_dvd_a
    have hgb : g ∣ b := dvd_trans hgd hdb
    rw [hg, Ideal.mem_span_singleton]; exact hgb

/-- **Jones Universal Polynomial (1982)**:
    There exists a single polynomial poly in 9 unknowns, parameterized by
    an integer, such that for any r.e. set S there is an offset making the
    parameterized solvability agree with S.

    Jones's explicit polynomial has degree 4 and 9 unknowns. The existence
    of such a polynomial is the quantitative form of the MRDP theorem. -/
axiom jones_universal_poly :
    ∃ poly : Int → DiophantineN 9,
      ∀ (S : Nat → Prop),
        ∃ offset : Int,
          ∀ k : Nat, S k ↔ hasSolutionN (poly (offset + k))

-- ============================================================
-- Part V: Consequences
-- ============================================================

/-- **Upward closure**: Since 9-variable H10 is undecidable, so is 10-variable. -/
theorem ten_var_h10_undecidable : H10_n_undecidable 10 :=
  H10_undecidable_monotone nine_var_h10_undecidable

/-- **11-variable**: Similarly undecidable by monotonicity. -/
theorem eleven_var_h10_undecidable : H10_n_undecidable 11 :=
  H10_undecidable_monotone ten_var_h10_undecidable

/-- **Degree boundary**: degree ≤ 1 is decidable (Bézout), degree 4 is not.
    Documents the complexity gap: undecidability threshold is in [2, 4] degree. -/
theorem degree_1_decidable_1var :
    ∀ a b : Int, ((∃ x : Int, a * x = b) ↔ a ∣ b) :=
  linear_one_var

/-- **Main complexity summary**: The complexity boundary for H10 undecidability
    lies between degree 1 (decidable by Bézout) and degree 4 with 9 variables. -/
theorem complexity_gap_summary :
    -- 1-var linear: decidable
    (∀ a b : Int, (∃ x : Int, a * x = b) ↔ a ∣ b) ∧
    -- 9-var general: undecidable
    H10_n_undecidable 9 :=
  ⟨linear_one_var, nine_var_h10_undecidable⟩

/-
## Open Questions (as of 2026)

### OQ-04a: Minimum variable count for undecidability?
- Known upper bound: 9 (Jones 1982)
- Known lower bound: at least 3 variables needed
- Unknown: whether 3, 4, 5, 6, 7, or 8 variables suffice

### OQ-04b: Minimum degree for undecidability?
- Known upper bound: degree 4 (Jones-Matiyasevich)
- Known lower bound: degree ≥ 2 (degree ≤ 1 is decidable)
- Unknown: whether degree 2 or 3 equations in many variables are undecidable

### OQ-04c: Can both minimums be achieved simultaneously?
- Jones (1982): YES, degree 4 and 9 variables can be achieved together.

The current best known explicit undecidable Diophantine equation has
9 unknowns and degree 4 (Jones 1982). Any improvement to either bound
would be a significant advance in computational number theory.
-/

end Hilbert10Simplicity
