import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleNumber
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.NumberTheory.Transcendental.Liouville.Residual
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Liouville's Theorem and Transcendental Numbers (Wiedijk #18)

## What This File Contains

This file formalizes **Liouville's Theorem** about rational approximations to algebraic numbers
and the consequent existence of transcendental numbers via **Liouville numbers**.

## The Theorems

**Liouville's Approximation Theorem** (1844): If α is a real algebraic number of degree n > 1,
then there exists a constant c > 0 such that for all rationals p/q with q > 0:

$$\left| \alpha - \frac{p}{q} \right| > \frac{c}{q^n}$$

**Corollary**: Any number that can be approximated "too well" by rationals must be transcendental.
Such numbers are called **Liouville numbers**.

**Liouville Number Definition**: A real number ξ is a Liouville number if for every positive
integer n, there exist integers p and q with q > 1 such that:

$$0 < \left| \xi - \frac{p}{q} \right| < \frac{1}{q^n}$$

**Main Result**: All Liouville numbers are transcendental.

## Historical Significance

This was the **first explicit construction of transcendental numbers** (1844), predating:
- Cantor's diagonal argument (1874) showing transcendentals are uncountable
- Hermite's proof that e is transcendental (1873)
- Lindemann's proof that π is transcendental (1882)

Liouville's constant L = Σₙ 10^(-n!) was the first number proven transcendental.

## Key Ideas

1. **Algebraic numbers have bounded approximability**: The minimal polynomial provides a lower
   bound on how close rationals can get.

2. **Liouville numbers violate all such bounds**: They can be approximated arbitrarily well,
   better than any polynomial bound allows.

3. **Therefore Liouville numbers cannot be algebraic**: They must be transcendental.

## Mathlib Dependencies

- `Liouville` : Definition of Liouville numbers from `Mathlib.NumberTheory.Liouville.Basic`
- `liouvilleNumber` : The explicit Liouville constant from `Mathlib.NumberTheory.Liouville.LiouvilleConstant`
- `Transcendental` : Definition from `Mathlib.RingTheory.Algebraic`
- `IsAlgebraic` : Algebraic number definition

## Status

- [x] Statement of Liouville's approximation theorem
- [x] Definition of Liouville numbers (from Mathlib)
- [x] Explicit Liouville constant construction (from Mathlib)
- [x] Transcendence of Liouville numbers (from Mathlib)
- [x] Pedagogical exposition

## References

- Liouville, J. (1844). "Sur des classes très-étendues de quantités..."
- Mathlib: `Mathlib.NumberTheory.Liouville`
- Baker, A. (1990). "Transcendental Number Theory"
-/

set_option maxHeartbeats 400000

noncomputable section

open Real Polynomial
open scoped Nat

namespace LiouvilleTheorem

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: BACKGROUND AND DEFINITIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
A real number is **algebraic** over ℤ if it is a root of a non-zero polynomial
with integer coefficients: `IsAlgebraic ℤ x`.

A number is **transcendental** if it is not algebraic: `Transcendental ℤ x`.

The **degree** of an algebraic number is the degree of its minimal polynomial:
`Polynomial.natDegree`.

A real number is a **Liouville number** if it can be approximated by rationals
better than any polynomial bound allows: `Liouville x`.

Formally: For every n ≥ 1, there exist integers p and q with q > 1 such that
x ≠ p/q and |x - p/q| < 1/q^n.

This definition captures numbers that are "too well approximated" by rationals.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: LIOUVILLE'S APPROXIMATION THEOREM
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### The Approximation Theorem (Liouville, 1844)

**Theorem**: Let α be a real algebraic number of degree n ≥ 2 over ℚ.
Then there exists a constant c > 0 (depending only on α) such that for all
integers p, q with q > 0:

  |α - p/q| > c / q^n

**Proof Outline**:

1. Let P(x) be the minimal polynomial of α over ℤ, with degree n.

2. For any rational p/q ≠ α, we have P(p/q) ≠ 0 (since P is irreducible and
   p/q is rational while α is irrational for n ≥ 2).

3. Clearing denominators: q^n · P(p/q) is a non-zero integer, so |q^n · P(p/q)| ≥ 1.

4. By the Mean Value Theorem, for some ξ between p/q and α:
   P(p/q) = P(p/q) - P(α) = (p/q - α) · P'(ξ)

5. If |α - p/q| < 1, then |P'(ξ)| is bounded by some M depending on α.

6. Therefore: |α - p/q| ≥ 1 / (M · q^n)

7. If |α - p/q| ≥ 1, the bound holds trivially for small c.

**Key Insight**: The degree of the minimal polynomial limits how well the number
can be approximated by rationals.
-/

/-- **Liouville's Approximation Theorem** (1844) — formerly axiom, now proved.

    If α is algebraic of degree n ≥ 2, then there exists c > 0 such that
    for all rationals p/q with q > 0: |α - p/q| > c/q^n (or α = p/q).

    **Irrational case**: Uses Mathlib's `Liouville.exists_pos_real_of_irrational_root`,
    which proves the bound via the Mean Value Theorem and denominator clearing.

    **Rational case**: Uses the integer gap: for α = a/b rational and p/q ≠ α,
    |α - p/q| = |aq - bp|/(bq) ≥ 1/(bq) ≥ 1/(b·q^n). -/
theorem liouville_approximation_theorem_axiom
    (α : ℝ) (hα : IsAlgebraic ℤ α) (n : ℕ) (hn : n ≥ 2)
    (hdeg : ∃ f : Polynomial ℤ, f.natDegree = n ∧ Polynomial.aeval α f = 0 ∧ f ≠ 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ p q : ℤ, q > 0 → |α - p / q| > c / (q : ℝ) ^ n ∨ α = p / q := by
  obtain ⟨f, hfn, hfa, hf0⟩ := hdeg
  -- Convert aeval to eval (map ...) for Mathlib compatibility
  have heval : Polynomial.eval α (Polynomial.map (algebraMap ℤ ℝ) f) = 0 := by
    rwa [Polynomial.eval_map, ← Polynomial.aeval_def]
  by_cases hirr : Irrational α
  · -- Case 1: α is irrational — use Mathlib's theorem
    obtain ⟨A, hA, hbound⟩ := Liouville.exists_pos_real_of_irrational_root hirr hf0 heval
    -- Use c = 1/(2A): from Mathlib's bound |α-p/q| ≥ 1/(A·q^n) > 1/(2A·q^n)
    refine ⟨1 / (2 * A), by positivity, fun p q hq => ?_⟩
    left
    -- Map q : ℤ (q > 0) to b : ℕ with (↑b + 1 : ℝ) = (↑q : ℝ)
    have hq_pos : (0 : ℝ) < (q : ℝ) := Int.cast_pos.mpr hq
    set b := q.toNat - 1 with hb_def
    have hqn : q.toNat ≥ 1 := by omega
    have hb_succ : (↑b + 1 : ℝ) = (↑q : ℝ) := by
      have : (b : ℤ) + 1 = q := by
        simp [hb_def, Int.toNat_sub_of_le (by omega : 1 ≤ q)]
        omega
      push_cast [← this]; ring
    -- Apply Mathlib bound
    have hmb := hbound p b
    rw [hfn, hb_succ] at hmb
    -- hmb : 1 ≤ (↑q : ℝ) ^ n * (|α - ↑p / ↑q| * A)
    -- Goal : |α - ↑p / ↑q| > 1 / (2 * A) / (↑q : ℝ) ^ n
    have hqn_pos : (0 : ℝ) < (↑q : ℝ) ^ n := pow_pos hq_pos n
    rw [div_div]
    rw [gt_iff_lt, lt_div_iff (by positivity : 0 < 2 * A * (↑q : ℝ) ^ n)]
    -- Goal : 1 < |α - ↑p / ↑q| * (2 * A * ↑q ^ n)
    have h1 : |α - ↑p / ↑q| * A ≥ 1 / (↑q : ℝ) ^ n := by
      rwa [ge_iff_le, div_le_iff hqn_pos, mul_comm]
    calc 1 = 1 * 1 := by ring
      _ < 2 * (|α - ↑p / ↑q| * A * (↑q : ℝ) ^ n) := by
          have := mul_le_mul_of_nonneg_right h1 (le_of_lt hqn_pos)
          rw [div_mul_cancel₀ _ (ne_of_gt hqn_pos)] at this
          linarith [abs_nonneg (α - ↑p / ↑q), hA]
      _ = |α - ↑p / ↑q| * (2 * A * (↑q : ℝ) ^ n) := by ring
  · -- Case 2: α is rational — use integer gap argument
    -- Extract rational representation: α = ↑r for some r : ℚ
    obtain ⟨r, rfl⟩ : ∃ r : ℚ, (↑r : ℝ) = α := not_not.mp hirr
    -- Use c = 1/(2 * r.den). For p/q ≠ ↑r: |↑r - p/q| ≥ 1/(r.den · q^n) > c/q^n
    refine ⟨1 / (2 * (r.den : ℝ)), by positivity, fun p q hq => ?_⟩
    by_cases heq : (↑r : ℝ) = ↑p / ↑q
    · exact Or.inr heq
    · left
      -- Integer gap: r.num * q - p * r.den is a nonzero integer
      have hq_pos : (0 : ℝ) < (↑q : ℝ) := Int.cast_pos.mpr hq
      have hq_ne : (↑q : ℝ) ≠ 0 := ne_of_gt hq_pos
      have hden_pos : (0 : ℝ) < (↑r.den : ℝ) := Nat.cast_pos.mpr r.pos
      set k := r.num * q - p * (r.den : ℤ) with hk_def
      have hk_ne : k ≠ 0 := by
        intro hk
        apply heq
        rw [Rat.cast_def, div_eq_div_iff (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp r.pos)) hq_ne]
        have : r.num * q = p * (r.den : ℤ) := by omega
        exact_mod_cast this
      -- |k| ≥ 1 since k is a nonzero integer
      have hk_abs : (1 : ℝ) ≤ |(↑k : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk_ne
      -- Key identity: ↑r - ↑p / ↑q = ↑k / (↑r.den * ↑q)
      have hid : (↑r : ℝ) - ↑p / ↑q = (↑k : ℝ) / ((↑r.den : ℝ) * ↑q) := by
        rw [Rat.cast_def, hk_def]; field_simp; push_cast; ring
      -- Chain of inequalities
      rw [gt_iff_lt]
      calc 1 / (2 * (↑r.den : ℝ)) / (↑q : ℝ) ^ n
          < 1 / ((↑r.den : ℝ) * (↑q : ℝ) ^ n) := by
            rw [div_div]; apply div_lt_div_of_pos_right (by linarith : 1 / (2 * ↑r.den) < 1 / ↑r.den)
              (by positivity)
        _ ≤ 1 / ((↑r.den : ℝ) * ↑q) := by
            apply div_le_div_of_nonneg_left one_pos (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_left
              (le_self_pow₀ (by linarith : 1 ≤ (↑q : ℝ)) (by omega : n ≠ 0))
              (by positivity)
        _ ≤ |(↑k : ℝ)| / ((↑r.den : ℝ) * ↑q) := by
            exact div_le_div_of_nonneg_right hk_abs (by positivity)
        _ = |↑r - ↑p / ↑q| := by rw [hid, abs_div, abs_of_pos (by positivity : 0 < ↑r.den * ↑q)]

theorem liouville_approximation_theorem
    (α : ℝ) (hα : IsAlgebraic ℤ α) (n : ℕ) (hn : n ≥ 2)
    (hdeg : ∃ p : Polynomial ℤ, p.natDegree = n ∧ Polynomial.aeval α p = 0 ∧ p ≠ 0) :
    ∃ c : ℝ, c > 0 ∧ ∀ p q : ℤ, q > 0 → |α - p / q| > c / (q : ℝ) ^ n ∨ α = p / q :=
  liouville_approximation_theorem_axiom α hα n hn hdeg

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: LIOUVILLE NUMBERS AND THEIR TRANSCENDENCE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Definition of Liouville Number**

A real number ξ is Liouville if for every positive integer n, there exist
integers p and q with q > 1 such that:
  0 < |ξ - p/q| < 1/q^n

Equivalently: ξ can be approximated by rationals better than any polynomial
bound would allow for an algebraic number.

Note: The Mathlib definition uses `x ≠ p/q` instead of `0 < |x - p/q|`, which
is equivalent for the approximation property. -/
theorem liouville_def (x : ℝ) :
    Liouville x ↔ ∀ n : ℕ, ∃ p q : ℤ, 1 < q ∧ x ≠ p / q ∧ |x - p / q| < 1 / (q : ℝ) ^ n := by
  rfl

/-- **Main Theorem: Liouville numbers are transcendental** (Wiedijk #18)

This follows from Liouville's approximation theorem by contraposition:
- If α is algebraic of degree n, it cannot be approximated better than c/q^n
- Liouville numbers can be approximated arbitrarily well
- Therefore Liouville numbers cannot be algebraic

**Proof Strategy**:
Suppose ξ is Liouville and algebraic of degree n. Then:
1. By the approximation theorem, |ξ - p/q| > c/q^n for some c > 0
2. By the Liouville property, there exist p, q with |ξ - p/q| < 1/q^(n+1)
3. For large enough q, 1/q^(n+1) < c/q^n, contradiction!
-/
theorem liouville_transcendental (x : ℝ) (hx : Liouville x) : Transcendental ℤ x :=
  Liouville.transcendental hx

/-- Alternative statement: Liouville numbers are not algebraic. -/
theorem liouville_not_algebraic (x : ℝ) (hx : Liouville x) : ¬IsAlgebraic ℤ x := by
  have := liouville_transcendental x hx
  unfold Transcendental at this
  exact this

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: THE LIOUVILLE CONSTANT
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Construction of an Explicit Transcendental Number

**Liouville's Constant** (1844):

L = Σₙ₌₁^∞ 10^(-n!) = 10^(-1) + 10^(-2) + 10^(-6) + 10^(-24) + 10^(-120) + ...

In decimal: L = 0.110001000000000000000001000...

The 1's appear at positions 1, 2, 6, 24, 120, ... (the factorials).

**Why L is Liouville**:

The partial sums Lₘ = Σₙ₌₁^m 10^(-n!) are excellent rational approximations.

If we write Lₘ = pₘ/qₘ with qₘ = 10^(m!), then:

|L - pₘ/qₘ| = Σₙ₌ₘ₊₁^∞ 10^(-n!)
            < 2 · 10^(-(m+1)!)
            = 2 / qₘ^(m+1)
            < 1 / qₘ^m   (for m ≥ 2)

This beats the bound 1/q^n for arbitrarily large n by taking m > n.
-/

/-- **The Liouville constant is a Liouville number**

    The Liouville constant L = Σₙ₌₁^∞ 10^(-n!) is Liouville's original example
    of a transcendental number (1844). -/
theorem liouville_constant_is_liouville : Liouville (liouvilleNumber 10) :=
  liouville_liouvilleNumber (by norm_num : (2 : ℕ) ≤ 10)

/-- **The Liouville constant is transcendental** (First Explicit Example, 1844)

This was historically the first number proven to be transcendental!
-/
theorem liouville_constant_transcendental : Transcendental ℤ (liouvilleNumber 10) :=
  liouville_transcendental _ liouville_constant_is_liouville

/-- **The Liouville constant is irrational** (formerly axiom, now proved)

    Transcendental implies irrational: if L = p/q, then L is a root of
    q·X - p = 0, making L algebraic. This contradicts transcendence. -/
theorem liouville_constant_irrational_axiom : Irrational (liouvilleNumber 10) :=
  liouville_constant_is_liouville.irrational

/-- The Liouville constant is irrational (weaker statement, but worth noting). -/
theorem liouville_constant_irrational : Irrational (liouvilleNumber 10) :=
  liouville_constant_irrational_axiom

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: PROPERTIES OF LIOUVILLE NUMBERS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Liouville numbers form an uncountable set.** (formerly axiom, now proved)

    The set of Liouville numbers is residual (comeagre) in ℝ by
    `eventually_residual_liouville` from Mathlib. In a nonempty Baire space like ℝ,
    residual sets are not meagre. But any countable subset of ℝ is meagre: each
    singleton has empty interior (since ℝ is a perfect space with no isolated points),
    hence is nowhere dense, hence meagre, and a countable union of meagre sets is
    meagre. Contradiction. -/
theorem liouville_uncountable_axiom : ¬Set.Countable {x : ℝ | Liouville x} := by
  intro hcount
  have hnotmeagre : ¬IsMeagre {x : ℝ | Liouville x} :=
    not_isMeagre_of_mem_residual eventually_residual_liouville
  apply hnotmeagre
  have eq : {x : ℝ | Liouville x} = ⋃ x ∈ {x : ℝ | Liouville x}, ({x} : Set ℝ) := by ext; simp
  rw [eq]
  exact isMeagre_biUnion hcount fun x _ =>
    (isClosed_singleton.isNowhereDense_iff.mpr (interior_singleton x)).isMeagre

theorem liouville_uncountable : ¬Set.Countable {x : ℝ | Liouville x} :=
  liouville_uncountable_axiom

/-- **Adding a rational preserves the Liouville property.** (formerly axiom, now proved)

    Follows from LiouvilleWith.add_rat and the equivalence with Liouville. -/
theorem liouville_add_rat_axiom (x : ℝ) (hx : Liouville x) (r : ℚ) : Liouville (x + r) :=
  LiouvilleWith.forall_liouvilleWith_iff.mp (fun p => (hx.liouvilleWith p).add_rat r)

/-- If x is Liouville and r is a non-zero rational, then x + r is Liouville.

Adding a rational doesn't change the approximability properties. -/
theorem liouville_add_rat (x : ℝ) (hx : Liouville x) (r : ℚ) : Liouville (x + r) :=
  liouville_add_rat_axiom x hx r

/-- **Scaling by a non-zero rational preserves the Liouville property.** (formerly axiom, now proved)

    Follows from LiouvilleWith.rat_mul and the equivalence with Liouville. -/
theorem liouville_mul_rat_axiom (x : ℝ) (hx : Liouville x) (r : ℚ) (hr : r ≠ 0) : Liouville (r * x) :=
  LiouvilleWith.forall_liouvilleWith_iff.mp (fun p => (hx.liouvilleWith p).rat_mul hr)

/-- If x is Liouville and r is a non-zero rational, then r * x is Liouville.

Scaling by a rational changes the constant but preserves the Liouville property. -/
theorem liouville_mul_rat (x : ℝ) (hx : Liouville x) (r : ℚ) (hr : r ≠ 0) : Liouville (r * x) :=
  liouville_mul_rat_axiom x hx r hr

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: GENERALIZATIONS AND IMPROVEMENTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Roth's Theorem (1955)

Liouville's bound |α - p/q| > c/q^n for algebraic α of degree n was dramatically
improved by Klaus Roth:

**Roth's Theorem**: For any algebraic irrational α and any ε > 0, there exists
c = c(α, ε) > 0 such that for all rationals p/q:

  |α - p/q| > c / q^(2+ε)

The exponent 2 is optimal (by Hurwitz's theorem on Diophantine approximation).

This earned Roth the Fields Medal in 1958.

**Consequence**: A number ξ is transcendental if for every ε > 0, there are
infinitely many rationals p/q with |ξ - p/q| < 1/q^(2+ε).
-/

/-- **Roth's Theorem** (1955)

For algebraic irrational α and any ε > 0, the inequality |α - p/q| < 1/q^(2+ε)
has only finitely many solutions.

This dramatically strengthens Liouville's theorem.

**Implementation Note**: The full proof is very deep, using methods from
algebraic geometry and the subspace theorem. -/
axiom roth_theorem (α : ℝ) (hα : IsAlgebraic ℤ α) (hirr : Irrational α) (ε : ℝ) (hε : ε > 0) :
    Set.Finite {pq : ℤ × ℤ | pq.2 > 0 ∧ |α - pq.1 / pq.2| < 1 / (pq.2 : ℝ) ^ (2 + ε)}

/-!
### The Thue-Siegel-Roth Progression

The exponent in approximation theorems improved over time:

1. **Liouville (1844)**: Exponent n (degree of algebraic number)
2. **Thue (1909)**: Exponent n/2 + 1 + ε
3. **Siegel (1921)**: Exponent 2√n + ε
4. **Dyson (1947)**: Exponent √(2n) + ε
5. **Roth (1955)**: Exponent 2 + ε (optimal!)

Each improvement required increasingly sophisticated techniques.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VII: CONNECTIONS TO OTHER RESULTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Related Theorems

**Hermite-Lindemann (1882)**: e^α is transcendental for non-zero algebraic α.
This provides another (more powerful) method for proving transcendence.

**Gelfond-Schneider (1934)**: α^β is transcendental when α ≠ 0, 1 is algebraic
and β is algebraic irrational. Hilbert's 7th problem.

**Baker's Theorem (1966)**: Provides effective bounds for linear combinations
of logarithms, with applications to Diophantine equations.

### Connection to Diophantine Approximation

Liouville's theorem is foundational to **Diophantine approximation**, the study
of how well real numbers can be approximated by rationals.

Key results in this area:
- **Dirichlet's theorem**: For any α and N, there exists p/q with q ≤ N and |α - p/q| < 1/(qN)
- **Hurwitz's theorem**: For any irrational α, there are infinitely many p/q with |α - p/q| < 1/(√5 · q²)
- **Continued fractions**: Best rational approximations come from convergents
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII: EXAMPLES AND COMPUTATIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Example: The number Σₙ 2^(-n!) is also transcendental (same argument works). -/
theorem liouville_base_2_transcendental : Transcendental ℤ (liouvilleNumber 2) :=
  liouville_transcendental _ (liouville_liouvilleNumber (by norm_num : (2 : ℕ) ≤ 2))

/-- For any integer base b ≥ 2, the Liouville number Σₙ b^(-n!) is transcendental. -/
theorem liouville_any_base_transcendental (b : ℕ) (hb : 2 ≤ b) :
    Transcendental ℤ (liouvilleNumber b) :=
  liouville_transcendental _ (liouville_liouvilleNumber hb)

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IX: MEASURE-THEORETIC PERSPECTIVE
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Almost All Numbers Are NOT Liouville

Despite being uncountable, Liouville numbers have **Lebesgue measure zero**.

**Theorem** (Borel, 1909): The set of Liouville numbers has measure zero.

This means:
- Liouville numbers are "rare" from a measure-theoretic perspective
- A random real number is almost surely NOT Liouville
- Yet the set is still uncountable (and of the same cardinality as ℝ)

**Proof idea**: For each n, the set of numbers with infinitely many
approximations |x - p/q| < 1/q^n can be covered by intervals whose
total measure tends to 0 as n → ∞.

**Contrast with transcendental numbers**: Almost all real numbers ARE transcendental
(since algebraic numbers are countable), but only measure zero of transcendentals
are Liouville.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART X: SUMMARY
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Summary of Wiedijk #18

**Liouville's Theorem** provides the first explicit proof that transcendental
numbers exist:

1. **The Approximation Bound**: Algebraic numbers of degree n cannot be
   approximated better than c/q^n by rationals p/q.

2. **Liouville Numbers**: Numbers that violate this bound for all n.

3. **Transcendence**: Liouville numbers must be transcendental.

4. **Explicit Example**: L = Σ 10^(-n!) is transcendental.

**Historical Impact**:
- First constructive proof of transcendental numbers (1844)
- Opened the field of transcendence theory
- Techniques evolved into Roth's theorem and beyond
- Foundational for Diophantine approximation

**Mathlib Status**: Fully formalized!
- `Liouville.transcendental`: The main theorem
- `liouvilleNumber`: The explicit constant
- `isLiouville_liouvilleNumber`: Verification of the Liouville property
-/

end LiouvilleTheorem
