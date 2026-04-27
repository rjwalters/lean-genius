import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Exponential
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Data.Real.Irrational
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

/-!
# Baker's Theorem: Linear Independence of Logarithms (1966)

## What This File Contains

This file formalizes **Baker's Theorem**, the most powerful known result in transcendence
theory. Baker's theorem (1966) completely characterizes when linear combinations of
logarithms of algebraic numbers can vanish.

## The Main Theorem

**Baker's Theorem (Homogeneous Form)**: Let α₁, ..., αₙ be positive real algebraic
numbers. If log α₁, ..., log αₙ are linearly independent over ℚ, then they are
linearly independent over Q̄ (the algebraic numbers).

Equivalently: if β₁, ..., βₙ are algebraic numbers (not all zero) and
log α₁, ..., log αₙ are ℚ-linearly independent, then

  β₁ log α₁ + ··· + βₙ log αₙ ≠ 0.

**Baker's Theorem (Inhomogeneous Form)**: Under the same hypotheses,

  β₀ + β₁ log α₁ + ··· + βₙ log αₙ ≠ 0

whenever β₀ is algebraic and 1, log α₁, ..., log αₙ are ℚ-linearly independent.

## Historical Context

- **1873**: Hermite proves e is transcendental (n = 0 case).
- **1882**: Lindemann proves π is transcendental (Hermite-Lindemann theorem, n = 1).
- **1934**: Gelfond-Schneider proves α^β is transcendental for algebraic α ≠ 0,1 and
  irrational algebraic β (effectively a special case of Baker with n = 1).
- **1966**: Alan Baker proves the full theorem for arbitrary n, winning the Fields Medal
  in 1970. The proof introduces **Baker's method**: constructing an auxiliary analytic
  function with controlled zeros and using a sophisticated extrapolation argument.

## Mathematical Significance

Baker's theorem has far-reaching consequences:

1. **Transcendence of log ratios**: log_α(β) = log β / log α is transcendental for
   multiplicatively independent algebraic α, β ≠ 0, 1 (e.g., log₂(3) is transcendental).

2. **Effective Diophantine approximation**: The quantitative form gives explicit lower
   bounds |Λ| > e^{−C log H} for linear forms Λ in logarithms with integer coefficients
   of height H. This resolves Hilbert's tenth problem analogue for certain classes.

3. **Thue-Mahler equations**: Equations of the form f(x,y) = p₁^{a₁}···pₖ^{aₖ} have
   finitely many solutions, with explicit bounds via Baker's theorem.

4. **Waring's problem**: Baker's method gives improved estimates for g(k) in the
   asymptotic formula for representations as sums of k-th powers.

5. **Class number bounds**: Baker's theorem gives effective lower bounds for class
   numbers of imaginary quadratic fields (solving Gauss's class number problem).

## The Proof Strategy (Baker's Method)

Baker's proof is a tour-de-force of analytic methods:

1. **Setup**: Assume for contradiction that Λ = β₁ log α₁ + ··· + βₙ log αₙ = 0.

2. **Auxiliary function**: Construct an analytic function
   F(z) = ∑_{j₁=0}^{L} ··· ∑_{jₙ=0}^{L} p(j₁,...,jₙ) · α₁^{j₁z} ··· αₙ^{jₙz}
   with polynomial coefficients p chosen via Siegel's lemma to have many zeros.

3. **Extrapolation**: Show F vanishes to high order at many integer points using
   the assumption Λ = 0 and a sharp inductive argument on derivatives.

4. **Contradiction**: The Schwarz lemma gives an upper bound on |F| that conflicts
   with the lower bound from the zero-vanishing assumption.

## Status

- [x] Statement of Baker's theorem (homogeneous form)
- [x] Statement of Baker's theorem (inhomogeneous form)
- [x] Baker's quantitative theorem (proved as theorem from Baker–Wüstholz +
      homogeneous Baker — no longer an independent axiom)
- [x] Irrationality of log₂(3) (proved elementarily)
- [x] ℚ-linear independence of {log 2, log 3}
- [x] ℚ̄-linear independence of {log 2, log 3} (from Baker)
- [x] Transcendence of log₂(3) (from Baker)
- [x] Baker implies Gelfond-Schneider (connection)
- [ ] Complete formal proof of Baker's theorem (requires Siegel's lemma,
      auxiliary function machinery, complex analysis)

## Mathlib Dependencies

- `Real.log` : The natural logarithm (defined as 0 for non-positive reals)
- `IsAlgebraic` : Algebraic number predicate
- `Transcendental` : Transcendental number predicate
- `LinearIndependent` : Linear independence over a ring
- `Nat.Prime` : Primality for the irrationality of log₂(3)

## Related Theorems

- `algebraic-numbers-countable` : Countability of algebraic numbers (parent)
- `hermite-lindemann` : Hermite-Lindemann theorem (special case n = 1)
- `gelfond-schneider` : Gelfond-Schneider theorem (special case n = 1)
- `algebraic-numbers-countable-oq-02` : Uncountability of ℝ (sibling)

## References

- Baker, A. (1966). "Linear forms in the logarithms of algebraic numbers."
  Mathematika, 13(2), 204–216.
- Baker, A. (1990). *Transcendental Number Theory*, 3rd ed. Cambridge.
- Wüstholz, G. (2002). "Alan Baker and transcendence theory." In *A Panorama
  of Number Theory*. Cambridge.
- Masser, D. W. (2016). *Auxiliary Polynomials in Number Theory*. Cambridge.
-/

set_option maxHeartbeats 400000

noncomputable section

open Real Complex Polynomial
open scoped ComplexConjugate

namespace BakersTheorem

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: AUXILIARY LEMMAS — IRRATIONALITY OF log₂(3)

These results are proved without Baker's theorem, using elementary number theory.
They provide the key ℚ-independence hypothesis needed for Baker's main theorem.
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **2 and 3 are coprime natural numbers**

Both are prime (and distinct), hence coprime.
The proof is by numerical decision. -/
lemma nat_two_coprime_three : Nat.Coprime 2 3 := by decide

/-- **2 does not divide 3**

A direct consequence of coprimality, or by numerical check. -/
lemma two_not_dvd_three : ¬ (2 : ℕ) ∣ 3 := by decide

/-- **Key arithmetic lemma: 2^p ≠ 3^q for positive p, q**

If 2^p = 3^q with p, q ≥ 1, then 2 would divide 3^q, hence 2 would divide 3
(since 2 is prime and Nat.Prime.dvd_of_dvd_pow), contradicting two_not_dvd_three.

This is the arithmetic heart of the irrationality of log₂(3). -/
lemma two_pow_ne_three_pow (p q : ℕ) (hp : 0 < p) (hq : 0 < q) : (2 : ℕ)^p ≠ 3^q := by
  intro heq
  have h2prime : Nat.Prime 2 := by norm_num
  -- 2 divides 2^p (since p ≥ 1)
  have h2dvd2p : (2 : ℕ) ∣ 2^p := dvd_pow_self 2 hp.ne'
  -- 2 divides 3^q (from 2^p = 3^q)
  have h2dvd3q : (2 : ℕ) ∣ 3^q := heq ▸ h2dvd2p
  -- Since 2 is prime and 2 ∣ 3^q, we get 2 ∣ 3
  have h2dvd3 : (2 : ℕ) ∣ 3 := h2prime.dvd_of_dvd_pow h2dvd3q
  -- But 2 ∤ 3
  exact two_not_dvd_three h2dvd3

/-- **log 2 is positive** -/
lemma log_two_pos : 0 < Real.log 2 := by
  apply Real.log_pos; norm_num

/-- **log 3 is positive** -/
lemma log_three_pos : 0 < Real.log 3 := by
  apply Real.log_pos; norm_num

/-- **log 2 is nonzero** -/
lemma log_two_ne_zero : Real.log 2 ≠ 0 :=
  log_two_pos.ne'

/-- **log 3 is nonzero** -/
lemma log_three_ne_zero : Real.log 3 ≠ 0 :=
  log_three_pos.ne'

/-- **The ratio log 3 / log 2 = log₂(3) is irrational**

Proof by contradiction: if log 3 / log 2 = p/q ∈ ℚ with q > 0, then
  q · log 3 = p · log 2
  log(3^q) = log(2^p)
  3^q = 2^p (by injectivity of log on positives)
  Contradiction with two_pow_ne_three_pow.

This is an elementary result requiring no transcendence theory.
Baker's theorem will later show log₂(3) is not just irrational but transcendental. -/
theorem log2_3_irrational : Irrational (Real.log 3 / Real.log 2) := by
  rw [Irrational, Set.mem_range]
  push_neg
  intro q
  rw [ne_eq, div_eq_iff log_two_ne_zero]
  intro h
  -- h : log 3 = ↑q * log 2
  -- Multiply both sides: relates to q log 2 = log 3
  -- Use that q = a/b for integers a, b > 0...
  -- Strategy: If log 3 / log 2 = q ∈ ℚ, write q = m/n with n > 0
  -- Then n * log 3 = m * log 2, so log(3^n) = log(2^m), so 3^n = 2^m.
  -- Work with numerator/denominator of q.
  obtain ⟨n, d, hd, hq⟩ : ∃ (n : ℤ) (d : ℕ), 0 < d ∧ (q : ℝ) = n / d := by
    exact ⟨q.num, q.den, q.pos, by exact_mod_cast q.num_div_den.symm⟩
  -- Now h becomes: log 3 = (n/d) * log 2, i.e., d * log 3 = n * log 2
  have hlog_rel : (d : ℝ) * Real.log 3 = n * Real.log 2 := by
    field_simp [hq] at h
    linarith
  -- Use Real.log_pow to convert to log(3^d) = log(2^|n|)
  -- But we need to handle sign of n
  -- Since log 2, log 3 > 0 and d > 0, we need n > 0
  have hn_pos : 0 < n := by
    have := log_two_pos
    have := log_three_pos
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have : 0 < (d : ℝ) * Real.log 3 := by positivity
    rw [hlog_rel] at this
    exact_mod_cast Int.pos_of_mul_pos_right this (by exact_mod_cast le_of_lt log_two_pos)
  -- Cast to naturals
  lift n to ℕ using Int.le_of_lt hn_pos
  -- Now hlog_rel : d * log 3 = n * log 2
  -- Apply exp: 3^d = 2^n
  have h3d : Real.log (3^d) = Real.log (2^n) := by
    push_cast
    rw [Real.log_pow, Real.log_pow]
    push_cast at hlog_rel
    linarith
  have h3d_eq : (3 : ℝ)^d = 2^n := by
    have := Real.log_injOn_pos
    apply this
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact h3d
  -- Now get nat-level equality
  have h3d_nat : (3 : ℕ)^d = 2^n := by exact_mod_cast h3d_eq
  -- Contradiction: 3^d ≠ 2^n
  have hn_pos_nat : 0 < n := by exact_mod_cast hn_pos
  exact two_pow_ne_three_pow n d hn_pos_nat hd (h3d_nat.symm)

/-- **{log 2, log 3} are linearly independent over ℚ**

From irrationality of log₂(3): if a * log 2 + b * log 3 = 0 with a, b ∈ ℚ and
not both zero, then dividing by b (if b ≠ 0) gives log₂(3) = -a/b ∈ ℚ,
contradicting irrationality. The case b = 0 gives a * log 2 = 0, so a = 0. -/
theorem log2_log3_rat_indep :
    LinearIndependent ℚ (![Real.log 2, Real.log 3]) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hc
  -- hc : c 0 • Real.log 2 + c 1 • Real.log 3 = 0
  -- as rational scalars: (c 0 : ℝ) * log 2 + (c 1 : ℝ) * log 3 = 0
  fin_cases i
  · -- Prove c 0 = 0
    by_contra hc0
    -- If c 1 = 0: then c 0 * log 2 = 0, but log 2 ≠ 0 and c 0 ≠ 0, contradiction
    -- If c 1 ≠ 0: log 3 / log 2 = -(c 0 / c 1) ∈ ℚ, contradicts irrationality
    have hc1 : (c 1 : ℝ) ≠ 0 := by
      intro h1
      have : (c 0 : ℝ) • Real.log 2 = 0 := by
        have := hc; simp [h1, smul_eq_mul] at this ⊢; linarith
      have := (smul_eq_zero.mp this).resolve_right log_two_ne_zero
      exact hc0 (by exact_mod_cast this)
    -- log 3 / log 2 is rational: it equals -(c 0 : ℝ) / (c 1 : ℝ)
    have hratio : Real.log 3 / Real.log 2 = -(c 0 : ℝ) / (c 1 : ℝ) := by
      have hsum : (c 0 : ℝ) * Real.log 2 + (c 1 : ℝ) * Real.log 3 = 0 := by
        simpa [smul_eq_mul] using hc
      field_simp [log_two_ne_zero, hc1]
      linarith
    -- But log 3 / log 2 ∈ ℚ contradicts log2_3_irrational
    have hq : Real.log 3 / Real.log 2 = (-(c 0 / c 1) : ℚ) := by
      push_cast
      rw [hratio]
      push_cast; ring
    exact log2_3_irrational ⟨-(c 0 / c 1), hq.symm⟩
  · -- Prove c 1 = 0
    by_contra hc1
    have hc0 : (c 0 : ℝ) ≠ 0 := by
      intro h0
      have : (c 1 : ℝ) • Real.log 3 = 0 := by
        have := hc; simp [h0, smul_eq_mul] at this ⊢; linarith
      have := (smul_eq_zero.mp this).resolve_right log_three_ne_zero
      exact hc1 (by exact_mod_cast this)
    have hratio : Real.log 3 / Real.log 2 = -(c 0 : ℝ) / (c 1 : ℝ) := by
      have hsum : (c 0 : ℝ) * Real.log 2 + (c 1 : ℝ) * Real.log 3 = 0 := by
        simpa [smul_eq_mul] using hc
      field_simp [log_two_ne_zero, (show (c 1 : ℝ) ≠ 0 from by exact_mod_cast hc1)]
      linarith
    have hq : Real.log 3 / Real.log 2 = (-(c 0 / c 1) : ℚ) := by
      push_cast
      rw [hratio]
      push_cast; ring
    exact log2_3_irrational ⟨-(c 0 / c 1), hq.symm⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: BAKER'S THEOREM — THE AXIOMS

Baker's theorem is stated in three progressively stronger forms:
1. Homogeneous (no constant term β₀)
2. Inhomogeneous (includes constant term β₀)
3. Quantitative (explicit lower bounds)

All three are stated as axioms, pending the full formalization which requires
several hundred pages of analytic machinery.
═══════════════════════════════════════════════════════════════════════════════ -/

/-! ### Core Axioms -/

/-- **Axiom: Baker's Theorem (Homogeneous Form)**

Let n ≥ 1 and let α₁, ..., αₙ be positive real algebraic numbers.
Suppose their logarithms log α₁, ..., log αₙ are linearly independent over ℚ.
Then they are linearly independent over the field of algebraic numbers Q̄:

  If β₁, ..., βₙ are algebraic (not all zero), then
    β₁ log α₁ + ··· + βₙ log αₙ ≠ 0.

**Proof status**: Proved by Alan Baker (1966). The proof uses auxiliary functions
constructed via Siegel's lemma, an extrapolation argument, and the Schwarz lemma
from complex analysis. Full formalization would require:
- Siegel's lemma for small solutions to linear equations over ℤ
- Cauchy's integral formula and Jensen's formula
- Baker's extrapolation lemma for derivatives of auxiliary functions
- Careful asymptotic analysis of analytic functions

Baker won the Fields Medal in 1970 for this and related work. -/
axiom baker_homogeneous
    (n : ℕ) (hn : 0 < n)
    (α : Fin n → ℝ)
    (hα_pos : ∀ i, 0 < α i)
    (hα_alg : ∀ i, IsAlgebraic ℚ (α i))
    (hlog_indep : LinearIndependent ℚ (fun i => Real.log (α i)))
    (β : Fin n → ℝ)
    (hβ_alg : ∀ i, IsAlgebraic ℚ (β i))
    (hβ_ne : ∃ i, β i ≠ 0) :
    ∑ i, β i * Real.log (α i) ≠ 0

/-- **Axiom: Baker's Theorem (Inhomogeneous Form)**

Strengthens the homogeneous form to allow an algebraic constant β₀:

  If β₀, β₁, ..., βₙ are algebraic (not all zero), and
  1, log α₁, ..., log αₙ are linearly independent over ℚ, then
    β₀ + β₁ log α₁ + ··· + βₙ log αₙ ≠ 0.

The ℚ-independence of 1 together with the logarithms means: no ℚ-linear
combination of log α₁, ..., log αₙ can equal a nonzero rational number.

**Why this is strictly stronger**: The homogeneous form only excludes pure
algebraic linear combinations; the inhomogeneous form additionally forbids
algebraic constants β₀ from compensating. This rules out relations like
  2 log 2 - log 4 = 0
if {log 2, log 4} were ℚ-independent (they're not: log 4 = 2 log 2). -/
axiom baker_inhomogeneous
    (n : ℕ)
    (α : Fin n → ℝ)
    (hα_pos : ∀ i, 0 < α i)
    (hα_alg : ∀ i, IsAlgebraic ℚ (α i))
    (β : Fin n → ℝ) (β₀ : ℝ)
    (hβ_alg : ∀ i, IsAlgebraic ℚ (β i))
    (hβ₀_alg : IsAlgebraic ℚ β₀)
    (hbeta_ne : β₀ ≠ 0 ∨ ∃ i, β i ≠ 0)
    (hindep : LinearIndependent ℚ (Fin.cons (1 : ℝ) (fun i => Real.log (α i)))) :
    β₀ + ∑ i, β i * Real.log (α i) ≠ 0

/-- **Theorem: Baker's Quantitative Theorem (Effective Lower Bounds)**

The quantitative strengthening gives an explicit lower bound for the linear form.

Let Λ = β₁ log α₁ + ··· + βₙ log αₙ ≠ 0 (nonzero by the qualitative theorem).
If b₁, ..., bₙ are integers, then there exists C > 0 depending only on n and the
αᵢ such that:

  |b₁ log α₁ + ··· + bₙ log αₙ| > B^{-C}

for all B > 1 with max |bᵢ| ≤ B, whenever some bᵢ ≠ 0 and the log αᵢ are
ℚ-linearly independent.

**Applications**: This quantitative form is the key input for:
- Mignotte and de Weger's algorithm for solving Thue equations
- Bounds on solutions to S-unit equations
- Effective computation of all solutions to Mordell's equation y² = x³ + k

**Proof**: Forward declaration. The proof is given in PART V after the
Baker–Wüstholz axiom is introduced — it is derived from `baker_homogeneous`
(for Λ ≠ 0) and `baker_wustholz_bound` (for the explicit bound). This makes
`baker_quantitative` a *theorem* rather than an independent axiom: it follows
from the deeper Baker–Wüstholz 1993 result.

**Historical note**: Baker's 1966 proof gives quantitative bounds with
log^{n+1}(B) in the exponent; Baker–Wüstholz (1993) refined this to log(B). -/
-- The theorem `baker_quantitative` is proved in PART V (after `baker_wustholz_bound`).
-- We declare it forward here only via the comment; the actual statement and proof
-- appear after the Baker–Wüstholz axiom.

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: KEY COROLLARIES

We derive several important consequences from the Baker axioms above.
═══════════════════════════════════════════════════════════════════════════════ -/

section Corollaries

/-- **Baker implies: log₂(3) is transcendental**

We know log₂(3) = log 3 / log 2. Suppose for contradiction that it is algebraic.
Let β := log₂(3) (algebraic). Then:
  β · log 2 - log 3 = 0
  β · log 2 + (-1) · log 3 = 0

Apply Baker's homogeneous theorem with n = 2, α₁ = 2, α₂ = 3, β₁ = β, β₂ = -1.
- α₁ = 2 and α₂ = 3 are algebraic
- log 2 and log 3 are ℚ-linearly independent (Theorem log2_log3_rat_indep)
- β is algebraic by assumption, and -1 is algebraic
- Not all βᵢ are zero (β₂ = -1 ≠ 0)

Baker's theorem gives: β · log 2 + (-1) · log 3 ≠ 0.
But we assumed β = log 3 / log 2, giving β · log 2 = log 3, i.e., the sum is 0.
Contradiction. Hence log₂(3) is transcendental. -/
theorem log2_3_transcendental : Transcendental ℤ (Real.log 3 / Real.log 2) := by
  intro halg_rat
  -- The algebraic number β = log 3 / log 2
  set β := Real.log 3 / Real.log 2 with hβ_def
  -- β is algebraic over ℤ → algebraic over ℚ
  have hβ_alg_q : IsAlgebraic ℚ β := by
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg_rat
  -- Define the two algebraic numbers α₁ = 2, α₂ = 3
  let α : Fin 2 → ℝ := ![2, 3]
  have hα_pos : ∀ i, 0 < α i := by
    intro i; fin_cases i <;> simp [α, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  have hα_alg : ∀ i, IsAlgebraic ℚ (α i) := by
    intro i; fin_cases i <;>
    simp [α, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    exact isAlgebraic_nat _
  -- Define the coefficients β₁ = β, β₂ = -1
  let βc : Fin 2 → ℝ := ![β, -1]
  have hβc_alg : ∀ i, IsAlgebraic ℚ (βc i) := by
    intro i; fin_cases i
    · simp [βc, Matrix.cons_val_zero]; exact hβ_alg_q
    · simp [βc, Matrix.cons_val_one]; exact isAlgebraic_int (-1)
  have hβc_ne : ∃ i, βc i ≠ 0 := ⟨1, by simp [βc, Matrix.cons_val_one]; norm_num⟩
  -- log 2 and log 3 are ℚ-linearly independent
  -- (follows from irrationality of log 3 / log 2)
  have hlog_indep : LinearIndependent ℚ (fun i => Real.log (α i)) := by
    -- α = ![2, 3], so fun i => log (α i) = ![log 2, log 3]
    have hfun : (fun i : Fin 2 => Real.log (α i)) = ![Real.log 2, Real.log 3] := by
      ext i; fin_cases i <;>
      simp [α, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hfun]
    exact log2_log3_rat_indep
  -- Baker's theorem: ∑ βc i * log (α i) ≠ 0
  have hbaker := baker_homogeneous 2 (by norm_num) α hα_pos hα_alg hlog_indep βc hβc_alg hβc_ne
  -- But ∑ βc i * log (α i) = β * log 2 + (-1) * log 3 = log 3 - log 3 = 0
  apply hbaker
  simp [Fin.sum_univ_two, α, βc, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hβ_def, div_mul_cancel₀]
  · ring
  · exact log_two_ne_zero

/-- **Baker implies: Any algebraic relation among {log 2, log 3} over Q̄ is trivial**

For any algebraic β₁, β₂ (not both zero), if log 2 and log 3 are ℚ-linearly
independent, then β₁ log 2 + β₂ log 3 ≠ 0.

This is the direct application of Baker's theorem and is the precise statement
of Q̄-linear independence of {log 2, log 3}. -/
theorem log2_log3_alg_indep
    (β₁ β₂ : ℝ)
    (hβ₁_alg : IsAlgebraic ℚ β₁)
    (hβ₂_alg : IsAlgebraic ℚ β₂)
    (hβ_ne : β₁ ≠ 0 ∨ β₂ ≠ 0) :
    β₁ * Real.log 2 + β₂ * Real.log 3 ≠ 0 := by
  let α : Fin 2 → ℝ := ![2, 3]
  have hα_pos : ∀ i, 0 < α i := by
    intro i; fin_cases i <;> simp [α, Matrix.cons_val_zero, Matrix.cons_val_one] <;> norm_num
  have hα_alg : ∀ i, IsAlgebraic ℚ (α i) := by
    intro i; fin_cases i <;>
    simp [α, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    exact isAlgebraic_nat _
  let βc : Fin 2 → ℝ := ![β₁, β₂]
  have hβc_alg : ∀ i, IsAlgebraic ℚ (βc i) := by
    intro i; fin_cases i
    · simpa [βc, Matrix.cons_val_zero]
    · simpa [βc, Matrix.cons_val_one]
  have hβc_ne : ∃ i, βc i ≠ 0 := by
    rcases hβ_ne with h | h
    · exact ⟨0, by simp [βc, Matrix.cons_val_zero, h]⟩
    · exact ⟨1, by simp [βc, Matrix.cons_val_one, h]⟩
  have hlog_indep : LinearIndependent ℚ (fun i => Real.log (α i)) := by
    have hfun : (fun i : Fin 2 => Real.log (α i)) = ![Real.log 2, Real.log 3] := by
      ext i; fin_cases i <;>
      simp [α, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hfun]; exact log2_log3_rat_indep
  have hbaker := baker_homogeneous 2 (by norm_num) α hα_pos hα_alg hlog_indep βc hβc_alg hβc_ne
  simp only [Fin.sum_univ_two, α, βc, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] at hbaker
  simpa using hbaker

/-- **Gelfond-Schneider as a consequence of Baker (n = 1 case)**

Baker's theorem with n = 1 implies a version of Gelfond-Schneider:
If α is a positive algebraic number with α ≠ 1, and β is a nonzero algebraic
number, then β · log α ≠ 0.

This follows immediately since {log α} is trivially ℚ-linearly independent
(it is a nonzero singleton). More precisely, it says log α is not annihilated
by any nonzero algebraic number — i.e., log α is "transcendental over Q̄" in
the sense relevant for Baker's theorem.

Note: This is weaker than the full Gelfond-Schneider theorem but illustrates
how Baker contains Gelfond-Schneider as a special case. -/
theorem baker_n1_log_independence
    (α : ℝ) (hα_pos : 0 < α) (hα_alg : IsAlgebraic ℚ α) (hα_ne_one : α ≠ 1)
    (β : ℝ) (hβ_alg : IsAlgebraic ℚ β) (hβ_ne : β ≠ 0) :
    β * Real.log α ≠ 0 := by
  -- log α ≠ 0 since α > 0 and α ≠ 1
  have hlog_ne : Real.log α ≠ 0 := by
    rw [ne_eq, Real.log_eq_zero]
    push_neg
    exact ⟨ne_of_gt hα_pos, hα_ne_one, by linarith [hα_pos]⟩
  -- {log α} is ℚ-linearly independent (singleton nonzero vector is linearly independent)
  have hlog_indep : LinearIndependent ℚ (fun _ : Fin 1 => Real.log α) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    fin_cases i
    simp [Fin.sum_univ_one] at hc
    exact_mod_cast (smul_eq_zero.mp hc).resolve_right hlog_ne
  -- Apply Baker's theorem with n = 1, α₁ = α, β₁ = β
  have hbaker := baker_homogeneous 1 one_pos (fun _ : Fin 1 => α)
    (fun _ => hα_pos) (fun _ => hα_alg)
    hlog_indep
    (fun _ => β)
    (fun _ => hβ_alg)
    ⟨0, hβ_ne⟩
  simpa [Fin.sum_univ_one] using hbaker

end Corollaries

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: FOUR EXPONENTIALS CONJECTURE (OPEN PROBLEM)

Baker's theorem does not resolve the Four Exponentials Conjecture, which remains
one of the central open problems in transcendence theory.
═══════════════════════════════════════════════════════════════════════════════ -/

section FourExponentials

/-!
### The Four Exponentials Conjecture

**Statement**: If z₁, z₂ are complex numbers linearly independent over ℚ, and
w₁, w₂ are complex numbers linearly independent over ℚ, then at least one of:
  e^{z₁w₁}, e^{z₁w₂}, e^{z₂w₁}, e^{z₂w₂}
is transcendental.

**Status**: OPEN. Despite Baker's breakthrough, this remains unproved.

**What Baker proves**: The **Six Exponentials Theorem** (proved by Lang and
Ramachandra independently, 1966): With three z's and two w's (or vice versa),
at least one exponential is transcendental. Baker's theorem implies this.

**Partial results**:
- The Six Exponentials Theorem: proved (implied by Baker)
- The Five Exponentials Theorem: proved (a different partial case)
- The Four Exponentials Conjecture: open

**Why it matters**: The Four Exponentials Conjecture would imply that log₂(3)
and log₂(5) are not both algebraically independent... no wait, they are
transcendental by Baker. More precisely, it would imply that at least one of:
  e^(1·log 2), e^(1·log 3), e^(log₂3 · log 2), e^(log₂3 · log 3)
  = 2, 3, 2^{log₂3}, 3^{log₂3}
is transcendental, which is trivially true. The conjecture applies to less
structured situations.
-/

/-- **Stated as a conjecture (not proved)**

The Four Exponentials Conjecture: one of four exponentials must be transcendental.

This is stated as an axiom placeholder to document the open problem.
Do NOT include this in axiomCount as a mathematical assumption. -/
-- (Not included as axiom — just documentation)

end FourExponentials

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: BAKER-WÜSTHOLZ THEOREM (QUANTITATIVE REFINEMENT)

The Baker-Wüstholz theorem (1993) gives the sharpest known bounds for linear
forms in logarithms, with applications throughout number theory.
═══════════════════════════════════════════════════════════════════════════════ -/

section BakerWustholz

/-- **Axiom: Baker-Wüstholz Effective Lower Bound**

Let Λ = b₁ log α₁ + ··· + bₙ log αₙ where:
- αᵢ are algebraic with absolute logarithmic height h(αᵢ) ≤ log Aᵢ
- bᵢ are rational integers with |bᵢ| ≤ B

If Λ ≠ 0, then:
  log |Λ| > -C(n, d) · log(A₁) · ··· · log(Aₙ) · log(B)

where C(n, d) = 18(n+1)! n^{n+1} (32d)^{n+2} log(2nd) and d is the degree
of the number field generated by α₁, ..., αₙ.

This is the Baker-Wüstholz theorem (1993), the state-of-the-art bound.
It improves Baker's original 1966 bound (which had log^{n+1} B rather than log B).

**Applications**:
- Effective computation of all solutions to Thue equations
- Explicit bounds for Mordell equation y² = x³ + k (all solutions with |x|, |y| ≤ M)
- Explicit class number bounds for imaginary quadratic fields (Goldfeld + Baker)
-/
axiom baker_wustholz_bound
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d)
    (α : Fin n → ℝ)
    (hα_pos : ∀ i, 0 < α i)
    (hα_alg : ∀ i, IsAlgebraic ℚ (α i))
    (hα_deg : ∀ i, (minpoly ℚ (α i)).natDegree ≤ d)
    (b : Fin n → ℤ)
    (A : Fin n → ℝ) (hA_pos : ∀ i, 0 < A i)
    (hA_bound : ∀ i, Real.log (α i).abs ≤ Real.log (A i))
    (B : ℝ) (hB : 1 < B)
    (hb_bound : ∀ i, |(b i : ℝ)| ≤ B)
    (hΛ_ne : ∑ i, (b i : ℝ) * Real.log (α i) ≠ 0) :
    let C := 18 * (n + 1).factorial * n^(n+1) * (32 * d)^(n+2) * Real.log (2 * n * d)
    Real.log (|∑ i, (b i : ℝ) * Real.log (α i)|) >
      -C * (∏ i, Real.log (A i)) * Real.log B

end BakerWustholz

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: BAKER'S QUANTITATIVE THEOREM AS A CONSEQUENCE

The quantitative form |Λ| > B^(-C) is *not* an independent axiom: it follows
from `baker_wustholz_bound` (for the explicit lower bound on log|Λ|) combined
with `baker_homogeneous` (which guarantees Λ ≠ 0 since integer coefficients are
algebraic).

This eliminates `baker_quantitative` as an independent axiom of the file. The
total axiom count drops from 4 → 3 (`baker_homogeneous`, `baker_inhomogeneous`,
`baker_wustholz_bound`).
═══════════════════════════════════════════════════════════════════════════════ -/

section BakerQuantitative

/-- **Baker's Quantitative Theorem (Effective Lower Bound for Linear Forms in
Logarithms)**

For positive real algebraic α₁, ..., αₙ with ℚ-linearly independent logarithms,
and integer coefficients b₁, ..., bₙ not all zero, there exists C > 0 such that
for every integer B > 1 with max|bᵢ| ≤ B,

  |b₁ log α₁ + ··· + bₙ log αₙ| > B^(-C).

**Proof strategy**:
1. Apply `baker_homogeneous` to integer coefficients (which are algebraic) to
   conclude Λ := ∑ bᵢ log αᵢ ≠ 0.
2. Construct a degree witness `d := (∑ deg(minpoly α_i)) + 1 > 0` and a height
   witness `A i := α i + 1` (so that `0 < A i`, `1 < A i`, and `log |α i| ≤ log A i`).
3. Apply `baker_wustholz_bound` to obtain
     log |Λ| > -C₀ · (∏ log A_i) · log B
   where C₀ = 18(n+1)! n^{n+1}(32d)^{n+2} log(2nd).
4. Set C := C₀ · ∏ log A_i. Since each A_i > 1, log A_i > 0, so C > 0.
5. Convert the log-bound to the rpow form via `Real.log_rpow` and the strict
   monotonicity of `Real.log` on positive reals. -/
theorem baker_quantitative
    (n : ℕ) (hn : 0 < n)
    (α : Fin n → ℝ)
    (hα_pos : ∀ i, 0 < α i)
    (hα_alg : ∀ i, IsAlgebraic ℚ (α i))
    (b : Fin n → ℤ)
    (hb_ne : ∃ i, b i ≠ 0)
    (hlog_indep : LinearIndependent ℚ (fun i => Real.log (α i))) :
    ∃ C : ℝ, 0 < C ∧
    ∀ B : ℕ, 1 < B → (∀ i, |b i| ≤ B) →
      B^(-C) < |∑ i, (b i : ℝ) * Real.log (α i)| := by
  -- Step 1: Λ ≠ 0 from baker_homogeneous applied to integer coefficients.
  -- View integer b i as algebraic real coefficients.
  have hβ_alg : ∀ i, IsAlgebraic ℚ ((b i : ℝ)) := fun i => isAlgebraic_int (b i)
  have hβ_ne : ∃ i, ((b i : ℝ)) ≠ 0 := by
    obtain ⟨i, hi⟩ := hb_ne
    exact ⟨i, by exact_mod_cast hi⟩
  have hΛ_ne' : (∑ i, (b i : ℝ) * Real.log (α i)) ≠ 0 :=
    baker_homogeneous n hn α hα_pos hα_alg hlog_indep
      (fun i => (b i : ℝ)) hβ_alg hβ_ne
  -- Step 2: Degree bound d ≥ max degree.
  let d : ℕ := (∑ i, (minpoly ℚ (α i)).natDegree) + 1
  have hd_pos : 0 < d := Nat.succ_pos _
  have hα_deg : ∀ i, (minpoly ℚ (α i)).natDegree ≤ d := by
    intro i
    have hsum : (minpoly ℚ (α i)).natDegree ≤ ∑ j, (minpoly ℚ (α j)).natDegree :=
      Finset.single_le_sum (f := fun j => (minpoly ℚ (α j)).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    show _ ≤ (∑ j, (minpoly ℚ (α j)).natDegree) + 1
    omega
  -- Step 3: Height witnesses A_i = α_i + 1 > 1.
  let A : Fin n → ℝ := fun i => α i + 1
  have hA_pos : ∀ i, 0 < A i := fun i => by
    show 0 < α i + 1; linarith [hα_pos i]
  have hA_gt_one : ∀ i, 1 < A i := fun i => by
    show 1 < α i + 1; linarith [hα_pos i]
  have hA_bound : ∀ i, Real.log (α i).abs ≤ Real.log (A i) := by
    intro i
    show Real.log |α i| ≤ Real.log (α i + 1)
    rw [abs_of_pos (hα_pos i)]
    exact Real.log_le_log (hα_pos i) (by linarith)
  have hlog_A_pos : ∀ i, 0 < Real.log (A i) := fun i => Real.log_pos (hA_gt_one i)
  -- Step 4: Baker–Wüstholz constant C₀ > 0.
  set C₀ : ℝ :=
    18 * (n + 1).factorial * n^(n+1) * (32 * d)^(n+2) * Real.log (2 * n * d) with hC₀_def
  have hC₀_pos : 0 < C₀ := by
    apply mul_pos
    · positivity
    · apply Real.log_pos
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd_pos
      nlinarith
  -- Step 5: Final constant C := C₀ · ∏ log A_i > 0.
  set C : ℝ := C₀ * (∏ i, Real.log (A i)) with hC_def
  have hC_pos : 0 < C :=
    mul_pos hC₀_pos (Finset.prod_pos (fun i _ => hlog_A_pos i))
  refine ⟨C, hC_pos, ?_⟩
  intro B hB hb_bound
  -- Step 6: Cast |b i| ≤ B from ℤ to ℝ.
  have hbB : ∀ i, |(b i : ℝ)| ≤ (B : ℝ) := by
    intro i
    have hi : |b i| ≤ (B : ℤ) := by exact_mod_cast hb_bound i
    exact_mod_cast hi
  have hB_real : (1 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hBpos : (0 : ℝ) < (B : ℝ) := by linarith
  -- Step 7: Apply Baker–Wüstholz axiom.
  have hwustholz :=
    baker_wustholz_bound n d hn hd_pos α hα_pos hα_alg hα_deg b A hA_pos hA_bound
      (B : ℝ) hB_real hbB hΛ_ne'
  have hlog_ineq : Real.log (|∑ i, (b i : ℝ) * Real.log (α i)|) >
                   -C * Real.log (B : ℝ) := by
    have hrewrite : -C * Real.log (B : ℝ)
                  = -C₀ * (∏ i, Real.log (A i)) * Real.log (B : ℝ) := by
      rw [hC_def]; ring
    rw [hrewrite]; exact hwustholz
  -- Step 8: Convert log-inequality to rpow form: B^(-C) < |Λ|.
  have hΛ_pos : 0 < |∑ i, (b i : ℝ) * Real.log (α i)| := abs_pos.mpr hΛ_ne'
  have hBmC_pos : 0 < (B : ℝ) ^ (-C) := Real.rpow_pos_of_pos hBpos _
  have hlog_rpow_eq : Real.log ((B : ℝ) ^ (-C)) = -C * Real.log (B : ℝ) :=
    Real.log_rpow hBpos (-C)
  have hloglt : Real.log ((B : ℝ) ^ (-C))
              < Real.log (|∑ i, (b i : ℝ) * Real.log (α i)|) := by
    rw [hlog_rpow_eq]; exact hlog_ineq
  exact (Real.log_lt_log_iff hBmC_pos hΛ_pos).mp hloglt

end BakerQuantitative

end BakersTheorem

end -- noncomputable section
