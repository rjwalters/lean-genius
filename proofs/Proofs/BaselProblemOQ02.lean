/-
Open Question: Are all odd zeta values ζ(2k+1) transcendental?

**Problem Statement (OPEN)**

Building on the Basel Problem (∑ 1/n² = π²/6), this formalizes the
open question about the arithmetic nature of odd zeta values.

**Known Results:**
- ζ(2k) = rational × π^(2k), hence transcendental (Euler + Lindemann 1882)
- ζ(3) is irrational (Apéry, 1978)
- Infinitely many ζ(2k+1) are irrational (Rivoal, 2000)
- At least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational (Zudilin, 2001)

**Open:** Is ζ(3) transcendental? Is any specific ζ(2k+1) transcendental?

**Formalization Summary:**
- General zetaValue infrastructure: summability, positivity, bounds
- Even zeta values: closed forms from Mathlib, transcendence from Lindemann axiom
- Odd zeta values: conjectures stated, Apéry axiomatized
- Structural relationships connecting transcendence to irrationality

**Status**: OPEN for odd values; PROVED for even values (from Lindemann)

Source: Extension of the Basel Problem formalization
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

open BigOperators Filter Topology Real Polynomial

namespace BaselProblemOQ02

-- ============================================================================
-- ## Part 1: Zeta Values at Natural Numbers
-- ============================================================================

/-- The Riemann zeta function at natural number s:
    ζ(s) = ∑_{n=1}^∞ 1/n^s (as a tsum over ℕ, with the n=0 term vanishing). -/
noncomputable def zetaValue (s : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s

-- ============================================================================
-- ## Part 2: General zetaValue Infrastructure
-- ============================================================================

/-- The p-series ∑ 1/n^s converges for s ≥ 2.
    Uses p-series convergence criterion from Mathlib. -/
theorem summable_zetaValue (s : ℕ) (hs : 2 ≤ s) :
    Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ s) := by
  have hlt : (1 : ℝ) < (s : ℝ) := by exact_mod_cast (show 1 < s by omega)
  have h := Real.summable_nat_rpow_inv.mpr hlt
  convert h using 1
  ext n; simp [div_eq_mul_inv]

/-- Each term of the zeta series is nonneg. -/
lemma zetaValue_term_nonneg (s n : ℕ) : (0 : ℝ) ≤ 1 / (n : ℝ) ^ s := by positivity

/-- ζ(s) ≥ 1 for s ≥ 2 (the n=1 term alone contributes 1, all others ≥ 0). -/
theorem zetaValue_ge_one (s : ℕ) (hs : 2 ≤ s) : 1 ≤ zetaValue s := by
  unfold zetaValue
  apply hasSum_le _ (hasSum_ite_eq (1 : ℕ) (1 : ℝ)) (summable_zetaValue s hs).hasSum
  intro n
  split_ifs with h
  · subst h; simp
  · positivity

/-- ζ(s) > 0 for s ≥ 2. -/
theorem zetaValue_pos (s : ℕ) (hs : 2 ≤ s) : 0 < zetaValue s :=
  lt_of_lt_of_le one_pos (zetaValue_ge_one s hs)

/-- ζ(s) ≠ 0 for s ≥ 2. -/
theorem zetaValue_ne_zero (s : ℕ) (hs : 2 ≤ s) : zetaValue s ≠ 0 :=
  ne_of_gt (zetaValue_pos s hs)

-- ============================================================================
-- ## Part 3: Known Even Zeta Values
-- ============================================================================

/-- ζ(2) = π²/6 — the Basel Problem (Euler 1734). -/
theorem zetaValue_two : zetaValue 2 = π ^ 2 / 6 := by
  unfold zetaValue; exact hasSum_zeta_two.tsum_eq

/-- ζ(4) = π⁴/90 (Euler). -/
theorem zetaValue_four : zetaValue 4 = π ^ 4 / 90 := by
  unfold zetaValue; exact hasSum_zeta_four.tsum_eq

-- ============================================================================
-- ## Part 4: Deep Axioms (Results Not Yet in Mathlib)
-- ============================================================================

/-- **Lindemann's Theorem (1882)**: π is transcendental over ℚ.
    This is the key ingredient for showing even zeta values are transcendental.
    Not yet in Mathlib v4.26.0. -/
axiom pi_transcendental : Transcendental ℚ (Real.pi : ℝ)

/-- **Apéry's Theorem (1978)**: ζ(3) is irrational.
    The first (and still only individually named) odd zeta value
    proved irrational. The proof uses rapidly converging series
    and is one of the most celebrated results in 20th century number theory. -/
axiom apery_theorem : Irrational (zetaValue 3)

-- ============================================================================
-- ## Part 5: Even Zeta Value Transcendence
-- ============================================================================

/-- Helper: composition of a nonzero polynomial with a polynomial of positive
    natDegree is nonzero. Over an integral domain, natDegree(p.comp g) =
    natDegree(p) * natDegree(g), so if p ≠ 0 and natDegree(g) > 0, the
    composition is nonzero (either natDegree p = 0 and p is a nonzero constant
    that comp preserves, or natDegree p > 0 and the product is positive). -/
private lemma comp_ne_zero_of_pos_natDegree {p g : ℚ[X]} (hp : p ≠ 0)
    (hg : 0 < g.natDegree) : p.comp g ≠ 0 := by
  rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
  · -- p is a nonzero constant: p = C(p.coeff 0), comp with anything = p
    have heq := eq_C_of_natDegree_eq_zero hd
    rw [heq, C_comp]
    rwa [heq] at hp
  · -- p has positive degree: natDegree(p.comp g) = natDegree(p) * natDegree(g) > 0
    intro h
    have hpos : 0 < (p.comp g).natDegree := by
      rw [natDegree_comp]
      exact Nat.mul_pos hd hg
    simp [h] at hpos

/-- Key algebraic lemma: if x is transcendental over ℚ and n ≥ 1,
    then x^n is transcendental over ℚ.

    Proof: If p(x^n) = 0 for nonzero p ∈ ℚ[X], then the polynomial
    q(t) = p(t^n) ∈ ℚ[X] satisfies q(x) = 0 and q ≠ 0 (since
    natDegree(X^n) = n > 0), contradicting transcendence of x. -/
theorem transcendental_pow_of_transcendental {x : ℝ} (hx : Transcendental ℚ x)
    {n : ℕ} (hn : 0 < n) : Transcendental ℚ (x ^ n) := by
  intro ⟨p, hp_ne, hp_eval⟩
  apply hx
  refine ⟨p.comp (X ^ n), ?_, ?_⟩
  · exact comp_ne_zero_of_pos_natDegree hp_ne
      (by simp only [natDegree_X_pow]; omega)
  · rw [aeval_comp, map_pow, aeval_X]
    exact hp_eval

/-- ζ(2) = π²/6 is transcendental over ℚ.

    Proof: π² is transcendental (from transcendental_pow). If π²/6 were
    algebraic, then 6 · (π²/6) = π² would be algebraic (product of
    algebraic numbers). Contradiction. -/
theorem zetaValue_two_transcendental : Transcendental ℚ (zetaValue 2) := by
  rw [zetaValue_two]
  have h_pi2 : Transcendental ℚ (π ^ 2) :=
    transcendental_pow_of_transcendental pi_transcendental (by norm_num)
  intro h_alg
  apply h_pi2
  -- π² = 6 * (π²/6)
  have heq : (π : ℝ) ^ 2 = algebraMap ℚ ℝ 6 * (π ^ 2 / 6) := by
    have : algebraMap ℚ ℝ = (↑· : ℚ → ℝ) := funext fun _ => rfl
    rw [this]; push_cast; ring
  rw [heq]
  exact (isAlgebraic_algebraMap (6 : ℚ)).mul h_alg

/-- ζ(4) = π⁴/90 is transcendental over ℚ.
    Same technique: if π⁴/90 were algebraic, then 90 · (π⁴/90) = π⁴
    would be algebraic. But π⁴ is transcendental (from transcendental_pow). -/
theorem zetaValue_four_transcendental : Transcendental ℚ (zetaValue 4) := by
  rw [zetaValue_four]
  have h_pi4 : Transcendental ℚ (π ^ 4) :=
    transcendental_pow_of_transcendental pi_transcendental (by norm_num)
  intro h_alg
  apply h_pi4
  have heq : (π : ℝ) ^ 4 = algebraMap ℚ ℝ 90 * (π ^ 4 / 90) := by
    have : algebraMap ℚ ℝ = (↑· : ℚ → ℝ) := funext fun _ => rfl
    rw [this]; push_cast; ring
  rw [heq]
  exact (isAlgebraic_algebraMap (90 : ℚ)).mul h_alg

-- ============================================================================
-- ## Part 6: The Open Conjecture
-- ============================================================================

/-- **Open Conjecture: Transcendence of Odd Zeta Values**

    All odd zeta values ζ(2k+1) for k ≥ 1 are transcendental.
    Not a single odd zeta value has been proved transcendental.
    Even the transcendence of ζ(3) alone is a major open problem. -/
def odd_zeta_transcendence_conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → Transcendental ℚ (zetaValue (2 * k + 1))

/-- **Weaker Open Conjecture: Irrationality of all odd zeta values.**
    While we know infinitely many are irrational (Rivoal 2000),
    we cannot prove irrationality for any specific ζ(2k+1) beyond ζ(3). -/
def odd_zeta_irrationality_conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → Irrational (zetaValue (2 * k + 1))

-- ============================================================================
-- ## Part 7: Structural Relationships
-- ============================================================================

/-- The transcendence conjecture implies the irrationality conjecture. -/
theorem transcendence_implies_irrationality :
    odd_zeta_transcendence_conjecture → odd_zeta_irrationality_conjecture := by
  intro h k hk
  exact Transcendental.irrational (h k hk)

/-- The conjecture specialized to ζ(3) implies Apéry's theorem. -/
theorem conjecture_implies_apery :
    odd_zeta_irrationality_conjecture → Irrational (zetaValue 3) := by
  intro h
  exact h 1 le_rfl

/-- Apéry's theorem is weaker than the full irrationality conjecture. -/
theorem apery_weaker_than_conjecture :
    odd_zeta_irrationality_conjecture →
    Irrational (zetaValue 3) ∧ Irrational (zetaValue 5) := by
  intro h
  exact ⟨h 1 le_rfl, h 2 (by omega)⟩

-- ============================================================================
-- ## Part 8: Deep Results on Odd Zeta Irrationality
-- ============================================================================

/-- **Rivoal's Theorem (2000)**: Infinitely many odd zeta values are irrational.
    Proved using very-well-poised hypergeometric series and a linear independence
    criterion. The precise result: the ℚ-vector space spanned by
    1, ζ(3), ζ(5), ..., ζ(s) has dimension ≥ c · log s as s → ∞.
    Not yet in Mathlib. -/
axiom rivoal_theorem :
  {k : ℕ | 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))}.Infinite

/-- **Zudilin's Theorem (2001)**: At least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational.
    Refines Ball–Rivoal method with well-poised hypergeometric series.
    Not yet in Mathlib. -/
axiom zudilin_theorem :
  Irrational (zetaValue 5) ∨ Irrational (zetaValue 7) ∨
  Irrational (zetaValue 9) ∨ Irrational (zetaValue 11)

/-- **Fischler–Sprang–Zudilin (2019)**: A quantitative strengthening of Rivoal's theorem.
    Among the odd zeta values ζ(3), ζ(5), ..., ζ(2s+1), for any ε ∈ (0,1) and all
    sufficiently large s, at least (1−ε)·log(s)/(1+log 2) of them are irrational.

    Formally: for each ε ∈ (0,1) there is a threshold s₀ such that for all s ≥ s₀,
    there exists a finite set S ⊆ {1,...,s} with |S| ≥ (1−ε)·log(s)/(1+log 2)
    and ζ(2k+1) irrational for every k ∈ S.

    This dramatically strengthens Rivoal's qualitative "infinitely many" to a
    logarithmic lower bound — the current state of the art on odd zeta irrationality.
    Reference: Compositio Mathematica 155(5), pp. 938–952, 2019. Not yet in Mathlib. -/
axiom fischler_sprang_zudilin_2019 (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∃ (S : Finset ℕ),
        (1 - ε) * Real.log s / (1 + Real.log 2) ≤ (S.card : ℝ) ∧
        ∀ k ∈ S, k ≤ s ∧ 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))

-- ============================================================================
-- ## Part 9: The Irrationality Landscape
-- ============================================================================

/-- The full irrationality conjecture implies Rivoal's theorem:
    if ALL odd zeta values are irrational, certainly infinitely many are. -/
theorem conjecture_implies_rivoal :
    odd_zeta_irrationality_conjecture →
    {k : ℕ | 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))}.Infinite := by
  intro h
  apply Set.infinite_of_injective_forall_mem (f := fun n => n + 1)
    (fun a b hab => by omega)
  intro n
  exact ⟨by omega, h (n + 1) (by omega)⟩

/-- The full irrationality conjecture implies Zudilin's theorem. -/
theorem conjecture_implies_zudilin :
    odd_zeta_irrationality_conjecture →
    Irrational (zetaValue 5) ∨ Irrational (zetaValue 7) ∨
    Irrational (zetaValue 9) ∨ Irrational (zetaValue 11) := by
  intro h
  exact Or.inl (h 2 (by omega))

/-- The hierarchy of known results:
    Transcendence conjecture ⟹ Irrationality conjecture ⟹ Rivoal + Zudilin + Apéry.
    This gives a concrete summary: knowing the conjecture recovers all known results. -/
theorem conjecture_implies_all_known :
    odd_zeta_transcendence_conjecture →
    (Irrational (zetaValue 3)) ∧
    ({k : ℕ | 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))}.Infinite) ∧
    (Irrational (zetaValue 5) ∨ Irrational (zetaValue 7) ∨
     Irrational (zetaValue 9) ∨ Irrational (zetaValue 11)) := by
  intro h
  have hirr := transcendence_implies_irrationality h
  exact ⟨conjecture_implies_apery hirr,
         conjecture_implies_rivoal hirr,
         conjecture_implies_zudilin hirr⟩

-- ============================================================================
-- ## Part 10: The Even–Odd Divide
-- ============================================================================

/-- The stark contrast between even and odd zeta values:
    - Even: ζ(2k) = rational × π^(2k), fully understood since Euler (1734)
    - Odd: ζ(2k+1) has no known closed form; arithmetic nature mostly unknown

    This definition captures the even case: ζ(2k) is a rational multiple of π^(2k). -/
def even_zeta_rational_multiple (k : ℕ) (_ : k ≠ 0) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ zetaValue (2 * k) = q * π ^ (2 * k)

/-- **Even Zeta Values Are Transcendental** (conditional on Lindemann).

    For all k ≥ 1, ζ(2k) is transcendental over ℚ. This follows from:
    1. ζ(2k) = c_k · π^(2k) where c_k = (-1)^(k+1) · 2^(2k-1) · B_{2k} / (2k)!
    2. c_k ≠ 0 (Bernoulli numbers B_{2k} ≠ 0 for k ≥ 1)
    3. π is transcendental (Lindemann, axiomatized)
    4. Nonzero rational × power of transcendental = transcendental -/
def even_zeta_values_transcendental : Prop :=
  ∀ k : ℕ, 1 ≤ k → Transcendental ℚ (zetaValue (2 * k))

/-- ζ(2) is verified transcendental (see zetaValue_two_transcendental). -/
theorem even_zeta_transcendental_at_1 :
    Transcendental ℚ (zetaValue (2 * 1)) := by
  simp only [Nat.mul_one]; exact zetaValue_two_transcendental

/-- ζ(4) is verified transcendental (see zetaValue_four_transcendental). -/
theorem even_zeta_transcendental_at_2 :
    Transcendental ℚ (zetaValue (2 * 2)) := by
  norm_num; exact zetaValue_four_transcendental

/-- The hierarchy of arithmetic properties:
    transcendental ⊃ irrational ⊃ "not rational"

    For even zeta values: ζ(2) is transcendental (hence irrational).
    For ζ(3): irrational (Apéry), transcendence unknown.
    For ζ(5): unknown even whether irrational. -/
theorem even_odd_hierarchy :
    -- ζ(2) is transcendental (strongest property)
    Transcendental ℚ (zetaValue 2) ∧
    -- ζ(3) is irrational (Apéry, but transcendence unknown)
    Irrational (zetaValue 3) ∧
    -- ζ(2) being transcendental implies it is irrational
    Irrational (zetaValue 2) := by
  refine ⟨zetaValue_two_transcendental, apery_theorem, ?_⟩
  exact Transcendental.irrational zetaValue_two_transcendental

/-- Problem status: OPEN for the transcendence conjecture (odd values).
    RESOLVED for even values (transcendental, via Lindemann). -/
def problem_status : String :=
  "OPEN: no odd ζ(2k+1) known transcendental. " ++
  "RESOLVED: all even ζ(2k) are transcendental (Euler + Lindemann)."

end BaselProblemOQ02
