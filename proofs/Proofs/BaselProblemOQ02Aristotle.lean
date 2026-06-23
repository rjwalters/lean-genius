/-
  Aristotle targets for Basel Problem OQ-02 (Odd Zeta Transcendence)
  Routine supporting lemmas for automated proof search.
  See BaselProblemOQ02.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (odd zeta transcendence)
  - Known results provable from Mathlib + axioms
  - Clean theorem statements with no definition sorries
  - No axiom declarations (converted to theorem ... := by sorry)

  Status: pi_transcendental proved via import. zeta_two/four_transcendental
  proved via transcendental_pow + algebraic closure. Apéry's theorem
  (ζ(3) irrational, 1978) is not exposed here — it is not Aristotle-tractable
  and is declared as `axiom apery_theorem` in BaselProblemOQ02.lean.
-/
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic
import Proofs.PiTranscendental

open BigOperators Filter Topology Real Polynomial

namespace BaselProblemOQ02Aristotle

-- Definitions needed for the theorems
noncomputable def zetaValue (s : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s

-- π is transcendental over ℚ (proved in PiTranscendental.lean from Lindemann axiom)
theorem pi_transcendental : Transcendental ℚ (Real.pi : ℝ) :=
  pi_transcendental_over_rationals

-- Known closed forms (from Mathlib)
theorem zetaValue_two : zetaValue 2 = π ^ 2 / 6 := by
  unfold zetaValue; exact hasSum_zeta_two.tsum_eq

theorem zetaValue_four : zetaValue 4 = π ^ 4 / 90 := by
  unfold zetaValue; exact hasSum_zeta_four.tsum_eq

-- Helper: composition with nonzero polynomial of positive degree is nonzero
private lemma comp_ne_zero_of_pos_natDegree {p g : ℚ[X]} (hp : p ≠ 0)
    (hg : 0 < g.natDegree) : p.comp g ≠ 0 := by
  intro h
  have hd : 0 < p.natDegree := by
    by_contra h_le
    push_neg at h_le
    interval_cases p.natDegree <;> simp_all [natDegree_eq_zero_iff_degree_le_zero] at *
  have hpos : 0 < (p.comp g).natDegree := by
    rw [natDegree_comp]
    exact Nat.mul_pos hd hg
  simp [h] at hpos

-- Key lemma: transcendental → power is transcendental
theorem transcendental_pow_of_transcendental {x : ℝ} (hx : Transcendental ℚ x)
    {n : ℕ} (hn : 0 < n) : Transcendental ℚ (x ^ n) := by
  intro ⟨p, hp_ne, hp_eval⟩
  apply hx
  refine ⟨p.comp (X ^ n), ?_, ?_⟩
  · exact comp_ne_zero_of_pos_natDegree hp_ne
      (by simp only [natDegree_X_pow]; omega)
  · rw [aeval_comp, map_pow, aeval_X]
    exact hp_eval

-- PROVED: ζ(2) is transcendental
-- Strategy: ζ(2) = π²/6, π transcendental → π² transcendental → π²/6 transcendental
theorem zeta_two_transcendental : Transcendental ℚ (zetaValue 2) := by
  rw [zetaValue_two]
  have h_pi2 : Transcendental ℚ (π ^ 2) :=
    transcendental_pow_of_transcendental pi_transcendental (by norm_num)
  intro h_alg
  apply h_pi2
  -- π² = 6 * (π²/6), and 6 is algebraic, so π² = algebraic * algebraic = algebraic
  have heq : (π : ℝ) ^ 2 = algebraMap ℚ ℝ 6 * (π ^ 2 / 6) := by
    have : algebraMap ℚ ℝ = (↑· : ℚ → ℝ) := funext fun _ => rfl
    rw [this]; push_cast; ring
  rw [heq]
  exact (isAlgebraic_algebraMap (6 : ℚ)).mul h_alg

-- PROVED: ζ(4) is transcendental
-- Strategy: ζ(4) = π⁴/90, same approach as ζ(2)
theorem zeta_four_transcendental : Transcendental ℚ (zetaValue 4) := by
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

end BaselProblemOQ02Aristotle
