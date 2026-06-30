/-
  Erdős / Abel-Ruffini family — OQ-04-OQ-01-OQ-01
  The alternate quintic witness x⁵ - x - 1.

  Parent (abel-ruffini-oq-04-oq-01, file AbelRuffiniOQ04OQ01.lean) proved the
  concrete Abel-Ruffini result Gal(x⁵ - 4x + 2) ≅ S₅ and asked, as its first
  open question, whether x⁵ - x - 1 is a second concrete S₅ witness, claiming
  it could be handled "by the same argument used here" after a sign analysis
  showing "3 real roots".

  ## Key finding of this entry (corrects the open question)

  The premise is FALSE: x⁵ - x - 1 has **exactly one** real root, not three
  (its local maximum, at x = -5^(-1/4), already lies below the x-axis). Hence
  it has TWO complex-conjugate pairs of roots, and complex conjugation acts on
  the five roots as a *double* transposition — an EVEN permutation lying in A₅.
  The parent's decisive step (complex conjugation supplies an odd permutation /
  a transposition, because x⁵ - 4x + 2 has 3 real + 1 conjugate pair) therefore
  does NOT transfer. A correct S₅ proof for x⁵ - x - 1 must obtain a
  transposition by another route — e.g. Dedekind's theorem applied to the
  factorization mod 2, where x⁵ - x - 1 ≡ (x²+x+1)(x³+x²+1) gives cycle type
  (2,3), whose cube is a transposition — together with the mod-3 reduction,
  where x⁵ - x - 1 stays irreducible and supplies a 5-cycle.

  Consistency check via the discriminant: with two conjugate pairs the
  discriminant is positive, and indeed the Bring-Jerrard formula
  256·p⁵ + 3125·q⁴ at (p,q) = (-1,-1) gives 2869 > 0, a non-square
  (2869 = 19·151), confirming Gal ⊄ A₅.

  ## What is machine-checked below (0 sorries, 0 axioms)

  * `q_natDegree`, `q_monic`         — basic shape of q = X⁵ - X - 1 over ℚ
  * `q_eval_one`, `q_eval_neg_one`   — ±1 are not roots (only candidate
                                       rational roots, by the monic rational
                                       root theorem)
  * `exists_real_root_Ioo`           — a real root exists in (1,2) (IVT)
  * `disc_value`                     — 256·(-1)⁵ + 3125·(-1)⁴ = 2869
  * `not_isSquare_2869`              — 2869 is not a perfect square

  ## What is NOT formalized here (documented, not claimed)

  * Irreducibility of x⁵ - x - 1 over ℚ (the genuinely hard, non-Eisenstein
    step; provable in principle by reduction mod 3, but Mathlib has no cheap
    decision procedure for irreducibility over 𝔽₃ and the Aristotle prover was
    unavailable this session).
  * "Exactly one real root" as a Lean theorem (only existence is proved here;
    the uniqueness follows from the derivative analysis sketched above).
  * The full Gal(x⁵ - x - 1) ≅ S₅, which — per the finding above — requires a
    different argument from the parent, not a copy of it.
-/
import Mathlib

open Polynomial

namespace AbelRuffiniOQ04OQ01OQ01

/-- The alternate quintic witness, over ℚ. -/
noncomputable def q : ℚ[X] := X ^ 5 - X - 1

/-- q has degree 5. -/
theorem q_natDegree : q.natDegree = 5 := by
  unfold q; compute_degree!

/-- q is monic. -/
theorem q_monic : q.Monic := by
  unfold q
  monicity!

/-- 1 is not a root of q (q.eval 1 = -1). -/
theorem q_eval_one : q.eval 1 = -1 := by
  unfold q; simp

/-- -1 is not a root of q (q.eval (-1) = -1). -/
theorem q_eval_neg_one : q.eval (-1) = -1 := by
  unfold q; simp; norm_num

/-- The real polynomial function x ↦ x⁵ - x - 1. -/
def f (x : ℝ) : ℝ := x ^ 5 - x - 1

theorem f_continuous : Continuous f := by
  unfold f; fun_prop

theorem f_one : f 1 = -1 := by unfold f; norm_num

theorem f_two : f 2 = 29 := by unfold f; norm_num

/-- x⁵ - x - 1 has a real root in the open interval (1, 2).
    (Existence; combined with the derivative analysis in the header, this root
    is the unique real root.) -/
theorem exists_real_root_Ioo : ∃ x ∈ Set.Ioo (1 : ℝ) 2, f x = 0 := by
  have hcont : ContinuousOn f (Set.Icc 1 2) := f_continuous.continuousOn
  have hlt : f 1 < 0 := by rw [f_one]; norm_num
  have hgt : (0 : ℝ) < f 2 := by rw [f_two]; norm_num
  obtain ⟨x, hx, hfx⟩ :=
    intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 2) hcont
      (show (0 : ℝ) ∈ Set.Ioo (f 1) (f 2) by
        rw [f_one, f_two]; constructor <;> norm_num)
  exact ⟨x, hx, hfx⟩

/-- The Bring-Jerrard discriminant value for x⁵ + px + q at (p,q) = (-1,-1):
    256·p⁵ + 3125·q⁴ = 2869. -/
theorem disc_value : (256 : ℤ) * (-1) ^ 5 + 3125 * (-1) ^ 4 = 2869 := by
  norm_num

/-- 2869 (= 19 · 151) is not a perfect square. Hence the discriminant of
    x⁵ - x - 1 is a non-square and its Galois group is not contained in A₅. -/
theorem not_isSquare_2869 : ¬ ∃ r : ℕ, r * r = 2869 := by
  rintro ⟨r, hr⟩
  have hb : r ≤ 53 := by nlinarith
  interval_cases r <;> omega

end AbelRuffiniOQ04OQ01OQ01
