/-
Erdős Problem #395 — Open Question oq-02:
  "Does a similar result hold for higher-dimensional vectors?"

Source: https://erdosproblems.com/395  (open questions, follow-up #2)
Parent: Erdős #395 — Reverse Littlewood–Offord, SOLVED by
        He–Juškevičius–Narayanan–Spiro (HJNS 2024).

## The parent result (HJNS 2024)

For unit *complex* vectors z₁, …, zₙ (|zᵢ| = 1 in ℂ ≅ ℝ²) and random signs
εᵢ ∈ {±1}, the probability that |ε₁z₁ + … + εₙzₙ| ≤ √2 is at least c/n for an
absolute constant c > 0.  Here ℂ = ℝ² is the **2-dimensional** real inner
product space.

## The open question

Does the same phenomenon — a c/n lower bound on the probability that a random
sign sum lands within a *fixed* distance of the origin — persist for unit
vectors in higher-dimensional real inner product spaces ℝ^d (d ≥ 3)?

This file does **not** resolve the open question for fixed dimension d (that
remains open).  What it does, axiom-free, is isolate the *correct shape* of any
higher-dimensional statement by proving a clean obstruction:

  **If the dimension is allowed to grow with n, the naive "dimension-free,
  fixed-threshold" analogue of HJNS is FALSE.**

The mechanism is the orthogonality identity.  If z₁, …, zₙ are *orthonormal*
unit vectors (which exist precisely when the ambient dimension d ≥ n — e.g. the
standard basis of ℝⁿ), then for **every** sign choice ε ∈ {±1}ⁿ,

  ‖ε₁z₁ + … + εₙzₙ‖² = Σ εᵢ² ‖zᵢ‖² = n   (the cross terms ⟨zᵢ,zⱼ⟩ vanish),

so the sign sum sits at distance exactly √n from the origin — *deterministically*.
Hence for any fixed threshold C, once n > C² no sign choice lands within C: the
favourable event is empty and its probability is 0, not ≥ c/n.

**Conclusion / contribution.** Any correct higher-dimensional reverse
Littlewood–Offord statement must keep the dimension d bounded (independent of n),
or let the threshold grow with the dimension.  The orthonormal configuration is
the obstruction, and the proof here is fully machine-checked with 0 axioms.

References:
- [HJNS24] He, Juškevičius, Narayanan, Spiro, "The Reverse Littlewood–Offord
           problem of Erdős", arXiv:2408.11034 (2024).
- Parent formalization: Proofs/Erdos395Problem.lean.
-/
import Mathlib

open scoped RealInnerProductSpace BigOperators

namespace Erdos395OQ02

/-!
## Part I: Sign vectors and signed sums in a real inner product space

We work over an arbitrary real inner product space `E`, so the statements cover
ℝ^d for every dimension d uniformly (the complex case ℂ = ℝ² of the parent
problem included).
-/

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A sign vector: each component is `+1` or `-1`. -/
def IsSign (ε : Fin n → ℝ) : Prop := ∀ i, ε i = 1 ∨ ε i = -1

/-- The signed sum `ε₁ z₁ + … + εₙ zₙ`. -/
def signedSum (z : Fin n → E) (ε : Fin n → ℝ) : E := ∑ i, ε i • z i

/-- A sign squares to one. -/
lemma sign_mul_self {ε : Fin n → ℝ} (hε : IsSign ε) (i : Fin n) : ε i * ε i = 1 := by
  rcases hε i with h | h <;> rw [h] <;> ring

/-!
## Part II: The orthogonality identity

For an orthonormal family the squared norm of *every* sign sum equals `n`,
independently of the signs.  This is the engine of the obstruction.
-/

/-- **Orthogonality identity.** If `z` is orthonormal and `ε` is a sign vector,
then `‖ε₁z₁ + … + εₙzₙ‖² = n` for every choice of signs. -/
theorem signedSum_norm_sq_of_orthonormal (z : Fin n → E) (hz : Orthonormal ℝ z)
    (ε : Fin n → ℝ) (hε : IsSign ε) :
    ‖signedSum z ε‖ ^ 2 = (n : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, signedSum, sum_inner]
  simp_rw [inner_sum, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp hz]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [sign_mul_self hε, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- Consequence: the sign sum of an orthonormal family has norm exactly `√n`. -/
theorem signedSum_norm_of_orthonormal (z : Fin n → E) (hz : Orthonormal ℝ z)
    (ε : Fin n → ℝ) (hε : IsSign ε) :
    ‖signedSum z ε‖ = Real.sqrt n := by
  have h := signedSum_norm_sq_of_orthonormal z hz ε hε
  have : ‖signedSum z ε‖ = Real.sqrt (‖signedSum z ε‖ ^ 2) :=
    (Real.sqrt_sq (norm_nonneg _)).symm
  rw [this, h]

/-!
## Part III: The obstruction

For a fixed threshold `C` with `C² < n`, *no* sign choice of an orthonormal
family lands within distance `C` of the origin.  The favourable set is empty.
-/

/-- **Obstruction (set form).** For an orthonormal family and a threshold `C`
with `C² < n`, the set of sign vectors whose signed sum has norm `≤ C` is
empty. -/
theorem orthonormal_smallSum_eq_empty (z : Fin n → E) (hz : Orthonormal ℝ z)
    (C : ℝ) (hC : C ^ 2 < (n : ℝ)) :
    {ε : Fin n → ℝ | IsSign ε ∧ ‖signedSum z ε‖ ≤ C} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ε ⟨hε, hle⟩
  have h0 : (0 : ℝ) ≤ ‖signedSum z ε‖ := norm_nonneg _
  have hsq : ‖signedSum z ε‖ ^ 2 ≤ C ^ 2 := by nlinarith [h0, hle]
  rw [signedSum_norm_sq_of_orthonormal z hz ε hε] at hsq
  linarith

/-!
## Part IV: Probability formulation and falsity of the dimension-free analogue

We now phrase the counting/probability version in `EuclideanSpace ℝ (Fin d)`,
matching the parent problem's `probSmallSum`, and prove that the
"dimension-free, fixed-threshold" reverse Littlewood–Offord statement fails.

Sign vectors are indexed by `Fin n → Bool` (`true ↦ +1`, `false ↦ -1`), giving a
finite sample space of size `2ⁿ`.
-/

/-- Boolean encoding of a sign. -/
def toSign (b : Bool) : ℝ := if b then 1 else -1

/-- The sign vector induced by a Boolean vector. -/
def signOf (s : Fin n → Bool) : Fin n → ℝ := fun i => toSign (s i)

lemma isSign_signOf (s : Fin n → Bool) : IsSign (signOf s) := by
  intro i; unfold signOf toSign; cases s i <;> simp

variable {d : ℕ}

/-- Number of sign choices `ε ∈ {±1}ⁿ` with `‖ε₁z₁ + … + εₙzₙ‖ ≤ C`. -/
noncomputable def smallSumCount (z : Fin n → EuclideanSpace ℝ (Fin d)) (C : ℝ) : ℕ :=
  (Finset.univ.filter (fun s : Fin n → Bool => ‖signedSum z (signOf s)‖ ≤ C)).card

/-- Probability that a uniform random sign choice gives `‖sum‖ ≤ C`. -/
noncomputable def smallSumProb (z : Fin n → EuclideanSpace ℝ (Fin d)) (C : ℝ) : ℝ :=
  (smallSumCount z C : ℝ) / (2 : ℝ) ^ n

/-- For an orthonormal family with `C² < n`, *no* sign choice is favourable. -/
theorem orthonormal_smallSumCount_eq_zero (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Orthonormal ℝ z) (C : ℝ) (hC : C ^ 2 < (n : ℝ)) :
    smallSumCount z C = 0 := by
  rw [smallSumCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ hle
  have h0 : (0 : ℝ) ≤ ‖signedSum z (signOf s)‖ := norm_nonneg _
  have hsq : ‖signedSum z (signOf s)‖ ^ 2 ≤ C ^ 2 := by nlinarith [h0, hle]
  rw [signedSum_norm_sq_of_orthonormal z hz (signOf s) (isSign_signOf s)] at hsq
  linarith

/-- Hence the probability is exactly `0`. -/
theorem orthonormal_smallSumProb_eq_zero (z : Fin n → EuclideanSpace ℝ (Fin d))
    (hz : Orthonormal ℝ z) (C : ℝ) (hC : C ^ 2 < (n : ℝ)) :
    smallSumProb z C = 0 := by
  rw [smallSumProb, orthonormal_smallSumCount_eq_zero z hz C hC]; simp

/-- The standard basis of `EuclideanSpace ℝ (Fin n)` is orthonormal; it realizes
the obstruction in ambient dimension `d = n`. -/
theorem basisFun_orthonormal :
    Orthonormal ℝ (⇑(EuclideanSpace.basisFun (Fin n) ℝ)) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal

/-- **Headline.** The dimension-free, fixed-threshold analogue of HJNS is FALSE:
there is no single threshold `C` and constant `c > 0` such that, for all `n` and
all orthonormal unit configurations in `EuclideanSpace ℝ (Fin n)` (dimension
growing with `n`), the probability that `‖ε₁z₁ + … + εₙzₙ‖ ≤ C` is at least
`c / n`.

The witness is the standard orthonormal basis in dimension `d = n`: for `n > C²`
the favourable event is empty (probability `0`), while `c / n > 0`. -/
theorem dimensionFree_reverseLO_false :
    ¬ ∃ C c : ℝ, 0 < c ∧
        ∀ m : ℕ, 0 < m → ∀ z : Fin m → EuclideanSpace ℝ (Fin m),
          Orthonormal ℝ z → c / (m : ℝ) ≤ smallSumProb z C := by
  rintro ⟨C, c, hc, h⟩
  -- Pick `m` with `C² < m` (so the obstruction fires) and `m > 0`.
  obtain ⟨m, hm⟩ := exists_nat_gt (C ^ 2)
  have hCsq : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
  have hm0 : 0 < m := by
    have : (0 : ℝ) < (m : ℝ) := lt_of_le_of_lt hCsq hm
    exact_mod_cast this
  -- The standard basis in dimension `m` gives probability 0.
  have hprob :=
    orthonormal_smallSumProb_eq_zero (d := m) (⇑(EuclideanSpace.basisFun (Fin m) ℝ))
      basisFun_orthonormal C (by exact_mod_cast hm)
  have hge := h m hm0 (⇑(EuclideanSpace.basisFun (Fin m) ℝ)) basisFun_orthonormal
  rw [hprob] at hge
  -- `c / m ≤ 0` but `c / m > 0`.
  have : 0 < c / (m : ℝ) := div_pos hc (by exact_mod_cast hm0)
  linarith

/-!
## Part V: The genuine open question (left unproven)

The *fixed-dimension* form of the question is what remains genuinely open.  For
each fixed `d`, does there exist a threshold `C_d` and constant `c_d > 0` such
that for all `n` and all unit vectors `z₁, …, zₙ ∈ ℝ^d`, the probability that
`‖ε₁z₁ + … + εₙzₙ‖ ≤ C_d` is at least `c_d / n`?

We record the statement as a `Prop`; it is **not** a theorem here.
-/

/-- The fixed-dimension higher-dimensional reverse Littlewood–Offord question for
ambient dimension `d`.  This proposition is the open problem and is deliberately
left unproven. -/
def ReverseLO_fixedDim (d : ℕ) : Prop :=
  ∃ C c : ℝ, 0 < c ∧
    ∀ m : ℕ, 0 < m → ∀ z : Fin m → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖z i‖ = 1) → c / (m : ℝ) ≤ smallSumProb z C

/-!
## Part VI: Summary

**Erdős #395 oq-02 — Higher-dimensional reverse Littlewood–Offord.**

- Parent (HJNS 2024): in dimension 2 (ℂ), `P(‖Σεᵢzᵢ‖ ≤ √2) ≥ c/n`.
- This file (0 axioms): proves the **orthogonality identity**
  `‖Σεᵢzᵢ‖² = n` for orthonormal families, hence the favourable event is empty
  once the threshold satisfies `C² < n`.  Therefore the **dimension-free**
  fixed-threshold analogue is FALSE (`dimensionFree_reverseLO_false`): any
  correct higher-dimensional statement must bound the dimension `d`
  independently of `n` (or grow the threshold with `d`).
- The **fixed-dimension** question `ReverseLO_fixedDim d` (d ≥ 3) is recorded as
  an open `Prop` and remains unresolved.
-/

end Erdos395OQ02
